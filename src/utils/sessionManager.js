const { LRUCache } = require('lru-cache');
const { EventEmitter } = require('events');
const fs = require('fs').promises;
const path = require('path');
const crypto = require('crypto');
const { StorageFactory, StorageAdapter } = require('../storage');
const log = require('./logger');
const { encryptUserConfig, decryptUserConfig, normalizeSensitiveInputsForStorage } = require('./encryption');
const { redactToken } = require('./security');
const { MAX_SESSION_BRIEF_BATCH, normalizeSessionBriefTokens } = require('./sessionBriefBatch');

const DECRYPTED_CACHE_TTL_MS = 5 * 60 * 1000;
const FAILED_LOOKUP_MAX = 10;
const FAILED_LOOKUP_WINDOW_MS = 60 * 1000;
const FAILED_LOOKUP_BLOCK_MS = 5 * 60 * 1000;

const META_KEYS = {
  SESSION_TOKEN: '__sessionToken',
  SESSION_FINGERPRINT: '__sessionFingerprint'
};

const INTERNAL_FLAGS = [
  '_encrypted',
  '__decryptionWarning',
  '__decryptionWarningFields',
  '__nestedEncryptionRecovered',
  '__nestedEncryptionRecoveredFields',
  '__credentialDecryptionFailed',
  '__credentialDecryptionFailedFields',
  '__credentialWarningEntry',
  '__sessionTokenError',
  '__originalToken',
  '__configHash',
  '__configHashScope',
  '__configBaseHash',
  '__historyUserHash',
  '__needsSessionPersist',
  '__persistReason',
  '__regenerated',
  '__regeneratedAt',
  '__fetchedAt',
  '__invalidSession'
];

function stripInternalFlags(config) {
  if (!config || typeof config !== 'object') return config;
  try {
    for (const flag of INTERNAL_FLAGS) {
      delete config[flag];
    }
  } catch (_) { }
  return config;
}

function computeConfigFingerprint(config) {
  try {
    const serialized = JSON.stringify(config || {});
    return crypto.createHash('sha256').update(serialized).digest('hex').slice(0, 16);
  } catch (err) {
    return 'fingerprint_error';
  }
}

function computeTokenFingerprint(token) {
  try {
    return crypto.createHash('sha256').update(String(token || '')).digest('hex').slice(0, 16);
  } catch (err) {
    return 'token_fingerprint_error';
  }
}

function computeHistoryUserHash(token) {
  return `sesshist_${computeTokenFingerprint(token)}`;
}

function computeIntegrityHash(token, fingerprint) {
  try {
    return crypto.createHash('sha256').update(String(token || '')).update('|').update(String(fingerprint || '')).digest('hex').slice(0, 24);
  } catch (err) {
    return 'integrity_error';
  }
}

function embedSessionMetadata(config, token, fingerprint) {
  const cloned = cloneConfig(config);
  try {
    Object.defineProperty(cloned, META_KEYS.SESSION_TOKEN, { value: token, enumerable: true, configurable: true, writable: true });
    Object.defineProperty(cloned, META_KEYS.SESSION_FINGERPRINT, { value: fingerprint, enumerable: true, configurable: true, writable: true });
  } catch (_) {
    cloned[META_KEYS.SESSION_TOKEN] = token;
    cloned[META_KEYS.SESSION_FINGERPRINT] = fingerprint;
  }
  return cloned;
}

function stripSessionMetadata(config) {
  if (!config || typeof config !== 'object') {
    return { config, metadata: {} };
  }
  const metadata = {
    token: config[META_KEYS.SESSION_TOKEN],
    fingerprint: config[META_KEYS.SESSION_FINGERPRINT]
  };
  try {
    delete config[META_KEYS.SESSION_TOKEN];
    delete config[META_KEYS.SESSION_FINGERPRINT];
    stripInternalFlags(config);
  } catch (_) { }
  return { config, metadata };
}

function cloneConfig(config) {
  if (!config || typeof config !== 'object') return config;
  try {
    if (typeof structuredClone === 'function') return structuredClone(config);
  } catch (_) { }
  try {
    return JSON.parse(JSON.stringify(config));
  } catch (_) {
    return config;
  }
}

function tryDecodeStatelessToken(token) {
  if (!token) return null;
  try {
    let jsonStr = null;
    try {
      jsonStr = Buffer.from(token, 'base64url').toString('utf8');
    } catch (_) {
      jsonStr = Buffer.from(token, 'base64').toString('utf8');
    }
    const parsed = JSON.parse(jsonStr);
    if (parsed && typeof parsed === 'object') {
      log.debug(() => `[SessionManager] Decoded stateless config from token successfully`);
      return parsed;
    }
  } catch (_) { }
  return null;
}

let storageAdapter = null;
async function getStorageAdapter() {
  if (!storageAdapter) {
    storageAdapter = await StorageFactory.getStorageAdapter();
  }
  return storageAdapter;
}

class SessionManager extends EventEmitter {
  constructor(options = {}) {
    super();
    this.instanceId = crypto.randomBytes(8).toString('hex');
    this.maxSessions = (Number.isFinite(options.maxSessions) && options.maxSessions > 0) ? options.maxSessions : null;
    this.maxAge = options.maxAge || 90 * 24 * 60 * 60 * 1000;
    this.persistencePath = options.persistencePath || path.join(process.cwd(), 'data', 'sessions.json');
    
    this.ensureDataDir();

    const cacheOptions = {
      ttl: this.maxAge,
      updateAgeOnGet: true,
      updateAgeOnHas: false
    };
    if (this.maxSessions) cacheOptions.max = this.maxSessions;
    this.cache = new LRUCache(cacheOptions);

    this.decryptedCache = new LRUCache({
      max: this.maxSessions || 30000,
      ttl: DECRYPTED_CACHE_TTL_MS,
      updateAgeOnGet: true
    });

    this.failedLookups = new LRUCache({ max: 10000, ttl: FAILED_LOOKUP_BLOCK_MS });
    this.isReady = true;
  }

  async waitUntilReady() {
    return true;
  }

  getStats() {
    return {
      activeSessions: this.cache.size,
      maxSessions: this.maxSessions || 30000,
      decryptedCacheSize: this.decryptedCache.size,
      instanceId: this.instanceId,
      isReady: this.isReady
    };
  }

  getMetrics() {
    return this.getStats();
  }

  ensureDataDir() {
    try {
      const dir = path.dirname(this.persistencePath);
      if (!require('fs').existsSync(dir)) {
        require('fs').mkdirSync(dir, { recursive: true });
      }
    } catch (_) { }
  }

  generateToken() {
    return crypto.randomBytes(16).toString('hex');
  }

  async createSession(config) {
    try {
      const normalizedConfig = normalizeSensitiveInputsForStorage(stripInternalFlags(cloneConfig(config)));
      const token = this.generateToken();
      const tokenFingerprint = computeTokenFingerprint(token);
      const fingerprint = computeConfigFingerprint(normalizedConfig);
      const configWithMetadata = embedSessionMetadata(normalizedConfig, token, fingerprint);
      
      let encryptedConfig;
      try {
        encryptedConfig = encryptUserConfig(configWithMetadata);
      } catch (encErr) {
        encryptedConfig = configWithMetadata;
      }

      const integrity = computeIntegrityHash(token, fingerprint);
      const now = Date.now();
      const sessionData = {
        token,
        tokenFingerprint,
        historyUserHash: computeHistoryUserHash(token),
        config: encryptedConfig,
        createdAt: now,
        updatedAt: now,
        lastAccessedAt: now,
        disabled: false,
        fingerprint,
        integrity
      };

      this.cache.set(token, sessionData);
      const configForCache = cloneConfig(normalizedConfig);
      configForCache.__historyUserHash = sessionData.historyUserHash;
      this.decryptedCache.set(token, configForCache);

      try {
        const adapter = await getStorageAdapter();
        await adapter.set(token, sessionData, StorageAdapter.CACHE_TYPES.SESSION);
      } catch (err) { }

      this.emit('sessionCreated', { token, source: 'local' });
      return token;
    } catch (err) {
      log.error(() => ['[SessionManager] Failed to create session:', err.message || err]);
      throw err;
    }
  }

  async getSession(token) {
    if (!token) return null;

    let sessionData = this.cache.get(token);

    if (!sessionData) {
      const loadedConfig = await this.loadSessionFromStorage(token);
      if (loadedConfig) return loadedConfig;

      const recoveredStateless = tryDecodeStatelessToken(token);
      if (recoveredStateless) {
        log.warn(() => `[SessionManager] Recovered stateless config from token ${redactToken(token)}`);
        return recoveredStateless;
      }

      this._recordFailedLookup(token);
      return null;
    }

    const cachedDecrypted = this.decryptedCache.get(token);
    if (cachedDecrypted) {
      const cloned = cloneConfig(cachedDecrypted);
      cloned.__historyUserHash = sessionData.historyUserHash;
      return cloned;
    }

    try {
      let decryptedConfig;
      if (sessionData.config && sessionData.config._encrypted) {
        const rawDecrypted = decryptUserConfig(sessionData.config);
        const stripped = stripSessionMetadata(rawDecrypted);
        decryptedConfig = stripped.config;
      } else {
        const stripped = stripSessionMetadata(sessionData.config);
        decryptedConfig = stripped.config;
      }

      if (decryptedConfig) {
        decryptedConfig.__historyUserHash = sessionData.historyUserHash;
        this.decryptedCache.set(token, cloneConfig(decryptedConfig));
        return cloneConfig(decryptedConfig);
      }
    } catch (err) { }

    const recoveredStateless = tryDecodeStatelessToken(token);
    if (recoveredStateless) return recoveredStateless;

    return null;
  }

  _recordFailedLookup(token) {
    let entry = this.failedLookups.get(token);
    const now = Date.now();
    if (!entry || (now - entry.firstFailAt > FAILED_LOOKUP_WINDOW_MS)) {
      entry = { count: 1, firstFailAt: now, blockedUntil: 0 };
    } else {
      entry.count++;
    }
    if (entry.count >= FAILED_LOOKUP_MAX && !entry.blockedUntil) {
      entry.blockedUntil = now + FAILED_LOOKUP_BLOCK_MS;
    }
    this.failedLookups.set(token, entry);
  }

  hasSession(token) {
    return this.cache.has(token);
  }

  async updateSession(token, config) {
    if (!token) return false;
    const normalizedConfig = normalizeSensitiveInputsForStorage(stripInternalFlags(cloneConfig(config)));
    let sessionData = this.cache.get(token) || {};

    const fingerprint = computeConfigFingerprint(normalizedConfig);
    const configWithMetadata = embedSessionMetadata(normalizedConfig, token, fingerprint);
    
    let encryptedConfig;
    try {
      encryptedConfig = encryptUserConfig(configWithMetadata);
    } catch (_) {
      encryptedConfig = configWithMetadata;
    }

    const integrity = computeIntegrityHash(token, fingerprint);
    const now = Date.now();

    sessionData.config = encryptedConfig;
    sessionData.lastAccessedAt = now;
    sessionData.updatedAt = now;
    sessionData.fingerprint = fingerprint;
    sessionData.integrity = integrity;
    sessionData.tokenFingerprint = computeTokenFingerprint(token);
    sessionData.historyUserHash = sessionData.historyUserHash || computeHistoryUserHash(token);

    this.cache.set(token, sessionData);
    const configForCache = cloneConfig(normalizedConfig);
    configForCache.__historyUserHash = sessionData.historyUserHash;
    this.decryptedCache.set(token, configForCache);

    try {
      const adapter = await getStorageAdapter();
      await adapter.set(token, sessionData, StorageAdapter.CACHE_TYPES.SESSION);
    } catch (err) { }

    this.emit('sessionUpdated', { token, source: 'local' });
    return true;
  }

  async loadSessionFromStorage(token) {
    try {
      if (!token) return null;
      const adapter = await getStorageAdapter();
      const stored = await adapter.get(token, StorageAdapter.CACHE_TYPES.SESSION);
      if (!stored) return null;

      let decryptedConfig;
      if (stored.config && stored.config._encrypted) {
        const rawDecrypted = decryptUserConfig(stored.config);
        const stripped = stripSessionMetadata(rawDecrypted);
        decryptedConfig = stripped.config;
      } else {
        const stripped = stripSessionMetadata(stored.config);
        decryptedConfig = stripped.config;
      }

      if (decryptedConfig) {
        this.cache.set(token, stored);
        this.decryptedCache.set(token, cloneConfig(decryptedConfig));
        return cloneConfig(decryptedConfig);
      }
    } catch (_) { }
    return null;
  }

  deleteSession(token) {
    const existed = this.cache.delete(token);
    this.decryptedCache.delete(token);
    return existed;
  }

  setupShutdownHandlers(server) { }
}

let instance = null;
function getSessionManager(options = {}) {
  if (!instance) {
    instance = new SessionManager(options);
  }
  return instance;
}

module.exports = {
  MAX_SESSION_BRIEF_BATCH,
  SessionManager,
  getSessionManager,
  normalizeSessionBriefTokens,
  stripInternalFlags
};
