const { LRUCache } = require('lru-cache');
const { EventEmitter } = require('events');
const fs = require('fs').promises;
const path = require('path');
const crypto = require('crypto');
const Redis = require('ioredis');
const { StorageFactory, StorageAdapter } = require('../storage');
const { StorageUnavailableError } = require('../storage/errors');
const log = require('./logger');
const { shutdownLogger } = require('./logger');
const sentry = require('./sentry');
const { handleCaughtError } = require('./errorClassifier');
const { encryptUserConfig, decryptUserConfig, normalizeSensitiveInputsForStorage, getDecryptionWarnings } = require('./encryption');
const { redactToken } = require('./security');
const { getRedisPassword } = require('./redisHelper');
const { MAX_SESSION_BRIEF_BATCH, SESSION_BRIEF_LOOKUP_CONCURRENCY, normalizeSessionBriefTokens } = require('./sessionBriefBatch');

const DECRYPTED_CACHE_TTL_MS = 5 * 60 * 1000;
const STORAGE_COUNT_CACHE_TTL_MS = 5 * 60 * 1000;
const TTL_REFRESH_DEBOUNCE_MS = 60 * 60 * 1000;
const SESSION_INDEX_VERIFY_INTERVAL_MS = 3 * 60 * 60 * 1000;

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

function sanitizeHistoryComponent(value) {
  return String(value || '')
    .trim()
    .replace(/[^a-zA-Z0-9_-]/g, '_')
    .slice(0, 200);
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
    this.redisTtlEnabled = String(process.env.SESSION_REDIS_TTL_ENABLED || 'true').toLowerCase() === 'true';
    this.snapshotEnabled = String(process.env.SESSION_SNAPSHOT_ENABLED || '').toLowerCase() === 'true';
    this.persistencePath = options.persistencePath || path.join(process.cwd(), 'data', 'sessions.json');
    this.snapshotPath = process.env.SESSION_SNAPSHOT_PATH || this.persistencePath;
    this.autoSaveInterval = options.autoSaveInterval || 60 * 1000;
    this.shutdownTimeout = options.shutdownTimeout || 10 * 1000;

    this.storageMaxSessions = (Number.isFinite(options.storageMaxSessions) && options.storageMaxSessions > 0) ? options.storageMaxSessions : null;
    this.storageMaxAge = options.storageMaxAge || 90 * 24 * 60 * 60 * 1000;

    this.lastStorageCount = 0;
    this.lastEvictionCount = 0;
    this.evictionHistory = [];
    this.storageCountCache = { value: 0, ts: 0 };

    this.ensureDataDir();

    const cacheOptions = {
      ttl: this.maxAge,
      updateAgeOnGet: true,
      updateAgeOnHas: false,
      dispose: (value, key) => {
        this.lastEvictionCount++;
      }
    };
    if (this.maxSessions) cacheOptions.max = this.maxSessions;
    this.cache = new LRUCache(cacheOptions);

    const decryptedTtl = Math.min(this.maxAge || Infinity, DECRYPTED_CACHE_TTL_MS);
    this.decryptedCache = new LRUCache({
      max: this.maxSessions || 30000,
      ttl: Number.isFinite(decryptedTtl) ? decryptedTtl : DECRYPTED_CACHE_TTL_MS,
      updateAgeOnGet: true
    });

    this.failedLookups = new LRUCache({ max: 10000, ttl: FAILED_LOOKUP_BLOCK_MS });
    this.saveTimer = null;
    this.cleanupTimer = null;
    this.sessionIndexVerifyTimer = null;
    this.dirty = false;
    this.consecutiveSaveFailures = 0;
    this.isReady = false;
    this.loadingPromise = null;
    this.pendingPersistence = new Set();

    this.loadingPromise = this._initializeSessions();
    this.startAutoSave();
    this.startMemoryCleanup();
  }

  async waitUntilReady() {
    if (this.isReady) return;
    if (this.loadingPromise) {
      await this.loadingPromise;
    }
  }

  _calculateTtlSeconds() {
    if (!this.redisTtlEnabled) return null;
    return Number.isFinite(this.maxAge) ? Math.floor(this.maxAge / 1000) : null;
  }

  _trackPersistence(promise) {
    this.pendingPersistence.add(promise);
    promise.finally(() => this.pendingPersistence.delete(promise)).catch(() => { });
    return promise;
  }

  async _flushPendingPersistence() {
    if (this.pendingPersistence.size === 0) return;
    try {
      await Promise.allSettled(Array.from(this.pendingPersistence));
    } catch (_) { }
  }

  async _initializeSessions() {
    try {
      await this.loadFromDisk();
      if (this.snapshotEnabled) await this.restoreFromSnapshotIfStorageEmpty();
      this.isReady = true;
    } catch (err) {
      this.isReady = true;
    }
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
    const normalizedConfig = normalizeSensitiveInputsForStorage(stripInternalFlags(cloneConfig(config)));
    const token = this.generateToken();
    const tokenFingerprint = computeTokenFingerprint(token);
    const fingerprint = computeConfigFingerprint(normalizedConfig);
    const configWithMetadata = embedSessionMetadata(normalizedConfig, token, fingerprint);
    const encryptedConfig = encryptUserConfig(configWithMetadata);
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
      disabledAt: null,
      fingerprint,
      integrity
    };

    this.cache.set(token, sessionData);
    const configForCache = cloneConfig(normalizedConfig);
    configForCache.__historyUserHash = sessionData.historyUserHash;
    this.decryptedCache.set(token, configForCache);
    this.dirty = true;

    try {
      const adapter = await getStorageAdapter();
      const ttlSeconds = this._calculateTtlSeconds();
      await adapter.set(token, sessionData, StorageAdapter.CACHE_TYPES.SESSION, ttlSeconds);
    } catch (err) { }

    this.emit('sessionCreated', { token, source: 'local' });
    return token;
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
      const rawDecrypted = decryptUserConfig(sessionData.config);
      const { config: decryptedConfig } = stripSessionMetadata(rawDecrypted);
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
    let sessionData = this.cache.get(token);

    if (!sessionData) {
      await this.loadSessionFromStorage(token);
      sessionData = this.cache.get(token);
    }

    const fingerprint = computeConfigFingerprint(normalizedConfig);
    const configWithMetadata = embedSessionMetadata(normalizedConfig, token, fingerprint);
    const encryptedConfig = encryptUserConfig(configWithMetadata);
    const integrity = computeIntegrityHash(token, fingerprint);
    const tokenFingerprint = computeTokenFingerprint(token);

    const now = Date.now();
    sessionData = sessionData || {};
    sessionData.config = encryptedConfig;
    sessionData.lastAccessedAt = now;
    sessionData.updatedAt = now;
    sessionData.fingerprint = fingerprint;
    sessionData.integrity = integrity;
    sessionData.tokenFingerprint = tokenFingerprint;
    sessionData.historyUserHash = sessionData.historyUserHash || computeHistoryUserHash(token);

    this.cache.set(token, sessionData);
    const configForCache = cloneConfig(normalizedConfig);
    configForCache.__historyUserHash = sessionData.historyUserHash;
    this.decryptedCache.set(token, configForCache);
    this.dirty = true;

    try {
      const adapter = await getStorageAdapter();
      const ttlSeconds = this._calculateTtlSeconds();
      await adapter.set(token, sessionData, StorageAdapter.CACHE_TYPES.SESSION, ttlSeconds);
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

      const rawDecrypted = decryptUserConfig(stored.config);
      const { config: decryptedConfig } = stripSessionMetadata(rawDecrypted);
      if (decryptedConfig) {
        this.cache.set(token, stored);
        this.decryptedCache.set(token, cloneConfig(decryptedConfig));
        return cloneConfig(decryptedConfig);
      }
    } catch (_) { }
    return null;
  }

  async saveToDisk() { }
  async loadFromDisk() { }
  async restoreFromSnapshotIfStorageEmpty() { }
  startAutoSave() { }
  startMemoryCleanup() { }

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
