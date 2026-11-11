'use strict';

// Exercise the actual app event handlers without a browser, network, or config writes.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const test = require('node:test');
const vm = require('node:vm');

const modelSource = fs.readFileSync(path.join(__dirname, 'web/model.js'), 'utf8');
const appSource = fs.readFileSync(path.join(__dirname, 'web/app.js'), 'utf8');

function memoryStorage(initial = []) {
  const values = new Map(initial);
  return {
    get length() { return values.size; },
    key(index) { return [...values.keys()][index] ?? null; },
    getItem(key) { return values.get(String(key)) ?? null; },
    setItem(key, value) { values.set(String(key), String(value)); },
    removeItem(key) { values.delete(String(key)); },
    clear() { values.clear(); },
    entries() { return [...values.entries()]; },
  };
}

function fixture() {
  const config = {
    schemaVersion: 1,
    categories: [{id: 'phd', label: 'PhD', description: ''}],
    projects: [{id: 'project', categoryId: 'phd', parentId: null, label: 'Project', description: ''}],
    approaches: [], environments: [], assignments: [], overrides: {}, relations: [],
    migrations: [{
      id: 'migration', title: 'Migration', sourcePaths: [], targetPaths: [],
      stage: 'candidate', notes: '', consumerProjectIds: ['project'], adoptedProjectIds: [],
    }],
  };
  return {
    config,
    revision: 'revision-1',
    snapshot: {
      repoRoot: '/fixture', files: [], toolchain: 'fixture-toolchain', git: {},
      generatedAt: '2026-11-11T00:00:00Z', evidence: [], boards: [], warnings: [],
    },
  };
}

let harnessNumber = 0;
async function harness({state = fixture(), storage = memoryStorage(), session = memoryStorage()} = {}) {
  const documentEvents = new Map(), windowEvents = new Map(), requests = [], exports = [];
  const app = {innerHTML: ''};
  const toast = {textContent: '', classList: {add() {}, remove() {}}};
  const dialog = {open: false};
  const importer = {addEventListener() {}};
  const elements = {'#app': app, '#editor': dialog, '#toast': toast, '#config-import': importer};
  const document = {
    activeElement: null,
    querySelector(selector) { return elements[selector] ?? null; },
    addEventListener(name, callback) { documentEvents.set(name, callback); },
    createElement() { return {click() {}}; },
  };
  const number = ++harnessNumber;
  const context = {
    XYIN_DATA: structuredClone(state), console, structuredClone, document,
    location: {protocol: 'http:'},
    localStorage: storage, sessionStorage: session,
    crypto: {randomUUID() { return `session-${number}-1234-5678-000000000000`; }},
    setTimeout() {}, clearTimeout() {},
    URL: {createObjectURL() { return 'blob:fixture'; }, revokeObjectURL() {}},
    Blob: class { constructor(parts) { exports.push(JSON.parse(parts.join(''))); } },
    addEventListener(name, callback) { windowEvents.set(name, callback); },
    fetch(url, options = {}) {
      if (url === '/api/state') return Promise.resolve({ok: true, json: async () => structuredClone(state)});
      return new Promise(resolve => {
        const body = options.body ? JSON.parse(options.body) : null;
        requests.push({url, method: options.method, body, resolve});
      });
    },
  };
  context.window = context;
  context.globalThis = context;
  vm.createContext(context);
  vm.runInContext(modelSource, context);
  await vm.runInContext(appSource, context);
  return {
    app, requests, storage, session, exports, windowEvents,
    click(action, fields = {}) {
      return documentEvents.get('click')({target: {closest() { return {dataset: {action, ...fields}}; }}});
    },
    stage(value) {
      documentEvents.get('change')({target: {
        value, dataset: {stage: 'migration'}, matches(selector) { return selector === '[data-stage]'; },
      }});
    },
    async exported() {
      await this.click('export');
      return exports.at(-1);
    },
    finishSave(request, revision) {
      request.resolve({ok: true, json: async () => ({
        config: structuredClone(request.body.config), snapshot: state.snapshot, revision,
      })});
    },
  };
}

test('navigation cannot release another event\'s pending save; later edits survive its response', async () => {
  const h = await harness();
  h.stage('switching');
  const firstSave = h.click('save');
  assert.equal(h.requests.length, 1);
  assert.equal(h.requests[0].body.config.migrations[0].stage, 'switching');

  await h.click('view', {id: 'migrations'});
  const saveButton = h.app.innerHTML.match(/<button\b[^>]*data-action="save"[^>]*>/)?.[0];
  assert.ok(saveButton?.includes('disabled'), 'navigation must leave the pending save disabled');
  await h.click('save');
  assert.equal(h.requests.length, 1, 'even dispatched directly, a second save must wait');

  h.stage('complete');
  assert.equal((await h.exported()).migrations[0].stage, 'complete');
  h.finishSave(h.requests[0], 'revision-2');
  await firstSave;
  assert.equal((await h.exported()).migrations[0].stage, 'complete', 'old response must not replace new edits');
  assert.match(h.app.innerHTML, /Unsaved changes/);
  assert.ok(h.storage.entries().some(([, raw]) => {
    const value = JSON.parse(raw);
    return value.baseRevision === 'revision-2' && value.config?.migrations[0].stage === 'complete';
  }), 'the remaining draft must be persisted against the newly saved revision');

  const secondSave = h.click('save');
  assert.equal(h.requests.length, 2);
  assert.equal(h.requests[1].body.baseRevision, 'revision-2');
  assert.equal(h.requests[1].body.config.migrations[0].stage, 'complete');
  h.finishSave(h.requests[1], 'revision-3');
  await secondSave;
  assert.equal((await h.exported()).migrations[0].stage, 'complete');
  assert.doesNotMatch(h.app.innerHTML, /Unsaved changes/);
});

test('a save conflict preserves the edited configuration and does not advance its revision', async () => {
  const h = await harness();
  h.stage('preparing');
  const save = h.click('save');
  h.requests[0].resolve({ok: false, status: 409, json: async () => ({error: 'Configuration changed'})});
  await save;
  assert.equal((await h.exported()).migrations[0].stage, 'preparing');
  assert.match(h.app.innerHTML, /The configuration has changed in another window/);
  assert.match(h.app.innerHTML, /Unsaved changes/);
  assert.ok(h.storage.entries().some(([, raw]) => {
    const value = JSON.parse(raw);
    return value.baseRevision === 'revision-1' && value.config?.migrations[0].stage === 'preparing';
  }));
});

test('a stale own-session draft is archived and survives later editing and saving', async () => {
  const state = fixture();
  const oldConfig = structuredClone(state.config);
  oldConfig.categories[0].label = 'Unexported earlier work';
  oldConfig.migrations[0].stage = 'ready';
  const oldRaw = JSON.stringify({baseRevision: 'revision-0', config: oldConfig, at: '2026-11-10T00:00:00Z'});
  const session = memoryStorage([['xyin-progress-session', 'retained-session']]);
  const ownKey = 'xyin-progress-draft-v1:/fixture:retained-session';
  const storage = memoryStorage([[ownKey, oldRaw]]);
  const h = await harness({state, storage, session});

  assert.equal(storage.getItem(ownKey), null, 'the stale draft must leave the active key');
  const archived = storage.entries().find(([key, value]) => key.includes(':archive:') && value === oldRaw);
  assert.ok(archived, 'the exact stale draft must be retained in an independent archive');
  assert.match(h.app.innerHTML, /1 other or earlier draft is stored separately/);
  assert.equal((await h.exported()).categories[0].label, 'PhD', 'the old draft must not replace current configuration');

  h.stage('switching');
  assert.equal(storage.getItem(archived[0]), oldRaw, 'new edits must not replace the archive');
  const save = h.click('save');
  h.finishSave(h.requests[0], 'revision-2');
  await save;
  assert.equal(storage.getItem(ownKey), null, 'saving should clear only the current draft');
  assert.equal(storage.getItem(archived[0]), oldRaw, 'saving must preserve unexported historical work');
  await h.click('export-draft', {id: '0'});
  assert.equal(h.exports.at(-1).categories[0].label, 'Unexported earlier work');

  const nextState = {...state, config: h.requests[0].body.config, revision: 'revision-2'};
  const reopened = await harness({state: nextState, storage, session});
  assert.match(reopened.app.innerHTML, /1 other or earlier draft is stored separately/);
  await reopened.click('export-draft', {id: '0'});
  assert.equal(reopened.exports.at(-1).migrations[0].stage, 'ready');
});

test('different sessions retain independent drafts, and saving one leaves the other intact', async () => {
  const storage = memoryStorage();
  const aSession = memoryStorage([['xyin-progress-session', 'window-a']]);
  const bSession = memoryStorage([['xyin-progress-session', 'window-b']]);
  const a = await harness({storage, session: aSession});
  const b = await harness({storage, session: bSession});
  const aKey = 'xyin-progress-draft-v1:/fixture:window-a';
  const bKey = 'xyin-progress-draft-v1:/fixture:window-b';

  a.stage('preparing');
  b.stage('switching');
  assert.equal(JSON.parse(storage.getItem(aKey)).config.migrations[0].stage, 'preparing');
  assert.equal(JSON.parse(storage.getItem(bKey)).config.migrations[0].stage, 'switching');
  const bRaw = storage.getItem(bKey);
  const save = a.click('save');
  a.finishSave(a.requests[0], 'revision-2');
  await save;
  assert.equal(storage.getItem(aKey), null);
  assert.equal(storage.getItem(bKey), bRaw, 'saving A must not remove or overwrite B');
  assert.equal((await b.exported()).migrations[0].stage, 'switching');

  const nextState = {...fixture(), config: a.requests[0].body.config, revision: 'revision-2'};
  const reopened = await harness({state: nextState, storage, session: bSession});
  assert.match(reopened.app.innerHTML, /1 other or earlier draft is stored separately/);
  await reopened.click('export-draft', {id: '0'});
  assert.equal(reopened.exports.at(-1).migrations[0].stage, 'switching', 'B remains recoverable after server changes');
});
