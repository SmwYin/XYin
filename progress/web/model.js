(function (root) {
  'use strict';
  const STAGES = {candidate: 'Candidate', preparing: 'Preparing', ready: 'Target prepared', switching: 'Switching consumers', complete: 'Batch complete'};
  const RELATIONS = {alternative: 'Alternative', complementary: 'Complementary', mirror: 'Mirror / port', generalizes: 'Generalisation', specializes: 'Specialisation', equivalent_scope: 'Equivalent within scope', partial_integration: 'Partly integrated', unknown: 'Unconfirmed'};
  const ROLES = {active: 'Current', alternative: 'Alternative', reference: 'Reference', shared: 'Shared'};
  const ID = /^[A-Za-z0-9][A-Za-z0-9_-]*$/;
  const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
  const safePath = (value, glob = false) => typeof value === 'string' && value.length > 0 && value.length <= 1000 && !value.startsWith('/') && !value.includes('\\') && !/[\u0000-\u001f]/.test(value) && !value.split('/').some(p => p === '..' || p === '.' || p === '') && (value === 'XYin.lean' || value === 'XYinTest.lean' || value.startsWith('XYin/') || value.startsWith('XYinTest/')) && (glob || !/[?*\[\]]/.test(value));

  function validate(config) {
    const errors = [];
    if (!isObject(config)) return ['The configuration must be a JSON object.'];
    const arrays = ['categories', 'projects', 'approaches', 'environments', 'assignments', 'relations', 'migrations'];
    const fields = {categories:['id','label','description'],projects:['id','categoryId','parentId','label','description'],approaches:['id','projectId','label','description','environmentId','role','entryModules'],environments:['id','label','toolchain','note'],assignments:['id','pattern','projectId','approachId'],relations:['id','fromApproachId','toApproachId','kind','note'],migrations:['id','title','sourcePaths','targetPaths','stage','notes','consumerProjectIds','adoptedProjectIds']};
    const allowed = new Set(['schemaVersion', 'overrides', ...arrays]);
    for (const key of Object.keys(config)) if (!allowed.has(key)) errors.push(`Unknown configuration field: ${key}`);
    if (config.schemaVersion !== 1) errors.push('Only schemaVersion: 1 is supported.');
    for (const key of arrays) if (!Array.isArray(config[key]) || config[key].length > 10000) errors.push(`${key} must be an array with at most 10,000 entries.`);
    if (!isObject(config.overrides)) errors.push('overrides must be an object.');
    if (errors.length) return errors;
    const maps = {};
    for (const key of arrays) {
      maps[key] = new Map();
      for (const row of config[key]) {
        if (!isObject(row) || typeof row.id !== 'string' || !ID.test(row.id) || row.id.length > 100) { errors.push(`${key} contains an invalid ID.`); continue; }
        if (Object.keys(row).length !== fields[key].length || Object.keys(row).some(f=>!fields[key].includes(f))) errors.push(`${row.id}: required fields are missing or unknown fields are present.`);
        if (maps[key].has(row.id)) errors.push(`Duplicate ${key} ID: ${row.id}`);
        maps[key].set(row.id, row);
      }
    }
    if (errors.length) return errors;
    const string = (row, field, required = false) => {
      if (typeof row[field] !== 'string' || row[field].length > 10000 || (required && !row[field].trim())) errors.push(`${row.id}: ${field} must be ${required ? 'non-empty ' : ''}text of at most 10,000 characters.`);
    };
    const strings = (row, field) => {
      if (!Array.isArray(row[field]) || row[field].some(v => typeof v !== 'string')) { errors.push(`${row.id}: ${field} must be an array of strings.`); return []; }
      return row[field];
    };
    for (const row of [...config.categories, ...config.projects, ...config.approaches, ...config.environments]) string(row, 'label', true);
    for (const row of [...config.categories, ...config.projects, ...config.approaches]) string(row, 'description');
    for (const row of config.environments) { string(row, 'toolchain'); string(row, 'note'); }
    for (const row of config.projects) {
      if (!maps.categories.has(row.categoryId)) errors.push(`${row.id}: the category does not exist.`);
      if (row.parentId !== null) {
        const parent = maps.projects.get(row.parentId);
        if (!parent || parent.categoryId !== row.categoryId) errors.push(`${row.id}: the parent project must belong to the same category.`);
      }
      const seen = new Set([row.id]); let parent = maps.projects.get(row.parentId);
      while (parent) {
        if (seen.has(parent.id)) { errors.push(`${row.id}: the project hierarchy must not contain a cycle.`); break; }
        seen.add(parent.id); parent = maps.projects.get(parent.parentId);
      }
    }
    for (const row of config.approaches) {
      if (!maps.projects.has(row.projectId)) errors.push(`${row.id}: the project does not exist.`);
      if (!maps.environments.has(row.environmentId)) errors.push(`${row.id}: the environment does not exist.`);
      if (!Object.hasOwn(ROLES, row.role)) errors.push(`${row.id}: the approach role is invalid.`);
      const entries = strings(row, 'entryModules');
      if(entries.length > 1000) errors.push(`${row.id}: at most 1,000 entry modules are allowed.`);
      entries.forEach(v => { if (!/^[A-Za-z_][A-Za-z0-9_'.]*$/.test(v)) errors.push(`${row.id}: an entry module is invalid.`); });
    }
    const checkOwner = (row, label) => {
      if (!isObject(row)) { errors.push(`${label}: the assignment must be an object.`); return; }
      if (!maps.projects.has(row.projectId)) errors.push(`${label}: the project does not exist.`);
      if (row.approachId !== null && maps.approaches.get(row.approachId)?.projectId !== row.projectId) errors.push(`${label}: the approach must belong to the selected project.`);
    };
    for (const row of config.assignments) { if (!safePath(row.pattern, true)) errors.push(`${row.id}: the matching path is invalid.`); checkOwner(row, row.id); }
    if(Object.keys(config.overrides).length > 10000) errors.push('At most 10,000 manual overrides are allowed.');
    for (const [path, row] of Object.entries(config.overrides)) { if (!safePath(path) || !path.endsWith('.lean')) errors.push(`Invalid override path: ${path}`); if(isObject(row) && (Object.keys(row).length!==2 || Object.keys(row).some(k=>!['projectId','approachId'].includes(k)))) errors.push(`${path}: the assignment fields are invalid.`); checkOwner(row, path); }
    for (const row of config.relations) {
      if (!maps.approaches.has(row.fromApproachId) || !maps.approaches.has(row.toApproachId) || row.fromApproachId === row.toApproachId) errors.push(`${row.id}: a relationship must connect two different existing approaches.`);
      if (!Object.hasOwn(RELATIONS, row.kind)) errors.push(`${row.id}: the relationship type is invalid.`);
      string(row, 'note');
    }
    for (const row of config.migrations) {
      string(row, 'title', true); string(row, 'notes');
      if (!Object.hasOwn(STAGES, row.stage)) errors.push(`${row.id}: the migration stage is invalid.`);
      const sources=strings(row,'sourcePaths'), targets=strings(row,'targetPaths');
      if(sources.length>2000||targets.length>2000) errors.push(`${row.id}: source and target lists must each contain at most 2,000 files.`);
      for (const path of sources) if (!safePath(path)) errors.push(`${row.id}: a source path is invalid.`);
      for (const path of targets) if (!safePath(path) || !path.startsWith('XYin/ForMathlib/')) errors.push(`${row.id}: target paths must be within XYin/ForMathlib/.`);
      const consumers = strings(row, 'consumerProjectIds');
      const adopted = strings(row, 'adoptedProjectIds');
      if(consumers.length>10000||adopted.length>10000||new Set(consumers).size!==consumers.length||new Set(adopted).size!==adopted.length) errors.push(`${row.id}: project lists must contain unique IDs and at most 10,000 entries.`);
      if ([...consumers, ...adopted].some(id => !maps.projects.has(id))) errors.push(`${row.id}: a consumer project does not exist.`);
      if (adopted.some(id => !consumers.includes(id))) errors.push(`${row.id}: confirmed projects must be within this batch's consumer scope.`);
    }
    return errors;
  }

  const globCache = new Map();
  function matches(path, pattern) {
    let regex = globCache.get(pattern);
    if (!regex) {
      let expr = '';
      for (let i = 0; i < pattern.length; i++) {
        const c = pattern[i];
        if (c === '*' && pattern[i + 1] === '*') {
          if (pattern[i + 2] === '/') { expr += '(?:.*/)?'; i += 2; }
          else { expr += '.*'; i++; }
        } else if (c === '*') expr += '[^/]*';
        else if (c === '?') expr += '[^/]';
        else expr += c.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
      }
      regex = new RegExp(`^${expr}$`); globCache.set(pattern, regex);
    }
    return regex.test(path);
  }
  function assignment(config, path) {
    if (Object.hasOwn(config.overrides, path)) return {...config.overrides[path], manual: true};
    let result = {projectId: null, approachId: null, manual: false};
    for (const rule of config.assignments) if (matches(path, rule.pattern)) result = {projectId: rule.projectId, approachId: rule.approachId, manual: false, ruleId: rule.id};
    return result;
  }
  function descendants(config, projectId) {
    const result = new Set([projectId]); let changed = true;
    while (changed) { changed = false; for (const p of config.projects) if (result.has(p.parentId) && !result.has(p.id)) { result.add(p.id); changed = true; } }
    return result;
  }
  function projectFiles(config, snapshot, projectId) {
    const ids = descendants(config, projectId);
    return snapshot.files.filter(f => ids.has(assignment(config, f.path).projectId));
  }
  const closureCache = new WeakMap();
  function closures(snapshot) {
    if (closureCache.has(snapshot)) return closureCache.get(snapshot);
    const files = new Map(snapshot.files.map(f => [f.module, f])); const result = new Map();
    for (const file of snapshot.files) {
      const seen = new Set(); const pending = [...file.imports];
      while (pending.length) {
        const module = pending.pop(); if (seen.has(module)) continue;
        seen.add(module); if (files.has(module)) pending.push(...files.get(module).imports);
      }
      result.set(file.path, seen);
    }
    closureCache.set(snapshot, result); return result;
  }
  function adoption(config, snapshot, migration, projectId) {
    const byPath = new Map(snapshot.files.map(f => [f.path, f.module]));
    const sources = new Set(migration.sourcePaths.map(p => byPath.get(p)).filter(Boolean));
    const targets = new Set(migration.targetPaths.map(p => byPath.get(p)).filter(Boolean));
    const excluded = new Set([...migration.sourcePaths, ...migration.targetPaths]);
    let old = 0; let target = 0;
    for (const file of projectFiles(config, snapshot, projectId)) {
      if (excluded.has(file.path)) continue;
      const deps = closures(snapshot).get(file.path);
      if ([...sources].some(m => deps.has(m))) old++;
      if ([...targets].some(m => deps.has(m))) target++;
    }
    return {old, target, confirmed: migration.adoptedProjectIds.includes(projectId)};
  }
  function deletionIssue(config, kind, id) {
    if (kind === 'categories' && config.projects.some(p => p.categoryId === id)) return 'Move this category\'s projects to another category first.';
    if (kind === 'projects' && (config.projects.some(p => p.parentId === id) || config.approaches.some(a => a.projectId === id) || config.assignments.some(a => a.projectId === id) || Object.values(config.overrides).some(a => a.projectId === id) || config.migrations.some(m => m.consumerProjectIds.includes(id)))) return 'This project still has child projects, approaches, file rules or migration references. Update those assignments first.';
    if (kind === 'approaches' && (config.assignments.some(a => a.approachId === id) || Object.values(config.overrides).some(a => a.approachId === id) || config.relations.some(r => r.fromApproachId === id || r.toApproachId === id))) return 'This approach is still referenced by file assignments or approach relationships. Update those references first.';
    if (kind === 'environments' && config.approaches.some(a => a.environmentId === id)) return 'This environment is still used by an approach. Update the approach\'s environment first.';
    return null;
  }
  const api = {STAGES, RELATIONS, ROLES, validate, matches, assignment, descendants, projectFiles, adoption, deletionIssue, safePath};
  root.XYinModel = api;
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
})(globalThis);
