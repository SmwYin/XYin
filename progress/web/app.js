(async function () {
  'use strict';
  const M = window.XYinModel;
  const boot = window.XYIN_DATA;
  let config = structuredClone(boot.config), snapshot = boot.snapshot, revision = boot.revision;
  let savedConfig = JSON.stringify(config), connected = false, busy = false, pendingDrafts = [], conflict = false;
  let view = 'overview', categoryId = null, projectId = null, approachFilter = '', query = '', limit = 60;
  let selected = new Set(), undo = [];
  const app = document.querySelector('#app'), dialog = document.querySelector('#editor');
  const storageBase = `xyin-progress-draft-v1:${snapshot.repoRoot}`;
  let sessionId;
  try { sessionId=sessionStorage.getItem('xyin-progress-session'); if(!sessionId){sessionId=crypto.randomUUID();sessionStorage.setItem('xyin-progress-session',sessionId);} }
  catch (_) { sessionId=Date.now().toString(36)+'-'+Math.random().toString(36).slice(2); }
  const storageKey = `${storageBase}:${sessionId}`;
  const esc = value => String(value ?? '').replace(/[&<>"']/g, char => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[char]));
  const count = (value, singular, plural = singular + 's') => `${value} ${value === 1 ? singular : plural}`;
  const dirty = () => JSON.stringify(config) !== savedConfig;
  const find = (kind, id) => config[kind].find(row => row.id === id);
  const label = (kind, id) => find(kind, id)?.label || 'Uncategorised';
  const button = (text, action, attrs = '', variant = '') => `<button type="button" class="button ${variant}" data-action="${action}" ${attrs}>${text}</button>`;
  const badge = (text, color = 'muted') => `<span class="badge ${color}">${esc(text)}</span>`;
  const date = value => value ? new Date(value).toLocaleString('en-GB', {hour12:false, timeZone:'Europe/London'}) : 'Not recorded';
  const options = (items, value, empty = null) => `${empty === null ? '' : `<option value="">${esc(empty)}</option>`}${items.map(row => `<option value="${esc(row.id)}" ${row.id === value ? 'selected' : ''}>${esc(row.label)}</option>`).join('')}`;
  const newId = prefix => `${prefix}-${typeof crypto.randomUUID === 'function' ? crypto.randomUUID().slice(0,8) : Date.now().toString(36)}`;
  const fullProject = id => { const parts = []; let row = find('projects', id); const seen = new Set(); while (row && !seen.has(row.id)) { seen.add(row.id); parts.unshift(row.label); row = find('projects', row.parentId); } return parts.join(' / '); };
  const projectOptions = () => config.projects.map(row => ({id:row.id, label:`${label('categories', row.categoryId)} / ${fullProject(row.id)}`}));
  const notices = () => `${conflict ? `<div class="notice warning">The configuration has changed in another window. Export your draft before reloading the repository version.${button('Reload', 'reload-state', '', 'small')}</div>` : ''}${pendingDrafts.length ? `<div class="notice warning">${count(pendingDrafts.length, 'other or earlier draft')} ${pendingDrafts.length === 1 ? 'is' : 'are'} stored separately.${button('View retained drafts', 'drafts', '', 'small')}</div>` : ''}`;

  function toast(message) { const node = document.querySelector('#toast'); node.textContent = message; node.classList.add('show'); clearTimeout(toast.timer); toast.timer = setTimeout(() => node.classList.remove('show'), 4200); }
  function remember() {
    try {
      if (dirty()) localStorage.setItem(storageKey, JSON.stringify({baseRevision:revision,config,at:new Date().toISOString()}));
      else localStorage.removeItem(storageKey);
    } catch (_) { toast('Browser storage is unavailable. Use Export configuration to keep your changes.'); }
  }
  function update(mutator, message = 'Configuration draft updated') {
    const next = structuredClone(config); mutator(next);
    const errors = M.validate(next);
    if (errors.length) throw new Error(errors.slice(0,6).join('\n'));
    undo.push(config); if (undo.length > 20) undo.shift(); config = next;
    remember(); render(); toast(message);
  }
  async function api(path, method = 'GET', body) {
    const response = await fetch(path, {method, cache:'no-store', headers: body === undefined ? {} : {'Content-Type':'application/json'}, body:body === undefined ? undefined : JSON.stringify(body)});
    const data = await response.json();
    if (!response.ok) { if (response.status === 409) { conflict = true; render(); } throw new Error(data.error || data.message || `Request failed (${response.status})`); }
    return data;
  }
  function download(value, filename = 'config.json') {
    const url = URL.createObjectURL(new Blob([JSON.stringify(value,null,2)+'\n'], {type:'application/json'}));
    const anchor = document.createElement('a'); anchor.href=url; anchor.download=filename; anchor.click();
    setTimeout(() => URL.revokeObjectURL(url), 2000);
  }
  async function copy(value) {
    try { await navigator.clipboard.writeText(value); }
    catch (_) { const node=document.createElement('textarea'); node.value=value; document.body.append(node); node.select(); document.execCommand('copy'); node.remove(); }
    toast('Copied');
  }
  function title() { return ({overview:'Research and migration',catalog:projectId ? fullProject(projectId) : label('categories',categoryId),migrations:'ForMathlib migration',matrix:'Adoption matrix',evidence:'Evidence and records',settings:'Categories and relationships'})[view]; }
  function sidebar() {
    const nav = [['overview','◈','Overview'],['migrations','↗','ForMathlib migration'],['matrix','▦','Adoption matrix'],['evidence','◷','Evidence and records'],['settings','⚙','Configuration']];
    const tree = (parent, category, depth = 0) => config.projects.filter(p=>p.parentId===parent && p.categoryId===category).map(p=>`<div class="${depth ? 'tree-child' : 'tree-project'}"><button class="tree-row" data-action="project" data-id="${esc(p.id)}" ${projectId===p.id && view==='catalog'?'aria-current="page"':''}><span>${esc(p.label)}</span><span class="tree-count">${M.projectFiles(config,snapshot,p.id).length}</span></button>${tree(p.id,category,depth+1)}</div>`).join('');
    return `<aside class="sidebar"><div class="brand"><span class="brand-mark">χ</span><div class="brand-text">XYin<span>RESEARCH WORKSPACE</span></div></div><div class="sidebar-section">Workspace</div><nav aria-label="Workspace">${nav.map(([id,icon,text])=>`<button class="nav-item" data-action="view" data-id="${id}" ${view===id?'aria-current="page"':''}><span aria-hidden="true">${icon}</span>${text}</button>`).join('')}</nav><div class="sidebar-section">Repository categories ${button('+','edit','data-kind="categories"','quiet small')}</div><nav aria-label="Categories and projects">${config.categories.map(c=>`<div class="tree-category"><button class="tree-row" data-action="category" data-id="${esc(c.id)}" ${categoryId===c.id && !projectId && view==='catalog'?'aria-current="page"':''}><strong>${esc(c.label)}</strong><span>${config.projects.filter(p=>p.categoryId===c.id).length}</span></button>${tree(null,c.id)}</div>`).join('')}</nav><div class="sidebar-footer"><span class="status-dot"></span>${connected?'Local configuration service':'Offline snapshot'}<small>${esc(snapshot.toolchain)}<br>${esc(snapshot.git?.branch || 'Branch not recorded')} · ${esc(snapshot.git?.head?.slice(0,7)||'—')}</small></div></aside>`;
  }
  function render() {
    const focusId = document.activeElement?.id;
    const selection = typeof document.activeElement?.selectionStart === 'number' ? document.activeElement.selectionStart : null;
    app.innerHTML = `${sidebar()}<div class="workspace"><header class="topbar"><div class="breadcrumbs">XYin <span>/</span> ${esc(title())}</div><div class="toolbar"><span class="draft-indicator ${dirty()?'dirty':''}">${dirty()?'● Unsaved changes':'Configuration saved'}</span>${undo.length?button('Undo','undo','','quiet small'):''}${button('Refresh scan','refresh',`${busy||!connected?'disabled':''} title="Rescan source files and records locally; does not run Lean"`,'quiet small')}${button('Import','import','','quiet small')}${button('Export configuration','export','','small')}${button(connected?'Save to repository':'Offline · export to save','save',`${busy||!connected||!dirty()?'disabled':''} title="Writes only progress/config.json; export configuration when offline"`,'primary small')}</div></header><main id="main">${notices()}${({overview:overview,catalog:catalog,migrations:migrations,matrix:matrix,evidence:evidence,settings:settings})[view]()}</main><footer class="footer-note">Snapshot ${esc(date(snapshot.generatedAt))} · Categories and approaches are configuration-based · Lean files remain in place</footer></div>`;
    if (focusId) { const node=document.getElementById(focusId); if(node) {node.focus(); if(selection!==null && node.setSelectionRange) node.setSelectionRange(selection,selection);} }
  }
  function heading(eyebrow, text, description, actions = '') { return `<div class="page-heading"><div><div class="eyebrow">${esc(eyebrow)}</div><h1>${esc(text)}</h1><p class="lede">${esc(description)}</p></div><div class="heading-actions">${actions}</div></div>`; }
  function projectCard(project) {
    const files=M.projectFiles(config,snapshot,project.id), ids=M.descendants(config,project.id), approaches=config.approaches.filter(a=>ids.has(a.projectId));
    return `<button class="project-card" data-action="project" data-id="${esc(project.id)}"><div class="card-header"><span class="card-meta">${esc(label('categories',project.categoryId))}</span><span aria-hidden="true">↗</span></div><h3 class="card-title">${esc(project.label)}</h3><p class="card-description">${esc(project.description)}</p><div class="card-meta">${count(files.length, 'file')} <span>·</span> ${count(approaches.length, 'approach', 'approaches')}</div></button>`;
  }
  function overview() {
    const assigned=snapshot.files.filter(f=>M.assignment(config,f.path).projectId).length;
    const stats=[['Lean files',snapshot.files.length,`${assigned} assigned`],['Projects',config.projects.length,count(config.categories.length, 'category', 'categories')],['Approaches',config.approaches.length,count(config.relations.length, 'explicit relationship')],['Migrations',config.migrations.length,`${count(config.migrations.filter(m=>m.stage==='complete').length, 'batch', 'batches')} marked complete manually`]];
    return heading('LOCAL RESEARCH ATLAS','Your research, organised for reuse.','Explore projects and approaches, prepare shared implementations, and track adoption of ForMathlib.',button('Create migration','edit','data-kind="migrations"','primary'))+
      `<div class="stats-grid">${stats.map(([name,n,note])=>`<div class="stat-card"><div class="stat-label">${name}</div><div class="stat-number">${n}</div><div class="stat-note">${note}</div></div>`).join('')}</div><section class="panel"><div class="panel-header"><h2>Project map</h2>${button('Manage projects','view','data-id="settings"','quiet small')}</div><div class="panel-body project-grid">${config.projects.filter(p=>!p.parentId).map(projectCard).join('')}</div></section><div class="split-grid"><section class="panel"><div class="panel-header"><h2>Migration queue</h2>${button('View board →','view','data-id="migrations"','quiet small')}</div><div class="panel-body">${config.migrations.slice(0,4).map(m=>`<button class="relation-row" data-action="edit" data-kind="migrations" data-id="${esc(m.id)}"><span><strong>${esc(m.title)}</strong><small>${count(m.sourcePaths.length, 'source')} · ${count(m.consumerProjectIds.length, 'planned consumer')}</small></span>${badge(M.STAGES[m.stage],m.stage==='complete'?'green':'amber')}</button>`).join('')||empty('Select project files to create your first migration.')}</div></section><section class="panel"><div class="panel-header"><h2>Evidence and scope</h2>${button('View records →','view','data-id="evidence"','quiet small')}</div><div class="panel-body"><p>Mathematical progress, migration stages and build evidence are recorded separately. Parallel implementations keep their own entry points and environments.</p><div class="callout">${count(snapshot.evidence?.length||0, 'group of existing evidence', 'groups of existing evidence')}<br><small>Historical records do not certify the current build.</small></div>${!connected?`<p class="hint">You are viewing an offline snapshot. Edits are kept as a browser draft; export the configuration to bring it back to the repository.</p>${button('Copy local launch command','copy','data-value="python3 progress/server.py"','small')}`:''}</div></section></div>`;
  }
  function empty(text) { return `<div class="empty-state"><span aria-hidden="true">◇</span><p>${esc(text)}</p></div>`; }
  function catalog() {
    const project=find('projects',projectId), category=find('categories',categoryId);
    const scopeProjects=project ? M.descendants(config,project.id) : new Set(config.projects.filter(p=>p.categoryId===categoryId).map(p=>p.id));
    const allFiles=snapshot.files.filter(f=>scopeProjects.has(M.assignment(config,f.path).projectId));
    const approaches=config.approaches.filter(a=>scopeProjects.has(a.projectId));
    const files=allFiles.filter(f=>(!approachFilter||M.assignment(config,f.path).approachId===approachFilter) && (!query||`${f.path} ${f.module}`.toLowerCase().includes(query.toLowerCase())));
    const childProjects=config.projects.filter(p=>project?p.parentId===project.id:p.categoryId===categoryId&&!p.parentId);
    return heading(project?label('categories',project.categoryId):'REPOSITORY',project?.label||category?.label||'Project',project?.description||category?.description||'',`${button('Edit','edit',`data-kind="${project?'projects':'categories'}" data-id="${esc(project?.id||category?.id)}"`)} ${button('New project','edit',`data-kind="projects" data-parent="${esc(project?.id||'')}" data-category="${esc(project?.categoryId||category?.id)}"`)} ${project?button('New approach','edit',`data-kind="approaches" data-project="${esc(project.id)}"`,'primary'):''}`)+
      `${childProjects.length?`<div class="project-grid">${childProjects.map(projectCard).join('')}</div>`:''}<section class="panel"><div class="panel-header"><h2>Approaches and implementations <span class="count">${approaches.length}</span></h2><span class="hint">Edit relationships and assignments</span></div><div class="panel-body project-grid">${approaches.map(a=>`<article class="project-card"><div class="card-header">${badge(M.ROLES[a.role],a.role==='active'?'green':'muted')}${button('Edit','edit',`data-kind="approaches" data-id="${esc(a.id)}"`,'quiet small')}</div><h3>${esc(a.label)}</h3><p class="card-description">${esc(a.description)}</p><div class="card-meta">${esc(label('environments',a.environmentId))} · ${count(allFiles.filter(f=>M.assignment(config,f.path).approachId===a.id).length, 'file')}</div>${button('View files','filter-approach',`data-id="${esc(a.id)}"`,'quiet small')}</article>`).join('')||empty('No approaches yet. Create one, then assign files to it.')}</div></section>${renderRelations(approaches.map(a=>a.id))}<section class="panel"><div class="panel-header"><h2>File browser <span class="count">${files.length}</span></h2><div class="inline-actions">${button(`Assign selected (${selected.size})`,'assign-selected',selected.size?'':'disabled','small')}${button('Create migration','migration-selected',selected.size?'':'disabled','small')}</div></div><div class="filters"><input id="file-search" class="search" type="search" placeholder="Search files or modules…" value="${esc(query)}" aria-label="Search files"><select id="approach-filter" aria-label="Filter approaches">${options(approaches,approachFilter,'All approaches')}</select><span class="hint">${selected.size?'Selected '+count(selected.size, 'item'):'Select files to assign them together'}</span></div><div class="table-wrap"><table><thead><tr><th><input id="select-visible" type="checkbox" aria-label="Select all displayed files" ${files.slice(0,limit).length&&files.slice(0,limit).every(f=>selected.has(f.path))?'checked':''}></th><th>File / module</th><th>Project and approach</th><th>Assignment source</th><th></th></tr></thead><tbody>${files.slice(0,limit).map(f=>{const a=M.assignment(config,f.path);return `<tr><td><input type="checkbox" data-file-select="${esc(f.path)}" aria-label="Select ${esc(f.path)}" ${selected.has(f.path)?'checked':''}></td><td><button class="source-link" data-action="file" data-id="${esc(f.path)}">${esc(f.path.split('/').pop())}</button><div class="path">${esc(f.path)}</div></td><td>${esc(fullProject(a.projectId))}<small>${a.approachId?esc(label('approaches',a.approachId)):'No approach assigned'}</small></td><td>${badge(a.manual?'Manual override':'Matching rules',a.manual?'blue':'muted')}</td><td>${button('Assign','assign',`data-id="${esc(f.path)}"`,'quiet small')}</td></tr>`;}).join('')}</tbody></table></div>${!files.length?empty('No matching files. This category may remain empty until needed.'):''}${files.length>limit?`<div class="panel-body">${button(`Show ${Math.min(60,files.length-limit)} more`,'more','','small')}</div>`:''}</section>`;
  }
  function renderRelations(ids = null) {
    const rows=config.relations.filter(r=>!ids||ids.includes(r.fromApproachId)||ids.includes(r.toApproachId));
    return `<section class="panel"><div class="panel-header"><h2>Approach relationships</h2>${button('Add relationship','edit','data-kind="relations"','small')}</div><div class="panel-body">${rows.map(r=>`<div class="relation-row"><div><strong>${esc(label('approaches',r.fromApproachId))} <span class="relation-arrow">→</span> ${esc(label('approaches',r.toApproachId))}</strong><p>${esc(r.note)}</p></div><div class="inline-actions">${badge(M.RELATIONS[r.kind],'blue')}${button('Edit','edit',`data-kind="relations" data-id="${esc(r.id)}"`,'quiet small')}</div></div>`).join('')||empty('Relationships are explicitly recorded, rather than inferred from directory names.')}</div></section>`;
  }
  function migrations() {
    return heading('FORMATHLIB PIPELINE','Build a shared foundation, one migration at a time.','Stages are recorded manually. Actual imports and build evidence are shown separately; other experiments can remain in place.',button('New migration','edit','data-kind="migrations"','primary'))+
      `<div class="kanban">${Object.entries(M.STAGES).map(([stage,text])=>{const rows=config.migrations.filter(m=>m.stage===stage);return `<section class="kanban-column"><div class="column-heading"><h2>${text}</h2><span>${rows.length}</span></div>${rows.map(m=>`<article class="migration-card"><div class="card-header"><span class="eyebrow">${esc(m.id)}</span>${button('Edit','edit',`data-kind="migrations" data-id="${esc(m.id)}"`,'quiet small')}</div><h3>${esc(m.title)}</h3><p>${esc(m.notes)}</p><div class="migration-paths"><small>Source</small>${m.sourcePaths.map(p=>`<div class="path">${esc(p)}</div>`).join('')}<small>ForMathlib targets</small>${m.targetPaths.map(p=>`<div class="path">${esc(p)}</div>`).join('')||'<span class="hint">Location to be decided</span>'}</div><div class="card-meta">${m.adoptedProjectIds.length} / ${count(m.consumerProjectIds.length, 'consumer')} confirmed manually</div><label class="hint" for="stage-${esc(m.id)}">Change stage</label><select id="stage-${esc(m.id)}" data-stage="${esc(m.id)}">${options(Object.entries(M.STAGES).map(([id,label])=>({id,label})),m.stage)}</select></article>`).join('')||'<div class="empty-column">No entries yet</div>'}</section>`;}).join('')}</div><div class="notice">A migration may cover several modules. The target implementation should depend only on Mathlib / ForMathlib. Selected consumers should have switched, with relevant build evidence. This interface does not move files or change imports.</div>`;
  }
  function matrix() {
    const ids=new Set(config.migrations.flatMap(m=>m.consumerProjectIds));
    const projects=config.projects.filter(p=>ids.has(p.id));
    return heading('ADOPTION MATRIX','Which projects use the shared implementation?','Direct and transitive imports are scanned statically. Manual confirmations are separate; an undetected import does not rule out a mathematical dependency.',button('Manage migration scope','view','data-id="migrations"'))+
      `<section class="panel"><div class="table-wrap"><table><thead><tr><th>Migrations</th>${projects.map(p=>`<th>${esc(fullProject(p.id))}</th>`).join('')}</tr></thead><tbody>${config.migrations.map(m=>`<tr><td><button class="source-link" data-action="edit" data-kind="migrations" data-id="${esc(m.id)}">${esc(m.title)}</button><small>${M.STAGES[m.stage]}</small></td>${projects.map(p=>{if(!m.consumerProjectIds.includes(p.id))return '<td class="matrix-cell">—</td>';const a=M.adoption(config,snapshot,m,p.id);return `<td class="matrix-cell">${badge(a.old&&a.target?'Both implementations':a.target?'Uses target':a.old?'Uses source':'Not detected',a.old&&a.target?'amber':a.target?'green':a.old?'blue':'muted')}<small>Source ${a.old} · Target ${a.target}</small>${a.confirmed?badge('Manually confirmed','blue'):''}</td>`;}).join('')}</tr>`).join('')}</tbody></table></div>${!config.migrations.length?empty('Create a migration and select its consumer projects first.'):''}</section><p class="hint">Counts show files importing each implementation, including transitive imports and excluding the source and target files themselves. These are adoption counts, not build results.</p>`;
  }
  function evidence() {
    return heading('EVIDENCE & SNAPSHOTS','Keep the evidence behind every status.','Existing records retain their scope, environment and date. The scan does not run Lean.')+
      `<div class="stats-grid"><div class="stat-card"><div class="stat-label">Source snapshot</div><div class="stat-number">${snapshot.files.length}</div><div class="stat-note">${esc(date(snapshot.generatedAt))}</div></div><div class="stat-card"><div class="stat-label">Current toolchain</div><div class="stat-value mono">${esc(snapshot.toolchain)}</div><div class="stat-note">Independent environments are listed separately</div></div><div class="stat-card"><div class="stat-label">Historical evidence groups</div><div class="stat-number">${snapshot.evidence?.length||0}</div><div class="stat-note">Does not certify the current version</div></div></div>${(snapshot.warnings||[]).map(w=>`<div class="notice warning">${esc(w)}</div>`).join('')}<div class="split-grid">${(snapshot.boards||[]).map(b=>`<section class="panel"><div class="panel-header"><h2>${esc(b.label)}</h2>${badge('Task record totals','blue')}</div><div class="panel-body"><div class="inline-actions">${Object.entries(b.counts).map(([name,n])=>badge(`${name} · ${n}`)).join('')}</div><p class="hint">Statuses come from task records, not a fresh proof or build check.</p><div class="path">${esc(b.sourcePath)}</div>${button('Copy record path','copy',`data-value="${esc(snapshot.repoRoot+'/'+b.sourcePath)}"`,'quiet small')}</div></section>`).join('')}</div>${(snapshot.evidence||[]).map(e=>`<section class="panel evidence-card"><div class="panel-header"><h2>${esc(e.label)}</h2>${badge('Historical record','amber')}</div><div class="panel-body"><p>${esc(e.summary)}</p><div class="detail-grid"><div><div class="detail-label">Recorded at</div>${esc(date(e.date))}</div><div><div class="detail-label">Environment</div>${esc(label('environments',e.environmentId))}</div><div><div class="detail-label">Recorded status</div>${esc(e.status)}</div><div><div class="detail-label">Recorded scope</div>${count(e.scope?.length||0, 'file')}</div></div><details><summary>View recorded scope</summary><div class="dependency-list">${(e.scope||[]).map(p=>`<div class="path">${esc(p)}</div>`).join('')}</div></details><div class="path">${esc(e.sourcePath)}</div>${button('Copy evidence path','copy',`data-value="${esc(snapshot.repoRoot+'/'+e.sourcePath)}"`,'quiet small')}</div></section>`).join('')}`;
  }
  function settings() {
    const rows=(kind,display)=>config[kind].map(row=>`<tr><td><strong>${esc(row.label||row.pattern)}</strong><small>${esc(row.id)}</small></td><td>${display(row)}</td><td class="row-actions">${button('Edit','edit',`data-kind="${kind}" data-id="${esc(row.id)}"`,'quiet small')}${button('Delete','delete',`data-kind="${kind}" data-id="${esc(row.id)}"`,'quiet small')}</td></tr>`).join('');
    const section=(kind,name,display)=>`<section class="panel"><div class="panel-header"><h2>${name} <span class="count">${config[kind].length}</span></h2>${button('New','edit',`data-kind="${kind}"`,'small')}</div><div class="table-wrap"><table><thead><tr><th>Name / stable ID</th><th>Assignment and description</th><th>Actions</th></tr></thead><tbody>${rows(kind,display)}</tbody></table></div></section>`;
    const unmapped=snapshot.files.filter(f=>!M.assignment(config,f.path).projectId);
    return heading('CONFIGURATION','Organise the structure. Keep files in place.','Edit categories, projects, approaches, environments and matching rules. Rules are applied in order; the last match wins. Individual file overrides take precedence.',button('Export configuration','export','','primary'))+
      `<div class="notice ${unmapped.length?'warning':'success'}">${unmapped.length?`${count(unmapped.length, 'file')} ${unmapped.length === 1 ? 'needs' : 'need'} categorising`:'All scanned files are assigned to a project'} · ${count(Object.keys(config.overrides).length, 'manual override')} · ${dirty()?'Changes have not been saved to the configuration file':'The view matches the loaded configuration'}</div>${unmapped.length?`<section class="panel"><div class="panel-body">${unmapped.map(f=>`<div class="relation-row"><span class="path">${esc(f.path)}</span>${button('Categorise','assign',`data-id="${esc(f.path)}"`,'small')}</div>`).join('')}</div></section>`:''}`+
      section('categories','Repository categories',r=>esc(r.description))+
      section('projects','Projects',r=>`${badge(label('categories',r.categoryId),'blue')} ${r.parentId?esc(fullProject(r.parentId)):'Top-level project'}<p>${esc(r.description)}</p>`)+
      section('approaches','Approaches',r=>`${esc(fullProject(r.projectId))} · ${esc(label('environments',r.environmentId))}<p>${esc(r.description)}</p>`)+renderRelations()+
      section('environments','Environments',r=>`<span class="mono">${esc(r.toolchain)}</span><p>${esc(r.note)}</p>`)+
      section('assignments','File matching rules',r=>`${esc(fullProject(r.projectId))}<small>${r.approachId?esc(label('approaches',r.approachId)):'No approach assigned'}</small>`)+
      `<section class="panel"><div class="panel-header"><h2>Individual file overrides</h2></div><div class="panel-body">${Object.entries(config.overrides).map(([path,o])=>`<div class="relation-row"><div><span class="path">${esc(path)}</span><small>${esc(fullProject(o.projectId))} · ${o.approachId?esc(label('approaches',o.approachId)):'No approach assigned'}</small></div>${button('Use matching rules','clear-override',`data-id="${esc(path)}"`,'quiet small')}</div>`).join('')||'<p class="hint">Select files in a project and choose Assign selected to create overrides.</p>'}</div></section>`;
  }

  const input = (name, text, value, extra = '') => `<div class="field"><label for="field-${name}">${esc(text)}</label><input id="field-${name}" name="${name}" value="${esc(value)}" ${extra}></div>`;
  const textarea = (name,text,value,hint='') => `<div class="field full"><label for="field-${name}">${esc(text)}</label><textarea id="field-${name}" name="${name}" rows="3">${esc(value)}</textarea>${hint?`<small class="hint">${esc(hint)}</small>`:''}</div>`;
  const select = (name,text,items,value,emptyLabel=null) => `<div class="field"><label for="field-${name}">${esc(text)}</label><select id="field-${name}" name="${name}">${options(items,value,emptyLabel)}</select></div>`;
  function openDialog(title, body, onSubmit = null, submitText = 'Apply changes') {
    dialog.innerHTML=`<form id="editor-form"><div class="modal-header"><h2 id="dialog-title">${esc(title)}</h2><button type="button" class="button quiet" data-action="close" aria-label="Close dialogue">×</button></div><div class="modal-body">${body}<div id="form-error" class="form-error" role="alert"></div></div><div class="modal-footer">${button('Cancel','close','','quiet')}${onSubmit?`<button type="submit" class="button primary">${esc(submitText)}</button>`:''}</div></form>`;
    dialog.querySelector('form').onsubmit=async event=>{event.preventDefault();try{await onSubmit(new FormData(event.target));dialog.close();}catch(error){dialog.querySelector('#form-error').textContent=error.message;}};
    if (!dialog.open) dialog.showModal();
  }
  function confirmAction(title, message, callback, text = 'Confirm') { openDialog(title,`<p>${esc(message)}</p>`,callback,text); }
  function draftDialog() {
    openDialog('Retained configuration drafts',`<p class="hint">These drafts are stored separately. Editing or saving this configuration will not overwrite them. After loading a draft, save it explicitly. Other windows may still be editing.</p>${pendingDrafts.map((d,i)=>`<div class="relation-row"><div><strong>${esc(date(d.at))}</strong><small>Based on revision ${esc(d.baseRevision?.slice(0,8)||'Unknown')}</small></div><div class="inline-actions">${button('Export','export-draft',`data-id="${i}"`,'small')}${button('Load','load-draft',`data-id="${i}"`,'small')}${button('Delete','delete-draft',`data-id="${i}"`,'quiet small')}</div></div>`).join('')}`);
  }
  function edit(kind, id, defaults = {}) {
    const existing=find(kind,id);
    const defaultProject=defaults.project || projectId || config.projects[0]?.id || '';
    const data=existing || ({categories:{id:newId('category'),label:'',description:''},projects:{id:newId('project'),label:'',description:'',categoryId:defaults.category||categoryId||config.categories[0]?.id||'',parentId:defaults.parent||null},approaches:{id:newId('approach'),label:'',description:'',projectId:defaultProject,environmentId:config.environments[0]?.id||'',role:'active',entryModules:[]},environments:{id:newId('env'),label:'',toolchain:'',note:''},relations:{id:newId('relation'),fromApproachId:config.approaches.find(a=>a.projectId===defaultProject)?.id||config.approaches[0]?.id||'',toApproachId:config.approaches[1]?.id||'',kind:'unknown',note:''},assignments:{id:newId('rule'),pattern:'',projectId:defaultProject,approachId:null},migrations:{id:newId('migration'),title:'',sourcePaths:defaults.paths||[],targetPaths:[],stage:'candidate',notes:'',consumerProjectIds:[],adoptedProjectIds:[]}})[kind];
    const kindLabels={categories:'Category',projects:'Project',approaches:'Approach',environments:'Environment',relations:'Approach relationship',assignments:'File matching rule',migrations:'Migration'};
    if (!data) return;
    let fields=input('id','Stable ID',data.id,'required pattern="[A-Za-z0-9][A-Za-z0-9_-]*" '+(existing?'readonly':''));
    if (['categories','projects','approaches','environments'].includes(kind)) fields+=input('label','Display name',data.label,'required');
    if (kind==='projects') fields+=select('categoryId','Category',config.categories,data.categoryId)+select('parentId','Parent project',projectOptions().filter(p=>!M.descendants(config,data.id).has(p.id)),data.parentId,'None · top-level project');
    if (kind==='approaches') fields+=select('projectId','Project',projectOptions(),data.projectId)+select('environmentId','Environment',config.environments,data.environmentId)+select('role','Approach role',Object.entries(M.ROLES).map(([id,label])=>({id,label})),data.role)+textarea('entryModules','Build entry modules',data.entryModules.join('\n'),'One module per line. Recording an entry does not start a build.');
    if (['categories','projects','approaches'].includes(kind)) fields+=textarea('description','Description and scope',data.description);
    if (kind==='environments') fields+=input('toolchain','Lean toolchain',data.toolchain)+textarea('note','Environment notes',data.note,'Record dependency versions or an independent workspace. This is not a verification claim.');
    if (kind==='assignments') fields+=input('pattern','Path pattern',data.pattern,'required placeholder="XYin/PhD/Example/**"')+select('projectId','Project',projectOptions(),data.projectId)+select('approachId','Approach',config.approaches.filter(a=>a.projectId===data.projectId),data.approachId,'Unassigned')+'<p class="hint full">* matches within one path component; ** matches across components. New rules are appended and override earlier matches. Individual file overrides still take precedence.</p>';
    if (kind==='relations') {
      const items=config.approaches.map(a=>({id:a.id,label:`${fullProject(a.projectId)} / ${a.label}`}));
      fields+=select('fromApproachId','From approach',items,data.fromApproachId)+select('toApproachId','To approach',items,data.toApproachId)+select('kind','Relationship type',Object.entries(M.RELATIONS).map(([id,label])=>({id,label})),data.kind)+textarea('note','Relationship notes and assumptions',data.note,'Generalisation, specialisation and partial integration read from the first approach to the second. Specify the scope of any equivalence.');
    }
    if (kind==='migrations') {
      fields+=input('title','Migration title',data.title,'required')+select('stage','Manually recorded stage',Object.entries(M.STAGES).map(([id,label])=>({id,label})),data.stage)+textarea('sourcePaths','Source files',data.sourcePaths.join('\n'),'One repository-relative path per line. You can also select files in a project before creating a migration.')+textarea('targetPaths','ForMathlib target files',data.targetPaths.join('\n'),'One path under XYin/ForMathlib/ per line. Planned files need not exist yet.')+textarea('notes','Migration notes / outstanding work',data.notes)+`<div class="field full"><label>Batch consumers and manual confirmations</label><p class="hint">Select projects for this batch on the left and record manual confirmations on the right. These do not replace import scans or build evidence.</p><div class="checkbox-list">${projectOptions().map(p=>`<div class="check-row"><label><input type="checkbox" name="consumerProjectIds" value="${esc(p.id)}" ${data.consumerProjectIds.includes(p.id)?'checked':''}>${esc(p.label)}</label><label><input type="checkbox" name="adoptedProjectIds" value="${esc(p.id)}" ${data.adoptedProjectIds.includes(p.id)?'checked':''} ${!data.consumerProjectIds.includes(p.id)?'disabled':''}>Switch confirmed</label></div>`).join('')}</div></div>`;
    }
    openDialog(`${existing?'Edit':'New'} ${kindLabels[kind].toLowerCase()}`,`<div class="form-grid">${fields}</div>${existing&&['relations','migrations'].includes(kind)?button('Delete entry','delete',`data-kind="${kind}" data-id="${esc(id)}"`,'quiet small'):''}`,form=>{
      const next={id:String(form.get('id')).trim()};
      const get=name=>String(form.get(name)||'').trim();
      const lines=name=>get(name).split(/\r?\n/).map(x=>x.trim()).filter(Boolean);
      if (['categories','projects','approaches','environments'].includes(kind)) next.label=get('label');
      if (['categories','projects','approaches'].includes(kind)) next.description=get('description');
      if (kind==='projects') Object.assign(next,{categoryId:get('categoryId'),parentId:get('parentId')||null});
      if (kind==='approaches') Object.assign(next,{projectId:get('projectId'),environmentId:get('environmentId'),role:get('role'),entryModules:lines('entryModules')});
      if (kind==='environments') Object.assign(next,{toolchain:get('toolchain'),note:get('note')});
      if (kind==='relations') Object.assign(next,{fromApproachId:get('fromApproachId'),toApproachId:get('toApproachId'),kind:get('kind'),note:get('note')});
      if (kind==='assignments') Object.assign(next,{pattern:get('pattern'),projectId:get('projectId'),approachId:get('approachId')||null});
      if (kind==='migrations') Object.assign(next,{title:get('title'),sourcePaths:lines('sourcePaths'),targetPaths:lines('targetPaths'),stage:get('stage'),notes:get('notes'),consumerProjectIds:form.getAll('consumerProjectIds'),adoptedProjectIds:form.getAll('adoptedProjectIds')});
      update(draft=>{
        if(existing) draft[kind][draft[kind].findIndex(row=>row.id===id)]=next; else draft[kind].push(next);
        if(kind==='projects'&&existing&&existing.categoryId!==next.categoryId) for(const child of draft.projects) if(M.descendants(config,id).has(child.id)) child.categoryId=next.categoryId;
        if(kind==='approaches'&&existing&&existing.projectId!==next.projectId) {
          for(const rule of draft.assignments) if(rule.approachId===id) rule.projectId=next.projectId;
          for(const owner of Object.values(draft.overrides)) if(owner.approachId===id) owner.projectId=next.projectId;
        }
      });
    });
    if(kind==='assignments') dialog.querySelector('[name=projectId]').onchange=event=>{dialog.querySelector('[name=approachId]').innerHTML=options(config.approaches.filter(a=>a.projectId===event.target.value),null,'Unassigned');};
    if(kind==='migrations') for(const checkbox of dialog.querySelectorAll('[name=consumerProjectIds]')) checkbox.onchange=()=>{const adopted=[...dialog.querySelectorAll('[name=adoptedProjectIds]')].find(node=>node.value===checkbox.value); adopted.disabled=!checkbox.checked; if(!checkbox.checked)adopted.checked=false;};
  }
  function assign(paths) {
    if(!paths.length)return;
    const old=M.assignment(config,paths[0]);
    const p=old.projectId||projectId||config.projects[0]?.id;
    openDialog(`Assign ${count(paths.length, 'file')}`,`<p class="hint">Only configuration assignments change. File paths and Lean contents remain unchanged.</p><details><summary>Selected files</summary>${paths.map(path=>`<div class="path">${esc(path)}</div>`).join('')}</details><div class="form-grid">${select('projectId','Target project',projectOptions(),p)}${select('approachId','Target approach',config.approaches.filter(a=>a.projectId===p),old.approachId,'Unassigned')}</div>`,form=>{
      const owner={projectId:String(form.get('projectId')),approachId:String(form.get('approachId')||'')||null};
      update(draft=>{for(const path of paths)draft.overrides[path]=owner;},'Assignments updated; source files have not moved'); selected.clear();render();
    });
    dialog.querySelector('[name=projectId]').onchange=event=>{dialog.querySelector('[name=approachId]').innerHTML=options(config.approaches.filter(a=>a.projectId===event.target.value),null,'Unassigned');};
  }
  function fileDetails(path) {
    const file=snapshot.files.find(f=>f.path===path); if(!file)return;
    const owner=M.assignment(config,path), dependents=snapshot.files.filter(f=>f.imports.includes(file.module));
    openDialog(file.path.split('/').pop(),`<div class="path">${esc(path)}</div><div class="detail-grid"><div><div class="detail-label">Project</div>${esc(fullProject(owner.projectId))}</div><div><div class="detail-label">Approach</div>${owner.approachId?esc(label('approaches',owner.approachId)):'Unassigned'}</div><div><div class="detail-label">Lines</div>${file.lines}</div><div><div class="detail-label">Assignment basis</div>${owner.manual?'Manual override':esc(owner.ruleId||'Uncategorised')}</div></div><p class="mono path">${esc(file.sha256)}</p><div class="inline-actions">${button('Copy file path','copy',`data-value="${esc(snapshot.repoRoot+'/'+path)}"`,'small')}${button('Copy module name','copy',`data-value="${esc(file.module)}"`,'small')}${button('Assign','assign',`data-id="${esc(path)}"`,'small')}</div><h3>Direct imports</h3><div class="dependency-list">${file.imports.map(m=>`<div class="path">${esc(m)}</div>`).join('')||'None'}</div><h3>Direct consumers · ${dependents.length}</h3><div class="dependency-list">${dependents.map(f=>`<div class="path">${esc(f.path)}</div>`).join('')||'No direct consumers in the current scan'}</div><p class="hint">This is a source scan; it does not establish build or proof status.</p>`);
  }
  async function loadState(discard = false) {
    const state=await api('/api/state');
    const errors=M.validate(state.config);if(errors.length)throw new Error(errors.join('\n'));
    snapshot=state.snapshot;
    if(discard){config=state.config;revision=state.revision;savedConfig=JSON.stringify(config);undo=[];conflict=false;localStorage.removeItem(storageKey);selected.clear();}
    connected=true;render();
  }
  document.addEventListener('click',async event=>{
    const target=event.target.closest('[data-action]');if(!target)return;
    const {action,id,kind}=target.dataset;
    let ownsBusy = false;
    try {
      if(action==='view'){view=id;categoryId=null;projectId=null;selected.clear();query='';approachFilter='';render();}
      else if(action==='category'||action==='project'){view='catalog';projectId=action==='project'?id:null;categoryId=action==='category'?id:find('projects',id).categoryId;selected.clear();query='';approachFilter='';limit=60;render();}
      else if(action==='edit')edit(kind,id,target.dataset);
      else if(action==='close')dialog.close();
      else if(action==='file')fileDetails(id);
      else if(action==='copy')await copy(target.dataset.value);
      else if(action==='filter-approach'){approachFilter=id;limit=60;render();document.querySelector('#file-search')?.scrollIntoView({block:'center'});}
      else if(action==='more'){limit+=60;render();}
      else if(action==='assign')assign([id]);
      else if(action==='assign-selected')assign([...selected]);
      else if(action==='migration-selected')edit('migrations',null,{paths:[...selected]});
      else if(action==='export'){download(config);toast('Configuration exported. Exporting does not write back to the repository.');}
      else if(action==='drafts')draftDialog();
      else if(action==='export-draft')download(pendingDrafts[Number(id)].config,'config-recovered-draft.json');
      else if(action==='load-draft'){
        const draft=pendingDrafts[Number(id)];
        confirmAction('Load retained draft','This replaces the current draft and can be undone. The backup is retained. Review differences from the repository version before saving.',()=>{update(next=>{for(const key of Object.keys(next))delete next[key];Object.assign(next,structuredClone(draft.config));});view='overview';projectId=null;categoryId=null;render();},'Load draft');
      }
      else if(action==='delete-draft'){
        const draft=pendingDrafts[Number(id)];
        confirmAction('Delete retained draft','Delete only this browser draft backup. Export anything you want to retain first.',()=>{if(localStorage.getItem(draft.storageKey)!==draft.raw)throw new Error('This draft has changed in another window. Reload the page to review its latest contents.');localStorage.removeItem(draft.storageKey);pendingDrafts=pendingDrafts.filter(d=>d!==draft);render();},'Delete backup');
      }
      else if(action==='import')document.querySelector('#config-import').click();
      else if(action==='undo'){if(undo.length){config=undo.pop();remember();render();toast('Last configuration change undone');}}
      else if(action==='clear-override')update(draft=>delete draft.overrides[id]);
      else if(action==='delete'){
        const issue=M.deletionIssue(config,kind,id);if(issue)throw new Error(issue);
        confirmAction('Delete configuration entry',`Delete the configuration entry “${find(kind,id)?.label||id}”. No Lean files will be deleted.`,()=>update(draft=>{draft[kind]=draft[kind].filter(row=>row.id!==id);}), 'Delete entry');
      }
      else if(action==='save'){
        if(!connected||busy)return;busy=true;ownsBusy=true;render();
        const submitted=structuredClone(config), submittedText=JSON.stringify(submitted);
        const state=await api('/api/config','PUT',{config:submitted,baseRevision:revision});
        const hasNewEdits=JSON.stringify(config)!==submittedText;
        revision=state.revision;if(!hasNewEdits)config=state.config;snapshot=state.snapshot;savedConfig=JSON.stringify(state.config);conflict=false;remember();toast(hasNewEdits?'Submitted configuration saved; later edits remain in your draft':'Configuration saved to progress/config.json');
      }
      else if(action==='refresh'){
        if(!connected||busy)return;busy=true;ownsBusy=true;render();const state=await api('/api/refresh','POST',{});snapshot=state.snapshot;
        if(state.revision!==revision){if(dirty()){conflict=true;toast('Repository configuration changed; your current draft is retained.');}else{config=state.config;revision=state.revision;savedConfig=JSON.stringify(config);}}
        else toast('Files and historical records refreshed; Lean was not run');
      }
      else if(action==='reload-state')confirmAction('Reload repository configuration','Your unsaved draft will be replaced. Export it first to retain your changes.',()=>loadState(true),'Load repository version');
    }catch(error){toast(error.message);}
    finally{if(ownsBusy){busy=false;render();}}
  });
  document.addEventListener('change',event=>{
    const target=event.target;
    try{
      if(target.matches('[data-file-select]')){if(target.checked)selected.add(target.dataset.fileSelect);else selected.delete(target.dataset.fileSelect);render();}
      else if(target.id==='select-visible'){for(const checkbox of document.querySelectorAll('[data-file-select]'))if(target.checked)selected.add(checkbox.dataset.fileSelect);else selected.delete(checkbox.dataset.fileSelect);render();}
      else if(target.id==='approach-filter'){approachFilter=target.value;limit=60;render();}
      else if(target.matches('[data-stage]'))update(draft=>{draft.migrations.find(m=>m.id===target.dataset.stage).stage=target.value;},'Manually recorded stage updated');
    }catch(error){toast(error.message);render();}
  });
  document.addEventListener('input',event=>{if(event.target.id==='file-search'){query=event.target.value;limit=60;render();}});
  document.querySelector('#config-import').addEventListener('change',async event=>{
    const file=event.target.files[0];event.target.value='';if(!file)return;
    try{
      if(file.size>5*1024*1024)throw new Error('The configuration exceeds 5 MB. Check that you selected the correct file.');
      const imported=JSON.parse(await file.text()), errors=M.validate(imported);if(errors.length)throw new Error(errors.slice(0,5).join('\n'));
      confirmAction('Import configuration',`Load ${count(imported.categories.length, 'category', 'categories')}, ${count(imported.projects.length, 'project')} and ${count(imported.approaches.length, 'approach', 'approaches')}. This replaces the current draft without changing Lean files and can be undone.`,()=>{update(draft=>{for(const key of Object.keys(draft))delete draft[key];Object.assign(draft,imported);});view='overview';projectId=null;categoryId=null;selected.clear();render();},'Load configuration');
    }catch(error){toast(`Import failed: ${error.message}`);}
  });
  window.addEventListener('beforeunload',event=>{if(dirty()){event.preventDefault();event.returnValue='';}});
  window.addEventListener('storage',event=>{if(event.key===storageKey&&dirty())toast('Another page updated this session draft. Your current edits are retained; export or save them.');});
  try {
    if(location.protocol==='http:'||location.protocol==='https:'){
      const state=await api('/api/state');const errors=M.validate(state.config);if(errors.length)throw new Error(errors.join('\n'));
      config=state.config;snapshot=state.snapshot;revision=state.revision;savedConfig=JSON.stringify(config);connected=true;
    }
  }catch(_){connected=false;}
  try{
    const raw=localStorage.getItem(storageKey);
    if(raw){const draft=JSON.parse(raw);if(!M.validate(draft.config).length){if(draft.baseRevision===revision){config=draft.config;toast('Browser configuration draft restored');}else {localStorage.setItem(`${storageBase}:archive:${Date.now()}-${sessionId}`,raw);localStorage.removeItem(storageKey);}}}
    for(let i=0;i<localStorage.length;i++){
      const key=localStorage.key(i);
      if(key!==storageKey&&(key===storageBase||key.startsWith(storageBase+':'))){
        try{const raw=localStorage.getItem(key),draft=JSON.parse(raw);if(!M.validate(draft.config).length)pendingDrafts.push({...draft,storageKey:key,raw});}catch(_){}
      }
    }
  }catch(_){/* Browser storage is optional; export remains available. */}
  render();
})();
