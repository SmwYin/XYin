const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const M = require('./web/model.js');
const seed = JSON.parse(fs.readFileSync(path.join(__dirname, 'config.json'), 'utf8'));

test('seed schema is valid and every scanned Lean file has a consistent owner', () => {
  assert.deepEqual(M.validate(seed), []);
  const snapshot = JSON.parse(fs.readFileSync(path.join(__dirname, 'snapshot.json'), 'utf8'));
  for (const f of snapshot.files) {
    const owner = M.assignment(seed, f.path);
    assert.ok(owner.projectId, f.path);
    if(owner.approachId) assert.equal(seed.approaches.find(a=>a.id===owner.approachId).projectId, owner.projectId);
  }
});

test('glob matching respects component boundaries, zero-depth **/, and regex characters', () => {
  assert.equal(M.matches('XYin/A.lean','XYin/**/*.lean'), true);
  assert.equal(M.matches('XYin/PhD/A.lean','XYin/**/*.lean'), true);
  assert.equal(M.matches('XYin/PhD/A.lean','XYin/*.lean'), false);
  assert.equal(M.matches('XYin/Axlean','XYin/A.lean'), false);
  assert.equal(M.matches('XYin/A[1].lean','XYin/A[1].lean'), true);
});

test('last matching rule wins and file overrides survive broad classification', () => {
  const c = structuredClone(seed), file = 'XYin/PhD/NewQExpansion/Basic.lean';
  c.assignments.push({id:'last',pattern:'XYin/PhD/**',projectId:c.projects[0].id,approachId:null});
  assert.equal(M.assignment(c,file).projectId,c.projects[0].id);
  c.overrides[file] = {projectId:c.projects[1].id,approachId:null};
  assert.equal(M.assignment(c,file).projectId,c.projects[1].id);
  assert.equal(M.assignment(c,file).manual,true);
});

test('reject cycles, cross-project approaches, unsafe paths and unapproved fields', () => {
  let c = structuredClone(seed); c.projects[0].parentId=c.projects[0].id;
  assert.ok(M.validate(c).some(e=>e.includes('cycle')));
  c=structuredClone(seed); c.overrides['XYin/PhD/X.lean']={projectId:c.projects.find(p=>p.id!==c.approaches[0].projectId).id,approachId:c.approaches[0].id};
  assert.ok(M.validate(c).some(e=>e.includes('approach')));
  for(const unsafe of ['/tmp/a.lean','XYin/../x.lean','XYin/PhD\\x.lean','Other/file.lean','XYin/x\ny.lean']){
    c=structuredClone(seed);c.migrations[0].sourcePaths=[unsafe];assert.notDeepEqual(M.validate(c),[],unsafe);
  }
  c=structuredClone(seed);c.approaches[0].execute='lake build';assert.ok(M.validate(c).length);
  for(const key of ['projects','approaches','relations','overrides']){c=structuredClone(seed);c[key]=null;assert.ok(M.validate(c).length);}
});

test('adoption follows import closure, excludes source itself, handles cycles and keeps manual confirmation separate', () => {
  const c=structuredClone(seed), p=c.projects[0].id;
  c.assignments=[{id:'all',pattern:'XYin/**',projectId:p,approachId:null}];c.overrides={};
  const snapshot={files:[
    {path:'XYin/Old.lean',module:'XYin.Old',imports:[]},
    {path:'XYin/ForMathlib/New.lean',module:'XYin.ForMathlib.New',imports:[]},
    {path:'XYin/A.lean',module:'XYin.A',imports:['XYin.B']},
    {path:'XYin/B.lean',module:'XYin.B',imports:['XYin.A','XYin.Old']},
    {path:'XYin/C.lean',module:'XYin.C',imports:['XYin.ForMathlib.New']}
  ]};
  const migration={sourcePaths:['XYin/Old.lean'],targetPaths:['XYin/ForMathlib/New.lean'],adoptedProjectIds:[]};
  assert.deepEqual(M.adoption(c,snapshot,migration,p),{old:2,target:1,confirmed:false});
  migration.adoptedProjectIds=[p];
  assert.deepEqual(M.adoption(c,snapshot,migration,p),{old:2,target:1,confirmed:true});
});

function discoveryFixture() {
  return {
    schemaVersion: 1,
    categories: [{id:'formathlib',label:'ForMathlib',description:''},{id:'others',label:'Others',description:''}],
    projects: [
      {id:'others-support',categoryId:'others',parentId:null,label:'Support',description:''},
      {id:'existing',categoryId:'formathlib',parentId:null,label:'Existing',description:''},
      {id:'retired',categoryId:'formathlib',parentId:null,label:'Retired',description:''},
    ],
    approaches: [], environments: [], relations: [], migrations: [], overrides: {},
    assignments: [
      {id:'fallback-xyin',pattern:'XYin/**/*.lean',projectId:'others-support',approachId:null},
      {id:'fallback-tests',pattern:'XYinTest/**/*.lean',projectId:'others-support',approachId:null},
      {id:'entry-xyin',pattern:'XYin.lean',projectId:'others-support',approachId:null},
      {id:'entry-tests',pattern:'XYinTest.lean',projectId:'others-support',approachId:null},
      {id:'existing-rule',pattern:'XYin/ForMathlib/Existing/**',projectId:'existing',approachId:null},
    ],
    discoveredForMathlibDirectories: ['Existing'],
  };
}

function discoveryUpdate(base) {
  const remote = structuredClone(base);
  remote.projects.push({id:'new-project',categoryId:'formathlib',parentId:null,label:'New',description:'Discovered folder'});
  remote.assignments.splice(4,0,{id:'new-rule',pattern:'XYin/ForMathlib/New/**',projectId:'new-project',approachId:null});
  remote.discoveredForMathlibDirectories = [...(base.discoveredForMathlibDirectories || []),'New'];
  return remote;
}

test('discovered folder metadata is optional and accepts only unique safe direct names', () => {
  const legacy = discoveryFixture(); delete legacy.discoveredForMathlibDirectories;
  assert.deepEqual(M.validate(legacy), []);
  for (const names of [[], ['NumberTheory', 'My folder', '代数']]) {
    assert.deepEqual(M.validate({...legacy,discoveredForMathlibDirectories:names}), []);
  }
  for (const names of [null, 'Algebra', [null], [''], ['.'], ['..'], ['.hidden'], ['a/b'], ['a\\b'], ['a\nb'], ['A*'], ['A?'], ['A[1]'], ['a]'], ['x'.repeat(1001)], ['Same','Same'], Array.from({length:10001},(_,i)=>String(i))]) {
    assert.ok(M.validate({...legacy,discoveredForMathlibDirectories:names}).some(error=>error.includes('discoveredForMathlibDirectories')));
  }
});

test('discovery merge preserves manual names, deleted rows, rule order, narrowing and file overrides', () => {
  const base = discoveryFixture(), remote = discoveryUpdate(base), draft = structuredClone(base);
  draft.projects.find(row=>row.id==='existing').label='My chosen project name';
  draft.projects=draft.projects.filter(row=>row.id!=='retired').reverse();
  draft.assignments=[
    draft.assignments[0],
    {...draft.assignments[1],pattern:'XYinTest/Tactic2/**'},
    draft.assignments[3],
    draft.assignments[2],
    {id:'manual-rule',pattern:'XYin/ForMathlib/New/**',projectId:'existing',approachId:null},
  ];
  draft.overrides['XYin/ForMathlib/New/Override.lean']={projectId:'others-support',approachId:null};
  draft.discoveredForMathlibDirectories.push('Manual');
  const originals=structuredClone({base,draft,remote});
  const merged=M.mergeDiscovery(base,draft,remote);
  assert.deepEqual(merged.projects.slice(0,draft.projects.length),draft.projects);
  assert.equal(merged.projects.find(row=>row.id==='existing').label,'My chosen project name');
  assert.equal(merged.projects.some(row=>row.id==='retired'),false);
  assert.deepEqual(merged.assignments.map(row=>row.id),['fallback-xyin','new-rule','fallback-tests','entry-tests','entry-xyin','manual-rule']);
  assert.deepEqual(merged.assignments.filter(row=>row.id!=='new-rule'),draft.assignments);
  assert.equal(M.assignment(merged,'XYin/ForMathlib/New/Basic.lean').projectId,'existing');
  assert.equal(M.assignment(merged,'XYin/ForMathlib/New/Override.lean').projectId,'others-support');
  assert.deepEqual(merged.discoveredForMathlibDirectories,['Existing','Manual','New']);
  assert.deepEqual({base,draft,remote},originals);
  merged.projects[0].label='Changed result';
  assert.deepEqual({base,draft,remote},originals,'the result must not share mutable input rows');
});

test('new rules follow only the canonical leading fallback block and never overtake manual rules', () => {
  const base=discoveryFixture(),remote=discoveryUpdate(base);
  const reordered=structuredClone(base);
  [reordered.assignments[0],reordered.assignments[3]]=[reordered.assignments[3],reordered.assignments[0]];
  let merged=M.mergeDiscovery(base,reordered,remote);
  assert.deepEqual(merged.assignments.slice(0,4),reordered.assignments.slice(0,4));
  assert.equal(merged.assignments[4].id,'new-rule');
  const retargeted=structuredClone(base);
  retargeted.assignments[0].projectId='existing';
  merged=M.mergeDiscovery(base,retargeted,remote);
  assert.equal(merged.assignments[0].id,'new-rule');
  assert.deepEqual(merged.assignments.slice(1),retargeted.assignments);
  assert.equal(M.assignment(merged,'XYin/ForMathlib/New/Basic.lean').projectId,'existing');
});

test('discovery refuses conflicting IDs and invalid references without changing the draft', () => {
  const base=discoveryFixture(),remote=discoveryUpdate(base);
  for (const key of ['projects','assignments']) {
    const draft=structuredClone(base), newRow=remote[key].find(row=>row.id.startsWith('new-'));
    draft[key].push({...newRow,...(key==='projects'?{label:'My manual project'}:{projectId:'existing'})});
    const original=structuredClone(draft);
    assert.throws(()=>M.mergeDiscovery(base,draft,remote),/conflicts with your draft/);
    assert.deepEqual(draft,original);
  }
  const draft=structuredClone(base);
  draft.categories=draft.categories.filter(row=>row.id!=='formathlib');
  draft.projects=draft.projects.filter(row=>row.categoryId!=='formathlib');
  draft.assignments=draft.assignments.filter(row=>row.projectId==='others-support');
  assert.deepEqual(M.validate(draft),[]);
  assert.throws(()=>M.mergeDiscovery(base,draft,remote),/category does not exist/);
});

test('discovery refuses external edits, deleted rows, reordering and non-append metadata', () => {
  const base=discoveryFixture(),draft=structuredClone(base);
  const mutations=[
    remote=>{remote.categories[0].label='Renamed externally';},
    remote=>{remote.projects[1].description='Edited externally';},
    remote=>{remote.projects=remote.projects.filter(row=>row.id!=='retired');},
    remote=>{[remote.projects[0],remote.projects[1]]=[remote.projects[1],remote.projects[0]];},
    remote=>{remote.assignments[0].pattern='XYin/PhD/**';},
    remote=>{remote.assignments.splice(2,1);},
    remote=>{[remote.assignments[0],remote.assignments[1]]=[remote.assignments[1],remote.assignments[0]];},
    remote=>{remote.overrides['XYin/A.lean']={projectId:'existing',approachId:null};},
    remote=>{remote.discoveredForMathlibDirectories=['New','Existing'];},
    remote=>{remote.discoveredForMathlibDirectories=['New'];},
  ];
  for (const mutate of mutations) {
    const remote=discoveryUpdate(base);mutate(remote);
    assert.deepEqual(M.validate(remote),[],'external change should be valid but ineligible for automatic merge');
    const before=structuredClone({base,draft,remote});
    assert.throws(()=>M.mergeDiscovery(base,draft,remote),/changed outside automatic discovery/);
    assert.deepEqual({base,draft,remote},before);
  }
});

test('merging undo snapshots retains discovery additions and clean merges keep remote serialisation', () => {
  const base=discoveryFixture(),remote=discoveryUpdate(base);
  const undoBeforeEdit=structuredClone(base),undoAfterEdit=structuredClone(base);
  undoAfterEdit.projects.find(row=>row.id==='existing').label='Edited name';
  const mergedUndo=[undoBeforeEdit,undoAfterEdit].map(draft=>M.mergeDiscovery(base,draft,remote));
  for (const restored of mergedUndo) {
    assert.ok(restored.projects.some(row=>row.id==='new-project'));
    assert.ok(restored.assignments.some(row=>row.id==='new-rule'));
    assert.deepEqual(restored.discoveredForMathlibDirectories,['Existing','New']);
  }
  assert.equal(mergedUndo[0].projects.find(row=>row.id==='existing').label,'Existing');
  assert.equal(mergedUndo[1].projects.find(row=>row.id==='existing').label,'Edited name');
  assert.equal(JSON.stringify(mergedUndo[0]),JSON.stringify(remote));
  const alreadyAdded=structuredClone(remote);
  assert.deepEqual(M.mergeDiscovery(base,alreadyAdded,remote),remote,'identical additions should not be duplicated');
  const rekeyed={...remote,projects:remote.projects.map(row=>Object.fromEntries(Object.entries(row).reverse()))};
  assert.equal(JSON.stringify(M.mergeDiscovery(base,base,rekeyed)),JSON.stringify(rekeyed),'object key ordering must not create a false conflict or dirty state');
});

test('discovery reuses an unsaved same-label project and remaps the new rule without losing notes', () => {
  const base=discoveryFixture(),remote=discoveryUpdate(base);
  for (const createProject of [true,false]) {
    const draft=structuredClone(base);
    const manualProject=createProject
      ? {id:'my-custom-id',categoryId:'formathlib',parentId:null,label:'New',description:'My project notes'}
      : {...draft.projects.find(row=>row.id==='existing'),label:'New',description:'My renamed project notes'};
    if(createProject) draft.projects.push(manualProject);
    else draft.projects[draft.projects.findIndex(row=>row.id==='existing')]=manualProject;
    const before=structuredClone({base,draft,remote});
    const merged=M.mergeDiscovery(base,draft,remote);
    assert.deepEqual(merged.projects,draft.projects,'the manual project should be reused rather than duplicated');
    assert.deepEqual(merged.projects.find(row=>row.id===manualProject.id),manualProject);
    assert.equal(merged.projects.some(row=>row.id==='new-project'),false);
    assert.equal(merged.assignments.find(row=>row.id==='new-rule').projectId,manualProject.id);
    assert.equal(M.assignment(merged,'XYin/ForMathlib/New/Basic.lean').projectId,manualProject.id);
    assert.notEqual(JSON.stringify(merged),JSON.stringify(remote),'reusing the local project must remain an unsaved change');
    assert.deepEqual({base,draft,remote},before);
    merged.projects.find(row=>row.id===manualProject.id).description='Changed result';
    assert.deepEqual({base,draft,remote},before,'the reused project must also be cloned');
    const undo=M.mergeDiscovery(base,base,remote);
    assert.equal(JSON.stringify(undo),JSON.stringify(remote),'undo without the local project should restore the remote default cleanly');
    assert.equal(undo.assignments.find(row=>row.id==='new-rule').projectId,'new-project');
  }
});

test('same-label discovery matching is scoped and rejects ambiguity or differing ID collisions', () => {
  const base=discoveryFixture(),remote=discoveryUpdate(base);
  const ambiguous=structuredClone(base);
  for(const id of ['manual-one','manual-two']) ambiguous.projects.push({id,categoryId:'formathlib',parentId:null,label:'New',description:id});
  const before=structuredClone(ambiguous);
  assert.throws(()=>M.mergeDiscovery(base,ambiguous,remote),/more than one draft project matches/);
  assert.deepEqual(ambiguous,before);

  const scoped=structuredClone(base);
  scoped.projects.push({id:'other-category',categoryId:'others',parentId:null,label:'New',description:''});
  scoped.projects.push({id:'other-parent',categoryId:'formathlib',parentId:'existing',label:'New',description:''});
  const merged=M.mergeDiscovery(base,scoped,remote);
  assert.ok(merged.projects.some(row=>row.id==='new-project'),'different category or parent must not cause reuse');
  assert.equal(merged.assignments.find(row=>row.id==='new-rule').projectId,'new-project');

  const collision=structuredClone(base);
  collision.projects.push({...remote.projects.find(row=>row.id==='new-project'),description:'My manual notes'});
  assert.throws(()=>M.mergeDiscovery(base,collision,remote),/ID “new-project” conflicts/,'a matching ID must still have identical contents');
});
