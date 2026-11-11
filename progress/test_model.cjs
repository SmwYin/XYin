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
