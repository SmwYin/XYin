#!/bin/bash
# Per-folder before/after statistics + full diff against the pre-cleanup backup.
set -u
ROOT=/Users/dfa25dxu/Projects/Lean/XYin
OUT=$ROOT/.mathlib-quality/cleanup-2026-09-26
TMP=$(mktemp -d)
tar -xzf $ROOT/.mathlib-quality/backups/pre-cleanup-2026-09-26.tar.gz -C $TMP XYin XYin.lean ScratchGS.lean lakefile.toml 2>/dev/null
cd $ROOT
python3 - "$TMP" <<'PY'
import os,re,sys,collections
tmp=sys.argv[1]
decl=re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|scoped|local|nonrec)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\b",re.M)
def scan(base,dirs):
    st=collections.defaultdict(lambda:[0,0,0,0,0])  # files, lines, decls, simp, sorry
    for d in dirs:
        for dp,_,fs in os.walk(os.path.join(base,d)):
            for f in fs:
                if not f.endswith('.lean'): continue
                p=os.path.join(dp,f); rel=os.path.relpath(p,base); s=open(p).read()
                parts=rel.split('/')
                key=('Tests' if parts[0]=='XYinTest' else (parts[2] if len(parts)>3 and parts[1]=='PhD' else ('Tests' if parts[-1] in ('LaurentQExpSimpTests.lean','QExpSimpConditionTests.lean','Examples.lean') else ( parts[2] if len(parts)>=3 and parts[1]=='PhD' else parts[-1]))))
                if parts[:2]==['XYin','PhD'] and len(parts)==4: key=parts[2]
                if rel in ('XYin/PhD/Tactic2/LaurentQExpSimpTests.lean','XYin/PhD/Tactic2/QExpSimpConditionTests.lean','XYin/PhD/qExpansion_tactic/Examples.lean'): key='Tests'
                v=st[key]; v[0]+=1; v[1]+=s.count('\n')+1; v[2]+=len(decl.findall(s)); v[3]+=s.count('@[simp'); v[4]+=len(re.findall(r'\bsorry\b',s))
    return st
before=scan(tmp,['XYin']); after=scan('.',['XYin','XYinTest'])
keys=sorted(set(before)|set(after), key=lambda k:-before.get(k,[0,0])[1])
rows=['| Folder | Files | Lines | Declarations | `@[simp]` | sorry |','|---|---:|---:|---:|---:|---:|']
T=[[0]*5,[0]*5]
for k in keys:
    b=before.get(k,[0]*5); a=after.get(k,[0]*5)
    for i in range(5): T[0][i]+=b[i]; T[1][i]+=a[i]
    rows.append(f'| {k} | {b[0]} → {a[0]} | {b[1]:,} → {a[1]:,} | {b[2]} → {a[2]} | {b[3]} → {a[3]} | {b[4]} → {a[4]} |')
rows.append(f'| **Total** | {T[0][0]} → {T[1][0]} | {T[0][1]:,} → {T[1][1]:,} | {T[0][2]} → {T[1][2]} | {T[0][3]} → {T[1][3]} | {T[0][4]} → {T[1][4]} |')
open(os.environ.get('OUTFILE','/dev/stdout'),'w').write('\n'.join(rows)+'\n')
PY
( cd $TMP && diff -ruN --exclude='*.olean' XYin $ROOT/XYin > $OUT/changes-XYin.diff; diff -uN XYin.lean $ROOT/XYin.lean >> $OUT/changes-XYin.diff; diff -uN lakefile.toml $ROOT/lakefile.toml >> $OUT/changes-XYin.diff; diff -ruN /dev/null $ROOT/XYinTest.lean >> $OUT/changes-XYin.diff 2>/dev/null ) 
echo "diff lines: $(wc -l < $OUT/changes-XYin.diff)"
rm -rf $TMP
