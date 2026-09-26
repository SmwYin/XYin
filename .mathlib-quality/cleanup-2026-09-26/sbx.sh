#!/bin/bash
# Sandbox helper for the 2026-09-26 cleanup.
#   sbx.sh create NAME         clone main tree (sources + build dir) into a private sandbox + pristine base copy
#   sbx.sh changes NAME        list files changed/added/deleted in the sandbox vs its base
#   sbx.sh merge NAME GLOB...  copy changes whose paths match one of the GLOBs into main (refuses on conflicts);
#                              XYin.lean is merged as a patch
set -u
ROOT=${ROOT:-/Users/dfa25dxu/Projects/Lean/XYin}
SBROOT=${SBROOT:-/Users/dfa25dxu/Projects/Lean/.xyin-sandboxes}
cmd=$1; name=$2; shift 2
SB=$SBROOT/$name; BASE=$SBROOT/$name.base
SRC="XYin XYinTest XYin.lean XYinTest.lean lakefile.toml"
changes() {
  (cd "$SBROOT" && diff -rq "$name.base" "$name" -x .lake -x lake-manifest.json -x lean-toolchain -x 'CLEANUP_REPORT.md' -x '*.orig*' -x '.scratch' 2>/dev/null) |
  python3 -c '
import sys,re,os
name,sbroot=sys.argv[1],sys.argv[2]
def walk(root,rel):
    full=os.path.join(root,rel)
    if os.path.isdir(full):
        for dp,dn,fn in os.walk(full):
            for f in fn: yield os.path.relpath(os.path.join(dp,f),root)
    else: yield rel
for l in sys.stdin:
    l=l.rstrip("\n")
    m=re.match(r"Files (\S+) and (\S+) differ",l)
    if m: print("M", m.group(2)[len(name)+1:]); continue
    m=re.match(r"Only in (\S+): (.+)",l)
    if m:
        d,f=m.group(1),m.group(2)
        if d==name or d.startswith(name+"/"):
            rel=(d[len(name)+1:]+"/" if d!=name else "")+f
            for r in walk(os.path.join(sbroot,name),rel): print("A", r)
        elif d==name+".base" or d.startswith(name+".base/"):
            rel=(d[len(name)+6:]+"/" if d!=name+".base" else "")+f
            for r in walk(os.path.join(sbroot,name+".base"),rel): print("D", r)
' "$name" "$SBROOT"
}
case $cmd in
create)
  rm -rf "$SB" "$BASE"; mkdir -p "$SB/.lake" "$BASE"
  cd "$ROOT" && cp -Rc $SRC lake-manifest.json lean-toolchain "$SB/" && cp -Rc $SRC "$BASE/" \
    && cp -Rc .lake/build "$SB/.lake/build" && ln -s "$ROOT/.lake/packages" "$SB/.lake/packages"
  echo "created $SB (base $BASE)";;
changes) changes;;
merge)
  globs=("$@"); conflicts=0; plan=()
  while read -r kind path; do
    [ -z "$path" ] && continue
    ok=0; for g in "${globs[@]}"; do [[ "$path" == $g ]] && ok=1; done
    if [ "$path" = "XYin.lean" ] || [ "$path" = "XYinTest.lean" ]; then ok=1; fi
    if [ $ok = 0 ]; then echo "OUTSIDE-OWNERSHIP (skipped): $kind $path"; continue; fi
    plan+=("$kind $path")
  done < <(changes)
  for item in "${plan[@]}"; do
    kind=${item%% *}; path=${item#* }
    case "$path" in XYin.lean|XYinTest.lean) continue;; esac
    if [ "$kind" != A ] && ! cmp -s "$ROOT/$path" "$BASE/$path"; then echo "CONFLICT (main changed since base): $path"; conflicts=1; fi
    if [ "$kind" = A ] && [ -e "$ROOT/$path" ]; then echo "CONFLICT (exists in main): $path"; conflicts=1; fi
  done
  [ $conflicts = 1 ] && { echo "merge aborted"; exit 1; }
  for item in "${plan[@]}"; do
    kind=${item%% *}; path=${item#* }
    case "$path" in
      XYin.lean|XYinTest.lean) diff -u "$BASE/$path" "$SB/$path" > "$SBROOT/$name.$path.patch"; (cd "$ROOT" && patch -p0 --no-backup-if-mismatch "$path" < "$SBROOT/$name.$path.patch") || { echo "PATCH FAILED for $path"; exit 1; }; echo "patched $path";;
      *) if [ "$kind" = D ]; then rm "$ROOT/$path" && echo "deleted $path"; else mkdir -p "$(dirname "$ROOT/$path")" && cp "$SB/$path" "$ROOT/$path" && echo "copied $kind $path"; fi;;
    esac
  done;;
esac
