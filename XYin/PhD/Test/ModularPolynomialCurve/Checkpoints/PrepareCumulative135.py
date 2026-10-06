"""Freeze source and named-check metadata only, after the owner declares a source freeze.

This script never starts a compiler and never reads current Lean artifacts.  The
historical 99-module receipt, independent audit and build log remain byte-exact.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

WD = Path('/private/tmp/xyin-y0-aintlib-work')
RETAINED = Path('/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts')
BASELINE = Path('/private/tmp/Cumulative99Baseline')
COMPILER = Path('/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
PATTERN = re.compile(r"'([^\n]+?)' (?:depends on axioms:\s*\[(.*?)\]|does not depend on any axioms)", re.S)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exact_prints(text):
    return [{'name': m.group(1), 'axioms': sorted(set(re.findall(
        r'[A-Za-z][A-Za-z.]*', m.group(2) or '')))} for m in PATTERN.finditer(text)]


def normalized_checks(receipt):
    checks = receipt.get('checks')
    if isinstance(checks, dict):
        return [{'name': n, 'axioms': sorted(a)} for n, a in checks.items()]
    assert isinstance(checks, list), 'Receipt must record every exact print in order.'
    return [{'name': c.get('name', c.get('declaration')), 'axioms': sorted(c['axioms'])}
            for c in checks]


def source_metadata(receipt):
    source = receipt.get('source')
    path = source.get('path') if isinstance(source, dict) else source
    path = path or receipt.get('isolated_source') or receipt.get('retained_source')
    digest = receipt.get('source_sha256')
    if digest is None and isinstance(source, dict):
        digest = source.get('sha256')
    return path, digest


def inspect_named_receipt(path, source_name, source_hash, checks, examples):
    receipt = json.loads(path.read_text())
    module = 'AINTLIBDrafts.' + Path(source_name).stem
    assert receipt['module'] == module
    assert receipt.get('exit_code', receipt.get('exitCode')) == 0, path
    assert receipt.get('status') == 'CLOSED' or receipt.get('closed') is True, path
    source_path, digest = source_metadata(receipt)
    assert Path(source_path).name == source_name and digest == source_hash, path
    assert sha(source_path) == source_hash, path
    exact = normalized_checks(receipt)
    assert len(exact) == checks, (source_name, 'check count')
    assert all(c['name'] and set(c['axioms']) <= ALLOWED for c in exact), path
    assert receipt['examples'] == examples, (source_name, 'example count')
    log = Path(receipt['log'])
    assert sha(log) == receipt['log_sha256'], path
    log_text = log.read_text()
    assert exact_prints(log_text) == exact, (path, 'full log exact prints')
    assert 'sorryAx' not in log_text and not re.search(
        r'(^|\n).*\b(?:warning|error):', log_text), path
    setup = Path(receipt['setup'])
    assert sha(setup) == receipt['setup_sha256'], path
    data = json.loads(setup.read_text())
    assert data['name'] == module, path
    assert data['options']['autoImplicit'] is False, path
    assert data['options']['relaxedAutoImplicit'] is False, path
    assert not data.get('plugins') and not data.get('dynlibs'), path
    return {'source_sha256': source_hash, 'checks': exact, 'examples': examples,
            'named_receipt': str(path), 'named_receipt_sha256': sha(path),
            'log': str(log), 'log_sha256': sha(log),
            'setup': str(setup), 'setup_sha256': sha(setup),
            'closed_exit_zero_recorded': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--confirm-frozen', action='store_true', required=True,
                        help='Use only after the root owner declares all source/config writers frozen.')
    parser.add_argument('--output-prefix', type=Path,
                        default=Path('/private/tmp/CumulativePost99'))
    args = parser.parse_args()
    assert args.confirm_frozen
    manifest = json.loads((BASELINE / 'manifest.json').read_text())
    for name, entry in manifest.items():
        if name != 'baseline':
            assert sha(entry['path']) == entry['sha256'], ('Historical archive drift', name)
    historical = json.loads((BASELINE / 'receipt.json').read_text())
    audit = json.loads((BASELINE / 'independent-audit.json').read_text())
    assert sha(BASELINE / 'receipt.json') == audit['receipt_sha256']
    assert sha(BASELINE / 'build.log') == audit['build_log_sha256']
    assert (audit['module_count'], audit['checks'], audit['examples']) == (99, 935, 186)
    inventory = {p.name for p in RETAINED.glob('*.lean')}
    assert inventory == {p.name for p in (WD / 'AINTLIBDrafts').glob('*.lean')}
    assert set(historical['source_sha256']) <= inventory
    sources = {}
    counts = {}
    for name in sorted(inventory):
        data = (RETAINED / name).read_bytes()
        assert data == (WD / 'AINTLIBDrafts' / name).read_bytes(), name
        sources[name] = hashlib.sha256(data).hexdigest()
        text = data.decode()
        counts[name] = {'checks': len(re.findall(r'^\s*#print axioms\b', text, re.M)),
                        'examples': len(re.findall(r'^\s*(?:noncomputable\s+)?example\b', text, re.M))}
        if name in audit['modules']:
            assert sources[name] == audit['modules'][name]['source_sha256'], ('Baseline source drift', name)
            assert counts[name]['checks'] == len(audit['modules'][name]['declarations'])
            assert counts[name]['examples'] == audit['modules'][name]['examples']
    candidates = {}
    for path in sorted(Path('/private/tmp').glob('*receipt*.json')):
        try:
            receipt = json.loads(path.read_text())
            source_path, digest = source_metadata(receipt)
        except (ValueError, OSError, AttributeError):
            continue
        if not isinstance(source_path, str):
            continue
        name = Path(source_path).name
        if name not in inventory or name in audit['modules']:
            continue
        if digest != sources[name] or receipt.get('module') != 'AINTLIBDrafts.' + Path(name).stem:
            continue
        # A matching named receipt must be wholly valid; a staged failure cannot be silently selected.
        candidates.setdefault(name, []).append(inspect_named_receipt(
            path, name, digest, counts[name]['checks'], counts[name]['examples']))
    direct = {}
    for name in sorted(inventory - set(audit['modules'])):
        entries = candidates.get(name, [])
        assert entries, ('No closed matching correct-name named receipt', name)
        assert all(e['checks'] == entries[0]['checks'] for e in entries), ('Receipt disagreement', name)
        direct[name] = entries[0]
        direct[name]['all_matching_named_receipts'] = [
            {'path': e['named_receipt'], 'sha256': e['named_receipt_sha256']} for e in entries]
    configs = {}
    for name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
        path = WD / name
        configs[name] = {'path': str(path), 'sha256': sha(path)}
    pinned = {'aintlib_revision': 'ab1451487da02cd4483d0e2cdb2cc9e44bbbac17',
              'mathlib_revision': '300d0e535721bc098547106fc297d8ba2a63f6bb',
              'toolchain': 'leanprover/lean4:v4.35.0-rc3'}
    assert (WD / 'lean-toolchain').read_text().strip() == pinned['toolchain']
    for path, revision in ((WD, pinned['aintlib_revision']),
                           (WD / '.lake/packages/mathlib', pinned['mathlib_revision'])):
        assert subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip() == revision
        dirty = subprocess.check_output(['git', '-C', str(path), 'diff', '--name-only', 'HEAD'], text=True).splitlines()
        assert not dirty if path != WD else all(n == 'lakefile.toml' for n in dirty)
    original_config = subprocess.check_output(['git', '-C', str(WD), 'show', 'HEAD:lakefile.toml'])
    bridge_config = b'\n[[lean_lib]]\nname = "AINTLIBDrafts"\n[lean_lib.leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit = false\n'
    assert (WD / 'lakefile.toml').read_bytes() == original_config + bridge_config
    snapshot = {'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
                'prepared_source_only': True, 'inspected_rebuilding_artifacts': False,
                'root_source_freeze_confirmation_required': True,
                'preparation_script': str(Path(__file__).resolve()),
                'preparation_script_sha256': sha(Path(__file__).resolve()),
                'module_count': len(inventory),
                'check_count': sum(c['checks'] for c in counts.values()),
                'example_count': sum(c['examples'] for c in counts.values()),
                'source_sha256': sources, 'source_counts': counts,
                'driver_sha256': sha(RETAINED.parent / 'RunAINTLIBBridge.py'),
                'exact_compiler': str(COMPILER), 'exact_compiler_sha256': sha(COMPILER),
                'config_files': configs, **pinned,
                'historical99_receipt': str(BASELINE / 'receipt.json'),
                'historical99_receipt_sha256': sha(BASELINE / 'receipt.json'),
                'historical99_independent_audit': str(BASELINE / 'independent-audit.json'),
                'historical99_independent_audit_sha256': sha(BASELINE / 'independent-audit.json'),
                'historical99_build_log': str(BASELINE / 'build.log'),
                'historical99_build_log_sha256': sha(BASELINE / 'build.log'),
                'historical99_archive_manifest': str(BASELINE / 'manifest.json'),
                'historical99_archive_manifest_sha256': sha(BASELINE / 'manifest.json')}
    snapshot_path = Path(str(args.output_prefix) + 'PreparedSourceSnapshot.json')
    direct_path = Path(str(args.output_prefix) + 'PreparedDirectChecks.json')
    assert not snapshot_path.exists() and not direct_path.exists(), 'Never overwrite a frozen prepared checkpoint.'
    assert inventory == {p.name for p in RETAINED.glob('*.lean')}
    assert inventory == {p.name for p in (WD / 'AINTLIBDrafts').glob('*.lean')}
    for name, digest in sources.items():
        assert sha(RETAINED / name) == sha(WD / 'AINTLIBDrafts' / name) == digest, ('Changed during preparation', name)
    for name, record in configs.items():
        assert sha(record['path']) == record['sha256'], ('Config changed during preparation', name)
    assert sha(RETAINED.parent / 'RunAINTLIBBridge.py') == snapshot['driver_sha256']
    snapshot_path.write_text(json.dumps(snapshot, indent=2) + '\n')
    metadata = {'prepared_without_reading_rebuilding_artifacts': True,
                'source_snapshot_sha256': sha(snapshot_path), 'modules': direct,
                'module_count': len(direct),
                'check_count': sum(len(m['checks']) for m in direct.values()),
                'example_count': sum(m['examples'] for m in direct.values())}
    direct_path.write_text(json.dumps(metadata, indent=2) + '\n')
    print(json.dumps({'source_snapshot': str(snapshot_path), 'source_snapshot_sha256': sha(snapshot_path),
                      'direct_checks': str(direct_path), 'direct_checks_sha256': sha(direct_path),
                      'modules': snapshot['module_count'], 'checks': snapshot['check_count'],
                      'examples': snapshot['example_count'], 'post99_modules': len(direct)}, indent=2))


if __name__ == '__main__':
    main()
