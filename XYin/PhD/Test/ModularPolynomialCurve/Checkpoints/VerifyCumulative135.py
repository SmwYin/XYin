import argparse
import hashlib
import json
import pathlib
import re
import shlex
import subprocess
import runpy

parser = argparse.ArgumentParser(description='Independent closed cumulative provenance audit; execute only after root confirms CLOSED exit0.')
parser.add_argument('--expected-jobs', type=int, required=True)
parser.add_argument('--expected-modules', type=int, required=True)
parser.add_argument('--expected-checks', type=int, required=True)
parser.add_argument('--expected-examples', type=int, required=True)
parser.add_argument('--cumulative-session', type=int, required=True)
parser.add_argument('--expected-receipt-sha256', required=True)
parser.add_argument('--receipt', type=pathlib.Path,
                    default=pathlib.Path('/private/tmp/xyin-y0-aintlib-work/yzero-bridge-receipt.json'))
parser.add_argument('--parent-receipt', type=pathlib.Path,
                    default=pathlib.Path('/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBBridgeReceipt.json'))
parser.add_argument('--prepared-source-snapshot', type=pathlib.Path,
                    default=pathlib.Path('/private/tmp/CumulativePost99PreparedSourceSnapshot.json'))
parser.add_argument('--output', type=pathlib.Path,
                    default=pathlib.Path('/private/tmp/CumulativePost99IndependentAudit.json'))
parser.add_argument('--prepared-direct-checks', type=pathlib.Path,
                    default=pathlib.Path('/private/tmp/CumulativePost99PreparedDirectChecks.json'))
args = parser.parse_args()
prepared = json.loads(args.prepared_source_snapshot.read_text())
assert (args.expected_modules, args.expected_checks, args.expected_examples) == (
    prepared['module_count'], prepared['check_count'], prepared['example_count'])
assert prepared['prepared_source_only'] and not prepared['inspected_rebuilding_artifacts']
direct_prepared = json.loads(args.prepared_direct_checks.read_text())
assert direct_prepared['prepared_without_reading_rebuilding_artifacts']
assert direct_prepared['source_snapshot_sha256'] == hashlib.sha256(args.prepared_source_snapshot.read_bytes()).hexdigest()

wd = pathlib.Path('/private/tmp/xyin-y0-aintlib-work')
retained = pathlib.Path('/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts')
receipt_path = args.receipt
assert hashlib.sha256(receipt_path.read_bytes()).hexdigest() == args.expected_receipt_sha256
receipt = json.loads(receipt_path.read_text())
names = set(receipt['source_sha256'])
assert len(names) == receipt['source_file_count'] == args.expected_modules
assert receipt['source_sha256'] == prepared['source_sha256']
assert names == set(receipt['per_module_checks'])
assert set(receipt['targets']) == {'AINTLIBDrafts.' + pathlib.Path(n).stem for n in names}
assert receipt['build_exit_code'] == 0
parent_receipt_path = args.parent_receipt
assert parent_receipt_path.read_bytes() == receipt_path.read_bytes()
current_inventory = {p.name for p in retained.glob('*.lean')}
excluded_current_sources = sorted(current_inventory - names)
assert names == current_inventory
assert names == {p.name for p in (wd / 'AINTLIBDrafts').glob('*.lean')}
assert (wd / 'lean-toolchain').read_text().strip() == receipt['toolchain']
assert receipt['toolchain'] == 'leanprover/lean4:v4.35.0-rc3'
assert receipt['aintlib_revision'] == 'ab1451487da02cd4483d0e2cdb2cc9e44bbbac17'
assert receipt['mathlib_revision'] == '300d0e535721bc098547106fc297d8ba2a63f6bb'

for key in ('sources_changed_during_build', 'target_sources_changed_during_build',
            'module_check_failures', 'unexpected_axioms', 'bridge_diagnostics'):
    assert not receipt[key], key
assert not receipt['source_inventory_changed_during_build']
assert not receipt['sorryAx_in_build_output']
allowed = {'propext', 'Classical.choice', 'Quot.sound'}

historical99_path = pathlib.Path(prepared['historical99_receipt'])
assert hashlib.sha256(historical99_path.read_bytes()).hexdigest() == prepared['historical99_receipt_sha256']
historical99 = json.loads(historical99_path.read_text())
historical_audit_path = pathlib.Path(prepared['historical99_independent_audit'])
assert hashlib.sha256(historical_audit_path.read_bytes()).hexdigest() == prepared['historical99_independent_audit_sha256']
historical_audit = json.loads(historical_audit_path.read_text())
assert (historical_audit['module_count'], historical_audit['checks'], historical_audit['examples']) == (99, 935, 186)
assert historical_audit['receipt_sha256'] == prepared['historical99_receipt_sha256']
assert set(historical_audit['modules']) == set(historical99['source_sha256'])
historical_log = pathlib.Path(prepared['historical99_build_log'])
assert hashlib.sha256(historical_log.read_bytes()).hexdigest() == prepared['historical99_build_log_sha256'] == historical_audit['build_log_sha256']
archive_manifest = pathlib.Path(prepared['historical99_archive_manifest'])
assert hashlib.sha256(archive_manifest.read_bytes()).hexdigest() == prepared['historical99_archive_manifest_sha256']
for name, record in json.loads(archive_manifest.read_text()).items():
    if name != 'baseline':
        assert hashlib.sha256(pathlib.Path(record['path']).read_bytes()).hexdigest() == record['sha256'], ('Historical99 archive drift', name)
assert hashlib.sha256((retained.parent / 'RunAINTLIBBridge.py').read_bytes()).hexdigest() == prepared['driver_sha256']
for name, record in prepared['config_files'].items():
    assert hashlib.sha256(pathlib.Path(record['path']).read_bytes()).hexdigest() == record['sha256'], ('Frozen config drift', name)
assert prepared['exact_compiler'] == '/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean'
assert hashlib.sha256(pathlib.Path(prepared['exact_compiler']).read_bytes()).hexdigest() == prepared['exact_compiler_sha256']
preparation_script = pathlib.Path(prepared['preparation_script'])
assert hashlib.sha256(preparation_script.read_bytes()).hexdigest() == prepared['preparation_script_sha256']
helpers = runpy.run_path(str(preparation_script), run_name='source_audit_helpers')
assert set(direct_prepared['modules']) == names - set(historical_audit['modules'])
expected_prints = {}
print_provenance = {}
for source_name in names:
    if source_name in historical_audit['modules']:
        old_module = historical_audit['modules'][source_name]
        assert old_module['source_sha256'] == receipt['source_sha256'][source_name]
        expected_prints[source_name] = old_module['declarations']
        print_provenance[source_name] = {'path': str(historical_audit_path), 'sha256': prepared['historical99_independent_audit_sha256']}
        continue
    frozen_direct = direct_prepared['modules'][source_name]
    assert frozen_direct['source_sha256'] == receipt['source_sha256'][source_name]
    named_receipt = pathlib.Path(frozen_direct['named_receipt'])
    assert hashlib.sha256(named_receipt.read_bytes()).hexdigest() == frozen_direct['named_receipt_sha256']
    direct = helpers['inspect_named_receipt'](
        named_receipt, source_name, receipt['source_sha256'][source_name],
        prepared['source_counts'][source_name]['checks'],
        prepared['source_counts'][source_name]['examples'])
    for key in ('source_sha256', 'checks', 'examples', 'named_receipt',
                'named_receipt_sha256', 'log', 'log_sha256', 'setup', 'setup_sha256'):
        assert direct[key] == frozen_direct[key], ('Frozen direct-check metadata drift', source_name, key)
    expected_prints[source_name] = direct['checks']
    print_provenance[source_name] = {'path': str(named_receipt), 'sha256': frozen_direct['named_receipt_sha256']}
assert len(expected_prints) == args.expected_modules

pattern = re.compile(r"'([^\n]+?)' (?:depends on axioms:\s*\[(.*?)\]|does not depend on any axioms)", re.S)
modules = {}
all_names, all_free, all_axioms = set(), set(), set()
total_checks = total_examples = total_artifacts = 0
for name in sorted(names):
    source = retained / name
    isolated = wd / 'AINTLIBDrafts' / name
    source_bytes = source.read_bytes()
    assert hashlib.sha256(source_bytes).hexdigest() == receipt['source_sha256'][name], name
    assert source_bytes == isolated.read_bytes(), name
    text = source_bytes.decode()
    checks = len(re.findall(r'^\s*#print axioms\b', text, re.M))
    examples = len(re.findall(r'^\s*(?:noncomputable\s+)?example\b', text, re.M))
    stem = pathlib.Path(name).stem
    trace = json.loads((wd / '.lake/build/lib/lean/AINTLIBDrafts' / (stem + '.trace')).read_text())
    messages = '\n'.join(entry['message'] for entry in trace['log'])
    assert not any(entry['level'] in ('warning', 'error') for entry in trace['log']), name
    assert 'sorryAx' not in messages, name
    matches = list(pattern.finditer(messages))
    module_names, module_free, module_axioms = set(), set(), set()
    for match in matches:
        declaration, raw = match.groups()
        axioms = set(re.findall(r'[A-Za-z][A-Za-z.]*', raw or ''))
        assert axioms <= allowed, (name, declaration, axioms)
        module_names.add(declaration)
        module_axioms |= axioms
        if not axioms:
            module_free.add(declaration)
    actual_exact_prints = [{'name': m.group(1), 'axioms': sorted(set(re.findall(r'[A-Za-z][A-Za-z.]*', m.group(2) or '')))} for m in matches]
    assert actual_exact_prints == expected_prints[name], ('Exact declaration/axiom mismatch', name)
    recorded = receipt['per_module_checks'][name]
    assert checks == prepared['source_counts'][name]['checks'], name
    assert examples == prepared['source_counts'][name]['examples'], name
    assert checks == len(matches) == recorded['expected_axiom_check_count'] == recorded['observed_axiom_check_count'], name
    assert module_names == set(recorded['audited_declarations']), name
    assert module_free == set(recorded['axiom_free_declarations']), name
    assert module_axioms == set(recorded['observed_axioms']), name
    assert not recorded['diagnostics'], name
    setup_path = wd / '.lake/build/ir/AINTLIBDrafts' / (stem + '.setup.json')
    setup = json.loads(setup_path.read_text())
    assert setup['name'] == 'AINTLIBDrafts.' + stem, name
    assert setup['options']['autoImplicit'] is False, name
    assert setup['options']['relaxedAutoImplicit'] is False, name
    assert not setup.get('plugins') and not setup.get('dynlibs'), name
    command = next(entry['message'] for entry in trace['log'] if '--setup' in entry['message'])
    tokens = shlex.split(command)
    assert tokens[tokens.index('--setup') + 1] == str(setup_path), name
    assert str(isolated) in tokens, name
    assert '/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean' in tokens, name
    assert not any(t.startswith('-DautoImplicit') or t.startswith('-DrelaxedAutoImplicit') for t in tokens), name
    artifacts = {}
    for suffix in ('olean', 'olean.private', 'olean.server', 'ilean', 'ir', 'ir.sig'):
        artifact = wd / '.lake/build/lib/lean/AINTLIBDrafts' / (stem + '.' + suffix)
        data = artifact.read_bytes()
        assert data, artifact
        artifacts[suffix] = {'bytes': len(data), 'current_sha256': hashlib.sha256(data).hexdigest()}
    modules[name] = {'source_sha256': receipt['source_sha256'][name], 'checks': checks,
                     'examples': examples, 'trace_matches_receipt': True,
                     'setup_strict': True, 'artifacts': artifacts,
                     'trace_sha256': hashlib.sha256((wd / '.lake/build/lib/lean/AINTLIBDrafts' / (stem + '.trace')).read_bytes()).hexdigest(),
                     'setup_sha256': hashlib.sha256(setup_path.read_bytes()).hexdigest(),
                     'direct_print_provenance': print_provenance[name],
                     'declarations': [{ 'name': m.group(1), 'axioms': sorted(set(re.findall(r'[A-Za-z][A-Za-z.]*', m.group(2) or ''))) } for m in matches] }
    total_checks += checks
    total_examples += examples
    total_artifacts += len(artifacts)
    all_names |= module_names
    all_free |= module_free
    all_axioms |= module_axioms
assert total_checks == receipt['expected_axiom_check_count'] == receipt['observed_axiom_check_count'] == args.expected_checks
assert total_examples == receipt['sanity_example_count'] == args.expected_examples
assert total_artifacts == args.expected_modules * 6
assert all_names == set(receipt['audited_declarations'])
assert all_free == set(receipt['axiom_free_declarations'])
assert all_axioms == set(receipt['observed_axioms']) == allowed
build_path = pathlib.Path(receipt['build_log'])
build_data = build_path.read_bytes()
build_jobs_matches = re.findall(r'Build completed successfully \((\d+) jobs\)\.', build_data.decode())
assert build_jobs_matches == [str(args.expected_jobs)], build_jobs_matches
for path, revision in ((wd, receipt['aintlib_revision']),
                       (wd / '.lake/packages/mathlib', receipt['mathlib_revision'])):
    actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    assert actual == revision, (path, actual, revision)
    dirty = subprocess.check_output(['git', '-C', str(path), 'diff', '--name-only', 'HEAD'], text=True).splitlines()
    assert not dirty if path != wd else all(n == 'lakefile.toml' for n in dirty)
audit = {'verified_receipt': str(receipt_path), 'checkpoint_time': receipt['verified_at_utc'],
         'parent_receipt_byte_equal': True,
         'excluded_current_retained_sources': excluded_current_sources,
         'exact_inventory_sha256': hashlib.sha256('\n'.join(sorted(names)).encode()).hexdigest(),
         'aintlib_revision': receipt['aintlib_revision'],
         'mathlib_revision': receipt['mathlib_revision'],
         'toolchain': receipt['toolchain'],
         'build_jobs': args.expected_jobs,
         'unique_audited_declaration_count': len(all_names),
         'axiom_free_declaration_count': len(all_free),
         'strict_exact_lean_binary_in_all_traces': True,
         'cumulative_driver_session': args.cumulative_session,
         'receipt_sha256': hashlib.sha256(receipt_path.read_bytes()).hexdigest(),
         'prepared_source_snapshot_sha256': hashlib.sha256(args.prepared_source_snapshot.read_bytes()).hexdigest(),
         'historical99_receipt_sha256': prepared['historical99_receipt_sha256'],
         'historical99_independent_audit_sha256': prepared['historical99_independent_audit_sha256'],
         'historical99_build_log_sha256': prepared['historical99_build_log_sha256'],
         'preserved_historical99_archive_byte_exact': True,
         'named_post99_receipts_frozen_before_build': True,
         'frozen_config_files': prepared['config_files'],
         'exact_compiler_sha256': prepared['exact_compiler_sha256'],
         'prepared_direct_checks_sha256': hashlib.sha256(args.prepared_direct_checks.read_bytes()).hexdigest(),
         'includes_noncomputable_examples': True,
         'legal_apostrophe_declaration_names_supported': True,
         'exact_prints_match_frozen_independent_baseline_or_named_receipts': True,
         'build_log_sha256': hashlib.sha256(build_data).hexdigest(),
         'modules': modules, 'module_count': args.expected_modules, 'checks': total_checks,
         'examples': total_examples, 'available_artifacts': total_artifacts,
         'all_receipt_sources_current': True, 'all_traces_match': True,
         'all_setups_strict': True, 'no_diagnostics': True,
         'no_compiler_started': True, 'full_mathematical_review': False,
         'excluded_new_leaf': 'All temporary proofs and any later retained sources absent from this exact frozen checkpoint inventory'}
out = args.output
out.write_text(json.dumps(audit, indent=2) + '\n')
print(json.dumps({key: value for key, value in audit.items() if key != 'modules'}, indent=2))
