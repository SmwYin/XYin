# XYin/PhD/qExpansion_tactic/Examples.lean

**Source path**: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/qExpansion_tactic/Examples.lean
**Project-internal imports**: [`XYin.PhD.qExpansion_tactic.Qj`]
**Namespace**: root (opens `XYin.PhD.qExpansion_tactic`, incl. scoped)

Demonstration/test file for the `#qexp` commands and the `qexp_coeff` proof-producing
term elaborator from Qj.lean. Contains only anonymous `example`s, `#qexp` command
invocations, and `#check`s — no named declarations. Notably it does NOT import
link.lean, so the examples are facts about the formal series `qj_qexpansion` /
`Delta_qexpansion`, not (directly) about the analytic modular objects.

### `example` (qj coefficient, auto mode)
- **Type**: `example : qj_qexpansion.coeff 4 = 864299970 := qexp_coeff qj 4`
- **What**: The 4th coefficient of the q·j series is 864299970 (the j-invariant Fourier coefficient c(3)), with the value discovered by the elaborator.
- **How**: Elaborated by the `qexp_coeff` term elaborator (auto form): `foo` computes the value and certifies it by native evaluation (`mkNativeDecideProofFor`), chained with `qj_qexpansion_coeff_eq`. Proof depends on the `ofReduceBool` axiom.
- **Hypotheses**: none
- **Uses from project**: [`qj_qexpansion` (Qj), `qexpCoeffAuto` syntax / `elab_rules : term` (Qj), hence `foo`, `qjCoeffInt`, `qj_qexpansion_coeff_eq`, `mkNativeDecideProofFor`]
- **Used by**: unused in file (anonymous)
- **Visibility**: public (anonymous example)
- **Lines**: 15 (1 line)
- **Notes**: none

### `example` (qj coefficient, manual mode)
- **Type**: `example : qj_qexpansion.coeff 4 = 864299970 := qexp_coeff qj 4 864299970`
- **What**: Same coefficient fact, but with the expected value supplied by the user and checked by the elaborator.
- **How**: `qexp_coeff` manual form: `fooWithValue` builds a native-decide certificate that `qjCoeffInt 4 = 864299970` and chains with `qj_qexpansion_coeff_eq`.
- **Hypotheses**: none
- **Uses from project**: [`qj_qexpansion` (Qj), `qexpCoeffManual` syntax / `elab_rules : term` (Qj), hence `fooWithValue`, `qjCoeffInt`, `qj_qexpansion_coeff_eq`, `mkNativeDecideProofFor`]
- **Used by**: unused in file (anonymous)
- **Visibility**: public (anonymous example)
- **Lines**: 17 (1 line)
- **Notes**: none

### `example` (Delta coefficient, auto mode)
- **Type**: `example : Delta_qexpansion.coeff 4 = -1472 := qexp_coeff Delta 4`
- **What**: The 4th coefficient of the Δ series is τ(4) = −1472, value discovered automatically.
- **How**: `qexp_coeff` auto form via `deltaFoo` (native-decide certificate for `deltaCoeffInt 4 = −1472` chained with `Delta_qexpansion_coeff_eq`).
- **Hypotheses**: none
- **Uses from project**: [`Delta_qexpansion` (Qj), `qexpCoeffAuto` syntax / `elab_rules : term` (Qj), hence `deltaFoo`, `deltaCoeffInt`, `Delta_qexpansion_coeff_eq`, `mkNativeDecideProofFor`]
- **Used by**: unused in file (anonymous)
- **Visibility**: public (anonymous example)
- **Lines**: 25 (1 line)
- **Notes**: none

### `example` (Delta coefficient, manual mode)
- **Type**: `example : Delta_qexpansion.coeff 4 = -1472 := qexp_coeff Delta 4 (-1472)`
- **What**: Same τ(4) = −1472 fact with the value supplied and checked.
- **How**: `qexp_coeff` manual form via `deltaFooWithValue`.
- **Hypotheses**: none
- **Uses from project**: [`Delta_qexpansion` (Qj), `qexpCoeffManual` syntax / `elab_rules : term` (Qj), hence `deltaFooWithValue`, `deltaCoeffInt`, `Delta_qexpansion_coeff_eq`, `mkNativeDecideProofFor`]
- **Used by**: unused in file (anonymous)
- **Visibility**: public (anonymous example)
- **Lines**: 27 (1 line)
- **Notes**: none

### Non-declaration content
- Lines 3–4: `set_option linter.style.header false`, `set_option linter.style.longLine false` (file-level).
- Lines 9–10, 19–20, 29–30: `#qexp qj coeff 4`, `#qexp qj precision 4`, `#qexp Delta coeff 4`, `#qexp Delta precision 4`, `#qexp qj coeff 100`, `#qexp qj precision 100` — command invocations exercising the `#qexp` elaborator (display only, no proof terms).
- Lines 12–13, 22–23: `#check` invocations of both `qexp_coeff` forms.
- Lines 31–40: commented-out stress tests (`#qexp qj coeff 1000/2000` and two `example`s proving the 2000th q·j coefficient, a 238-digit integer, in both auto and manual modes) — evidence the native-evaluation route scales to n = 2000.

### File Summary
- Total declarations: 4 (0 defs, 4 lemmas/theorems [anonymous examples], 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): []
- Unused declarations (not used by anything in this file): [all 4 anonymous examples — test/demo content by nature]
- Declarations with sorry: []
- Declarations with set_option: [] (two file-level set_options: `linter.style.header false`, `linter.style.longLine false`, lines 3–4)
- Proofs >30 lines: []
