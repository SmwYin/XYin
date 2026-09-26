# Inventory: XYin/PhD/qExpansion_tactic/Examples.lean  (65 lines)

Demonstration/test file for the `#qexp` commands and the `qexp_coeff` term elaborator from `Qj.lean`: informational coefficient printouts, `#check`s of the elaborated proof terms, four `example`s (auto and manual mode for `qj` and `Delta`), and a commented-out stress test at n = 1000/2000. Contains NO declarations. It is imported by the library root `XYin.lean:39`.

## Declarations

(none — the file consists only of `open`, `#qexp` commands, `#check`s, `example`s and comments)

### `example` (auto mode, q·j)  — L33
- **Type**: `qj_qexpansion.coeff 4 = 864299970 := qexp_coeff qj 4`
- **What**: c(3) = 864299970 certified with the value computed during elaboration.
- **How**: `qexp_coeff` elaborator → `mkQexpCoeffProof` → `Eq.trans qj_qexpansion_coeff_eq (native certificate)`; depends on `Lean.ofReduceBool`.
- **Hypotheses**: none
- **Uses from project**: `qj_qexpansion`, `qexp_coeff` syntax/elaborator, `qjTarget`, `mkQexpCoeffProof`, `qj_qexpansion_coeff_eq`, `qjCoeffInt`
- **Used by**: n/a (example)
- **Visibility**: n/a
- **Lines**: 33
- **Notes**: `native_decide`-class trust (`Lean.ofReduceBool`); the same fact is proved by `rfl` in `jFunction/qexp_coeffs.lean:108–109` (`qj_qExpansion_coeff_four_aux`) without the axiom.

### `example` (manual mode, q·j) — L36
- **Type**: `qj_qexpansion.coeff 4 = 864299970 := qexp_coeff qj 4 864299970`
- **What**: same fact with the value supplied.
- **How**: manual branch of the elaborator (`elabTermEnsuringType x q(ℤ)`).
- **Hypotheses**: none
- **Uses from project**: as above
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 36
- **Notes**: —

### `example` (auto mode, Δ) — L46
- **Type**: `Delta_qexpansion.coeff 4 = -1472 := qexp_coeff Delta 4`
- **What**: τ(4) = −1472.
- **How**: as L33 with `deltaTarget`.
- **Hypotheses**: none
- **Uses from project**: `Delta_qexpansion`, `deltaTarget`, `Delta_qexpansion_coeff_eq`, `deltaCoeffInt`, `qexp_coeff`
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 46
- **Notes**: Duplicates `qexp_coeffs.lean:71–73 Delta_qExpansion_coeff_four` (proved by `rfl`).

### `example` (manual mode, Δ) — L49
- **Type**: `Delta_qexpansion.coeff 4 = -1472 := qexp_coeff Delta 4 (-1472)`
- **What**: same, manual.
- **How**: manual branch.
- **Hypotheses**: none
- **Uses from project**: as above
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 49
- **Notes**: —

### Commands / checks
- `#qexp qj coeff 4`, `#qexp qj precision 4` (L24–25); `#check qexp_coeff qj 4`, `#check qexp_coeff qj 4 864299970` (L28–29); `#qexp Delta coeff 4`, `#qexp Delta precision 4` (L39–40); `#check qexp_coeff Delta 4`, `#check qexp_coeff Delta 4 (-1472)` (L42–43); `#qexp qj coeff 100`, `#qexp qj precision 100` (L52–53). Each emits an info message (plus a `[qexp time: …ms]` message since `reportTiming = true`) on every `lake build`.
- Commented-out block L55–65: `#qexp qj coeff 1000`, `#qexp qj coeff 2000`, `#check qexp_coeff qj 2000` (238-digit coefficient stress test).

## File Summary
- Total declarations: 0 (0 defs, 0 lemmas/theorems, 0 instances, 0 other); 4 `example`s, 6 `#qexp`, 4 `#check`, 1 commented block
- Key API (used by 3+ others in the file): none
- Unused declarations: none (no declarations)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations (evidence for the analysis phases)
### Mathlib API candidates
- Not applicable (no definitions). Searched nothing.

### Missing API / repeated patterns
- None.

### Junk candidates
- The whole file is test-only: it contains only `#eval`-class commands (`#qexp`), `#check`s and `example`s — YES, it is test-only and contains `#qexp`/`#check`/`example` only (answering the batch question (d)). It is nevertheless imported by the library root (`XYin.lean:39`), so its 10 info messages + 4 timing messages appear in every full build and its native-evaluation examples run on every build. Move to a `test/` directory outside the `XYin` lib (lakefile has a single `[[lean_lib]] name = "XYin"` with no globs, so root-import closure = library).
- L21 `open scoped XYin.PhD.qExpansion_tactic` is redundant: that namespace declares nothing `scoped` (the `qexp_coeff` syntax is global, declared after `end`, and `#qexp` is a global `syntax`).
- L55–65 commented-out stress test.
- All four examples duplicate facts already proved axiom-free by `rfl` in `qexp_coeffs.lean:71–73, 108–109` — the examples show the elaborator works but add nothing to the library.

### Moral duplicates within this batch
- L33/L36 and L46/L49 are pairs proving the same statement two ways (auto vs manual) — intended as demos.

### Generalization notes
- None.
