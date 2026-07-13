# Cleanup record: T002

## Baseline and scope

- Target: the analytic/lattice bridge in `XYin/PhD/Cox/LatticeJ.lean`.
- New declarations: `periodPair_G_eq_aux`, `riemannZeta_six_aux`,
  `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`, `Delta_eq_E4_E6`, and
  `j_eq_periodPair_j`.
- Baseline and final target build: `lake build XYin.PhD.Cox.LatticeJ`.
- Direct diagnostics show only planned sorries owned by later tickets.

## API and statement audit

- Fixed a latent signature error: without `open Real`, the bare `π` in the two public
  comparison theorems became an implicit complex parameter. Their checked types now contain
  `↑Real.pi` and no hidden `π` argument.
- Mathlib has the normalized Eisenstein series, zeta-value formula, eta discriminant,
  `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`, and discriminant product API, but no
  lattice `PeriodPair.G` comparison. The private reindexing lemma is therefore genuine local API.
- The historical `Delta_E4_eqn` bridge was rejected because its axiom audit contains `sorryAx`.
- The project `Delta` bridge instead unfolds through `Delta_eq_eta_pow` to mathlib's
  discriminant and uses the sorry-free cubic identity directly.
- No parameter admits a sound weakening: `τ : ℍ`, `k : ℕ`, and `3 ≤ k` are required by the
  relevant Eisenstein API. There are no reversed inequalities.

## Cleanup and simplify

- Reindexed the lattice `tsum` through `latticeEquivProd` and the `Fin 2`/product equivalences.
- Packed the multi-line helper conclusion to the 100-column policy and merged consecutive rewrites.
- Kept only the reusable two-use `periodPair_G_eq_aux` and the nontrivial zeta-six calculation;
  single-use E₄/E₆ wrapper lemmas were inlined.
- Removed single-use local `have`s and semicolon tactic chains.
- Replaced the multi-paragraph implementation docstring on `Delta_eq_E4_E6` by a one-sentence
  statement docstring.
- Simplified `j_eq_periodPair_j`: totalized division means no discriminant nonvanishing is
  needed. The proof cancels only the fixed nonzero factor `64π¹²/27`, avoiding any T003
  dependency.
- All names pass the naming gate; private helpers use the `_aux` suffix; proof bodies are at
  most fifteen lines and contain no narrative comments.

## Gates

| Gate | Result |
|---|---|
| `lake_build_file` | pass |
| `definition_protected` | pass; no definition body changed |
| `theorem_statement_protected` | pass relative to the intended source statement; `open Real` repairs the accidental implicit `π` |
| `structure_gate` | pass |
| `naming_gate` | pass |
| `line_packing_gate` | pass |
| `inequality_orientation_gate` | pass |
| `cumulative_no_unintended_breakage` | pass |
| `git diff --check` | pass |
| axiom audit | only `propext`, `Classical.choice`, `Quot.sound` |

## Buzz

- Outcome: FAST-BOARD. A threshold-1 ms profiled compile found no declaration remotely near
  the 1000 ms budget; the largest T002 tactic nodes were about 25 ms.
- No heartbeat override, profiler scaffold, or deferral remains.

## Phase checklist

- [x] Doctor
- [x] Prepare and read references
- [x] Style/API audit
- [x] File-level import/scope fixes
- [x] Per-declaration golf and generality audit
- [x] Non-rename refactoring
- [x] Rename pass (empty)
- [x] Final diagnostics and gates
- [x] Simplify pass
- [x] Buzz pass
- [x] Report
