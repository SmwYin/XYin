# Cleanup record: T005

## Baseline and scope

- Target: `j_eq_iff_exists_sl2_smul_eq` and `j_surjective` in
  `XYin/PhD/Cox/LatticeJ.lean`.
- Added the direct dependencies `Mathlib.NumberTheory.ModularForms.NormTrace` and
  `XYin.PhD.Modularforms.ForMathlib_Cusps` for the weight-zero cusp-form argument.
- Both focused and full-repository `lake build` pass; `LatticeJ.lean` is now entirely
  sorry-free.

## API and mathematical audit

- Injectivity is exactly the requested chain: analytic `j` equals the normalized-lattice `j`,
  lattice `j` equality is homothety, and normalized homothety is an `SL₂(ℤ)` orbit.
- Surjectivity uses contradiction. If `c` is omitted by `j`, then `(j-c)⁻¹` is holomorphic,
  invariant of weight zero, and vanishes at infinity. It defines a level-one weight-zero cusp
  form, hence is constant and therefore zero, contradicting its nonvanishing at `τ = i`.
- Reproved the two missing clean interfaces locally: differentiability of `j` from the
  holomorphicity of `E₄` and `Δ`, and `qj → 1` from `E₄ → 1` and `q/Δ → 1`.
- Explicitly rejected the existing `qj` constant-coefficient route because its transitive axiom
  audit contains `sorryAx`/native q-expansion axioms. The replacement uses mathlib's clean
  `EisensteinSeries.E_qExpansion_coeff_zero`.
- A fundamental-domain proof was considered, but the current API has no comparable range or
  properness theorem; it would be much longer than the cusp-form argument.

## Cleanup and simplify

- The injectivity theorem reduces to a single four-bridge rewrite.
- Removed an unused local function from the surjectivity proof and replaced
  `Classical.arbitrary ℍ` by the explicit point `i : ℍ`.
- Retained eight nontrivial private helpers matching the analytic pipeline; each has an `_aux`
  suffix and avoids exposing new public API.
- Normalized helper naming to `mdifferentiable`, `mdiff`, and `isZeroAtImInfty`, packed every
  line to at most 100 columns, and introduced no heartbeat or tactic escape hatch.

## Validation

- `#print axioms` for both public declarations reports exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- Independent `T` and `S` tests check the injectivity orbit direction; a surjectivity sanity
  declaration produces `∃ τ : ℍ, j τ = c` for every `c`, so its witness type enforces upper
  half-plane membership.
- `git diff --check`, naming, line-packing, forbidden-tactic, and no-sorry scans pass.
- Full `lake build` completes successfully.

## Buzz

- Outcome: FAST-BOARD. A threshold-5 ms profiled compile found no declaration near the 1000 ms
  budget; the largest reported local tactic node was below 70 ms.
- No heartbeat override, profiler scaffold, or deferral remains.

## Phase checklist

- [x] Doctor
- [x] Prepare and read references
- [x] Style/API audit
- [x] File-level import audit
- [x] Per-declaration golf and generality audit
- [x] Non-rename refactoring
- [x] Rename pass
- [x] Final diagnostics and gates
- [x] Simplify pass
- [x] Buzz pass
- [x] Report
