# Cleanup report — worker `lqe` (LaurentQExpansion / Algebra / IntegralPowerSeries / uniqueness)

Date: 2026-09-26. Sandbox: `/Users/dfa25dxu/Projects/Lean/.xyin-sandboxes/lqe`.

## 1. Build

Final `lake build` in SB (both default targets `XYin`, `XYinTest`), `.scratch/build6.log`:

```
✔ [3917/3918] Built XYin (4.3s)
Build completed successfully (3918 jobs).
```

No new warnings in the four owned files (the only linter hit during the session, a 101-character
line in `Algebra.lean`, was fixed). All owned files pass
`#lint only simpNF simpComm simpVarHead docBlame defLemma unusedArguments`.

## 2. Files changed (lines before → after)

| File | before | after | decls before → after |
|---|---|---|---|
| `XYin/PhD/LaurentQExpansion/LaurentQExpansion.lean` | 706 | 849 | 49 → 87 |
| `XYin/PhD/LaurentQExpansion/Algebra.lean` | 439 | 455 | 28 → 37 |
| `XYin/PhD/IntegralPowerSeries/IntegralPowerSeries.lean` | 229 | 267 | 33 → 39 |
| `XYin/uniqueness.lean` | 297 | 305 | 15 → 15 |

No files added or deleted; `XYin.lean` untouched. Accounting (docstrings included): the
109 declarations that survive went from 1294 to 1067 lines (−227, although ≈ 30 docstring lines
were added to previously undocumented lemmas); 16 declarations / 84 lines were deleted (the 4
from `Algebra.lean`, 31 lines, were private helpers: 3 moved to `LaurentQExpansion.lean` as
public API, 1 replaced by the public 𝓝[≠] lemma); 69 new declarations / ≈ 420 lines of API
were added.

Merge notes for the orchestrator: (i) `cuspFunction_poleRemoved_eq` now reads
`(h) (f) (hq0) (hqnorm)` (its unused `hmero` was dropped) and `iteratedDeriv_sq_mul` moved from
`PeriodPair.` to the root namespace (generalised) — both had 0 users outside the owned set at
base, but check other workers' new code; (ii) new `@[simp]` lemmas (§3, Task 3) were checked
against the base tree only — if a merged downstream `simpa … using` collapses to `True`, drop
the attribute as done for `cuspFunction_const`.

## 3. Done items

### Task 1 — transport family (`LaurentQExpansion.lean`)
* New `norm_lt_one_mem_nhdsNE_zero` (moved from Algebra.lean, made public) and
  `eventually_ne_zero_and_norm_lt_one`; used in `analyticAt_cuspFunction_of_not_pos`,
  `cuspFunction_qpow_mul_eventuallyEq`, `cuspFunction_poleRemoved_eventuallyEq`,
  `cuspFunction_poleRemoved_nat_mul_eventuallyEq` (4 former inline punctured-disc blocks).
* New `cuspFunction_apply_of_ne_zero`, `cuspFunction_eventuallyEq_comp`,
  `cuspFunction_comp_eventuallyEq`, `cuspFunction_comp₂_eventuallyEq`. The three private
  `cuspFunction_{add,mul,const}_eventuallyEq` (29 lines) are deleted; `meromorphicAt_cuspFunction_
  add/mul` are now one-line `congr`s through `cuspFunction_comp₂_eventuallyEq`, `_const` goes
  through `cuspFunction_const`. (The private ones could not be kept public: `CuspData.lean` has
  a private `Cox.cuspFunction_mul_eventuallyEq` — no clash because of its namespace, but no need.)
* `cuspFunction_const` (global equality, moved from Algebra.lean), `analyticAt_cuspFunction_const`
  (moved), new `qExpansion_const` [simp].
* New `cuspFunction_nat_mul_eventuallyEq`; `meromorphicAt_cuspFunction_nat_mul` 13 → 7 lines,
  `meromorphicAt_cuspFunction_of_nat_mul` 6 → 1, `meromorphicOrderAt_cuspFunction_nat_mul`
  19 → 2 (via new `meromorphicOrderAt_comp_const_mul_pow`).
* New `cuspFunction_qpow_mul_eventuallyEq` (𝓝[≠] form): replaces `hEq_shift` in
  `analyticAt_cuspFunction_poleRemoved` and the private 𝓝-lemma of Algebra.lean.

### Task 2 — closure lemmas and pole-order helpers
* `meromorphicAt_cuspFunction_{neg,sub,const_mul,smul,pow,inv,div,polynomial_eval}` (1 line each
  via the transport lemmas); general `MeromorphicAt.polynomial_eval` (mathlib gap; replaces
  CuspData.lean's private `meromorphicAt_polynomial_eval`).
* `meromorphicAt_cuspFunction_finset_sum/prod`: 12 → 4 lines each (`Finset.sum/prod_induction`).
* Algebra.lean: `laurentqExpansion_{const_mul,smul,sub,pow,polynomial_eval}`; the last has
  exactly the hypotheses of the Cox inductions (`0 < h`, `MeromorphicAt (cuspFunction h f) 0`);
  verified in `.scratch/test_cox.lean` that it closes `IntegralDescent.lean:35–52` and
  `DiagonalLaurent.lean:164–185` by `exact` (`polynomialIn P j` unfolds by defeq).
* `poleOrder` helpers: `poleOrder_eq_iff`, `poleOrder_lt_iff` (replaces Cox private
  `poleOrder_lt_of_neg_lt_meromorphicOrderAt`), `poleOrder_eq_zero_of_analyticAt`,
  `poleOrder_const/zero/one` [simp], `poleOrder_neg`, `poleRemoved_apply` [simp],
  `poleRemoved_of_poleOrder_eq_zero` (replaces 3 inline `hfun` blocks),
  `to_qExpansion_of_poleOrder_eq_zero`, `to_qExpansion_const` [simp],
  `cuspFunction_poleRemoved_eventuallyEq`, `laurentqExpansion.coeff_{eq_zero_of_lt',
  neg_poleOrder_add', of_geq'}` (pole order given by an equation),
  `laurentqExpansion.eq_qExpansion_of_{poleOrder_eq_zero,analyticAt}`,
  `laurentqExpansion.order_eq_neg_poleOrder`.
* Re-proofs through them: `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` 18 → 1 line,
  `analyticAt_cuspFunction_iff_poleOrder_eq_zero` 11 → 4, `cuspFunction_poleRemoved_eq` 14 → 7,
  `laurentqExpansion.poleOrder_to_order` 18 → 2, `to_qExpansion_eq_powerSeriesPart` 11 → 4,
  `eq_qExpansion_iff` 14 → 6, `analyticAt_cuspFunction_poleRemoved` 44 → 21 (no `0 < h` case
  split any more — `cuspFunction_poleRemoved_eventuallyEq` is hypothesis-free — and the sign split
  merged into one `Int.toNat` case), `to_qExpansion_coeff_zero_ne` 22 → 17, coefficient lemmas
  `coeff_eq_HahnSeries_add` 9 → 1, `coeff_eq_zero_of_lt` 7 → 1, `coeff_of_geq` 8 → 4,
  `coeff_of_qExpansion` 7 → 3, circle-integral helper `exists_pos_lt_one_…` 21 → 7.
* Order bookkeeping (step7 L35): `analyticOrderAt_const_mul_pow`,
  `meromorphicOrderAt_comp_const_mul_pow` (general `𝕜`, `E`).
* `periodic_comp_ofComplex_of_vadd` (public copy of Congruence.lean's private lemma, H21).

### Task 3 — simp API
`@[simp]`: `qExpansion_const`, `poleOrder_const/zero/one`, `poleRemoved_apply`,
`to_qExpansion_const`, `laurentqExpansion.coeff_neg_poleOrder_add`,
`laurentqExpansion.coeff_neg_poleOrder`, `natMulOrderEmbedding_apply`,
`coeff_mapAlgHom_ofId_int`, `coeToComplexPowerSeries.ringHom_apply` (existing simp:
`laurentqExpansion_const/zero/one`, `powerSeriesMapAlgHom_apply`). Full build green.
Dropped after they broke downstream `simpa … using` (per the rules; documented in the
docstrings): `cuspFunction_const` (AnalyticSupport.lean:53 — hypothesis collapsed to `True`
while the goal is stated with `(1 : ℍ → ℂ)`), `coeff_toHasCoeffsInPowerSeries` and
`coeff_toIntegralPowerSeries_cast` (jfunction.lean:210 — `coeTo_of_toIntegralPowerSeries`
collapsed to `True`). `laurentqExpansion_add/mul/neg` need `0 < h` and meromorphy: not tagged.

### Task 4 — period change (`Algebra.lean`)
* New `natMulOrderEmbedding m hm : ℤ ↪o ℤ` (`k ↦ m * k`), `HahnSeries.ofPowerSeries_expand`
  (`expand m` ↔ `embDomain`), `laurentqExpansion_nat_mul` (the embDomain packaging, 9 lines).
* `laurentqExpansion_nat_mul_coeff` 31 → 3 lines and `_of_not_dvd` 23 → 3 lines are now
  corollaries (`HahnSeries.embDomain_coeff` / `embDomain_notin_range`); statements unchanged.
* `cuspFunction_poleRemoved_nat_mul_eventuallyEq` 22 → 9, `to_qExpansion_nat_mul` 17 → 12.

### Task 5 — ring laws (`Algebra.lean`)
* Shared private helper `map_finset_prod_of_mul` (+ `@[to_additive] map_finset_sum_of_add`):
  a map multiplicative on a multiplicatively closed predicate commutes with `Finset.prod`.
  `laurentqExpansion_finset_sum/prod` 16 → 5 lines each (the two `Finset.induction_on` copies).
* `laurentqExpansion_neg` 11 → 2 (via `_const_mul`), `laurentqExpansion_const` 11 → 3.
* No bundled `RingHom` (refuted in step5, not forced).

### Task 6 — `IntegralPowerSeries.lean`
* New: `coeff_powerSeriesMapAlgHom`, `coeff_mapAlgHom_ofId_int` [simp],
  `coeToComplexPowerSeries.ringHom_apply` [simp], `coeToComplexPowerSeries.coeff_ringHom(_int)`,
  `coeff_toHasCoeffsInPowerSeries`, `IntegralPowerSeries.mapAlgHom_ofId_toIntegralPowerSeries`,
  `IntegralPowerSeries.coeff_toIntegralPowerSeries_cast`,
  `IntegralPowerSeries.toIntegralPowerSeries_eq_of_map_eq`, `hasCoeffsIn_pow/_algebraMap/_X/
  _finset_sum/_finset_prod`. All replacements for the jFunction/link sites verified in
  `.scratch/test_jf.lean`.
* Deleted (0 users anywhere, pure aliases/`Iff.rfl`): `powerSeriesMapSubmodule`,
  `mem_powerSeriesMapSubmodule_iff`, the middle layer `RIntegralCPowerSeriesSubring`,
  `IsRIntegralCPowerSeries`, `IsIntegralCPowerSeries`, `isRIntegralCPowerSeries_iff_coeff`,
  `toRIntegralCPowerSeries`, `coeToComplexPowerSeries_of_toRIntegralCPowerSeries` (step5 row 29);
  the ℤ layer is now defined directly from the generic one (same reducible normal forms;
  `IntegralPowerSeriesSubring.pow_mem` in Deltaqexpansions still works).
* Kept: `modularFormModuleofIsScalarTower`, `qExpansion_smul_algebra`,
  `modularFormQExpansionSubmodule`, `powerSeriesMapAlgHom(_apply)`,
  `coeToComplexPowerSeries.ringHom`, all `hasCoeffsIn_*` closure lemmas.
* `IsIntegralPowerSeriesmod` re-proved through `coeff_toIntegralPowerSeries_cast`.

### Task 7 — `uniqueness.lean`
* Copyright header + `/-! -/` module docstring after the imports; dropped the unused imports
  `Mathlib.Topology.Algebra.Module.Cardinality` and `Mathlib.Data.Nat.Choose.Cast`.
* `key_eventuallyEq` 31 → 21 lines: `eventuallyEq_nhds_of_eventuallyEq_nhdsNE` replaces the
  `pure`/`nhdsNE_sup_pure` trick, and `refine` avoids restating the goal.
* New `AnalyticAt.eventuallyEq_of_iteratedDeriv_eq` (mathlib gap, L40);
  `weierstrassP_eventuallyEq` goes through it.
* `iteratedDeriv_sq_mul` generalised (G-11) to any `NontriviallyNormedField 𝕜` with
  `ContDiffAt 𝕜 n g 0`; proof no longer needs `CharZero`/division (`Nat.descFactorial`); moved
  out of `namespace PeriodPair` (0 users outside the file).
* `iteratedDeriv_eq_of_invariants`: `hG4/hG6` hoisted out of the induction, `hcoef` 8 → 3 lines.
* `invariantsDetermineLattice` deleted: trivial restatement of `lattice_eq_of_g₂_eq_of_g₃_eq`
  (`fun _ _ ↦ lattice_eq_of_g₂_eq_of_g₃_eq`), 0 uses, stale `talk4.lean` docstring.

### Task 8 — mathlib swaps
* `analyticTaylor` kept (private) and related to mathlib by
  `analyticTaylor_cuspFunction : analyticTaylor (cuspFunction h f) = qExpansion h f := rfl`, used
  in `to_qExpansion_nat_mul` instead of unfolding `qExpansion`.
* `cuspFunction_nat_mul_eq_cuspFunction_pow`: the fragile `simp only; ring_nf; field_simp` block
  reduced to `field_simp; push_cast; ring`.
* Docstrings added to 22 previously undocumented lemmas of `LaurentQExpansion.lean` and 4 of
  `uniqueness.lean`.

## 4. New public API (exact statements; `h : ℝ`, `f g : ℍ → ℂ`)

LaurentQExpansion.lean (root namespace unless stated):
* `norm_lt_one_mem_nhdsNE_zero : {q : ℂ | ‖q‖ < 1} ∈ 𝓝[≠] 0`
* `eventually_ne_zero_and_norm_lt_one : ∀ᶠ q : ℂ in 𝓝[≠] 0, q ≠ 0 ∧ ‖q‖ < 1`
* `cuspFunction_apply_of_ne_zero (h) (f) (hq : q ≠ 0) : cuspFunction h f q = f (ofComplex (invQParam h q))`
* `cuspFunction_eventuallyEq_comp (h) (f) : cuspFunction h f =ᶠ[𝓝[≠] 0] f ∘ ofComplex ∘ invQParam h`
* `cuspFunction_comp_eventuallyEq (h) (φ : ℂ → ℂ) (f) : cuspFunction h (fun τ ↦ φ (f τ)) =ᶠ[𝓝[≠] 0] fun q ↦ φ (cuspFunction h f q)`
* `cuspFunction_comp₂_eventuallyEq (h) (op : ℂ → ℂ → ℂ) (f g) : cuspFunction h (fun τ ↦ op (f τ) (g τ)) =ᶠ[𝓝[≠] 0] fun q ↦ op (cuspFunction h f q) (cuspFunction h g q)`
* `cuspFunction_const (h) (a) : cuspFunction h (fun _ ↦ a) = fun _ ↦ a` (not simp)
* `analyticAt_cuspFunction_const (h) (a) : AnalyticAt ℂ (cuspFunction h (fun _ ↦ a)) 0`
* `@[simp] qExpansion_const (h) (a) : qExpansion h (fun _ ↦ a) = PowerSeries.C a`
* `meromorphicAt_cuspFunction_neg (hf : MeromorphicAt (cuspFunction h f) 0) : MeromorphicAt (cuspFunction h (fun τ ↦ -f τ)) 0`; `_inv (hf)` : same with `fun τ ↦ (f τ)⁻¹`
* `meromorphicAt_cuspFunction_sub (hf) (hg) : MeromorphicAt (cuspFunction h (fun τ ↦ f τ - g τ)) 0`; `_div (hf) (hg)` : same with `fun τ ↦ f τ / g τ`
* `meromorphicAt_cuspFunction_const_mul (a) (hf) : MeromorphicAt (cuspFunction h (fun τ ↦ a * f τ)) 0`; `_smul (a) (hf) : MeromorphicAt (cuspFunction h (a • f)) 0`
* `meromorphicAt_cuspFunction_pow (hf) (n) : MeromorphicAt (cuspFunction h (fun τ ↦ f τ ^ n)) 0`
* `MeromorphicAt.polynomial_eval (hg : MeromorphicAt g x) (P : 𝕜[X]) : MeromorphicAt (fun w ↦ P.eval (g w)) x`
* `meromorphicAt_cuspFunction_polynomial_eval (hf) (P : ℂ[X]) : MeromorphicAt (cuspFunction h (fun τ ↦ P.eval (f τ))) 0`
* `periodic_comp_ofComplex_of_vadd (hf : ∀ τ, f (h +ᵥ τ) = f τ) : Periodic (f ∘ ofComplex) h`
* `analyticOrderAt_const_mul_pow (hc : c ≠ 0) (r) : analyticOrderAt (fun q : 𝕜 ↦ c * q ^ r) 0 = r`
* `meromorphicOrderAt_comp_const_mul_pow (hF : MeromorphicAt F 0) (hc : c ≠ 0) (hr : r ≠ 0) : meromorphicOrderAt (F ∘ fun q ↦ c * q ^ r) 0 = meromorphicOrderAt F 0 * r`
* `cuspFunction_nat_mul_eventuallyEq (hfper : Periodic (f ∘ ofComplex) h) : cuspFunction (m * h) f =ᶠ[𝓝[≠] 0] cuspFunction h f ∘ fun q ↦ q ^ m`
* `poleOrder_eq_iff (hr : r ≠ 0) : poleOrder h f = r ↔ meromorphicOrderAt (cuspFunction h f) 0 = ((-(r:ℤ) : ℤ) : WithTop ℤ)`
* `poleOrder_lt_iff (hm : 0 < m) : poleOrder h f < m ↔ ((-(m:ℤ) : ℤ) : WithTop ℤ) < meromorphicOrderAt (cuspFunction h f) 0`
* `poleOrder_eq_zero_of_analyticAt (hf : AnalyticAt ℂ (cuspFunction h f) 0) : poleOrder h f = 0`
* `@[simp] poleOrder_const (h) (a) : poleOrder h (fun _ ↦ a) = 0`, `poleOrder_zero (h) : poleOrder h 0 = 0`, `poleOrder_one (h) : poleOrder h 1 = 0`
* `poleOrder_neg (h) (f) : poleOrder h (fun τ ↦ -f τ) = poleOrder h f`
* `@[simp] poleRemoved_apply (h) (f) (τ) : poleRemoved h f τ = 𝕢 h τ ^ poleOrder h f * f τ`
* `poleRemoved_of_poleOrder_eq_zero (h0 : poleOrder h f = 0) : poleRemoved h f = f`
* `to_qExpansion_of_poleOrder_eq_zero (h0) : to_qExpansion h f = qExpansion h f`; `@[simp] to_qExpansion_const (h) (a) : to_qExpansion h (fun _ ↦ a) = PowerSeries.C a`
* `cuspFunction_qpow_mul_eventuallyEq (hh : 0 < h) (f) (n) : cuspFunction h (fun τ ↦ 𝕢 h τ ^ n * f τ) =ᶠ[𝓝[≠] 0] fun q ↦ q ^ n * cuspFunction h f q`
* `cuspFunction_poleRemoved_eventuallyEq (h) (f) : cuspFunction h (poleRemoved h f) =ᶠ[𝓝[≠] 0] fun q ↦ q ^ poleOrder h f * cuspFunction h f q` (no hypotheses)
* `laurentqExpansion.coeff_eq_zero_of_lt' (hM : poleOrder h f = M) (hn : n < -M) : (laurentqExpansion h f).coeff n = 0`
* `laurentqExpansion.coeff_neg_poleOrder_add' (hM : poleOrder h f = M) (n : ℕ) : (laurentqExpansion h f).coeff (-M + n) = (to_qExpansion h f).coeff n`
* `laurentqExpansion.coeff_of_geq' (hM : poleOrder h f = M) (hn : -M ≤ n) : (laurentqExpansion h f).coeff n = (to_qExpansion h f).coeff (n + M).toNat`
* `laurentqExpansion.eq_qExpansion_of_poleOrder_eq_zero (h0) : laurentqExpansion h f = qExpansion h f`; `…_of_analyticAt (hf : AnalyticAt ℂ (cuspFunction h f) 0)` (same conclusion)
* `laurentqExpansion.order_eq_neg_poleOrder (hmero) (h0 : poleOrder h f ≠ 0) : (laurentqExpansion h f).order = -(poleOrder h f)`

Algebra.lean:
* `analyticAt_cuspFunction_qpow_mul (hh) (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n) : AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ n * f τ)) 0` (was private)
* `analyticAt_cuspFunction_qParam_pow (hh) (n) : AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ n)) 0`
* `qExpansion_qParam_pow (hh) (n) : qExpansion h (fun τ ↦ 𝕢 h τ ^ n) = X ^ n` (was private)
* `qExpansion_qpow_mul (hh) (hf) (n) : qExpansion h (fun τ ↦ 𝕢 h τ ^ n * f τ) = X ^ n * qExpansion h f` (was private)
* `laurentqExpansion_qParam_pow (hh) (n) : laurentqExpansion h (fun τ ↦ 𝕢 h τ ^ n) = HahnSeries.single n 1`
* `laurentqExpansion_const_mul (hh) (a) (hf) : laurentqExpansion h (fun τ ↦ a * f τ) = HahnSeries.C a * laurentqExpansion h f`
* `laurentqExpansion_smul (hh) (a) (hf) : laurentqExpansion h (a • f) = a • laurentqExpansion h f`
* `laurentqExpansion_sub (hh) (hf) (hg) : laurentqExpansion h (fun τ ↦ f τ - g τ) = laurentqExpansion h f - laurentqExpansion h g`
* `laurentqExpansion_pow (hh) (hf) (n) : laurentqExpansion h (fun τ ↦ f τ ^ n) = laurentqExpansion h f ^ n`
* `laurentqExpansion_polynomial_eval (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0) (P : ℂ[X]) : laurentqExpansion h (fun τ ↦ P.eval (f τ)) = P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion h f)`
* `natMulOrderEmbedding (m) (hm : m ≠ 0) : ℤ ↪o ℤ` (`k ↦ m * k`), `@[simp] natMulOrderEmbedding_apply : natMulOrderEmbedding m hm k = m * k`
* `HahnSeries.ofPowerSeries_expand (m) (hm) (F : R⟦X⟧) : ofPowerSeries ℤ R (F.expand m hm) = embDomain (natMulOrderEmbedding m hm) (ofPowerSeries ℤ R F)`
* `laurentqExpansion_nat_mul (hm : m ≠ 0) (hmero : MeromorphicAt (cuspFunction h f) 0) (hfper : Periodic (f ∘ ofComplex) h) : laurentqExpansion (m * h) f = HahnSeries.embDomain (natMulOrderEmbedding m hm) (laurentqExpansion h f)`

IntegralPowerSeries.lean:
* `coeff_powerSeriesMapAlgHom (R A) (f) (n) : (powerSeriesMapAlgHom R A f).coeff n = algebraMap R A (f.coeff n)`
* `@[simp] coeff_mapAlgHom_ofId_int (F : ℤ⟦X⟧) (n) : (PowerSeries.mapAlgHom (Algebra.ofId ℤ ℂ) F).coeff n = (F.coeff n : ℂ)`
* `hasCoeffsIn_pow (R A) (hx) (n)`, `hasCoeffsIn_algebraMap (R A) (r) : HasCoeffsIn R A (algebraMap R A⟦X⟧ r)`, `hasCoeffsIn_X (R A)`, `hasCoeffsIn_finset_sum (R A) (hx : ∀ i ∈ s, HasCoeffsIn R A (x i))`, `hasCoeffsIn_finset_prod` (`[CommSemiring A]`)
* `@[simp] coeToComplexPowerSeries.ringHom_apply (R) (f) : coeToComplexPowerSeries.ringHom R f = f.map (algebraMap R ℂ)`
* `coeToComplexPowerSeries.coeff_ringHom (R) (f) (n) : (… f).coeff n = algebraMap R ℂ (f.coeff n)`; `…coeff_ringHom_int (f : ℤ⟦X⟧) (n) : (coeToComplexPowerSeries.ringHom ℤ f).coeff n = (f.coeff n : ℂ)`
* `coeff_toHasCoeffsInPowerSeries (R A) (hf) (n) : algebraMap R A ((toHasCoeffsInPowerSeries R A hf).coeff n) = f.coeff n` (not simp)
* `IntegralPowerSeries.mapAlgHom_ofId_toIntegralPowerSeries (hf) : PowerSeries.mapAlgHom (Algebra.ofId ℤ ℂ) (toIntegralPowerSeries hf) = f`
* `IntegralPowerSeries.coeff_toIntegralPowerSeries_cast (hf) (n) : ((toIntegralPowerSeries hf).coeff n : ℂ) = f.coeff n` (not simp)
* `IntegralPowerSeries.toIntegralPowerSeries_eq_of_map_eq (hf) (hg : coeToComplexPowerSeries.ringHom ℤ g = f) : toIntegralPowerSeries hf = g`

uniqueness.lean:
* `AnalyticAt.eventuallyEq_of_iteratedDeriv_eq [CompleteSpace 𝕜] [CharZero 𝕜] (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) (h : ∀ n, iteratedDeriv n f x = iteratedDeriv n g x) : f =ᶠ[𝓝 x] g`
* `iteratedDeriv_sq_mul (g : 𝕜 → 𝕜) (hg : ContDiffAt 𝕜 n g 0) (hn : 2 ≤ n) : iteratedDeriv n (fun z ↦ z ^ 2 * g z) 0 = n * (n - 1) * iteratedDeriv (n - 2) g 0` (was `PeriodPair.iteratedDeriv_sq_mul` for `ℂ`, analytic `g`)

Statement changes of existing public lemmas (all with 0 users outside the owned set):
`cuspFunction_poleRemoved_eq` lost its unused `hmero` hypothesis and now takes `(h) (f)`
explicitly; `iteratedDeriv_sq_mul` (see above). Every other existing name/statement is unchanged.

## 5. Kept on purpose (genuine but unused)
Circle-integral subtree (`qExpansion_coeff_eq_circleIntegral_of_differentiableOn`,
`exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt`, three private helpers,
`laurentqExpansion_coeff_eq_circleIntegral`); `meromorphicAt_of_comp_pow`;
`meromorphicAt_cuspFunction_nat_mul`; `analyticTaylor_comp_pow`; `to_qExpansion_nat_mul`;
`cuspFunction_nat_mul_eq_cuspFunction_pow`; `to_qExpansion_ne_zero`;
`laurentqExpansion.to_qExpansion_eq_powerSeriesPart`; `laurentqExpansion.coeff_zero`;
`laurentqExpansion_one`; `modularFormModuleofIsScalarTower`, `qExpansion_smul_algebra`,
`modularFormQExpansionSubmodule`, `hasCoeffsIn_{one,neg,sub,C_algebraMap,smul,add,zero}`; the whole
℘-recursion block of uniqueness.lean.

## 6. Deferred / follow-ups outside the owned set (verified replacements)

Cox worker (all checked in `.scratch/test_cox.lean` against the new API):
* `Cox/ModularPolynomial/IntegralDescent.lean:25–29` → `laurentqExpansion_pow one_pos j_cuspFunction_meromorphicAt n`;
  `:31–33` → `meromorphicAt_cuspFunction_polynomial_eval j_cuspFunction_meromorphicAt P`;
  `:35–52` → `laurentqExpansion_polynomial_eval one_pos j_cuspFunction_meromorphicAt P`;
  `:54–59` → `by simpa [j_poleOrder] using laurentqExpansion.order_eq_neg_poleOrder j_cuspFunction_meromorphicAt (by simp [j_poleOrder])`;
  `:181–182` `mul (const (-1))` → `meromorphicAt_cuspFunction_neg`.
* `Cox/DiagonalLaurent.lean:152–185` → `laurentqExpansion_pow (by positivity) (j_widthM_cuspMeromorphicAt m) n`,
  `meromorphicAt_cuspFunction_polynomial_eval …`, `laurentqExpansion_polynomial_eval (by positivity) (j_widthM_cuspMeromorphicAt m) P`;
  `:28–30` → `by simpa using meromorphicAt_cuspFunction_nat_mul (PNat.ne_zero m) j_cuspFunction_meromorphicAt ModularFunction.j_periodic`;
  `:32–40` via `order_eq_neg_poleOrder`; `:46–56` optionally via `laurentqExpansion_nat_mul` (note `h = 1` needs `simpa` for `m * 1`).
* `Cox/ModularFunction/CuspData.lean:86–95` (private `cuspFunction_mul_eventuallyEq`) →
  `cuspFunction_comp₂_eventuallyEq _ (· * ·) _ _`; `:115–123` (private `meromorphicAt_polynomial_eval`) →
  `MeromorphicAt.polynomial_eval`; `:125–134` → `cuspFunction_comp_eventuallyEq h (fun x ↦ P.eval x) g`.
* `Cox/ModularFunction.lean:63–73` → `cuspFunction_comp₂_eventuallyEq h (fun x y ↦ x - a * y ^ m) f g`;
  `:132–144` (private `poleOrder_lt_of_neg_lt_meromorphicOrderAt`) → `(poleOrder_lt_iff hm).2`;
  `:89–94` → `meromorphicAt_cuspFunction_sub/const_mul/pow`.
* `Cox/CoxMatrices/LaurentExpansion.lean:124–131` → `eventually_ne_zero_and_norm_lt_one`;
  `:143–184` (`hsuborder`/`hφnc`/`hcompOrder`) → `meromorphicOrderAt_comp_const_mul_pow j_cuspFunction_meromorphicAt hη hr`
  (verified); `:42–45`, `:284–286` → `coeff_neg_poleOrder_add'` / `coeff_of_geq'`; `:190` → `poleRemoved_apply`.
* `Cox/ModularPolynomial/AnalyticSupport.lean:48–49` → `meromorphicAt_cuspFunction_neg`;
  `Cox/ModularFunction/LevelJ.lean:291–294`, `Cox/LevelThree.lean:126–130`,
  `Cox/Kronecker.lean:152` → the new punctured-disc / `coeff_*'` lemmas.
* `ModularFunctions/Congruence.lean:36–48` private `periodic_comp_ofComplex_of_vadd` →
  delete (public root-level copy now in LaurentQExpansion.lean; no name clash meanwhile because
  the private one lives in `namespace ModularFunction`).

jFunction / qExpansion_tactic worker (checked in `.scratch/test_jf.lean`):
* `jfunction.lean:208–211` → `(coeff_toIntegralPowerSeries_cast Delta_isIntegralPowerSeries (n + 1)).symm`;
  `:321–323` (private `qj_coeff_cast_aux`) → `coeff_toIntegralPowerSeries_cast qj_isIntegralPowerSeries n`
  (publicise as `qjCoeffs_cast`); `:226–229` → `coeToComplexPowerSeries.coeff_ringHom_int`;
  `:337–349 qj_periodic` → `periodic_comp_ofComplex_of_vadd qj_vadd_one_aux`;
  `:440–451` → `cuspFunction_qpow_mul_eventuallyEq (h := 1) one_pos j 1`;
  `:478–484` → `poleRemoved_apply`; `:487–502` → `coeff_eq_zero_of_lt'`/`coeff_of_geq'`.
* `Deltaqexpansions.lean:107–111` → `exact_mod_cast (coeff_toIntegralPowerSeries_cast hS n).trans hz`;
  `:246–255` → `toIntegralPowerSeries_eq_of_map_eq _ map_integralE4_pow_three_sub_integralE6_pow_two`;
  `:80` → `hasCoeffsIn_pow ℤ ℂ E4_isIntegralPowerSeries 3`.
* `jLevelN.lean:103–114` → `periodic_comp_ofComplex_of_vadd`; `:144`, `:177–181` → punctured-disc lemmas.
* `qexp_coeffs.lean:46–51` → `coeff_toIntegralPowerSeries_cast`; `:138–141` → `coeff_neg_poleOrder_add'`.
* `link.lean:156–166` (`E4_int_link`, `E6_int_link`) → `rw [E4_int_series_eq]; exact mapAlgHom_ofId_toIntegralPowerSeries E4_isIntegralPowerSeries`;
  `:200–206` → `rw [← coeToComplexPowerSeries.coeff_ringHom_int, map_integralE4_pow_three_sub_integralE6_pow_two]`;
  `:226–230` → `rw [← Delta_qexpansion_coeff_eq, ← coeff_mapAlgHom_ofId_int, Delta_qexpansion_link]`;
  `:234–239` → `coeff_toIntegralPowerSeries_cast Delta_isIntegralPowerSeries n`.
* `XYinTest/Tactic2/LaurentQExpSimpTests.lean:9–40` → `coeff_of_geq'`, `coeff_eq_zero_of_lt'`.

Deferred inside the owned set:
* Renaming `laurentqExpansion.*` into `UpperHalfPlane.laurentqExpansion` / snake-case
  `to_qExpansion` (naming items deferred by the rules).
* `poleOrder` closed form as definition (the task forbids redefining `poleOrder`).
* `poleOrder_add_le / _mul_le / _pow_le / _congr`, `laurentqExpansion_inv/_div`, the
  `LaurentSeries.substMonomial` bridge (L14, design ticket), `HasCoeffsIn → PowerSeries.lifts`
  (G-20, upstream-first), generalised `IsIntegralPowerSeriesmod` (G-21; the existing statement is
  used externally).
* Upstream candidates: `MeromorphicAt.polynomial_eval`, `AnalyticAt.eventuallyEq_of_iteratedDeriv_eq`,
  `iteratedDeriv_sq_mul`, `HahnSeries.ofPowerSeries_expand`, `analyticOrderAt_const_mul_pow`,
  `meromorphicOrderAt_comp_const_mul_pow`, the transport lemmas.

## 7. Perf
No kernel-computation file was edited. `link.lean`, `qexp_coeffs.lean`, `LevelThree.lean` were
rebuilt as downstream modules only (6.9 s, 7.4 s, 12 s in the final build; 5.4–6.2 s,
4.0–6.2 s, 11 s in the intermediate builds); none of the definitions they reduce by
`rfl`/`decide +kernel` (the `Qj.lean` arrays) was touched.
