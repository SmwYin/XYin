# Inventory: XYin/PhD/Modularforms/multipliable_lems.lean  (81 lines)

Multipliability of the eta/Δ-type products ∏(1 − qⁿ) on ℍ and on the unit disc, non-vanishing of ∏(1 + fᵢ), and order lemmas for real infinite products with nonnegative terms. Imported by `Delta.lean`, which uses only `MultipliableEtaProductExpansion` and `Multipliable_pow` (Delta.lean:349). No file header/docstring.

## Declarations

### `lemma Complex.summable_nat_multipliable_one_add`
- **Type**: `(f : ℕ → ℂ) (hf : Summable f) : Multipliable (fun n : ℕ => 1 + f n)`
- **What**: ∑ fₙ convergent ⇒ ∏(1 + fₙ) convergent over ℂ.
- **How**: `exact Complex.multipliable_one_add_of_summable hf`.
- **Hypotheses**: Summable f.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 16–18, proof body ≈ 1 line
- **Notes**: Exact wrapper of mathlib `Complex.multipliable_one_add_of_summable` (`Mathlib/Analysis/SpecialFunctions/Log/Summable.lean:49`). Comment line 15 "this is being PRd" is stale. Dead project-wide.

### `theorem term_ne_zero`
- **Type**: `(z : ℍ) (n : ℕ) : 1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z) ≠ 0`
- **What**: The eta-product factors 1 − q^{n+1} are nonzero on ℍ.
- **How**: `sub_ne_zero` + norm argument from `exp_upperHalfPlane_lt_one_nat`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `exp_upperHalfPlane_lt_one_nat` (exp_lems.lean:18)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 20–22, proof body ≈ 2 lines
- **Notes**: = mathlib `ModularForm.one_sub_eta_q_ne_zero` (`Mathlib/NumberTheory/ModularForms/DedekindEta.lean:53`) via `eta_q_eq_cexp` (:46). Dead project-wide.

### `theorem ball_pow_ne_1`
- **Type**: `(x : ℂ) (hx : x ∈ ball 0 1) (n : ℕ) : 1 + (fun n ↦ -x ^ (n + 1)) n ≠ 0`
- **What**: 1 − x^{n+1} ≠ 0 for |x| < 1 (written as 1 + (−x^{n+1})).
- **How**: `pow_lt_one₀` + `sub_ne_zero` via norms.
- **Hypotheses**: ‖x‖ < 1.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 24–29, proof body ≈ 5 lines
- **Notes**: Un-beta-reduced statement `(fun n ↦ -x^(n+1)) n`. No mathlib analogue found (searched `one_sub_pow_ne_zero`, DedekindEta.lean); mathlib gets it from `norm_lt_one` inline. Dead project-wide.

### `theorem multipliable_lt_one`
- **Type**: `(x : ℂ) (hx : x ∈ ball 0 1) : Multipliable fun i ↦ 1 - x ^ (i+ 1)`
- **What**: ∏(1 − x^{i+1}) converges on the unit disc.
- **How**: `Complex.multipliable_one_add_of_summable` on `−x^{i+1}` summable by `summable_geometric_of_norm_lt_one` composed with `Nat.succ_injective`.
- **Hypotheses**: ‖x‖ < 1.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 31–35, proof body ≈ 3 lines
- **Notes**: = mathlib `ModularForm.multipliable_one_sub_pow` (`DedekindEta.lean:66`) with `mem_ball_zero_iff`. Dead project-wide.

### `lemma MultipliableEtaProductExpansion`
- **Type**: `(z : ℍ) : Multipliable (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * (n + 1) * z)))`
- **What**: The Euler/eta product ∏(1 − q^{n+1}) converges on ℍ.
- **How**: `Complex.multipliable_one_add_of_summable` on `−exp(…)`, summable via `summable_norm_iff.mp (summable_exp_pow z)`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `summable_exp_pow` (Summability/Basic.lean:177)
- **Used by**: `MultipliableEtaProductExpansion_pnat` (46); used in Delta.lean:349
- **Visibility**: public
- **Lines**: 37–40, proof body ≈ 2 lines
- **Notes**: Mathlib: `multipliable_one_sub_pow (norm_exp_two_pi_I_lt_one z)` after `eta_q_eq_pow`/`Complex.exp_nat_mul`, or `multipliableLocallyUniformlyOn_eta` (`DedekindEta.lean:106`). CamelCase name violates convention. Live.

### `lemma MultipliableEtaProductExpansion_pnat`
- **Type**: `(z : ℍ) : Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z)))`
- **What**: ℕ+-indexed version.
- **How**: `multipliable_pnat_iff_multipliable_succ` (`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:535`) + previous.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `MultipliableEtaProductExpansion`
- **Used by**: `MultipliableDeltaProductExpansion_pnat` (61)
- **Visibility**: public
- **Lines**: 42–46, proof body ≈ 3 lines
- **Notes**: Dead outside file.

### `lemma tprod_ne_zero`
- **Type**: `(x : ℍ) (f : ℕ → ℍ → ℂ) (hf : ∀ i x, 1 + f i x ≠ 0) (hu : ∀ x : ℍ, Summable fun n => f n x) : (∏' i : ℕ, (1 + f i) x) ≠ 0`
- **What**: A product ∏(1 + fᵢ(x)) with nonzero factors and summable fᵢ(x) is nonzero.
- **How**: Rewrite as `cexp (∑' log (1 + fᵢ x))` via `Complex.cexp_tsum_eq_tprod` (`Log/Summable.lean:39`) with `Complex.summable_log_one_add_of_summable` (:43); `Complex.exp_ne_zero`.
- **Hypotheses**: factors nonzero, summability (quantified over all x, only x used).
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 48–53, proof body ≈ 4 lines
- **Notes**: Mathlib `tprod_one_add_ne_zero_of_summable` (`Log/Summable.lean:216`) is the general `NormedRing` version but needs `Summable (‖f ·‖)`; the ℂ-specific route here needs only `Summable f`. Odd statement (`(1 + f i) x` pointwise on function-valued f; `hf`/`hu` over-quantified). Dead project-wide.

### `lemma Multipliable_pow`
- **Type**: `{ι : Type*} (f : ι → ℂ) (hf : Multipliable f) (n : ℕ) : Multipliable (fun i => f i ^ n)`
- **What**: Multipliability is preserved by n-th powers.
- **How**: `exact hf.pow n`.
- **Hypotheses**: Multipliable f.
- **Uses from project**: []
- **Used by**: unused in file; used in Delta.lean:349
- **Visibility**: public
- **Lines**: 55–57, proof body ≈ 1 line
- **Notes**: Exact wrapper of mathlib `Multipliable.pow` (`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:334`), which holds for any `CommMonoid` with `ContinuousMul`. Live but trivially replaceable.

### `lemma MultipliableDeltaProductExpansion_pnat`
- **Type**: `(z : ℍ) : Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z))^24)`
- **What**: The Δ-product ∏(1 − qⁿ)^{24} converges.
- **How**: `(MultipliableEtaProductExpansion_pnat z).pow 24`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `MultipliableEtaProductExpansion_pnat`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 59–61, proof body ≈ 1 line
- **Notes**: Dead project-wide.

### `lemma tprod_pow`
- **Type**: `(f : ℕ → ℂ) (hf : Multipliable f) (n : ℕ) : (∏' (i : ℕ), f i) ^ n = ∏' (i : ℕ), (f i) ^ n`
- **What**: n-th power of a tprod is the tprod of n-th powers.
- **How**: `(hf.tprod_pow n).symm`.
- **Hypotheses**: Multipliable f.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 63–65, proof body ≈ 1 line
- **Notes**: Exact wrapper (symm) of mathlib `Multipliable.tprod_pow` (`InfiniteSum/Basic.lean:702`). Dead project-wide.

### `theorem hasProd_le_nonneg`
- **Type**: `{a₁ a₂ : ℝ} {ι} (f g : ι → ℝ) (h : ∀ i, f i ≤ g i) (h0 : ∀ i, 0 ≤ f i) (hf : HasProd f a₁) (hg : HasProd g a₂) : a₁ ≤ a₂`
- **What**: Termwise 0 ≤ f ≤ g implies the products satisfy a₁ ≤ a₂ (real, nonnegative terms).
- **How**: `le_of_tendsto_of_tendsto'` with `Finset.prod_le_prod`.
- **Hypotheses**: f ≤ g termwise, f ≥ 0.
- **Uses from project**: []
- **Used by**: `HasProd.le_one_nonneg` (76)
- **Visibility**: public
- **Lines**: 69–72, proof body ≈ 2 lines
- **Notes**: Mathlib `hasProd_le` (`Mathlib/Topology/Algebra/InfiniteSum/Order.lean:54`) needs `[IsOrderedMonoid α]`, which ℝ under multiplication is not; the nonneg-restricted real version is a genuine (small) gap — no analogue found (searched `nonneg` in Order.lean: only `tsum_nonneg`). Variables declared at line 67.

### `theorem HasProd.le_one_nonneg`
- **Type**: `{a : ℝ} (g : ℕ → ℝ) (h : ∀ i, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i) (ha : HasProd g a) : a ≤ 1`
- **What**: A product of factors in [0,1] is ≤ 1.
- **How**: `hasProd_le_nonneg` against the constant 1 (`hasProd_one`).
- **Hypotheses**: 0 ≤ g ≤ 1.
- **Uses from project**: `hasProd_le_nonneg`
- **Used by**: `one_le_tprod_nonneg` (80)
- **Visibility**: public
- **Lines**: 74–76, proof body ≈ 1 line
- **Notes**: Mathlib `HasProd.le_one` (`Order.lean:165`) again needs `IsOrderedMonoid`. `ι` unnecessarily specialised to ℕ.

### `theorem one_le_tprod_nonneg`
- **Type**: `(g : ℕ → ℝ) (h : ∀ i, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i) : ∏' i, g i ≤ 1`
- **What**: tprod of factors in [0,1] is ≤ 1 (multipliable or not, since a non-multipliable tprod is 1).
- **How**: case split on `Multipliable g`; `tprod_eq_one_of_not_multipliable` (`Mathlib/Topology/Algebra/InfiniteSum/Defs.lean:201`).
- **Hypotheses**: 0 ≤ g ≤ 1.
- **Uses from project**: `HasProd.le_one_nonneg`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 78–81, proof body ≈ 3 lines
- **Notes**: MISNAMED: name says `1 ≤ ∏'`, statement is `∏' ≤ 1` (mathlib name would be `tprod_le_one_of_nonneg`). Dead project-wide.

## File Summary
- Total declarations: 13 (0 defs, 13 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none
- Unused declarations (not used by anything in this file): `Complex.summable_nat_multipliable_one_add`, `term_ne_zero`, `ball_pow_ne_1`, `multipliable_lt_one`, `tprod_ne_zero`, `Multipliable_pow`, `MultipliableDeltaProductExpansion_pnat`, `tprod_pow`, `one_le_tprod_nonneg` (of these only `Multipliable_pow` is used elsewhere: Delta.lean:349; `MultipliableEtaProductExpansion` is used in-file and at Delta.lean:349)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `Complex.summable_nat_multipliable_one_add` (16) = `Complex.multipliable_one_add_of_summable` (`Mathlib/Analysis/SpecialFunctions/Log/Summable.lean:49`).
- `multipliable_lt_one` (31) = `ModularForm.multipliable_one_sub_pow` (`Mathlib/NumberTheory/ModularForms/DedekindEta.lean:66`); `term_ne_zero` (20) = `one_sub_eta_q_ne_zero` (:53) + `eta_q_eq_cexp` (:46); `MultipliableEtaProductExpansion` (37) = `multipliable_one_sub_pow (norm_exp_two_pi_I_lt_one z)` + `eta_q_eq_pow` (:50), see also `multipliableLocallyUniformlyOn_eta` (:106), `eta_tprod_ne_zero` (:111), `eta_ne_zero` (:117).
- `Multipliable_pow` (55) = `Multipliable.pow` (`InfiniteSum/Basic.lean:334`); `tprod_pow` (63) = `Multipliable.tprod_pow` (:702).
- `tprod_ne_zero` (48) ≈ `tprod_one_add_ne_zero_of_summable` (`Log/Summable.lean:216`, needs norm-summability) or the ℂ route `cexp_tsum_eq_tprod` it already uses.
- `hasProd_le_nonneg`/`HasProd.le_one_nonneg`/`one_le_tprod_nonneg` (69–81): no mathlib analogue for ℝ (mathlib's `hasProd_le`, `HasProd.le_one`, `tprod_le_one` at `Order.lean:54/165/177` require `IsOrderedMonoid`). Candidate for a small mathlib PR: `hasProd_le_of_nonneg` in an ordered semiring with `ClosedIicTopology`.
### Missing API / repeated patterns
- The "1 − exp ≠ 0 via norm < 1" fragment (`sub_ne_zero.mpr (ne_of_apply_ne norm (ne_of_gt (by simpa using …)))`) is repeated at 21–22 and 28–29 → one lemma `one_sub_ne_zero_of_norm_lt_one {x : ℂ} (hx : ‖x‖ < 1) : 1 - x ≠ 0`.
- `simpa [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable (…)` at 33 and 39: same 2-line skeleton.
- `variable {a a₁ a₂ : ℝ} {ι}` (67) are declared mid-file after unrelated lemmas.
### Junk candidates
- Dead project-wide: `Complex.summable_nat_multipliable_one_add`, `term_ne_zero`, `ball_pow_ne_1`, `multipliable_lt_one`, `MultipliableEtaProductExpansion_pnat`, `tprod_ne_zero`, `MultipliableDeltaProductExpansion_pnat`, `tprod_pow`, `hasProd_le_nonneg`, `HasProd.le_one_nonneg`, `one_le_tprod_nonneg` — 11 of 13.
- One-line wrappers: lines 16–18, 55–57, 63–65.
- Stale comment 15 "this is being PRd". Missing copyright header/docstring (file starts at `module`). Unused `open ArithmeticFunction` (12).
- Misnamed `one_le_tprod_nonneg` (78); CamelCase `MultipliableEtaProductExpansion(_pnat)`, `MultipliableDeltaProductExpansion_pnat`, `Multipliable_pow`.
### Moral duplicates within this batch
- `multipliable_lt_one` (31) vs `MultipliableEtaProductExpansion` (37): same lemma at `x = exp(2πi z)`.
- `term_ne_zero` (20) vs `ball_pow_ne_1` (24): same nonvanishing at `x = exp(2πi z)`.
- `MultipliableEtaProductExpansion_pnat` (42) vs Basic.lean `nat_pos_tsum2'`-style ℕ/ℕ+ shuttling.
### Generalization notes
- `Multipliable_pow`, `tprod_pow`: stated for ℂ; mathlib versions hold in any topological `CommMonoid` (`Multipliable.pow`) / with `T2Space` (`tprod_pow`).
- `hasProd_le_nonneg`, `HasProd.le_one_nonneg`, `one_le_tprod_nonneg`: only `Finset.prod_le_prod` and `le_of_tendsto_of_tendsto'` are used, so they hold in any `OrderedCommSemiring` with `OrderClosedTopology`; `ι` need not be ℕ (74, 78).
- `multipliable_lt_one`, `ball_pow_ne_1`: only `‖x‖ < 1` is used — could be stated for any complete normed field (as `multipliable_one_add_of_summable` at `Log/Summable.lean:169` is).
