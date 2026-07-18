# Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/LaurentQExpansion/LaurentQExpansion.lean
Project-internal imports: `XYin.PhD.Modularforms.Eisenstein`, `XYin.PhD.IntegralPowerSeries.HasIntegralQExpansion`
(Note: no declaration from either project import is actually referenced in this file's bodies — everything used comes from mathlib's `Mathlib.NumberTheory.ModularForms.QExpansion` (`UpperHalfPlane.cuspFunction`, `UpperHalfPlane.qExpansion`, `qExpansion_coeff`) plus the mathlib analysis/Laurent-series library. Both internal imports appear removable, though `HasIntegralQExpansion` transitively supplies the mathlib QExpansion import.)

File-level: `set_option linter.style.header false` (line 7); `noncomputable section` (line 17); no namespace is opened for declarations, so most lemmas land in the root namespace.

### `[notation] I∞` (local)
- **Type**: `local notation "I∞" => comap Complex.im atTop`
- **What**: Local notation for the filter of neighbourhoods of the cusp i∞ (imaginary part tending to infinity).
- **How**: Notation only.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: unused in file (dead notation)
- **Visibility**: local
- **Lines**: 14
- **Notes**: never referenced in the file.

### `[notation] 𝕢` (local)
- **Type**: `local notation "𝕢" => Periodic.qParam`
- **What**: Local notation for the q-parameter map `q h τ = exp(2πiτ/h)`.
- **How**: Notation only.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `UpperHalfPlane.poleRemoved`, `cuspFunction_qpow_mul_eq`
- **Visibility**: local
- **Lines**: 15
- **Notes**: none

### `[lemma] cuspFunction_nat_mul_eq_cuspFunction_pow`
- **Type**: `{h : ℝ} {m : ℕ} {f : ℍ → ℂ} (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) {q : ℂ} (hq : q ≠ 0) : cuspFunction ((m : ℝ) * h) f q = cuspFunction h f (q ^ m)`
- **What**: For an h-periodic function f, the cusp function relative to the enlarged period m·h at q equals the cusp function relative to h evaluated at q^m — the change-of-period substitution q ↦ q^m for q-expansions.
- **How**: Unfolds both sides via `Periodic.cuspFunction_eq_of_nonzero`; the branch ambiguity of `log(q^m) = m·log q + 2πin` is resolved by `Complex.exp_eq_exp_iff_exists_int`, giving `invQParam h (q^m) = invQParam (m·h) q + n·h`, and periodicity (`Periodic.int_mul`) kills the n·h shift.
- **Hypotheses**: f∘ofComplex is h-periodic; q ≠ 0.
- **Uses from project**: []
- **Used by**: `meromorphicAt_cuspFunction_nat_mul`, `meromorphicAt_cuspFunction_of_nat_mul`, `meromorphicOrderAt_cuspFunction_nat_mul` (also used cross-file by `Algebra.to_qExpansion_nat_mul`)
- **Visibility**: public
- **Lines**: 21–41, proof 19 lines
- **Notes**: none

### `[lemma] cuspFunction_add_eventuallyEq` (private)
- **Type**: `(h : ℝ) (f g : ℍ → ℂ) : cuspFunction h (fun τ ↦ f τ + g τ) =ᶠ[nhdsWithin 0 ({0}ᶜ)] fun q ↦ cuspFunction h f q + cuspFunction h g q`
- **What**: On the punctured neighbourhood of q = 0, the cusp function of a pointwise sum is the sum of the cusp functions.
- **How**: For q ≠ 0 the cusp function is just evaluation at `invQParam h q` (`Periodic.cuspFunction_eq_of_nonzero`), so the identity is definitional there.
- **Hypotheses**: none (statement only holds away from 0).
- **Uses from project**: []
- **Used by**: `meromorphicAt_cuspFunction_add`
- **Visibility**: private
- **Lines**: 43–52, proof 8 lines
- **Notes**: none

### `[lemma] cuspFunction_mul_eventuallyEq` (private)
- **Type**: `(h : ℝ) (f g : ℍ → ℂ) : cuspFunction h (fun τ ↦ f τ * g τ) =ᶠ[nhdsWithin 0 ({0}ᶜ)] fun q ↦ cuspFunction h f q * cuspFunction h g q`
- **What**: On the punctured neighbourhood of 0, the cusp function of a pointwise product is the product of the cusp functions.
- **How**: Same as the additive version: `Periodic.cuspFunction_eq_of_nonzero` reduces to evaluation at `invQParam`, where the identity is `rfl`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `meromorphicAt_cuspFunction_mul`
- **Visibility**: private
- **Lines**: 54–63, proof 8 lines
- **Notes**: none

### `[lemma] cuspFunction_const_eventuallyEq` (private)
- **Type**: `(h : ℝ) (a : ℂ) : cuspFunction h (fun _ : ℍ ↦ a) =ᶠ[nhdsWithin 0 ({0}ᶜ)] fun _ ↦ a`
- **What**: On the punctured neighbourhood of 0, the cusp function of a constant function is that constant.
- **How**: `Periodic.cuspFunction_eq_of_nonzero` reduces to evaluation of the constant.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `meromorphicAt_cuspFunction_const`
- **Visibility**: private
- **Lines**: 65–71, proof 6 lines
- **Notes**: none

### `[lemma] meromorphicAt_cuspFunction_add`
- **Type**: `{h : ℝ} {f g : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) (hg : MeromorphicAt (cuspFunction h g) 0) : MeromorphicAt (cuspFunction h (fun τ ↦ f τ + g τ)) 0`
- **What**: Meromorphy at the cusp is preserved under pointwise addition.
- **How**: `MeromorphicAt.add` combined with the punctured-neighbourhood identification `cuspFunction_add_eventuallyEq` via `MeromorphicAt.congr` (meromorphy at a point only depends on the germ on the punctured neighbourhood).
- **Hypotheses**: both cusp functions meromorphic at 0.
- **Uses from project**: [`cuspFunction_add_eventuallyEq`]
- **Used by**: `meromorphicAt_cuspFunction_finset_sum` (cross-file: `Algebra.laurentqExpansion_add`)
- **Visibility**: public
- **Lines**: 74–78, term proof 1 line
- **Notes**: none

### `[lemma] meromorphicAt_cuspFunction_mul`
- **Type**: `{h : ℝ} {f g : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) (hg : MeromorphicAt (cuspFunction h g) 0) : MeromorphicAt (cuspFunction h (fun τ ↦ f τ * g τ)) 0`
- **What**: Meromorphy at the cusp is preserved under pointwise multiplication.
- **How**: `MeromorphicAt.mul` plus `cuspFunction_mul_eventuallyEq` via `MeromorphicAt.congr`.
- **Hypotheses**: both cusp functions meromorphic at 0.
- **Uses from project**: [`cuspFunction_mul_eventuallyEq`]
- **Used by**: `meromorphicAt_cuspFunction_finset_prod` (cross-file: `Algebra.laurentqExpansion_mul`)
- **Visibility**: public
- **Lines**: 81–85, term proof 1 line
- **Notes**: none

### `[lemma] meromorphicAt_cuspFunction_const`
- **Type**: `(h : ℝ) (a : ℂ) : MeromorphicAt (cuspFunction h (fun _ : ℍ ↦ a)) 0`
- **What**: The cusp function of a constant is meromorphic at 0.
- **How**: `MeromorphicAt.const` transported through `cuspFunction_const_eventuallyEq` by `MeromorphicAt.congr`.
- **Hypotheses**: none.
- **Uses from project**: [`cuspFunction_const_eventuallyEq`]
- **Used by**: `meromorphicAt_cuspFunction_finset_sum`, `meromorphicAt_cuspFunction_finset_prod` (cross-file: `Algebra.laurentqExpansion_zero/_one/_const/_neg`)
- **Visibility**: public
- **Lines**: 88–90, term proof 1 line
- **Notes**: none

### `[lemma] meromorphicAt_cuspFunction_finset_sum`
- **Type**: `{ι : Type*} {h : ℝ} {s : Finset ι} {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) : MeromorphicAt (cuspFunction h (∑ i ∈ s, f i)) 0`
- **What**: A finite pointwise sum of functions with cusp-meromorphic q-expansions is again cusp-meromorphic.
- **How**: `Finset.induction_on`; base case is `meromorphicAt_cuspFunction_const h 0`, inductive step is `meromorphicAt_cuspFunction_add`.
- **Hypotheses**: each summand cusp-meromorphic.
- **Uses from project**: [`meromorphicAt_cuspFunction_const`, `meromorphicAt_cuspFunction_add`]
- **Used by**: unused in file (cross-file: `Algebra.laurentqExpansion_finset_sum`)
- **Visibility**: public
- **Lines**: 93–104, proof 9 lines
- **Notes**: none

### `[lemma] meromorphicAt_cuspFunction_finset_prod`
- **Type**: `{ι : Type*} {h : ℝ} {s : Finset ι} {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) : MeromorphicAt (cuspFunction h (∏ i ∈ s, f i)) 0`
- **What**: A finite pointwise product of cusp-meromorphic functions is cusp-meromorphic.
- **How**: `Finset.induction_on` with base `meromorphicAt_cuspFunction_const h 1` and step `meromorphicAt_cuspFunction_mul`.
- **Hypotheses**: each factor cusp-meromorphic.
- **Uses from project**: [`meromorphicAt_cuspFunction_const`, `meromorphicAt_cuspFunction_mul`]
- **Used by**: unused in file (cross-file: `Algebra.laurentqExpansion_finset_prod`)
- **Visibility**: public
- **Lines**: 107–118, proof 9 lines
- **Notes**: none

### `[lemma] meromorphicAt_cuspFunction_nat_mul`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (hfper : Periodic (f ∘ ofComplex) h) : MeromorphicAt (cuspFunction ((m : ℝ) * h) f) 0`
- **What**: If f is meromorphic at the cusp for period h, it is also meromorphic at the cusp for the enlarged period m·h (the "easy" direction of period change).
- **How**: `cuspFunction (m·h) f` agrees on the punctured disc with `cuspFunction h f ∘ (q ↦ q^m)` by `cuspFunction_nat_mul_eq_cuspFunction_pow`; the composite is meromorphic by `MeromorphicAt.comp_analyticAt` with the analytic map q ↦ q^m.
- **Hypotheses**: m ≠ 0; f cusp-meromorphic for h; f∘ofComplex h-periodic.
- **Uses from project**: [`cuspFunction_nat_mul_eq_cuspFunction_pow`]
- **Used by**: unused in file (cross-file: `Algebra.to_qExpansion_nat_mul`)
- **Visibility**: public
- **Lines**: 122–134, proof 10 lines
- **Notes**: none

### `[lemma] eventually_differentiableAt_pow_mul_of_meromorphicAt_comp_pow_aux` (private)
- **Type**: `{g : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0) (h : MeromorphicAt (g ∘ fun q ↦ q ^ m) 0) (n : ℕ) : ∀ᶠ z in nhdsWithin 0 ({0}ᶜ), DifferentiableAt ℂ (fun z ↦ z ^ n * g z) z`
- **What**: If g∘(q↦q^m) is meromorphic at 0, then z^n·g(z) is differentiable at every point of a punctured neighbourhood of 0 — the key local-differentiability input for descending meromorphy along the power map.
- **How**: `MeromorphicAt.eventually_analyticAt` gives analyticity of the composite on a punctured neighbourhood U; the image of U under q↦q^m is a neighbourhood of 0 by openness of the power map (`Complex.isOpenQuotientMap_pow`), and at each nonzero image point q^m one inverts the composition using `analyticAt_comp_iff_of_deriv_ne_zero` (the derivative m·q^{m-1} ≠ 0), so g itself is analytic there.
- **Hypotheses**: m ≠ 0; g∘(·^m) meromorphic at 0.
- **Uses from project**: []
- **Used by**: `meromorphicAt_of_comp_pow`
- **Visibility**: private
- **Lines**: 136–166, proof 29 lines
- **Notes**: proof close to 30 lines; genuinely nontrivial open-mapping argument.

### `[lemma] meromorphicAt_of_comp_pow`
- **Type**: `{g : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0) (h : MeromorphicAt (g ∘ fun q ↦ q ^ m) 0) : MeromorphicAt g 0`
- **What**: Meromorphy descends along the ramified covering q ↦ q^m: if g(q^m) is meromorphic at 0 then so is g. This is the hard direction of period change for q-expansions.
- **How**: If z^n·(g∘(·^m)) is analytic at 0 (from the definition of meromorphy), then G(z) = z^n·g(z) satisfies: G∘(·^m) analytic at 0 (after rewriting q^{mn} = q^{(m−1)n}·q^n), hence G is continuous at 0 by `(Complex.isOpenQuotientMap_pow m).continuousAt_comp_iff`, and differentiable on a punctured neighbourhood by the auxiliary lemma; the removable-singularity theorem `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` makes G analytic at 0.
- **Hypotheses**: m ≠ 0; g∘(·^m) meromorphic at 0.
- **Uses from project**: [`eventually_differentiableAt_pow_mul_of_meromorphicAt_comp_pow_aux`]
- **Used by**: `meromorphicAt_cuspFunction_of_nat_mul`
- **Visibility**: public
- **Lines**: 169–195, proof 24 lines
- **Notes**: general complex-analysis fact with no modular-forms content; strong mathlib candidate.

### `[lemma] meromorphicAt_cuspFunction_of_nat_mul`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction ((m : ℝ) * h) f) 0) (hfper : Periodic (f ∘ ofComplex) h) : MeromorphicAt (cuspFunction h f) 0`
- **What**: Converse period-change: if an h-periodic f is cusp-meromorphic with respect to the larger period m·h, it is already cusp-meromorphic with respect to h.
- **How**: The m·h-cusp function is the h-cusp function composed with q ↦ q^m (`cuspFunction_nat_mul_eq_cuspFunction_pow`), so `meromorphicAt_of_comp_pow` applies.
- **Hypotheses**: m ≠ 0; cusp-meromorphy for m·h; h-periodicity.
- **Uses from project**: [`meromorphicAt_of_comp_pow`, `cuspFunction_nat_mul_eq_cuspFunction_pow`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 199–207, proof 6 lines
- **Notes**: none

### `[def] UpperHalfPlane.poleOrder`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : ℕ`
- **What**: The pole order of f at the cusp: the natural number −ord₀(cuspFunction h f) when the meromorphic order at q = 0 is negative, and 0 otherwise (including the junk cases order = ⊤ and f not meromorphic).
- **How**: Defined by an if-then-else on `meromorphicOrderAt (cuspFunction h f) 0 < 0`, extracting `Int.natAbs` of `untopD 0` of the order.
- **Hypotheses**: none (total function; meaningful when the cusp function is meromorphic at 0).
- **Uses from project**: []
- **Used by**: `poleOrder_nat_mul`, `UpperHalfPlane.poleRemoved`, `UpperHalfPlane.laurentqExpansion`, `analyticAt_cuspFunction_poleRemoved`, `analyticAt_iff`, `cuspFunction_poleRemoved_eq`, `laurentqExpansion.coeff_eq_HahnSeries_add`, `laurentqExpansion.coeff_eq_zero_of_lt`, `laurentqExpansion.coeff_neg_poleOrder_add`, `laurentqExpansion.coeff_of_geq`, `laurentqExpansion.coeff_of_qExpansion`, `laurentqExpansion.coeff_neg_poleOrder`, `laurentqExpansion.coeff_zero`, `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero`, `to_qExpansion_coeff_zero_ne`, `to_qExpansion_ne_zero`, `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder`, `order`, `laurentqExpansion.ne_zero`, `laurentqExpansion.poleOrder_to_order`, `laurentqExpansion.to_qExpansion_eq_powerSeriesPart`, `laurentqExpansion.eq_qExpansion_iff`, `laurentqExpansion_coeff_eq_circleIntegral`
- **Visibility**: public (namespace `UpperHalfPlane`)
- **Lines**: 209–212
- **Notes**: no docstring.

### `[lemma] meromorphicOrderAt_cuspFunction_nat_mul`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (hfper : Periodic (f ∘ ofComplex) h) : meromorphicOrderAt (cuspFunction ((m : ℝ) * h) f) 0 = meromorphicOrderAt (cuspFunction h f) 0 * m`
- **What**: Enlarging the period by a factor m multiplies the meromorphic order at the cusp by m (in `WithTop ℤ`).
- **How**: Rewrites the m·h-cusp function as `cuspFunction h f ∘ (·^m)` via `cuspFunction_nat_mul_eq_cuspFunction_pow` and `meromorphicOrderAt_congr`, then applies mathlib's composition formula `MeromorphicAt.meromorphicOrderAt_comp`, computing that q ↦ q^m has analytic order m at 0 (`analyticOrderAt_pow`, `analyticOrderAt_id`) and is non-eventually-constant via `eventuallyConst_iff_analyticOrderAt_sub_eq_top`.
- **Hypotheses**: m ≠ 0; cusp-meromorphy for h; h-periodicity.
- **Uses from project**: [`cuspFunction_nat_mul_eq_cuspFunction_pow`]
- **Used by**: `poleOrder_nat_mul`
- **Visibility**: public
- **Lines**: 214–249, proof 32 lines
- **Notes**: proof >30 lines; the block computing `analyticOrderAt (·^m) 0 = m` is duplicated verbatim twice inside the proof (lines 227–239 vs 240–244).

### `[lemma] poleOrder_nat_mul`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (hfper : Periodic (f ∘ ofComplex) h) : poleOrder ((m : ℝ) * h) f = m * poleOrder h f`
- **What**: The pole order at the cusp scales by m when the period is enlarged to m·h.
- **How**: Case split on `meromorphicOrderAt (cuspFunction h f) 0` (⊤ vs an integer k) using `meromorphicOrderAt_cuspFunction_nat_mul`; for k < 0 the natAbs of k·m is computed by `Int.natAbs_mul`, for k ≥ 0 both if-branches collapse to 0.
- **Hypotheses**: m ≠ 0; cusp-meromorphy; h-periodicity.
- **Uses from project**: [`meromorphicOrderAt_cuspFunction_nat_mul`, `UpperHalfPlane.poleOrder`]
- **Used by**: unused in file (cross-file: `Algebra.to_qExpansion_nat_mul`, `Algebra.laurentqExpansion_nat_mul_coeff`, `Algebra.laurentqExpansion_nat_mul_coeff_of_not_dvd`)
- **Visibility**: public
- **Lines**: 251–291, proof 37 lines
- **Notes**: proof >30 lines, mostly `WithTop ℤ` cast bookkeeping.

### `[def] UpperHalfPlane.poleRemoved`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : ℍ → ℂ`
- **What**: The function τ ↦ q(τ)^M · f(τ) where q = exp(2πiτ/h) and M = poleOrder h f: multiplying by q^M cancels the pole at the cusp, yielding a function holomorphic at q = 0.
- **How**: Direct definition `fun τ ↦ (𝕢 h τ) ^ (poleOrder h f) * f τ`.
- **Hypotheses**: none.
- **Uses from project**: [`UpperHalfPlane.poleOrder`]
- **Used by**: `UpperHalfPlane.to_qExpansion`, `analyticAt_cuspFunction_poleRemoved`, `analyticAt_iff`, `cuspFunction_poleRemoved_eq`, `to_qExpansion_coeff_zero_ne`, `laurentqExpansion.eq_qExpansion_iff`, `cuspFunction_to_analyticAt_meromorphicAt`, `cuspFunction_to_analyticAt_analyticAt`, `exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt`, `laurentqExpansion_coeff_eq_circleIntegral`
- **Visibility**: public (namespace `UpperHalfPlane`)
- **Lines**: 293–294
- **Notes**: no docstring.

### `[def] UpperHalfPlane.to_qExpansion`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : PowerSeries ℂ`
- **What**: The Taylor power series at q = 0 of the pole-removed function, i.e. the q-expansion of q^M·f; this is the "regular part" of the Laurent q-expansion shifted so that its constant term is the leading Laurent coefficient.
- **How**: Definitional: `qExpansion h (poleRemoved h f)` (mathlib's `UpperHalfPlane.qExpansion`).
- **Hypotheses**: none.
- **Uses from project**: [`UpperHalfPlane.poleRemoved`]
- **Used by**: `UpperHalfPlane.laurentqExpansion`, `laurentqExpansion.coeff_eq_HahnSeries_add`, `laurentqExpansion.coeff_eq_zero_of_lt`, `laurentqExpansion.coeff_neg_poleOrder_add`, `laurentqExpansion.coeff_of_geq`, `laurentqExpansion.coeff_of_qExpansion`, `laurentqExpansion.coeff_neg_poleOrder`, `laurentqExpansion.coeff_zero`, `to_qExpansion_coeff_zero_ne`, `to_qExpansion_ne_zero`, `laurentqExpansion.ne_zero`, `laurentqExpansion.to_qExpansion_eq_powerSeriesPart`, `laurentqExpansion.eq_qExpansion_iff`, `laurentqExpansion_coeff_eq_circleIntegral`
- **Visibility**: public (namespace `UpperHalfPlane`)
- **Lines**: 296–297
- **Notes**: no docstring; snake_case name `to_qExpansion` is nonstandard for a def.

### `[def] UpperHalfPlane.laurentqExpansion`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : LaurentSeries ℂ`
- **What**: The Laurent q-expansion of f at the cusp: q^{−M} times the power series of the pole-removed function, realized in `LaurentSeries ℂ = HahnSeries ℤ ℂ` as `single(−M) 1 * ofPowerSeries(to_qExpansion h f)`.
- **How**: Direct definition combining `HahnSeries.single` and `HahnSeries.ofPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.to_qExpansion`]
- **Used by**: `laurentqExpansion.coeff_eq_HahnSeries_add`, `laurentqExpansion.coeff_eq_zero_of_lt`, `laurentqExpansion.coeff_neg_poleOrder_add`, `laurentqExpansion.coeff_of_geq`, `laurentqExpansion.coeff_of_qExpansion`, `laurentqExpansion.coeff_neg_poleOrder`, `laurentqExpansion.coeff_zero`, `laurentqExpansion.ne_zero`, `laurentqExpansion.poleOrder_to_order`, `laurentqExpansion.to_qExpansion_eq_powerSeriesPart`, `laurentqExpansion.eq_qExpansion_iff`, `laurentqExpansion_coeff_eq_circleIntegral`
- **Visibility**: public (namespace `UpperHalfPlane`)
- **Lines**: 299–301
- **Notes**: no docstring; this is the file's central definition.

### `[lemma] cuspFunction_qpow_mul_eq`
- **Type**: `{h : ℝ} (hh : 0 < h) (f : ℍ → ℂ) {n : ℕ} {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) : cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ) q = q ^ n * cuspFunction h f q`
- **What**: For 0 < ‖q‖ < 1, the cusp function of q(τ)^n·f(τ) at q equals q^n times the cusp function of f — multiplication by the q-parameter becomes multiplication by q.
- **How**: For such q, `Periodic.im_invQParam_pos_of_norm_lt_one` puts invQParam h q in the upper half-plane, so `ofComplex` is a genuine section and `Periodic.qParam_right_inv` gives 𝕢 h (ofComplex (invQParam h q)) = q; both sides are then evaluated by `Periodic.cuspFunction_eq_of_nonzero`.
- **Hypotheses**: h > 0; q ≠ 0; ‖q‖ < 1.
- **Uses from project**: []
- **Used by**: `analyticAt_cuspFunction_poleRemoved`, `cuspFunction_poleRemoved_eq` (cross-file: `Algebra.cuspFunction_qpow_mul_eventuallyEq`)
- **Visibility**: public
- **Lines**: 303–320, proof 16 lines
- **Notes**: none

### `[lemma] analyticAt_cuspFunction_poleRemoved`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) : AnalyticAt ℂ (cuspFunction h (poleRemoved h f)) 0`
- **What**: The central regularity theorem: multiplying by q^{poleOrder} removes the pole, i.e. the cusp function of the pole-removed function is analytic at q = 0. This justifies defining the Laurent expansion via the Taylor series of `poleRemoved`.
- **How**: For h > 0, on a punctured disc the pole-removed cusp function equals q^M·cuspFunction h f (`cuspFunction_qpow_mul_eq`). Case split on `meromorphicOrderAt`: if ⊤, f vanishes near 0 (`meromorphicOrderAt_eq_top_iff`) and the function is eventually 0; if a finite order k, `meromorphicOrderAt_eq_int_iff` produces an analytic g with cuspFunction = q^k·g, and for k < 0 one has M = |k| so q^M·q^k·g = g (zpow arithmetic via `zpow_add₀`), while for k ≥ 0, M = 0 and q^k·g is analytic. In every branch the value at 0 is fixed by `Periodic.cuspFunction_zero_eq_limUnder_nhds_ne` and the extension is glued with `eventuallyEq_nhds_of_eventuallyEq_nhdsNE`. For h ≤ 0, invQParam always has nonpositive imaginary part, so via `UpperHalfPlane.ofComplex_apply_of_im_nonpos` the cusp function is constant on the punctured disc, hence analytic.
- **Hypotheses**: cuspFunction h f meromorphic at 0 (h ≤ 0 branch needs nothing).
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.poleRemoved`, `cuspFunction_qpow_mul_eq`]
- **Used by**: `analyticAt_iff`, `to_qExpansion_coeff_zero_ne`, `cuspFunction_to_analyticAt_meromorphicAt`, `cuspFunction_to_analyticAt_analyticAt` (cross-file: `Algebra.laurentqExpansion_eq_shiftedLaurent`, `Algebra.analyticAt_cuspFunction_qpow_of_poleOrder_le`, `Algebra.to_qExpansion_nat_mul`)
- **Visibility**: public
- **Lines**: 322–455, proof 132 lines
- **Notes**: proof >30 lines (132) — the longest in the file; the "F 0 = limUnder" calc block is repeated four times and is a clear candidate for a helper lemma; junk-value branch h ≤ 0 handled in full.

### `[lemma] analyticAt_iff`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) : AnalyticAt ℂ (cuspFunction h f) 0 ↔ poleOrder h f = 0`
- **What**: A cusp-meromorphic function is analytic at the cusp iff its pole order vanishes.
- **How**: Forward: analyticity forces `meromorphicOrderAt ≥ 0` (`AnalyticAt.meromorphicOrderAt_nonneg`), so the if-condition in `poleOrder` fails. Backward: pole order 0 makes `poleRemoved h f = f` definitionally, and `analyticAt_cuspFunction_poleRemoved` applies.
- **Hypotheses**: cusp-meromorphy at 0.
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.poleRemoved`, `analyticAt_cuspFunction_poleRemoved`]
- **Used by**: `cuspFunction_poleRemoved_eq` (cross-file: `Algebra.laurentqExpansion_zero/_one/_const`)
- **Visibility**: public
- **Lines**: 457–470, proof 12 lines
- **Notes**: bare root-namespace name `analyticAt_iff` is dangerously generic.

### `[lemma] analyticAt_cuspFunction_of_not_pos`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hh : h ≤ 0) : AnalyticAt ℂ (cuspFunction h f) 0`
- **What**: For a nonpositive period the cusp function is analytic at 0 (junk-value case: everything degenerates to a constant).
- **How**: For h ≤ 0 and ‖q‖ < 1, `Periodic.im_invQParam` shows Im(invQParam h q) ≤ 0, so `UpperHalfPlane.ofComplex_apply_of_im_nonpos` sends every point to the same default τ₀; the cusp function is eventually constant, its value at 0 computed by `Periodic.cuspFunction_zero_eq_limUnder_nhds_ne`, and `eventuallyEq_nhds_of_eventuallyEq_nhdsNE` upgrades to full-neighbourhood equality with a constant.
- **Hypotheses**: h ≤ 0.
- **Uses from project**: []
- **Used by**: `cuspFunction_poleRemoved_eq`
- **Visibility**: public
- **Lines**: 472–509, proof 36 lines
- **Notes**: proof >30 lines; duplicates verbatim the h ≤ 0 branch of `analyticAt_cuspFunction_poleRemoved` (that branch could be replaced by an application of this lemma).

### `[lemma] cuspFunction_poleRemoved_eq`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) : cuspFunction h (poleRemoved h f) q = q ^ poleOrder h f * cuspFunction h f q`
- **What**: On the punctured unit disc, the cusp function of the pole-removed function is q^M times the original cusp function.
- **How**: For h > 0 this is `cuspFunction_qpow_mul_eq`; for h ≤ 0 both sides are handled by showing poleOrder = 0 via `analyticAt_iff` applied to `analyticAt_cuspFunction_of_not_pos`, making `poleRemoved h f = f`.
- **Hypotheses**: cusp-meromorphy; q ≠ 0; ‖q‖ < 1.
- **Uses from project**: [`cuspFunction_qpow_mul_eq`, `analyticAt_iff`, `analyticAt_cuspFunction_of_not_pos`, `UpperHalfPlane.poleRemoved`, `UpperHalfPlane.poleOrder`]
- **Used by**: `to_qExpansion_coeff_zero_ne`, `laurentqExpansion_coeff_eq_circleIntegral` (cross-file: `Algebra.to_qExpansion_nat_mul`)
- **Visibility**: public
- **Lines**: 511–524, proof 12 lines
- **Notes**: none

### `[lemma] laurentqExpansion.coeff_eq_HahnSeries_add`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) {n : ℤ} : (laurentqExpansion h f).coeff n = ((HahnSeries.ofPowerSeries ℤ ℂ) (to_qExpansion h f)).coeff (n + poleOrder h f)`
- **What**: The n-th Laurent coefficient equals the (n+M)-th coefficient of the underlying power series viewed in Hahn series — the basic index-shift identity.
- **How**: Unfolds `laurentqExpansion` and applies `HahnSeries.coeff_single_mul` for multiplication by `single (−M) 1`.
- **Hypotheses**: none.
- **Uses from project**: [`UpperHalfPlane.laurentqExpansion`, `UpperHalfPlane.to_qExpansion`, `UpperHalfPlane.poleOrder`]
- **Used by**: `laurentqExpansion.coeff_eq_zero_of_lt`, `laurentqExpansion.coeff_neg_poleOrder_add`
- **Visibility**: public
- **Lines**: 526–534, proof 7 lines
- **Notes**: none

### `[lemma] laurentqExpansion.coeff_eq_zero_of_lt`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} {n : ℤ} (hn : n < -(poleOrder h f : ℤ)) : (laurentqExpansion h f).coeff n = 0`
- **What**: Laurent coefficients below the principal-part cutoff −M vanish.
- **How**: By the index shift `coeff_eq_HahnSeries_add`, the coefficient sits at negative index n+M of a power series coerced into Laurent series, which vanishes by `PowerSeries.coeff_coe`.
- **Hypotheses**: n < −M.
- **Uses from project**: [`laurentqExpansion.coeff_eq_HahnSeries_add`, `UpperHalfPlane.poleOrder`, `UpperHalfPlane.to_qExpansion`]
- **Used by**: `laurentqExpansion.coeff_of_qExpansion`, `laurentqExpansion.poleOrder_to_order`, `laurentqExpansion_coeff_eq_circleIntegral` (cross-file: `Algebra.laurentqExpansion_nat_mul_coeff`, `Algebra.laurentqExpansion_nat_mul_coeff_of_not_dvd`)
- **Visibility**: public
- **Lines**: 536–542, proof 6 lines
- **Notes**: none

### `[lemma] laurentqExpansion.coeff_neg_poleOrder_add`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) (n : ℕ) : (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ) + n) = (to_qExpansion h f).coeff n`
- **What**: The Laurent coefficient at −M + n is the n-th power-series coefficient of the pole-removed q-expansion.
- **How**: Index shift `coeff_eq_HahnSeries_add` followed by `PowerSeries.coeff_coe` at the nonnegative index n.
- **Hypotheses**: none.
- **Uses from project**: [`laurentqExpansion.coeff_eq_HahnSeries_add`, `UpperHalfPlane.to_qExpansion`, `UpperHalfPlane.poleOrder`]
- **Used by**: `laurentqExpansion.coeff_of_geq`, `laurentqExpansion.coeff_neg_poleOrder`, `laurentqExpansion.to_qExpansion_eq_powerSeriesPart`
- **Visibility**: public
- **Lines**: 544–555, proof 10 lines
- **Notes**: none

### `[lemma] laurentqExpansion.coeff_of_geq`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} {n : ℤ} (hn : n ≥ -(poleOrder h f : ℤ)) : (laurentqExpansion h f).coeff n = (to_qExpansion h f).coeff (Int.toNat (n + poleOrder h f))`
- **What**: For n ≥ −M the Laurent coefficient is the power-series coefficient at the shifted index (n+M).toNat.
- **How**: Rewrites n as −M + (n+M).toNat using `Int.toNat_of_nonneg` and applies `coeff_neg_poleOrder_add`.
- **Hypotheses**: n ≥ −M.
- **Uses from project**: [`laurentqExpansion.coeff_neg_poleOrder_add`, `UpperHalfPlane.poleOrder`, `UpperHalfPlane.to_qExpansion`]
- **Used by**: `laurentqExpansion.coeff_of_qExpansion`, `laurentqExpansion.coeff_zero`, `laurentqExpansion_coeff_eq_circleIntegral` (cross-file: `Algebra.laurentqExpansion_nat_mul_coeff`, `Algebra.laurentqExpansion_nat_mul_coeff_of_not_dvd`)
- **Visibility**: public
- **Lines**: 557–573, proof 15 lines
- **Notes**: `≥` in statement (mathlib style prefers `≤`).

### `[lemma] laurentqExpansion.coeff_of_qExpansion`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) (n : ℤ) : (laurentqExpansion h f).coeff n = if n < -(poleOrder h f : ℤ) then 0 else (to_qExpansion h f).coeff (Int.toNat (n + poleOrder h f))`
- **What**: Complete closed-form description of every Laurent coefficient as an if-then-else.
- **How**: Case split combining `coeff_eq_zero_of_lt` and `coeff_of_geq`.
- **Hypotheses**: none.
- **Uses from project**: [`laurentqExpansion.coeff_eq_zero_of_lt`, `laurentqExpansion.coeff_of_geq`, `UpperHalfPlane.poleOrder`, `UpperHalfPlane.to_qExpansion`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 575–581, proof 5 lines
- **Notes**: none

### `[lemma] laurentqExpansion.coeff_neg_poleOrder`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ)) = (to_qExpansion h f).coeff 0`
- **What**: The leading (most negative possibly-nonzero) Laurent coefficient is the constant term of the pole-removed power series.
- **How**: Specialization of `coeff_neg_poleOrder_add` at n = 0.
- **Hypotheses**: none.
- **Uses from project**: [`laurentqExpansion.coeff_neg_poleOrder_add`]
- **Used by**: `laurentqExpansion.poleOrder_to_order`, `laurentqExpansion.eq_qExpansion_iff`
- **Visibility**: public
- **Lines**: 583–585, proof 2 lines
- **Notes**: none

### `[lemma] laurentqExpansion.coeff_zero`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : (laurentqExpansion h f).coeff 0 = (to_qExpansion h f).coeff (poleOrder h f)`
- **What**: The constant Laurent coefficient is the M-th coefficient of the pole-removed power series.
- **How**: Specialization of `coeff_of_geq` at n = 0 (0 ≥ −M).
- **Hypotheses**: none.
- **Uses from project**: [`laurentqExpansion.coeff_of_geq`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 587–591, proof 4 lines
- **Notes**: none

### `[lemma] meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (h0 : poleOrder h f ≠ 0) : meromorphicOrderAt (cuspFunction h f) 0 = -(poleOrder h f : ℤ)`
- **What**: When the pole order is nonzero, the meromorphic order at the cusp is exactly −M — i.e. `poleOrder` faithfully records genuine poles.
- **How**: Since M ≠ 0, the if-condition in the definition of `poleOrder` must have held, so the order is a negative integer k, and `Int.ofNat_natAbs_of_nonpos` identifies (|k| : ℤ) = −k.
- **Hypotheses**: poleOrder h f ≠ 0.
- **Uses from project**: [`UpperHalfPlane.poleOrder`]
- **Used by**: `to_qExpansion_coeff_zero_ne`, `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder`
- **Visibility**: public
- **Lines**: 593–610, proof 16 lines
- **Notes**: none

### `[lemma] to_qExpansion_coeff_zero_ne`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (h0 : poleOrder h f ≠ 0) : (to_qExpansion h f).coeff 0 ≠ 0`
- **What**: When f has a genuine pole at the cusp, the leading Laurent coefficient (constant term of the pole-removed series) is nonzero.
- **How**: The pole-removed cusp function G equals q^M·cuspFunction h f on the punctured disc (`cuspFunction_poleRemoved_eq`), so by `meromorphicOrderAt_mul` its meromorphic order is M + (−M) = 0 (using `meromorphicOrderAt_pow` and `meromorphicOrderAt_id` for the factor q^M and `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero` for f); as G is analytic (`analyticAt_cuspFunction_poleRemoved`), `AnalyticAt.meromorphicOrderAt_eq` converts this to analytic order 0, and `AnalyticAt.analyticOrderAt_eq_zero` gives G(0) ≠ 0, which is the constant coefficient by `qExpansion_coeff`.
- **Hypotheses**: cusp-meromorphy; poleOrder ≠ 0.
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.poleRemoved`, `UpperHalfPlane.to_qExpansion`, `analyticAt_cuspFunction_poleRemoved`, `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero`, `cuspFunction_poleRemoved_eq`]
- **Used by**: `to_qExpansion_ne_zero`, `laurentqExpansion.poleOrder_to_order`, `laurentqExpansion.eq_qExpansion_iff`
- **Visibility**: public
- **Lines**: 612–653, proof 40 lines
- **Notes**: proof >30 lines.

### `[lemma] to_qExpansion_ne_zero`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (h0 : poleOrder h f ≠ 0) : to_qExpansion h f ≠ 0`
- **What**: The pole-removed power series is nonzero when f has a genuine pole.
- **How**: Immediate from the nonvanishing constant coefficient `to_qExpansion_coeff_zero_ne`.
- **Hypotheses**: cusp-meromorphy; poleOrder ≠ 0.
- **Uses from project**: [`to_qExpansion_coeff_zero_ne`, `UpperHalfPlane.to_qExpansion`, `UpperHalfPlane.poleOrder`]
- **Used by**: `laurentqExpansion.ne_zero`
- **Visibility**: public
- **Lines**: 655–660, proof 4 lines
- **Notes**: none

### `[lemma] meromorphicOrderAt_cuspFunction_eq_neg_poleOrder`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (h0 : poleOrder h f ≠ 0) : meromorphicOrderAt (cuspFunction h f) 0 = -(poleOrder h f : ℤ)`
- **What**: Restatement of `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero` with the identical statement.
- **How**: Direct term-mode application of that lemma.
- **Hypotheses**: poleOrder ≠ 0.
- **Uses from project**: [`meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 662–664, term proof 1 line
- **Notes**: exact duplicate of `..._of_ne_zero` (same statement, same hypotheses) — one of the two should be deleted.

### `[theorem] order`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : poleOrder h f = Int.toNat (-(meromorphicOrderAt (cuspFunction h f) 0).untopD 0)`
- **What**: Closed formula for the pole order without the if-then-else: it is the positive part of minus the meromorphic order (with junk value 0 for order ⊤).
- **How**: Case analysis on the `WithTop ℤ` order; for k < 0 the natAbs/toNat identification is `Int.ofNat_natAbs_of_nonpos`, for k ≥ 0 both sides are 0 via `Int.toNat_of_nonpos`.
- **Hypotheses**: none.
- **Uses from project**: [`UpperHalfPlane.poleOrder`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 666–687, proof 20 lines
- **Notes**: root-namespace name `order` is far too generic — will clash badly; should be e.g. `UpperHalfPlane.poleOrder_eq_toNat_neg_meromorphicOrderAt`.

### `[lemma] laurentqExpansion.ne_zero`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (h0 : poleOrder h f ≠ 0) : laurentqExpansion h f ≠ 0`
- **What**: The Laurent q-expansion of a function with a genuine pole is a nonzero Laurent series.
- **How**: A product of the nonzero single term (`HahnSeries.single_ne_zero`) and the image of a nonzero power series; injectivity `HahnSeries.ofPowerSeries_injective` reduces to `to_qExpansion_ne_zero`. (Uses that `LaurentSeries ℂ` has no zero divisors.)
- **Hypotheses**: cusp-meromorphy; poleOrder ≠ 0.
- **Uses from project**: [`UpperHalfPlane.laurentqExpansion`, `to_qExpansion_ne_zero`]
- **Used by**: `laurentqExpansion.poleOrder_to_order`
- **Visibility**: public
- **Lines**: 689–700, proof 10 lines
- **Notes**: none

### `[lemma] laurentqExpansion.poleOrder_to_order`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (h0 : poleOrder h f ≠ 0) : poleOrder h f = -(laurentqExpansion h f).order`
- **What**: The analytic pole order coincides with minus the Hahn-series order (valuation) of the Laurent q-expansion — the analytic and algebraic notions of leading exponent agree.
- **How**: The coefficient at −M is nonzero (`coeff_neg_poleOrder` + `to_qExpansion_coeff_zero_ne`), giving order ≤ −M by `HahnSeries.order_le_of_coeff_ne_zero`; conversely coefficients below −M vanish (`coeff_eq_zero_of_lt`), so the order coefficient would be zero if order < −M, contradicting `HahnSeries.coeff_order_eq_zero` for the nonzero series (`laurentqExpansion.ne_zero`).
- **Hypotheses**: cusp-meromorphy; poleOrder ≠ 0.
- **Uses from project**: [`laurentqExpansion.coeff_neg_poleOrder`, `to_qExpansion_coeff_zero_ne`, `laurentqExpansion.coeff_eq_zero_of_lt`, `laurentqExpansion.ne_zero`, `UpperHalfPlane.poleOrder`, `UpperHalfPlane.laurentqExpansion`]
- **Used by**: `laurentqExpansion.to_qExpansion_eq_powerSeriesPart`
- **Visibility**: public
- **Lines**: 702–719, proof 16 lines
- **Notes**: none

### `[lemma] laurentqExpansion.to_qExpansion_eq_powerSeriesPart`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (h0 : poleOrder h f ≠ 0) : to_qExpansion h f = (laurentqExpansion h f).powerSeriesPart`
- **What**: The pole-removed q-expansion is exactly the `powerSeriesPart` of the Laurent series (coefficients re-indexed from the order).
- **How**: Coefficientwise via `LaurentSeries.powerSeriesPart_coeff`, rewriting the order as −M by `poleOrder_to_order` and applying `coeff_neg_poleOrder_add`.
- **Hypotheses**: cusp-meromorphy; poleOrder ≠ 0.
- **Uses from project**: [`laurentqExpansion.poleOrder_to_order`, `laurentqExpansion.coeff_neg_poleOrder_add`, `UpperHalfPlane.to_qExpansion`, `UpperHalfPlane.laurentqExpansion`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 721–731, proof 9 lines
- **Notes**: none

### `[lemma] laurentqExpansion.eq_qExpansion_iff`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) : laurentqExpansion h f = qExpansion h f ↔ poleOrder h f = 0`
- **What**: The Laurent q-expansion coincides with the ordinary (power-series) q-expansion, coerced into Laurent series, precisely when there is no pole at the cusp.
- **How**: Forward: if M ≠ 0, the Laurent coefficient at −M < 0 is nonzero (`coeff_neg_poleOrder`, `to_qExpansion_coeff_zero_ne`) while a coerced power series has zero coefficient there (`PowerSeries.coeff_coe`) — contradiction. Backward: M = 0 makes `poleRemoved h f = f`, so `to_qExpansion = qExpansion` and the `single 0 1` factor is 1.
- **Hypotheses**: cusp-meromorphy.
- **Uses from project**: [`laurentqExpansion.coeff_neg_poleOrder`, `to_qExpansion_coeff_zero_ne`, `UpperHalfPlane.laurentqExpansion`, `UpperHalfPlane.to_qExpansion`, `UpperHalfPlane.poleRemoved`, `UpperHalfPlane.poleOrder`]
- **Used by**: unused in file (cross-file: `Algebra.laurentqExpansion_zero/_one/_const`)
- **Visibility**: public
- **Lines**: 734–767, proof 32 lines
- **Notes**: proof >30 lines.

### `[lemma] qExpansion_coeff_eq_circleIntegral_of_differentiableOn`
- **Type**: `{g : ℍ → ℂ} {R : ℝ} (hR : 0 < R) (hDiff : DifferentiableOn ℂ (cuspFunction h g) (closedBall 0 R)) (n : ℕ) : (qExpansion h g).coeff n = (2πi)⁻¹ * ∮ z in C(0,R), cuspFunction h g z / z^(n+1)`
- **What**: Cauchy integral formula for q-expansion coefficients: the n-th coefficient is the circle integral of cuspFunction/z^{n+1} over any circle of radius R on which the cusp function is holomorphic.
- **How**: Mathlib's `DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul` expresses the integral as (2πi/n!)·(iterated derivative at 0), matched against the definition `qExpansion_coeff = (n!)⁻¹·iteratedDeriv n (cuspFunction) 0` after clearing 2πi (`two_pi_I_ne_zero`).
- **Hypotheses**: R > 0; cusp function differentiable on the closed ball of radius R. Uses the section variable {h : ℝ}.
- **Uses from project**: []
- **Used by**: `laurentqExpansion_coeff_eq_circleIntegral`
- **Visibility**: public
- **Lines**: 770–786, proof 15 lines
- **Notes**: none

### `[lemma] cuspFunction_to_analyticAt_meromorphicAt`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) : MeromorphicAt (cuspFunction h (poleRemoved h f)) 0`
- **What**: The pole-removed cusp function is (trivially) meromorphic at 0, being analytic there.
- **How**: `AnalyticAt.meromorphicAt` applied to `analyticAt_cuspFunction_poleRemoved`.
- **Hypotheses**: cusp-meromorphy.
- **Uses from project**: [`analyticAt_cuspFunction_poleRemoved`, `UpperHalfPlane.poleRemoved`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 788–791, proof 1 line
- **Notes**: name `cuspFunction_to_analyticAt_meromorphicAt` is uninformative/garbled.

### `[lemma] cuspFunction_to_analyticAt_analyticAt`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) : AnalyticAt ℂ (cuspFunction h (poleRemoved h f)) 0`
- **What**: Verbatim restatement of `analyticAt_cuspFunction_poleRemoved`.
- **How**: Direct application of that lemma.
- **Hypotheses**: cusp-meromorphy.
- **Uses from project**: [`analyticAt_cuspFunction_poleRemoved`, `UpperHalfPlane.poleRemoved`]
- **Used by**: `exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt`
- **Visibility**: public
- **Lines**: 793–796, proof 1 line
- **Notes**: exact duplicate of `analyticAt_cuspFunction_poleRemoved`; should be removed.

### `[lemma] exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) : ∃ R, 0 < R ∧ R < 1 ∧ DifferentiableOn ℂ (cuspFunction h (poleRemoved h f)) (closedBall 0 R)`
- **What**: There is a radius 0 < R < 1 on whose closed disc the pole-removed cusp function is holomorphic — supplying the contour for the Cauchy-formula coefficient computation.
- **How**: `AnalyticAt.exists_ball_analyticOnNhd` gives an open ball of analyticity of radius R₀; take R = min(R₀/2, 1/2) and restrict via `Metric.closedBall_subset_ball`.
- **Hypotheses**: cusp-meromorphy.
- **Uses from project**: [`cuspFunction_to_analyticAt_analyticAt`, `UpperHalfPlane.poleRemoved`]
- **Used by**: `laurentqExpansion_coeff_eq_circleIntegral`
- **Visibility**: public
- **Lines**: 799–817, proof 17 lines
- **Notes**: preceded by a `-- double check` TODO comment (line 798). NOTE: the statement only asserts differentiability on the punctured data near 0; it is correct but the ball is only guaranteed around 0, not the whole disc where cuspFunction h f may have other poles — fine since `poleRemoved`'s cusp function is analytic at 0 and the ball comes from that analyticity.

### `[lemma] laurentqExpansion_coeff_eq_circleIntegral`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) : ∃ R, 0 < R ∧ R < 1 ∧ ∀ n : ℤ, (laurentqExpansion h f).coeff n = (2πi)⁻¹ * ∮ z in C(0,R), cuspFunction h f z / z^(n+1)`
- **What**: Cauchy integral formula for all Laurent q-expansion coefficients: on a suitable circle, every integer-indexed coefficient of the Laurent q-expansion is the standard contour integral of cuspFunction·z^{−n−1}. This certifies that `laurentqExpansion` really is the analytic Laurent expansion of the cusp function.
- **How**: Choose R from `exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt`. For n < −M the coefficient is 0 (`coeff_eq_zero_of_lt`) and the integrand equals z^k·(pole-removed cusp function) with k = −(n+M+1) ≥ 0 on the sphere (via `cuspFunction_poleRemoved_eq` and zpow bookkeeping with `zpow_add₀`), which is holomorphic on the disc, so the integral vanishes by `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`. For n ≥ −M the coefficient equals the (n+M)-th coefficient of `to_qExpansion` (`coeff_of_geq`), which is the circle integral of the pole-removed cusp function over z^{n+M+1} by `qExpansion_coeff_eq_circleIntegral_of_differentiableOn`; the integrands agree on the sphere by `cuspFunction_poleRemoved_eq` and `zpow_sub₀`, and `circleIntegral.integral_congr` transfers the integral.
- **Hypotheses**: cusp-meromorphy at 0.
- **Uses from project**: [`exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt`, `laurentqExpansion.coeff_eq_zero_of_lt`, `laurentqExpansion.coeff_of_geq`, `cuspFunction_poleRemoved_eq`, `qExpansion_coeff_eq_circleIntegral_of_differentiableOn`, `UpperHalfPlane.laurentqExpansion`, `UpperHalfPlane.to_qExpansion`, `UpperHalfPlane.poleRemoved`, `UpperHalfPlane.poleOrder`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 819–971, proof 151 lines
- **Notes**: proof >30 lines (151) — second-longest in the file; the two sphere-EqOn calc blocks are heavy zpow manipulation and would benefit from a `z^a * z^b = z^(a+b)` helper; the "z ≠ 0 on the sphere" and "‖z‖ < 1 on the sphere" sub-proofs are duplicated.

### File Summary
- Total declarations: 45 (4 defs, 39 lemmas/theorems, 0 instances, 2 local notations)
- Key API (used by 3+ others): `UpperHalfPlane.poleOrder` (24 in-file users), `UpperHalfPlane.poleRemoved` (10), `UpperHalfPlane.to_qExpansion` (14), `UpperHalfPlane.laurentqExpansion` (12), `analyticAt_cuspFunction_poleRemoved` (4 in-file + 3 cross-file), `cuspFunction_nat_mul_eq_cuspFunction_pow` (3 + 1 cross-file), `cuspFunction_poleRemoved_eq` (2 + 1 cross-file), `to_qExpansion_coeff_zero_ne` (3), `laurentqExpansion.coeff_eq_zero_of_lt` (3 + 2 cross-file), `laurentqExpansion.coeff_of_geq` (3 + 2 cross-file), `laurentqExpansion.coeff_neg_poleOrder_add` (3)
- Unused declarations (not used by anything in this file): `I∞` notation, `meromorphicAt_cuspFunction_finset_sum`, `meromorphicAt_cuspFunction_finset_prod`, `meromorphicAt_cuspFunction_nat_mul`, `meromorphicAt_cuspFunction_of_nat_mul`, `poleOrder_nat_mul`, `laurentqExpansion.coeff_of_qExpansion`, `laurentqExpansion.coeff_zero`, `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder`, `order`, `laurentqExpansion.to_qExpansion_eq_powerSeriesPart`, `laurentqExpansion.eq_qExpansion_iff`, `cuspFunction_to_analyticAt_meromorphicAt`, `laurentqExpansion_coeff_eq_circleIntegral` (several of these are consumed by `Algebra.lean` or downstream files)
- Declarations with sorry: []
- Declarations with set_option: [] (file-level `set_option linter.style.header false` at line 7)
- Proofs >30 lines: `meromorphicOrderAt_cuspFunction_nat_mul` (32), `poleOrder_nat_mul` (37), `analyticAt_cuspFunction_poleRemoved` (132), `analyticAt_cuspFunction_of_not_pos` (36), `to_qExpansion_coeff_zero_ne` (40), `laurentqExpansion.eq_qExpansion_iff` (32), `laurentqExpansion_coeff_eq_circleIntegral` (151)
