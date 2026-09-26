# Inventory: XYin/PhD/LaurentQExpansion/LaurentQExpansion.lean  (706 lines)

The project's core analytic API for **Laurent q-expansions at the cusp**: extends mathlib's `UpperHalfPlane.qExpansion` (analytic at `q = 0`) to functions whose cusp function is merely `MeromorphicAt` `0`. Defines `poleOrder` (from `meromorphicOrderAt`), `poleRemoved` (`𝕢^poleOrder · f`), `to_qExpansion` (= `qExpansion` of `poleRemoved`) and `laurentqExpansion : LaurentSeries ℂ` (= `single (−poleOrder) 1 * ofPowerSeries (to_qExpansion)`); proves pole removal works, coefficient bookkeeping, nonvanishing of the leading coefficient, meromorphy transport along `h ↦ m·h`, and a Cauchy-integral formula. Imported by `LaurentQExpansion/Algebra.lean`, `Tactic2/LaurentQExpSimpTests.lean`, `jFunction/jfunction.lean`, `XYin.lean`; `laurentqExpansion` has 133 external references, `poleOrder` 62. Root namespace with `open UpperHalfPlane`; the four defs are explicitly `UpperHalfPlane.*`, but the `laurentqExpansion.coeff_*` lemmas live in the root namespace `laurentqExpansion` (NOT `UpperHalfPlane.laurentqExpansion`, so no dot-notation on values). `variable {h : ℝ}` at L44 is shadowed by explicit binders in every lemma except `qExpansion_coeff_eq_circleIntegral_of_differentiableOn`.

## Declarations

### `lemma cuspFunction_nat_mul_eq_cuspFunction_pow`
- **Type**: `{h : ℝ} {m : ℕ} {f : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) h) {q : ℂ} (hq : q ≠ 0) : cuspFunction ((m : ℝ) * h) f q = cuspFunction h f (q ^ m)`
- **What**: Scaling the period by `m` composes the cusp function with `q ↦ q^m` (away from `0`).
- **How**: `Periodic.cuspFunction_eq_of_nonzero` (mathlib Analysis/Complex/Periodic.lean:119) twice; `Complex.exp_eq_exp_iff_exists_int` (SpecialFunctions/Complex/Log.lean:171) on `exp(log(q^m)) = exp(m·log q)` gives `invQParam h (q^m) = invQParam (m h) q + n·h`; conclude by `hfper.int_mul`.
- **Hypotheses**: `f ∘ ofComplex` is `h`-periodic; `q ≠ 0` (any `m`, even `0`).
- **Uses from project**: []
- **Used by**: meromorphicAt_cuspFunction_nat_mul, meromorphicAt_cuspFunction_of_nat_mul, meromorphicOrderAt_cuspFunction_nat_mul; externally Algebra.lean
- **Visibility**: public
- **Lines**: 46–66, proof ≈ 19 lines
- **Notes**: no mathlib analogue (grepped `nat_mul`, `qParam_mul`, `mul_qParam`, `(n * h)` in Periodic.lean, QExpansion.lean, UpperHalfPlane/Exp.lean); upstream candidate `Function.Periodic.cuspFunction_nat_mul`. The `ring_nf; field_simp; push_cast; ring` block (L60–64) is fragile.

### `private lemma cuspFunction_add_eventuallyEq`
- **Type**: `(h : ℝ) (f g : ℍ → ℂ) : cuspFunction h (fun τ ↦ f τ + g τ) =ᶠ[𝓝[≠] 0] fun q ↦ cuspFunction h f q + cuspFunction h g q`
- **What**: Cusp function of a sum is the sum of cusp functions on a punctured neighbourhood (no continuity needed).
- **How**: `Periodic.cuspFunction_eq_of_nonzero` ×3, `rfl`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: meromorphicAt_cuspFunction_add
- **Visibility**: private
- **Lines**: 68–77, proof ≈ 8 lines
- **Notes**: mathlib `UpperHalfPlane.cuspFunction_add` (QExpansion.lean:456) is the global version under `ContinuousAt … 0` hypotheses; this hypothesis-free `𝓝[≠]` form is a gap. Identical skeleton to the next two lemmas.

### `private lemma cuspFunction_mul_eventuallyEq`
- **Type**: `(h : ℝ) (f g : ℍ → ℂ) : cuspFunction h (fun τ ↦ f τ * g τ) =ᶠ[𝓝[≠] 0] fun q ↦ cuspFunction h f q * cuspFunction h g q`
- **What**: as above for products.
- **How**: as above.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: meromorphicAt_cuspFunction_mul
- **Visibility**: private
- **Lines**: 79–88, proof ≈ 8 lines
- **Notes**: duplicate skeleton (L68–96, three copies).

### `private lemma cuspFunction_const_eventuallyEq`
- **Type**: `(h : ℝ) (a : ℂ) : cuspFunction h (fun _ : ℍ ↦ a) =ᶠ[𝓝[≠] 0] fun _ ↦ a`
- **What**: cusp function of a constant is that constant off `0`.
- **How**: `Periodic.cuspFunction_eq_of_nonzero`, `rfl`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: meromorphicAt_cuspFunction_const
- **Visibility**: private
- **Lines**: 90–96, proof ≈ 5 lines
- **Notes**: Algebra.lean re-proves the global version `cuspFunction_const` (L40–46) privately — moral duplicate.

### `lemma meromorphicAt_cuspFunction_add`
- **Type**: `{h : ℝ} {f g : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) (hg : MeromorphicAt (cuspFunction h g) 0) : MeromorphicAt (cuspFunction h (fun τ ↦ f τ + g τ)) 0`
- **What**: cusp-meromorphy is closed under pointwise addition.
- **How**: mathlib `MeromorphicAt.add` (Meromorphic/Basic.lean:74) transported by `MeromorphicAt.congr` (:250) along `cuspFunction_add_eventuallyEq`.
- **Hypotheses**: both cusp-meromorphic.
- **Uses from project**: cuspFunction_add_eventuallyEq
- **Used by**: meromorphicAt_cuspFunction_finset_sum; externally Algebra.lean
- **Visibility**: public
- **Lines**: 99–103, proof ≈ 1 line
- **Notes**: none.

### `lemma meromorphicAt_cuspFunction_mul`
- **Type**: `{h : ℝ} {f g : ℍ → ℂ} (hf) (hg) : MeromorphicAt (cuspFunction h (fun τ ↦ f τ * g τ)) 0`
- **What**: closed under pointwise multiplication.
- **How**: `MeromorphicAt.mul` (Basic.lean:98) + `congr` along `cuspFunction_mul_eventuallyEq`.
- **Hypotheses**: both cusp-meromorphic.
- **Uses from project**: cuspFunction_mul_eventuallyEq
- **Used by**: meromorphicAt_cuspFunction_finset_prod; externally Algebra.lean, Cox/ModularPolynomial/{AnalyticSupport,IntegralDescent,Interpolation}.lean
- **Visibility**: public
- **Lines**: 106–110, proof ≈ 1 line
- **Notes**: none.

### `lemma meromorphicAt_cuspFunction_const`
- **Type**: `(h : ℝ) (a : ℂ) : MeromorphicAt (cuspFunction h (fun _ : ℍ ↦ a)) 0`
- **What**: constants are cusp-meromorphic.
- **How**: `MeromorphicAt.const` (Basic.lean:68) + `congr`.
- **Hypotheses**: none.
- **Uses from project**: cuspFunction_const_eventuallyEq
- **Used by**: meromorphicAt_cuspFunction_finset_sum, meromorphicAt_cuspFunction_finset_prod; externally 9 refs (Algebra, DiagonalLaurent, AnalyticSupport, IntegralDescent)
- **Visibility**: public
- **Lines**: 113–115, proof ≈ 1 line
- **Notes**: none.

### `lemma meromorphicAt_cuspFunction_finset_sum`
- **Type**: `{ι : Type*} {h : ℝ} {s : Finset ι} {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) : MeromorphicAt (cuspFunction h (∑ i ∈ s, f i)) 0`
- **What**: closed under finite sums.
- **How**: `Finset.induction_on`; empty case from `meromorphicAt_cuspFunction_const h 0`; step by `Finset.sum_insert` + `change` to a pointwise sum + `meromorphicAt_cuspFunction_add`.
- **Hypotheses**: each summand cusp-meromorphic.
- **Uses from project**: meromorphicAt_cuspFunction_const, meromorphicAt_cuspFunction_add
- **Used by**: unused in file; externally Algebra.lean, AnalyticSupport.lean, Interpolation.lean
- **Visibility**: public
- **Lines**: 118–129, proof ≈ 9 lines
- **Notes**: mathlib has `MeromorphicAt.sum` (Basic.lean:138); this induction exists only because there is no `cuspFunction_finset_sum_eventuallyEq`.

### `lemma meromorphicAt_cuspFunction_finset_prod`
- **Type**: as above with `∏`.
- **What**: closed under finite products.
- **How**: as above with `meromorphicAt_cuspFunction_mul`, `meromorphicAt_cuspFunction_const h 1`.
- **Hypotheses**: each factor cusp-meromorphic.
- **Uses from project**: meromorphicAt_cuspFunction_const, meromorphicAt_cuspFunction_mul
- **Used by**: unused in file; externally Algebra.lean, IntegralDescent.lean
- **Visibility**: public
- **Lines**: 132–143, proof ≈ 9 lines
- **Notes**: duplicate skeleton with the sum version and with Algebra.lean L250–281 (`MeromorphicAt.prod`, Basic.lean:109).

### `lemma meromorphicAt_cuspFunction_nat_mul`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (hfper : Periodic (f ∘ ofComplex) h) : MeromorphicAt (cuspFunction ((m : ℝ) * h) f) 0`
- **What**: meromorphy at the cusp is preserved when the period is multiplied by `m`.
- **How**: `MeromorphicAt.comp_analyticAt` (Basic.lean:438) of `cuspFunction h f` with `q ↦ q^m`, then `congr` along `cuspFunction_nat_mul_eq_cuspFunction_pow`.
- **Hypotheses**: `m ≠ 0`; cusp-meromorphic; `h`-periodic.
- **Uses from project**: cuspFunction_nat_mul_eq_cuspFunction_pow
- **Used by**: unused in file; externally Algebra.lean (2)
- **Visibility**: public
- **Lines**: 147–159, proof ≈ 9 lines
- **Notes**: with `meromorphicAt_cuspFunction_of_nat_mul` this is an `iff` that is never stated.

### `private lemma eventually_differentiableAt_pow_mul_of_meromorphicAt_comp_pow_aux`
- **Type**: `{g : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0) (h : MeromorphicAt (g ∘ fun q ↦ q ^ m) 0) (n : ℕ) : ∀ᶠ z in 𝓝[≠] 0, DifferentiableAt ℂ (fun z ↦ z ^ n * g z) z`
- **What**: If `g ∘ (·^m)` is meromorphic at `0`, then `z^n · g` is differentiable on a punctured neighbourhood of `0`.
- **How**: `MeromorphicAt.eventually_analyticAt` (Basic.lean:343) gives analyticity of `g ∘ (·^m)` on a punctured nbhd; push the nbhd forward through the open map `Complex.isOpenQuotientMap_pow` (Analysis/Complex/OpenMapping.lean:253, `.isOpenMap.image_mem_nhds`); at each `q^m ≠ 0` recover analyticity of `g` from that of the composite via `analyticAt_comp_iff_of_deriv_ne_zero` (Calculus/InverseFunctionTheorem/Analytic.lean:40) with `deriv_pow_field ≠ 0`.
- **Hypotheses**: `m ≠ 0`; `g ∘ (·^m)` meromorphic at `0`.
- **Uses from project**: []
- **Used by**: meromorphicAt_of_comp_pow
- **Visibility**: private
- **Lines**: 161–191, proof ≈ 30 lines (>30 incl. statement)
- **Notes**: `letI : NeZero m`; the set `U` and `hUimage` manipulation (L176–185) is a manual "image of a nbhd under an open map is a nbhd" argument.

### `lemma meromorphicAt_of_comp_pow`
- **Type**: `{g : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0) (h : MeromorphicAt (g ∘ fun q ↦ q ^ m) 0) : MeromorphicAt g 0`
- **What**: Meromorphy descends along the power map `z ↦ z^m` at its critical point `0` (mathlib's `meromorphicAt_comp_iff_of_deriv_ne_zero`, Basic.lean:458, needs a nonvanishing derivative and so does not apply).
- **How**: unpack `⟨n, hn⟩` (analyticity of `z^n · (g ∘ (·^m))`); set `G z = z^n g z`; `G ∘ (·^m) = q^{(m−1)n} · (q^{mn} g(q^m))` is analytic at `0`; continuity of `G` at `0` from `(isOpenQuotientMap_pow m).continuousAt_comp_iff`; differentiability on a punctured nbhd from the aux lemma; conclude by Riemann's removable-singularity theorem `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` (Analysis/Complex/RemovableSingularity.lean:36).
- **Hypotheses**: `m ≠ 0`.
- **Uses from project**: eventually_differentiableAt_pow_mul_of_meromorphicAt_comp_pow_aux
- **Used by**: meromorphicAt_cuspFunction_of_nat_mul
- **Visibility**: public
- **Lines**: 194–220, proof ≈ 24 lines
- **Notes**: general complex-analysis lemma, nothing cusp-specific; mathlib gap (upstream `meromorphicAt_comp_pow_iff` next to `meromorphicAt_comp_iff_of_deriv_ne_zero`). The `hmn : m * n = (m - 1) * n + n` calc (L203–206) is `Nat.succ_pred`/`omega`-level.

### `lemma meromorphicAt_cuspFunction_of_nat_mul`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction ((m : ℝ) * h) f) 0) (hfper : Periodic (f ∘ ofComplex) h) : MeromorphicAt (cuspFunction h f) 0`
- **What**: converse of `meromorphicAt_cuspFunction_nat_mul`: meromorphy at period `m h` implies meromorphy at period `h`.
- **How**: `meromorphicAt_of_comp_pow` after `congr` along `cuspFunction_nat_mul_eq_cuspFunction_pow`.
- **Hypotheses**: `m ≠ 0`; `h`-periodic.
- **Uses from project**: meromorphicAt_of_comp_pow, cuspFunction_nat_mul_eq_cuspFunction_pow
- **Used by**: unused in file; externally Cox/ModularPolynomial/Construction.lean, Interpolation.lean
- **Visibility**: public
- **Lines**: 224–232, proof ≈ 5 lines
- **Notes**: none.

### `def UpperHalfPlane.poleOrder`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : ℕ := if meromorphicOrderAt (cuspFunction h f) 0 < 0 then Int.natAbs ((meromorphicOrderAt (cuspFunction h f) 0).untopD 0) else 0`
- **What**: The order of the pole of the cusp function at `q = 0` (`0` when analytic, identically zero, or not meromorphic).
- **How**: definition by cases on `meromorphicOrderAt` (mathlib Meromorphic/Order.lean:47).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: poleOrder_eq_of_meromorphicOrderAt_eq, poleOrder_eq_zero_of_meromorphicOrderAt_nonneg, poleOrder_eq_toNat_neg_meromorphicOrderAt, poleOrder_nat_mul, poleRemoved, laurentqExpansion, analyticAt_cuspFunction_poleRemoved, analyticAt_cuspFunction_iff_poleOrder_eq_zero, cuspFunction_poleRemoved_eq, all `laurentqExpansion.coeff_*`, meromorphicOrderAt_cuspFunction_eq_neg_poleOrder, to_qExpansion_coeff_zero_ne, …, laurentqExpansion_coeff_eq_circleIntegral; externally 62 refs
- **Visibility**: public
- **Lines**: 236–239
- **Notes**: the `if/natAbs/untopD` shape forces three normalisation lemmas (L243–273) and `unfold` in `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` (L499); the closed form `Int.toNat (-(…).untopD 0)` proved at L261 is simpler and could BE the definition (or `(-(meromorphicOrderAt …)).untop₀.toNat`). No `@[simp]` lemmas `poleOrder_zero`, `poleOrder_one`, `poleOrder_const`, `poleOrder_of_analyticAt`. No mathlib analogue as a def — mathlib works with `meromorphicOrderAt : WithTop ℤ` and `MeromorphicNFAt`.

### `lemma poleOrder_eq_of_meromorphicOrderAt_eq`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} {r : ℕ} (hord : meromorphicOrderAt (cuspFunction h f) 0 = ((-(r : ℤ) : ℤ) : WithTop ℤ)) : poleOrder h f = r`
- **What**: meromorphic order `−r` reads off as pole order `r` (also for `r = 0`).
- **How**: unfold; `Nat.eq_zero_or_pos r`; `WithTop.untopD_coe`; `omega`.
- **Hypotheses**: order equals `−r`.
- **Uses from project**: poleOrder
- **Used by**: poleOrder_eq_toNat_neg_meromorphicOrderAt; externally jfunction.lean
- **Visibility**: public
- **Lines**: 243–251, proof ≈ 6 lines
- **Notes**: converse `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` (L496) is proved separately with a duplicated `unfold`/`cases` skeleton; an `iff` `poleOrder_eq_iff` is missing.

### `lemma poleOrder_eq_zero_of_meromorphicOrderAt_nonneg`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hord : 0 ≤ meromorphicOrderAt (cuspFunction h f) 0) : poleOrder h f = 0`
- **What**: nonnegative order (incl. `⊤`) means no pole.
- **How**: `simp [poleOrder, not_lt_of_ge hord]`.
- **Hypotheses**: order `≥ 0`.
- **Uses from project**: poleOrder
- **Used by**: poleOrder_eq_toNat_neg_meromorphicOrderAt, analyticAt_cuspFunction_iff_poleOrder_eq_zero
- **Visibility**: public
- **Lines**: 255–257, proof ≈ 1 line
- **Notes**: 0 external.

### `lemma poleOrder_eq_toNat_neg_meromorphicOrderAt`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : poleOrder h f = Int.toNat (-(meromorphicOrderAt (cuspFunction h f) 0).untopD 0)`
- **What**: closed formula for the pole order (positive part of minus the order, `0` at `⊤`).
- **How**: `cases` on the `WithTop ℤ` value; `⊤` via `poleOrder_eq_zero_of_meromorphicOrderAt_nonneg`; `k < 0` via `poleOrder_eq_of_meromorphicOrderAt_eq (r := k.natAbs)`; `k ≥ 0` via the nonneg lemma; `omega`.
- **Hypotheses**: none.
- **Uses from project**: poleOrder, poleOrder_eq_zero_of_meromorphicOrderAt_nonneg, poleOrder_eq_of_meromorphicOrderAt_eq
- **Used by**: poleOrder_nat_mul (×2); externally Cox/ModularFunction.lean, Cox/CoxMatrices/LaurentExpansion.lean
- **Visibility**: public
- **Lines**: 261–273, proof ≈ 11 lines
- **Notes**: this should be the definition.

### `lemma meromorphicOrderAt_cuspFunction_nat_mul`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero) (hfper) : meromorphicOrderAt (cuspFunction ((m : ℝ) * h) f) 0 = meromorphicOrderAt (cuspFunction h f) 0 * m`
- **What**: scaling the period by `m` multiplies the meromorphic order at the cusp by `m`.
- **How**: `meromorphicOrderAt_congr` (Order.lean:261) along `cuspFunction_nat_mul_eq_cuspFunction_pow`, then mathlib `MeromorphicAt.meromorphicOrderAt_comp` (Order.lean:810) with `analyticOrderAt_pow` (Analytic/Order.lean:455) + `analyticOrderAt_id` (:186) giving order `m` for `q^m`, non-constancy via `eventuallyConst_iff_analyticOrderAt_sub_eq_top` (:80).
- **Hypotheses**: `m ≠ 0`; cusp-meromorphic; `h`-periodic.
- **Uses from project**: cuspFunction_nat_mul_eq_cuspFunction_pow
- **Used by**: poleOrder_nat_mul
- **Visibility**: public
- **Lines**: 275–298, proof ≈ 19 lines
- **Notes**: 0 external; no docstring; the `horderPow` block (L287–290, `analyticOrderAt (q^m) 0 = m`) is a general fact worth its own simp lemma (`analyticOrderAt_pow_id`?).

### `lemma poleOrder_nat_mul`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero) (hfper) : poleOrder ((m : ℝ) * h) f = m * poleOrder h f`
- **What**: pole order scales linearly with the period multiplier.
- **How**: `poleOrder_eq_toNat_neg_meromorphicOrderAt` ×2, `meromorphicOrderAt_cuspFunction_nat_mul`, `WithTop.untopD_zero_mul` (Algebra/Order/Ring/WithTop.lean:73), then `Int.toNat_mul` (core `Init/Data/Int/Order.lean`) / `Int.toNat_eq_zero` by cases on the sign.
- **Hypotheses**: `m ≠ 0`; cusp-meromorphic; `h`-periodic.
- **Uses from project**: poleOrder_eq_toNat_neg_meromorphicOrderAt, meromorphicOrderAt_cuspFunction_nat_mul, poleOrder
- **Used by**: unused in file; externally Algebra.lean, DiagonalLaurent.lean
- **Visibility**: public
- **Lines**: 300–312, proof ≈ 10 lines
- **Notes**: no docstring.

### `def UpperHalfPlane.poleRemoved`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : ℍ → ℂ := fun τ ↦ 𝕢 h τ ^ poleOrder h f * f τ`
- **What**: `f` multiplied by `q^{poleOrder}` — the pole at the cusp is cancelled.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: poleOrder
- **Used by**: to_qExpansion, analyticAt_cuspFunction_poleRemoved, analyticAt_cuspFunction_iff_poleOrder_eq_zero, cuspFunction_poleRemoved_eq, to_qExpansion_coeff_zero_ne, laurentqExpansion.eq_qExpansion_iff, exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt, three private circle-integral lemmas, laurentqExpansion_coeff_eq_circleIntegral; externally 20 refs
- **Visibility**: public
- **Lines**: 316–317
- **Notes**: no `poleRemoved_apply` simp lemma (unfolded by `simp [UpperHalfPlane.poleRemoved]` at L382, 428, 437, 444, 596 and Algebra.lean:120); `poleRemoved h f = f` when `poleOrder h f = 0` is proved inline three times (L426–428, L442–444, L594–596) — missing `poleRemoved_of_poleOrder_eq_zero`.

### `def UpperHalfPlane.to_qExpansion`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : PowerSeries ℂ := qExpansion h (poleRemoved h f)`
- **What**: q-expansion of the pole-removed function (the regular part shifted so that its constant term is the leading Laurent coefficient).
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: poleRemoved
- **Used by**: laurentqExpansion, coeff_eq_HahnSeries_add, coeff_eq_zero_of_lt, coeff_neg_poleOrder_add, coeff_of_geq, coeff_of_qExpansion, coeff_neg_poleOrder, coeff_zero, to_qExpansion_coeff_zero_ne, to_qExpansion_ne_zero, to_qExpansion_eq_powerSeriesPart, eq_qExpansion_iff, laurentqExpansion_coeff_eq_circleIntegral; externally 13 refs
- **Visibility**: public
- **Lines**: 321–322
- **Notes**: snake_case name for a def (mathlib: `qExpansionPoleRemoved`/`regularPart`); relied upon definitionally (`rfl` at Algebra.lean:135; `simpa [UpperHalfPlane.to_qExpansion, …]` at L536, L597, Algebra.lean:380). Note: its constant coefficient is NOT guaranteed nonzero when `poleOrder = 0` (then `to_qExpansion = qExpansion`, which may vanish to any order) — unlike mathlib's `LaurentSeries.powerSeriesPart` (LaurentSeries.lean:209–212, always nonzero constant term for nonzero series).

### `def UpperHalfPlane.laurentqExpansion`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : LaurentSeries ℂ := HahnSeries.single (-(poleOrder h f : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℂ (to_qExpansion h f)`
- **What**: The Laurent q-expansion of `f` at the cusp: `q^{−poleOrder}` times the power series of the pole-removed function.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: poleOrder, to_qExpansion
- **Used by**: all `laurentqExpansion.*` lemmas, laurentqExpansion_coeff_eq_circleIntegral; externally 133 refs across Algebra, Tactic2, jFunction, Cox
- **Visibility**: public
- **Lines**: 326–328
- **Notes**: exactly the shape of mathlib `LaurentSeries.ofPowerSeries_powerSeriesPart : ofPowerSeries ℤ R x.powerSeriesPart = single (-x.order) 1 * x` / `single_order_mul_powerSeriesPart : single x.order 1 * x.powerSeriesPart = x` (LaurentSeries.lean:252, 237). Written with `HahnSeries.ofPowerSeries ℤ ℂ` rather than mathlib's coercion `(· : LaurentSeries ℂ)` (`coeToLaurentSeries`, LaurentSeries.lean:374; reducibly the same term), so the `LaurentSeries.coe_*` simp set (`coeff_coe` :335, `coe_C` :346, `coe_X` :349, `coe_mul` :332, `coe_pow` :359, `coe_smul` :353) does not fire syntactically; the file mixes both forms (`PowerSeries.coeff_coe` at L463, 473, 591).

### `lemma cuspFunction_qpow_mul_eq`
- **Type**: `{h : ℝ} (hh : 0 < h) (f : ℍ → ℂ) {n : ℕ} {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) : cuspFunction h (fun τ ↦ 𝕢 h τ ^ n * f τ) q = q ^ n * cuspFunction h f q`
- **What**: pointwise, on the punctured unit disc, the cusp function of `q^n · f` is `q^n` times that of `f`.
- **How**: `Periodic.im_invQParam_pos_of_norm_lt_one` (UpperHalfPlane/Exp.lean:25) puts `invQParam h q` in `ℍ`; `UpperHalfPlane.ofComplex_apply_of_im_pos` (UpperHalfPlane/Topology.lean:162); `Periodic.qParam_right_inv` (Periodic.lean:61).
- **Hypotheses**: `0 < h`; `q ≠ 0`; `‖q‖ < 1` (needed because `cuspFunction` passes through `ofComplex`, which is junk outside `ℍ`).
- **Uses from project**: []
- **Used by**: analyticAt_cuspFunction_poleRemoved, cuspFunction_poleRemoved_eq; externally Algebra.lean, jfunction.lean
- **Visibility**: public
- **Lines**: 330–336, proof ≈ 4 lines
- **Notes**: no docstring. Mathlib has no `cuspFunction_qParam_pow_mul`; `qExpansion_qpow_mul` in Algebra.lean (private) is its q-expansion form.

### `lemma cuspFunction_apply_zero_eq`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} {G : ℂ → ℂ} (hEq : cuspFunction h f =ᶠ[𝓝[≠] 0] G) (hG : ContinuousAt G 0) : cuspFunction h f 0 = G 0`
- **What**: the `limUnder`-defined value of the cusp function at `0` equals `G 0` whenever the cusp function agrees with a continuous `G` off `0`.
- **How**: `Periodic.cuspFunction_zero_eq_limUnder_nhds_ne` (Periodic.lean:123); `Filter.map_congr`; `Tendsto.limUnder_eq` with `tendsto_nhdsWithin_of_tendsto_nhds`.
- **Hypotheses**: as stated.
- **Uses from project**: []
- **Used by**: analyticAt_cuspFunction_of_eventuallyEq; externally Algebra.lean
- **Visibility**: public
- **Lines**: 340–349, proof ≈ 7 lines
- **Notes**: holds at the `Function.Periodic.cuspFunction h F` level for any `F : ℂ → ℂ`; generalises mathlib `Periodic.cuspFunction_zero_of_zero_at_inf` (Periodic.lean:198) / `UpperHalfPlane.cuspFunction_apply_zero` (QExpansion.lean:107); upstream candidate.

### `lemma analyticAt_cuspFunction_of_eventuallyEq`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0) (hEq : cuspFunction h f =ᶠ[𝓝[≠] 0] G) : AnalyticAt ℂ (cuspFunction h f) 0`
- **What**: analyticity of the cusp function follows from agreement off `0` with an analytic `G`.
- **How**: `eventuallyEq_nhds_of_eventuallyEq_nhdsNE` (Topology/NhdsWithin.lean:432) with the value at `0` from `cuspFunction_apply_zero_eq`; `AnalyticAt.congr`.
- **Hypotheses**: as stated.
- **Uses from project**: cuspFunction_apply_zero_eq
- **Used by**: analyticAt_cuspFunction_of_not_pos, analyticAt_cuspFunction_poleRemoved (×3)
- **Visibility**: public
- **Lines**: 353–357, proof ≈ 2 lines
- **Notes**: 0 external; the workhorse for all analyticity claims in the file.

### `lemma analyticAt_cuspFunction_of_not_pos`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hh : h ≤ 0) : AnalyticAt ℂ (cuspFunction h f) 0`
- **What**: junk case: for `h ≤ 0` the cusp function is constant (`invQParam h q` has non-positive imaginary part on the unit disc, so `ofComplex` returns the default point).
- **How**: `Periodic.im_invQParam` (Periodic.lean:54), `Real.log_nonpos`, `UpperHalfPlane.ofComplex_apply_of_im_nonpos` (Topology.lean:166), `analyticAt_cuspFunction_of_eventuallyEq` with `G := const`.
- **Hypotheses**: `h ≤ 0`.
- **Uses from project**: analyticAt_cuspFunction_of_eventuallyEq
- **Used by**: analyticAt_cuspFunction_poleRemoved, cuspFunction_poleRemoved_eq
- **Visibility**: public
- **Lines**: 359–372, proof ≈ 12 lines
- **Notes**: 0 external; exists solely to make `analyticAt_cuspFunction_poleRemoved` and `cuspFunction_poleRemoved_eq` free of `0 < h` (which Algebra.lean then re-imposes anyway); no docstring.

### `lemma analyticAt_cuspFunction_poleRemoved`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) : AnalyticAt ℂ (cuspFunction h (poleRemoved h f)) 0`
- **What**: **Pole removal**: multiplying by `q^{poleOrder}` yields a function whose cusp function is analytic at `0`.
- **How**: For `0 < h`: `cuspFunction h (poleRemoved) =ᶠ[𝓝[≠]0] q^{N} · cuspFunction h f` (`cuspFunction_qpow_mul_eq`). Case on `meromorphicOrderAt`: `⊤` ⇒ `f ≡ 0` near `0` (`meromorphicOrderAt_eq_top_iff`, Order.lean:64) ⇒ agrees with `0`; `k` ⇒ `meromorphicOrderAt_eq_int_iff` (Order.lean:94) gives analytic `g` with `cuspFunction h f = z^k • g` off `0`; if `k < 0` then `N = −k` (`Int.ofNat_natAbs_of_nonpos`) and `q^N q^k g = g` (`zpow_add₀`); if `k ≥ 0` then `N = 0` and `q^k g` is analytic. Each case closes with `analyticAt_cuspFunction_of_eventuallyEq`. For `h ≤ 0`: `analyticAt_cuspFunction_of_not_pos`.
- **Hypotheses**: cusp-meromorphic (any `h`).
- **Uses from project**: cuspFunction_qpow_mul_eq, analyticAt_cuspFunction_of_eventuallyEq, analyticAt_cuspFunction_of_not_pos, poleOrder, poleRemoved
- **Used by**: analyticAt_cuspFunction_iff_poleOrder_eq_zero, to_qExpansion_coeff_zero_ne, exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt; externally Algebra.lean (3), Cox/CoxMatrices/LaurentExpansion.lean
- **Visibility**: public
- **Lines**: 374–417, proof ≈ 43 lines (>30)
- **Notes**: no docstring on the file's central lemma. Mathlib vocabulary: this is `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt` (Basic.lean:359) / `meromorphicOrderAt_eq_int_iff` at `x = 0` plus the `cuspFunction`-transport; the analytic `g` there is `cuspFunction h (poleRemoved h f)` up to `=ᶠ[𝓝[≠]]`, i.e. essentially `toMeromorphicNFAt` (NormalForm.lean:377). A cleaner route: prove once `cuspFunction h (poleRemoved h f) =ᶠ[𝓝[≠] 0] (z ↦ z^N * cuspFunction h f z)` (= `cuspFunction_poleRemoved_eq`, L432, which is proved AFTER and re-derives `hEq_shift` L378–384), then apply mathlib's `MeromorphicAt.analyticAt`-style lemma `AnalyticAt.of_meromorphicOrderAt_pos`/`meromorphicOrderAt_nonneg` reasoning.

### `lemma analyticAt_cuspFunction_iff_poleOrder_eq_zero`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) : AnalyticAt ℂ (cuspFunction h f) 0 ↔ poleOrder h f = 0`
- **What**: a cusp-meromorphic function is analytic at the cusp iff it has no pole there.
- **How**: `→`: `AnalyticAt.meromorphicOrderAt_nonneg` (Order.lean:291) + `poleOrder_eq_zero_of_meromorphicOrderAt_nonneg`; `←`: `poleRemoved h f = f` (funext, simp) + `analyticAt_cuspFunction_poleRemoved`.
- **Hypotheses**: cusp-meromorphic.
- **Uses from project**: poleOrder_eq_zero_of_meromorphicOrderAt_nonneg, analyticAt_cuspFunction_poleRemoved, poleRemoved, poleOrder
- **Used by**: cuspFunction_poleRemoved_eq; externally Algebra.lean, jfunction.lean, Cox/ModularFunction.lean
- **Visibility**: public
- **Lines**: 420–430, proof ≈ 8 lines
- **Notes**: mathlib's `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt` (NormalForm.lean:114) is the same fact in normal-form vocabulary; not directly applicable because `cuspFunction h f 0` is a `limUnder` junk value that need not match.

### `lemma cuspFunction_poleRemoved_eq`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero) {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) : cuspFunction h (poleRemoved h f) q = q ^ poleOrder h f * cuspFunction h f q`
- **What**: pointwise formula for the pole-removed cusp function on the punctured unit disc, valid for every `h`.
- **How**: `0 < h`: `cuspFunction_qpow_mul_eq`; `h ≤ 0`: `poleOrder = 0` by `analyticAt_cuspFunction_iff_poleOrder_eq_zero` + `analyticAt_cuspFunction_of_not_pos`, then `poleRemoved h f = f`.
- **Hypotheses**: cusp-meromorphic; `q ≠ 0`; `‖q‖ < 1`.
- **Uses from project**: cuspFunction_qpow_mul_eq, analyticAt_cuspFunction_iff_poleOrder_eq_zero, analyticAt_cuspFunction_of_not_pos, poleRemoved, poleOrder
- **Used by**: to_qExpansion_coeff_zero_ne, cuspFunction_poleRemoved_div_zpow_eq_of_mem_sphere; externally Algebra.lean (2)
- **Visibility**: public
- **Lines**: 432–445, proof ≈ 9 lines
- **Notes**: no docstring; the `hmero` hypothesis is needed only for the `h ≤ 0` junk branch.

### `lemma laurentqExpansion.coeff_eq_HahnSeries_add`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) {n : ℤ} : (laurentqExpansion h f).coeff n = (HahnSeries.ofPowerSeries ℤ ℂ (to_qExpansion h f)).coeff (n + poleOrder h f)`
- **What**: Laurent coefficient `n` is power-series coefficient `n + poleOrder`.
- **How**: `HahnSeries.coeff_single_mul` (HahnSeries/Multiplication.lean:471: `(single b r * x).coeff a = r * x.coeff (a - b)`), `sub_eq_add_neg`.
- **Hypotheses**: none.
- **Uses from project**: laurentqExpansion, to_qExpansion, poleOrder
- **Used by**: coeff_eq_zero_of_lt, coeff_neg_poleOrder_add, coeff_of_geq
- **Visibility**: public
- **Lines**: 447–455, proof ≈ 5 lines
- **Notes**: 0 external; `simpa [UpperHalfPlane.poleOrder, …]` (L451) unfolds `poleOrder` needlessly; mixed-case name.

### `lemma laurentqExpansion.coeff_eq_zero_of_lt`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} {n : ℤ} (hn : n < -(poleOrder h f : ℤ)) : (laurentqExpansion h f).coeff n = 0`
- **What**: coefficients below `−poleOrder` vanish.
- **How**: `coeff_eq_HahnSeries_add` + `PowerSeries.coeff_coe` (LaurentSeries.lean:335, `if i < 0 then 0 else …`).
- **Hypotheses**: `n < −poleOrder`.
- **Uses from project**: coeff_eq_HahnSeries_add, poleOrder, laurentqExpansion
- **Used by**: coeff_of_qExpansion, poleOrder_to_order, laurentqExpansion_coeff_eq_circleIntegral; externally 7 refs (Algebra, Tactic2, jfunction, Kronecker)
- **Visibility**: public
- **Lines**: 457–463, proof ≈ 4 lines
- **Notes**: SHORT collision flagged (`coeff_eq_zero_of_lt`).

### `lemma laurentqExpansion.coeff_neg_poleOrder_add`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) (n : ℕ) : (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ) + n) = (to_qExpansion h f).coeff n`
- **What**: coefficient at `−poleOrder + n` is the `n`-th coefficient of the regular part.
- **How**: `simp [coeff_eq_HahnSeries_add, PowerSeries.coeff_coe]`.
- **Hypotheses**: none.
- **Uses from project**: coeff_eq_HahnSeries_add, poleOrder, to_qExpansion, laurentqExpansion
- **Used by**: coeff_neg_poleOrder, to_qExpansion_eq_powerSeriesPart; externally Tactic2, jFunction/qexp_coeffs.lean
- **Visibility**: public
- **Lines**: 465–467, proof ≈ 1 line
- **Notes**: the natural `@[simp]` lemma of the file (untagged).

### `lemma laurentqExpansion.coeff_of_geq`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} {n : ℤ} (hn : -(poleOrder h f : ℤ) ≤ n) : (laurentqExpansion h f).coeff n = (to_qExpansion h f).coeff (Int.toNat (n + poleOrder h f))`
- **What**: coefficients at or above `−poleOrder` via `Int.toNat`.
- **How**: `coeff_eq_HahnSeries_add`, `PowerSeries.coeff_coe`, `if_neg`, `Int.natAbs_of_nonneg`/`Int.toNat_of_nonneg` (core).
- **Hypotheses**: `−poleOrder ≤ n`.
- **Uses from project**: coeff_eq_HahnSeries_add, poleOrder, to_qExpansion, laurentqExpansion
- **Used by**: coeff_of_qExpansion, coeff_zero, laurentqExpansion_coeff_eq_circleIntegral; externally 9 refs (Algebra, Tactic2, jfunction, LevelThree, LaurentExpansion)
- **Visibility**: public
- **Lines**: 469–476, proof ≈ 5 lines
- **Notes**: `geq` is not mathlib naming (`_of_le`/`_of_neg_le`).

### `lemma laurentqExpansion.coeff_of_qExpansion`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) (n : ℤ) : (laurentqExpansion h f).coeff n = if n < -(poleOrder h f : ℤ) then 0 else (to_qExpansion h f).coeff (Int.toNat (n + poleOrder h f))`
- **What**: `ite` form of the two previous lemmas.
- **How**: `by_cases` + `coeff_eq_zero_of_lt` / `coeff_of_geq`.
- **Hypotheses**: none.
- **Uses from project**: coeff_eq_zero_of_lt, coeff_of_geq, poleOrder, to_qExpansion, laurentqExpansion
- **Used by**: unused in file; externally Cox/CoxMatrices/LaurentExpansion.lean
- **Visibility**: public
- **Lines**: 478–484, proof ≈ 4 lines
- **Notes**: name does not say `ite`; candidate `laurentqExpansion_coeff` `@[simp]`.

### `lemma laurentqExpansion.coeff_neg_poleOrder`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ)) = (to_qExpansion h f).coeff 0`
- **What**: the leading Laurent coefficient is the constant term of the regular part.
- **How**: `coeff_neg_poleOrder_add` at `n = 0`.
- **Hypotheses**: none.
- **Uses from project**: coeff_neg_poleOrder_add, poleOrder, to_qExpansion, laurentqExpansion
- **Used by**: laurentqExpansion.ne_zero, poleOrder_to_order, eq_qExpansion_iff; externally LaurentExpansion.lean
- **Visibility**: public
- **Lines**: 486–488, proof ≈ 1 line
- **Notes**: none.

### `lemma laurentqExpansion.coeff_zero`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : (laurentqExpansion h f).coeff 0 = (to_qExpansion h f).coeff (poleOrder h f)`
- **What**: the constant Laurent coefficient.
- **How**: `coeff_of_geq` at `n = 0`.
- **Hypotheses**: none.
- **Uses from project**: coeff_of_geq, poleOrder, to_qExpansion, laurentqExpansion
- **Used by**: unused in file; 0 external
- **Visibility**: public
- **Lines**: 490–494, proof ≈ 3 lines
- **Notes**: junk candidate; SHORT collision (`coeff_zero`).

### `lemma meromorphicOrderAt_cuspFunction_eq_neg_poleOrder`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (h0 : poleOrder h f ≠ 0) : meromorphicOrderAt (cuspFunction h f) 0 = -(poleOrder h f : ℤ)`
- **What**: when there is a genuine pole, the meromorphic order is minus the pole order.
- **How**: `unfold poleOrder`; the order must be `< 0` (else `poleOrder = 0`); `cases` on `WithTop ℤ`; `Int.ofNat_natAbs_of_nonpos` (core); `simp`.
- **Hypotheses**: `poleOrder h f ≠ 0`.
- **Uses from project**: poleOrder
- **Used by**: to_qExpansion_coeff_zero_ne (×2); externally Cox/ModularFunction.lean, LaurentExpansion.lean
- **Visibility**: public
- **Lines**: 496–513, proof ≈ 16 lines
- **Notes**: no docstring; converse of `poleOrder_eq_of_meromorphicOrderAt_eq` with duplicated `unfold`/`cases` skeleton (L246–251 vs L499–513); the `≠ 0` hypothesis is the price of the junk value `0`.

### `lemma to_qExpansion_coeff_zero_ne`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (h0 : poleOrder h f ≠ 0) : (to_qExpansion h f).coeff 0 ≠ 0`
- **What**: the leading Laurent coefficient is nonzero when there is a genuine pole.
- **How**: build `cuspFunction h f =ᶠ[𝓝[≠] 0] (z − 0)^{ord.untop₀} • cuspFunction h (poleRemoved h f)` from `cuspFunction_poleRemoved_eq`, `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder`, `zpow_add₀`; then mathlib `AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE` (Meromorphic/TrailingCoefficient.lean:64) identifies the trailing coefficient with `cuspFunction h (poleRemoved h f) 0`, which is nonzero by `MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero` (:143, order `≠ ⊤`); `qExpansion_coeff` at `0` is the value at `0`.
- **Hypotheses**: cusp-meromorphic; `poleOrder ≠ 0`.
- **Uses from project**: analyticAt_cuspFunction_poleRemoved, cuspFunction_poleRemoved_eq, meromorphicOrderAt_cuspFunction_eq_neg_poleOrder, to_qExpansion, poleRemoved, poleOrder
- **Used by**: to_qExpansion_ne_zero, laurentqExpansion.ne_zero, poleOrder_to_order, eq_qExpansion_iff
- **Visibility**: public
- **Lines**: 515–536, proof ≈ 20 lines
- **Notes**: no docstring; 0 external; good use of mathlib's trailing-coefficient API. The general statement (`coeff 0 ≠ 0 ↔ meromorphicOrderAt = −poleOrder ≠ ⊤`, i.e. also when `poleOrder = 0` but the order is exactly `0`) is not stated.

### `lemma to_qExpansion_ne_zero`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero) (h0 : poleOrder h f ≠ 0) : to_qExpansion h f ≠ 0`
- **What**: the regular part is a nonzero power series when there is a pole.
- **How**: from `to_qExpansion_coeff_zero_ne`.
- **Hypotheses**: as above.
- **Uses from project**: to_qExpansion_coeff_zero_ne, to_qExpansion, poleOrder
- **Used by**: unused in file; 0 external
- **Visibility**: public
- **Lines**: 538–543, proof ≈ 3 lines
- **Notes**: junk candidate.

### `lemma laurentqExpansion.ne_zero`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero) (h0 : poleOrder h f ≠ 0) : laurentqExpansion h f ≠ 0`
- **What**: the Laurent expansion is nonzero when there is a pole.
- **How**: `HahnSeries.ne_zero_of_coeff_ne_zero` (HahnSeries/Basic.lean:126) at `−poleOrder` via `coeff_neg_poleOrder` and `to_qExpansion_coeff_zero_ne`.
- **Hypotheses**: as above.
- **Uses from project**: coeff_neg_poleOrder, to_qExpansion_coeff_zero_ne, laurentqExpansion, poleOrder
- **Used by**: poleOrder_to_order
- **Visibility**: public
- **Lines**: 545–550, proof ≈ 3 lines
- **Notes**: 0 external; SHORT collision (`ne_zero`).

### `lemma laurentqExpansion.poleOrder_to_order`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero) (h0 : poleOrder h f ≠ 0) : poleOrder h f = -(laurentqExpansion h f).order`
- **What**: the pole order is minus the `HahnSeries.order` of the Laurent expansion.
- **How**: `HahnSeries.order_le_of_coeff_ne_zero` (Basic.lean:383) at `−poleOrder` (nonzero by `to_qExpansion_coeff_zero_ne`), and `≥` by `HahnSeries.coeff_order_eq_zero` (:374) + `coeff_eq_zero_of_lt` + `laurentqExpansion.ne_zero`; `le_antisymm`; negate.
- **Hypotheses**: cusp-meromorphic; `poleOrder ≠ 0`.
- **Uses from project**: coeff_neg_poleOrder, to_qExpansion_coeff_zero_ne, coeff_eq_zero_of_lt, laurentqExpansion.ne_zero, laurentqExpansion, poleOrder
- **Used by**: to_qExpansion_eq_powerSeriesPart; externally DiagonalLaurent.lean, IntegralDescent.lean
- **Visibility**: public
- **Lines**: 552–569, proof ≈ 16 lines
- **Notes**: no docstring. The statement `(poleOrder : ℤ) = -order` is awkward — the usable form `order = -poleOrder` is proved inline at L567 and immediately re-negated (and `to_qExpansion_eq_powerSeriesPart` un-negates it again at L576–579). Mathlib route: `HahnSeries.order_single_mul_of_isRegular` (Multiplication.lean:580) + `HahnSeries.order_single` (Basic.lean:389) + order `0` of `ofPowerSeries F` with `F.coeff 0 ≠ 0` gives `order = −poleOrder + 0` in a few lines.

### `lemma laurentqExpansion.to_qExpansion_eq_powerSeriesPart`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero) (h0 : poleOrder h f ≠ 0) : to_qExpansion h f = (laurentqExpansion h f).powerSeriesPart`
- **What**: the regular part is mathlib's `LaurentSeries.powerSeriesPart` of the expansion.
- **How**: `ext`; `LaurentSeries.powerSeriesPart_coeff` (LaurentSeries.lean:215); `poleOrder_to_order` (negated back); `coeff_neg_poleOrder_add`.
- **Hypotheses**: as above.
- **Uses from project**: poleOrder_to_order, coeff_neg_poleOrder_add, to_qExpansion, laurentqExpansion, poleOrder
- **Used by**: unused in file; 0 external
- **Visibility**: public
- **Lines**: 571–581, proof ≈ 9 lines
- **Notes**: junk candidate in its current form, but it is the mathlib-native statement: with `order = −poleOrder` it follows from `LaurentSeries.single_order_mul_powerSeriesPart` (:237) by cancelling `single a 1` (a unit). Fails for `poleOrder = 0` only because `to_qExpansion` is then not normalised (see `to_qExpansion` notes).

### `lemma laurentqExpansion.eq_qExpansion_iff`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero) : laurentqExpansion h f = ↑(qExpansion h f) ↔ poleOrder h f = 0`
- **What**: the Laurent expansion is the (coerced) ordinary q-expansion iff there is no pole.
- **How**: `→`: if `poleOrder ≠ 0`, the coefficient at `−poleOrder` is nonzero on the left (`coeff_neg_poleOrder`, `to_qExpansion_coeff_zero_ne`) but zero on the right (`PowerSeries.coeff_coe`, negative index); `←`: `poleRemoved h f = f` and `simp`.
- **Hypotheses**: cusp-meromorphic.
- **Uses from project**: to_qExpansion_coeff_zero_ne, coeff_neg_poleOrder, poleRemoved, to_qExpansion, laurentqExpansion, poleOrder
- **Used by**: unused in file; externally Algebra.lean (`laurentqExpansion_const`)
- **Visibility**: public
- **Lines**: 584–597, proof ≈ 11 lines
- **Notes**: no docstring; the `←` direction with hypothesis `AnalyticAt` (`laurentqExpansion_eq_coe_qExpansion_of_analyticAt`) is what users want and requires composing with `analyticAt_cuspFunction_iff_poleOrder_eq_zero`. Double blank lines at L582–583, 598–599.

### `lemma qExpansion_coeff_eq_circleIntegral_of_differentiableOn`
- **Type**: `{g : ℍ → ℂ} {R : ℝ} (hR : 0 < R) (hDiff : DifferentiableOn ℂ (cuspFunction h g) (Metric.closedBall 0 R)) (n : ℕ) : (qExpansion h g).coeff n = (2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h g z / z ^ (n + 1)` (section variable `h`)
- **What**: Cauchy formula for q-expansion coefficients under a bare `DifferentiableOn`-on-a-closed-disc hypothesis.
- **How**: `DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul` (Analysis/Complex/CauchyIntegral.lean:717–740 family), then the same `rw`/`simp_rw` chain as mathlib.
- **Hypotheses**: `0 < R`; cusp function differentiable on the closed disc.
- **Uses from project**: []
- **Used by**: laurentqExpansion_coeff_eq_circleIntegral
- **Visibility**: public
- **Lines**: 600–609, proof ≈ 6 lines
- **Notes**: verbatim copy of mathlib `UpperHalfPlane.qExpansion_coeff_eq_circleIntegral` (QExpansion.lean:279–288; lines 605–609 here = 283–288 there) with the `Periodic/MDiff/IsBoundedAtImInfty` hypotheses replaced by the weaker `DifferentiableOn` — a mathlib refactor candidate (generalise the mathlib lemma). 0 external; no docstring.

### `lemma exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero) : ∃ R : ℝ, 0 < R ∧ R < 1 ∧ DifferentiableOn ℂ (cuspFunction h (poleRemoved h f)) (Metric.closedBall 0 R)`
- **What**: there is a closed disc of radius `< 1` on which the pole-removed cusp function is holomorphic.
- **How**: `AnalyticAt.exists_ball_analyticOnNhd` (Analytic/ChangeOrigin.lean:386) from `analyticAt_cuspFunction_poleRemoved`; take `R := min (R0/2) (1/2)`; `Metric.closedBall_subset_ball`.
- **Hypotheses**: cusp-meromorphic.
- **Uses from project**: analyticAt_cuspFunction_poleRemoved, poleRemoved
- **Used by**: laurentqExpansion_coeff_eq_circleIntegral
- **Visibility**: public
- **Lines**: 613–631, proof ≈ 16 lines
- **Notes**: garbled name (`…_to_analyticAt`); the `min`/`linarith` fiddling (L618–629, 12 lines) is a generic "shrink the radius below 1"; 0 external.

### `private lemma cuspFunction_poleRemoved_div_zpow_eq_of_mem_sphere`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero) {R : ℝ} (hRpos : 0 < R) (hRlt1 : R < 1) {z : ℂ} (hz : z ∈ Metric.sphere 0 R) (a : ℤ) : cuspFunction h (poleRemoved h f) z / z ^ a = cuspFunction h f z / z ^ (a - poleOrder h f)`
- **What**: on a circle of radius `< 1`, dividing the pole-removed cusp function by `z^a` equals dividing the original by `z^{a − poleOrder}`.
- **How**: `cuspFunction_poleRemoved_eq`, `zpow_sub₀`, `div_div_eq_mul_div`, `ring`.
- **Hypotheses**: as stated.
- **Uses from project**: cuspFunction_poleRemoved_eq, poleRemoved, poleOrder
- **Used by**: circleIntegral_cuspFunction_div_zpow_eq_zero, circleIntegral_cuspFunction_poleRemoved_div_pow_eq
- **Visibility**: private
- **Lines**: 635–648, proof ≈ 9 lines
- **Notes**: none.

### `private lemma circleIntegral_cuspFunction_div_zpow_eq_zero`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero) {R} (hRpos) (hRlt1) (hDiff : DifferentiableOn ℂ (cuspFunction h (poleRemoved h f)) (Metric.closedBall 0 R)) {n : ℤ} (hn : n < -(poleOrder h f : ℤ)) : (∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1)) = 0`
- **What**: below the principal-part cutoff the contour integral vanishes (the integrand extends holomorphically over the disc).
- **How**: on the sphere the integrand equals `z^k · cuspFunction h (poleRemoved)` with `k = −(n + poleOrder + 1) ∈ ℕ` (`Int.toNat_of_nonneg`, the sphere lemma, `zpow_neg`); `circleIntegral.integral_congr` (MeasureTheory/Integral/CircleIntegral.lean:425); `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable` (CauchyIntegral.lean:441) with `countable_empty`.
- **Hypotheses**: as stated.
- **Uses from project**: cuspFunction_poleRemoved_div_zpow_eq_of_mem_sphere, poleRemoved, poleOrder
- **Used by**: laurentqExpansion_coeff_eq_circleIntegral
- **Visibility**: private
- **Lines**: 652–673, proof ≈ 18 lines
- **Notes**: none.

### `private lemma circleIntegral_cuspFunction_poleRemoved_div_pow_eq`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero) {R} (hRpos) (hRlt1) {m : ℕ} {n : ℤ} (hm : (m : ℤ) = n + poleOrder h f) : (∮ z in C(0, R), cuspFunction h (poleRemoved h f) z / z ^ (m + 1)) = ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1)`
- **What**: above the cutoff, the two contour integrals agree after the exponent shift.
- **How**: `circleIntegral.integral_congr` + the sphere lemma at `a = m + 1`.
- **Hypotheses**: as stated.
- **Uses from project**: cuspFunction_poleRemoved_div_zpow_eq_of_mem_sphere, poleRemoved, poleOrder
- **Used by**: laurentqExpansion_coeff_eq_circleIntegral
- **Visibility**: private
- **Lines**: 677–687, proof ≈ 7 lines
- **Notes**: none.

### `lemma laurentqExpansion_coeff_eq_circleIntegral`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) : ∃ R : ℝ, 0 < R ∧ R < 1 ∧ ∀ n : ℤ, (laurentqExpansion h f).coeff n = (2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1)`
- **What**: **Cauchy formula for Laurent coefficients**: on some circle every integer-indexed coefficient is the standard contour integral.
- **How**: choose `R` by `exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt`; for `n < −poleOrder` both sides vanish (`coeff_eq_zero_of_lt`, `circleIntegral_cuspFunction_div_zpow_eq_zero`); otherwise `coeff_of_geq`, unfold `to_qExpansion`, `qExpansion_coeff_eq_circleIntegral_of_differentiableOn`, and shift the exponent with `circleIntegral_cuspFunction_poleRemoved_div_pow_eq`.
- **Hypotheses**: cusp-meromorphic.
- **Uses from project**: exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt, coeff_eq_zero_of_lt, circleIntegral_cuspFunction_div_zpow_eq_zero, coeff_of_geq, to_qExpansion, qExpansion_coeff_eq_circleIntegral_of_differentiableOn, circleIntegral_cuspFunction_poleRemoved_div_pow_eq, laurentqExpansion, poleOrder
- **Used by**: unused in file; 0 external
- **Visibility**: public
- **Lines**: 691–706, proof ≈ 11 lines
- **Notes**: documented "main result" (module docstring L32–33) with no consumers; the `∃ R` form is forced by the purely local `MeromorphicAt` hypothesis (with `MDiff f`-type hypotheses as in mathlib's `qExpansion_coeff_eq_circleIntegral` it would hold for every `0 < R < 1`).

## File Summary
- Total declarations: 49 (4 defs, 45 lemmas — 7 private / 38 public, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `poleOrder` (≈25), `laurentqExpansion` (≈15), `to_qExpansion` (≈13), `poleRemoved` (≈12), `analyticAt_cuspFunction_of_eventuallyEq` (2 users, 4 sites), `analyticAt_cuspFunction_poleRemoved` (3), `to_qExpansion_coeff_zero_ne` (4), `cuspFunction_nat_mul_eq_cuspFunction_pow` (3), `laurentqExpansion.coeff_eq_HahnSeries_add` (3), `coeff_eq_zero_of_lt` (3), `coeff_of_geq` (3), `coeff_neg_poleOrder` (3)
- Unused declarations (not used by anything in this file): `meromorphicAt_cuspFunction_finset_sum` (ext 3), `meromorphicAt_cuspFunction_finset_prod` (ext 2), `meromorphicAt_cuspFunction_nat_mul` (ext 2), `meromorphicAt_cuspFunction_of_nat_mul` (ext 2), `poleOrder_nat_mul` (ext 4), `laurentqExpansion.coeff_of_qExpansion` (ext 1), `laurentqExpansion.coeff_zero` (ext 0), `to_qExpansion_ne_zero` (ext 0), `laurentqExpansion.to_qExpansion_eq_powerSeriesPart` (ext 0), `laurentqExpansion.eq_qExpansion_iff` (ext 1), `laurentqExpansion_coeff_eq_circleIntegral` (ext 0). Zero-external AND unused in-file: `coeff_zero`, `to_qExpansion_ne_zero`, `to_qExpansion_eq_powerSeriesPart`, `laurentqExpansion_coeff_eq_circleIntegral` (whose private/public helpers `qExpansion_coeff_eq_circleIntegral_of_differentiableOn`, `exists_pos_lt_one_…`, and 3 private lemmas are therefore also dead: L600–706, ≈107 lines)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `analyticAt_cuspFunction_poleRemoved` (≈43); `eventually_differentiableAt_pow_mul_of_meromorphicAt_comp_pow_aux` (≈30)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- No mathlib "Laurent expansion of a meromorphic germ" exists: `grep -rn -i laurent Mathlib/Analysis/{Meromorphic,Complex,Analytic}` hits only a comment (FactorizedRational.lean:295), and no file under `Mathlib/Analysis` or `Mathlib/NumberTheory/ModularForms` imports `LaurentSeries`/`HahnSeries`. Mathlib's vocabulary for the same content: `meromorphicOrderAt` (Meromorphic/Order.lean:47), `meromorphicOrderAt_eq_int_iff` (:94), `meromorphicOrderAt_eq_top_iff` (:64), `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt` (Basic.lean:359), `meromorphicTrailingCoeffAt` (TrailingCoefficient.lean:36) with `AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE` (:64) and `MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero` (:143), `MeromorphicNFAt`/`toMeromorphicNFAt` (NormalForm.lean:47/377). `analyticAt_cuspFunction_poleRemoved` (L374–417) and `to_qExpansion_coeff_zero_ne` (L515–536) are exactly these lemmas transported along `cuspFunction`; a mathlib-level `MeromorphicAt.laurentSeries` built from `meromorphicOrderAt` + `AnalyticAt.hasFPowerSeriesAt` would subsume `poleOrder`/`to_qExpansion`/`laurentqExpansion`.
- `poleOrder` (L236) duplicates arithmetic on `meromorphicOrderAt`: lemmas L243–273 and L496–513 are `WithTop ℤ`/`Int.toNat` bookkeeping; defining `poleOrder h f := (-(meromorphicOrderAt (cuspFunction h f) 0)).untop₀.toNat` (the closed form of L261) removes `poleOrder_eq_of_meromorphicOrderAt_eq`, `poleOrder_eq_zero_of_meromorphicOrderAt_nonneg`, `poleOrder_eq_toNat_neg_meromorphicOrderAt`.
- `laurentqExpansion` (L326) vs `LaurentSeries.powerSeriesPart`/`single_order_mul_powerSeriesPart`/`ofPowerSeries_powerSeriesPart` (LaurentSeries.lean:211, 237, 252): `laurentqExpansion.poleOrder_to_order` (L552) and `to_qExpansion_eq_powerSeriesPart` (L571) are the statements "`order = −poleOrder`, `powerSeriesPart = to_qExpansion`"; via `HahnSeries.order_single_mul_of_isRegular` (Multiplication.lean:580) + `HahnSeries.order_single` (Basic.lean:389) both collapse to a few lines once `(to_qExpansion h f).coeff 0 ≠ 0` (L515) is known. The coefficient lemmas L447–494 are instances of `HahnSeries.coeff_single_mul` (Multiplication.lean:471) + `PowerSeries.coeff_coe` (LaurentSeries.lean:335).
- `HahnSeries.ofPowerSeries ℤ ℂ` (L327, 449) vs mathlib's coercion `↑(f : PowerSeries ℂ) : LaurentSeries ℂ` (`coeToLaurentSeries`, LaurentSeries.lean:374) — switching unlocks the `LaurentSeries.coe_*` simp set (`coe_C` :346, `coe_X` :349, `coe_mul` :332, `coe_pow` :359, `coe_smul` :353, `coeff_coe` :335); the file already uses `PowerSeries.coeff_coe` (stated for the coercion) at L463/473/591, so the two spellings are being unified by `simp` on the fly.
- `meromorphicAt_cuspFunction_add/mul/const/finset_sum/finset_prod` (L99–143) = `MeromorphicAt.add/mul/const/sum/prod` (Basic.lean:74/98/68/138/109) + `congr`; all five (and the missing `neg/sub/smul/pow/zpow/inv/div`) follow from ONE transport lemma `cuspFunction h f =ᶠ[𝓝[≠] 0] f ∘ ofComplex ∘ invQParam h` (which is `Periodic.cuspFunction_eq_of_nonzero`, Periodic.lean:119, as a `Filter.EventuallyEq`).
- `cuspFunction_add/mul_eventuallyEq` (L68–88): hypothesis-free `𝓝[≠]` versions of mathlib `UpperHalfPlane.cuspFunction_add/mul` (QExpansion.lean:456/440, which need `ContinuousAt`) — mathlib gap.
- `cuspFunction_nat_mul_eq_cuspFunction_pow` (L46): no mathlib analogue (searched Periodic.lean/QExpansion.lean/UpperHalfPlane/Exp.lean for `nat_mul`, `qParam_mul`, `mul_qParam`); upstream `Function.Periodic.cuspFunction_nat_mul`.
- `meromorphicAt_of_comp_pow` (L194–220) + aux (L161–191): mathlib only has `meromorphicAt_comp_iff_of_deriv_ne_zero` (Basic.lean:458) and `MeromorphicAt.comp_analyticAt` (:438); descent along `z ↦ z^m` at `0` is absent — upstream candidate `meromorphicAt_comp_pow_iff`.
- `qExpansion_coeff_eq_circleIntegral_of_differentiableOn` (L600–609) is a verbatim copy of mathlib `qExpansion_coeff_eq_circleIntegral` (QExpansion.lean:279–288) with weaker hypotheses — refactor mathlib's lemma to take `DifferentiableOn … (closedBall 0 R)`.
- `cuspFunction_apply_zero_eq` (L340) generalises mathlib `Periodic.cuspFunction_zero_of_zero_at_inf` (Periodic.lean:198) / `UpperHalfPlane.cuspFunction_apply_zero` (QExpansion.lean:107): upstream `Periodic.cuspFunction_apply_zero_of_eventuallyEq`.
- `horderPow` (L287–290): `analyticOrderAt (fun q ↦ q ^ m) 0 = m` — worth a mathlib simp lemma (`analyticOrderAt_pow_id`?) next to `analyticOrderAt_id` (Analytic/Order.lean:186).
### Missing API / repeated patterns
- `poleRemoved h f = f` from `poleOrder h f = 0`: inline `funext τ; simp [UpperHalfPlane.poleRemoved, h0]` at L426–428, L442–444, L594–596 → `poleRemoved_of_poleOrder_eq_zero`.
- Punctured-unit-disc filter: `filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℂ) zero_lt_one), self_mem_nhdsWithin] with q hqnorm hq` + `Set.mem_compl_singleton_iff.mp hq` + `mem_ball_zero_iff.mp hqnorm` at L363–364, L380–384, L523–526 (and Algebra.lean's private `norm_lt_one_mem_nhdsNE_zero` L34) → one lemma `eventually_nhdsNE_zero_ne_zero_and_norm_lt_one`.
- `cuspFunction_*_eventuallyEq` 3× identical skeleton (L68–96); `finset_sum`/`finset_prod` induction pair (L118–143) duplicated again in Algebra.lean L250–281.
- `hEq_shift` in `analyticAt_cuspFunction_poleRemoved` (L378–384) re-proves `cuspFunction_poleRemoved_eq` (L432) which is stated later; reorder and reuse.
- `poleOrder_eq_of_meromorphicOrderAt_eq` (L243) / `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` (L496) are the two directions of `poleOrder h f = r ↔ meromorphicOrderAt … = -r` (for `r ≠ 0`) proved with duplicated `unfold`/`cases` skeletons.
- No `@[simp]` attribute anywhere in the file (0 occurrences); expected: `poleRemoved_apply`, `laurentqExpansion.coeff_neg_poleOrder_add`, `coeff_of_qExpansion` (as `laurentqExpansion_coeff`), `poleOrder_const/zero/one`, `to_qExpansion` unfolding.
- `poleOrder` lacks `poleOrder_add_le`, `poleOrder_mul` (from `meromorphicOrderAt_mul`, Order.lean:429), `poleOrder_pow`, `poleOrder_neg` (Order.lean:388), `poleOrder_smul`, `poleOrder_of_analyticAt` (the `.1` direction of L420 as a standalone), `poleOrder_const = 0`; Algebra.lean's ad-hoc common shifts (`N := poleOrder f + poleOrder g + poleOrder (f+g)`, Algebra.lean:170, 203) exist because of this.
- `laurentqExpansion` lacks `laurentqExpansion_eq_coe_qExpansion_of_analyticAt` (users must chain L420 and L584), `laurentqExpansion_congr`, `laurentqExpansion_smul/pow/sub/inv`, `laurentqExpansion_qParam_pow = single n 1`, and an `order`-form `laurentqExpansion_order : (laurentqExpansion h f).order = -poleOrder h f` (the sign-flipped L552 that L567 and L578 both re-derive).
- `meromorphicAt_cuspFunction_nat_mul` (L147) + `_of_nat_mul` (L224) → `meromorphicAt_cuspFunction_nat_mul_iff`.
- Naming: `to_qExpansion` (snake_case def), `coeff_of_geq`, `coeff_eq_HahnSeries_add`, `poleOrder_to_order`, `exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt`, `laurentqExpansion.*` in root namespace `laurentqExpansion` (not `UpperHalfPlane.laurentqExpansion`, so `(laurentqExpansion h f).coeff_of_geq` cannot work); `laurentqExpansion.coeff_eq_zero_of_lt`/`coeff_zero`/`ne_zero` flagged SHORT collisions in `_mathlib-collisions.tsv`.
- Missing docstrings: L275, 300, 330, 359, 374, 420, 432, 447–494 (all coeff lemmas), 496, 515, 538, 545, 552, 571, 584, 600.
### Junk candidates
- `laurentqExpansion.coeff_zero` (L490–494), `to_qExpansion_ne_zero` (L538–543), `laurentqExpansion.to_qExpansion_eq_powerSeriesPart` (L571–581): 0 users anywhere.
- Circle-integral subtree L600–706 (`qExpansion_coeff_eq_circleIntegral_of_differentiableOn`, `exists_pos_lt_one_…`, three privates, `laurentqExpansion_coeff_eq_circleIntegral`): 0 users anywhere (≈107 lines); listed as a main result in the module docstring (L32–33).
- `analyticAt_cuspFunction_of_not_pos` (L359–372) and the `h ≤ 0` branches of L374–417, L432–445: junk-value plumbing so that two lemmas do not need `0 < h`, which every consumer supplies anyway.
- `variable {h : ℝ}` (L44): used by exactly one declaration (L600); all others rebind `{h : ℝ}`.
- `m = 0` is permitted in `cuspFunction_nat_mul_eq_cuspFunction_pow` (L46): the `0 * h` statement is junk-true.
- Double blank lines L582–583, L598–599.
### Moral duplicates within this batch
- `cuspFunction_const_eventuallyEq` (L90) vs Algebra.lean `cuspFunction_const` (L40): same fact, `𝓝[≠]` vs global.
- `meromorphicAt_cuspFunction_finset_sum/prod` (L118–143) vs Algebra.lean `laurentqExpansion_finset_sum/prod` (L250–281): identical induction skeleton.
- `hEq_shift` (L378–384) vs `cuspFunction_poleRemoved_eq` (L432–445, `0 < h` branch) vs Algebra.lean `cuspFunction_qpow_mul_eventuallyEq` (L55–67): three derivations of "`cuspFunction (q^n f) = q^n cuspFunction f` near `0`" from `cuspFunction_qpow_mul_eq`.
- `poleOrder_eq_of_meromorphicOrderAt_eq` (L243) vs `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` (L496): converse pair with duplicated skeleton.
- `qExpansion_coeff_eq_circleIntegral_of_differentiableOn` (L600) vs mathlib `qExpansion_coeff_eq_circleIntegral` (QExpansion.lean:279).
- `laurentqExpansion` (L326) vs Algebra.lean `shiftedLaurent` (L108): same term with `poleOrder` vs free `N`.
### Generalization notes
- `cuspFunction_apply_zero_eq` (L340), `analyticAt_cuspFunction_of_eventuallyEq` (L353): use only `Periodic.cuspFunction_zero_eq_limUnder_nhds_ne` and the `update` definition (Periodic.lean:116); they hold for `Function.Periodic.cuspFunction h F` with arbitrary `F : ℂ → ℂ` and should be stated there.
- `meromorphicAt_of_comp_pow` and its aux (L161–220) are `ℂ`-specific (open mapping `Complex.isOpenQuotientMap_pow`, removable singularities) — the right generality; nothing cusp-specific, so they belong in a general complex-analysis file.
- `laurentqExpansion.coeff_*` (L447–494): pure HahnSeries bookkeeping about `single (-N) 1 * ofPowerSeries ℤ R F` for any semiring `R`, `N : ℕ`, `F : PowerSeries R`; state once generically and instantiate.
- `poleOrder_eq_*` (L243–273), `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` (L496–513): generic in the function; they are lemmas about `fun o : WithTop ℤ ↦ if o < 0 then natAbs (o.untopD 0) else 0`.
- `cuspFunction_qpow_mul_eq` (L330) needs `0 < h` only to land in `ℍ`; with `Periodic.cuspFunction` on `ℂ → ℂ` (no `ofComplex`) it holds for all `h ≠ 0`.
- `meromorphicOrderAt_cuspFunction_nat_mul` (L275) is stated for `m : ℕ` but `MeromorphicAt.meromorphicOrderAt_comp` works for any analytic non-constant `g`; the `q ↦ q^m` specialisation is the only use.
