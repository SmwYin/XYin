/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.LaurentQExpansion.LaurentQExpansion
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Algebra of Laurent q-expansions

This file proves that the analytic Laurent q-expansion respects finite sums and products of
cusp-meromorphic functions. It also compares the coefficients obtained from a period `h` with
those obtained from the enlarged period `m * h`.

## Main results

* `laurentqExpansion_add`, `laurentqExpansion_mul`: the Laurent q-expansion respects pointwise
  addition and multiplication of cusp-meromorphic functions; together with
  `laurentqExpansion_zero`, `laurentqExpansion_one`, `laurentqExpansion_const`,
  `laurentqExpansion_neg`, `laurentqExpansion_finset_sum` and `laurentqExpansion_finset_prod`
  it behaves like a ring homomorphism.
* `to_qExpansion_nat_mul`, `laurentqExpansion_nat_mul_coeff`,
  `laurentqExpansion_nat_mul_coeff_of_not_dvd`: enlarging the period from `h` to `m * h`
  substitutes `q ↦ q ^ m` in the expansion.
-/

open Complex Function Filter LaurentSeries ModularForm Set UpperHalfPlane

noncomputable section

local notation "𝕢" => Periodic.qParam

private lemma norm_lt_one_mem_nhdsNE_zero :
    {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
  nhdsWithin_le_nhds (by
    simpa [Metric.ball, dist_eq_norm] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

/-- The cusp function of a constant function is the constant function. -/
private lemma cuspFunction_const (h : ℝ) (a : ℂ) :
    cuspFunction h (fun _ : ℍ ↦ a) = fun _ : ℂ ↦ a := by
  ext q
  rcases eq_or_ne q 0 with rfl | hq
  · simpa [UpperHalfPlane.cuspFunction, Periodic.cuspFunction] using
      tendsto_const_nhds.limUnder_eq
  · simp [UpperHalfPlane.cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ hq]

private lemma analyticAt_cuspFunction_const (h : ℝ) (a : ℂ) :
    AnalyticAt ℂ (cuspFunction h (fun _ : ℍ ↦ a)) 0 := by
  rw [cuspFunction_const]
  exact analyticAt_const

/-- Near `0`, the cusp function of `𝕢 h τ ^ n * f τ` is `q ^ n` times the cusp function
of `f`, provided the latter is analytic at `0`. -/
private lemma cuspFunction_qpow_mul_eventuallyEq
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) :
    cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ) =ᶠ[nhds (0 : ℂ)]
      fun q ↦ q ^ n * cuspFunction h f q := by
  have hEq : cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ) =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
      fun q ↦ q ^ n * cuspFunction h f q := by
    filter_upwards [norm_lt_one_mem_nhdsNE_zero, self_mem_nhdsWithin] with q hqnorm hq
    exact cuspFunction_qpow_mul_eq hh f (Set.mem_compl_singleton_iff.mp hq) hqnorm
  have hG : AnalyticAt ℂ (fun q : ℂ ↦ q ^ n * cuspFunction h f q) 0 := by
    simpa using (analyticAt_id.pow n).mul hf
  exact eventuallyEq_nhds_of_eventuallyEq_nhdsNE hEq
    (cuspFunction_apply_zero_eq hEq hG.continuousAt)

private lemma analyticAt_cuspFunction_qpow_mul
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) :
    AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ)) 0 :=
  ((analyticAt_id.pow n).mul hf).congr
    (cuspFunction_qpow_mul_eventuallyEq hh hf n).symm

/-- The q-expansion of `τ ↦ 𝕢 h τ ^ n` is the monomial `X ^ n`. -/
private lemma qExpansion_qParam_pow (h : ℝ) (hh : 0 < h) (n : ℕ) :
    qExpansion h (fun τ : ℍ ↦ (𝕢 h τ) ^ n) =
      (PowerSeries.X : PowerSeries ℂ) ^ n := by
  have hEq : cuspFunction h (fun τ : ℍ ↦ (𝕢 h τ) ^ n) =ᶠ[nhds 0]
      fun q : ℂ ↦ q ^ n := by
    simpa [cuspFunction_const] using
      cuspFunction_qpow_mul_eventuallyEq hh (analyticAt_cuspFunction_const h 1) n
  ext k
  rw [qExpansion_coeff, hEq.iteratedDeriv_eq k, iteratedDeriv_fun_pow_zero]
  by_cases hk : k = n
  · subst k
    have hn : (n.factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    simpa [PowerSeries.coeff_X_pow] using inv_mul_cancel₀ hn
  · simp [PowerSeries.coeff_X_pow, hk]

/-- Multiplying by `𝕢 h τ ^ n` on functions is multiplying by `X ^ n` on q-expansions. -/
private lemma qExpansion_qpow_mul {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) :
    qExpansion h (fun τ ↦ (𝕢 h τ) ^ n * f τ) =
      (PowerSeries.X : PowerSeries ℂ) ^ n * qExpansion h f := by
  have hpow : AnalyticAt ℂ (cuspFunction h (fun τ : ℍ ↦ (𝕢 h τ) ^ n)) 0 := by
    simpa using
      analyticAt_cuspFunction_qpow_mul hh (analyticAt_cuspFunction_const h 1) n
  simpa [qExpansion_qParam_pow h hh n] using
    (qExpansion_mul (h := h) (f := fun τ : ℍ ↦ (𝕢 h τ) ^ n) (g := f) hpow hf)

/-- The "shift by `N`" presentation of a Laurent expansion:
`q ^ (-N)` times the power series of `𝕢 h τ ^ N * f τ`. For any `N` at least the pole order
this recovers the Laurent q-expansion (`laurentqExpansion_eq_shiftedLaurent`), so sums and
products can be computed with one common denominator exponent. -/
private def shiftedLaurent (h : ℝ) (N : ℕ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-(N : ℤ)) 1 *
    (HahnSeries.ofPowerSeries ℤ ℂ)
      (qExpansion h (fun τ ↦ (𝕢 h τ) ^ N * f τ))

/-- For `N` at least the pole order, `𝕢 h τ ^ N * f τ` factors through the pole-removed
function. -/
private lemma qpow_mul_eq_qpow_sub_mul_poleRemoved {h : ℝ} {f : ℍ → ℂ} {N : ℕ}
    (hN : poleOrder h f ≤ N) :
    (fun τ : ℍ ↦ (𝕢 h τ) ^ N * f τ) =
      fun τ : ℍ ↦ (𝕢 h τ) ^ (N - poleOrder h f) * poleRemoved h f τ := by
  funext τ
  simp only [UpperHalfPlane.poleRemoved]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hN]

/-- The Laurent q-expansion is independent of the chosen denominator exponent: any
`N ≥ poleOrder h f` gives the same series via the shifted presentation. -/
private lemma laurentqExpansion_eq_shiftedLaurent
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) {N : ℕ}
    (hN : poleOrder h f ≤ N) :
    laurentqExpansion h f = shiftedLaurent h N f := by
  have hq : qExpansion h (fun τ : ℍ ↦ (𝕢 h τ) ^ N * f τ) =
      (PowerSeries.X : PowerSeries ℂ) ^ (N - poleOrder h f) * to_qExpansion h f := by
    rw [qpow_mul_eq_qpow_sub_mul_poleRemoved hN,
      qExpansion_qpow_mul hh (analyticAt_cuspFunction_poleRemoved (h := h) (f := f) hf)
        (N - poleOrder h f)]
    rfl
  rw [UpperHalfPlane.laurentqExpansion, shiftedLaurent, hq, map_mul,
    HahnSeries.ofPowerSeries_X_pow, ← mul_assoc, HahnSeries.single_mul_single, one_mul,
    show -(N : ℤ) + ((N - poleOrder h f : ℕ) : ℤ) = -(poleOrder h f : ℤ) by omega]

private lemma analyticAt_cuspFunction_qpow_of_poleOrder_le
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) {N : ℕ}
    (hN : poleOrder h f ≤ N) :
    AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ N * f τ)) 0 := by
  rw [qpow_mul_eq_qpow_sub_mul_poleRemoved hN]
  exact analyticAt_cuspFunction_qpow_mul hh
    (analyticAt_cuspFunction_poleRemoved (h := h) (f := f) hf) _

/-- The shifted presentation is additive at a common shift `N`. -/
private lemma shiftedLaurent_add {h : ℝ} {f g : ℍ → ℂ} {N : ℕ}
    (hfN : AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ N * f τ)) 0)
    (hgN : AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ N * g τ)) 0) :
    shiftedLaurent h N (fun τ ↦ f τ + g τ) =
      shiftedLaurent h N f + shiftedLaurent h N g := by
  have hfun : (fun τ : ℍ ↦ (𝕢 h τ) ^ N * (f τ + g τ)) =
      (fun τ : ℍ ↦ (𝕢 h τ) ^ N * f τ) + fun τ : ℍ ↦ (𝕢 h τ) ^ N * g τ := by
    funext τ
    dsimp only [Pi.add_apply]
    ring
  simp only [shiftedLaurent]
  rw [hfun, qExpansion_add hfN hgN, map_add, mul_add]

/-- Laurent q-expansion respects pointwise addition of cusp-meromorphic functions. -/
lemma laurentqExpansion_add
    {h : ℝ} (hh : 0 < h) {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentqExpansion h (fun τ ↦ f τ + g τ) =
      laurentqExpansion h f + laurentqExpansion h g := by
  -- rewrite all three expansions with a common shift dominating all three pole orders
  set N := poleOrder h f + poleOrder h g + poleOrder h (fun τ ↦ f τ + g τ) with hN
  have hfg := meromorphicAt_cuspFunction_add hf hg
  rw [laurentqExpansion_eq_shiftedLaurent hh hfg (N := N) (by omega),
    laurentqExpansion_eq_shiftedLaurent hh hf (N := N) (by omega),
    laurentqExpansion_eq_shiftedLaurent hh hg (N := N) (by omega)]
  exact shiftedLaurent_add
    (analyticAt_cuspFunction_qpow_of_poleOrder_le hh hf (by omega))
    (analyticAt_cuspFunction_qpow_of_poleOrder_le hh hg (by omega))

/-- The shifted presentation is multiplicative, with the shifts adding up. -/
private lemma shiftedLaurent_mul {h : ℝ} {f g : ℍ → ℂ} {A B : ℕ}
    (hfA : AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ A * f τ)) 0)
    (hgB : AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ B * g τ)) 0) :
    shiftedLaurent h (A + B) (fun τ ↦ f τ * g τ) =
      shiftedLaurent h A f * shiftedLaurent h B g := by
  have hfun : (fun τ : ℍ ↦ (𝕢 h τ) ^ (A + B) * (f τ * g τ)) =
      (fun τ : ℍ ↦ (𝕢 h τ) ^ A * f τ) * fun τ : ℍ ↦ (𝕢 h τ) ^ B * g τ := by
    funext τ
    dsimp only [Pi.mul_apply]
    rw [pow_add]
    ring
  simp only [shiftedLaurent]
  rw [hfun, qExpansion_mul hfA hgB, map_mul, mul_mul_mul_comm,
    HahnSeries.single_mul_single, one_mul,
    show -((A + B : ℕ) : ℤ) = -(A : ℤ) + -(B : ℤ) by omega]

/-- Laurent q-expansion respects pointwise multiplication of cusp-meromorphic functions. -/
lemma laurentqExpansion_mul
    {h : ℝ} (hh : 0 < h) {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentqExpansion h (fun τ ↦ f τ * g τ) =
      laurentqExpansion h f * laurentqExpansion h g := by
  -- split the total shift as `A + B` so that `A + B` also dominates the product's pole order
  set A := poleOrder h f + poleOrder h (fun τ ↦ f τ * g τ) with hA
  set B := poleOrder h g with hB
  have hfg := meromorphicAt_cuspFunction_mul hf hg
  rw [laurentqExpansion_eq_shiftedLaurent hh hfg (N := A + B) (by omega),
    laurentqExpansion_eq_shiftedLaurent hh hf (N := A) (by omega),
    laurentqExpansion_eq_shiftedLaurent hh hg (N := B) (by omega)]
  exact shiftedLaurent_mul
    (analyticAt_cuspFunction_qpow_of_poleOrder_le hh hf (by omega))
    (analyticAt_cuspFunction_qpow_of_poleOrder_le hh hg (by omega))

/-- The Laurent q-expansion of a constant function is the corresponding constant series. -/
@[simp] lemma laurentqExpansion_const (h : ℝ) (a : ℂ) :
    laurentqExpansion h (fun _ : ℍ ↦ a) = HahnSeries.C a := by
  have hmero := meromorphicAt_cuspFunction_const h a
  have hpole : poleOrder h (fun _ : ℍ ↦ a) = 0 :=
    (analyticAt_cuspFunction_iff_poleOrder_eq_zero hmero).1 (analyticAt_cuspFunction_const h a)
  have hq : qExpansion h (fun _ : ℍ ↦ a) = PowerSeries.C a := by
    calc
      qExpansion h (fun _ : ℍ ↦ a) = qExpansion h (a • (1 : ℍ → ℂ)) := by
        congr 1
        ext τ
        simp
      _ = a • qExpansion h (1 : ℍ → ℂ) :=
        qExpansion_smul (by
          simpa only [Pi.one_apply] using analyticAt_cuspFunction_const h 1) a
      _ = PowerSeries.C a := by
        rw [PowerSeries.smul_eq_C_mul, qExpansion_one, mul_one]
  rw [(laurentqExpansion.eq_qExpansion_iff hmero).2 hpole, hq, HahnSeries.ofPowerSeries_C]

/-- The Laurent q-expansion of the zero function is zero. -/
@[simp] lemma laurentqExpansion_zero (h : ℝ) :
    laurentqExpansion h (0 : ℍ → ℂ) = 0 := by
  rw [Pi.zero_def, laurentqExpansion_const, map_zero]

/-- The Laurent q-expansion of the constant-one function is one. -/
@[simp] lemma laurentqExpansion_one (h : ℝ) :
    laurentqExpansion h (1 : ℍ → ℂ) = 1 := by
  rw [Pi.one_def, laurentqExpansion_const, map_one]

/-- Laurent q-expansion respects pointwise negation. -/
lemma laurentqExpansion_neg
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    laurentqExpansion h (fun τ ↦ -f τ) = -laurentqExpansion h f := by
  have hconst := meromorphicAt_cuspFunction_const h (-1)
  have hmul := laurentqExpansion_mul hh hconst hf
  have hC : HahnSeries.C (-1 : ℂ) = (-1 : LaurentSeries ℂ) := by simp
  calc
    laurentqExpansion h (fun τ ↦ -f τ) =
        laurentqExpansion h (fun τ ↦ (-1 : ℂ) * f τ) := by congr 1; funext τ; ring
    _ = HahnSeries.C (-1 : ℂ) * laurentqExpansion h f := by
      simpa only [laurentqExpansion_const] using hmul
    _ = -laurentqExpansion h f := by rw [hC]; ring

/-- Laurent q-expansion commutes with a finite pointwise sum. -/
lemma laurentqExpansion_finset_sum
    {h : ℝ} (hh : 0 < h) {I : Type*} (s : Finset I) {f : I → ℍ → ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) :
    laurentqExpansion h (∑ i ∈ s, f i) =
      ∑ i ∈ s, laurentqExpansion h (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have ih' := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      exact (laurentqExpansion_add hh (hf a (Finset.mem_insert_self a s))
        (meromorphicAt_cuspFunction_finset_sum
          (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))).trans
        (congrArg (laurentqExpansion h (f a) + ·) ih')

/-- Laurent q-expansion commutes with a finite pointwise product. -/
lemma laurentqExpansion_finset_prod
    {h : ℝ} (hh : 0 < h) {I : Type*} (s : Finset I) {f : I → ℍ → ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) :
    laurentqExpansion h (∏ i ∈ s, f i) =
      ∏ i ∈ s, laurentqExpansion h (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ih' := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      exact (laurentqExpansion_mul hh (hf a (Finset.mem_insert_self a s))
        (meromorphicAt_cuspFunction_finset_prod
          (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))).trans
        (congrArg (laurentqExpansion h (f a) * ·) ih')

/-- The formal Taylor series `∑ (F⁽ⁿ⁾(0)/n!) Xⁿ` of a function at `0`; for cusp functions
this coincides definitionally with `qExpansion`. -/
private def analyticTaylor (F : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0

/-- If `F` agrees near `0` with `G ∘ (· ^ m)`, then `F` is represented at `0` by the `m`-fold
expansion of the Taylor series of `G`. -/
private lemma hasFPowerSeriesAt_expand_analyticTaylor {G : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0)
    (hG : AnalyticAt ℂ G 0) {F : ℂ → ℂ}
    (hEq : F =ᶠ[nhds (0 : ℂ)] G ∘ fun q : ℂ ↦ q ^ m) :
    HasFPowerSeriesAt F
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ ((analyticTaylor G).expand m hm).coeff n)) 0 := by
  obtain ⟨R, hR, hGR⟩ := hG.exists_ball_analyticOnNhd
  have hpow : Tendsto (fun q : ℂ ↦ q ^ m) (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt (fun q : ℂ ↦ q ^ m) 0 := by fun_prop
    simpa [hm] using hcont.tendsto
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [hpow (Metric.ball_mem_nhds (0 : ℂ) hR), hEq] with q hq hqEq
  -- reindex the Taylor sum of `G` at `q ^ m` along the injection `n ↦ m * n`
  have hbase' : HasSum
      (fun n ↦ (analyticTaylor G).coeff n • (q ^ m) ^ n) (G (q ^ m)) := by
    simpa [analyticTaylor, sub_zero, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      Complex.hasSum_taylorSeries_on_ball hGR.analyticOn.differentiableOn hq
  have hreindexed : HasSum
      ((fun n ↦ ((analyticTaylor G).expand m hm).coeff n • q ^ n) ∘ fun n ↦ m * n)
      (G (q ^ m)) := by
    apply hbase'.congr_fun
    intro n
    simp only [Function.comp_apply]
    rw [PowerSeries.coeff_expand_mul]
    simp [pow_mul]
  have hinj : Function.Injective fun n ↦ m * n := fun i j hij ↦
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) hij
  have hsum : HasSum
      (fun n ↦ ((analyticTaylor G).expand m hm).coeff n • q ^ n) (G (q ^ m)) := by
    apply (hinj.hasSum_iff ?_).mp hreindexed
    intro n hn
    have hnotdvd : ¬m ∣ n := by
      rintro ⟨k, rfl⟩
      exact hn ⟨k, rfl⟩
    simp [PowerSeries.coeff_expand, hnotdvd]
  simpa [FormalMultilinearSeries.coeff_ofScalars, hqEq, Function.comp_apply,
    smul_eq_mul, mul_comm] using hsum

/-- If `F(q) = G(q ^ m)` near `0`, the Taylor series of `F` is the `m`-fold expansion
(`X ↦ X ^ m` substitution) of the Taylor series of `G`. -/
private lemma analyticTaylor_comp_pow {F G : ℂ → ℂ} {m : ℕ}
    (hm : m ≠ 0) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (hEq : F =ᶠ[nhds (0 : ℂ)] G ∘ fun q : ℂ ↦ q ^ m) :
    analyticTaylor F = (analyticTaylor G).expand m hm := by
  have hpEq := (hasFPowerSeriesAt_expand_analyticTaylor hm hG hEq).eq_formalMultilinearSeries
    hF.hasFPowerSeriesAt
  ext n
  have hn := congrArg (fun p ↦ p.coeff n) hpEq
  simpa [analyticTaylor, FormalMultilinearSeries.coeff_ofScalars, div_eq_inv_mul]
    using hn.symm

/-- On a punctured neighbourhood of `0`, the pole-removed cusp function for the enlarged
period `m * h` is the pole-removed cusp function for period `h` composed with `q ↦ q ^ m`. -/
private lemma cuspFunction_poleRemoved_nat_mul_eventuallyEq {h : ℝ} {m : ℕ} (hm : m ≠ 0)
    {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    cuspFunction ((m : ℝ) * h) (poleRemoved ((m : ℝ) * h) f) =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
      (cuspFunction h (poleRemoved h f)) ∘ fun q : ℂ ↦ q ^ m := by
  have hmeroM := meromorphicAt_cuspFunction_nat_mul hm hmero hfper
  filter_upwards [norm_lt_one_mem_nhdsNE_zero, self_mem_nhdsWithin] with q hqnorm hq
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
  have hqpowNorm : ‖q ^ m‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hqnorm hm
  calc
    cuspFunction ((m : ℝ) * h) (poleRemoved ((m : ℝ) * h) f) q
        = q ^ poleOrder ((m : ℝ) * h) f * cuspFunction ((m : ℝ) * h) f q :=
      cuspFunction_poleRemoved_eq hmeroM hq0 hqnorm
    _ = (q ^ m) ^ poleOrder h f * cuspFunction h f (q ^ m) := by
      rw [poleOrder_nat_mul hm hmero hfper,
        cuspFunction_nat_mul_eq_cuspFunction_pow (m := m) hfper hq0, pow_mul]
    _ = cuspFunction h (poleRemoved h f) (q ^ m) :=
      (cuspFunction_poleRemoved_eq hmero (pow_ne_zero _ hq0) hqpowNorm).symm

/-- Enlarging a period by `m` expands the pole-removed q-expansion by `X ↦ X^m`. -/
lemma to_qExpansion_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    to_qExpansion ((m : ℝ) * h) f = (to_qExpansion h f).expand m hm := by
  have hFan : AnalyticAt ℂ (cuspFunction ((m : ℝ) * h) (poleRemoved ((m : ℝ) * h) f)) 0 :=
    analyticAt_cuspFunction_poleRemoved (meromorphicAt_cuspFunction_nat_mul hm hmero hfper)
  have hGan : AnalyticAt ℂ (cuspFunction h (poleRemoved h f)) 0 :=
    analyticAt_cuspFunction_poleRemoved hmero
  have hGcomp : AnalyticAt ℂ ((cuspFunction h (poleRemoved h f)) ∘ fun q : ℂ ↦ q ^ m) 0 := by
    have hpow : AnalyticAt ℂ (fun q : ℂ ↦ q ^ m) 0 := by fun_prop
    have hGan0 : AnalyticAt ℂ (cuspFunction h (poleRemoved h f))
        ((fun q : ℂ ↦ q ^ m) 0) := by
      simpa [hm] using hGan
    exact AnalyticAt.comp (𝕜 := ℂ) (g := cuspFunction h (poleRemoved h f))
      (f := fun q : ℂ ↦ q ^ m) (x := 0) hGan0 hpow
  have hEq := (hFan.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hGcomp.continuousAt).mp (cuspFunction_poleRemoved_nat_mul_eventuallyEq hm hmero hfper)
  simpa [analyticTaylor, UpperHalfPlane.to_qExpansion, UpperHalfPlane.qExpansion] using
    analyticTaylor_comp_pow hm hFan hGan hEq

/-- The coefficient at `m * k` for period `m * h` is the coefficient at `k` for period `h`. -/
lemma laurentqExpansion_nat_mul_coeff {h : ℝ} {m : ℕ} (hm : m ≠ 0)
    {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) (k : ℤ) :
    (laurentqExpansion ((m : ℝ) * h) f).coeff ((m : ℤ) * k) =
      (laurentqExpansion h f).coeff k := by
  have hpole := poleOrder_nat_mul hm hmero hfper
  have hmpos : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  by_cases hk : k < -(poleOrder h f : ℤ)
  · have hkM : (m : ℤ) * k < -(poleOrder ((m : ℝ) * h) f : ℤ) := by
      rw [hpole]
      push_cast
      simpa [mul_neg] using Int.mul_lt_mul_of_pos_left hk hmpos
    rw [laurentqExpansion.coeff_eq_zero_of_lt hkM,
      laurentqExpansion.coeff_eq_zero_of_lt hk]
  · have hkge : -(poleOrder h f : ℤ) ≤ k := le_of_not_gt hk
    have hkMge : -(poleOrder ((m : ℝ) * h) f : ℤ) ≤ (m : ℤ) * k := by
      rw [hpole]
      push_cast
      simpa [mul_neg] using Int.mul_le_mul_of_nonneg_left hkge hmpos.le
    rw [laurentqExpansion.coeff_of_geq hkMge,
      laurentqExpansion.coeff_of_geq hkge, to_qExpansion_nat_mul hm hmero hfper]
    have hsum : 0 ≤ k + (poleOrder h f : ℤ) := by linarith
    have hnat : Int.toNat ((m : ℤ) * k + poleOrder ((m : ℝ) * h) f) =
        m * Int.toNat (k + poleOrder h f) := by
      rw [hpole,
        show (m : ℤ) * k + ((m * poleOrder h f : ℕ) : ℤ) =
          (m : ℤ) * (k + poleOrder h f) by push_cast; ring,
        Int.toNat_mul (by exact_mod_cast Nat.zero_le m) hsum]
      simp
    rw [hnat, PowerSeries.coeff_expand_mul]

/-- A Laurent coefficient at an enlarged period vanishes unless its exponent is divisible by
the enlargement factor. -/
lemma laurentqExpansion_nat_mul_coeff_of_not_dvd
    {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) {k : ℤ}
    (hk : ¬(m : ℤ) ∣ k) :
    (laurentqExpansion ((m : ℝ) * h) f).coeff k = 0 := by
  have hpole := poleOrder_nat_mul hm hmero hfper
  by_cases hlt : k < -(poleOrder ((m : ℝ) * h) f : ℤ)
  · exact laurentqExpansion.coeff_eq_zero_of_lt hlt
  · have hge : -(poleOrder ((m : ℝ) * h) f : ℤ) ≤ k := le_of_not_gt hlt
    rw [laurentqExpansion.coeff_of_geq hge,
      to_qExpansion_nat_mul hm hmero hfper]
    apply PowerSeries.coeff_expand_of_not_dvd
    intro hdvd
    apply hk
    obtain ⟨a, ha⟩ := hdvd
    have hnonneg : 0 ≤ k + (poleOrder ((m : ℝ) * h) f : ℤ) := by omega
    have hcast : ((k + (poleOrder ((m : ℝ) * h) f : ℤ)).toNat : ℤ) = (m : ℤ) * a := by
      exact_mod_cast ha
    rw [Int.toNat_of_nonneg hnonneg, hpole] at hcast
    push_cast at hcast
    refine ⟨(a : ℤ) - poleOrder h f, ?_⟩
    linear_combination hcast
