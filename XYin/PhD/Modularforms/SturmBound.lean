/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# The Sturm bound for arithmetic subgroups

We prove the Sturm bound for modular forms whose level is an arithmetic subgroup `Γ` of
`GL(2, ℝ)`, by taking the norm `ModularForm.norm` down to level one and applying the level-one
Sturm bound `ModularForm.sturm_bound_levelOne`. As a consequence, spaces of modular forms for
arithmetic subgroups (e.g. for finite-index subgroups of `SL(2, ℤ)`) are finite-dimensional.

The comparison between the two levels goes through the growth at `∞`: a `q`-expansion in
`q_h = exp (2πiτ / h)` vanishing to order `n` means `f τ = O(exp (-2π n im τ / h))`, the norm of
`f` is `f` times finitely many translates of `f` which are bounded at `∞`, and a level-one form
which is `O(exp (-2π r im τ))` has `q`-expansion vanishing to order at least `r`.

## Main results

* `UpperHalfPlane.exp_decay_atImInfty_of_coeff_eq_zero`: if the first `n` coefficients of the
  `q`-expansion of `f` with respect to the period `h` vanish, then
  `f τ = O(exp (-2π n im τ / h))` as `im τ → ∞`.
* `UpperHalfPlane.qExpansion_coeff_eq_zero_of_exp_decay`: conversely, if
  `f τ = O(exp (-2π r im τ / h))` as `im τ → ∞`, then the `q`-expansion coefficients of `f` of
  index `j < r` vanish.
* `ModularForm.coe_norm_isBigO`: the norm of `f` down to `ℋ` is `O(f)` as `im τ → ∞`.
* `ModularForm.sturm_bound`: **Sturm bound**. Let `f` be a modular form of weight `k` for an
  arithmetic subgroup `Γ`, let `h > 0` be a strict period of `Γ`, and let `d` be the index of
  `Γ ⊓ SL(2, ℤ)` in `SL(2, ℤ)`. If the `q`-expansion of `f` in `q_h` vanishes to order
  `n > h * ⌊k * d / 12⌋`, then `f = 0`.
* `ModularForm.sturm_bound_of_finiteIndex`: the same for finite-index subgroups `Γ` of `SL(2, ℤ)`,
  where `d` is the index of `Γ`.
* `ModularForm.instFiniteDimensional`: `ModularForm Γ k` is finite-dimensional for every
  arithmetic subgroup `Γ` of determinant one.
-/

@[expose] public section

open UpperHalfPlane ModularForm SlashInvariantForm SlashInvariantFormClass Filter Asymptotics
  Function Complex OnePoint

open scoped MatrixGroups Real Topology Manifold ModularForm

section Decay

namespace UpperHalfPlane

variable {h : ℝ} {f : ℍ → ℂ}

/-- If the first `n` coefficients of the `q`-expansion of `f` with respect to the period `h`
vanish, then `f τ = O(exp (-2π n im τ / h))` as `im τ → ∞`. -/
theorem exp_decay_atImInfty_of_coeff_eq_zero (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) {n : ℕ}
    (hn : ∀ j < n, (qExpansion h f).coeff j = 0) :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * n * τ.im / h) := by
  -- The cusp function is `O(‖q‖ ^ n)` at `0`, since its Taylor polynomial of degree `< n` is `0`.
  have H := (hasFPowerSeriesOnBall_cuspFunction hh
    (analyticAt_cuspFunction_zero hh hfper hfhol hfbdd)
    (hasSum_qExpansion hh hfper hfhol hfbdd)).hasFPowerSeriesAt.isBigO_sub_partialSum_pow n
  have hpartial (y : ℂ) : (FormalMultilinearSeries.ofScalars ℂ
      fun m ↦ (qExpansion h f).coeff m).partialSum n y = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by simp [hn j (Finset.mem_range.mp hj)]
  simp only [hpartial, sub_zero, zero_add] at H
  refine (H.comp_tendsto (qParam_tendsto_atImInfty hh)).congr (fun τ ↦ ?_) (fun τ ↦ ?_)
  · exact eq_cuspFunction τ hh.ne' hfper
  · simp only [comp_apply, Periodic.norm_qParam, coe_im, ← Real.exp_nat_mul]
    ring_nf

/-- If `f τ = O(exp (-2π r im τ / h))` as `im τ → ∞`, then the coefficients of index `j < r` of the
`q`-expansion of `f` with respect to the period `h` vanish. -/
theorem qExpansion_coeff_eq_zero_of_exp_decay (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) {r : ℝ}
    (hf : f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * r * τ.im / h)) {j : ℕ} (hj : j < r) :
    (qExpansion h f).coeff j = 0 := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  -- Bound the coefficient using its expression as an integral along `im τ = t`, for `t` large.
  have key : ∀ t ≥ max A 1,
      ‖(qExpansion h f).coeff j‖ ≤ C * Real.exp (-2 * π * (r - j) / h * t) := by
    intro t ht
    have ht0 : 0 < t := one_pos.trans_le (le_of_max_le_right ht)
    rw [qExpansion_coeff_eq_intervalIntegral hh hfper hfhol hfbdd j ht0, norm_mul]
    refine (mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := C * Real.exp (-2 * π * (r - j) / h * t)) fun u _ ↦ ?_) (norm_nonneg _)).trans
      (le_of_eq ?_)
    · have hτ := hA ⟨u + t * I, by simpa using ht0⟩ (by simpa using le_of_max_le_left ht)
      rw [norm_mul, norm_div, norm_one, norm_pow, Periodic.norm_qParam]
      simp only [Set.mem_setOf_eq, Real.norm_of_nonneg (Real.exp_pos _).le, mk_im, coe_I, add_im,
        ofReal_im, mul_im, ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
        zero_add] at hτ ⊢
      calc 1 / Real.exp (-2 * π * t / h) ^ j * ‖f ⟨u + t * I, _⟩‖
          ≤ 1 / Real.exp (-2 * π * t / h) ^ j * (C * Real.exp (-2 * π * r * t / h)) := by
            gcongr
            exact hτ
        _ = C * Real.exp (-2 * π * (r - j) / h * t) := by
            rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg, mul_left_comm, ← Real.exp_add]
            ring_nf
    · rw [sub_zero, abs_of_pos hh, norm_div, norm_one, norm_real, Real.norm_of_nonneg hh.le]
      field_simp
  -- The bound tends to `0` as `t → ∞`, since `j < r`.
  have hlim : Tendsto (fun t ↦ C * Real.exp (-2 * π * (r - j) / h * t)) atTop (𝓝 0) := by
    have hneg : -2 * π * (r - j) / h < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith [Real.pi_pos])
        (sub_pos.mpr hj)) hh
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg hneg)).const_mul C
  exact norm_le_zero_iff.mp (ge_of_tendsto hlim (eventually_atTop.mpr ⟨_, key⟩))

end UpperHalfPlane

namespace ModularFormClass

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} (f : F)

/-- If the first `n` coefficients of the `q`-expansion of a modular form `f` with respect to a
positive strict period `h` vanish, then `f τ = O(exp (-2π n im τ / h))` as `im τ → ∞`. -/
protected theorem exp_decay_atImInfty_of_coeff_eq_zero [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {n : ℕ} (hn : ∀ j < n, (qExpansion h f).coeff j = 0) :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * n * τ.im / h) :=
  have : Fact (IsCusp ∞ Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  exp_decay_atImInfty_of_coeff_eq_zero hh (periodic_comp_ofComplex f hΓ) (holo f)
    (bdd_at_infty f) hn

/-- If a modular form `f` satisfies `f τ = O(exp (-2π r im τ / h))` as `im τ → ∞`, where `h > 0` is
a strict period, then the coefficients of index `j < r` of its `q`-expansion vanish. -/
protected theorem qExpansion_coeff_eq_zero_of_exp_decay [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {r : ℝ}
    (hf : f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * r * τ.im / h)) {j : ℕ} (hj : j < r) :
    (qExpansion h f).coeff j = 0 :=
  have : Fact (IsCusp ∞ Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  qExpansion_coeff_eq_zero_of_exp_decay hh (periodic_comp_ofComplex f hΓ) (holo f)
    (bdd_at_infty f) hf hj

end ModularFormClass

end Decay

section Norm

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ] {k : ℤ} (f : F)

open ConjAct Pointwise in
/-- If `∞` is a cusp of `ℋ`, then the translates of a modular form `f` for `𝒢` by elements of `ℋ`
(as packaged by `SlashInvariantForm.quotientFunc`) are bounded at `∞`. -/
theorem SlashInvariantForm.isBoundedAtImInfty_quotientFunc [ModularFormClass F 𝒢 k]
    [𝒢.IsFiniteRelIndex ℋ] [Fact (IsCusp ∞ ℋ)] (q : ℋ ⧸ 𝒢.subgroupOf ℋ) :
    IsBoundedAtImInfty (quotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h r =>
    have hc : IsCusp ∞ (toConjAct (r : GL (Fin 2) ℝ)⁻¹⁻¹ • 𝒢) := by
      simpa using (Fact.out : IsCusp ∞ ℋ).of_isFiniteRelIndex_conj r.2
    simpa using isBoundedAt_infty_iff.mp
      (ModularFormClass.bdd_at_cusps (ModularForm.translate f (r : GL (Fin 2) ℝ)⁻¹) hc)

/-- If `∞` is a cusp of `ℋ`, then the norm of a modular form `f` down to `ℋ` is `O(f)` as
`im τ → ∞`: it is the product of `f` with finitely many translates of `f`, all bounded at `∞`. -/
theorem ModularForm.coe_norm_isBigO [ModularFormClass F 𝒢 k] [𝒢.IsFiniteRelIndex ℋ]
    [ℋ.HasDetPlusMinusOne] [Fact (IsCusp ∞ ℋ)] :
    ⇑(ModularForm.norm ℋ f) =O[atImInfty] f := by
  classical
  let := Fintype.ofFinite (ℋ ⧸ 𝒢.subgroupOf ℋ)
  let s := (Finset.univ : Finset (ℋ ⧸ 𝒢.subgroupOf ℋ)).erase (QuotientGroup.mk 1)
  have h₁ := Finset.mul_prod_erase (Finset.univ : Finset (ℋ ⧸ 𝒢.subgroupOf ℋ)) (quotientFunc f)
    (Finset.mem_univ (QuotientGroup.mk 1))
  have h₂ : (fun τ ↦ ∏ q ∈ s, quotientFunc f q τ) =O[atImInfty]
      fun τ ↦ ∏ q ∈ s, (1 : ℍ → ℝ) τ :=
    IsBigO.finsetProd fun q _ ↦ isBoundedAtImInfty_quotientFunc f q
  have h₃ := (isBigO_refl (⇑f) atImInfty).norm_right.mul h₂
  simp only [Pi.one_apply, Finset.prod_const_one, mul_one, isBigO_norm_right] at h₃
  rw [ModularForm.coe_norm, ← h₁, QuotientGroup.mk, quotientFunc_mk]
  refine h₃.congr_left fun τ ↦ ?_
  simp [s, Finset.prod_apply]

end Norm

section SturmBound

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ}

/-- **Sturm bound** for an arithmetic subgroup `Γ` of `GL(2, ℝ)`, for any `ModularFormClass`.

Let `h > 0` be a strict period of `Γ` and let `d` be the index of `Γ ⊓ SL(2, ℤ)` in `SL(2, ℤ)`.
If the `q`-expansion of `f` with respect to `h` vanishes to order `n > h * ⌊k * d / 12⌋`, then
`f = 0`. -/
theorem ModularFormClass.sturm_bound [ModularFormClass F Γ k] [Γ.IsArithmetic] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (f : F) {n : ℕ}
    (hn : ((k * Γ.relIndex 𝒮ℒ).toNat / 12 : ℕ) * h < n)
    (hf : (n : ℕ∞) ≤ (qExpansion h f).order) : ⇑f = 0 := by
  rw [← ModularForm.norm_eq_zero_iff 𝒮ℒ f]
  apply ModularForm.sturm_bound_levelOne
  -- The norm of `f` is `O(exp (-2π (n / h) im τ))`, since `f` is.
  have hF : ⇑(ModularForm.norm 𝒮ℒ f) =O[atImInfty]
      fun τ ↦ Real.exp (-2 * π * (n / h) * τ.im / 1) := by
    refine ((ModularForm.coe_norm_isBigO f).trans
      (ModularFormClass.exp_decay_atImInfty_of_coeff_eq_zero f hh hΓ fun j hj ↦
        PowerSeries.coeff_of_lt_order j (lt_of_lt_of_le (mod_cast hj) hf))).congr_right
      fun τ ↦ ?_
    congr 1
    field_simp
  -- Hence its level-one `q`-expansion vanishes to order `⌈n / h⌉ > ⌊k * d / 12⌋`.
  refine lt_of_lt_of_le (mod_cast Nat.lt_succ_self _) (PowerSeries.nat_le_order _
    ((k * Γ.relIndex 𝒮ℒ).toNat / 12 + 1) fun j hj ↦
      ModularFormClass.qExpansion_coeff_eq_zero_of_exp_decay _ one_pos one_mem_strictPeriods_SL hF
        ((lt_div_iff₀ hh).mpr (lt_of_le_of_lt ?_ hn)))
  gcongr
  exact_mod_cast Nat.lt_succ_iff.mp hj

/-- **Sturm bound** for an arithmetic subgroup `Γ` of `GL(2, ℝ)`.

Let `h > 0` be a strict period of `Γ` and let `d` be the index of `Γ ⊓ SL(2, ℤ)` in `SL(2, ℤ)`.
If the `q`-expansion of `f` with respect to `h` vanishes to order `n > h * ⌊k * d / 12⌋`, then
`f = 0`. -/
theorem ModularForm.sturm_bound [Γ.IsArithmetic] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (f : ModularForm Γ k) {n : ℕ} (hn : ((k * Γ.relIndex 𝒮ℒ).toNat / 12 : ℕ) * h < n)
    (hf : (n : ℕ∞) ≤ (qExpansion h f).order) : f = 0 :=
  (coe_eq_zero_iff f).mp (ModularFormClass.sturm_bound hh hΓ f hn hf)

open Matrix.SpecialLinearGroup in
/-- The index of (the image of) a subgroup `Γ` of `SL(2, ℤ)` in `𝒮ℒ` is the index of `Γ`. -/
theorem Subgroup.relIndex_map_mapGL_range (Γ : Subgroup SL(2, ℤ)) :
    (Γ : Subgroup (GL (Fin 2) ℝ)).relIndex 𝒮ℒ = Γ.index := by
  rw [MonoidHom.range_eq_map, relIndex_map_map_of_injective _ _ mapGL_injective,
    relIndex_top_right]

/-- **Sturm bound** for a finite-index subgroup `Γ` of `SL(2, ℤ)`.

Let `h > 0` be a strict period of `Γ` (for instance the width of the cusp `∞`). If the
`q`-expansion of `f` with respect to `h` vanishes to order `n > h * ⌊k * [SL(2, ℤ) : Γ] / 12⌋`,
then `f = 0`. -/
theorem ModularForm.sturm_bound_of_finiteIndex {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (hh : 0 < h) (hΓ : h ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods) (f : ModularForm Γ k)
    {n : ℕ} (hn : ((k * Γ.index).toNat / 12 : ℕ) * h < n)
    (hf : (n : ℕ∞) ≤ (qExpansion h f).order) : f = 0 :=
  sturm_bound hh hΓ f (by rwa [Subgroup.relIndex_map_mapGL_range]) hf

/-- Spaces of modular forms for an arithmetic subgroup `Γ` of determinant one (e.g. the image of a
finite-index subgroup of `SL(2, ℤ)`) are finite-dimensional: by the Sturm bound, a modular form is
determined by finitely many coefficients of its `q`-expansion. -/
instance ModularForm.instFiniteDimensional [Γ.IsArithmetic] [Γ.HasDetOne] :
    FiniteDimensional ℂ (ModularForm Γ k) := by
  have hh := Γ.strictWidthInfty_pos
  have hΓ := Γ.strictWidthInfty_mem_strictPeriods
  obtain ⟨n, hn⟩ := exists_nat_gt
    (((k * Γ.relIndex 𝒮ℒ).toNat / 12 : ℕ) * Γ.strictWidthInfty : ℝ)
  -- The first `n` coefficients of the `q`-expansion, as a `ℂ`-linear map.
  let L : ModularForm Γ k →ₗ[ℂ] Fin n → ℂ :=
    { toFun f j := (qExpansion Γ.strictWidthInfty f).coeff j
      map_add' f g := by ext j; simp [ModularForm.qExpansion_add hh hΓ f g]
      map_smul' a f := by ext j; simp [ModularForm.qExpansion_smul hh hΓ a f] }
  refine .of_injective L <| (injective_iff_map_eq_zero L).mpr fun f hf ↦
    sturm_bound hh hΓ f hn <| PowerSeries.nat_le_order _ _ fun j hj ↦ ?_
  simpa [L] using congr_fun hf ⟨j, hj⟩

end SturmBound
