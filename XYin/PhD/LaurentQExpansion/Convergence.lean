/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.LaurentQExpansion.Algebra

/-!
# Convergence and uniqueness of Laurent q-expansions

For a periodic holomorphic function meromorphic at the cusp, its formal Laurent q-expansion
converges throughout the punctured unit disc and reconstructs the function on the upper half-plane.
The coefficients are uniquely determined by this reconstruction and a lower support bound.
-/

open Complex Filter Function LaurentSeries ModularForm Set UpperHalfPlane
open scoped Manifold Topology

noncomputable section

local notation "𝕢" => Periodic.qParam

/-- A sum over integers supported above `-N` may be reindexed by `n - N`. -/
lemma hasSum_int_iff_natCast_sub_of_eq_zero {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {a : ℤ → α} {s : α} (N : ℕ)
    (ha : ∀ j < -(N : ℤ), a j = 0) :
    HasSum a s ↔ HasSum (fun n : ℕ ↦ a ((n : ℤ) - N)) s := by
  have hinj : Injective (fun n : ℕ ↦ (n : ℤ) - N) := by
    intro m n hmn
    change (m : ℤ) - N = (n : ℤ) - N at hmn
    omega
  exact (hinj.hasSum_iff (by
    intro j hj
    apply ha j
    by_contra hlt
    apply hj
    refine ⟨(j + N).toNat, ?_⟩
    change ((j + N).toNat : ℤ) - N = j
    omega)).symm

/-- Multiplication by a nonnegative power of the q-parameter preserves periodicity. -/
lemma periodic_comp_ofComplex_qpow_mul {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (N : ℕ) :
    Periodic ((fun τ : ℍ ↦ 𝕢 h τ ^ N * f τ) ∘ ofComplex) h := by
  intro z
  rcases le_or_gt z.im 0 with hz | hz
  · simp [ofComplex_apply_of_im_nonpos hz,
      ofComplex_apply_of_im_nonpos (by simpa using hz : (z + h).im ≤ 0)]
  · have hf := hfper z
    simp only [comp_apply, ofComplex_apply_of_im_pos hz,
      ofComplex_apply_of_im_pos (by simpa using hz : 0 < (z + h).im), coe_mk] at hf ⊢
    rw [hf, Periodic.qParam, Periodic.qParam, mul_add, add_div,
      mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hh.ne'), Complex.exp_add,
      Complex.exp_two_pi_mul_I, mul_one]

/-- A periodic function whose cusp function is analytic has a finite limit at infinity. -/
lemma tendsto_atImInfty_of_analyticAt_cuspFunction {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfan : AnalyticAt ℂ (cuspFunction h f) 0) :
    Tendsto f atImInfty (𝓝 (cuspFunction h f 0)) := by
  simpa only [comp_def, eq_cuspFunction _ hh.ne' hfper] using
    hfan.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)

/-- The pole-removed function is bounded at infinity. -/
lemma isBoundedAtImInfty_poleRemoved {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfmero : MeromorphicAt (cuspFunction h f) 0) :
    IsBoundedAtImInfty (poleRemoved h f) := by
  have ht := tendsto_atImInfty_of_analyticAt_cuspFunction hh
    (periodic_comp_ofComplex_qpow_mul hh hfper (poleOrder h f))
    (analyticAt_cuspFunction_poleRemoved hfmero)
  simpa [IsBoundedAtImInfty, BoundedAtFilter, Pi.one_def] using ht.isBigO_one ℝ

/-- The q-expansion of the pole-removed function converges on the unit disc. -/
lemma hasSum_toQExpansion_of_norm_lt {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f)
    (hfmero : MeromorphicAt (cuspFunction h f) 0) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (toQExpansion h f).coeff n * q ^ n)
      (cuspFunction h (poleRemoved h f) q) := by
  have hhol : MDiff (poleRemoved h f) :=
    ((Periodic.differentiable_qParam.mdifferentiable.comp mdifferentiable_coe).pow _).mul hfhol
  simpa only [toQExpansion, smul_eq_mul] using
    UpperHalfPlane.hasSum_qExpansion_of_norm_lt (f := poleRemoved h f) hh
      (periodic_comp_ofComplex_qpow_mul hh hfper (poleOrder h f)) hhol
      (isBoundedAtImInfty_poleRemoved hh hfper hfmero) hq

/-- The Laurent q-expansion converges on the punctured unit disc, starting at its pole bound. -/
lemma hasSum_laurentqExpansion_natCast_sub_of_norm_lt {h : ℝ} (hh : 0 < h)
    {f : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f)
    (hfmero : MeromorphicAt (cuspFunction h f) 0) {q : ℂ} (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (laurentqExpansion h f).coeff ((n : ℤ) - poleOrder h f) *
      q ^ ((n : ℤ) - poleOrder h f)) (cuspFunction h f q) := by
  have hs := (hasSum_toQExpansion_of_norm_lt hh hfper hfhol hfmero hq).mul_left
    (q ^ (-(poleOrder h f : ℤ)))
  rw [cuspFunction_poleRemoved_eq h f hq0 hq] at hs
  simp only [← zpow_natCast q, ← mul_assoc, ← zpow_add₀ hq0, neg_add_cancel,
    zpow_zero, one_mul] at hs
  convert hs using 1
  ext n
  rw [show (n : ℤ) - poleOrder h f = -(poleOrder h f : ℤ) + n by omega,
    laurentqExpansion.coeff_neg_poleOrder_add, zpow_add₀ hq0, zpow_natCast]
  ring

/-- The Laurent q-expansion converges on the punctured unit disc as a sum over all integers. -/
lemma hasSum_laurentqExpansion_of_norm_lt {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f)
    (hfmero : MeromorphicAt (cuspFunction h f) 0) {q : ℂ} (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) :
    HasSum (fun n : ℤ ↦ (laurentqExpansion h f).coeff n * q ^ n)
      (cuspFunction h f q) := by
  apply (hasSum_int_iff_natCast_sub_of_eq_zero (poleOrder h f) ?_).mpr
  · exact hasSum_laurentqExpansion_natCast_sub_of_norm_lt hh hfper hfhol hfmero hq0 hq
  · intro n hn
    rw [laurentqExpansion.coeff_eq_zero_of_lt hn, zero_mul]

/-- The Laurent q-expansion reconstructs the function at every point of the upper half-plane. -/
lemma hasSum_laurentqExpansion_natCast_sub {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f)
    (hfmero : MeromorphicAt (cuspFunction h f) 0) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ (laurentqExpansion h f).coeff ((n : ℤ) - poleOrder h f) *
      𝕢 h τ ^ ((n : ℤ) - poleOrder h f)) (f τ) := by
  simpa only [eq_cuspFunction τ hh.ne' hfper] using
    hasSum_laurentqExpansion_natCast_sub_of_norm_lt hh hfper hfhol hfmero
      (Periodic.qParam_ne_zero τ) (Periodic.norm_qParam_lt_one hh τ.im_pos)

/-- The Laurent expansion reconstructs the function by summing over every integer exponent. -/
lemma hasSum_laurentqExpansion {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f)
    (hfmero : MeromorphicAt (cuspFunction h f) 0) (τ : ℍ) :
    HasSum (fun n : ℤ ↦ (laurentqExpansion h f).coeff n * 𝕢 h τ ^ n) (f τ) := by
  simpa only [eq_cuspFunction τ hh.ne' hfper] using
    hasSum_laurentqExpansion_of_norm_lt hh hfper hfhol hfmero
      (Periodic.qParam_ne_zero τ) (Periodic.norm_qParam_lt_one hh τ.im_pos)

/-- A sufficient pole-clearing exponent identifies Laurent coefficients with Taylor coefficients. -/
lemma laurentqExpansion_coeff_natCast_sub_of_poleOrder_le {h : ℝ} (hh : 0 < h)
    {f : ℍ → ℂ} (hfmero : MeromorphicAt (cuspFunction h f) 0) {N : ℕ}
    (hN : poleOrder h f ≤ N) (n : ℕ) :
    (laurentqExpansion h f).coeff ((n : ℤ) - N) =
      (qExpansion h (fun τ : ℍ ↦ 𝕢 h τ ^ N * f τ)).coeff n := by
  rw [laurentqExpansion_eq_shiftedLaurent hh hfmero hN]
  simp [shiftedLaurent, HahnSeries.coeff_single_mul, PowerSeries.coeff_coe]

/-- A lower-bounded Laurent expansion reconstructing a function has its canonical coefficients.

Only meromorphy at the cusp is required: the convergent reconstruction is supplied as a hypothesis.
-/
lemma laurentqExpansion_coeff_unique {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfmero : MeromorphicAt (cuspFunction h f) 0) {c : ℤ → ℂ} {N : ℕ}
    (hc : ∀ j < -(N : ℤ), c j = 0)
    (hsum : ∀ τ : ℍ, HasSum (fun j : ℤ ↦ c j * 𝕢 h τ ^ j) (f τ)) (j : ℤ) :
    c j = (laurentqExpansion h f).coeff j := by
  let M := N + poleOrder h f
  have hM : poleOrder h f ≤ M := by omega
  have hcM : ∀ j < -(M : ℤ), c j = 0 := by
    intro j hj
    apply hc j
    dsimp [M] at hj
    omega
  by_cases hj : j < -(M : ℤ)
  · rw [hcM j hj, laurentqExpansion.coeff_eq_zero_of_lt (by omega)]
  · let n := (j + M).toNat
    have hn : (n : ℤ) - M = j := by dsimp [n]; omega
    rw [← hn, laurentqExpansion_coeff_natCast_sub_of_poleOrder_le hh hfmero hM n]
    let g : ℍ → ℂ := fun τ ↦ 𝕢 h τ ^ M * f τ
    let : FunLike (ℍ → ℂ) ℍ ℂ := { coe := id, coe_injective := fun _ _ h ↦ h }
    apply UpperHalfPlane.qExpansion_coeff_unique g (c := fun m ↦ c ((m : ℤ) - M)) hh
      (analyticAt_cuspFunction_qpow_of_poleOrder_le hh hfmero hM) ?_ n
    intro τ
    have hq0 := Periodic.qParam_ne_zero (h := h) τ
    have hs := ((hasSum_int_iff_natCast_sub_of_eq_zero M (by
      intro k hk
      rw [hcM k hk, zero_mul])).mp (hsum τ)).mul_left (𝕢 h τ ^ M)
    apply hs.congr_fun
    intro k
    simp only [smul_eq_mul]
    rw [← zpow_natCast (𝕢 h τ) M, zpow_sub₀ hq0, zpow_natCast]
    field_simp
    simp only [zpow_natCast]

/-- A formal Laurent series reconstructing a cusp-meromorphic function is its q-expansion. -/
lemma laurentqExpansion_eq_of_hasSum {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfmero : MeromorphicAt (cuspFunction h f) 0) {L : LaurentSeries ℂ}
    (hsum : ∀ τ : ℍ, HasSum (fun j : ℤ ↦ L.coeff j * 𝕢 h τ ^ j) (f τ)) :
    laurentqExpansion h f = L := by
  apply HahnSeries.ext
  funext j
  symm
  apply laurentqExpansion_coeff_unique hh hfmero (N := L.order.natAbs) ?_ hsum j
  intro k hk
  apply HahnSeries.coeff_eq_zero_of_lt_order
  have hle : -L.order ≤ (L.order.natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -L.order))
  omega
