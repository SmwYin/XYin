import Mathlib
import XYin.PhD.Modularforms.Delta
import XYin.PhD.Test.jfunctionLaurent

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups
  PowerSeries SlashInvariantFormClass Real Function IntegralPowerSeries
open scoped Manifold

/-!
# The scaled functions `jN` and `qjN`

This file collects the basic API for the scaled modular function `jN N z = j (N • z)`
and its pole-removed companion `qjN`.  It contains the `Γ₀(N)` slash-invariance,
cusp-function formulas, meromorphic-at-cusp statements, and differentiability data used by
the later Cox modular-equation files.
-/

local notation "𝕢" => Periodic.qParam
local notation "ℍₒ" => upperHalfPlaneSet

noncomputable section

section modularEquation

/-! ## `jN` and `Γ₀(N)` invariance

This section uses Cox Theorem 11.2(ii), the `SL₂(ℤ)`-invariance of `j`, to
formalise the `j(mτ)` invariance assertion in Theorem 11.9(ii).
-/

section JNInvariance

/-- The scaled `j`-function `jN N z = j (N • z)`.  This is Cox's `j(mτ)`
from Theorem 11.9(ii), with the level `m` represented by a positive natural. -/
noncomputable def jN (N : ℕ+) : ℍ → ℂ :=
  fun z => j (N • z)

/-- The level-one `j`-function is invariant under the usual `SL₂(ℤ)` action on `ℍ`. -/
lemma j_invariant (γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z := by
  have := congrFun (j_slashInvariant γ) z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one] at this
  exact this

private def gamma0Conjugate (N : ℕ+) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N : ℕ)) : SL(2, ℤ) :=
  let a := γ 0 0; let b := γ 0 1; let c := γ 1 0; let d := γ 1 1
  ⟨!![a, ↑N * b; c / ↑N, d], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have hdvd : (↑N : ℤ) ∣ c :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
    have hdet : a * d - b * c = 1 := by
      have := γ.prop; rwa [Matrix.det_fin_two] at this
    rw [show ↑N * b * (c / ↑N) = b * (↑N * (c / ↑N)) from by ring]
    rw [Int.mul_ediv_cancel' hdvd]
    linarith⟩

/-- Scaling by `N` commutes with the `Γ₀(N)` action after conjugating the matrix. -/
private lemma natPosSMul_gamma0_comm (N : ℕ+) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N : ℕ)) (z : ℍ) :
    (N • (γ • z) : ℍ) = gamma0Conjugate N γ hγ • (N • z : ℍ) := by
  ext
  simp only [coe_specialLinearGroup_apply, gamma0Conjugate, Matrix.of_apply, natPosSMul_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  have hdvd : (↑N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hcN : (↑N : ℤ) * (γ 1 0 / ↑N) = γ 1 0 := Int.mul_ediv_cancel' hdvd
  have hR :
      (algebraMap ℤ ℝ) (γ 1 0 / ↑N) * (↑N : ℝ) = (algebraMap ℤ ℝ) (γ 1 0) := by
    rw [show (↑N : ℝ) = (algebraMap ℤ ℝ) (↑N : ℤ) from by simp [algebraMap_int_eq]]
    rw [← map_mul, mul_comm, hcN]
  have hC : (↑((algebraMap ℤ ℝ) (γ 1 0 / ↑N)) : ℂ) * ((↑N : ℂ) * ↑z) =
      (↑((algebraMap ℤ ℝ) (γ 1 0)) : ℂ) * ↑z := by
    rw [← mul_assoc, show (↑((algebraMap ℤ ℝ) (γ 1 0 / ↑N)) : ℂ) * ↑N =
      ↑((algebraMap ℤ ℝ) (γ 1 0)) from by exact_mod_cast hR]
  rw [hC, map_mul,
    show (algebraMap ℤ ℝ) (↑N : ℤ) = (↑N : ℝ) from by simp [algebraMap_int_eq]]
  push_cast
  rw [← mul_div_assoc]
  congr 1; ring

/-- Cox Theorem 11.9(ii): `j(mτ)`, here `jN N`, is weight-zero invariant
under `Γ₀(N)`. -/
lemma jN_slashInvariant (N : ℕ+) (γ : CongruenceSubgroup.Gamma0 (N : ℕ)) :
    jN N ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = jN N := by
  ext z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one, jN]
  rw [natPosSMul_gamma0_comm N γ γ.prop z]
  exact j_invariant _ _

end JNInvariance

/-! ## Cusp and differentiability data for `jN`

The `qj` and `qjN` constructions encode the q-expansion behaviour from Cox
Theorem 11.8, and provide the meromorphic cusp data used later.
-/

section JNAtCusps

/-- The holomorphic remainder `qj` scaled by `N`, reflecting the q-expansion
normalisation in Cox Theorem 11.8. -/
noncomputable def qjN (N : ℕ+) : ℍ → ℂ :=
  fun z => qj (N • z)

/-- Coercion formula for scaling an upper-half-plane point built from a complex number. -/
lemma natPosSMul_ofComplex_coe (N : ℕ+) {w : ℂ} (hw : 0 < w.im) :
    (N • UpperHalfPlane.ofComplex w : ℍ) = UpperHalfPlane.ofComplex ((↑N : ℂ) * w) := by
  have hNw : 0 < ((↑N : ℂ) * w).im := by
    rw [Complex.mul_im]
    simp only [natCast_re, natCast_im, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr N.pos) hw
  apply UpperHalfPlane.ext
  rw [natPosSMul_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
    UpperHalfPlane.ofComplex_apply_of_im_pos hNw]

/-- Periodicity of the scaled q-expansion remainder from Cox Theorem 11.8. -/
lemma qjN_periodic (N : ℕ+) : Periodic (qjN N ∘ UpperHalfPlane.ofComplex) (N : ℕ) := by
  have hqNN : Periodic (qj ∘ UpperHalfPlane.ofComplex) ((↑N : ℂ) * ↑N) := by
    have := qj_periodic.nat_mul ((N : ℕ) * (N : ℕ))
    simpa [Nat.cast_mul] using this
  intro w
  simp only [Function.comp, qjN]
  by_cases hw : 0 < Complex.im w
  · have hwN : 0 < Complex.im (w + ↑N) := by simp [Complex.add_im]; linarith
    have hkey := hqNN ((↑N : ℂ) * w)
    have hring : (↑N : ℂ) * w + (↑N : ℂ) * ↑N = (↑N : ℂ) * (w + ↑N) := by ring
    rw [hring] at hkey
    simp only [Function.comp] at hkey
    rw [natPosSMul_ofComplex_coe N hwN, natPosSMul_ofComplex_coe N hw]
    exact hkey
  · have hw0 := le_of_not_gt hw
    have hwN : Complex.im (w + ↑N) ≤ 0 := by simp [Complex.add_im]; linarith
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos hw0,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hwN]

/-- The scaled pole-removed function `qjN N` is holomorphic on the upper half-plane. -/
lemma qjN_holomorphic (N : ℕ+) :
    ∀ z : ℂ, 0 < Complex.im z →
      DifferentiableAt ℂ (qjN N ∘ UpperHalfPlane.ofComplex) z := by
  intro z hz
  have hNz : 0 < Complex.im ((↑N : ℂ) * z) := by
    rw [Complex.mul_im]
    simp only [natCast_re, natCast_im, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr N.pos) hz
  have hqj := qj_holomorphic _ hNz
  have hN : DifferentiableAt ℂ (fun w => (↑N : ℂ) * w) z :=
    (differentiableAt_const _).mul differentiableAt_id
  refine (hqj.comp z hN).congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz] with w hw
  simp only [Function.comp, qjN]
  rw [natPosSMul_ofComplex_coe N hw]

/-- The scaled pole-removed function `qjN N` is manifold-differentiable on `ℍ`. -/
lemma qjN_MDifferentiable (N : ℕ+) : MDiff (qjN N) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  exact (qjN_holomorphic N z hz).differentiableWithinAt

/-- The scaled pole-removed function `qjN N` remains bounded as `im τ → ∞`. -/
lemma qjN_IsBoundedAtImInfty (N : ℕ+) :
    IsBoundedAtImInfty (qjN N) := by
  apply qj_IsBoundedAtImInfty.comp_tendsto
  rw [show atImInfty = Filter.comap UpperHalfPlane.im
    Filter.atTop from rfl, Filter.tendsto_comap_iff]
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr N.pos
  have him_eq :
      UpperHalfPlane.im ∘
          (fun x : ℍ => (N • x : ℍ)) =
        (fun x : ℝ => (↑N : ℝ) * x) ∘ UpperHalfPlane.im := by
    ext τ
    simp only [Function.comp, natPosSMul_apply, UpperHalfPlane.im, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  rw [him_eq]
  exact (Filter.Tendsto.const_mul_atTop hN_pos Filter.tendsto_id).comp Filter.tendsto_comap

/-- Analyticity at the cusp of the scaled q-expansion remainder from Cox
Theorem 11.8. -/
lemma qjN_cuspFunction_analyticAt (N : ℕ+) :
    AnalyticAt ℂ (cuspFunction (N : ℕ) (qjN N)) 0 :=
  DifferentiableOn.analyticAt (fun q hq => (UpperHalfPlane.differentiableOn_cuspFunction_ball
    (Nat.cast_pos.mpr N.pos) (qjN_periodic N)
    (qjN_MDifferentiable N) (qjN_IsBoundedAtImInfty N)) q hq)
      (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

/-- Cusp expansion of `jN N`: a pole term times the analytic remainder `qjN N`. -/
lemma jN_cuspFunction_eq (N : ℕ+) {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    cuspFunction (N : ℕ) (jN N) q =
      q⁻¹ ^ ((N : ℕ) * (N : ℕ)) * cuspFunction (N : ℕ) (qjN N) q := by
  have hN : (0 : ℝ) < (N : ℕ) := Nat.cast_pos.mpr N.pos
  have him := Periodic.im_invQParam_pos_of_norm_lt_one hN hq hq0
  let τ : ℍ := ⟨Periodic.invQParam (N : ℕ) q, him⟩
  have hjN_eq : cuspFunction (N : ℕ) (jN N) q = jN N τ := by
    change Periodic.cuspFunction (N : ℕ) _ q = _
    rw [Periodic.cuspFunction_eq_of_nonzero (N : ℕ) _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hqjN_eq : cuspFunction (N : ℕ) (qjN N) q = qjN N τ := by
    change Periodic.cuspFunction (N : ℕ) _ q = _
    rw [Periodic.cuspFunction_eq_of_nonzero (N : ℕ) _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hcexp :
      cexp (2 * ↑π * Complex.I *
        (↑(N • τ : ℍ) : ℂ)) = q ^ ((N : ℕ) * (N : ℕ)) := by
    rw [natPosSMul_apply]
    have hNnzC : (↑N : ℂ) ≠ 0 := by
      exact_mod_cast (PNat.ne_zero N)
    rw [show 2 * ↑π * Complex.I * ((↑N : ℂ) * (τ : ℂ)) = ↑((N : ℕ) * (N : ℕ)) *
      (2 * ↑π * Complex.I * (τ : ℂ) / ↑N) from by field_simp [hNnzC]; push_cast; ring,
      Complex.exp_nat_mul]
    congr 1
    simpa [τ, Periodic.qParam] using
      Periodic.qParam_right_inv (show ((N : ℕ) : ℝ) ≠ 0 by
        exact_mod_cast (PNat.ne_zero N)) hq0
  rw [hjN_eq, hqjN_eq]
  simp only [jN, qjN, qj, Pi.mul_apply]
  rw [hcexp, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq0), one_mul]

/-- Meromorphicity at the cusp for `jN N`, using the pole term in Cox
Theorem 11.8. -/
lemma jN_cuspFunction_Meromorphic (N : ℕ+) :
    MeromorphicAt (cuspFunction (N : ℕ) (jN N)) (0 : ℂ) := by
  have hqjN_mer : MeromorphicAt (cuspFunction (N : ℕ) (qjN N)) (0 : ℂ) := by
    change MeromorphicAt
      (Function.Periodic.cuspFunction (N : ℕ) (qjN N ∘ UpperHalfPlane.ofComplex)) 0
    exact (qjN_cuspFunction_analyticAt N).meromorphicAt
  have hpow : MeromorphicAt (fun q : ℂ => q⁻¹ ^ ((N : ℕ) * (N : ℕ))) (0 : ℂ) :=
    ((MeromorphicAt.id (0 : ℂ)).inv).pow _
  refine (hpow.mul hqjN_mer).congr ?_
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds (by simpa [Metric.ball, dist_eq_norm]
      using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hq hq'
  simp only [Pi.mul_apply]
  exact (jN_cuspFunction_eq N (by simpa using hq') hq).symm

/-- Packaged modular-function data available for `jN`: slash invariance on `Γ₀(N)` and
meromorphicity of the `q`-cusp function at `0`. -/
theorem jN_modular_data (N : ℕ+) :
    (∀ γ : CongruenceSubgroup.Gamma0 (N : ℕ),
      jN N ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = jN N) ∧
    MeromorphicAt (cuspFunction (N : ℕ) (jN N)) (0 : ℂ) :=
  ⟨jN_slashInvariant N, jN_cuspFunction_Meromorphic N⟩

/-- `cuspFunction (N) (jN N)` is `q^(-(N^2))` times an analytic remainder on `‖q‖ < 1`. -/
theorem jN_exists_analytic_remainder (N : ℕ+) :
    ∃ F : ℂ → ℂ,
      AnalyticAt ℂ F 0 ∧
      ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 →
        cuspFunction (N : ℕ) (jN N) q =
          q⁻¹ ^ ((N : ℕ) * (N : ℕ)) * F q := by
  refine ⟨cuspFunction (N : ℕ) (qjN N), qjN_cuspFunction_analyticAt N, ?_⟩
  intro q hq0 hq
  simpa using jN_cuspFunction_eq N hq0 hq

/-- Level-`2` specialisation of `jN_cuspFunction_eq`. -/
theorem jN_cuspFunction_eq_two {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    cuspFunction (2 : ℕ) (jN (2 : ℕ+)) q =
      q⁻¹ ^ (4 : ℕ) * cuspFunction (2 : ℕ) (qjN (2 : ℕ+)) q := by
  simpa using jN_cuspFunction_eq (N := (2 : ℕ+)) hq0 hq

/-- Holomorphicity of `jN N` on `ℍ`, expressed through the `ofComplex` chart. -/
lemma jN_Meromorphic (N : ℕ+) {z : ℍₒ} :
    DifferentiableAt ℂ (jN N ∘ UpperHalfPlane.ofComplex) z := by
  obtain ⟨z, hz⟩ := z
  have hz' := Set.mem_setOf.mp hz
  have hNz : 0 < Complex.im ((↑N : ℂ) * z) := by
    rw [Complex.mul_im]
    simp only [natCast_re, natCast_im, zero_mul, add_zero, Nat.cast_pos, N.pos,
        mul_pos_iff_of_pos_left]
    exact hz'
  have hE4 := UpperHalfPlane.mdifferentiableAt_iff.mp
    (ModularFormClass.holo E4 ⟨↑N * z, hNz⟩)
  have hΔ := UpperHalfPlane.mdifferentiableAt_iff.mp
    (ModularFormClass.holo Delta ⟨↑N * z, hNz⟩)
  have hΔ0 : (Delta ∘ UpperHalfPlane.ofComplex) (↑N * z) ≠ 0 := by
    simp only [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hNz, Delta_apply]
    exact Δ_ne_zero _
  have hj : DifferentiableAt ℂ (j ∘ UpperHalfPlane.ofComplex) (↑N * z) := by
    simpa [j, Function.comp] using (hE4.pow 3).div hΔ hΔ0
  have hcomp := hj.comp z (by
    change DifferentiableAt ℂ (fun w => (↑N : ℂ) * w) z
    exact differentiableAt_const _ |>.mul differentiableAt_id)
  have hEq : (jN N ∘ UpperHalfPlane.ofComplex)
      =ᶠ[nhds z] ((j ∘ UpperHalfPlane.ofComplex) ∘ fun w => (↑N : ℂ) * w) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz']
      with w hw
    have hNw : 0 < (↑N * w).im := by
      rw [Complex.mul_im]
      simp only [natCast_re, natCast_im, zero_mul, add_zero, Nat.cast_pos, N.pos,
        mul_pos_iff_of_pos_left]
      exact hw
    have hsmul :
        (N • UpperHalfPlane.ofComplex w : ℍ) = UpperHalfPlane.ofComplex ((↑N : ℂ) * w) :=
      natPosSMul_ofComplex_coe N hw
    simpa [Function.comp, jN, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos hNw] using congrArg j hsmul
  change DifferentiableAt ℂ (jN N ∘ UpperHalfPlane.ofComplex) z
  have hcomp' :
      DifferentiableAt ℂ ((j ∘ UpperHalfPlane.ofComplex) ∘ fun w => (↑N : ℂ) * w) z := by
    convert hcomp using 2
  exact hcomp'.congr_of_eventuallyEq hEq

/-- The scaled function `jN N` is manifold-differentiable on the upper half-plane. -/
theorem jN_MDifferentiable (N : ℕ+) : MDiff (jN N) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  exact (jN_Meromorphic N (z := ⟨z, hz⟩)).differentiableWithinAt

end JNAtCusps

end modularEquation
