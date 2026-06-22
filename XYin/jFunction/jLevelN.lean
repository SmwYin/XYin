import XYin.jFunction.jfunction

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups PowerSeries
  SlashInvariantFormClass Real Function IntegralPowerSeries
open scoped Manifold

local notation "𝕢" => Periodic.qParam
local notation "ℍₒ" => upperHalfPlaneSet

private lemma natCast_mul_im_pos (N : ℕ) [NeZero N] (z : ℍ) :
    0 < ((↑N : ℂ) * (z : ℂ)).im := by
  rw [Complex.mul_im]
  simp only [natCast_re, natCast_im, zero_mul, add_zero]
  exact mul_pos (Nat.cast_pos.mpr (NeZero.pos N)) z.2

noncomputable def jN (N : ℕ) [NeZero N] : ℍ → ℂ :=
  fun z => j ⟨(↑N : ℂ) * (z : ℂ), natCast_mul_im_pos N z⟩

lemma j_invariant (γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z := by
  have := congrFun (j_slashInvariant γ) z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one] at this
  exact this

private def gamma0Conjugate (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : SL(2, ℤ) :=
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

private lemma natPosSMul_gamma0_comm (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    (⟨(↑N : ℂ) * ((γ • z : ℍ) : ℂ), natCast_mul_im_pos N (γ • z)⟩ : ℍ) =
      gamma0Conjugate N γ hγ •
        (⟨(↑N : ℂ) * (z : ℂ), natCast_mul_im_pos N z⟩ : ℍ) := by
  ext
  simp only [coe_specialLinearGroup_apply, gamma0Conjugate, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  have hdvd : (↑N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hcN : (↑N : ℤ) * (γ 1 0 / ↑N) = γ 1 0 := Int.mul_ediv_cancel' hdvd
  have hR : (algebraMap ℤ ℝ) (γ 1 0 / ↑N) * (↑N : ℝ) = (algebraMap ℤ ℝ) (γ 1 0) := by
    rw [show (↑N : ℝ) = (algebraMap ℤ ℝ) (↑N : ℤ) from by simp [algebraMap_int_eq]]
    rw [← map_mul, mul_comm, hcN]
  have hC : (↑((algebraMap ℤ ℝ) (γ 1 0 / ↑N)) : ℂ) * ((↑N : ℂ) * ↑z) =
      (↑((algebraMap ℤ ℝ) (γ 1 0)) : ℂ) * ↑z := by
    rw [← mul_assoc, show (↑((algebraMap ℤ ℝ) (γ 1 0 / ↑N)) : ℂ) * ↑N =
      ↑((algebraMap ℤ ℝ) (γ 1 0)) from by exact_mod_cast hR]
  rw [hC, map_mul, show (algebraMap ℤ ℝ) (↑N : ℤ) = (↑N : ℝ) from by simp [algebraMap_int_eq]]
  push_cast
  rw [← mul_div_assoc]
  congr 1; ring

lemma jN_slashInvariant (N : ℕ) [NeZero N] (γ : CongruenceSubgroup.Gamma0 N) :
    jN N ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = jN N := by
  ext z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one, jN]
  rw [natPosSMul_gamma0_comm N γ γ.prop z]
  exact j_invariant _ _

noncomputable def qjN (N : ℕ) [NeZero N] : ℍ → ℂ :=
  fun z => qj ⟨(↑N : ℂ) * (z : ℂ), natCast_mul_im_pos N z⟩

lemma natCast_mul_ofComplex_coe (N : ℕ) [NeZero N] {w : ℂ} (hw : 0 < w.im) :
    (⟨(↑N : ℂ) * (UpperHalfPlane.ofComplex w : ℂ),
        natCast_mul_im_pos N (UpperHalfPlane.ofComplex w)⟩ : ℍ) =
      UpperHalfPlane.ofComplex ((↑N : ℂ) * w) := by
  have hNw : 0 < ((↑N : ℂ) * w).im := by
    rw [Complex.mul_im]
    simp only [natCast_re, natCast_im, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr (NeZero.pos N)) hw
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_mk, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
    UpperHalfPlane.ofComplex_apply_of_im_pos hNw]

lemma qjN_periodic (N : ℕ) [NeZero N] : Periodic (qjN N ∘ UpperHalfPlane.ofComplex) N := by
  have hqNN : Periodic (qj ∘ UpperHalfPlane.ofComplex) ((↑N : ℂ) * ↑N) := by
    have := qj_periodic.nat_mul (N * N)
    simpa [Nat.cast_mul] using this
  intro w
  simp only [Function.comp, qjN]
  by_cases hw : 0 < Complex.im w
  · have hwN : 0 < Complex.im (w + ↑N) := by simp [Complex.add_im]; linarith
    have hkey := hqNN ((↑N : ℂ) * w)
    rw [show (↑N : ℂ) * w + (↑N : ℂ) * ↑N = (↑N : ℂ) * (w + ↑N) from by ring] at hkey
    simp only [Function.comp] at hkey
    rw [natCast_mul_ofComplex_coe N hwN, natCast_mul_ofComplex_coe N hw]
    exact hkey
  · have hw0 := le_of_not_gt hw
    have hwN : Complex.im (w + ↑N) ≤ 0 := by simp [Complex.add_im]; linarith
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos hw0,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hwN]

lemma qjN_holomorphic (N : ℕ) [NeZero N] :
    ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (qjN N ∘ UpperHalfPlane.ofComplex) z := by
  intro z hz
  have hNz : 0 < Complex.im ((↑N : ℂ) * z) := by
    rw [Complex.mul_im]
    simp only [natCast_re, natCast_im, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr (NeZero.pos N)) hz
  have hqj := qj_holomorphic _ hNz
  have hN : DifferentiableAt ℂ (fun w => (↑N : ℂ) * w) z :=
    (differentiableAt_const _).mul differentiableAt_id
  refine (hqj.comp z hN).congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz] with w hw
  simp only [Function.comp, qjN]
  rw [natCast_mul_ofComplex_coe N hw]

lemma qjN_MDifferentiable (N : ℕ) [NeZero N] : MDiff (qjN N) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  exact (qjN_holomorphic N z hz).differentiableWithinAt

lemma qjN_IsBoundedAtImInfty (N : ℕ) [NeZero N] :
    IsBoundedAtImInfty (qjN N) := by
  apply qj_IsBoundedAtImInfty.comp_tendsto
  rw [show atImInfty = Filter.comap UpperHalfPlane.im
    Filter.atTop from rfl, Filter.tendsto_comap_iff]
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr (NeZero.pos N)
  have him_eq :
      UpperHalfPlane.im ∘
          (fun x : ℍ =>
            (⟨(↑N : ℂ) * (x : ℂ), natCast_mul_im_pos N x⟩ : ℍ)) =
        (fun x : ℝ => (↑N : ℝ) * x) ∘ UpperHalfPlane.im := by
    ext τ
    simp only [Function.comp, UpperHalfPlane.im, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, zero_mul, add_zero]
  rw [him_eq]
  exact (Filter.Tendsto.const_mul_atTop hN_pos Filter.tendsto_id).comp Filter.tendsto_comap

lemma qjN_cuspFunction_analyticAt (N : ℕ) [NeZero N] : AnalyticAt ℂ (cuspFunction N (qjN N)) 0 :=
  DifferentiableOn.analyticAt (fun q hq => (UpperHalfPlane.differentiableOn_cuspFunction_ball
    (Nat.cast_pos.mpr (NeZero.pos N)) (qjN_periodic N)
    (qjN_MDifferentiable N) (qjN_IsBoundedAtImInfty N)) q hq)
      (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

lemma jN_cuspFunction_eq (N : ℕ) [NeZero N] {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    cuspFunction N (jN N) q = q⁻¹ ^ (N * N) * cuspFunction N (qjN N) q := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have him := Periodic.im_invQParam_pos_of_norm_lt_one hN hq hq0
  let τ : ℍ := ⟨Periodic.invQParam N q, him⟩
  have hjN_eq : cuspFunction N (jN N) q = jN N τ := by
    change Periodic.cuspFunction N _ q = _
    rw [Periodic.cuspFunction_eq_of_nonzero N _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hqjN_eq : cuspFunction N (qjN N) q = qjN N τ := by
    change Periodic.cuspFunction N _ q = _
    rw [Periodic.cuspFunction_eq_of_nonzero N _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hcexp :
      cexp (2 * ↑π * Complex.I *
        (↑(⟨(↑N : ℂ) * (τ : ℂ), natCast_mul_im_pos N τ⟩ : ℍ) : ℂ)) = q ^ (N * N) := by
    rw [UpperHalfPlane.coe_mk]
    have hNnzC : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    rw [show 2 * ↑π * Complex.I * ((↑N : ℂ) * (τ : ℂ)) = ↑(N * N) *
      (2 * ↑π * Complex.I * (τ : ℂ) / ↑N) from by field_simp [hNnzC]; push_cast; ring,
      Complex.exp_nat_mul]
    congr 1
    simpa [τ, Periodic.qParam] using Periodic.qParam_right_inv (ne_of_gt hN) hq0
  rw [hjN_eq, hqjN_eq]
  simp only [jN, qjN, qj, Pi.mul_apply]
  rw [hcexp, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq0), one_mul]

lemma jN_cuspFunction_Meromorphic (N : ℕ) [NeZero N] :
    MeromorphicAt (cuspFunction N (jN N)) (0 : ℂ) := by
  have hqjN_mer : MeromorphicAt (cuspFunction N (qjN N)) (0 : ℂ) := by
    change MeromorphicAt (Function.Periodic.cuspFunction N (qjN N ∘ UpperHalfPlane.ofComplex)) 0
    exact (qjN_cuspFunction_analyticAt N).meromorphicAt
  have hpow : MeromorphicAt (fun q : ℂ => q⁻¹ ^ (N * N)) (0 : ℂ) :=
    ((MeromorphicAt.id (0 : ℂ)).inv).pow _
  refine (hpow.mul hqjN_mer).congr ?_
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds (by simpa [Metric.ball, dist_eq_norm]
      using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hq hq'
  simp only [Pi.mul_apply]
  exact (jN_cuspFunction_eq N (by simpa using hq') hq).symm

lemma jN_Meromorphic (N : ℕ) [NeZero N] {z : ℍₒ} :
    DifferentiableAt ℂ (jN N ∘ UpperHalfPlane.ofComplex) z := by
  obtain ⟨z, hz⟩ := z
  have hz' := Set.mem_setOf.mp hz
  have hNz : 0 < Complex.im ((↑N : ℂ) * z) := by
    rw [Complex.mul_im]
    simp only [natCast_re, natCast_im, zero_mul, add_zero, Nat.cast_pos, NeZero.pos,
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
    simp only [Function.comp, jN, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (↑N * w).im by
        rw [Complex.mul_im]; simp only [natCast_re, natCast_im, zero_mul, add_zero, Nat.cast_pos,
            NeZero.pos, mul_pos_iff_of_pos_left]; exact hw)]
  change DifferentiableAt ℂ (jN N ∘ UpperHalfPlane.ofComplex) z
  have hcomp' : DifferentiableAt ℂ ((j ∘ UpperHalfPlane.ofComplex) ∘ fun w => (↑N : ℂ) * w) z := by
    convert hcomp using 2
  exact hcomp'.congr_of_eventuallyEq hEq
