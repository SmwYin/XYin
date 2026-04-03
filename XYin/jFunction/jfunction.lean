import XYin.jFunction.generalised
import XYin.jFunction.HasIntegralQExpansion
import XYin.jFunction.Deltaqexpansions
import XYin.jFunction.LaurentQExpansion

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups PowerSeries
  SlashInvariantFormClass Real Function IntegralPowerSeries

local notation "𝕢" => Periodic.qParam
local notation "ℍₒ" => upperHalfPlaneSet

noncomputable section

/-- This defines the `j` function as E4^3/Δ -/
def j : ℍ → ℂ := fun τ ↦ (E4 τ) ^ 3 / Delta τ

lemma j_slashInvariant (γ : SL(2, ℤ)) : j ∣[(0 : ℤ)] γ = j := by
  ext z
  rw [slash_action_eq'_iff, j, j]
  have h1 := congrFun (E4.slash_action_eq' γ (by refine
      (Subgroup.mem_map_iff_mem (Matrix.SpecialLinearGroup.mapGL_injective)).mpr (by apply
      CongruenceSubgroup.mem_Gamma_one ))) z
  have h2 := congrFun (Delta.slash_action_eq' γ (by refine
      (Subgroup.mem_map_iff_mem (Matrix.SpecialLinearGroup.mapGL_injective)).mpr (by apply
      CongruenceSubgroup.mem_Gamma_one ))) z
  rw [← ModularForm.SL_slash] at h1 h2
  simp only [ModularForm.slash_action_eq'_iff, Nat.cast_ofNat, SlashInvariantForm.toFun_eq_coe,
    toSlashInvariantForm_coe, Fin.isValue] at h1
  rw [ModularForm.slash_action_eq'_iff, CuspForm_apply, CuspForm_apply] at h2
  rw [h1, h2]
  ring_nf
  have h3 := pow_ne_zero  12 (denom_ne_zero γ z)
  rw [ModularGroup.denom_apply] at h3
  rw [← zpow_natCast, ← zpow_mul]
  ring_nf
  nth_rw 2 [mul_comm]
  rw [← mul_assoc]
  nth_rw 3 [mul_comm]
  rw [Complex.mul_inv_cancel]
  · simp
  · exact h3

def Deltaoverq : ℍ → ℂ := fun z ↦ ∏' (n : ℕ), (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24

lemma DeltaoverqIdentity : Deltaoverq = (fun z ↦ 1 / cexp (2 * π * Complex.I * z) : ℍ → ℂ) * Delta
    := by
  ext z
  simp [Deltaoverq, Delta_apply, Δ, Pi.mul_apply, mul_assoc]

lemma Deltaoverq_ne_zero (z : ℍ) : Deltaoverq z ≠ 0 := by
  intro h
  have hprod : ∏' (n : ℕ), (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24 = 0 := by
    simpa [Deltaoverq] using h
  apply Δ_ne_zero z
  simp [Δ, hprod]

def InfSumDeltashift : ℍ → ℂ :=
  fun z ↦ ∑' n : ℕ, (qExpansion 1 Delta).coeff (n + 1) * cexp (2 * π * Complex.I * z) ^ n

lemma InfSumDeltashift_eq_Deltaoverq : InfSumDeltashift = Deltaoverq := by
  ext z
  let q : ℂ := cexp (2 * π * Complex.I * z)
  let a : ℕ → ℂ := fun n => (qExpansion 1 Delta).coeff n * q ^ n
  have hcoeff0 : (qExpansion 1 Delta).coeff 0 = 0 := by simpa [qExpansion_coeff] using
      (CuspFormClass.cuspFunction_apply_zero Delta (by norm_num) one_mem_strictPeriods_SL2Z)
  have hq : q ≠ 0 := by simp [q]
  have hs : HasSum a (Delta z) := by simpa [a, q, smul_eq_mul, Periodic.qParam] using
      (hasSum_qExpansion Delta (by norm_num) one_mem_strictPeriods_SL2Z z)
  have hs_shift : HasSum (fun n => a (n + 1)) (Delta z) := by
    have hs' : HasSum (fun n => a (n + 1)) (Delta z - ∑ i ∈ Finset.range 1, a i) :=
      (hasSum_nat_add_iff' 1).2 hs
    simpa [a, q, hcoeff0] using hs'
  have hs_div :
      HasSum (fun n => (qExpansion 1 Delta).coeff (n + 1) * q ^ n) ((1 / q) * Delta z) := by
    have hs_mul : HasSum (fun n => (1 / q) * a (n + 1)) ((1 / q) * Delta z) :=
        (HasSum.mul_left (1 / q) hs_shift)
    simpa [a, q, hq, pow_succ, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hs_mul
  have h_overq : Deltaoverq z = (1 / q) * Delta z := by
    simp [Deltaoverq, Delta_apply, Δ, q, mul_assoc]
  calc
  _ = ∑' n : ℕ, (qExpansion 1 Delta).coeff (n + 1) * q ^ n := by simp [InfSumDeltashift, q]
  _ = (1 / q) * Delta z := hs_div.tsum_eq
  _ = _ := by simpa using h_overq.symm

lemma InfSumDeltashift_hasSum (z : ℍ) : HasSum
    (fun m => ((qExpansion 1 Delta).coeff (m + 1)) • 𝕢 1 (z : ℂ) ^ m) (InfSumDeltashift z) := by
  let q : ℂ := 𝕢 1 (z : ℂ)
  have hq : q ≠ 0 := by simp [q, Periodic.qParam]
  have hcoeff0 : (qExpansion 1 Delta).coeff 0 = 0 := by
    simpa [qExpansion_coeff] using
        (CuspFormClass.cuspFunction_apply_zero Delta (by norm_num) one_mem_strictPeriods_SL2Z)
  have hs : HasSum (fun m => (qExpansion 1 Delta).coeff m • q ^ m) (Delta z) := by
    simpa [q] using (hasSum_qExpansion Delta (by norm_num) one_mem_strictPeriods_SL2Z z)
  have hs_shift :
    HasSum (fun m => (qExpansion 1 Delta).coeff (m + 1) • q ^ (m + 1)) (Delta z) := by
    have hs' : HasSum (fun m => (qExpansion 1 Delta).coeff (m + 1) • q ^ (m + 1))
        (Delta z - ∑ i ∈ Finset.range 1, (qExpansion 1 Delta).coeff i • q ^ i) :=
      (hasSum_nat_add_iff' 1).2 hs
    simpa [q, hcoeff0] using hs'
  have hs_div : HasSum (fun m => (qExpansion 1 Delta).coeff (m + 1) • q ^ m) (q⁻¹ • Delta z) := by
    have hs_mul : HasSum (fun m => q⁻¹ • ((qExpansion 1 Delta).coeff (m + 1) • q ^ (m + 1)))
        (q⁻¹ • Delta z) := hs_shift.const_smul q⁻¹
    simpa [q, hq, smul_smul, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hs_mul
  have hval : InfSumDeltashift z = q⁻¹ • Delta z := by
    calc
    _ = ∑' m : ℕ, (qExpansion 1 Delta).coeff (m + 1) * cexp (2 * π * Complex.I * z) ^ m := by
      simp [InfSumDeltashift]
    _ = ∑' m : ℕ, (qExpansion 1 Delta).coeff (m + 1) • q ^ m := by
      simp [q, Periodic.qParam, smul_eq_mul]
    _ = _ := hs_div.tsum_eq
  have hs_div' : HasSum (fun m => (qExpansion 1 Delta).coeff (m + 1) * 𝕢 1 (z : ℂ) ^ m)
      ((𝕢 1 (z : ℂ))⁻¹ * Delta z) := by
    simpa [q, smul_eq_mul] using hs_div
  have hval' : InfSumDeltashift z = (𝕢 1 (z : ℂ))⁻¹ * Delta z := by simp [q, smul_eq_mul, hval]
  simpa [hval'] using hs_div'

lemma cuspFunction_InfSumDeltashift_hasSum : ∀ {q : ℂ}, ‖q‖ < 1 → q ≠ 0 →
    HasSum (fun n ↦ ((qExpansion 1 Delta).coeff (n + 1)) • q ^ n)
      (cuspFunction 1 InfSumDeltashift q) := by
  intro q hq hq0
  let τ : ℍ := ⟨Periodic.invQParam 1 q,
    Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num : 0 < (1 : ℝ)) hq hq0⟩
  have hqparam : 𝕢 1 (τ : ℂ) = q := by
    simpa [τ] using Periodic.qParam_right_inv (by norm_num : (1 : ℝ) ≠ 0) hq0
  have hcusp : cuspFunction 1 InfSumDeltashift q = InfSumDeltashift τ := by
    have him : 0 < Complex.im (Periodic.invQParam 1 q) :=
      Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num : 0 < (1 : ℝ)) hq hq0
    change Periodic.cuspFunction 1 (InfSumDeltashift ∘ UpperHalfPlane.ofComplex) q =
      InfSumDeltashift τ
    rw [Periodic.cuspFunction_eq_of_nonzero 1 _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  simpa [hqparam, hcusp] using (InfSumDeltashift_hasSum τ)

lemma cuspFunction_InfSumDeltashift_zero_term : cuspFunction 1 InfSumDeltashift 0 = 1 := by
  have hlim : Tendsto InfSumDeltashift atImInfty (nhds (1 : ℂ)) := by
    rw [InfSumDeltashift_eq_Deltaoverq]
    simpa [Deltaoverq] using Delta_boundedfactor
  have hcomp : Tendsto
      ((((fun τ : ℍ => InfSumDeltashift τ) ∘ UpperHalfPlane.ofComplex) ∘
        Periodic.invQParam (1 : ℝ)))
      (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (1 : ℂ)) := by
    have hInv := Periodic.invQParam_tendsto (h := (1 : ℝ)) (by norm_num)
    exact hlim.comp (tendsto_comap_im_ofComplex.comp hInv)
  simpa [cuspFunction, Periodic.cuspFunction, comp_def] using
      (Tendsto.limUnder_eq hcomp)

lemma InfSumDeltashift_AnalyticAt : AnalyticAt ℂ (cuspFunction 1 InfSumDeltashift) 0 := by
  let cshift : ℕ → ℂ := fun m => (qExpansion 1 Delta).coeff (m + 1)
  have hs_cusp : ∀ {q : ℂ}, ‖q‖ < 1 → q ≠ 0 →
      HasSum (fun n ↦ cshift n • q ^ n) (cuspFunction 1 InfSumDeltashift q) := by
    simp only [cshift]
    exact cuspFunction_InfSumDeltashift_hasSum
  have Hupd : HasFPowerSeriesOnBall (update (cuspFunction 1 InfSumDeltashift) 0 (cshift 0))
      (.ofScalars ℂ cshift) 0 1 := by
    constructor
    · refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
      rcases eq_or_ne r 0 with rfl | hr'
      · simp
      · lift r to NNReal using hr.ne_top
        apply FormalMultilinearSeries.le_radius_of_summable
        simpa [norm_smul] using
          (hs_cusp (q := r) (by simpa using hr) (mod_cast hr')).summable.norm
    · simp
    · intro y hy
      rw [zero_add]
      rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
      rcases eq_or_ne y 0 with rfl | hy'
      · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (cshift 0)
      · simpa [update_of_ne hy', mul_comm] using hs_cusp (q := y) hy hy'
  have hc0 : cshift 0 = 1 := by
    simpa [cshift] using Delta_q_one_term
  have h0 : cshift 0 = cuspFunction 1 InfSumDeltashift 0 := by
    simp [hc0, cuspFunction_InfSumDeltashift_zero_term]
  have Hcusp :
      HasFPowerSeriesOnBall (cuspFunction 1 InfSumDeltashift) (.ofScalars ℂ cshift) 0 1 := by
    rwa [update_eq_self_iff.mpr h0] at Hupd
  exact Hcusp.hasFPowerSeriesAt.analyticAt

lemma InfSumDeltashift_coeff_eq (n : ℕ) :
    (qExpansion 1 InfSumDeltashift).coeff n = (qExpansion 1 Delta).coeff (n + 1) := by
  let cshift : ℕ → ℂ := fun m => (qExpansion 1 Delta).coeff (m + 1)
  simpa [cshift] using (qExpansion_coeff_unique'
      (by norm_num) InfSumDeltashift_AnalyticAt InfSumDeltashift_hasSum n).symm

lemma DeltaoverqIsIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 Deltaoverq) := by
  rw [int_iff]
  intro n
  let IntegralDelta : PowerSeries ℤ :=
    toIntegralPowerSeries DeltaIsIntegralPowerSeries
  use IntegralDelta.coeff (n + 1)
  have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
    simpa using qExpansion_ext Deltaoverq InfSumDeltashift
      (InfSumDeltashift_eq_Deltaoverq.symm)
  have hshift : (qExpansion 1 Deltaoverq).coeff n = (qExpansion 1 Delta).coeff (n + 1) := by
    calc
     _ = (qExpansion 1 InfSumDeltashift).coeff n := by simp [hq]
    _ = _ := InfSumDeltashift_coeff_eq n
  have hgcoeff : ((IntegralDelta.coeff (n + 1) : ℤ) : ℂ) = (qExpansion 1 Delta).coeff (n + 1) := by
    exact congrArg (PowerSeries.coeff (n + 1))
      (coeTo_of_toIntegralPowerSeries DeltaIsIntegralPowerSeries)
  calc
    _ = (qExpansion 1 Delta).coeff (n + 1) := hshift
    _ = _ := by simpa using hgcoeff.symm

def integralDeltaoverq : PowerSeries ℤ := toIntegralPowerSeries DeltaoverqIsIntegralPowerSeries

lemma coeTo_of_integralDeltaoverq :
    coeToComplexPowerSeries.ringHom integralDeltaoverq = qExpansion 1 Deltaoverq := by
  exact coeTo_of_toIntegralPowerSeries DeltaoverqIsIntegralPowerSeries

lemma integralDeltaoverq_constantCoeff_isUnit : IsUnit (constantCoeff integralDeltaoverq : ℤ) := by
  have hlim : Tendsto Deltaoverq atImInfty (nhds (1 : ℂ)) := by
    simpa [Deltaoverq] using Delta_boundedfactor
  have hcomp : Tendsto ((((fun τ : ℍ => Deltaoverq τ) ∘ UpperHalfPlane.ofComplex) ∘
      Periodic.invQParam (1 : ℝ))) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (1 : ℂ)) := by
    have hInv := Periodic.invQParam_tendsto (h := (1 : ℝ)) (by norm_num)
    exact hlim.comp (tendsto_comap_im_ofComplex.comp hInv)
  have hcusp0 : cuspFunction 1 Deltaoverq 0 = 1 := by
    simpa [cuspFunction, Periodic.cuspFunction, comp_def] using (Tendsto.limUnder_eq hcomp)
  have hcoeff0C : (qExpansion 1 Deltaoverq).coeff 0 = 1 := by simp [qExpansion_coeff, hcusp0]
  have hcast : ((constantCoeff integralDeltaoverq : ℤ) : ℂ) = 1 := by
    have h0 := congrArg (PowerSeries.coeff 0) coeTo_of_integralDeltaoverq
    simpa [coeToComplexPowerSeries.ringHom, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hcoeff0C] using h0
  have hZ : (constantCoeff integralDeltaoverq : ℤ) = 1 := by
    norm_num at hcast ⊢
    exact_mod_cast hcast
  simp [hZ]

lemma integralDeltaoverq_isUnit : IsUnit (integralDeltaoverq) := by
  exact PowerSeries.isUnit_iff_constantCoeff (φ := integralDeltaoverq).mpr
      integralDeltaoverq_constantCoeff_isUnit

def qoverDelta : ℍ → ℂ := fun z ↦ 1 / Deltaoverq z

def qj : ℍ → ℂ := (fun z ↦ cexp (2 * π * Complex.I * z) : ℍ → ℂ) * j

lemma qjIdentity : E4 ^ 3 * qoverDelta = qj := by
  ext z
  change (E4 z) ^ 3 * qoverDelta z = cexp (2 * π * Complex.I * z) * ((E4 z) ^ 3 / Delta z)
  have hDq : Deltaoverq z = (1 / cexp (2 * π * Complex.I * z)) * Delta z := by
    simpa [Pi.mul_apply] using congrFun DeltaoverqIdentity z
  have hDnz : Delta z ≠ 0 := by simpa [Delta_apply] using (Δ_ne_zero z)
  have hExpNz : cexp (2 * π * Complex.I * z) ≠ 0 := by exact Complex.exp_ne_zero _
  have hqoz : qoverDelta z = cexp (2 * π * Complex.I * z) / Delta z := by
    rw [qoverDelta, hDq]
    field_simp [hDnz, hExpNz]
  calc
  _ = (E4 z) ^ 3 * (cexp (2 * π * Complex.I * z) / Delta z) := by rw [hqoz]
  _ = _ := by ring

lemma Deltaoverq_AnalyticAt : AnalyticAt ℂ (cuspFunction 1 Deltaoverq) 0 := by
  simpa [InfSumDeltashift_eq_Deltaoverq] using InfSumDeltashift_AnalyticAt

lemma Deltaoverq_tendsto_atImInfty : Tendsto Deltaoverq atImInfty (nhds (1 : ℂ)) := by
  simpa [Deltaoverq] using Delta_boundedfactor

lemma qoverDelta_tendsto_atImInfty : Tendsto qoverDelta atImInfty (nhds (1 : ℂ)) := by
  have h : Tendsto (fun τ : ℍ => (Deltaoverq τ)⁻¹) atImInfty (nhds ((1 : ℂ)⁻¹)) :=
    Deltaoverq_tendsto_atImInfty.inv₀ (by norm_num)
  change Tendsto (fun τ : ℍ => (1 / Deltaoverq τ)) atImInfty (nhds (1 : ℂ))
  simpa [one_div] using h

lemma cuspFunction_Deltaoverq_zero : cuspFunction 1 Deltaoverq 0 = 1 := by
  have hcompD : Tendsto ((((fun τ : ℍ => Deltaoverq τ) ∘ UpperHalfPlane.ofComplex) ∘
      Periodic.invQParam (1 : ℝ))) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (1 : ℂ)) := by
    have hInv := Periodic.invQParam_tendsto (h := (1 : ℝ)) (by norm_num)
    exact Deltaoverq_tendsto_atImInfty.comp (tendsto_comap_im_ofComplex.comp hInv)
  simpa [cuspFunction, Periodic.cuspFunction, comp_def] using (Tendsto.limUnder_eq hcompD)

lemma cuspFunction_qoverDelta_zero : cuspFunction 1 qoverDelta 0 = 1 := by
  have h : Tendsto ((((fun τ : ℍ => qoverDelta τ) ∘ UpperHalfPlane.ofComplex) ∘
      Periodic.invQParam (1 : ℝ))) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (1 : ℂ)) := by
    have hInv := Periodic.invQParam_tendsto (h := (1 : ℝ)) (by norm_num)
    exact qoverDelta_tendsto_atImInfty.comp (tendsto_comap_im_ofComplex.comp hInv)
  simpa [cuspFunction, Periodic.cuspFunction, comp_def] using (Tendsto.limUnder_eq h)

lemma cuspFunction_qoverDelta_EqInv :
    cuspFunction 1 qoverDelta = fun q => (cuspFunction 1 Deltaoverq q)⁻¹ := by
  funext q
  by_cases hq : q = 0
  · simp [hq, cuspFunction_Deltaoverq_zero, cuspFunction_qoverDelta_zero]
  · simp [cuspFunction, Periodic.cuspFunction, hq, qoverDelta]

lemma Deltaoverq_Inv_AnalyticAt : AnalyticAt ℂ (fun q => (cuspFunction 1 Deltaoverq q)⁻¹) 0 := by
  exact Deltaoverq_AnalyticAt.inv (by simp [cuspFunction_Deltaoverq_zero])

lemma qoverDelta_AnalyticAt : AnalyticAt ℂ (cuspFunction 1 qoverDelta) 0 := by
  simpa [cuspFunction_qoverDelta_EqInv] using Deltaoverq_Inv_AnalyticAt

lemma E4_AnalyticAt : AnalyticAt ℂ (cuspFunction 1 E4) 0 := by
  exact analyticAt_cuspFunction_zero E4 (by norm_num) one_mem_strictPeriods_SL2Z

lemma E4cubed_isModularForm : ∃ f : ModularForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
    (CongruenceSubgroup.Gamma 1)) 12, (f : ℍ → ℂ) = E4 ^ 3 := by
  refine ⟨E4.mul (E4.mul E4), ?_⟩
  funext z
  simpa [pow_three] using congrFun (ModularForm.coe_mul E4 (E4.mul E4)) z

lemma E4cubed_AnalyticAt : AnalyticAt ℂ (cuspFunction 1 (E4 ^ 3)) 0 := by
  rcases E4cubed_isModularForm with ⟨f, hf⟩
  simpa [hf] using (analyticAt_cuspFunction_zero f (by norm_num) one_mem_strictPeriods_SL2Z)

lemma integralDeltaoverq_mul_qoverDelta_qExpansion :
    coeToComplexPowerSeries.ringHom integralDeltaoverq * qExpansion 1 qoverDelta = 1 := by
  rw [coeTo_of_integralDeltaoverq]
  have h :
      qExpansion 1 (Deltaoverq * qoverDelta) = qExpansion 1 Deltaoverq * qExpansion 1 qoverDelta
      := by
    apply qExpansion_mul
    · exact Deltaoverq_AnalyticAt
    · exact qoverDelta_AnalyticAt
  rw [←h]
  have h2 : Deltaoverq * qoverDelta = 1 := by
    ext z
    rw [Pi.mul_def]
    simp [qoverDelta, Deltaoverq_ne_zero]
  rw [h2]
  ext z
  rw [qExpansion_coeff]
  by_cases hz : z = 0
  · simp only [hz, Nat.factorial_zero, Nat.cast_one, inv_one, SlashInvariantFormClass.cuspFunction,
        Pi.one_comp, iteratedDeriv_zero, one_mul, coeff_one, ↓reduceIte, Periodic.cuspFunction,
        Pi.one_comp, update_self]
    exact Tendsto.limUnder_eq tendsto_const_nhds
  · simp only [SlashInvariantFormClass.cuspFunction, Pi.one_comp, coeff_one, hz, ↓reduceIte,
        mul_eq_zero, _root_.inv_eq_zero, Nat.cast_eq_zero]
    right
    have h3 : Periodic.cuspFunction 1 (1 : ℂ → ℂ) = (fun _ : ℂ => (1 : ℂ)) := by
      funext y
      by_cases hy : y = 0
      · subst hy
        simp only [Periodic.cuspFunction, Pi.one_comp, update_self]
        exact Tendsto.limUnder_eq tendsto_const_nhds
      · simp [Periodic.cuspFunction, hy]
    rw [h3]
    simpa [hz] using iteratedDeriv_const (c := (1 : ℂ)) (x := 0) (n := z)

lemma qoverDeltaIsIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 qoverDelta) := by
  rw [IsIntegralPowerSeries]
  obtain ⟨u, hu⟩ := integralDeltaoverq_isUnit
  refine ⟨(↑(u⁻¹) : PowerSeries ℤ), ?_⟩
  have h : coeToComplexPowerSeries.ringHom integralDeltaoverq
      * coeToComplexPowerSeries.ringHom (↑(u⁻¹) : PowerSeries ℤ) = 1 := by
    calc
    _ = coeToComplexPowerSeries.ringHom (↑u)
        * coeToComplexPowerSeries.ringHom (↑(u⁻¹) : PowerSeries ℤ) := by simp [hu]
    _ = coeToComplexPowerSeries.ringHom ((↑u) * (↑(u⁻¹) : PowerSeries ℤ)) := by
      rw [← map_mul]
    _ = _ := by simp
  symm
  calc
  _ = 1 * qExpansion 1 qoverDelta := by simp
  _ = (coeToComplexPowerSeries.ringHom integralDeltaoverq * coeToComplexPowerSeries.ringHom
      (↑(u⁻¹) : PowerSeries ℤ)) * qExpansion 1 qoverDelta := by simp [h]
  _ = coeToComplexPowerSeries.ringHom (↑(u⁻¹) : PowerSeries ℤ) * (coeToComplexPowerSeries.ringHom
      integralDeltaoverq * qExpansion 1 qoverDelta) := by ring
  _ = _ := by simp [integralDeltaoverq_mul_qoverDelta_qExpansion]

lemma qjauxIsIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3 * qoverDelta)) := by
  simp [qExpansion_mul E4cubed_AnalyticAt qoverDelta_AnalyticAt, IsIntegralPowerSeries,
    IntegralPowerSeriesSubring.mul_mem E4CubedIsIntegralPowerSeries qoverDeltaIsIntegralPowerSeries]

theorem qjIsIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 qj) := by
  simpa using qjIdentity ▸ qjauxIsIntegralPowerSeries

def qj_coeffs : ℕ → ℤ := fun n => (toIntegralPowerSeries qjIsIntegralPowerSeries).coeff n

def InfSumqj : ℍ → ℂ :=
    fun z ↦ ∑' n : ℕ, (qExpansion 1 qj).coeff n * cexp (2 * π * Complex.I * z) ^ n

lemma qj_periodic : Periodic (qj ∘ UpperHalfPlane.ofComplex) 1 := by
  intro w
  by_cases hw : 0 < Complex.im w
  · have hw1 : 0 < Complex.im (w + 1) := by simpa using hw
    let τ : ℍ := ⟨w, hw⟩
    have hτ1 : ((1 : ℝ) +ᵥ τ : ℍ) = UpperHalfPlane.ofComplex (w + 1) := by
      apply UpperHalfPlane.ext
      simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos hw1, UpperHalfPlane.coe_vadd, add_comm]
    have hE4 : E4 ((1 : ℝ) +ᵥ τ) = E4 τ := by
      simpa using
        (SlashInvariantForm.vAdd_apply_of_mem_strictPeriods (f := E4) (τ := τ)
          (hH := one_mem_strictPeriods_SL2Z))
    have hDelta : Delta ((1 : ℝ) +ᵥ τ) = Delta τ := by
      simpa using
        (SlashInvariantForm.vAdd_apply_of_mem_strictPeriods (f := Delta) (τ := τ)
          (hH := one_mem_strictPeriods_SL2Z))
    have hj : j ((1 : ℝ) +ᵥ τ) = j τ := by
      simp [j, hE4, hDelta]
    have hexp :
        cexp (2 * π * Complex.I * (((1 : ℝ) +ᵥ τ : ℍ) : ℂ)) =
          cexp (2 * π * Complex.I * (τ : ℂ)) := by
      calc
      _ = cexp (2 * π * Complex.I * ((1 : ℂ) + (τ : ℂ))) := by simp [UpperHalfPlane.coe_vadd]
      _ = cexp (2 * π * Complex.I * (τ : ℂ) + 2 * π * Complex.I) := by ring_nf
      _ = cexp (2 * π * Complex.I * (τ : ℂ)) * cexp (2 * π * Complex.I) := by rw [Complex.exp_add]
      _ = _ := by simp [Complex.exp_two_pi_mul_I]
    have hqv : qj ((1 : ℝ) +ᵥ τ) = qj τ := by
      change cexp (2 * π * Complex.I * (((1 : ℝ) +ᵥ τ : ℍ) : ℂ)) * j ((1 : ℝ) +ᵥ τ) =
        cexp (2 * π * Complex.I * (τ : ℂ)) * j τ
      rw [hj, hexp]
    have hq : qj (UpperHalfPlane.ofComplex (w + 1)) = qj (UpperHalfPlane.ofComplex w) := by
      calc
      _ = qj ((1 : ℝ) +ᵥ τ) := by rw [← hτ1]
      _ = qj τ := hqv
      _ = _ := by simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    simpa [comp] using hq
  · have hw0 : Complex.im w ≤ 0 := le_of_not_gt hw
    have hw1 : Complex.im (w + 1) ≤ 0 := by simpa using hw0
    simp [comp, UpperHalfPlane.ofComplex_apply_of_im_nonpos hw1,
        UpperHalfPlane.ofComplex_apply_of_im_nonpos hw0]

lemma qj_holomorphic : ∀ z : ℂ, 0 < Complex.im z →
    DifferentiableAt ℂ (qj ∘ UpperHalfPlane.ofComplex) z := by
  intro z hz
  have hexp := (Complex.differentiableAt_exp.comp z ((differentiableAt_id :
      DifferentiableAt ℂ (fun w : ℂ ↦ w) z).const_mul (2 * π * Complex.I)))
  have hEqExp : (((fun τ : ℍ ↦ cexp (2 * π * Complex.I * (τ : ℂ))) ∘ UpperHalfPlane.ofComplex)
      =ᶠ[nhds z] (fun w : ℂ ↦ cexp (2 * π * Complex.I * w))) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz] with w hw
    simp [comp, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have hexpH : DifferentiableAt ℂ
      (((fun τ : ℍ ↦ cexp (2 * π * Complex.I * (τ : ℂ))) ∘ UpperHalfPlane.ofComplex)) z := by
    exact hexp.congr_of_eventuallyEq hEqExp
  have hE4 : DifferentiableAt ℂ (E4 ∘ UpperHalfPlane.ofComplex) z :=
    ModularFormClass.differentiableAt_comp_ofComplex (f := E4) hz
  have hDelta : DifferentiableAt ℂ (Delta ∘ UpperHalfPlane.ofComplex) z :=
    ModularFormClass.differentiableAt_comp_ofComplex (f := Delta) hz
  have hDelta0 : (Delta ∘ UpperHalfPlane.ofComplex) z ≠ 0 := by
    simpa [comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz, Delta_apply] using
      (Δ_ne_zero (UpperHalfPlane.ofComplex z))
  have hj : DifferentiableAt ℂ (j ∘ UpperHalfPlane.ofComplex) z := by
    simpa [j, comp] using (hE4.pow 3).div hDelta hDelta0
  simpa [qj, comp, Pi.mul_apply] using hexpH.mul hj

lemma E4_IsBoundedAtImInfty : IsBoundedAtImInfty E4 := by simp [ModularFormClass.bdd_at_infty]

lemma E4cubed_IsBoundedAtImInfty : IsBoundedAtImInfty ((fun z : ℍ => (E4 z) ^ 3)) := by
  have hE4sq :
    IsBoundedAtImInfty (fun z : ℍ => E4 z * E4 z) := E4_IsBoundedAtImInfty.mul E4_IsBoundedAtImInfty
  have hE4cube' :
    IsBoundedAtImInfty (fun z : ℍ => E4 z * (E4 z * E4 z)) := E4_IsBoundedAtImInfty.mul hE4sq
  simpa [pow_three, mul_assoc] using hE4cube'

lemma qj_IsBoundedAtImInfty : IsBoundedAtImInfty qj := by
  have hqoverDelta : IsBoundedAtImInfty qoverDelta := by
    have hzero : ZeroAtFilter atImInfty (fun τ : ℍ => qoverDelta τ - 1) := by
      simpa [ZeroAtFilter, sub_eq_add_neg] using (qoverDelta_tendsto_atImInfty.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℍ => (1 : ℂ)) atImInfty (nhds (1 : ℂ))))
    have hbd0 : BoundedAtFilter atImInfty (fun τ : ℍ => qoverDelta τ - 1) :=
      hzero.boundedAtFilter
    have hbd1 : BoundedAtFilter atImInfty (fun _ : ℍ => (1 : ℂ)) :=
      const_boundedAtFilter atImInfty 1
    have hsum : BoundedAtFilter atImInfty (fun τ : ℍ => (qoverDelta τ - 1) + 1) :=
      hbd0.add hbd1
    simpa [IsBoundedAtImInfty, sub_eq_add_neg, add_assoc] using hsum
  have hqj' : IsBoundedAtImInfty ((fun z : ℍ => (E4 z) ^ 3) * qoverDelta) :=
    E4cubed_IsBoundedAtImInfty.mul hqoverDelta
  have hqjEq : ((fun z : ℍ => (E4 z) ^ 3) * qoverDelta) = qj := by
    ext z
    simpa [qj] using congrFun qjIdentity z
  simpa [hqjEq] using hqj'

lemma hasSum_qExpansion_qj {τ : ℍ} :
    HasSum (fun m : ℕ ↦ (qExpansion 1 qj).coeff m • 𝕢 1 τ ^ m) (qj τ) := by
  exact hasSum_qExpansion' (by positivity) qj_periodic qj_holomorphic qj_IsBoundedAtImInfty τ

lemma InfSumqj_Summable {z : ℍ} :
    Summable (fun n : ℕ => (qj_coeffs n) * cexp (2 * π * Complex.I * z) ^ n) := by
  have hs0 : Summable (fun n : ℕ => (qExpansion 1 qj).coeff n * cexp (2 * π * Complex.I * z) ^ n)
      := by
    have hs : HasSum (fun m : ℕ => (qExpansion 1 qj).coeff m • 𝕢 (1 : ℝ) z ^ m) (qj z) := by
      simpa using hasSum_qExpansion_qj
    have hs' : HasSum (fun m : ℕ => (qExpansion 1 qj).coeff m * cexp (2 * π * Complex.I * z) ^ m)
        (qj z) := by
      simpa [smul_eq_mul, Periodic.qParam] using hs
    exact hs'.summable
  have hcoeff : ∀ n : ℕ, ((qj_coeffs n : ℤ) : ℂ) = (qExpansion 1 qj).coeff n := by
    intro n
    exact congrArg (PowerSeries.coeff n) (coeTo_of_toIntegralPowerSeries qjIsIntegralPowerSeries)
  refine hs0.congr ?_
  intro n
  simp [hcoeff n]

lemma InfSumqj_eq_qj : InfSumqj = qj := by
  funext z
  have hs : HasSum (fun m : ℕ => (qExpansion 1 qj).coeff m * cexp (2 * π * Complex.I * z) ^ m)
      (qj z) := by
    have hs0 : HasSum (fun m : ℕ => (qExpansion 1 qj).coeff m • 𝕢 (1 : ℝ) z ^ m) (qj z) := by
      simpa using hasSum_qExpansion_qj
    simpa [smul_eq_mul, Periodic.qParam] using hs0
  have hcoeff :
      ∀ n : ℕ, ((qj_coeffs n : ℤ) : ℂ) = (qExpansion 1 qj).coeff n := by
    intro n
    exact congrArg (PowerSeries.coeff n) (coeTo_of_toIntegralPowerSeries qjIsIntegralPowerSeries)
  have hs' : HasSum (fun n : ℕ => (qj_coeffs n) * cexp (2 * π * Complex.I * z) ^ n) (qj z) := by
    have h_eq : (fun n : ℕ => (qExpansion 1 qj).coeff n * cexp (2 * π * Complex.I * z) ^ n)
        = (fun n : ℕ => (qj_coeffs n) * cexp (2 * π * Complex.I * z) ^ n) := by
      funext n
      simp [hcoeff n]
    simpa [h_eq] using hs
  calc
  InfSumqj z = ∑' n : ℕ, (qj_coeffs n) * cexp (2 * π * Complex.I * z) ^ n := by
    calc
    _ = ∑' n : ℕ, (qExpansion 1 qj).coeff n * cexp (2 * π * Complex.I * z) ^ n := by
      simp [InfSumqj]
    _ = ∑' n : ℕ, (qj_coeffs n) * cexp (2 * π * Complex.I * z) ^ n := by
      refine tsum_congr ?_
      intro n
      simp [hcoeff n]
  _ = qj z := hs'.tsum_eq

lemma qj_exp : ∀ z : ℍ, qj z =
    ∑' n, (qj_coeffs n) * cexp (2 * π * Complex.I * z) ^ n := by
  intro z
  have hcoeff : ∀ n : ℕ, ((qj_coeffs n : ℤ) : ℂ) = (qExpansion 1 qj).coeff n := by
    intro n
    exact congrArg (PowerSeries.coeff n) (coeTo_of_toIntegralPowerSeries qjIsIntegralPowerSeries)
  calc
  _ = InfSumqj z := by simp [InfSumqj_eq_qj]
  _ = ∑' n : ℕ, (qExpansion 1 qj).coeff n * cexp (2 * π * Complex.I * z) ^ n := by
    simp [InfSumqj]
  _ = ∑' n : ℕ, (qj_coeffs n) * cexp (2 * π * Complex.I * z) ^ n := by
    refine tsum_congr ?_
    intro n
    simp [hcoeff n]

lemma qj_exp' : ∃ (c : ℕ → ℤ), ∀ z : ℍ, qj z = ∑' n, (c n) * cexp (2 * π * Complex.I * z) ^ n := by
  refine ⟨qj_coeffs, ?_⟩
  exact qj_exp

lemma qj_exp_dvd (z : ℍ) : qj z / cexp (2 * π * Complex.I * z) =
    (∑' n, (qj_coeffs n) * cexp (2 * π * Complex.I * z) ^ n) / cexp (2 * π * Complex.I * z) := by
  exact congrArg (fun w : ℂ => w / cexp (2 * π * Complex.I * z)) (qj_exp z)

lemma cancelout1 (z : ℍ) : qj z / cexp (2 * π * Complex.I * z) = j z := by
  simp [qj]

lemma cancelout2 (z : ℍ) :
    (∑' n, (qj_coeffs n) * cexp (2 * π * Complex.I * z) ^ n) / cexp (2 * π * Complex.I * z)
    = (qj_coeffs 0 / cexp (2 * π * Complex.I * z)) +
    ∑' n, (qj_coeffs (n + 1)) * cexp (2 * π * Complex.I * z) ^ n := by
  let q : ℂ := cexp (2 * π * Complex.I * z)
  have hq : q ≠ 0 := by simp [q]
  have hsplit : (∑' n, (qj_coeffs n) * q ^ n)
        = (qj_coeffs 0) * q ^ 0 + ∑' n, (qj_coeffs (n + 1)) * q ^ (n + 1) := by
    simpa [q] using InfSumqj_Summable.tsum_eq_zero_add
  have hdiv : (∑' n, (qj_coeffs n) * q ^ n) / q
      = ((qj_coeffs 0) * q ^ 0 + ∑' n, (qj_coeffs (n + 1)) * q ^ (n + 1)) / q := by
    exact congrArg (fun w : ℂ => w / q) hsplit
  calc
  _ = ((qj_coeffs 0) * q ^ 0) / q + (∑' n, (qj_coeffs (n + 1)) * q ^ (n + 1)) / q := by
    simpa [add_div] using hdiv
  _ = (qj_coeffs 0 / q) + ∑' n, ((qj_coeffs (n + 1)) * q ^ (n + 1)) / q := by
    rw [tsum_div_const]
    simp
  _ = (qj_coeffs 0 / q) + ∑' n, (qj_coeffs (n + 1)) * q ^ n := by
    congr 1
    refine tsum_congr ?_
    intro n
    rw [pow_succ]
    field_simp [hq, mul_assoc]
  _ = _ := by simp [q]

lemma qj_exp_zero : (qExpansion 1 qj).coeff 0 = 1 := by
  have hqj : qExpansion 1 qj = qExpansion 1 (E4 ^ 3 * qoverDelta) := by
    simpa [qj] using congrArg (qExpansion 1) qjIdentity.symm
  have hmul :
      qExpansion 1 (E4 ^ 3 * qoverDelta) = qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta := by
    exact qExpansion_mul E4cubed_AnalyticAt qoverDelta_AnalyticAt
  have hE4pow : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E4 3
  have hE4coeff0 : (qExpansion 1 E4).coeff 0 = 1 := by
    simpa [E4] using congr_fun E4_q_exp 0
  have hE4pow0 : (qExpansion 1 (E4 ^ 3)).coeff 0 = 1 := by
    rw [hE4pow]
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE4coeff0
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hE4const]
  have hqover0 : (qExpansion 1 qoverDelta).coeff 0 = 1 := by
    simp [qExpansion_coeff, cuspFunction_qoverDelta_zero]
  calc
  _ = (qExpansion 1 (E4 ^ 3 * qoverDelta)).coeff 0 := by rw [hqj]
  _ = (qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta).coeff 0 := by rw [hmul]
  _ = (qExpansion 1 (E4 ^ 3)).coeff 0 * (qExpansion 1 qoverDelta).coeff 0 := by simp
  _ = _ := by simp [hE4pow0, hqover0]

lemma qj_exp_zero' : qj_coeffs 0 = 1 := by
  have h0 : ((qj_coeffs 0 : ℤ) : ℂ) = (qExpansion 1 qj).coeff 0 := by
    simpa [qj_coeffs] using
        congrArg (PowerSeries.coeff 0) (coeTo_of_toIntegralPowerSeries qjIsIntegralPowerSeries)
  have h1 : ((qj_coeffs 0 : ℤ) : ℂ) = 1 := by
    calc
    _ = (qExpansion 1 qj).coeff 0 := h0
    _ = _ := qj_exp_zero
  exact_mod_cast h1

lemma Delta_exp_two : (qExpansion 1 Delta).coeff 2 = -24 := by
  have hDeltaaux2 := congrArg (PowerSeries.coeff 2) Deltaaux
  have hqsub : qExpansion 1 (E4 ^ 3 - E6 ^ 2) = qExpansion 1 (E4 ^ 3) - qExpansion 1 (E6 ^ 2) := by
    calc
      _ = qExpansion 1 ((E4.mul (E4.mul E4)) - (E6.mul E6)) := by
        have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := by rfl
        have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := by rfl
        simp [pow_three, pow_two, hf, hg]
      _ = qExpansion 1 (E4.mul (E4.mul E4)) - qExpansion 1 (E6.mul E6) := by
        simpa using (_root_.qExpansion_sub (h := (1 : ℝ)) (hh := by norm_num)
          (hΓ := one_mem_strictPeriods_SL2Z) (f := E4.mul (E4.mul E4)) (g := E6.mul E6))
      _ = _ := by
        have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := by rfl
        have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := by rfl
        simp [pow_three, pow_two, hf, hg]
  have hE4pow : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E4 3
  have hE6pow : qExpansion 1 (E6 ^ 2) = (qExpansion 1 E6) ^ 2 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (6 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E6 2
  have hE40 : (qExpansion 1 E4).coeff 0 = 1 := by
    simpa [E4] using congr_fun E4_q_exp 0
  have hE41 : (qExpansion 1 E4).coeff 1 = 240 := by
    simpa [E4] using congr_fun E4_q_exp 1
  have hE42 : (qExpansion 1 E4).coeff 2 = 2160 := by
    have h := congr_fun E4_q_exp 2
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE60 : (qExpansion 1 E6).coeff 0 = 1 := by
    simpa [E6] using congr_fun E6_q_exp 0
  have hE61 : (qExpansion 1 E6).coeff 1 = -504 := by
    simpa [E6] using congr_fun E6_q_exp 1
  have hE62 : (qExpansion 1 E6).coeff 2 = -16632 := by
    have h := congr_fun E6_q_exp 2
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hantidiag2 : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hE4sq1 : (qExpansion 1 E4 ^ 2).coeff 1 = 480 := by
    rw [pow_two, PowerSeries.coeff_mul, antidiagonal_one]
    simp [hE40, hE41]
    norm_num
  have hE4sq2 : (qExpansion 1 E4 ^ 2).coeff 2 = 61920 := by
    rw [pow_two, PowerSeries.coeff_mul, hantidiag2]
    simp [hE40, hE41, hE42]
    norm_num
  have hE4mul1 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 1 = 480 := by
    simpa [pow_two] using hE4sq1
  have hE4mul2 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 2 = 61920 := by
    simpa [pow_two] using hE4sq2
  have hE4pow2 : (qExpansion 1 (E4 ^ 3)).coeff 2 = 179280 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, hantidiag2]
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    simp [hE40, hE41, hE42, hE4mul1, hE4mul2, hE4const]
    norm_num
  have hE6pow2 : (qExpansion 1 (E6 ^ 2)).coeff 2 = 220752 := by
    rw [hE6pow, pow_two, PowerSeries.coeff_mul, hantidiag2]
    simp [hE60, hE61, hE62]
    norm_num
  calc
    (qExpansion 1 Delta).coeff 2 = ((1 / 1728 : ℂ) • qExpansion 1 (E4 ^ 3 - E6 ^ 2)).coeff 2 := by
      simpa using hDeltaaux2
    _ = (1 / 1728 : ℂ) * (qExpansion 1 (E4 ^ 3 - E6 ^ 2)).coeff 2 := by simp
    _ = (1 / 1728 : ℂ) *
        ((qExpansion 1 (E4 ^ 3)).coeff 2 - (qExpansion 1 (E6 ^ 2)).coeff 2) := by
          simp [hqsub]
    _ = (1 / 1728 : ℂ) * (179280 - 220752) := by simp [hE4pow2, hE6pow2]
    _ = -24 := by norm_num

lemma Delta_exp_three : (qExpansion 1 Delta).coeff 3 = 252 := by
  have hDeltaaux3 := congrArg (PowerSeries.coeff 3) Deltaaux
  have hqsub : qExpansion 1 (E4 ^ 3 - E6 ^ 2) = qExpansion 1 (E4 ^ 3) - qExpansion 1 (E6 ^ 2) := by
    calc
      _ = qExpansion 1 ((E4.mul (E4.mul E4)) - (E6.mul E6)) := by
        have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := by rfl
        have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := by rfl
        simp [pow_three, pow_two, hf, hg]
      _ = qExpansion 1 (E4.mul (E4.mul E4)) - qExpansion 1 (E6.mul E6) := by
        simpa using (_root_.qExpansion_sub (h := (1 : ℝ)) (hh := by norm_num)
          (hΓ := one_mem_strictPeriods_SL2Z) (f := E4.mul (E4.mul E4)) (g := E6.mul E6))
      _ = _ := by
        have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := by rfl
        have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := by rfl
        simp [pow_three, pow_two, hf, hg]
  have hE4pow : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E4 3
  have hE6pow : qExpansion 1 (E6 ^ 2) = (qExpansion 1 E6) ^ 2 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (6 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E6 2
  have hE40 : (qExpansion 1 E4).coeff 0 = 1 := by
    simpa [E4] using congr_fun E4_q_exp 0
  have hE41 : (qExpansion 1 E4).coeff 1 = 240 := by
    simpa [E4] using congr_fun E4_q_exp 1
  have hE42 : (qExpansion 1 E4).coeff 2 = 2160 := by
    have h := congr_fun E4_q_exp 2
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE43 : (qExpansion 1 E4).coeff 3 = 6720 := by
    have h := congr_fun E4_q_exp 3
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE60 : (qExpansion 1 E6).coeff 0 = 1 := by
    simpa [E6] using congr_fun E6_q_exp 0
  have hE61 : (qExpansion 1 E6).coeff 1 = -504 := by
    simpa [E6] using congr_fun E6_q_exp 1
  have hE62 : (qExpansion 1 E6).coeff 2 = -16632 := by
    have h := congr_fun E6_q_exp 2
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE63 : (qExpansion 1 E6).coeff 3 = -122976 := by
    have h := congr_fun E6_q_exp 3
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hantidiag2 : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hantidiag3 : Finset.antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hE4pow3 : (qExpansion 1 (E4 ^ 3)).coeff 3 = 16954560 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, hantidiag3]
    have hE4sq1 : (qExpansion 1 E4 ^ 2).coeff 1 = 480 := by
      rw [pow_two, PowerSeries.coeff_mul, antidiagonal_one]
      simp [hE40, hE41]
      norm_num
    have hE4sq2 : (qExpansion 1 E4 ^ 2).coeff 2 = 61920 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag2]
      simp [hE40, hE41, hE42]
      norm_num
    have hE4sq3 : (qExpansion 1 E4 ^ 2).coeff 3 = 1050240 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag3]
      simp [hE40, hE41, hE42, hE43]
      norm_num
    have hE4mul1 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 1 = 480 := by
      simpa [pow_two] using hE4sq1
    have hE4mul2 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 2 = 61920 := by
      simpa [pow_two] using hE4sq2
    have hE4mul3 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 3 = 1050240 := by
      simpa [pow_two] using hE4sq3
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    simp [hE40, hE41, hE42, hE43, hE4mul1, hE4mul2, hE4mul3, hE4const]
    norm_num
  have hE6pow3 : (qExpansion 1 (E6 ^ 2)).coeff 3 = 16519104 := by
    rw [hE6pow, pow_two, PowerSeries.coeff_mul, hantidiag3]
    simp [hE60, hE61, hE62, hE63]
    norm_num
  calc
    (qExpansion 1 Delta).coeff 3 = ((1 / 1728 : ℂ) • qExpansion 1 (E4 ^ 3 - E6 ^ 2)).coeff 3 := by
      simpa using hDeltaaux3
    _ = (1 / 1728 : ℂ) * (qExpansion 1 (E4 ^ 3 - E6 ^ 2)).coeff 3 := by simp
    _ = (1 / 1728 : ℂ) *
        ((qExpansion 1 (E4 ^ 3)).coeff 3 - (qExpansion 1 (E6 ^ 2)).coeff 3) := by
          simp [hqsub]
    _ = (1 / 1728 : ℂ) * (16954560 - 16519104) := by simp [hE4pow3, hE6pow3]
    _ = 252 := by norm_num

lemma Delta_exp_four : (qExpansion 1 Delta).coeff 4 = -1472 := by
  have hDeltaaux4 := congrArg (PowerSeries.coeff 4) Deltaaux
  have hqsub : qExpansion 1 (E4 ^ 3 - E6 ^ 2) = qExpansion 1 (E4 ^ 3) - qExpansion 1 (E6 ^ 2) := by
    calc
      _ = qExpansion 1 ((E4.mul (E4.mul E4)) - (E6.mul E6)) := by
        have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := by rfl
        have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := by rfl
        simp [pow_three, pow_two, hf, hg]
      _ = qExpansion 1 (E4.mul (E4.mul E4)) - qExpansion 1 (E6.mul E6) := by
        simpa using (_root_.qExpansion_sub (h := (1 : ℝ)) (hh := by norm_num)
          (hΓ := one_mem_strictPeriods_SL2Z) (f := E4.mul (E4.mul E4)) (g := E6.mul E6))
      _ = _ := by
        have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := by rfl
        have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := by rfl
        simp [pow_three, pow_two, hf, hg]
  have hE4pow : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E4 3
  have hE6pow : qExpansion 1 (E6 ^ 2) = (qExpansion 1 E6) ^ 2 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (6 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E6 2
  have hE40 : (qExpansion 1 E4).coeff 0 = 1 := by
    simpa [E4] using congr_fun E4_q_exp 0
  have hE41 : (qExpansion 1 E4).coeff 1 = 240 := by
    simpa [E4] using congr_fun E4_q_exp 1
  have hE42 : (qExpansion 1 E4).coeff 2 = 2160 := by
    have h := congr_fun E4_q_exp 2
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE43 : (qExpansion 1 E4).coeff 3 = 6720 := by
    have h := congr_fun E4_q_exp 3
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE44 : (qExpansion 1 E4).coeff 4 = 17520 := by
    have h : (qExpansion 1 E4).coeff 4 = (240 : ℂ) * ArithmeticFunction.sigma 3 4 := by
      simpa [E4] using (congr_fun E4_q_exp 4)
    have hsigma : ArithmeticFunction.sigma 3 4 = 73 := by decide
    calc
      _ = (240 : ℂ) * ArithmeticFunction.sigma 3 4 := h
      _ = (240 : ℂ) * 73 := by simp [hsigma]
      _ = 17520 := by norm_num
  have hE60 : (qExpansion 1 E6).coeff 0 = 1 := by
    simpa [E6] using congr_fun E6_q_exp 0
  have hE61 : (qExpansion 1 E6).coeff 1 = -504 := by
    simpa [E6] using congr_fun E6_q_exp 1
  have hE62 : (qExpansion 1 E6).coeff 2 = -16632 := by
    have h := congr_fun E6_q_exp 2
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE63 : (qExpansion 1 E6).coeff 3 = -122976 := by
    have h := congr_fun E6_q_exp 3
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE64 : (qExpansion 1 E6).coeff 4 = -532728 := by
    have h : (qExpansion 1 E6).coeff 4 = -(504 : ℂ) * ArithmeticFunction.sigma 5 4 := by
      simpa [E6] using (congr_fun E6_q_exp 4)
    have hsigma : ArithmeticFunction.sigma 5 4 = 1057 := by decide
    calc
      _ = -(504 : ℂ) * ArithmeticFunction.sigma 5 4 := h
      _ = -(504 : ℂ) * 1057 := by simp [hsigma]
      _ = -532728 := by norm_num
  have hantidiag2 : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hantidiag3 : Finset.antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hantidiag4 : Finset.antidiagonal 4 = {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hE4pow4 : (qExpansion 1 (E4 ^ 3)).coeff 4 = 396974160 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, hantidiag4]
    have hE4sq1 : (qExpansion 1 E4 ^ 2).coeff 1 = 480 := by
      rw [pow_two, PowerSeries.coeff_mul, antidiagonal_one]
      simp [hE40, hE41]
      norm_num
    have hE4sq2 : (qExpansion 1 E4 ^ 2).coeff 2 = 61920 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag2]
      simp [hE40, hE41, hE42]
      norm_num
    have hE4sq3 : (qExpansion 1 E4 ^ 2).coeff 3 = 1050240 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag3]
      simp [hE40, hE41, hE42, hE43]
      norm_num
    have hE4sq4 : (qExpansion 1 E4 ^ 2).coeff 4 = 7926240 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag4]
      simp [hE40, hE41, hE42, hE43, hE44]
      norm_num
    have hE4mul1 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 1 = 480 := by
      simpa [pow_two] using hE4sq1
    have hE4mul2 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 2 = 61920 := by
      simpa [pow_two] using hE4sq2
    have hE4mul3 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 3 = 1050240 := by
      simpa [pow_two] using hE4sq3
    have hE4mul4 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 4 = 7926240 := by
      simpa [pow_two] using hE4sq4
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    simp [hE40, hE41, hE42, hE43, hE44, hE4mul1, hE4mul2, hE4mul3, hE4mul4, hE4const]
    norm_num
  have hE6pow4 : (qExpansion 1 (E6 ^ 2)).coeff 4 = 399517776 := by
    rw [hE6pow, pow_two, PowerSeries.coeff_mul, hantidiag4]
    simp [hE60, hE61, hE62, hE63, hE64]
    norm_num
  calc
    (qExpansion 1 Delta).coeff 4 = ((1 / 1728 : ℂ) • qExpansion 1 (E4 ^ 3 - E6 ^ 2)).coeff 4 := by
      simpa using hDeltaaux4
    _ = (1 / 1728 : ℂ) * (qExpansion 1 (E4 ^ 3 - E6 ^ 2)).coeff 4 := by simp
    _ = (1 / 1728 : ℂ) *
        ((qExpansion 1 (E4 ^ 3)).coeff 4 - (qExpansion 1 (E6 ^ 2)).coeff 4) := by
          simp [hqsub]
    _ = (1 / 1728 : ℂ) * (396974160 - 399517776) := by simp [hE4pow4, hE6pow4]
    _ = -1472 := by norm_num

lemma Delta_exp_five : (qExpansion 1 Delta).coeff 5 = 4830 := by
  have hDeltaaux5 := congrArg (PowerSeries.coeff 5) Deltaaux
  have hqsub : qExpansion 1 (E4 ^ 3 - E6 ^ 2) = qExpansion 1 (E4 ^ 3) - qExpansion 1 (E6 ^ 2) := by
    calc
      _ = qExpansion 1 ((E4.mul (E4.mul E4)) - (E6.mul E6)) := by
        have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := by rfl
        have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := by rfl
        simp [pow_three, pow_two, hf, hg]
      _ = qExpansion 1 (E4.mul (E4.mul E4)) - qExpansion 1 (E6.mul E6) := by
        simpa using (_root_.qExpansion_sub (h := (1 : ℝ)) (hh := by norm_num)
          (hΓ := one_mem_strictPeriods_SL2Z) (f := E4.mul (E4.mul E4)) (g := E6.mul E6))
      _ = _ := by
        have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := by rfl
        have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := by rfl
        simp [pow_three, pow_two, hf, hg]
  have hE4pow : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E4 3
  have hE6pow : qExpansion 1 (E6 ^ 2) = (qExpansion 1 E6) ^ 2 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (6 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E6 2
  have hE40 : (qExpansion 1 E4).coeff 0 = 1 := by
    simpa [E4] using congr_fun E4_q_exp 0
  have hE41 : (qExpansion 1 E4).coeff 1 = 240 := by
    simpa [E4] using congr_fun E4_q_exp 1
  have hE42 : (qExpansion 1 E4).coeff 2 = 2160 := by
    have h := congr_fun E4_q_exp 2
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE43 : (qExpansion 1 E4).coeff 3 = 6720 := by
    have h := congr_fun E4_q_exp 3
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE44 : (qExpansion 1 E4).coeff 4 = 17520 := by
    have h : (qExpansion 1 E4).coeff 4 = (240 : ℂ) * ArithmeticFunction.sigma 3 4 := by
      simpa [E4] using (congr_fun E4_q_exp 4)
    have hsigma : ArithmeticFunction.sigma 3 4 = 73 := by decide
    calc
      _ = (240 : ℂ) * ArithmeticFunction.sigma 3 4 := h
      _ = (240 : ℂ) * 73 := by simp [hsigma]
      _ = 17520 := by norm_num
  have hE45 : (qExpansion 1 E4).coeff 5 = 30240 := by
    have h : (qExpansion 1 E4).coeff 5 = (240 : ℂ) * ArithmeticFunction.sigma 3 5 := by
      simpa [E4] using (congr_fun E4_q_exp 5)
    have hsigma : ArithmeticFunction.sigma 3 5 = 126 := by decide
    calc
      _ = (240 : ℂ) * ArithmeticFunction.sigma 3 5 := h
      _ = (240 : ℂ) * 126 := by simp [hsigma]
      _ = 30240 := by norm_num
  have hE60 : (qExpansion 1 E6).coeff 0 = 1 := by
    simpa [E6] using congr_fun E6_q_exp 0
  have hE61 : (qExpansion 1 E6).coeff 1 = -504 := by
    simpa [E6] using congr_fun E6_q_exp 1
  have hE62 : (qExpansion 1 E6).coeff 2 = -16632 := by
    have h := congr_fun E6_q_exp 2
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE63 : (qExpansion 1 E6).coeff 3 = -122976 := by
    have h := congr_fun E6_q_exp 3
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE64 : (qExpansion 1 E6).coeff 4 = -532728 := by
    have h : (qExpansion 1 E6).coeff 4 = -(504 : ℂ) * ArithmeticFunction.sigma 5 4 := by
      simpa [E6] using (congr_fun E6_q_exp 4)
    have hsigma : ArithmeticFunction.sigma 5 4 = 1057 := by decide
    calc
      _ = -(504 : ℂ) * ArithmeticFunction.sigma 5 4 := h
      _ = -(504 : ℂ) * 1057 := by simp [hsigma]
      _ = -532728 := by norm_num
  have hE65 : (qExpansion 1 E6).coeff 5 = -1575504 := by
    have h : (qExpansion 1 E6).coeff 5 = -(504 : ℂ) * ArithmeticFunction.sigma 5 5 := by
      simpa [E6] using (congr_fun E6_q_exp 5)
    have hsigma : ArithmeticFunction.sigma 5 5 = 3126 := by decide
    calc
      _ = -(504 : ℂ) * ArithmeticFunction.sigma 5 5 := h
      _ = -(504 : ℂ) * 3126 := by simp [hsigma]
      _ = -1575504 := by norm_num
  have hantidiag2 : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hantidiag3 : Finset.antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hantidiag4 : Finset.antidiagonal 4 = {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hantidiag5 : Finset.antidiagonal 5 = {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hE4pow5 : (qExpansion 1 (E4 ^ 3)).coeff 5 = 4632858720 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, hantidiag5]
    have hE4sq1 : (qExpansion 1 E4 ^ 2).coeff 1 = 480 := by
      rw [pow_two, PowerSeries.coeff_mul, antidiagonal_one]
      simp [hE40, hE41]
      norm_num
    have hE4sq2 : (qExpansion 1 E4 ^ 2).coeff 2 = 61920 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag2]
      simp [hE40, hE41, hE42]
      norm_num
    have hE4sq3 : (qExpansion 1 E4 ^ 2).coeff 3 = 1050240 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag3]
      simp [hE40, hE41, hE42, hE43]
      norm_num
    have hE4sq4 : (qExpansion 1 E4 ^ 2).coeff 4 = 7926240 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag4]
      simp [hE40, hE41, hE42, hE43, hE44]
      norm_num
    have hE4sq5 : (qExpansion 1 E4 ^ 2).coeff 5 = 37500480 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag5]
      simp [hE40, hE41, hE42, hE43, hE44, hE45]
      norm_num
    have hE4mul1 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 1 = 480 := by
      simpa [pow_two] using hE4sq1
    have hE4mul2 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 2 = 61920 := by
      simpa [pow_two] using hE4sq2
    have hE4mul3 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 3 = 1050240 := by
      simpa [pow_two] using hE4sq3
    have hE4mul4 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 4 = 7926240 := by
      simpa [pow_two] using hE4sq4
    have hE4mul5 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 5 = 37500480 := by
      simpa [pow_two] using hE4sq5
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    simp [hE40, hE41, hE42, hE43, hE44, hE45, hE4mul1, hE4mul2, hE4mul3, hE4mul4, hE4mul5,
      hE4const]
    norm_num
  have hE6pow5 : (qExpansion 1 (E6 ^ 2)).coeff 5 = 4624512480 := by
    rw [hE6pow, pow_two, PowerSeries.coeff_mul, hantidiag5]
    simp [hE60, hE61, hE62, hE63, hE64, hE65]
    norm_num
  calc
    (qExpansion 1 Delta).coeff 5 = ((1 / 1728 : ℂ) • qExpansion 1 (E4 ^ 3 - E6 ^ 2)).coeff 5 := by
      simpa using hDeltaaux5
    _ = (1 / 1728 : ℂ) * (qExpansion 1 (E4 ^ 3 - E6 ^ 2)).coeff 5 := by simp
    _ = (1 / 1728 : ℂ) *
        ((qExpansion 1 (E4 ^ 3)).coeff 5 - (qExpansion 1 (E6 ^ 2)).coeff 5) := by
          simp [hqsub]
    _ = (1 / 1728 : ℂ) * (4632858720 - 4624512480) := by simp [hE4pow5, hE6pow5]
    _ = 4830 := by norm_num

lemma qj_exp_one : (qExpansion 1 qj).coeff 1 = 744 := by
  have hqj : qExpansion 1 qj = qExpansion 1 (E4 ^ 3 * qoverDelta) := by
    simpa [qj] using congrArg (qExpansion 1) qjIdentity.symm
  have hmul :
      qExpansion 1 (E4 ^ 3 * qoverDelta) = qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta := by
    exact qExpansion_mul E4cubed_AnalyticAt qoverDelta_AnalyticAt
  have hE4pow : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E4 3
  have hE40 : (qExpansion 1 E4).coeff 0 = 1 := by
    simpa [E4] using congr_fun E4_q_exp 0
  have hE41 : (qExpansion 1 E4).coeff 1 = 240 := by
    simpa [E4] using congr_fun E4_q_exp 1
  have hE4pow0 : (qExpansion 1 (E4 ^ 3)).coeff 0 = 1 := by
    rw [hE4pow]
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hE4const]
  have hE4pow1 : (qExpansion 1 (E4 ^ 3)).coeff 1 = 720 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, antidiagonal_one]
    simp [PowerSeries.coeff_mul, antidiagonal_one, hE40, hE41]
    norm_num
  have hqover0 : (qExpansion 1 qoverDelta).coeff 0 = 1 := by
    simp [qExpansion_coeff, cuspFunction_qoverDelta_zero]
  have hDeltaoverq1 : (qExpansion 1 Deltaoverq).coeff 1 = -24 := by
    have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
      simpa using qExpansion_ext Deltaoverq InfSumDeltashift (InfSumDeltashift_eq_Deltaoverq.symm)
    calc
      _ = (qExpansion 1 InfSumDeltashift).coeff 1 := by simp [hq]
      _ = (qExpansion 1 Delta).coeff 2 := by simpa using InfSumDeltashift_coeff_eq 1
      _ = -24 := Delta_exp_two
  have hmap0 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 0 = 1 := by
    have h0 := congrArg (PowerSeries.coeff 0) coeTo_of_integralDeltaoverq
    simpa [qExpansion_coeff, cuspFunction_Deltaoverq_zero] using h0
  have hmap1 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 1 = -24 := by
    have h1 := congrArg (PowerSeries.coeff 1) coeTo_of_integralDeltaoverq
    simpa [hDeltaoverq1] using h1
  have hqover1 : (qExpansion 1 qoverDelta).coeff 1 = 24 := by
    have hcoeff1 := congrArg (PowerSeries.coeff 1) integralDeltaoverq_mul_qoverDelta_qExpansion
    have hadd' : (-24 : ℂ) + (qExpansion 1 qoverDelta).coeff 1 = 0 := by
      simpa [PowerSeries.coeff_mul, antidiagonal_one, hmap0, hmap1, hqover0] using hcoeff1
    have hadd : (qExpansion 1 qoverDelta).coeff 1 + (-24 : ℂ) = 0 := by
      simpa [add_comm] using hadd'
    have hneg : (qExpansion 1 qoverDelta).coeff 1 = -(-24 : ℂ) :=
      (eq_neg_iff_add_eq_zero).2 hadd
    simpa using hneg
  calc
  _ = (qExpansion 1 (E4 ^ 3 * qoverDelta)).coeff 1 := by rw [hqj]
  _ = (qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta).coeff 1 := by rw [hmul]
  _ = (qExpansion 1 (E4 ^ 3)).coeff 0 * (qExpansion 1 qoverDelta).coeff 1
      + (qExpansion 1 (E4 ^ 3)).coeff 1 * (qExpansion 1 qoverDelta).coeff 0 := by
      rw [PowerSeries.coeff_mul, antidiagonal_one]
      simp [add_comm, mul_comm]
  _ = _ := by
      simp [hE4pow0, hE4pow1, hqover0, hqover1]
      norm_num

lemma qj_exp_one' : qj_coeffs 1 = 744 := by
  have h1 : ((qj_coeffs 1 : ℤ) : ℂ) = (qExpansion 1 qj).coeff 1 := by
    simpa [qj_coeffs] using
        congrArg (PowerSeries.coeff 1) (coeTo_of_toIntegralPowerSeries qjIsIntegralPowerSeries)
  have h2 : ((qj_coeffs 1 : ℤ) : ℂ) = 744 := by
    calc
    _ = (qExpansion 1 qj).coeff 1 := h1
    _ = _ := qj_exp_one
  exact_mod_cast h2

lemma qj_exp_two : (qExpansion 1 qj).coeff 2 = 196884 := by
  have hantidiag2 : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hqj : qExpansion 1 qj = qExpansion 1 (E4 ^ 3 * qoverDelta) := by
    simpa [qj] using congrArg (qExpansion 1) qjIdentity.symm
  have hmul :
      qExpansion 1 (E4 ^ 3 * qoverDelta) = qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta := by
    exact qExpansion_mul E4cubed_AnalyticAt qoverDelta_AnalyticAt
  have hE4pow : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E4 3
  have hE40 : (qExpansion 1 E4).coeff 0 = 1 := by
    simpa [E4] using congr_fun E4_q_exp 0
  have hE41 : (qExpansion 1 E4).coeff 1 = 240 := by
    simpa [E4] using congr_fun E4_q_exp 1
  have hE42 : (qExpansion 1 E4).coeff 2 = 2160 := by
    have h := congr_fun E4_q_exp 2
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE4pow0 : (qExpansion 1 (E4 ^ 3)).coeff 0 = 1 := by
    rw [hE4pow]
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hE4const]
  have hE4pow1 : (qExpansion 1 (E4 ^ 3)).coeff 1 = 720 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, antidiagonal_one]
    simp [PowerSeries.coeff_mul, antidiagonal_one, hE40, hE41]
    norm_num
  have hE4sq1 : (qExpansion 1 E4 ^ 2).coeff 1 = 480 := by
    rw [pow_two, PowerSeries.coeff_mul, antidiagonal_one]
    simp [hE40, hE41]
    norm_num
  have hE4sq2 : (qExpansion 1 E4 ^ 2).coeff 2 = 61920 := by
    rw [pow_two, PowerSeries.coeff_mul, hantidiag2]
    simp [hE40, hE41, hE42]
    norm_num
  have hE4mul1 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 1 = 480 := by
    simpa [pow_two] using hE4sq1
  have hE4mul2 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 2 = 61920 := by
    simpa [pow_two] using hE4sq2
  have hE4pow2 : (qExpansion 1 (E4 ^ 3)).coeff 2 = 179280 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, hantidiag2]
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    simp [hE40, hE41, hE42, hE4mul1, hE4mul2, hE4const]
    norm_num
  have hqover0 : (qExpansion 1 qoverDelta).coeff 0 = 1 := by
    simp [qExpansion_coeff, cuspFunction_qoverDelta_zero]
  have hDeltaoverq1 : (qExpansion 1 Deltaoverq).coeff 1 = -24 := by
    have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
      simpa using qExpansion_ext Deltaoverq InfSumDeltashift (InfSumDeltashift_eq_Deltaoverq.symm)
    calc
      _ = (qExpansion 1 InfSumDeltashift).coeff 1 := by simp [hq]
      _ = (qExpansion 1 Delta).coeff 2 := by simpa using InfSumDeltashift_coeff_eq 1
      _ = -24 := Delta_exp_two
  have hDeltaoverq2 : (qExpansion 1 Deltaoverq).coeff 2 = 252 := by
    have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
      simpa using qExpansion_ext Deltaoverq InfSumDeltashift (InfSumDeltashift_eq_Deltaoverq.symm)
    calc
      _ = (qExpansion 1 InfSumDeltashift).coeff 2 := by simp [hq]
      _ = (qExpansion 1 Delta).coeff 3 := by simpa using InfSumDeltashift_coeff_eq 2
      _ = 252 := Delta_exp_three
  have hmap0 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 0 = 1 := by
    have h0 := congrArg (PowerSeries.coeff 0) coeTo_of_integralDeltaoverq
    simpa [qExpansion_coeff, cuspFunction_Deltaoverq_zero] using h0
  have hmap1 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 1 = -24 := by
    have h1 := congrArg (PowerSeries.coeff 1) coeTo_of_integralDeltaoverq
    simpa [hDeltaoverq1] using h1
  have hmap2 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 2 = 252 := by
    have h2 := congrArg (PowerSeries.coeff 2) coeTo_of_integralDeltaoverq
    simpa [hDeltaoverq2] using h2
  have hqover1 : (qExpansion 1 qoverDelta).coeff 1 = 24 := by
    have hcoeff1 := congrArg (PowerSeries.coeff 1) integralDeltaoverq_mul_qoverDelta_qExpansion
    have hadd' : (-24 : ℂ) + (qExpansion 1 qoverDelta).coeff 1 = 0 := by
      simpa [PowerSeries.coeff_mul, antidiagonal_one, hmap0, hmap1, hqover0] using hcoeff1
    have hadd : (qExpansion 1 qoverDelta).coeff 1 + (-24 : ℂ) = 0 := by
      simpa [add_comm] using hadd'
    have hneg : (qExpansion 1 qoverDelta).coeff 1 = -(-24 : ℂ) :=
      (eq_neg_iff_add_eq_zero).2 hadd
    simpa using hneg
  have hqover2 : (qExpansion 1 qoverDelta).coeff 2 = 324 := by
    have hcoeff2 := congrArg (PowerSeries.coeff 2) integralDeltaoverq_mul_qoverDelta_qExpansion
    have h2eq : (qExpansion 1 qoverDelta).coeff 2 + (-24 : ℂ) * (qExpansion 1 qoverDelta).coeff 1
        + (252 : ℂ) = 0 := by
      simpa [PowerSeries.coeff_mul, hantidiag2, hmap0, hmap1, hmap2, hqover0, add_assoc, add_comm,
        add_left_comm, mul_comm, mul_left_comm, mul_assoc] using hcoeff2
    rw [hqover1] at h2eq
    have hadd : (qExpansion 1 qoverDelta).coeff 2 + (-324 : ℂ) = 0 := by
      have h2eq' := h2eq
      ring_nf at h2eq'
      simpa [add_comm] using h2eq'
    have hneg : (qExpansion 1 qoverDelta).coeff 2 = -(-324 : ℂ) :=
      (eq_neg_iff_add_eq_zero).2 hadd
    simpa using hneg
  calc
  _ = (qExpansion 1 (E4 ^ 3 * qoverDelta)).coeff 2 := by rw [hqj]
  _ = (qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta).coeff 2 := by rw [hmul]
  _ = (qExpansion 1 (E4 ^ 3)).coeff 0 * (qExpansion 1 qoverDelta).coeff 2
      + (qExpansion 1 (E4 ^ 3)).coeff 1 * (qExpansion 1 qoverDelta).coeff 1
      + (qExpansion 1 (E4 ^ 3)).coeff 2 * (qExpansion 1 qoverDelta).coeff 0 := by
      rw [PowerSeries.coeff_mul, hantidiag2]
      simp [add_assoc, add_comm, mul_comm]
  _ = _ := by
      simp [hE4pow0, hE4pow1, hE4pow2, hqover0, hqover1, hqover2]
      norm_num

lemma qj_exp_two' : qj_coeffs 2 = 196884 := by
  have h1 : ((qj_coeffs 2 : ℤ) : ℂ) = (qExpansion 1 qj).coeff 2 := by
    simpa [qj_coeffs] using
        congrArg (PowerSeries.coeff 2) (coeTo_of_toIntegralPowerSeries qjIsIntegralPowerSeries)
  have h2 : ((qj_coeffs 2 : ℤ) : ℂ) = 196884 := by
    calc
    _ = (qExpansion 1 qj).coeff 2 := h1
    _ = _ := qj_exp_two
  exact_mod_cast h2

lemma qj_exp_three : (qExpansion 1 qj).coeff 3 = 21493760 := by
  have hantidiag2 : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hantidiag3 : Finset.antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hqj : qExpansion 1 qj = qExpansion 1 (E4 ^ 3 * qoverDelta) := by
    simpa [qj] using congrArg (qExpansion 1) qjIdentity.symm
  have hmul :
      qExpansion 1 (E4 ^ 3 * qoverDelta) = qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta := by
    exact qExpansion_mul E4cubed_AnalyticAt qoverDelta_AnalyticAt
  have hE4pow : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E4 3
  have hE40 : (qExpansion 1 E4).coeff 0 = 1 := by
    simpa [E4] using congr_fun E4_q_exp 0
  have hE41 : (qExpansion 1 E4).coeff 1 = 240 := by
    simpa [E4] using congr_fun E4_q_exp 1
  have hE42 : (qExpansion 1 E4).coeff 2 = 2160 := by
    have h := congr_fun E4_q_exp 2
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE43 : (qExpansion 1 E4).coeff 3 = 6720 := by
    have h := congr_fun E4_q_exp 3
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE4pow0 : (qExpansion 1 (E4 ^ 3)).coeff 0 = 1 := by
    rw [hE4pow]
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hE4const]
  have hE4pow1 : (qExpansion 1 (E4 ^ 3)).coeff 1 = 720 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, antidiagonal_one]
    simp [PowerSeries.coeff_mul, antidiagonal_one, hE40, hE41]
    norm_num
  have hE4pow2 : (qExpansion 1 (E4 ^ 3)).coeff 2 = 179280 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, hantidiag2]
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    have hE4sq1 : (qExpansion 1 E4 ^ 2).coeff 1 = 480 := by
      rw [pow_two, PowerSeries.coeff_mul, antidiagonal_one]
      simp [hE40, hE41]
      norm_num
    have hE4sq2 : (qExpansion 1 E4 ^ 2).coeff 2 = 61920 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag2]
      simp [hE40, hE41, hE42]
      norm_num
    have hE4mul1 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 1 = 480 := by
      simpa [pow_two] using hE4sq1
    have hE4mul2 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 2 = 61920 := by
      simpa [pow_two] using hE4sq2
    simp [hE40, hE41, hE42, hE4mul1, hE4mul2, hE4const]
    norm_num
  have hE4pow3 : (qExpansion 1 (E4 ^ 3)).coeff 3 = 16954560 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, hantidiag3]
    have hE4sq1 : (qExpansion 1 E4 ^ 2).coeff 1 = 480 := by
      rw [pow_two, PowerSeries.coeff_mul, antidiagonal_one]
      simp [hE40, hE41]
      norm_num
    have hE4sq2 : (qExpansion 1 E4 ^ 2).coeff 2 = 61920 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag2]
      simp [hE40, hE41, hE42]
      norm_num
    have hE4sq3 : (qExpansion 1 E4 ^ 2).coeff 3 = 1050240 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag3]
      simp [hE40, hE41, hE42, hE43]
      norm_num
    have hE4mul1 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 1 = 480 := by
      simpa [pow_two] using hE4sq1
    have hE4mul2 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 2 = 61920 := by
      simpa [pow_two] using hE4sq2
    have hE4mul3 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 3 = 1050240 := by
      simpa [pow_two] using hE4sq3
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    simp [hE40, hE41, hE42, hE43, hE4mul1, hE4mul2, hE4mul3, hE4const]
    norm_num
  have hqover0 : (qExpansion 1 qoverDelta).coeff 0 = 1 := by
    simp [qExpansion_coeff, cuspFunction_qoverDelta_zero]
  have hDeltaoverq1 : (qExpansion 1 Deltaoverq).coeff 1 = -24 := by
    have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
      simpa using qExpansion_ext Deltaoverq InfSumDeltashift (InfSumDeltashift_eq_Deltaoverq.symm)
    calc
      _ = (qExpansion 1 InfSumDeltashift).coeff 1 := by simp [hq]
      _ = (qExpansion 1 Delta).coeff 2 := by simpa using InfSumDeltashift_coeff_eq 1
      _ = -24 := Delta_exp_two
  have hDeltaoverq2 : (qExpansion 1 Deltaoverq).coeff 2 = 252 := by
    have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
      simpa using qExpansion_ext Deltaoverq InfSumDeltashift (InfSumDeltashift_eq_Deltaoverq.symm)
    calc
      _ = (qExpansion 1 InfSumDeltashift).coeff 2 := by simp [hq]
      _ = (qExpansion 1 Delta).coeff 3 := by simpa using InfSumDeltashift_coeff_eq 2
      _ = 252 := Delta_exp_three
  have hDeltaoverq3 : (qExpansion 1 Deltaoverq).coeff 3 = -1472 := by
    have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
      simpa using qExpansion_ext Deltaoverq InfSumDeltashift (InfSumDeltashift_eq_Deltaoverq.symm)
    calc
      _ = (qExpansion 1 InfSumDeltashift).coeff 3 := by simp [hq]
      _ = (qExpansion 1 Delta).coeff 4 := by simpa using InfSumDeltashift_coeff_eq 3
      _ = -1472 := Delta_exp_four
  have hmap0 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 0 = 1 := by
    have h0 := congrArg (PowerSeries.coeff 0) coeTo_of_integralDeltaoverq
    simpa [qExpansion_coeff, cuspFunction_Deltaoverq_zero] using h0
  have hmap1 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 1 = -24 := by
    have h1 := congrArg (PowerSeries.coeff 1) coeTo_of_integralDeltaoverq
    simpa [hDeltaoverq1] using h1
  have hmap2 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 2 = 252 := by
    have h2 := congrArg (PowerSeries.coeff 2) coeTo_of_integralDeltaoverq
    simpa [hDeltaoverq2] using h2
  have hmap3 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 3 = -1472 := by
    have h3 := congrArg (PowerSeries.coeff 3) coeTo_of_integralDeltaoverq
    simpa [hDeltaoverq3] using h3
  have hqover1 : (qExpansion 1 qoverDelta).coeff 1 = 24 := by
    have hcoeff1 := congrArg (PowerSeries.coeff 1) integralDeltaoverq_mul_qoverDelta_qExpansion
    have hadd' : (-24 : ℂ) + (qExpansion 1 qoverDelta).coeff 1 = 0 := by
      simpa [PowerSeries.coeff_mul, antidiagonal_one, hmap0, hmap1, hqover0] using hcoeff1
    have hadd : (qExpansion 1 qoverDelta).coeff 1 + (-24 : ℂ) = 0 := by
      simpa [add_comm] using hadd'
    have hneg : (qExpansion 1 qoverDelta).coeff 1 = -(-24 : ℂ) :=
      (eq_neg_iff_add_eq_zero).2 hadd
    simpa using hneg
  have hqover2 : (qExpansion 1 qoverDelta).coeff 2 = 324 := by
    have hcoeff2 := congrArg (PowerSeries.coeff 2) integralDeltaoverq_mul_qoverDelta_qExpansion
    have h2eq : (qExpansion 1 qoverDelta).coeff 2 + (-24 : ℂ) * (qExpansion 1 qoverDelta).coeff 1
        + (252 : ℂ) = 0 := by
      simpa [PowerSeries.coeff_mul, hantidiag2, hmap0, hmap1, hmap2, hqover0, add_assoc, add_comm,
        add_left_comm, mul_comm, mul_left_comm, mul_assoc] using hcoeff2
    rw [hqover1] at h2eq
    have hadd : (qExpansion 1 qoverDelta).coeff 2 + (-324 : ℂ) = 0 := by
      have h2eq' := h2eq
      ring_nf at h2eq'
      simpa [add_comm] using h2eq'
    have hneg : (qExpansion 1 qoverDelta).coeff 2 = -(-324 : ℂ) :=
      (eq_neg_iff_add_eq_zero).2 hadd
    simpa using hneg
  have hqover3 : (qExpansion 1 qoverDelta).coeff 3 = 3200 := by
    have hcoeff3 := congrArg (PowerSeries.coeff 3) integralDeltaoverq_mul_qoverDelta_qExpansion
    have h3eq : (qExpansion 1 qoverDelta).coeff 3
        + (-24 : ℂ) * (qExpansion 1 qoverDelta).coeff 2
        + (252 : ℂ) * (qExpansion 1 qoverDelta).coeff 1
        + (-1472 : ℂ) = 0 := by
      simpa [PowerSeries.coeff_mul, hantidiag3, hmap0, hmap1, hmap2, hmap3, hqover0, add_assoc,
        add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc] using hcoeff3
    rw [hqover1, hqover2] at h3eq
    have hadd : (qExpansion 1 qoverDelta).coeff 3 + (-3200 : ℂ) = 0 := by
      have h3eq' := h3eq
      ring_nf at h3eq'
      simpa [add_comm] using h3eq'
    have hneg : (qExpansion 1 qoverDelta).coeff 3 = -(-3200 : ℂ) :=
      (eq_neg_iff_add_eq_zero).2 hadd
    simpa using hneg
  calc
  _ = (qExpansion 1 (E4 ^ 3 * qoverDelta)).coeff 3 := by rw [hqj]
  _ = (qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta).coeff 3 := by rw [hmul]
  _ = (qExpansion 1 (E4 ^ 3)).coeff 0 * (qExpansion 1 qoverDelta).coeff 3
      + (qExpansion 1 (E4 ^ 3)).coeff 1 * (qExpansion 1 qoverDelta).coeff 2
      + (qExpansion 1 (E4 ^ 3)).coeff 2 * (qExpansion 1 qoverDelta).coeff 1
      + (qExpansion 1 (E4 ^ 3)).coeff 3 * (qExpansion 1 qoverDelta).coeff 0 := by
      rw [PowerSeries.coeff_mul, hantidiag3]
      simp [add_assoc, add_comm, mul_comm]
  _ = _ := by
      simp [hE4pow0, hE4pow1, hE4pow2, hE4pow3, hqover0, hqover1, hqover2, hqover3]
      norm_num

lemma qj_exp_three' : qj_coeffs 3 = 21493760 := by
  have h1 : ((qj_coeffs 3 : ℤ) : ℂ) = (qExpansion 1 qj).coeff 3 := by
    simpa [qj_coeffs] using
        congrArg (PowerSeries.coeff 3) (coeTo_of_toIntegralPowerSeries qjIsIntegralPowerSeries)
  have h2 : ((qj_coeffs 3 : ℤ) : ℂ) = 21493760 := by
    calc
    _ = (qExpansion 1 qj).coeff 3 := h1
    _ = _ := qj_exp_three
  exact_mod_cast h2

lemma qj_exp_four : (qExpansion 1 qj).coeff 4 = 864299970 := by
  have hantidiag2 : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hantidiag3 : Finset.antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hantidiag4 : Finset.antidiagonal 4 = {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} := by
    ext p
    rcases p with ⟨a, b⟩
    simp
    omega
  have hqj : qExpansion 1 qj = qExpansion 1 (E4 ^ 3 * qoverDelta) := by
    simpa [qj] using congrArg (qExpansion 1) qjIdentity.symm
  have hmul :
      qExpansion 1 (E4 ^ 3 * qoverDelta) = qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta := by
    exact qExpansion_mul E4cubed_AnalyticAt qoverDelta_AnalyticAt
  have hE4pow : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := one_mem_strictPeriods_SL2Z) E4 3
  have hE40 : (qExpansion 1 E4).coeff 0 = 1 := by
    simpa [E4] using congr_fun E4_q_exp 0
  have hE41 : (qExpansion 1 E4).coeff 1 = 240 := by
    simpa [E4] using congr_fun E4_q_exp 1
  have hE42 : (qExpansion 1 E4).coeff 2 = 2160 := by
    have h := congr_fun E4_q_exp 2
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE43 : (qExpansion 1 E4).coeff 3 = 6720 := by
    have h := congr_fun E4_q_exp 3
    norm_num [ArithmeticFunction.sigma] at h ⊢
    exact h
  have hE44 : (qExpansion 1 E4).coeff 4 = 17520 := by
    have h : (qExpansion 1 E4).coeff 4 = (240 : ℂ) * ArithmeticFunction.sigma 3 4 := by
      simpa [E4] using (congr_fun E4_q_exp 4)
    have hsigma : ArithmeticFunction.sigma 3 4 = 73 := by
      decide
    calc
      _ = (240 : ℂ) * ArithmeticFunction.sigma 3 4 := h
      _ = (240 : ℂ) * 73 := by simp [hsigma]
      _ = 17520 := by norm_num
  have hE4pow0 : (qExpansion 1 (E4 ^ 3)).coeff 0 = 1 := by
    rw [hE4pow]
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hE4const]
  have hE4pow1 : (qExpansion 1 (E4 ^ 3)).coeff 1 = 720 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, antidiagonal_one]
    simp [PowerSeries.coeff_mul, antidiagonal_one, hE40, hE41]
    norm_num
  have hE4pow2 : (qExpansion 1 (E4 ^ 3)).coeff 2 = 179280 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, hantidiag2]
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    have hE4sq1 : (qExpansion 1 E4 ^ 2).coeff 1 = 480 := by
      rw [pow_two, PowerSeries.coeff_mul, antidiagonal_one]
      simp [hE40, hE41]
      norm_num
    have hE4sq2 : (qExpansion 1 E4 ^ 2).coeff 2 = 61920 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag2]
      simp [hE40, hE41, hE42]
      norm_num
    have hE4mul1 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 1 = 480 := by
      simpa [pow_two] using hE4sq1
    have hE4mul2 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 2 = 61920 := by
      simpa [pow_two] using hE4sq2
    simp [hE40, hE41, hE42, hE4mul1, hE4mul2, hE4const]
    norm_num
  have hE4pow3 : (qExpansion 1 (E4 ^ 3)).coeff 3 = 16954560 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, hantidiag3]
    have hE4sq1 : (qExpansion 1 E4 ^ 2).coeff 1 = 480 := by
      rw [pow_two, PowerSeries.coeff_mul, antidiagonal_one]
      simp [hE40, hE41]
      norm_num
    have hE4sq2 : (qExpansion 1 E4 ^ 2).coeff 2 = 61920 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag2]
      simp [hE40, hE41, hE42]
      norm_num
    have hE4sq3 : (qExpansion 1 E4 ^ 2).coeff 3 = 1050240 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag3]
      simp [hE40, hE41, hE42, hE43]
      norm_num
    have hE4mul1 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 1 = 480 := by
      simpa [pow_two] using hE4sq1
    have hE4mul2 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 2 = 61920 := by
      simpa [pow_two] using hE4sq2
    have hE4mul3 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 3 = 1050240 := by
      simpa [pow_two] using hE4sq3
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    simp [hE40, hE41, hE42, hE43, hE4mul1, hE4mul2, hE4mul3, hE4const]
    norm_num
  have hE4pow4 : (qExpansion 1 (E4 ^ 3)).coeff 4 = 396974160 := by
    rw [hE4pow, pow_three, PowerSeries.coeff_mul, hantidiag4]
    have hE4sq1 : (qExpansion 1 E4 ^ 2).coeff 1 = 480 := by
      rw [pow_two, PowerSeries.coeff_mul, antidiagonal_one]
      simp [hE40, hE41]
      norm_num
    have hE4sq2 : (qExpansion 1 E4 ^ 2).coeff 2 = 61920 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag2]
      simp [hE40, hE41, hE42]
      norm_num
    have hE4sq3 : (qExpansion 1 E4 ^ 2).coeff 3 = 1050240 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag3]
      simp [hE40, hE41, hE42, hE43]
      norm_num
    have hE4sq4 : (qExpansion 1 E4 ^ 2).coeff 4 = 7926240 := by
      rw [pow_two, PowerSeries.coeff_mul, hantidiag4]
      simp [hE40, hE41, hE42, hE43, hE44]
      norm_num
    have hE4mul1 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 1 = 480 := by
      simpa [pow_two] using hE4sq1
    have hE4mul2 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 2 = 61920 := by
      simpa [pow_two] using hE4sq2
    have hE4mul3 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 3 = 1050240 := by
      simpa [pow_two] using hE4sq3
    have hE4mul4 : (qExpansion 1 E4 * qExpansion 1 E4).coeff 4 = 7926240 := by
      simpa [pow_two] using hE4sq4
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE40
    simp [hE40, hE41, hE42, hE43, hE44, hE4mul1, hE4mul2, hE4mul3, hE4mul4, hE4const]
    norm_num
  have hqover0 : (qExpansion 1 qoverDelta).coeff 0 = 1 := by
    simp [qExpansion_coeff, cuspFunction_qoverDelta_zero]
  have hDeltaoverq1 : (qExpansion 1 Deltaoverq).coeff 1 = -24 := by
    have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
      simpa using qExpansion_ext Deltaoverq InfSumDeltashift (InfSumDeltashift_eq_Deltaoverq.symm)
    calc
      _ = (qExpansion 1 InfSumDeltashift).coeff 1 := by simp [hq]
      _ = (qExpansion 1 Delta).coeff 2 := by simpa using InfSumDeltashift_coeff_eq 1
      _ = -24 := Delta_exp_two
  have hDeltaoverq2 : (qExpansion 1 Deltaoverq).coeff 2 = 252 := by
    have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
      simpa using qExpansion_ext Deltaoverq InfSumDeltashift (InfSumDeltashift_eq_Deltaoverq.symm)
    calc
      _ = (qExpansion 1 InfSumDeltashift).coeff 2 := by simp [hq]
      _ = (qExpansion 1 Delta).coeff 3 := by simpa using InfSumDeltashift_coeff_eq 2
      _ = 252 := Delta_exp_three
  have hDeltaoverq3 : (qExpansion 1 Deltaoverq).coeff 3 = -1472 := by
    have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
      simpa using qExpansion_ext Deltaoverq InfSumDeltashift (InfSumDeltashift_eq_Deltaoverq.symm)
    calc
      _ = (qExpansion 1 InfSumDeltashift).coeff 3 := by simp [hq]
      _ = (qExpansion 1 Delta).coeff 4 := by simpa using InfSumDeltashift_coeff_eq 3
      _ = -1472 := Delta_exp_four
  have hDeltaoverq4 : (qExpansion 1 Deltaoverq).coeff 4 = 4830 := by
    have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
      simpa using qExpansion_ext Deltaoverq InfSumDeltashift (InfSumDeltashift_eq_Deltaoverq.symm)
    calc
      _ = (qExpansion 1 InfSumDeltashift).coeff 4 := by simp [hq]
      _ = (qExpansion 1 Delta).coeff 5 := by simpa using InfSumDeltashift_coeff_eq 4
      _ = 4830 := Delta_exp_five
  have hmap0 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 0 = 1 := by
    have h0 := congrArg (PowerSeries.coeff 0) coeTo_of_integralDeltaoverq
    simpa [qExpansion_coeff, cuspFunction_Deltaoverq_zero] using h0
  have hmap1 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 1 = -24 := by
    have h1 := congrArg (PowerSeries.coeff 1) coeTo_of_integralDeltaoverq
    simpa [hDeltaoverq1] using h1
  have hmap2 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 2 = 252 := by
    have h2 := congrArg (PowerSeries.coeff 2) coeTo_of_integralDeltaoverq
    simpa [hDeltaoverq2] using h2
  have hmap3 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 3 = -1472 := by
    have h3 := congrArg (PowerSeries.coeff 3) coeTo_of_integralDeltaoverq
    simpa [hDeltaoverq3] using h3
  have hmap4 : (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff 4 = 4830 := by
    have h4 := congrArg (PowerSeries.coeff 4) coeTo_of_integralDeltaoverq
    simpa [hDeltaoverq4] using h4
  have hqover1 : (qExpansion 1 qoverDelta).coeff 1 = 24 := by
    have hcoeff1 := congrArg (PowerSeries.coeff 1) integralDeltaoverq_mul_qoverDelta_qExpansion
    have hadd' : (-24 : ℂ) + (qExpansion 1 qoverDelta).coeff 1 = 0 := by
      simpa [PowerSeries.coeff_mul, antidiagonal_one, hmap0, hmap1, hqover0] using hcoeff1
    have hadd : (qExpansion 1 qoverDelta).coeff 1 + (-24 : ℂ) = 0 := by
      simpa [add_comm] using hadd'
    have hneg : (qExpansion 1 qoverDelta).coeff 1 = -(-24 : ℂ) :=
      (eq_neg_iff_add_eq_zero).2 hadd
    simpa using hneg
  have hqover2 : (qExpansion 1 qoverDelta).coeff 2 = 324 := by
    have hcoeff2 := congrArg (PowerSeries.coeff 2) integralDeltaoverq_mul_qoverDelta_qExpansion
    have h2eq : (qExpansion 1 qoverDelta).coeff 2 + (-24 : ℂ) * (qExpansion 1 qoverDelta).coeff 1
        + (252 : ℂ) = 0 := by
      simpa [PowerSeries.coeff_mul, hantidiag2, hmap0, hmap1, hmap2, hqover0, add_assoc, add_comm,
        add_left_comm, mul_comm, mul_left_comm, mul_assoc] using hcoeff2
    rw [hqover1] at h2eq
    have hadd : (qExpansion 1 qoverDelta).coeff 2 + (-324 : ℂ) = 0 := by
      have h2eq' := h2eq
      ring_nf at h2eq'
      simpa [add_comm] using h2eq'
    have hneg : (qExpansion 1 qoverDelta).coeff 2 = -(-324 : ℂ) :=
      (eq_neg_iff_add_eq_zero).2 hadd
    simpa using hneg
  have hqover3 : (qExpansion 1 qoverDelta).coeff 3 = 3200 := by
    have hcoeff3 := congrArg (PowerSeries.coeff 3) integralDeltaoverq_mul_qoverDelta_qExpansion
    have h3eq : (qExpansion 1 qoverDelta).coeff 3
        + (-24 : ℂ) * (qExpansion 1 qoverDelta).coeff 2
        + (252 : ℂ) * (qExpansion 1 qoverDelta).coeff 1
        + (-1472 : ℂ) = 0 := by
      simpa [PowerSeries.coeff_mul, hantidiag3, hmap0, hmap1, hmap2, hmap3, hqover0, add_assoc,
        add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc] using hcoeff3
    rw [hqover1, hqover2] at h3eq
    have hadd : (qExpansion 1 qoverDelta).coeff 3 + (-3200 : ℂ) = 0 := by
      have h3eq' := h3eq
      ring_nf at h3eq'
      simpa [add_comm] using h3eq'
    have hneg : (qExpansion 1 qoverDelta).coeff 3 = -(-3200 : ℂ) :=
      (eq_neg_iff_add_eq_zero).2 hadd
    simpa using hneg
  have hqover4 : (qExpansion 1 qoverDelta).coeff 4 = 25650 := by
    have hcoeff4 := congrArg (PowerSeries.coeff 4) integralDeltaoverq_mul_qoverDelta_qExpansion
    have h4eq : (qExpansion 1 qoverDelta).coeff 4
        + (-24 : ℂ) * (qExpansion 1 qoverDelta).coeff 3
        + (252 : ℂ) * (qExpansion 1 qoverDelta).coeff 2
        + (-1472 : ℂ) * (qExpansion 1 qoverDelta).coeff 1
        + (4830 : ℂ) = 0 := by
      simpa [PowerSeries.coeff_mul, hantidiag4, hmap0, hmap1, hmap2, hmap3, hmap4, hqover0,
        add_assoc, add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc] using hcoeff4
    rw [hqover1, hqover2, hqover3] at h4eq
    have hadd : (qExpansion 1 qoverDelta).coeff 4 + (-25650 : ℂ) = 0 := by
      have h4eq' := h4eq
      ring_nf at h4eq'
      simpa [add_comm] using h4eq'
    have hneg : (qExpansion 1 qoverDelta).coeff 4 = -(-25650 : ℂ) :=
      (eq_neg_iff_add_eq_zero).2 hadd
    simpa using hneg
  calc
  _ = (qExpansion 1 (E4 ^ 3 * qoverDelta)).coeff 4 := by rw [hqj]
  _ = (qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta).coeff 4 := by rw [hmul]
  _ = (qExpansion 1 (E4 ^ 3)).coeff 0 * (qExpansion 1 qoverDelta).coeff 4
      + (qExpansion 1 (E4 ^ 3)).coeff 1 * (qExpansion 1 qoverDelta).coeff 3
      + (qExpansion 1 (E4 ^ 3)).coeff 2 * (qExpansion 1 qoverDelta).coeff 2
      + (qExpansion 1 (E4 ^ 3)).coeff 3 * (qExpansion 1 qoverDelta).coeff 1
      + (qExpansion 1 (E4 ^ 3)).coeff 4 * (qExpansion 1 qoverDelta).coeff 0 := by
      rw [PowerSeries.coeff_mul, hantidiag4]
      simp [add_assoc, add_comm, mul_comm]
  _ = _ := by
    simp [hE4pow0, hE4pow1, hE4pow2, hE4pow3, hE4pow4, hqover0, hqover1, hqover2, hqover3, hqover4]
    norm_num

lemma qj_exp_four' : qj_coeffs 4 = 864299970 := by
  have h1 : ((qj_coeffs 4 : ℤ) : ℂ) = (qExpansion 1 qj).coeff 4 := by
    simpa [qj_coeffs] using
        congrArg (PowerSeries.coeff 4) (coeTo_of_toIntegralPowerSeries qjIsIntegralPowerSeries)
  have h2 : ((qj_coeffs 4 : ℤ) : ℂ) = 864299970 := by
    calc
    _ = (qExpansion 1 qj).coeff 4 := h1
    _ = _ := qj_exp_four
  exact_mod_cast h2

lemma j_exp : ∀ z : ℍ, j z = (qj_coeffs 0 / cexp (2 * π * Complex.I * z))
    + ∑' n, (qj_coeffs (n + 1)) * cexp (2 * π * Complex.I * z) ^ n := by
  intro z
  rw [← cancelout1, ← cancelout2]
  exact qj_exp_dvd z

lemma j_exp' : ∃ (c : ℕ → ℤ), ∀ z : ℍ, j z = (c 0 / cexp (2 * π * Complex.I * z))
    + ∑' n, (c (n + 1)) * cexp (2 * π * Complex.I * z) ^ n := by
  refine ⟨qj_coeffs, ?_⟩
  exact j_exp

lemma j_exp_to_minusone : ∃ (c : ℕ → ℤ), ∀ z : ℍ, j z =
    (1 / cexp (2 * π * Complex.I * z)) + ∑' n, (c n) * cexp (2 * π * Complex.I * z) ^ n := by
  let c : ℕ → ℤ := fun n ↦ qj_coeffs (n + 1)
  use c
  intro z
  have h := j_exp z
  rw [qj_exp_zero'] at h
  exact_mod_cast h

lemma j_exp_to_three : ∃ (c : ℕ → ℤ), c 0 = 744 ∧ c 1 = 196884 ∧ c 2 = 21493760 ∧ c 3 = 864299970
    ∧ ∀ z : ℍ, j z =
    (1 / cexp (2 * π * Complex.I * z)) + ∑' n, (c n) * cexp (2 * π * Complex.I * z) ^ n := by
  let c : ℕ → ℤ := fun n ↦ qj_coeffs (n + 1)
  refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [c] using qj_exp_one'
  · simpa [c] using qj_exp_two'
  · simpa [c] using qj_exp_three'
  · simpa [c] using qj_exp_four'
  · intro z
    have h := j_exp z
    rw [qj_exp_zero'] at h
    simpa [c] using h

theorem Delta_HasIntegralQExpansion : HasIntegralQExpansion 1 Delta :=
  HasIntegralQExpansion_ofPowerSeries DeltaIsIntegralPowerSeries

theorem E4_HasIntegralQExpansion : HasIntegralQExpansion 1 E4 :=
  HasIntegralQExpansion_ofPowerSeries E4IsIntegralPowerSeries

theorem E6_HasIntegralQExpansion : HasIntegralQExpansion 1 E6 :=
  HasIntegralQExpansion_ofPowerSeries E6IsIntegralPowerSeries

theorem j_HasIntegralQExpansion : HasIntegralQExpansion 1 j := by
  use 1
  simpa [HasIntegralQExpansion, qj, pow_one] using qjIsIntegralPowerSeries

end

lemma qj_cuspFunction_DifferentiableOn : DifferentiableOn ℂ (cuspFunction 1 qj) (Metric.ball 0 1) :=
  differentiableOn_cuspFunction_ball' (h := 1) (f := qj) (by norm_num)
    qj_periodic qj_holomorphic qj_IsBoundedAtImInfty

lemma qj_cuspFunction_AnalyticAt : AnalyticAt ℂ (cuspFunction 1 qj) 0 :=
  DifferentiableOn.analyticAt
    (fun q hq => qj_cuspFunction_DifferentiableOn q hq)
    (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

lemma j_cuspFunction_Meromorphic : MeromorphicAt (cuspFunction 1 j) (0 : ℂ) := by
  have hqj_mer : MeromorphicAt (cuspFunction 1 qj) (0 : ℂ) :=
    qj_cuspFunction_AnalyticAt.meromorphicAt
  have hdiv : MeromorphicAt (fun q : ℂ => q⁻¹ * cuspFunction 1 qj q) (0 : ℂ) := by
    exact ((MeromorphicAt.id (0 : ℂ)).inv).mul hqj_mer
  refine hdiv.congr ?_
  have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
    simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds hnorm0
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hq hq'
  have hq0 : q ≠ 0 := by simpa using hq'
  have him : 0 < Complex.im (Periodic.invQParam 1 q) :=
    Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num : 0 < (1 : ℝ)) hq hq0
  let τ : ℍ := ⟨Periodic.invQParam 1 q, him⟩
  have hj : cuspFunction 1 j q = j τ := by
    change Periodic.cuspFunction 1 (j ∘ UpperHalfPlane.ofComplex) q = j τ
    rw [Periodic.cuspFunction_eq_of_nonzero 1 _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hqj : cuspFunction 1 qj q = qj τ := by
    change Periodic.cuspFunction 1 (qj ∘ UpperHalfPlane.ofComplex) q = qj τ
    rw [Periodic.cuspFunction_eq_of_nonzero 1 _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hqparam : 𝕢 1 τ = q := by
    simpa [τ] using Periodic.qParam_right_inv (by norm_num : (1 : ℝ) ≠ 0) hq0
  have hcexp : cexp (2 * π * Complex.I * (τ : ℂ)) = q := by
    simpa [Periodic.qParam, mul_assoc] using hqparam
  calc
    _ = q⁻¹ * qj τ := by rw [hqj]
    _ = q⁻¹ * (q * j τ) := by simp [qj, Pi.mul_apply, hcexp]
    _ = j τ := by field_simp [hq0]
    _ = _ := hj.symm

lemma j_cuspFunction_notAnalytic : ¬ AnalyticAt ℂ (cuspFunction 1 j) 0 := by
  have hqj0 : cuspFunction 1 qj 0 = 1 := by
    simpa [qExpansion_coeff] using qj_exp_zero
  intro hjan
  have hmul_tendsto :
      Tendsto (fun q : ℂ ↦ q * cuspFunction 1 j q)
        (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (0 : ℂ)) := by
    have hcont : ContinuousAt (fun q : ℂ ↦ q * cuspFunction 1 j q) (0 : ℂ) :=
      continuousAt_id.mul hjan.continuousAt
    simpa using hcont.continuousWithinAt.tendsto
  have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
    simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds hnorm0
  have hEq :
      (fun q : ℂ ↦ q * cuspFunction 1 j q) =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        cuspFunction 1 qj := by
    filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
    simpa [qj, Periodic.qParam, pow_one, Pi.mul_apply] using
      (cuspFunction_qpow_mul_eq (h := 1) (hh := by norm_num) (f := j) (n := 1) hq0 hqnorm).symm
  have hqj_tendsto_zero :
      Tendsto (cuspFunction 1 qj) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (0 : ℂ)) :=
    hmul_tendsto.congr' hEq
  have hqj_tendsto_one :
      Tendsto (cuspFunction 1 qj) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (1 : ℂ)) := by
    simpa [hqj0] using qj_cuspFunction_AnalyticAt.continuousAt.continuousWithinAt.tendsto
  have : (1 : ℂ) = 0 := tendsto_nhds_unique hqj_tendsto_one hqj_tendsto_zero
  exact one_ne_zero this

lemma j_poleOrder : poleOrder 1 j = 1 := by
  let F : ℂ → ℂ := cuspFunction 1 qj
  have hqj0 : F 0 = 1 := by
    simpa [F, qExpansion_coeff] using qj_exp_zero
  have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
    simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds hnorm0
  have hEq :
      cuspFunction 1 j =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q : ℂ => q⁻¹ * F q := by
    filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
    have hmul : F q = q * cuspFunction 1 j q := by
      simpa [F, qj, Periodic.qParam, Pi.mul_apply, pow_one] using
        (cuspFunction_qpow_mul_eq (h := 1) (hh := by norm_num) (f := j) (n := 1) hq0 hqnorm)
    calc
      cuspFunction 1 j q = q⁻¹ * (q * cuspFunction 1 j q) := by
        field_simp [hq0]
      _ = q⁻¹ * F q := by rw [hmul]
  have hFan : AnalyticAt ℂ F 0 := by
    simpa [F] using qj_cuspFunction_AnalyticAt
  have hFmer : MeromorphicAt F (0 : ℂ) := hFan.meromorphicAt
  have hFord : meromorphicOrderAt F (0 : ℂ) = 0 := by
    rw [AnalyticAt.meromorphicOrderAt_eq (f := F) (x := (0 : ℂ)) hFan]
    have hAord : analyticOrderAt F (0 : ℂ) = 0 :=
      (hFan.analyticOrderAt_eq_zero).2 (by simp [hqj0])
    simp [hAord]
  have hqinvord : meromorphicOrderAt (fun q : ℂ ↦ q⁻¹) (0 : ℂ) = (-1 : WithTop ℤ) := by
    calc
      meromorphicOrderAt (fun q : ℂ ↦ q⁻¹) (0 : ℂ)
          = -meromorphicOrderAt (fun q : ℂ ↦ q) (0 : ℂ) := by
              simpa using (meromorphicOrderAt_inv (f := fun q : ℂ ↦ q) (x := (0 : ℂ)))
      _ = (-1 : WithTop ℤ) := by
            change -meromorphicOrderAt (𝕜 := ℂ) id 0 = (-1 : WithTop ℤ)
            simp
  have hord : meromorphicOrderAt (cuspFunction 1 j) (0 : ℂ) = (-1 : WithTop ℤ) := by
    have hqinvmer : MeromorphicAt (fun q : ℂ ↦ q⁻¹) (0 : ℂ) := (MeromorphicAt.id (0 : ℂ)).inv
    rw [meromorphicOrderAt_congr hEq]
    change meromorphicOrderAt (((fun q : ℂ ↦ q⁻¹) * F)) (0 : ℂ) = (-1 : WithTop ℤ)
    rw [meromorphicOrderAt_mul hqinvmer hFmer, hqinvord, hFord]
    norm_num
  unfold UpperHalfPlane.poleOrder
  rw [hord]
  have hlt : ((-1 : WithTop ℤ) < 0) := by
    change (((-1 : ℤ) : WithTop ℤ) < 0)
    exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)
  rw [if_pos hlt]
  decide

lemma j_poleRemoved : poleRemoved 1 j = qj := by
  ext τ
  simp [UpperHalfPlane.poleRemoved, qj, j_poleOrder, Periodic.qParam, pow_one]

lemma j_to_qExpansion : to_qExpansion 1 j = qExpansion 1 qj := by
  simp [UpperHalfPlane.to_qExpansion, j_poleRemoved]

theorem jLaurentqExpansion_lt_minusone {n : ℤ} (hn : n < -1) :
    (laurentqExpansion 1 j).coeff n = 0 := by
  have hlt : n < -(poleOrder 1 j : ℤ) := by simpa [j_poleOrder] using hn
  exact laurentqExpansion.coeff_eq_zero_of_lt hlt

theorem jLaurentqExpansion_isIntegral {n : ℤ} :
    ∃ m : ℤ, (laurentqExpansion 1 j).coeff n = m := by
  by_cases hn : n < -1
  · refine ⟨0, ?_⟩
    simp [jLaurentqExpansion_lt_minusone hn]
  · refine ⟨qj_coeffs (Int.toNat (n + 1)), ?_⟩
    have hge : -(poleOrder 1 j : ℤ) ≤ n := by
      simpa [j_poleOrder] using le_of_not_gt hn
    have hcoeff :
        (((qj_coeffs (Int.toNat (n + 1)) : ℤ) : ℂ)) =
          (qExpansion 1 qj).coeff (Int.toNat (n + 1)) := by
      simpa [qj_coeffs] using congrArg (PowerSeries.coeff (Int.toNat (n + 1)))
        (coeTo_of_toIntegralPowerSeries qjIsIntegralPowerSeries)
    calc
      (laurentqExpansion 1 j).coeff n
          = (to_qExpansion 1 j).coeff (Int.toNat (n + poleOrder 1 j)) := by
              simpa using
                (laurentqExpansion.coeff_of_geq (h := 1) (f := j) (n := n) (hn := hge))
      _ = (qExpansion 1 qj).coeff (Int.toNat (n + poleOrder 1 j)) := by
            rw [j_to_qExpansion]
      _ = (qExpansion 1 qj).coeff (Int.toNat (n + 1)) := by
            simp [j_poleOrder]
      _ = qj_coeffs (Int.toNat (n + 1)) := by
            simpa using hcoeff.symm

theorem jLaurentqExpansion_minusone : (laurentqExpansion 1 j).coeff (-1) = 1 := by
  calc
    (laurentqExpansion 1 j).coeff (-1) = (to_qExpansion 1 j).coeff 0 := by
      simpa [j_poleOrder] using (laurentqExpansion.coeff_neg_poleOrder (h := 1) (f := j))
    _ = (qExpansion 1 qj).coeff 0 := by rw [j_to_qExpansion]
    _ = 1 := qj_exp_zero

theorem jLaurentqExpansion_zero : (laurentqExpansion 1 j).coeff 0 = 744 := by
  calc
    (laurentqExpansion 1 j).coeff 0 = (to_qExpansion 1 j).coeff 1 := by
      simpa [j_poleOrder] using (laurentqExpansion.coeff_neg_poleOrder_add (h := 1) (f := j) 1)
    _ = (qExpansion 1 qj).coeff 1 := by rw [j_to_qExpansion]
    _ = 744 := qj_exp_one

theorem jLaurentqExpansion_one : (laurentqExpansion 1 j).coeff 1 = 196884 := by
  calc
    (laurentqExpansion 1 j).coeff 1 = (to_qExpansion 1 j).coeff 2 := by
      simpa [j_poleOrder] using (laurentqExpansion.coeff_neg_poleOrder_add (h := 1) (f := j) 2)
    _ = (qExpansion 1 qj).coeff 2 := by rw [j_to_qExpansion]
    _ = 196884 := qj_exp_two

theorem jLaurentqExpansion_two : (laurentqExpansion 1 j).coeff 2 = 21493760 := by
  calc
    (laurentqExpansion 1 j).coeff 2 = (to_qExpansion 1 j).coeff 3 := by
      simpa [j_poleOrder] using (laurentqExpansion.coeff_neg_poleOrder_add (h := 1) (f := j) 3)
    _ = (qExpansion 1 qj).coeff 3 := by rw [j_to_qExpansion]
    _ = 21493760 := qj_exp_three

theorem jLaurentqExpansion_three : (laurentqExpansion 1 j).coeff 3 = 864299970 := by
  calc
    (laurentqExpansion 1 j).coeff 3 = (to_qExpansion 1 j).coeff 4 := by
      simpa [j_poleOrder] using (laurentqExpansion.coeff_neg_poleOrder_add (h := 1) (f := j) 4)
    _ = (qExpansion 1 qj).coeff 4 := by rw [j_to_qExpansion]
    _ = 864299970 := qj_exp_four

section modularEquation

noncomputable def jN (N : ℕ+) : ℍ → ℂ := j ∘ (N • ·)

lemma j_invariant (γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z := by
  have := congrFun (j_slashInvariant γ) z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one] at this
  exact this

private def gamma0Conjugate (N : ℕ+) (γ : SL(2, ℤ))
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

private lemma natPosSMul_gamma0_comm (N : ℕ+) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    N • (γ • z) = gamma0Conjugate N γ hγ • (N • z) := by
  ext
  simp only [natPosSMul_apply, coe_specialLinearGroup_apply, gamma0Conjugate,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
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
  rw [hC, map_mul, show (algebraMap ℤ ℝ) (↑↑N : ℤ) = (↑↑N : ℝ) from by simp [algebraMap_int_eq]]
  push_cast
  rw [← mul_div_assoc]
  congr 1; ring

--rename jLevelN, notation
-- try integer/natural number with instance non-zero
--check
lemma jN_slashInvariant (N : ℕ+) (γ : CongruenceSubgroup.Gamma0 N) :
    jN N ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = jN N := by
  ext z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one, jN, Function.comp]
  rw [natPosSMul_gamma0_comm N γ γ.prop z]
  exact j_invariant _ _

noncomputable def qjN (N : ℕ+) : ℍ → ℂ := qj ∘ (N • ·)

lemma natPosSMul_ofComplex_coe (N : ℕ+) {w : ℂ} (hw : 0 < w.im) :
    N • UpperHalfPlane.ofComplex w = UpperHalfPlane.ofComplex ((↑↑N : ℂ) * w) := by
  have hNw : 0 < ((↑↑N : ℂ) * w).im := by
    rw [Complex.mul_im]
    simp only [natCast_re, natCast_im, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr N.pos) hw
  apply UpperHalfPlane.ext
  rw [natPosSMul_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
    UpperHalfPlane.ofComplex_apply_of_im_pos hNw]

lemma qjN_periodic (N : ℕ+) : Periodic (qjN N ∘ UpperHalfPlane.ofComplex) N := by
  have hqNN : Periodic (qj ∘ UpperHalfPlane.ofComplex) ((↑↑N : ℂ) * ↑↑N) := by
    have := qj_periodic.nat_mul ((N : ℕ) * N)
    simpa [Nat.cast_mul] using this
  intro w
  simp only [Function.comp, qjN]
  by_cases hw : 0 < Complex.im w
  · have hwN : 0 < Complex.im (w + ↑↑N) := by simp [Complex.add_im]; linarith
    have hkey := hqNN ((↑↑N : ℂ) * w)
    rw [show (↑↑N : ℂ) * w + (↑↑N : ℂ) * ↑↑N = (↑↑N : ℂ) * (w + ↑↑N) from by ring] at hkey
    simp only [Function.comp] at hkey
    rw [natPosSMul_ofComplex_coe N hwN, natPosSMul_ofComplex_coe N hw]
    exact hkey
  · have hw0 := le_of_not_gt hw
    have hwN : Complex.im (w + ↑↑N) ≤ 0 := by simp [Complex.add_im]; linarith
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos hw0,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hwN]

lemma qjN_holomorphic (N : ℕ+) :
    ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (qjN N ∘ UpperHalfPlane.ofComplex) z := by
  intro z hz
  have hNz : 0 < Complex.im ((↑↑N : ℂ) * z) := by
    rw [Complex.mul_im]
    simp only [natCast_re, natCast_im, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr N.pos) hz
  have hqj := qj_holomorphic _ hNz
  have hN : DifferentiableAt ℂ (fun w => (↑↑N : ℂ) * w) z :=
    (differentiableAt_const _).mul differentiableAt_id
  refine (hqj.comp z hN).congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz] with w hw
  simp only [Function.comp, qjN]
  rw [natPosSMul_ofComplex_coe N hw]

lemma qjN_IsBoundedAtImInfty (N : ℕ+) :
    IsBoundedAtImInfty (qjN N) := by
  apply qj_IsBoundedAtImInfty.comp_tendsto
  rw [show atImInfty = Filter.comap UpperHalfPlane.im
    Filter.atTop from rfl, Filter.tendsto_comap_iff]
  have hN_pos : (0 : ℝ) < ↑↑N := Nat.cast_pos.mpr N.pos
  have him_eq :
      UpperHalfPlane.im ∘ (fun x : ℍ => N • x) = (fun x => ↑↑N * x) ∘ UpperHalfPlane.im := by
    ext τ
    simp only [Function.comp, UpperHalfPlane.im, natPosSMul_apply, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  rw [him_eq]
  exact (Filter.Tendsto.const_mul_atTop hN_pos Filter.tendsto_id).comp Filter.tendsto_comap

lemma qjN_cuspFunction_analyticAt (N : ℕ+) : AnalyticAt ℂ (cuspFunction N (qjN N)) 0 :=
  DifferentiableOn.analyticAt (fun q hq => (differentiableOn_cuspFunction_ball'
    (Nat.cast_pos.mpr N.pos) (qjN_periodic N) (qjN_holomorphic N) (qjN_IsBoundedAtImInfty N)) q hq)
      (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

lemma jN_cuspFunction_eq (N : ℕ+) {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    cuspFunction N (jN N) q = q⁻¹ ^ ((N : ℕ) * N) * cuspFunction N (qjN N) q := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr N.pos
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
  have hcexp : cexp (2 * ↑π * Complex.I * (↑(N • τ) : ℂ)) = q ^ ((N : ℕ) * N) := by
    rw [natPosSMul_apply, show 2 * ↑π * Complex.I * ((↑↑N : ℂ) * (τ : ℂ)) = ↑((N : ℕ) * N) *
      (2 * ↑π * Complex.I * (τ : ℂ) / ↑↑N) from by field_simp; push_cast; ring, Complex.exp_nat_mul]
    congr 1
    simpa [τ, Periodic.qParam] using Periodic.qParam_right_inv (ne_of_gt hN) hq0
  rw [hjN_eq, hqjN_eq]
  simp only [jN, qjN, Function.comp, qj, Pi.mul_apply]
  rw [hcexp, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq0), one_mul]

lemma jN_cuspFunction_Meromorphic (N : ℕ+) : MeromorphicAt (cuspFunction N (jN N)) (0 : ℂ) := by
  have hqjN_mer : MeromorphicAt (cuspFunction N (qjN N)) (0 : ℂ) := by
    change MeromorphicAt (Function.Periodic.cuspFunction N (qjN N ∘ UpperHalfPlane.ofComplex)) 0
    exact (qjN_cuspFunction_analyticAt N).meromorphicAt
  have hpow : MeromorphicAt (fun q : ℂ => q⁻¹ ^ ((N : ℕ) * N)) (0 : ℂ) :=
    ((MeromorphicAt.id (0 : ℂ)).inv).pow _
  refine (hpow.mul hqjN_mer).congr ?_
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds (by simpa [Metric.ball, dist_eq_norm]
      using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hq hq'
  simp only [Pi.mul_apply]
  exact (jN_cuspFunction_eq N (by simpa using hq') hq).symm

lemma jN_Meromorphic (N : ℕ+) {z : ℍₒ} :
    DifferentiableAt ℂ (jN N ∘ UpperHalfPlane.ofComplex) z := by
  obtain ⟨z, hz⟩ := z
  have hz' := Set.mem_setOf.mp hz
  have hNz : 0 < Complex.im ((↑↑N : ℂ) * z) := by
    rw [Complex.mul_im]
    simp only [natCast_re, natCast_im, zero_mul, add_zero, Nat.cast_pos, PNat.pos,
        mul_pos_iff_of_pos_left]
    exact hz'
  have hE4 := ModularFormClass.differentiableAt_comp_ofComplex (f := E4) hNz
  have hΔ := ModularFormClass.differentiableAt_comp_ofComplex (f := Delta) hNz
  have hΔ0 : (Delta ∘ UpperHalfPlane.ofComplex) (↑↑N * z) ≠ 0 := by
    simp only [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hNz, Delta_apply]
    exact Δ_ne_zero _
  have hj : DifferentiableAt ℂ (j ∘ UpperHalfPlane.ofComplex) (↑↑N * z) := by
    simpa [j, Function.comp] using (hE4.pow 3).div hΔ hΔ0
  have hN : DifferentiableAt ℂ (· * (↑↑N : ℂ)) z := differentiableAt_id.mul_const _
  have hcomp := hj.comp z (by
    change DifferentiableAt ℂ (fun w => (↑↑N : ℂ) * w) z
    exact differentiableAt_const _ |>.mul differentiableAt_id)
  have hEq : (jN N ∘ UpperHalfPlane.ofComplex)
      =ᶠ[nhds z] ((j ∘ UpperHalfPlane.ofComplex) ∘ fun w => (↑↑N : ℂ) * w) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz']
      with w hw
    simp only [Function.comp, jN, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (↑↑N * w).im by
        rw [Complex.mul_im]; simp only [natCast_re, natCast_im, zero_mul, add_zero, Nat.cast_pos,
            PNat.pos, mul_pos_iff_of_pos_left]; exact hw)]
    exact congr_arg j (UpperHalfPlane.ext rfl)
  change DifferentiableAt ℂ (jN N ∘ UpperHalfPlane.ofComplex) z
  have hcomp' : DifferentiableAt ℂ ((j ∘ UpperHalfPlane.ofComplex) ∘ fun w => (↑↑N : ℂ) * w) z := by
    convert hcomp using 2
  exact hcomp'.congr_of_eventuallyEq hEq

end modularEquation
