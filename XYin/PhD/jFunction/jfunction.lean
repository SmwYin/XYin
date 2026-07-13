import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import XYin.PhD.IntegralPowerSeries.HasIntegralQExpansion
import XYin.PhD.jFunction.Deltaqexpansions
import XYin.PhD.LaurentQExpansion.LaurentQExpansion

set_option linter.style.header false

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups PowerSeries
  SlashInvariantFormClass Real Function IntegralPowerSeries
open scoped Manifold

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
  simp only [ModularForm.slash_action_eq'_iff, SlashInvariantForm.toFun_eq_coe,
    toSlashInvariantForm_coe, Fin.isValue] at h1
  rw [ModularForm.slash_action_eq'_iff, CuspForm_apply, CuspForm_apply] at h2
  rw [h1, h2]
  ring_nf
  have h3 := pow_ne_zero 12 (denom_ne_zero γ z)
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

lemma DeltaoverqIdentity :
    Deltaoverq = (fun z ↦ 1 / cexp (2 * π * Complex.I * z) : ℍ → ℂ) * Delta := by
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
      (CuspFormClass.cuspFunction_apply_zero Delta (by norm_num) (by simp))
  have hq : q ≠ 0 := by simp [q]
  have hs : HasSum a (Delta z) := by
    have hDelta := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := Delta) (by norm_num)
        (SlashInvariantFormClass.periodic_comp_ofComplex Delta (by simp))
        (ModularFormClass.holo Delta) (ModularFormClass.bdd_at_infty Delta) z
    simpa [a, q, smul_eq_mul, Periodic.qParam] using hDelta
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
        (CuspFormClass.cuspFunction_apply_zero Delta (by norm_num) (by simp))
  have hs : HasSum (fun m => (qExpansion 1 Delta).coeff m • q ^ m) (Delta z) := by
    have hDelta := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := Delta) (by norm_num)
        (SlashInvariantFormClass.periodic_comp_ofComplex Delta (by simp))
        (ModularFormClass.holo Delta) (ModularFormClass.bdd_at_infty Delta) z
    simpa [q] using hDelta
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
  simpa [cshift] using (UpperHalfPlane.qExpansion_coeff_unique (f := InfSumDeltashift)
      (h := 1) (by norm_num) InfSumDeltashift_AnalyticAt InfSumDeltashift_hasSum n).symm

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
    (coeToComplexPowerSeries.ringHom ℤ) integralDeltaoverq = qExpansion 1 Deltaoverq := by
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
    have hmap : PowerSeries.coeff 0 ((coeToComplexPowerSeries.ringHom ℤ) integralDeltaoverq) =
        ((PowerSeries.coeff 0 integralDeltaoverq : ℤ) : ℂ) := by
      simp [coeToComplexPowerSeries.ringHom, powerSeriesMapAlgHom,
        PowerSeries.coeff_zero_eq_constantCoeff]
    have hcoeff0 : ((PowerSeries.coeff 0 integralDeltaoverq : ℤ) : ℂ) = 1 :=
      hmap.symm.trans (by simpa [hcoeff0C] using h0)
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hcoeff0
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
  exact ModularFormClass.analyticAt_cuspFunction_zero E4 (by norm_num) (by simp)

lemma E4cubed_isModularForm : ∃ f : ModularForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
    (CongruenceSubgroup.Gamma 1)) 12, (f : ℍ → ℂ) = E4 ^ 3 := by
  refine ⟨E4.mul (E4.mul E4), ?_⟩
  funext z
  simpa [pow_three] using congrFun (ModularForm.coe_mul E4 (E4.mul E4)) z

lemma E4cubed_AnalyticAt : AnalyticAt ℂ (cuspFunction 1 (E4 ^ 3)) 0 := by
  rcases E4cubed_isModularForm with ⟨f, hf⟩
  simpa [hf] using
    (ModularFormClass.analyticAt_cuspFunction_zero f (by norm_num) (by simp))

lemma integralDeltaoverq_mul_qoverDelta_qExpansion :
    (coeToComplexPowerSeries.ringHom ℤ) integralDeltaoverq * qExpansion 1 qoverDelta = 1 := by
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
  · simp only [hz, Nat.factorial_zero, Nat.cast_one, inv_one, UpperHalfPlane.cuspFunction,
        Pi.one_comp, iteratedDeriv_zero, one_mul, coeff_one, ↓reduceIte, Periodic.cuspFunction,
        Pi.one_comp, update_self]
    exact Tendsto.limUnder_eq tendsto_const_nhds
  · simp only [UpperHalfPlane.cuspFunction, Pi.one_comp, coeff_one, hz, ↓reduceIte,
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
  have h : (coeToComplexPowerSeries.ringHom ℤ) integralDeltaoverq
      * (coeToComplexPowerSeries.ringHom ℤ) (↑(u⁻¹) : PowerSeries ℤ) = 1 := by
    calc
    _ = (coeToComplexPowerSeries.ringHom ℤ) (↑u)
        * (coeToComplexPowerSeries.ringHom ℤ) (↑(u⁻¹) : PowerSeries ℤ) := by simp [hu]
    _ = (coeToComplexPowerSeries.ringHom ℤ) ((↑u) * (↑(u⁻¹) : PowerSeries ℤ)) := by
      rw [← map_mul]
    _ = _ := by simp
  symm
  calc
  _ = 1 * qExpansion 1 qoverDelta := by simp
  _ = ((coeToComplexPowerSeries.ringHom ℤ) integralDeltaoverq *
        (coeToComplexPowerSeries.ringHom ℤ) (↑(u⁻¹) : PowerSeries ℤ)) *
      qExpansion 1 qoverDelta := by rw [← h]
  _ = (coeToComplexPowerSeries.ringHom ℤ) (↑(u⁻¹) : PowerSeries ℤ) *
      ((coeToComplexPowerSeries.ringHom ℤ) integralDeltaoverq *
        qExpansion 1 qoverDelta) := by ring
  _ = _ := by
    rw [integralDeltaoverq_mul_qoverDelta_qExpansion]
    simp

lemma qjauxIsIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3 * qoverDelta)) := by
  rw [qExpansion_mul E4cubed_AnalyticAt qoverDelta_AnalyticAt]
  exact hasCoeffsIn_mul ℤ ℂ E4CubedIsIntegralPowerSeries qoverDeltaIsIntegralPowerSeries

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
        (SlashInvariantForm.vAdd_apply_of_mem_strictPeriods (f := E4) (τ := τ) (hH := by simp))
    have hDelta : Delta ((1 : ℝ) +ᵥ τ) = Delta τ := by
      simpa using
        (SlashInvariantForm.vAdd_apply_of_mem_strictPeriods (f := Delta) (τ := τ) (hH := by simp))
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
    UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo E4 ⟨z, hz⟩)
  have hDelta : DifferentiableAt ℂ (Delta ∘ UpperHalfPlane.ofComplex) z :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo Delta ⟨z, hz⟩)
  have hDelta0 : (Delta ∘ UpperHalfPlane.ofComplex) z ≠ 0 := by
    simpa [comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz, Delta_apply] using
      (Δ_ne_zero (UpperHalfPlane.ofComplex z))
  have hj : DifferentiableAt ℂ (j ∘ UpperHalfPlane.ofComplex) z := by
    simpa [j, comp] using (hE4.pow 3).div hDelta hDelta0
  simpa [qj, comp, Pi.mul_apply] using hexpH.mul hj

lemma qj_MDifferentiable : MDiff qj := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  exact (qj_holomorphic z hz).differentiableWithinAt

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
  exact UpperHalfPlane.hasSum_qExpansion (h := 1) (f := qj) (by positivity) qj_periodic
    qj_MDifferentiable qj_IsBoundedAtImInfty τ

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

/-- The regularized modular invariant `qj` has constant coefficient one. -/
lemma qj_qExpansion_coeff_zero : (qExpansion 1 qj).coeff 0 = 1 := by
  have hqj : qExpansion 1 qj = qExpansion 1 (E4 ^ 3 * qoverDelta) := by
    simpa [qj] using congrArg (qExpansion 1) qjIdentity.symm
  have hmul :
      qExpansion 1 (E4 ^ 3 * qoverDelta) = qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta := by
    exact qExpansion_mul E4cubed_AnalyticAt qoverDelta_AnalyticAt
  have hE4pow : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := by simp) E4 3
  have hE4coeff0 : (qExpansion 1 E4).coeff 0 = 1 := by
    simpa [UpperHalfPlane.qExpansion_coeff, E4] using
      EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) ⟨2, rfl⟩
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
  UpperHalfPlane.differentiableOn_cuspFunction_ball (h := 1) (f := qj) (by norm_num)
    qj_periodic qj_MDifferentiable qj_IsBoundedAtImInfty

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
    simpa [qExpansion_coeff] using qj_qExpansion_coeff_zero
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
    simpa [F, qExpansion_coeff] using qj_qExpansion_coeff_zero
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
    have hcoeff : (((qj_coeffs (Int.toNat (n + 1)) : ℤ) : ℂ)) =
        (qExpansion 1 qj).coeff (Int.toNat (n + 1)) := by
      simpa [qj_coeffs] using congrArg (PowerSeries.coeff (Int.toNat (n + 1)))
        (coeTo_of_toIntegralPowerSeries qjIsIntegralPowerSeries)
    calc
    _ = (to_qExpansion 1 j).coeff (Int.toNat (n + poleOrder 1 j)) := by
            simpa using (laurentqExpansion.coeff_of_geq hge)
    _ = (qExpansion 1 qj).coeff (Int.toNat (n + poleOrder 1 j)) := by rw [j_to_qExpansion]
    _ = (qExpansion 1 qj).coeff (Int.toNat (n + 1)) := by simp [j_poleOrder]
    _ = _ := by simpa using hcoeff.symm
