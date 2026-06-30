import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.NormTrace

set_option linter.style.header false

open Filter ModularForm ModularFormClass MatrixGroups Function CongruenceSubgroup
open scoped Manifold
open UpperHalfPlane hiding I

local notation "𝕢" => Periodic.qParam

noncomputable section

private abbrev E4 : ModularForm 𝒮ℒ 4 := ModularForm.E₄

private abbrev Delta : CuspForm 𝒮ℒ 12 := CuspForm.discriminant

/-- This defines the `j` function as E4^3/Δ -/
def j : ℍ → ℂ := fun τ ↦ (E4 τ) ^ 3 / Delta τ

lemma j_slashInvariant (γ : SL(2, ℤ)) : j ∣[(0 : ℤ)] γ = j := by
  ext z
  rw [slash_action_eq'_iff, j, j]
  have h1 := congrFun (E4.slash_action_eq' γ ⟨γ, rfl⟩) z
  have h2 := congrFun (Delta.slash_action_eq' γ ⟨γ, rfl⟩) z
  rw [← ModularForm.SL_slash] at h1 h2
  rw [ModularForm.slash_action_eq'_iff] at h1 h2
  simp only [SlashInvariantForm.toFun_eq_coe] at h1 h2
  let d : ℂ := (γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)
  change E4.toSlashInvariantForm (γ • z) = d ^ (4 : ℤ) * E4.toSlashInvariantForm z at h1
  change Delta.toSlashInvariantForm (γ • z) = d ^ (12 : ℤ) *
    Delta.toSlashInvariantForm z at h2
  change (E4.toSlashInvariantForm (γ • z)) ^ 3 / Delta.toSlashInvariantForm (γ • z) =
    d ^ (0 : ℤ) * (E4.toSlashInvariantForm z ^ 3 / Delta.toSlashInvariantForm z)
  rw [h1, h2]
  simp only [zpow_zero, one_mul]
  have hden : d ≠ 0 := by
    dsimp [d]
    simpa [ModularGroup.denom_apply] using denom_ne_zero γ z
  have hDnz : Delta.toSlashInvariantForm z ≠ 0 := by
    simpa [Delta] using ModularForm.discriminant_ne_zero z
  field_simp [hden, hDnz]

def Deltaoverq : ℍ → ℂ := fun z ↦ ∏' (n : ℕ), (1 - ModularForm.eta_q n z) ^ 24

lemma Delta_eq_q_mul_Deltaoverq (z : ℍ) : Delta z = 𝕢 1 z * Deltaoverq z := by
  simpa [Delta, Deltaoverq] using ModularForm.discriminant_eq_q_prod z

lemma Deltaoverq_ne_zero (z : ℍ) : Deltaoverq z ≠ 0 := by
  intro h
  have hD : Delta z = 0 := by simp [Delta_eq_q_mul_Deltaoverq z, h]
  exact ModularForm.discriminant_ne_zero z (by simpa [Delta] using hD)

def qoverDelta : ℍ → ℂ := fun z ↦ 1 / Deltaoverq z

def qj : ℍ → ℂ := (fun z ↦ 𝕢 1 z : ℍ → ℂ) * j

lemma qjIdentity : (fun z : ℍ => (E4 z) ^ 3) * qoverDelta = qj := by
  ext z
  change (E4 z) ^ 3 * qoverDelta z = 𝕢 1 z * ((E4 z) ^ 3 / Delta z)
  have hDnz : Delta z ≠ 0 := by simpa [Delta] using ModularForm.discriminant_ne_zero z
  have hq : 𝕢 1 z ≠ 0 := by simp [Periodic.qParam]
  have hDoq : Deltaoverq z ≠ 0 := Deltaoverq_ne_zero z
  rw [qoverDelta]
  have hD := Delta_eq_q_mul_Deltaoverq z
  field_simp [hDnz, hq, hDoq, hD]
  rw [hD]
  ring

lemma Deltaoverq_tendsto_atImInfty : Tendsto Deltaoverq atImInfty (nhds (1 : ℂ)) := by
  simpa [Deltaoverq] using ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow

lemma qoverDelta_tendsto_atImInfty : Tendsto qoverDelta atImInfty (nhds (1 : ℂ)) := by
  have h : Tendsto (fun τ : ℍ => (Deltaoverq τ)⁻¹) atImInfty (nhds ((1 : ℂ)⁻¹)) :=
    Deltaoverq_tendsto_atImInfty.inv₀ (by norm_num)
  change Tendsto (fun τ : ℍ => (1 / Deltaoverq τ)) atImInfty (nhds (1 : ℂ))
  simpa [one_div] using h

lemma E4_tendsto_atImInfty : Tendsto (E4 : ℍ → ℂ) atImInfty (nhds (1 : ℂ)) := by
  have han : AnalyticAt ℂ (cuspFunction 1 (E4 : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero (h := (1 : ℝ)) E4 (by norm_num)
      one_mem_strictPeriods_SL
  have hper : Periodic ((E4 : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex E4 one_mem_strictPeriods_SL
  have h0 : cuspFunction 1 (E4 : ℍ → ℂ) 0 = 1 := by
    have hcoeff : (qExpansion 1 (E4 : ℍ → ℂ)).coeff 0 = 1 := by
      simpa [E4] using (EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) ⟨2, rfl⟩)
    simpa [qExpansion_coeff] using hcoeff
  have hlim : Tendsto (fun τ : ℍ => cuspFunction 1 (E4 : ℍ → ℂ) (𝕢 (1 : ℝ) τ)) atImInfty
        (nhds (cuspFunction 1 (E4 : ℍ → ℂ) 0)) :=
    han.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num))
  have hfun : (fun τ : ℍ => cuspFunction 1 (E4 : ℍ → ℂ) (𝕢 (1 : ℝ) τ)) = (E4 : ℍ → ℂ) :=
    funext fun τ => UpperHalfPlane.eq_cuspFunction (h := 1) (f := (E4 : ℍ → ℂ)) τ
      (by norm_num) hper
  simpa [hfun, h0] using hlim

lemma j_MDifferentiable : MDiff j := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hE4 : DifferentiableAt ℂ (E4 ∘ UpperHalfPlane.ofComplex) z :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo E4 ⟨z, hz⟩)
  have hDelta : DifferentiableAt ℂ (Delta ∘ UpperHalfPlane.ofComplex) z :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo Delta ⟨z, hz⟩)
  have hDelta0 : (Delta ∘ UpperHalfPlane.ofComplex) z ≠ 0 := by
    simpa [comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz, Delta] using
      ModularForm.discriminant_ne_zero (UpperHalfPlane.ofComplex z)
  have hj : DifferentiableAt ℂ (j ∘ UpperHalfPlane.ofComplex) z := by
    simpa [j, comp] using (hE4.pow 3).div hDelta hDelta0
  exact hj.differentiableWithinAt

theorem qj_tendsto_atImInfty : Tendsto qj atImInfty (nhds (1 : ℂ)) := by
  have hE4 : Tendsto (fun τ : ℍ => (E4 τ) ^ 3) atImInfty (nhds ((1 : ℂ) ^ 3)) :=
    E4_tendsto_atImInfty.pow 3
  have hqj : Tendsto ((fun τ : ℍ => (E4 τ) ^ 3) * qoverDelta) atImInfty
      (nhds ((1 : ℂ) ^ 3 * 1)) :=
    hE4.mul qoverDelta_tendsto_atImInfty
  have hEq : ((fun τ : ℍ => (E4 τ) ^ 3) * qoverDelta) = qj := by
    ext τ
    exact congrFun qjIdentity τ
  simpa [hEq] using hqj

theorem zero_at_cusps_of_zero_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {k : ℤ}
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic]
    (hc : IsCusp c 𝒢) (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsZeroAtImInfty (f ∣[k] A)) :
    c.IsZeroAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  refine (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun A hA ↦ hb A ⟨A, rfl⟩

def levelOneWeightZeroCuspForm {f : ℍ → ℂ} (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f)
    (hmdiff : MDiff f) (hzero : IsZeroAtImInfty f) : CuspForm (Gamma 1) 0 where
  toFun := f
  slash_action_eq' := fun γ hγ => by
    obtain ⟨γ', _, rfl⟩ := hγ
    exact hslash γ'
  holo' := hmdiff
  zero_at_cusps' := fun hc =>
    zero_at_cusps_of_zero_at_infty hc fun A hA => by
      obtain ⟨γ, rfl⟩ := hA
      have hγ : f ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = f := hslash γ
      simpa [hγ] using hzero

theorem weight_zero_cuspForm_eq_zero {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hmdiff : MDiff f) (hzero : IsZeroAtImInfty f) :
    f = 0 := by
  let F : ModularForm (Gamma 1) 0 := levelOneWeightZeroCuspForm hslash hmdiff hzero
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero F
  have hc0 : c = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hc ▸ show IsZeroAtImInfty ⇑F from hzero)
  ext z
  simpa [hc0] using congrFun hc z

theorem f_slashInvariant (c : ℂ) : letI f : ℍ → ℂ := fun τ => (j τ - c)⁻¹
    ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f := by
  intro γ
  ext τ
  have hj := congrFun (j_slashInvariant γ) τ
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one] at hj ⊢
  simpa [hj]

theorem f_MDiff (c : ℂ) (hc : ∀ τ : ℍ, j τ ≠ c) :
    MDiff (fun τ : ℍ => (j τ - c)⁻¹) := fun τ =>
  ((j_MDifferentiable τ).sub mdifferentiableAt_const).inv (sub_ne_zero.mpr (hc τ))

theorem f_IsZeroAtInfty (c : ℂ) : IsZeroAtImInfty (fun τ : ℍ => (j τ - c)⁻¹) := by
  let q : ℍ → ℂ := fun τ => 𝕢 1 τ
  have hq : Tendsto q atImInfty (nhds 0) := qParam_tendsto_atImInfty (by norm_num)
  have hden : Tendsto (fun τ : ℍ => qj τ - c * q τ) atImInfty (nhds 1) := by
    simpa using qj_tendsto_atImInfty.sub (tendsto_const_nhds.mul hq)
  have hratio : Tendsto (fun τ : ℍ => q τ / (qj τ - c * q τ)) atImInfty (nhds 0) := by
    simpa using hq.mul (hden.inv₀ (by norm_num : (1 : ℂ) ≠ 0))
  have hEq : (fun τ : ℍ => (j τ - c)⁻¹) =ᶠ[atImInfty] fun τ : ℍ => q τ / (qj τ - c * q τ) := by
    refine Eventually.of_forall fun τ => ?_
    simp only [show qj τ = q τ * j τ from by simp [q, qj, Periodic.qParam]]
    field_simp [show q τ ≠ 0 from by simp [q, Periodic.qParam]]
  exact hratio.congr' hEq.symm

/-- The modular `j`-function is surjective. -/
theorem j_surjective : Function.Surjective j := by
  intro c
  by_contra! hc
  let f : ℍ → ℂ := fun τ => (j τ - c)⁻¹
  have hf := weight_zero_cuspForm_eq_zero (f_slashInvariant c) (f_MDiff c hc) (f_IsZeroAtInfty c)
  have τ : ℍ := Classical.arbitrary ℍ
  exact inv_ne_zero (sub_ne_zero.mpr (hc τ)) (congrFun hf τ)
