import Mathlib.NumberTheory.ModularForms.NormTrace
import XYin.PhD.Modularforms.ForMathlib_Cusps
import XYin.PhD.jFunction.jfunction

set_option linter.style.header false

open Real Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups PowerSeries
  SlashInvariantFormClass Function CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Manifold

local notation "𝕢" => Periodic.qParam

noncomputable section

private def levelOneWeightZeroCuspForm {f : ℍ → ℂ} (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f)
    (hmdiff : MDiff f) (hzero : IsZeroAtImInfty f) : CuspForm (Gamma 1) 0 where
  toFun := f
  slash_action_eq' := fun γ hγ => by
    obtain ⟨γ', _, rfl⟩ := hγ
    exact hslash γ'
  holo' := hmdiff
  zero_at_cusps' := fun hc =>
    zero_at_cusps_of_zero_at_infty hc fun A hA => by
      obtain ⟨γ, rfl⟩ := hA
      have hγ : f ∣[(0 : ℤ)] (mapGL ℝ γ) = f := hslash γ
      simpa [hγ] using hzero

private theorem weight_zero_cuspForm_eq_zero {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hmdiff : MDiff f) (hzero : IsZeroAtImInfty f) :
    f = 0 := by
  let F : ModularForm (Gamma 1) 0 := levelOneWeightZeroCuspForm hslash hmdiff hzero
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero F
  have hc0 : c = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hc ▸ show IsZeroAtImInfty ⇑F from hzero)
  ext z
  simpa [hc0] using congrFun hc z

private theorem f_slashInvariant (c : ℂ) : letI f : ℍ → ℂ := fun τ => (j τ - c)⁻¹
    ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f := by
  intro γ
  ext τ
  have hj := congrFun (j_slashInvariant γ) τ
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one] at hj ⊢
  simpa [hj]

private theorem f_MDiff (c : ℂ) (hc : ∀ τ : ℍ, j τ ≠ c) :
    MDiff (fun τ : ℍ => (j τ - c)⁻¹) := fun τ =>
  ((j_MDifferentiable τ).sub mdifferentiableAt_const).inv (sub_ne_zero.mpr (hc τ))

private theorem f_IsZeroAtInfty (c : ℂ) : IsZeroAtImInfty (fun τ : ℍ => (j τ - c)⁻¹) := by
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

end
