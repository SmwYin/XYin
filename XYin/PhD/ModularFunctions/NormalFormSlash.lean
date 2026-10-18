/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Normal forms and the slash action

The weight-zero slash action preserves meromorphic functions in normal form, including for
matrices of negative determinant, whose action conjugates both the source and target.

This file also collects small facts about the slash action used throughout the modular-function
development: the weight-zero slash action of `SL₂(ℤ)` is composition
(`ModularForm.SL_slash_zero_eq`), integral matrices act holomorphically
(`UpperHalfPlane.sl2_mdifferentiable`), and the slash action preserves agreement on punctured
neighborhoods (`UpperHalfPlane.slash_eventuallyEq_nhdsNE`).
-/

open Filter Complex UpperHalfPlane ModularForm

open scoped Topology UpperHalfPlane Manifold MatrixGroups ComplexConjugate

/-- Analytic changes of coordinate with nonzero derivative preserve meromorphic normal form. -/
lemma MeromorphicNFAt.comp_analyticAt_of_deriv_ne_zero {f g : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicNFAt f (g x)) (hg : AnalyticAt ℂ g x) (hg' : deriv g x ≠ 0) :
    MeromorphicNFAt (f ∘ g) x := by
  rw [meromorphicNFAt_iff_analyticAt_or] at hf ⊢
  rcases hf with hf | ⟨hf, horder, hzero⟩
  · exact Or.inl (hf.comp hg)
  · exact Or.inr ⟨hf.comp_analyticAt hg,
      (meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) hg hg').symm ▸ horder, hzero⟩

/-- Conjugating the source and target preserves complex analyticity. -/
lemma AnalyticAt.conj_conj {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f (conj x)) :
    AnalyticAt ℂ (fun z ↦ conj (f (conj z))) x := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [continuous_conj.continuousAt.eventually hf.eventually_analyticAt] with z hz
  simpa using! hz.differentiableAt.star_star

/-- Conjugating the source and target preserves meromorphic normal form. -/
lemma MeromorphicNFAt.conj_conj {f : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicNFAt f (conj x)) :
    MeromorphicNFAt (fun z ↦ conj (f (conj z))) x := by
  rcases hf with hf | ⟨n, g, hg, hgzero, heq⟩
  · left
    filter_upwards [hf.comp_tendsto continuous_conj.continuousAt] with z hz
    simpa using congrArg conj hz
  · right
    refine ⟨n, fun z ↦ conj (g (conj z)), hg.conj_conj, by simpa using hgzero, ?_⟩
    filter_upwards [heq.comp_tendsto continuous_conj.continuousAt] with z hz
    simpa using congrArg conj hz

/-- The weight-zero slash action of `SL₂(ℤ)` is composition with the Möbius action. -/
theorem ModularForm.SL_slash_zero_eq (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    f ∣[(0 : ℤ)] γ = fun τ ↦ f (γ • τ) := by
  ext τ
  simp [SL_slash_apply]

/-- A function is invariant under the weight-zero slash action of `γ ∈ SL₂(ℤ)` iff it is
invariant under the Möbius action of `γ`. -/
theorem ModularForm.SL_slash_zero_eq_iff {f : ℍ → ℂ} {γ : SL(2, ℤ)} :
    f ∣[(0 : ℤ)] γ = f ↔ ∀ τ, f (γ • τ) = f τ := by
  rw [SL_slash_zero_eq, funext_iff]

/-- The weight-zero slash action of the pointwise inverse. -/
theorem ModularForm.inv_slash_zero (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) :
    f⁻¹ ∣[(0 : ℤ)] g = (g.det.val ^ 2)⁻¹ • (f ∣[(0 : ℤ)] g)⁻¹ := by
  have hd : ((|g.det.val| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr g.det_ne_zero
  funext τ
  simp only [slash_apply, Pi.inv_apply, map_inv₀, Pi.smul_apply, zero_sub, neg_zero, zpow_zero,
    mul_one, zpow_neg_one, mul_inv, inv_inv, Complex.real_smul]
  rw [← sq_abs, Complex.ofReal_inv, Complex.ofReal_pow]
  field_simp

namespace UpperHalfPlane

/-- Integral matrices of determinant one have positive determinant in `GL₂(ℝ)`. -/
theorem sl2_det_pos (δ : SL(2, ℤ)) : 0 < (δ : GL (Fin 2) ℝ).det.val := by
  simp

/-- The action of an integral determinant-one matrix is holomorphic. -/
lemma sl2_mdifferentiable (delta : SL(2, ℤ)) :
    MDiff (fun tau : ℍ ↦ delta • tau) :=
  mdifferentiable_smul (sl2_det_pos delta)

/-- The slash action preserves agreement on punctured neighborhoods. -/
theorem slash_eventuallyEq_nhdsNE {f g : ℍ → ℂ} (k : ℤ) (γ : GL (Fin 2) ℝ) {τ : ℍ}
    (h : ∀ᶠ w in 𝓝[≠] (γ • τ), f w = g w) : ∀ᶠ w in 𝓝[≠] τ, (f ∣[k] γ) w = (g ∣[k] γ) w := by
  filter_upwards [((Homeomorph.smul γ).map_punctured_nhds_eq τ).le h]
    with w (hw : f (γ • w) = g (γ • w))
  simp only [slash_apply, hw]

private lemma meromorphicNFOn_slash_zero_of_pos {f : ℍ → ℂ}
    (hf : MeromorphicNFOn (f ∘ ofComplex) {z : ℂ | 0 < z.im})
    {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    MeromorphicNFOn ((f ∣[(0 : ℤ)] g) ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  intro z hz
  let τ : ℍ := ⟨z, hz⟩
  have hf' : MeromorphicNFAt (f ∘ ofComplex) (↑(g • ofComplex (τ : ℂ)) : ℂ) := by
    simpa only [ofComplex_apply] using hf (g • τ).im_pos
  have hcomp := hf'.comp_analyticAt_of_deriv_ne_zero
    (g := fun z : ℂ ↦ (↑(g • ofComplex z) : ℂ))
    (τ.analyticAt_smul hg) (τ.deriv_smul_ne_zero hg)
  have hnf : MeromorphicNFAt (fun z ↦ f (g • ofComplex z)) z := by
    simpa [Function.comp_def, τ] using hcomp
  have hconst : ((|g.det.val| : ℝ) : ℂ) ^ (-1 : ℤ) ≠ 0 := by
    exact zpow_ne_zero _ (by exact_mod_cast abs_ne_zero.mpr g.det_ne_zero)
  convert (meromorphicNFAt_mul_iff_left analyticAt_const hconst).mpr hnf using 1
  ext w
  simp only [Function.comp_apply, slash_apply, σ, hg, ↓reduceIte,
    ContinuousAlgEquiv.refl_apply, zero_sub, neg_zero, zpow_zero, mul_one, Pi.mul_apply]

private lemma meromorphicNFOn_slash_zero_J {f : ℍ → ℂ}
    (hf : MeromorphicNFOn (f ∘ ofComplex) {z : ℂ | 0 < z.im}) :
    MeromorphicNFOn ((f ∣[(0 : ℤ)] J) ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hpos : 0 < (-conj z).im := by simpa using hz
  have hneg : MeromorphicNFAt ((f ∘ ofComplex) ∘ Neg.neg) (conj z) :=
    (hf hpos).comp_analyticAt_of_deriv_ne_zero (by fun_prop) (by simp)
  have hnf := hneg.conj_conj
  apply (meromorphicNFAt_congr ?_).mpr hnf
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  norm_num [Function.comp_def, slash_apply, σ, J_smul, ofComplex_apply_of_im_pos hw]

/-- The weight-zero slash action preserves meromorphic normal form on the upper half-plane. -/
lemma meromorphicNFOn_slash_zero {f : ℍ → ℂ}
    (hf : MeromorphicNFOn (f ∘ ofComplex) {z : ℂ | 0 < z.im})
    (g : GL (Fin 2) ℝ) :
    MeromorphicNFOn ((f ∣[(0 : ℤ)] g) ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  rcases g.det_ne_zero.lt_or_gt with hg | hg
  · rw [show g = J * (J * g) by simp [← mul_assoc, ← sq], SlashAction.slash_mul]
    exact meromorphicNFOn_slash_zero_of_pos (meromorphicNFOn_slash_zero_J hf)
      (by simpa using hg)
  · exact meromorphicNFOn_slash_zero_of_pos hf hg

end UpperHalfPlane
