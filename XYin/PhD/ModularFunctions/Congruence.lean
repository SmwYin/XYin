/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.ModularFunctions.JInvariant

/-!
# Modular functions on congruence subgroups

For `Γ₀(N)`, every integral modular transform has period `N`. This relates the period-free
definition of modular functions to the cusp expansions used in classical function-field
arguments, and supplies a constructor from those expansions.
-/

open Complex Function UpperHalfPlane Matrix.SpecialLinearGroup
open scoped Manifold MatrixGroups ModularForm

noncomputable section

namespace ModularFunction

/-- Restrict a modular function to a subgroup. Every cusp of the subgroup is also a cusp
of the original group. -/
def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (f : ModularFunction Γ) (h : Γ' ≤ Γ) :
    ModularFunction Γ' where
  toFun := f
  slash_action_eq' γ hγ := f.slash_action_eq' γ (h hγ)
  meromorphic' := f.meromorphic'
  bdd_at_cusps' hc := f.bdd_at_cusps (hc.mono h)

@[simp]
theorem coe_restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (f : ModularFunction Γ) (h : Γ' ≤ Γ) :
    (f.restrict h : ℍ → ℂ) = f := rfl

private lemma conjugate_T_pow_mem_Gamma0 (N : ℕ+) (γ : SL(2, ℤ)) :
    γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 (N : ℕ) := by
  have hT : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma (N : ℕ) := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  exact CongruenceSubgroup.Gamma0_mem.mpr
    (CongruenceSubgroup.Gamma_mem.mp ((CongruenceSubgroup.Gamma_normal _).conj_mem _ hT γ)).2.2.1

/-- Every integral modular transform of a weight-zero `Γ₀(N)`-invariant function has period
`N`. No analytic assumptions are needed. -/
theorem periodic_comp_sl2_of_gamma0_invariant (N : ℕ+) {f : ℍ → ℂ}
    (hinv : ∀ γ : CongruenceSubgroup.Gamma0 (N : ℕ), f ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = f)
    (γ : SL(2, ℤ)) : Periodic (fun z : ℂ ↦ f (γ • ofComplex z)) (N : ℂ) := by
  let t : SL(2, ℤ) := ModularGroup.T ^ (N : ℤ)
  let δ : SL(2, ℤ) := γ * t * γ⁻¹
  have hδ : δ ∈ CongruenceSubgroup.Gamma0 (N : ℕ) := conjugate_T_pow_mem_Gamma0 N γ
  have hinv' := ModularForm.SL_slash_zero_eq_iff.mp (hinv ⟨δ, hδ⟩)
  have hperiod (τ : ℍ) : f (γ • ((N : ℝ) +ᵥ τ)) = f (γ • τ) := by
    have hT : t • τ = (N : ℝ) +ᵥ τ := by
      simpa only [t, Int.cast_natCast] using modular_T_zpow_smul τ (N : ℤ)
    rw [← hT]
    simpa only [δ, mul_smul, inv_smul_smul] using hinv' (γ • τ)
  simpa only [Function.comp_def, ofReal_natCast] using
    periodic_comp_ofComplex_of_vadd (f := fun τ ↦ f (γ • τ)) hperiod

/-- Every integral modular transform of a `Γ₀(N)` modular function has period `N`. -/
theorem periodic_comp_sl2_gamma0 (N : ℕ+)
    (f : ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ))) (γ : SL(2, ℤ)) :
    Periodic (fun z : ℂ ↦ f (γ • ofComplex z)) (N : ℂ) := by
  apply periodic_comp_sl2_of_gamma0_invariant N
  intro δ
  exact f.slash_action_eq' _ ⟨δ, δ.property, rfl⟩

/-- The period-`N` cusp expansion of a `Γ₀(N)` modular function is meromorphic at zero. -/
theorem cuspFunction_gamma0 (N : ℕ+)
    (f : ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ))) (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction (N : ℝ) (fun τ : ℍ ↦ f (γ • τ))) 0 := by
  have hc : IsCusp (mapGL ℝ γ • OnePoint.infty)
      (CongruenceSubgroup.Gamma0 (N : ℕ)) :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
      (isCusp_SL2Z_iff'.mpr ⟨γ, rfl⟩)
  have hslash := ModularForm.SL_slash_zero_eq f γ
  have hper : Periodic (((f : ℍ → ℂ) ∣[(0 : ℤ)] γ) ∘ ofComplex) (N : ℝ) := by
    simpa only [hslash, Function.comp_def, ofReal_natCast] using periodic_comp_sl2_gamma0 N f γ
  have hf := f.meromorphicAt_cuspFunction hc rfl (Nat.cast_pos.mpr N.pos) hper
  change MeromorphicAt (cuspFunction (N : ℝ) ((f : ℍ → ℂ) ∣[(0 : ℤ)] γ)) 0 at hf
  simpa only [hslash] using hf

/-- Construct a `Γ₀(N)` modular function from its canonical meromorphic representative,
invariance, and meromorphic period-`N` expansions at every integral cusp. -/
def ofGamma0CuspData (N : ℕ+) (f : ℍ → ℂ)
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet)
    (hinv : ∀ γ : CongruenceSubgroup.Gamma0 (N : ℕ), f ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = f)
    (hcusp : ∀ γ : SL(2, ℤ),
      MeromorphicAt (cuspFunction (N : ℝ) (fun τ : ℍ ↦ f (γ • τ))) 0) :
    ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ)) where
  toFun := f
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact hinv ⟨γ, hγ⟩
  meromorphic' := mmeromorphicNF_iff.2 hf
  bdd_at_cusps' hc := OnePoint.isOfExponentialGrowthAt_of_forall_sl2 (h := (N : ℝ))
    (Nat.cast_pos.mpr N.pos) (fun γ ↦ by
      simpa only [Function.comp_def, ofReal_natCast] using
        periodic_comp_sl2_of_gamma0_invariant N hinv γ) hcusp (hc.mono (Subgroup.map_le_range ..))

@[simp]
theorem coe_ofGamma0CuspData (N : ℕ+) (f : ℍ → ℂ)
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet)
    (hinv : ∀ γ : CongruenceSubgroup.Gamma0 (N : ℕ), f ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = f)
    (hcusp : ∀ γ : SL(2, ℤ),
      MeromorphicAt (cuspFunction (N : ℝ) (fun τ : ℍ ↦ f (γ • τ))) 0) :
    (ofGamma0CuspData N f hf hinv hcusp : ℍ → ℂ) = f := rfl

/-- Construct a `Γ₀(N)` modular function from a holomorphic invariant function whose
period-`N` expansions at every integral cusp are meromorphic. -/
def ofGamma0Holomorphic (N : ℕ+) (f : ℍ → ℂ) (hf : MDiff f)
    (hinv : ∀ γ : CongruenceSubgroup.Gamma0 (N : ℕ), f ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = f)
    (hcusp : ∀ γ : SL(2, ℤ),
      MeromorphicAt (cuspFunction (N : ℝ) (fun τ : ℍ ↦ f (γ • τ))) 0) :
    ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ)) :=
  ofGamma0CuspData N f hf.meromorphicNFOn_comp_ofComplex hinv hcusp

@[simp]
theorem coe_ofGamma0Holomorphic (N : ℕ+) (f : ℍ → ℂ) (hf : MDiff f)
    (hinv : ∀ γ : CongruenceSubgroup.Gamma0 (N : ℕ), f ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = f)
    (hcusp : ∀ γ : SL(2, ℤ),
      MeromorphicAt (cuspFunction (N : ℝ) (fun τ : ℍ ↦ f (γ • τ))) 0) :
    (ofGamma0Holomorphic N f hf hinv hcusp : ℍ → ℂ) = f := rfl

/-- The field element of a holomorphic `Γ₀(N)` modular function is its holomorphic germ. -/
theorem toMeromorphicField_ofGamma0Holomorphic (N : ℕ+) (f : ℍ → ℂ) (hf : MDiff f)
    (hinv : ∀ γ : CongruenceSubgroup.Gamma0 (N : ℕ), f ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = f)
    (hcusp : ∀ γ : SL(2, ℤ),
      MeromorphicAt (cuspFunction (N : ℝ) (fun τ : ℍ ↦ f (γ • τ))) 0) :
    (ofGamma0Holomorphic N f hf hinv hcusp).toMeromorphicField =
      MeromorphicField.ofHolomorphic f hf :=
  toMeromorphicField_eq_iff.2 (MeromorphicField.toFun_ofHolomorphic f hf).symm

/-- Restriction to a subgroup does not change the field element. -/
@[simp]
theorem toMeromorphicField_restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (f : ModularFunction Γ)
    (h : Γ' ≤ Γ) : (f.restrict h).toMeromorphicField = f.toMeromorphicField :=
  toMeromorphicField_eq_iff.2 (f.toFun_toMeromorphicField).symm

end ModularFunction
