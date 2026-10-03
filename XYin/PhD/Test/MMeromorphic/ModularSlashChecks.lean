import XYin.PhD.Test.MMeromorphic.ModularField
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

/-!
# Comparison with mathlib's weight-zero slash invariance

Ordinary invariance and mathlib's weight-zero slash invariance agree on determinant-one
groups. On a general positive-determinant group the pinned slash action also has a
determinant factor, so positivity alone does not justify the comparison.
-/

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace MMeromorphicTest.Modular

noncomputable section

variable {ι : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
  {c : ι → CuspCoordinate}

/-- Determinant one removes the determinant and conjugation factors in weight zero. -/
theorem invariant_iff_slashInvariant (f : ℍ → ℂ) :
    (∀ γ ∈ Γ, ∀ τ : ℍ, f (γ • τ) = f τ) ↔
      (∀ γ ∈ Γ, f ∣[(0 : ℤ)] γ = f) := by
  constructor
  · intro hf γ hγ
    ext τ
    simpa [ModularForm.slash_apply, σ, Subgroup.HasDetOne.det_eq hγ] using hf γ hγ τ
  · intro hf γ hγ τ
    simpa [ModularForm.slash_apply, σ, Subgroup.HasDetOne.det_eq hγ] using
      congr_fun (hf γ hγ) τ

/-- The independently defined raw modular predicate supplies the standard bundled form. -/
def IsModularFunction.toSlashInvariantForm {f : ℍ → ℂ}
    (hf : IsModularFunction Γ c f) : SlashInvariantForm Γ 0 where
  toFun := f
  slash_action_eq' := (invariant_iff_slashInvariant f).mp hf.invariant

@[simp] theorem IsModularFunction.coe_toSlashInvariantForm {f : ℍ → ℂ}
    (hf : IsModularFunction Γ c f) : (hf.toSlashInvariantForm : ℍ → ℂ) = f := rfl

/-- The standard slash-invariant function gives our predicate after its analytic conditions. -/
theorem isModularFunction_of_slashInvariantForm (f : SlashInvariantForm Γ 0)
    (hf : UHP.Meromorphic f) (hc : ∀ i, MeromorphicAtCusp (c i) f) :
    IsModularFunction Γ c f :=
  ⟨hf, (invariant_iff_slashInvariant f).mpr f.slash_action_eq', hc⟩

example {f : ℍ → ℂ} (hf : IsModularFunction Γ c f) : SlashInvariantForm Γ 0 :=
  hf.toSlashInvariantForm

example (f : SlashInvariantForm Γ 0) (hf : UHP.Meromorphic f)
    (hc : ∀ i, MeromorphicAtCusp (c i) f) : ModularFunctionField Γ c :=
  (isModularFunction_of_slashInvariantForm f hf hc).toField Γ c

-- A subgroup of the integer modular group has the required determinant-one instance.
example (Δ : Subgroup SL(2, ℤ)) {f : ℍ → ℂ}
    (hf : IsModularFunction (Δ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) c f) :
    SlashInvariantForm (Δ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) 0 :=
  hf.toSlashInvariantForm

#print axioms invariant_iff_slashInvariant
#print axioms IsModularFunction.toSlashInvariantForm

end

end MMeromorphicTest.Modular
