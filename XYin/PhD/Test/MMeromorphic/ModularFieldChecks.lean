import XYin.PhD.Test.MMeromorphic.ModularField
import XYin.PhD.Test.MMeromorphic.ChartsChecks

/-! Tests of predicate-first modular field construction, including a pole at the cusp. -/

open UpperHalfPlane Set
open scoped Manifold Topology MatrixGroups

namespace MMeromorphicTest.Modular

noncomputable section

variable {ι : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {c : ι → CuspCoordinate}
  {f g : ℍ → ℂ}

-- The more general chart predicate gives an ambient field element by a theorem.
example (hf : MMeromorphicExperiment.Charts.MMeromorphic f) : Ambient :=
  toAmbient (MMeromorphicExperiment.Charts.mMeromorphic_upperHalfPlane_iff.mp hf)

-- The raw modular definition is checked before the field element is constructed.
example (hf : IsModularFunction Γ c f) : ModularFunctionField Γ c := hf.toField Γ c

example (hf : IsModularFunction Γ c f) (hg : IsModularFunction Γ c g) :
    IsModularFunction Γ c ((f + g) * f⁻¹) := (hf.add hg).mul hf.inv

example (a : ModularFunctionField Γ c) (ha : a ≠ 0) : a * a⁻¹ = 1 := mul_inv_cancel₀ ha

/-- The ordinary cusp at infinity, with width one. -/
def infinityCoordinate : CuspCoordinate where
  scaling := 1
  scaling_pos := by simp
  width := 1
  width_pos := zero_lt_one

/-- A test function with a simple pole in its q-coordinate at infinity. -/
def inverseQ (τ : ℍ) : ℂ := (Function.Periodic.qParam 1 (τ : ℂ))⁻¹

theorem inverseQ_meromorphic : UHP.Meromorphic inverseQ := by
  apply UHP.inv
  apply UHP.of_mdifferentiable
  exact (Function.Periodic.differentiable_qParam.mdifferentiable).comp
    UpperHalfPlane.mdifferentiable_coe

theorem inverseQ_atCusp : MeromorphicAtCusp infinityCoordinate inverseQ := by
  refine ⟨fun z ↦ z⁻¹, (MeromorphicAt.id 0).inv, ?_⟩
  filter_upwards with τ
  simp [inverseQ, infinityCoordinate]

-- A cusp pole is allowed; boundedness at the cusp would reject this test.
theorem inverseQ_isModular :
    IsModularFunction (⊥ : Subgroup (GL (Fin 2) ℝ))
      (fun _ : Unit ↦ infinityCoordinate) inverseQ := by
  refine ⟨inverseQ_meromorphic, ?_, fun _ ↦ inverseQ_atCusp⟩
  intro γ hγ τ
  have hγone : γ = 1 := by simpa using hγ
  simp [hγone]

example : ModularFunctionField (⊥ : Subgroup (GL (Fin 2) ℝ))
    (fun _ : Unit ↦ infinityCoordinate) := inverseQ_isModular.toField _ _

#print axioms inverseQ_isModular
#print axioms modularSubfield

end

end MMeromorphicTest.Modular
