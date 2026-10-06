import XYin.PhD.Cox.ModularFunctionField

/-!
# The actual level-one modular field as rational functions in j

This uses the existing Cox generation theorem for the independent production modular-function
definition. It is an actual algebra equivalence, with the rational coordinate sent to j.
It does not define a geometric X(1) or identify an unconstructed curve with this field.
-/

open UpperHalfPlane UpperHalfPlane.MeromorphicField
open Cox.UpperHalfPlaneFunctionField
open scoped MatrixGroups

noncomputable section

namespace MMeromorphicTest.LevelOneField

/-- Evaluation of a rational function at j as a bundled modular function. -/
def ratFuncToModular : RatFunc ℂ →ₐ[ℂ] ModularFunction 𝒮ℒ where
  toFun r := ModularFunction.ofMeromorphicField (algebraMap (RatFunc ℂ) MeromorphicField r)
    (algebraMap_ratFunc_mem_subfield le_rfl r)
  map_one' := ModularFunction.toMeromorphicField_injective (by simp)
  map_mul' _ _ := ModularFunction.toMeromorphicField_injective (by simp)
  map_zero' := ModularFunction.toMeromorphicField_injective (by simp)
  map_add' _ _ := ModularFunction.toMeromorphicField_injective (by simp)
  commutes' c := ModularFunction.toMeromorphicField_injective (by
    simp only [ModularFunction.toMeromorphicField_ofMeromorphicField,
      ModularFunction.toMeromorphicField_algebraMap]
    exact (IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) MeromorphicField c).symm)

@[simp]
theorem toMeromorphicField_ratFuncToModular (r : RatFunc ℂ) :
    (ratFuncToModular r).toMeromorphicField = algebraMap (RatFunc ℂ) MeromorphicField r :=
  ModularFunction.toMeromorphicField_ofMeromorphicField _
    (algebraMap_ratFunc_mem_subfield le_rfl r)

/-- The Cox generation result supplies surjectivity for the revised modular-function bundle. -/
theorem ratFuncToModular_surjective : Function.Surjective ratFuncToModular := by
  intro f
  obtain ⟨r, hr⟩ := toMeromorphicField_eq_ratFunc f
  exact ⟨r, ModularFunction.toMeromorphicField_injective
    ((toMeromorphicField_ratFuncToModular r).trans hr)⟩

/-- The field of level-one modular functions is the rational function field over ℂ. -/
def ratFuncModularEquiv : RatFunc ℂ ≃ₐ[ℂ] ModularFunction 𝒮ℒ :=
  AlgEquiv.ofBijective ratFuncToModular
    ⟨ratFuncToModular.injective, ratFuncToModular_surjective⟩

@[simp]
theorem ratFuncModularEquiv_apply (r : RatFunc ℂ) :
    ratFuncModularEquiv r = ratFuncToModular r := rfl

/-- The coordinate of the rational function field maps to the classical modular invariant. -/
theorem ratFuncModularEquiv_X : ratFuncModularEquiv RatFunc.X = jModularFunction := by
  apply ModularFunction.toMeromorphicField_injective
  rw [ratFuncModularEquiv_apply, toMeromorphicField_ratFuncToModular,
    algebraMap_ratFunc, ← RatFunc.algebraMap_X, ratFuncEvalJ_algebraMap, evalJFracPoly,
    RingHom.comp_apply, evalJ_X]
  symm
  apply ModularFunction.toMeromorphicField_eq_iff.2
  simp [jElement]

example (c : ℂ) : ratFuncModularEquiv (algebraMap ℂ (RatFunc ℂ) c) =
    algebraMap ℂ (ModularFunction 𝒮ℒ) c := ratFuncModularEquiv.commutes c

example (f : ModularFunction 𝒮ℒ) :
    ratFuncModularEquiv (ratFuncModularEquiv.symm f) = f :=
  ratFuncModularEquiv.apply_symm_apply f

#print axioms ratFuncModularEquiv
#print axioms ratFuncModularEquiv_X
#print axioms Cox.theorem_11_9_i_subfield

end MMeromorphicTest.LevelOneField
