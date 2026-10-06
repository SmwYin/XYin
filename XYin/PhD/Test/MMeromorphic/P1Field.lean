import XYin.PhD.Test.MMeromorphic.P1Chart
import XYin.PhD.Test.MMeromorphic.GeometricFunctionField

/-!
# The function field of the independent projective j-line model

The scheme is independently `Proj ℂ[X₀,X₁]`. Its actual nonempty affine chart, rather than an
assumed chart, identifies its function field with the field of level-one modular functions.
This is a theorem for the standard projective j-line model. Identification with a compact
analytic orbit quotient or an AINTLIB moduli-space construction is separate from this theorem.
-/

open AlgebraicGeometry
open scoped MatrixGroups

noncomputable section

namespace MMeromorphicTest.P1

instance functionFieldComplexAlgebra : Algebra ℂ scheme.functionField :=
  ((algebraMap Γ(scheme, standardOpen) scheme.functionField).comp
    (algebraMap ℂ Γ(scheme, standardOpen))).toAlgebra

instance functionFieldComplexScalarTower :
    IsScalarTower ℂ Γ(scheme, standardOpen) scheme.functionField :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The actual function field of the projective j-line is the rational function field. -/
def functionFieldRatFuncEquiv : scheme.functionField ≃ₐ[ℂ] RatFunc ℂ :=
  AffineFunctionField.functionFieldAlgEquiv scheme standardOpen
    standardOpen_isAffineOpen standardOpenSectionAlgEquiv

/-- The projective j-line function field is the field of level-one modular functions. -/
def functionFieldModularEquiv : scheme.functionField ≃ₐ[ℂ] ModularFunction 𝒮ℒ :=
  GeometricFunctionField.functionFieldModularEquiv scheme standardOpen
    standardOpen_isAffineOpen standardOpenSectionAlgEquiv

/-- The affine coordinate of the independent geometric model, viewed in its function field. -/
def parameter : scheme.functionField := functionFieldRatFuncEquiv.symm RatFunc.X

/-- The geometric parameter is the germ of the section `X₁ / X₀`. -/
theorem parameter_eq_affineCoordinate :
    parameter = algebraMap Γ(scheme, standardOpen) scheme.functionField
      (standardOpenAwayRingEquiv affineCoordinate) := by
  apply functionFieldRatFuncEquiv.injective
  rw [parameter, functionFieldRatFuncEquiv.apply_symm_apply]
  rw [functionFieldRatFuncEquiv, AffineFunctionField.functionFieldAlgEquiv_algebraMap]
  have he : standardOpenSectionAlgEquiv (standardOpenAwayRingEquiv affineCoordinate) =
      Polynomial.X := by
    change chartRingEquiv
      (standardOpenAwayRingEquiv.symm (standardOpenAwayRingEquiv affineCoordinate)) = _
    rw [standardOpenAwayRingEquiv.symm_apply_apply, chartRingEquiv_affineCoordinate]
  rw [he, RatFunc.algebraMap_X]

/-- The comparison sends the geometric j-coordinate to the actual modular invariant. -/
theorem functionFieldModularEquiv_parameter :
    functionFieldModularEquiv parameter = jModularFunction := by
  change LevelOneField.ratFuncModularEquiv
    (functionFieldRatFuncEquiv (functionFieldRatFuncEquiv.symm RatFunc.X)) = _
  rw [functionFieldRatFuncEquiv.apply_symm_apply]
  exact LevelOneField.ratFuncModularEquiv_X

example (c : ℂ) : functionFieldModularEquiv (algebraMap ℂ scheme.functionField c) =
    algebraMap ℂ (ModularFunction 𝒮ℒ) c := functionFieldModularEquiv.commutes c

example (f : ModularFunction 𝒮ℒ) :
    functionFieldModularEquiv (functionFieldModularEquiv.symm f) = f :=
  functionFieldModularEquiv.apply_symm_apply f

#print axioms functionFieldRatFuncEquiv
#print axioms functionFieldModularEquiv
#print axioms functionFieldModularEquiv_parameter
#print axioms parameter_eq_affineCoordinate

end MMeromorphicTest.P1
