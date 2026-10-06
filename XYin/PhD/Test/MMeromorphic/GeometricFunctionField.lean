import XYin.PhD.Test.MMeromorphic.AffineFunctionField
import XYin.PhD.Test.MMeromorphic.LevelOneField

/-!
# A geometric affine-chart criterion for the level-one function field

For an independently defined integral complex scheme, a nonempty affine polynomial chart
identifies its function field with the actual field of level-one modular functions. Supplying
such a chart for a constructed geometric X(1) remains separate work; no X(1) is defined here.
-/

open AlgebraicGeometry
open scoped MatrixGroups

noncomputable section

namespace MMeromorphicTest.GeometricFunctionField

variable (X : Scheme) [IsIntegral X] (U : X.Opens) [Nonempty U]
  [Algebra ℂ Γ(X, U)] [Algebra ℂ X.functionField]
  [IsScalarTower ℂ Γ(X, U) X.functionField]

/-- The polynomial coordinate of an independent geometric chart is interpreted as j. -/
def functionFieldModularEquiv (hU : IsAffineOpen U)
    (coordinateRingEquiv : Γ(X, U) ≃ₐ[ℂ] Polynomial ℂ) :
    X.functionField ≃ₐ[ℂ] ModularFunction 𝒮ℒ :=
  (AffineFunctionField.functionFieldAlgEquiv X U hU coordinateRingEquiv).trans
    LevelOneField.ratFuncModularEquiv

@[simp]
theorem functionFieldModularEquiv_complex (hU : IsAffineOpen U)
    (coordinateRingEquiv : Γ(X, U) ≃ₐ[ℂ] Polynomial ℂ) (c : ℂ) :
    functionFieldModularEquiv X U hU coordinateRingEquiv
        (algebraMap ℂ X.functionField c) =
      algebraMap ℂ (ModularFunction 𝒮ℒ) c :=
  (functionFieldModularEquiv X U hU coordinateRingEquiv).commutes c

example (hU : IsAffineOpen U) (e : Γ(X, U) ≃ₐ[ℂ] Polynomial ℂ)
    (f : ModularFunction 𝒮ℒ) :
    functionFieldModularEquiv X U hU e
      ((functionFieldModularEquiv X U hU e).symm f) = f :=
  (functionFieldModularEquiv X U hU e).apply_symm_apply f

#print axioms functionFieldModularEquiv

end MMeromorphicTest.GeometricFunctionField
