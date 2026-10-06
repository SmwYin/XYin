import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Function fields from an affine polynomial chart

A nonempty affine open of an integral scheme determines its function field. If its section
ring is explicitly identified with `ℂ[X]`, fraction-ring uniqueness identifies the scheme's
function field with `RatFunc ℂ`. The coordinate-ring equivalence is a hypothesis; this file
does not construct a projective line or a compactified modular curve.

The algebra-equivalence version additionally records compatible complex-algebra structures
on the chart sections and the function field. A bare ring equivalence need not preserve the
chosen embedding of the constants.
-/

open AlgebraicGeometry

namespace MMeromorphicTest.AffineFunctionField

noncomputable section

variable (X : Scheme) [IsIntegral X] (U : X.Opens) [Nonempty U]

/-- An explicit affine polynomial chart identifies an integral scheme's function field. -/
def functionFieldRingEquiv (hU : IsAffineOpen U)
    (coordinateRingEquiv : Γ(X, U) ≃+* Polynomial ℂ) : X.functionField ≃+* RatFunc ℂ := by
  letI := functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsFractionRing.ringEquivOfRingEquiv coordinateRingEquiv

/-- The induced equivalence extends the supplied coordinate-ring equivalence. -/
@[simp]
theorem functionFieldRingEquiv_algebraMap (hU : IsAffineOpen U)
    (coordinateRingEquiv : Γ(X, U) ≃+* Polynomial ℂ) (p : Γ(X, U)) :
    functionFieldRingEquiv X U hU coordinateRingEquiv (algebraMap Γ(X, U) X.functionField p) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (coordinateRingEquiv p) := by
  letI := functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap coordinateRingEquiv p

variable [Algebra ℂ Γ(X, U)] [Algebra ℂ X.functionField]
    [IsScalarTower ℂ Γ(X, U) X.functionField]

/-- A complex-algebra chart yields a complex-algebra equivalence of function fields. -/
def functionFieldAlgEquiv (hU : IsAffineOpen U)
    (coordinateRingEquiv : Γ(X, U) ≃ₐ[ℂ] Polynomial ℂ) : X.functionField ≃ₐ[ℂ] RatFunc ℂ := by
  letI := functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsFractionRing.algEquivOfAlgEquiv coordinateRingEquiv

/-- The field comparison extends the geometric affine coordinate map. -/
@[simp]
theorem functionFieldAlgEquiv_algebraMap (hU : IsAffineOpen U)
    (coordinateRingEquiv : Γ(X, U) ≃ₐ[ℂ] Polynomial ℂ) (p : Γ(X, U)) :
    functionFieldAlgEquiv X U hU coordinateRingEquiv (algebraMap Γ(X, U) X.functionField p) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (coordinateRingEquiv p) := by
  letI := functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap coordinateRingEquiv p

/-- The algebra equivalence preserves the chosen complex constants. -/
@[simp]
theorem functionFieldAlgEquiv_complex (hU : IsAffineOpen U)
    (coordinateRingEquiv : Γ(X, U) ≃ₐ[ℂ] Polynomial ℂ) (c : ℂ) :
    functionFieldAlgEquiv X U hU coordinateRingEquiv (algebraMap ℂ X.functionField c) =
      algebraMap ℂ (RatFunc ℂ) c :=
  (functionFieldAlgEquiv X U hU coordinateRingEquiv).commutes c

section PolynomialSpec

local instance polynomialSpecFunctionFieldAlgebra :
    Algebra (Polynomial ℂ) (Spec (.of (Polynomial ℂ))).functionField :=
  instAlgebraCarrierFunctionFieldSpec (.of (Polynomial ℂ))

local instance polynomialSpecFunctionFieldIsFractionRing :
    IsFractionRing (Polynomial ℂ) (Spec (.of (Polynomial ℂ))).functionField :=
  functionField_isFractionRing_of_affine (.of (Polynomial ℂ))

/-- Sanity check: the function field of the polynomial affine line is `RatFunc ℂ`. -/
def polynomialSpecFunctionFieldRingEquiv :
    (Spec (.of (Polynomial ℂ))).functionField ≃+* RatFunc ℂ :=
  IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl (Polynomial ℂ))

example (p : Polynomial ℂ) :
    polynomialSpecFunctionFieldRingEquiv
        (algebraMap (Polynomial ℂ) (Spec (.of (Polynomial ℂ))).functionField p) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) p :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (RingEquiv.refl (Polynomial ℂ)) p

end PolynomialSpec

#print axioms functionFieldRingEquiv
#print axioms functionFieldRingEquiv_algebraMap
#print axioms functionFieldAlgEquiv
#print axioms functionFieldAlgEquiv_complex
#print axioms polynomialSpecFunctionFieldRingEquiv

end

end MMeromorphicTest.AffineFunctionField
