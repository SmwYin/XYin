import XYin.PhD.Test.ModularPolynomialCurve.OrbitMap
import XYin.PhD.Test.ModularPolynomialCurve.SchemeField
import XYin.PhD.Test.ModularPolynomialCurve.ComplexPoints

/-!
# Modular-polynomial models and Gamma-zero modular functions

Independent plane coordinates, complex points, the actual orbit quotient, polynomial
field presentations, and the plane scheme's generic-point function field are compared
here. See `ModularPolynomialCurve/README.md` for the normalization distinction and the
additional work required to identify AINTLIB's coarse moduli scheme.
-/

noncomputable section

namespace ModularPolynomialCurveTest

/-- The orbit quotient maps to actual complex-valued points of the independent plane scheme. -/
def orbitSchemePointMap (N : ℕ+) : gamma0Orbits N → ComplexPoints.SchemePoint N :=
  (ComplexPoints.schemePointEquiv N).symm ∘ orbitMap N

theorem orbitSchemePointMap_surjective (N : ℕ+) :
    Function.Surjective (orbitSchemePointMap N) :=
  (ComplexPoints.schemePointEquiv N).symm.surjective.comp (orbitMap_surjective N)

example (N : ℕ+) (τ : UpperHalfPlane) :
    ComplexPoints.schemePointEquiv N (orbitSchemePointMap N (Quotient.mk _ τ)) =
      jPair N τ :=
  (ComplexPoints.schemePointEquiv N).apply_symm_apply _

#print axioms orbitSchemePointMap_surjective

end ModularPolynomialCurveTest
