import XYin.PhD.ModularFunctions.GrowthAtCusp

/-!
# Checks for the weighted exponential cusp condition
-/

open UpperHalfPlane OnePoint
open scoped MatrixGroups ModularForm

namespace MMeromorphicTest.CuspGrowthCoordinates

variable {c : OnePoint ℝ} {f f' : ℍ → ℂ} {k k' : ℤ} {g : GL (Fin 2) ℝ}

example (hf : IsExpBoundedAt c f 0) : IsOfExponentialGrowthAt c f :=
  IsExpBoundedAt.iff_at_zero.mp hf

example (hf : IsOfExponentialGrowthAt c f) : IsExpBoundedAt c f 0 :=
  IsExpBoundedAt.iff_at_zero.mpr hf

-- A single scaling matrix suffices in both directions, for an arbitrary weight.
example (hg : g • ∞ = c) (hf : IsExpBoundedAt c f k) :
    IsOfExponentialGrowth (f ∣[k] g) := (isExpBoundedAt_iff hg).mp hf

example (hg : g • ∞ = c) (hf : IsOfExponentialGrowth (f ∣[k] g)) :
    IsExpBoundedAt c f k := (isExpBoundedAt_iff hg).mpr hf

example : IsExpBoundedAt ∞ f k ↔ IsOfExponentialGrowth f := isExpBoundedAt_infty_iff

-- Multiplication is valid in different weights, despite the determinant factor in slash.
example (hf : IsExpBoundedAt c f k) (hf' : IsExpBoundedAt c f' k') :
    IsExpBoundedAt c (f * f') (k + k') := hf.mul hf'

example (hf : IsBoundedAt c f k) : IsExpBoundedAt c f k := hf.isExpBoundedAt

example (a : ℂ) : IsExpBoundedAt c (fun _ ↦ a) 0 := isExpBoundedAt_const a

#print axioms OnePoint.IsExpBoundedAt.iff_at_zero
#print axioms OnePoint.isExpBoundedAt_iff
#print axioms OnePoint.IsExpBoundedAt.mul

end MMeromorphicTest.CuspGrowthCoordinates
