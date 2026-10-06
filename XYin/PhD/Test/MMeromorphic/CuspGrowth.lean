import XYin.PhD.ModularFunctions.GrowthAtCusp

/-!
# Checks for the production exponential cusp predicate

The positive-exponent big-O formulation and the production weighted-boundedness formulation
are equivalent. The requested cusp condition uses the actual projective-line cusp and slash
action. No duplicate growth or cusp definitions are introduced here.
-/

open Asymptotics UpperHalfPlane
open scoped Topology MatrixGroups ModularForm

namespace MMeromorphicTest.Exponential

/-- Requiring a positive rather than nonnegative exponential rate does not change the predicate. -/
theorem isOfExponentialGrowth_iff_positive_rate {f : ℍ → ℂ} :
    IsOfExponentialGrowth f ↔
      ∃ a : ℝ, 0 < a ∧ f =O[atImInfty] (fun τ ↦ Real.exp (a * τ.im)) := by
  constructor
  · intro hf
    obtain ⟨a, ha, hbound⟩ := isOfExponentialGrowth_iff_isBigO.1 hf
    exact ⟨a + 1, by linarith,
      hbound.trans (exp_mul_im_isBigO_exp_mul_im (by linarith))⟩
  · rintro ⟨a, _, hbound⟩
    exact IsOfExponentialGrowth.of_isBigO_exp hbound

example (c : OnePoint ℝ) (f : ℍ → ℂ) (k : ℤ) :
    c.IsExpBoundedAt f k ↔
      ∀ g : GL (Fin 2) ℝ, g • OnePoint.infty = c →
        IsOfExponentialGrowth (f ∣[k] g) := Iff.rfl

example (c : OnePoint ℝ) (f : ℍ → ℂ) :
    c.IsExpBoundedAt f 0 ↔ c.IsOfExponentialGrowthAt f :=
  OnePoint.IsExpBoundedAt.iff_at_zero

#print axioms isOfExponentialGrowth_iff_positive_rate

end MMeromorphicTest.Exponential
