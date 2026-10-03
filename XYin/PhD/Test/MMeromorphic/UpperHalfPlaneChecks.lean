import XYin.PhD.Test.MMeromorphic.UpperHalfPlane
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! Sanity checks comparing a direct upper half-plane interface with the coordinate interface. -/

open UpperHalfPlane
open scoped Manifold Topology

namespace MMeromorphicTest.UHP

-- The coordinate condition already has addition and multiplication theorems.
example {f g : ℍ → ℂ}
    (hf : DifferentiableOn ℂ (f ∘ ofComplex) {z : ℂ | 0 < z.im})
    (hg : DifferentiableOn ℂ (g ∘ ofComplex) {z : ℂ | 0 < z.im}) :
    DifferentiableOn ℂ ((f + g * f) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
  hf.add (hg.mul hf)

-- The direct predicate hides the coordinate conversion from arithmetic clients.
example {f g : ℍ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic ((f + g * f) / g) := div (add hf (mul hg hf)) hg

-- The direct interface also hides the extra coercion/extension used by composition.
example {f : ℍ → ℂ} {h : ℍ → ℍ} (hf : Meromorphic f) (hh : MDiff h) :
    Meromorphic (f ∘ h) := comp hf hh

/-- A holomorphic function with an interior zero. -/
def shiftedCoordinate (τ : ℍ) : ℂ := (τ : ℂ) - Complex.I

theorem shiftedCoordinate_meromorphic : Meromorphic shiftedCoordinate :=
  of_mdifferentiable (mdifferentiable_coe.sub mdifferentiable_const)

theorem shiftedCoordinate_ne_zero : shiftedCoordinate ≠ 0 := by
  intro h
  have he := congrFun h (⟨⟨0, 2⟩, by norm_num⟩ : ℍ)
  have hi := congrArg Complex.im he
  norm_num [shiftedCoordinate] at hi

/-- Even a holomorphic nonzero function fails the field inverse law pointwise at its zeros. -/
theorem pointwise_mul_inv_fails : shiftedCoordinate * shiftedCoordinate⁻¹ ≠ 1 := by
  intro h
  have he := congrFun h UpperHalfPlane.I
  simp [shiftedCoordinate, UpperHalfPlane.coe_I] at he

-- Closure under inverse therefore must not be confused with having a field instance.
example : Meromorphic shiftedCoordinate⁻¹ := inv shiftedCoordinate_meromorphic

#print axioms pointwise_mul_inv_fails
#print axioms comp

end MMeromorphicTest.UHP
