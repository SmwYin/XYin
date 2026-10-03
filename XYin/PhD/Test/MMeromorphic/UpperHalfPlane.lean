import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# A minimal upper half-plane predicate

This experimental interface acts on `f : ℍ → ℂ`. Its implementation uses `ofComplex`,
but clients can use the arithmetic and pullback lemmas without mentioning that extension.
The predicate deliberately retains mathlib's freedom at isolated points.
-/

open Filter Set UpperHalfPlane
open scoped Manifold Topology MatrixGroups

namespace MMeromorphicTest.UHP

/-- Meromorphy of a raw upper half-plane function, with arbitrary values at isolated points. -/
def Meromorphic (f : ℍ → ℂ) : Prop :=
  MeromorphicOn (f ∘ ofComplex) {z : ℂ | 0 < z.im}

variable {f g : ℍ → ℂ}

theorem iff_forall : Meromorphic f ↔ ∀ τ : ℍ, MeromorphicAt (f ∘ ofComplex) (τ : ℂ) := by
  constructor
  · exact fun h τ ↦ h τ τ.im_pos
  · exact fun h z hz ↦ h ⟨z, hz⟩

theorem of_mdifferentiable (hf : MDiff f) : Meromorphic f :=
  ((UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd
    isOpen_upperHalfPlaneSet).meromorphicOn

theorem const (c : ℂ) : Meromorphic (fun _ ↦ c) := MeromorphicOn.const c

theorem add (hf : Meromorphic f) (hg : Meromorphic g) : Meromorphic (f + g) :=
  hf.add hg

theorem sub (hf : Meromorphic f) (hg : Meromorphic g) : Meromorphic (f - g) :=
  hf.sub hg

theorem neg (hf : Meromorphic f) : Meromorphic (-f) := hf.neg

theorem mul (hf : Meromorphic f) (hg : Meromorphic g) : Meromorphic (f * g) :=
  hf.mul hg

theorem inv (hf : Meromorphic f) : Meromorphic f⁻¹ := hf.inv

theorem div (hf : Meromorphic f) (hg : Meromorphic g) : Meromorphic (f / g) :=
  hf.div hg

theorem pow (hf : Meromorphic f) (n : ℕ) : Meromorphic (f ^ n) := hf.pow n

/-- Pullback along a holomorphic upper half-plane map. -/
theorem comp (hf : Meromorphic f) {h : ℍ → ℍ} (hh : MDiff h) :
    Meromorphic (f ∘ h) := by
  rw [iff_forall] at hf ⊢
  intro τ
  have ha : AnalyticAt ℂ (fun z ↦ (h (ofComplex z) : ℂ)) (τ : ℂ) :=
    ((UpperHalfPlane.mdifferentiable_iff.mp
      (UpperHalfPlane.mdifferentiable_coe.comp hh)).analyticOnNhd
      isOpen_upperHalfPlaneSet) τ τ.im_pos
  have hm : MeromorphicAt (f ∘ ofComplex) (↑(h (ofComplex τ)) : ℂ) := by
    simpa only [ofComplex_apply] using hf (h τ)
  have hc := hm.comp_analyticAt (x := (τ : ℂ))
    (g := fun z ↦ (h (ofComplex z) : ℂ)) ha
  simpa only [Function.comp_def, ofComplex_apply] using hc

/-- The positive determinant action used in modular invariance preserves the condition. -/
theorem comp_smul (hf : Meromorphic f) {γ : GL (Fin 2) ℝ} (hγ : 0 < γ.det.val) :
    Meromorphic (fun τ ↦ f (γ • τ)) :=
  comp hf (UpperHalfPlane.mdifferentiable_smul hγ)

/-- The direct predicate is a subring condition, before quotienting exceptional values. -/
def subring : Subring (ℍ → ℂ) where
  carrier := {f | Meromorphic f}
  zero_mem' := const 0
  one_mem' := const 1
  add_mem' := add
  mul_mem' := mul
  neg_mem' := neg

end MMeromorphicTest.UHP
