import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Analysis.Complex.Basic

/-!
# Complex-valued points of the polynomial affine line

The points here are actual algebra homomorphisms, and then actual scheme morphisms over
`Spec ℂ`. They are not defined using a modular-function field. The result is a point-coordinate
bridge only: it neither identifies the prime-spectrum carrier with `ℂ`, nor constructs the
analytic structure or cusp compactification of the modular quotient.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MMeromorphicTest.PolynomialSpectrumPoints

/-- Complex-valued algebra points of the polynomial affine line. -/
abbrev AlgebraPoint := Polynomial ℂ →ₐ[ℂ] ℂ

/-- The coordinate of an algebra point is its value on `X`. -/
def algebraPointEquiv : AlgebraPoint ≃ ℂ := (Polynomial.aevalEquiv ℂ ℂ).symm

@[simp] theorem algebraPointEquiv_apply (p : AlgebraPoint) :
    algebraPointEquiv p = p Polynomial.X := rfl

@[simp] theorem algebraPointEquiv_symm_apply (z : ℂ) :
    algebraPointEquiv.symm z = Polynomial.aeval z := rfl

/-- The base scheme. -/
abbrev complexBase : Scheme := Spec (CommRingCat.of ℂ)

/-- The scheme `Spec ℂ[X]`. -/
abbrev complexAffineLine : Scheme := Spec (CommRingCat.of (Polynomial ℂ))

/-- The structure morphism of `Spec ℂ[X]` over `Spec ℂ`. -/
def structureMap : complexAffineLine ⟶ complexBase :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ))

/-- A complex-valued point as a scheme morphism over `Spec ℂ`.

The condition is the actual commuting triangle for morphisms over the base scheme.
-/
abbrev SchemePoint :=
  {p : complexBase ⟶ complexAffineLine // p ≫ structureMap = 𝟙 complexBase}

/-- The scheme point induced contravariantly by an algebra point. -/
def schemePointOfAlgebra (p : AlgebraPoint) : SchemePoint :=
  ⟨Spec.map (CommRingCat.ofHom p.toRingHom), by
    rw [structureMap, ← Spec.map_comp, Spec.map_eq_id]
    ext z
    exact p.commutes z⟩

/-- The commuting base triangle makes the corresponding ring map `ℂ`-linear. -/
def algebraPointOfScheme (p : SchemePoint) : AlgebraPoint where
  toRingHom := (Spec.preimage p.val).hom
  commutes' z := by
    have h := congrArg Spec.preimage p.property
    simp only [Spec.preimage_comp, structureMap, Spec.preimage_map, Spec.preimage_id] at h
    exact congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ f z) h

/-- Algebra points and scheme points over the base agree. -/
def algebraSchemePointEquiv : AlgebraPoint ≃ SchemePoint where
  toFun := schemePointOfAlgebra
  invFun := algebraPointOfScheme
  left_inv p := by
    apply AlgHom.ext
    intro q
    change (Spec.preimage (Spec.map (CommRingCat.ofHom p.toRingHom))).hom q = p q
    rw [Spec.preimage_map]
    rfl
  right_inv p := by
    apply Subtype.ext
    change Spec.map (Spec.preimage p.val) = p.val
    exact Spec.map_preimage p.val

/-- Actual scheme morphisms over `Spec ℂ` are parametrized by their affine coordinate. -/
def schemePointEquiv : SchemePoint ≃ ℂ :=
  algebraSchemePointEquiv.symm.trans algebraPointEquiv

@[simp] theorem schemePointEquiv_apply (p : SchemePoint) :
    schemePointEquiv p = (Spec.preimage p.val).hom Polynomial.X := rfl

@[simp] theorem schemePointEquiv_symm_apply (z : ℂ) :
    schemePointEquiv.symm z = schemePointOfAlgebra (Polynomial.aeval z) := rfl

example (z : ℂ) : schemePointEquiv (schemePointEquiv.symm z) = z :=
  schemePointEquiv.apply_symm_apply z

example (p : SchemePoint) : schemePointEquiv.symm (schemePointEquiv p) = p :=
  schemePointEquiv.symm_apply_apply p

example (p : SchemePoint) : p.val ≫ structureMap = 𝟙 complexBase := p.property

#print axioms algebraPointEquiv
#print axioms algebraSchemePointEquiv
#print axioms schemePointEquiv

end MMeromorphicTest.PolynomialSpectrumPoints
