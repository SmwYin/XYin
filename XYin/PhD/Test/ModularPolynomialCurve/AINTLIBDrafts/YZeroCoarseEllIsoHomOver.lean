/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseHomOverClassifiers

/-!
# Native complex elliptic-object isomorphisms give fixed-base pointed morphisms

A native isomorphism between the literal `complexEllObj` objects has the identity
base map, as forced by `base_w`. Its actual top map, square, and zero compatibility
define a pointed `HomOver` over `Spec ℂ`. Projecting both native inverse laws gives
a literal total-space scheme isomorphism and hence an `IsIso` instance for that map.

The fixed-base `HomOver` adapter recovers the original native isomorphism hom.
The construction preserves its direction and top morphism; no level assumption is
needed. Explicitly typed scheme-morphism aliases in the square and zero proofs keep
identity cancellation on the canonical source and target schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ModularCurves

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable (E E' : ModularCurves.EllipticCurve (Spec (.of ℂ)))

/-- Native morphisms between the literal complex objects have the identity base map. -/
theorem complexEllHom_baseHom_eq_id (u : complexEllObj E ⟶ complexEllObj E') :
    u.baseHom = 𝟙 (Spec (.of ℂ)) := by
  have h := u.base_w
  change u.baseHom ≫ 𝟙 (Spec (.of ℂ)) = 𝟙 (Spec (.of ℂ)) at h
  exact (Category.comp_id u.baseHom).symm.trans h

/-- The actual top maps and native inverse laws give a literal total-space isomorphism. -/
def complexTotalIsoOfEllIso (e : complexEllObj E ≅ complexEllObj E') : E.E ≅ E'.E where
  hom := e.hom.top
  inv := e.inv.top
  hom_inv_id := congrArg EllHom.top e.hom_inv_id
  inv_hom_id := congrArg EllHom.top e.inv_hom_id

/-- A native pointed complex-object isomorphism yields a pointed map over `Spec ℂ`. -/
def complexHomOverOfEllIso (e : complexEllObj E ≅ complexEllObj E') : E.HomOver E' where
  hom := e.hom.top
  over_w := by
    let t : E.E ⟶ E'.E := e.hom.top
    let b : Spec (.of ℂ) ⟶ Spec (.of ℂ) := e.hom.baseHom
    have h : t ≫ E'.π = E.π ≫ b := e.hom.isPullback.w
    have hb : b = 𝟙 (Spec (.of ℂ)) := complexEllHom_baseHom_eq_id E E' e.hom
    rw [hb, Category.comp_id] at h
    exact h
  zero_w := by
    let t : E.E ⟶ E'.E := e.hom.top
    let b : Spec (.of ℂ) ⟶ Spec (.of ℂ) := e.hom.baseHom
    have h : E.zero ≫ t = b ≫ E'.zero := e.hom.zero_w
    have hb : b = 𝟙 (Spec (.of ℂ)) := complexEllHom_baseHom_eq_id E E' e.hom
    rw [hb, Category.id_comp] at h
    exact h

/-- The recovered pointed morphism has the original native top map. -/
@[simp]
theorem complexHomOverOfEllIso_hom (e : complexEllObj E ≅ complexEllObj E') :
    (complexHomOverOfEllIso E E' e).hom = e.hom.top := rfl

/-- Its underlying scheme morphism is the hom of the literal total-space isomorphism. -/
instance complexHomOverOfEllIso_isIso (e : complexEllObj E ≅ complexEllObj E') :
    IsIso (complexHomOverOfEllIso E E' e).hom := by
  change IsIso e.hom.top
  exact (complexTotalIsoOfEllIso E E' e).isIso_hom

/-- Reconstructing the native morphism recovers the actual original isomorphism hom. -/
theorem complexEllHomOfHomOver_complexHomOverOfEllIso
    (e : complexEllObj E ≅ complexEllObj E') :
    complexEllHomOfHomOver E E' (complexHomOverOfEllIso E E' e) = e.hom := by
  apply EllHom.ext
  · exact (complexEllHom_baseHom_eq_id E E' e.hom).symm
  · rfl

example : complexHomOverOfEllIso E E (Iso.refl (complexEllObj E)) =
    (𝟙 E : E ⟶ E) := by
  apply ModularCurves.EllipticCurve.HomOver.ext
  rfl

-- General native isomorphisms also reconstruct correctly inside the actual level functor.
example (N : ℕ) [NeZero N] (e : complexEllObj E ≅ complexEllObj E')
    (β : complexFullMarking N E') :
    (gammaFullNaiveProblem (.of ℂ) N).map
      (complexEllHomOfHomOver E E' (complexHomOverOfEllIso E E' e)).op β =
    (gammaFullNaiveProblem (.of ℂ) N).map e.hom.op β := by
  rw [complexEllHomOfHomOver_complexHomOverOfEllIso]

#print axioms complexEllHom_baseHom_eq_id
#print axioms complexTotalIsoOfEllIso
#print axioms complexHomOverOfEllIso
#print axioms complexHomOverOfEllIso_hom
#print axioms complexHomOverOfEllIso_isIso
#print axioms complexEllHomOfHomOver_complexHomOverOfEllIso
#print axioms CategoryTheory.Iso.hom_inv_id
#print axioms CategoryTheory.Iso.inv_hom_id
#print axioms CategoryTheory.CommSq.w
#print axioms ModularCurves.EllHom.zero_w
#print axioms complexEllHomOfHomOver

end ModularPolynomialCurveTest.AINTLIB
