/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseMarkedComplexCurves
public import ModularCurves.Moduli.Groupoid

/-!
# Pointed complex curve isomorphisms as native elliptic-object morphisms

A `HomOver` with an isomorphism on total spaces gives a cartesian `EllHom` between
the literal complex elliptic objects. Its base map is the identity and its top map
is the original `HomOver.hom`. Pullback-section equality is equivalent to the forward
equation for that original map, so the two directions of transport can be compared
without introducing a second curve isomorphism.

The construction uses the pinned `Moduli.Groupoid` definition of `HomOver` and
`IsPullback.of_horiz_isIso`. The section equations use only the native `pullSection`
definition and cancellation by the given isomorphism. No level condition is required.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ModularCurves

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable (E E' : ModularCurves.EllipticCurve (Spec (.of ℂ)))
variable (f : E.HomOver E')

/-- A pointed complex curve isomorphism gives the native cartesian elliptic-object map. -/
def complexEllHomOfHomOver [hf : IsIso f.hom] : complexEllObj E ⟶ complexEllObj E' where
  baseHom := 𝟙 _
  base_w := Category.id_comp _
  top := f.hom
  isPullback := by
    change IsPullback f.hom E.π E'.π (𝟙 (Spec (.of ℂ)))
    exact IsPullback.of_horiz_isIso ⟨by rw [f.over_w, Category.comp_id]⟩
  zero_w := by
    change E.zero ≫ f.hom = 𝟙 _ ≫ E'.zero
    rw [f.zero_w, Category.id_comp]

variable [IsIso f.hom]

/-- The native object morphism lies over the literal identity of the complex base. -/
theorem complexEllHomOfHomOver_baseHom :
    (complexEllHomOfHomOver E E' f).baseHom = 𝟙 (Spec (.of ℂ)) := rfl

/-- The top morphism is the original pointed curve morphism. -/
theorem complexEllHomOfHomOver_top :
    (complexEllHomOfHomOver E E' f).top = f.hom := rfl

/-- Pullback along the object map is inverse to the given pointed curve isomorphism. -/
theorem complexEllHomOfHomOver_pullSection_comp (Q : E'.Section) :
    (EllHom.pullSection (.of ℂ) (complexEllHomOfHomOver E E' f) Q).val ≫ f.hom =
      Q.val := by
  have h :
      (EllHom.pullSection (.of ℂ) (complexEllHomOfHomOver E E' f) Q).val ≫
        (complexEllHomOfHomOver E E' f).top =
          (complexEllHomOfHomOver E E' f).baseHom ≫ Q.val :=
    (complexEllHomOfHomOver E E' f).isPullback.lift_fst _ _ _
  exact h.trans (Category.id_comp Q.val)

/-- A pullback-section equality is exactly the forward equation for the original map. -/
theorem complexEllHomOfHomOver_pullSection_eq_iff (P : E.Section) (Q : E'.Section) :
    EllHom.pullSection (.of ℂ) (complexEllHomOfHomOver E E' f) Q = P ↔
      P.val ≫ f.hom = Q.val := by
  constructor
  · intro h
    rw [← h]
    exact complexEllHomOfHomOver_pullSection_comp E E' f Q
  · intro h
    apply Subtype.ext
    apply (cancel_mono f.hom).mp
    exact (complexEllHomOfHomOver_pullSection_comp E E' f Q).trans h.symm

-- The bridge is independent of the level N; identity transport is the relevant sanity check.
example (P : E.Section) :
    EllHom.pullSection (.of ℂ)
      (complexEllHomOfHomOver E E ⟨𝟙 _, by simp, by simp⟩) P = P := by
  apply (complexEllHomOfHomOver_pullSection_eq_iff _ _ _ _ _).mpr
  exact Category.comp_id _

#print axioms complexEllHomOfHomOver
#print axioms complexEllHomOfHomOver_baseHom
#print axioms complexEllHomOfHomOver_top
#print axioms complexEllHomOfHomOver_pullSection_comp
#print axioms complexEllHomOfHomOver_pullSection_eq_iff
#print axioms EllHom.pullSection
#print axioms IsPullback.of_horiz_isIso

end ModularPolynomialCurveTest.AINTLIB
