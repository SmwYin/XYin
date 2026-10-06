/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseFineComplexPoints
public import AINTLIBDrafts.YZeroCoarsePointOrbits

/-!
# Borel orbits of actual full-level complex scheme points

The transform is postcomposition with the literal Borel-action morphism. Since
`SchemeAction.hom_mul` composes in the same order as multiplication, this is a right
action on points. Equality of the actual coarse images is precisely this orbit relation.
The explicit orbit quotient is therefore equivalent to the actual coarse complex points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

local instance complexPointOrbitsFullAlgebra : Algebra ℂ
    Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) :=
  (fullCoefficientHom (R := .of ℂ) N hN (complexLevelIsUnit N)).toAlgebra

local instance complexPointOrbitsInvariantAlgebra : Algebra ℂ
    (yZeroInvariantRing (R := .of ℂ) N hN (complexLevelIsUnit N)) :=
  yZeroInvariantAlgebra (R := .of ℂ) N hN (complexLevelIsUnit N)

/-- Postcomposition of a full-level point with the actual Borel-action morphism. -/
def fullComplexBorelTransform (g : ModularCurves.borel N) (p : fullComplexSchemePoint N hN) :
    fullComplexSchemePoint N hN :=
  ⟨p.val ≫ (borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).hom g, by
    rw [Category.assoc, borelAction_over]
    exact p.property⟩

/-- Postcomposition of scheme points corresponds to pullback of their section-ring points. -/
theorem fullComplexAlgebraPointOfScheme_borelTransform (g : ModularCurves.borel N)
    (p : fullComplexSchemePoint N hN)
    (x : Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤)) :
    fullComplexAlgebraPointOfScheme N hN (fullComplexBorelTransform N hN g p) x =
      fullComplexAlgebraPointOfScheme N hN p
        (((borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).hom g).appTop.hom x) := by
  change (Spec.preimage ((p.val ≫
    (borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).hom g) ≫
    (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.toSpecΓ)).hom x = _
  rw [Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc,
    Spec.preimage_comp, Spec.preimage_map]
  rfl

/-- The actual coarse image of a scheme point corresponds to restriction to invariants. -/
theorem yZeroComplexSchemePointOfFull_eq_ofAlgebra (p : fullComplexSchemePoint N hN) :
    yZeroComplexSchemePointOfFull N hN p =
      yZeroComplexSchemePointOfAlgebra N hN
        ((fullComplexAlgebraPointOfScheme N hN p).comp
          (yZeroComplexInvariantInclusion N hN)) := by
  have hp : fullComplexSchemePointOfAlgebra N hN
      (fullComplexAlgebraPointOfScheme N hN p) = p :=
    (fullComplexAlgebraSchemePointEquiv N hN).right_inv p
  simpa only [hp] using fullComplexSchemePointOfAlgebra_comp_yZeroPr N hN
    (fullComplexAlgebraPointOfScheme N hN p)

/-- Two actual full-level complex scheme points have the same coarse image exactly when
one is obtained from the other by the direct Borel transform. -/
theorem yZeroComplexSchemePointOfFull_eq_iff_borel
    (p q : fullComplexSchemePoint N hN) :
    yZeroComplexSchemePointOfFull N hN p = yZeroComplexSchemePointOfFull N hN q ↔
      ∃ g : ModularCurves.borel N,
        q.val = p.val ≫ (borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).hom g := by
  have hcoarse :
      yZeroComplexSchemePointOfFull N hN p = yZeroComplexSchemePointOfFull N hN q ↔
        (fullComplexAlgebraPointOfScheme N hN p).comp
            (yZeroComplexInvariantInclusion N hN) =
          (fullComplexAlgebraPointOfScheme N hN q).comp
            (yZeroComplexInvariantInclusion N hN) := by
    rw [yZeroComplexSchemePointOfFull_eq_ofAlgebra, yZeroComplexSchemePointOfFull_eq_ofAlgebra]
    exact (yZeroComplexAlgebraSchemePointEquiv N hN).injective.eq_iff
  rw [hcoarse, yZeroComplexInvariantRestriction_eq_iff_borel]
  constructor
  · rintro ⟨g, hg⟩
    have hAlg : fullComplexAlgebraPointOfScheme N hN q =
        fullComplexAlgebraPointOfScheme N hN (fullComplexBorelTransform N hN g p) := by
      ext x
      rw [fullComplexAlgebraPointOfScheme_borelTransform]
      exact hg x
    have hPoints : q = fullComplexBorelTransform N hN g p :=
      (fullComplexAlgebraSchemePointEquiv N hN).symm.injective hAlg
    exact ⟨g, congrArg Subtype.val hPoints⟩
  · rintro ⟨g, hg⟩
    have hPoints : q = fullComplexBorelTransform N hN g p := Subtype.ext hg
    refine ⟨g, ?_⟩
    intro x
    rw [hPoints, fullComplexAlgebraPointOfScheme_borelTransform]

/-- The literal Borel orbit relation on actual full-level complex scheme points. -/
def fullComplexBorelOrbitSetoid : Setoid (fullComplexSchemePoint N hN) where
  r p q := ∃ g : ModularCurves.borel N,
    q.val = p.val ≫ (borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).hom g
  iseqv := ⟨fun p ↦ (yZeroComplexSchemePointOfFull_eq_iff_borel N hN p p).mp rfl,
    fun {p q} hpq ↦ (yZeroComplexSchemePointOfFull_eq_iff_borel N hN q p).mp
      ((yZeroComplexSchemePointOfFull_eq_iff_borel N hN p q).mpr hpq).symm,
    fun {p q r} hpq hqr ↦ (yZeroComplexSchemePointOfFull_eq_iff_borel N hN p r).mp
      (((yZeroComplexSchemePointOfFull_eq_iff_borel N hN p q).mpr hpq).trans
        ((yZeroComplexSchemePointOfFull_eq_iff_borel N hN q r).mpr hqr))⟩

/-- Actual full-level complex points modulo the literal Borel orbit relation. -/
abbrev fullComplexBorelOrbitQuotient := Quotient (fullComplexBorelOrbitSetoid N hN)

/-- The actual full-to-coarse map descends to the explicit Borel orbit quotient. -/
def yZeroComplexSchemePointOfBorelOrbit :
    fullComplexBorelOrbitQuotient N hN → yZeroComplexSchemePoint N hN :=
  Quotient.lift (yZeroComplexSchemePointOfFull N hN) fun p q hpq ↦
    (yZeroComplexSchemePointOfFull_eq_iff_borel N hN p q).mpr hpq

@[simp]
theorem yZeroComplexSchemePointOfBorelOrbit_mk (p : fullComplexSchemePoint N hN) :
    yZeroComplexSchemePointOfBorelOrbit N hN
        (Quotient.mk (fullComplexBorelOrbitSetoid N hN) p) =
      yZeroComplexSchemePointOfFull N hN p := rfl

/-- The actual coarse fibers give injectivity, and actual complex-point lifting gives
surjectivity. No freeness assumption on the Borel action is required. -/
theorem yZeroComplexSchemePointOfBorelOrbit_bijective :
    Function.Bijective (yZeroComplexSchemePointOfBorelOrbit N hN) := by
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro p q hpq
    exact Quotient.sound ((yZeroComplexSchemePointOfFull_eq_iff_borel N hN p q).mp hpq)
  · intro p
    obtain ⟨q, hq⟩ := yZeroComplexSchemePoint_lifts N hN p
    exact ⟨Quotient.mk (fullComplexBorelOrbitSetoid N hN) q, hq⟩

/-- The explicit Borel orbit quotient is equivalent to the actual coarse complex points. -/
def fullComplexBorelOrbitEquivYZero :
    fullComplexBorelOrbitQuotient N hN ≃ yZeroComplexSchemePoint N hN :=
  Equiv.ofBijective (yZeroComplexSchemePointOfBorelOrbit N hN)
    (yZeroComplexSchemePointOfBorelOrbit_bijective N hN)

@[simp]
theorem fullComplexBorelOrbitEquivYZero_mk (p : fullComplexSchemePoint N hN) :
    fullComplexBorelOrbitEquivYZero N hN
        (Quotient.mk (fullComplexBorelOrbitSetoid N hN) p) =
      yZeroComplexSchemePointOfFull N hN p := rfl

-- Concrete level-3 checks exercise the actual orbit quotient and both inverse laws.
example (p : yZeroComplexSchemePoint 3 (by decide)) :
    fullComplexBorelOrbitEquivYZero 3 (by decide)
        ((fullComplexBorelOrbitEquivYZero 3 (by decide)).symm p) = p :=
  (fullComplexBorelOrbitEquivYZero 3 (by decide)).right_inv p

example (q : fullComplexBorelOrbitQuotient 3 (by decide)) :
    (fullComplexBorelOrbitEquivYZero 3 (by decide)).symm
        (fullComplexBorelOrbitEquivYZero 3 (by decide) q) = q :=
  (fullComplexBorelOrbitEquivYZero 3 (by decide)).left_inv q

#print axioms fullComplexBorelTransform
#print axioms fullComplexAlgebraPointOfScheme_borelTransform
#print axioms yZeroComplexSchemePointOfFull_eq_ofAlgebra
#print axioms yZeroComplexSchemePointOfFull_eq_iff_borel
#print axioms fullComplexBorelOrbitSetoid
#print axioms yZeroComplexSchemePointOfBorelOrbit
#print axioms yZeroComplexSchemePointOfBorelOrbit_mk
#print axioms yZeroComplexSchemePointOfBorelOrbit_bijective
#print axioms fullComplexBorelOrbitEquivYZero
#print axioms fullComplexBorelOrbitEquivYZero_mk

end ModularPolynomialCurveTest.AINTLIB
