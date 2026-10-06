/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseMarkingClassifiers
public import AINTLIBDrafts.YZeroCoarseComplexPointOrbits
public import ModularCurves.Moduli.Coarse
public import AINTLIBDrafts.YZeroCoarseHomOverClassifiers
public import AINTLIBDrafts.YZeroCoarseNativeRoundtrip
public import AINTLIBDrafts.YZeroCoarseClassifierPointIso
public import AINTLIBDrafts.YZeroCoarseEllIsoHomOver

/-!
# Native full-level classes and actual coarse complex points

The map from a native marked elliptic curve over `Spec ℂ` to its represented
fine point descends to AINTLIB's actual `GammaHClasses` for the Borel subgroup.
The raw relation in `ModularCurves.Moduli.Coarse` uses a pointed same-base
isomorphism and positive `glSmul g`, with both marked sections transported by
`HomOver.mapPoint`.

The proof turns the forward section equations into functorial pullback equations
using `complexEllHomOfHomOver_pullSection_eq_iff`, then applies classifier
naturality and the checked positive Borel action formula. The actual coarse
fiber criterion identifies the resulting fine points. Computing on a native
representative is definitional, and the source-j value is the given curve's j.

Conversely, the actual coarse fiber criterion and positive Borel action formula
identify the appropriate fine classifiers. Their pointed curve isomorphism gives
exactly a witness of the original native quotient relation. Actual full-point
lifting and native classifier roundtrip supply surjectivity, hence an equivalence
with the actual coarse complex points and concrete inverse formulas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ModularCurves ModularCurves.YZeroCoarseJ

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

/-- The actual native marking classifier descends through the actual pointed/Borel relation. -/
def gammaHClassesComplexPoint :
    GammaHClasses (Spec (.of ℂ)) N (borel N) → yZeroComplexSchemePoint N hN := by
  refine Quot.lift
    (fun a : Σ E : ModularCurves.EllipticCurve (Spec (.of ℂ)), E.FullLevelPt N =>
      yZeroComplexSchemePointOfMarking N hN a.1 a.2) ?_
  rintro a b ⟨f, g, hIso, hg, hP, hQ⟩
  let : IsIso f.hom := hIso
  let u := complexEllHomOfHomOver a.1 b.1 f
  let γ : borel N := ⟨g, hg⟩
  have hPull : (gammaFullNaiveProblem (.of ℂ) N).map u.op b.2 =
      a.1.glSmul g a.2 := by
    apply Subtype.ext
    apply Prod.ext
    · exact (complexEllHomOfHomOver_pullSection_eq_iff a.1 b.1 f
        (a.1.glSmul g a.2).1.1 b.2.1.1).mpr (congrArg Subtype.val hP)
    · exact (complexEllHomOfHomOver_pullSection_eq_iff a.1 b.1 f
        (a.1.glSmul g a.2).1.2 b.2.1.2).mpr (congrArg Subtype.val hQ)
  have hNat := fullComplexSchemePointOfMarking_map N hN a.1 b.1 u b.2
  rw [hPull] at hNat
  have hPoint : (fullComplexSchemePointOfMarking N hN b.1 b.2).val =
      (fullComplexSchemePointOfMarking N hN a.1 a.2).val ≫
        (borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).hom γ :=
    (congrArg Subtype.val hNat).symm.trans
      (fullComplexSchemePointOfMarking_glSmul N hN a.1 γ a.2)
  change yZeroComplexSchemePointOfFull N hN
      (fullComplexSchemePointOfMarking N hN a.1 a.2) =
    yZeroComplexSchemePointOfFull N hN (fullComplexSchemePointOfMarking N hN b.1 b.2)
  exact (yZeroComplexSchemePointOfFull_eq_iff_borel N hN
    (fullComplexSchemePointOfMarking N hN a.1 a.2)
    (fullComplexSchemePointOfMarking N hN b.1 b.2)).mpr ⟨γ, hPoint⟩

@[simp]
theorem gammaHClassesComplexPoint_mk
    (E : ModularCurves.EllipticCurve (Spec (.of ℂ))) (L : E.FullLevelPt N) :
    gammaHClassesComplexPoint N hN (GammaHClasses.mk (borel N) E L) =
      yZeroComplexSchemePointOfMarking N hN E L := rfl

/-- The class map preserves the source-j value of the given native curve. -/
theorem gammaHClassesComplexPoint_sourceJ_mk
    (E : ModularCurves.EllipticCurve (Spec (.of ℂ))) (L : E.FullLevelPt N) :
    yZeroComplexSourceJValue N hN
        (gammaHClassesComplexPoint N hN (GammaHClasses.mk (borel N) E L)) =
      (fieldWeierstrassModel E.toEllipticCurveGeom).j := by
  rw [gammaHClassesComplexPoint_mk]
  exact yZeroComplexSourceJValue_of_marking N hN E L

/-- Every actual coarse complex point is represented by a native marked curve. -/
theorem gammaHClassesComplexPoint_surjective :
    Function.Surjective (gammaHClassesComplexPoint N hN) := by
  intro p
  obtain ⟨q, hq⟩ := yZeroComplexSchemePoint_lifts N hN p
  let E : ModularCurves.EllipticCurve (Spec (.of ℂ)) :=
    (fullComplexPointEllObj N hN q).curve
  let L : E.FullLevelPt N := fullComplexPointLevel N hN q
  refine ⟨GammaHClasses.mk (borel N) E L, ?_⟩
  rw [gammaHClassesComplexPoint_mk]
  change yZeroComplexSchemePointOfFull N hN
    (fullComplexSchemePointOfMarking N hN (fullComplexPointEllObj N hN q).curve
      (fullComplexPointLevel N hN q)) = p
  rw [fullComplexSchemePointOfMarking_native]
  exact hq

/-- Equal actual coarse points determine the same original native Borel class. -/
theorem gammaHClassesComplexPoint_injective :
    Function.Injective (gammaHClassesComplexPoint N hN) := by
  intro a b
  refine Quot.induction_on₂ a b ?_
  rintro ⟨E, α⟩ ⟨E', β⟩ h
  change yZeroComplexSchemePointOfFull N hN
    (fullComplexSchemePointOfMarking N hN E α) =
      yZeroComplexSchemePointOfFull N hN
        (fullComplexSchemePointOfMarking N hN E' β) at h
  obtain ⟨g, hg⟩ := (yZeroComplexSchemePointOfFull_eq_iff_borel N hN
    (fullComplexSchemePointOfMarking N hN E α)
    (fullComplexSchemePointOfMarking N hN E' β)).mp h
  let αg : complexFullMarking N E :=
    E.glSmul (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) α
  have hpoint : fullComplexSchemePointOfMarking N hN E αg =
      fullComplexSchemePointOfMarking N hN E' β :=
    Subtype.ext ((fullComplexSchemePointOfMarking_glSmul N hN E g α).trans hg.symm)
  let e := complexFullMarkingIsoOfPointEq N hN E E' αg β hpoint
  let f := complexHomOverOfEllIso E E' e
  have hLevel : (gammaFullNaiveProblem (.of ℂ) N).map
      (complexEllHomOfHomOver E E' f).op β = αg := by
    change (gammaFullNaiveProblem (.of ℂ) N).map
      (complexEllHomOfHomOver E E' (complexHomOverOfEllIso E E' e)).op β = αg
    rw [complexEllHomOfHomOver_complexHomOverOfEllIso]
    exact complexFullMarkingIsoOfPointEq_level N hN E E' αg β hpoint
  have hP : αg.1.1.val ≫ f.hom = β.1.1.val :=
    (complexEllHomOfHomOver_pullSection_eq_iff E E' f αg.1.1 β.1.1).mp
      (congrArg (fun L : complexFullMarking N E => L.1.1) hLevel)
  have hQ : αg.1.2.val ≫ f.hom = β.1.2.val :=
    (complexEllHomOfHomOver_pullSection_eq_iff E E' f αg.1.2 β.1.2).mp
      (congrArg (fun L : complexFullMarking N E => L.1.2) hLevel)
  apply Quot.sound
  refine ⟨f, (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)),
    inferInstance, g.property, ?_, ?_⟩
  · exact Subtype.ext hP
  · exact Subtype.ext hQ

/-- The actual native Borel classes are equivalent to the actual coarse complex points. -/
def gammaHClassesComplexPointEquiv :
    GammaHClasses (Spec (.of ℂ)) N (borel N) ≃ yZeroComplexSchemePoint N hN :=
  Equiv.ofBijective (gammaHClassesComplexPoint N hN)
    ⟨gammaHClassesComplexPoint_injective N hN, gammaHClassesComplexPoint_surjective N hN⟩

/-- On a given marked curve, the equivalence computes the actual coarse classifier. -/
@[simp]
theorem gammaHClassesComplexPointEquiv_mk
    (E : ModularCurves.EllipticCurve (Spec (.of ℂ))) (L : E.FullLevelPt N) :
    gammaHClassesComplexPointEquiv N hN (GammaHClasses.mk (borel N) E L) =
      yZeroComplexSchemePointOfMarking N hN E L := rfl

/-- The inverse equivalence recovers the class of the given native marked curve. -/
@[simp]
theorem gammaHClassesComplexPointEquiv_symm_of_marking
    (E : ModularCurves.EllipticCurve (Spec (.of ℂ))) (L : E.FullLevelPt N) :
    (gammaHClassesComplexPointEquiv N hN).symm
        (yZeroComplexSchemePointOfMarking N hN E L) =
      GammaHClasses.mk (borel N) E L := by
  exact (gammaHClassesComplexPointEquiv N hN).symm_apply_apply
    (GammaHClasses.mk (borel N) E L)

/-- The equivalence computes source-j on the original native representative. -/
theorem gammaHClassesComplexPointEquiv_sourceJ_mk
    (E : ModularCurves.EllipticCurve (Spec (.of ℂ))) (L : E.FullLevelPt N) :
    yZeroComplexSourceJValue N hN
        (gammaHClassesComplexPointEquiv N hN (GammaHClasses.mk (borel N) E L)) =
      (fieldWeierstrassModel E.toEllipticCurveGeom).j :=
  gammaHClassesComplexPoint_sourceJ_mk N hN E L

/-- Any actual full lift computes the inverse as its actual native curve-and-level class. -/
theorem gammaHClassesComplexPointEquiv_symm_of_full
    (q : fullComplexSchemePoint N hN) :
    (gammaHClassesComplexPointEquiv N hN).symm
        (yZeroComplexSchemePointOfFull N hN q) =
      GammaHClasses.mk (borel N) (fullComplexPointEllObj N hN q).curve
        (fullComplexPointLevel N hN q) := by
  apply (gammaHClassesComplexPointEquiv N hN).injective
  rw [Equiv.apply_symm_apply]
  change yZeroComplexSchemePointOfFull N hN q =
    yZeroComplexSchemePointOfFull N hN
      (fullComplexSchemePointOfMarking N hN (fullComplexPointEllObj N hN q).curve
        (fullComplexPointLevel N hN q))
  exact (congrArg (yZeroComplexSchemePointOfFull N hN)
    (fullComplexSchemePointOfMarking_native N hN q)).symm

/-- A specified actual full lift gives the same inverse formula for its coarse point. -/
theorem gammaHClassesComplexPointEquiv_symm_of_lift
    (p : yZeroComplexSchemePoint N hN) (q : fullComplexSchemePoint N hN)
    (hq : yZeroComplexSchemePointOfFull N hN q = p) :
    (gammaHClassesComplexPointEquiv N hN).symm p =
      GammaHClasses.mk (borel N) (fullComplexPointEllObj N hN q).curve
        (fullComplexPointLevel N hN q) :=
  (congrArg (gammaHClassesComplexPointEquiv N hN).symm hq).symm.trans
    (gammaHClassesComplexPointEquiv_symm_of_full N hN q)

#print axioms ModularCurves.GammaHClasses
#print axioms ModularCurves.GammaHClasses.mk
#print axioms gammaHClassesComplexPoint
#print axioms gammaHClassesComplexPoint_mk
#print axioms gammaHClassesComplexPoint_sourceJ_mk
#print axioms gammaHClassesComplexPoint_surjective
#print axioms gammaHClassesComplexPoint_injective
#print axioms gammaHClassesComplexPointEquiv
#print axioms gammaHClassesComplexPointEquiv_mk
#print axioms gammaHClassesComplexPointEquiv_symm_of_marking
#print axioms gammaHClassesComplexPointEquiv_sourceJ_mk
#print axioms gammaHClassesComplexPointEquiv_symm_of_full
#print axioms gammaHClassesComplexPointEquiv_symm_of_lift

example (E : ModularCurves.EllipticCurve (Spec (.of ℂ))) (L : E.FullLevelPt 3) :
    gammaHClassesComplexPoint 3 (by decide) (GammaHClasses.mk (borel 3) E L) =
      yZeroComplexSchemePointOfMarking 3 (by decide) E L :=
  gammaHClassesComplexPoint_mk 3 (by decide) E L

example (E : ModularCurves.EllipticCurve (Spec (.of ℂ))) (L : E.FullLevelPt 3) :
    yZeroComplexSourceJValue 3 (by decide)
        (gammaHClassesComplexPoint 3 (by decide) (GammaHClasses.mk (borel 3) E L)) =
      (fieldWeierstrassModel E.toEllipticCurveGeom).j :=
  gammaHClassesComplexPoint_sourceJ_mk 3 (by decide) E L

example (p : yZeroComplexSchemePoint 3 (by decide)) :
    ∃ a : GammaHClasses (Spec (.of ℂ)) 3 (borel 3),
      gammaHClassesComplexPoint 3 (by decide) a = p :=
  gammaHClassesComplexPoint_surjective 3 (by decide) p

-- Two-sided roundtrip checks exercise the actual native-class/coarse-point equivalence.
example (p : yZeroComplexSchemePoint 3 (by decide)) :
    gammaHClassesComplexPointEquiv 3 (by decide)
        ((gammaHClassesComplexPointEquiv 3 (by decide)).symm p) = p :=
  (gammaHClassesComplexPointEquiv 3 (by decide)).right_inv p

example (a : GammaHClasses (Spec (.of ℂ)) 3 (borel 3)) :
    (gammaHClassesComplexPointEquiv 3 (by decide)).symm
        (gammaHClassesComplexPointEquiv 3 (by decide) a) = a :=
  (gammaHClassesComplexPointEquiv 3 (by decide)).left_inv a

end ModularPolynomialCurveTest.AINTLIB
