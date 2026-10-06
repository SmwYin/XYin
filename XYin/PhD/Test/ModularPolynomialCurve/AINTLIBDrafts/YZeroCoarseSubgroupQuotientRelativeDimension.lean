/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import AINTLIBDrafts.YZeroCoarseChartQuotientRelativeDimension
public import AINTLIBDrafts.YZeroCoarseConstantAxisEtale

/-!
# Relative dimension one of the actual subgroup quotient

The conditional local API preserves any relative dimension of the literal
quotient scalar ring map through the actual affine-base isomorphism. The
checked raw chart condition supplies dimension one under a free patch,
etale subgroup projection, and Noetherian base patch.

The actual quotient gluing cover and its structural triangles then give
smooth relative dimension one over a locally Noetherian base. Each final
open immersion has dimension zero, so composition adds one and zero. The
public wrapper uses its actual chosen killing integer; the marked-axis
wrapper supplies subgroup etaleness over any Noetherian ring.

This independently proves the relative-curve property of the original raw
quotient. Genus one, a pointed Weierstrass model, and quotient-j still
require separate mathematical inputs.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch)

/-- The actual local quotient structure map has the relative dimension of its scalar map. -/
theorem quotientToBase_smoothOfRelativeDimension_of_locally (n : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) P.quotientBaseHom) :
    SmoothOfRelativeDimension n P.quotientToBase := by
  have : SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom P.quotientBaseHom)) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))).mpr h
  change SmoothOfRelativeDimension n
    (Spec.map (CommRingCat.ofHom P.quotientBaseHom) ≫ P.hV.isoSpec.inv)
  exact inferInstanceAs (SmoothOfRelativeDimension (n + 0)
    (Spec.map (CommRingCat.ofHom P.quotientBaseHom) ≫ P.hV.isoSpec.inv))

/-- The actual free quotient chart has relative dimension one. -/
theorem quotientToBase_smoothOfRelativeDimension_one [Module.Free P.baseRing P.groupRing]
    [Etale G.π] [IsNoetherianRing P.baseRing] :
    SmoothOfRelativeDimension 1 P.quotientToBase :=
  P.quotientToBase_smoothOfRelativeDimension_of_locally 1
    P.quotientBaseHom_locally_standardSmoothRelDim_one

#print axioms quotientToBase_smoothOfRelativeDimension_of_locally
#print axioms quotientToBase_smoothOfRelativeDimension_one
#print axioms quotientBaseHom_locally_standardSmoothRelDim_one
#print axioms quotientToBase
#print axioms AlgebraicGeometry.HasRingHomProperty.Spec_iff
#print axioms AlgebraicGeometry.smoothOfRelativeDimension_comp

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : E.FiniteLocallyFreeSubgroup)
  (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
  [Etale G.π] [IsLocallyNoetherian S]

/-- The actual glued quotient has relative dimension one over its original base. -/
theorem gluedQuotientS_smoothOfRelativeDimension_one :
    SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension 1)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @SmoothOfRelativeDimension 1)
    (f := G.gluedQuotientS N hkill) (G.quotientGlueData N hkill).openCover).mpr ?_
  change ∀ i : ↥E.E, SmoothOfRelativeDimension 1
    (G.gluedQuotientι N hkill i ≫ G.gluedQuotientS N hkill)
  intro i
  have : Module.Free (G.gluePatch N hkill i).baseRing
      (G.gluePatch N hkill i).groupRing := G.free_gluePatch N hkill i
  have : IsNoetherianRing (G.gluePatch N hkill i).baseRing :=
    IsLocallyNoetherian.component_noetherian
      ⟨(G.gluePatch N hkill i).V, (G.gluePatch N hkill i).hV⟩
  rw [G.gluedQuotientι_gluedQuotientS N hkill i]
  have : SmoothOfRelativeDimension 1 (G.gluePatch N hkill i).quotientToBase :=
    (G.gluePatch N hkill i).quotientToBase_smoothOfRelativeDimension_one
  exact inferInstanceAs (SmoothOfRelativeDimension (1 + 0)
    ((G.gluePatch N hkill i).quotientToBase ≫ (G.gluePatch N hkill i).V.ι))

/-- The public chosen-killing quotient has the same relative dimension one. -/
theorem quotientS_smoothOfRelativeDimension_one [G.HasKillingInt] :
    SmoothOfRelativeDimension 1 G.quotientS :=
  G.gluedQuotientS_smoothOfRelativeDimension_one G.killN G.killN_spec

example [G.HasKillingInt] : SmoothOfRelativeDimension 1 G.quotientS :=
  G.quotientS_smoothOfRelativeDimension_one

#print axioms gluedQuotientS_smoothOfRelativeDimension_one
#print axioms quotientS_smoothOfRelativeDimension_one
#print axioms gluedQuotientι_gluedQuotientS
#print axioms free_gluePatch

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The actual marked-axis quotient has relative dimension one over a Noetherian ring. -/
theorem sectionAxis_quotientS_smoothOfRelativeDimension_one (R : CommRingCat.{u})
    [IsNoetherianRing R] (N : ℕ) [NeZero N] (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup R N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
    SmoothOfRelativeDimension 1 G.quotientS := by
  let G := sectionAxisSubgroup R N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
  have : Etale G.π := sectionAxisSubgroup_etale R N E hinv L
  exact G.quotientS_smoothOfRelativeDimension_one

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let E : EllipticCurve (Spec (.of ℂ)) := (fullComplexPointEllObj 3 (by norm_num) p).curve
    let G : E.FiniteLocallyFreeSubgroup := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    SmoothOfRelativeDimension 1 G.quotientS :=
  sectionAxis_quotientS_smoothOfRelativeDimension_one (.of ℂ) 3
    (fullComplexPointEllObj 3 (by norm_num) p).curve (complexLevelNIsInvertible 3)
    (fullComplexPointLevel 3 (by norm_num) p)

#print axioms sectionAxis_quotientS_smoothOfRelativeDimension_one
#print axioms sectionAxisSubgroup_etale
#print axioms sectionAxisSubgroup_hasKillingInt
#print axioms AlgebraicGeometry.IsLocallyNoetherian.component_noetherian
#print axioms AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover
#print axioms AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
