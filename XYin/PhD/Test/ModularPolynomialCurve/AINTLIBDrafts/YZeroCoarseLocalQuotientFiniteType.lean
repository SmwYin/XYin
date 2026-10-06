/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseLocalQuotientGeometry
public import Mathlib.RingTheory.Adjoin.Tower

/-!
# Finite type of the actual local subgroup quotient algebra

For an actual stable affine patch of an elliptic curve, the chart ring is finite
type over its actual affine base-patch ring. This follows from the curve's
structure map. If the base-patch ring is Noetherian and the group-patch ring is
free, the verified finite coinvariant extension and Artin--Tate show that the
coinvariant algebra is also finite type. No domain hypothesis is required.

The raw quotient is initially a subring. Its scalar map is defined by restricting
the existing geometric scalar map; the subtype-composition check identifies it
with the actual structure map on sections. The existing raw-subring/coinvariant
comparison is then an algebra equivalence for these explicit scalars. This
transfers finite type to the literal raw quotient ring and its scalar ring hom.
No global algebra instances are registered for the raw quotient.

The actual patch APIs require only group-patch freeness and Noetherianity of the
base-patch ring. The general subalgebra Artin--Tate wrapper retains its ambient
finite-type hypothesis. Sanities cover the actual source chart without extra
hypotheses, a product base ring, and the actual raw scalar map. No scheme-level
finite-type, finite-presentation, or quotient elliptic curve claim is made here.
-/

@[expose] public section

open AlgebraicGeometry ModularCurves
open scoped TensorProduct

noncomputable section

universe u

namespace ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

/-- Artin--Tate applied to a literal subalgebra with a finite ambient extension. -/
theorem subalgebra_finiteType_of_moduleFinite {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [IsNoetherianRing R] [Algebra.FiniteType R B]
    (C : Subalgebra R B) [Module.Finite C B] : Algebra.FiniteType R C :=
  ⟨fg_of_fg_of_fg R C B Algebra.FiniteType.out Module.Finite.fg_top
    Subtype.val_injective⟩

/-- The actual chart ring is finite type over its actual base patch by the curve structure map. -/
theorem chartRing_finiteType {S : Scheme.{u}} {E : EllipticCurve S}
    {G : E.FiniteLocallyFreeSubgroup} (P : G.AffineChartPatch) :
    Algebra.FiniteType P.baseRing P.chartRing := by
  have : Smooth E.π := SmoothOfRelativeDimension.smooth (n := 1) (f := E.π)
  have h : (algebraMap P.baseRing P.chartRing).FiniteType :=
    E.π.finiteType_appLE P.hV P.hU P.hover
  exact RingHom.finiteType_algebraMap.mp h

/-- The actual chart coinvariants are finite type over the actual affine base-patch ring. -/
theorem chartCoinvariants_finiteType {S : Scheme.{u}} {E : EllipticCurve S}
    {G : E.FiniteLocallyFreeSubgroup} (P : G.AffineChartPatch)
    [Module.Free P.baseRing P.groupRing] [IsNoetherianRing P.baseRing] :
    Algebra.FiniteType P.baseRing (coinvariants P.chartCoaction) := by
  have : Algebra.FiniteType P.baseRing P.chartRing := chartRing_finiteType P
  have : Module.Finite (coinvariants P.chartCoaction) P.chartRing := chartCoinvariants_finite P
  exact subalgebra_finiteType_of_moduleFinite (coinvariants P.chartCoaction)

example (C : Subalgebra (ℂ × ℂ) (ℂ × ℂ)) [Module.Finite C (ℂ × ℂ)] :
    Algebra.FiniteType (ℂ × ℂ) C :=
  subalgebra_finiteType_of_moduleFinite C

#print axioms subalgebra_finiteType_of_moduleFinite
#print axioms chartRing_finiteType
example {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
    (P : G.AffineChartPatch) : Algebra.FiniteType P.baseRing P.chartRing :=
  chartRing_finiteType P
#print axioms chartCoinvariants_finiteType

end ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch)

/-- Restriction along the actual curve structure map, with image in the raw quotient subring. -/
def quotientBaseHom : P.baseRing →+* G.quotientRing P.hstable :=
  (algebraMap P.baseRing P.chartRing).codRestrict _ fun r ↦ by
    rw [P.quotientRing_eq_coinvariants]
    exact (coinvariants P.chartCoaction).algebraMap_mem r

/-- The quotient scalar map has exactly the existing geometric scalar map after inclusion. -/
theorem quotientBaseHom_comp_subtype :
    (G.quotientRing P.hstable).subtype.comp (quotientBaseHom P) =
      (E.π.appLE P.V P.U P.hover).hom := by
  ext r
  rfl

/-- The raw quotient subring and chart coinvariants agree as algebras over the actual base ring. -/
def quotientCoinvariantsAlgEquiv :
    let _ : Algebra P.baseRing (G.quotientRing P.hstable) := (quotientBaseHom P).toAlgebra
    G.quotientRing P.hstable ≃ₐ[P.baseRing] coinvariants P.chartCoaction := by
  let : Algebra P.baseRing (G.quotientRing P.hstable) := (quotientBaseHom P).toAlgebra
  exact
    { (RingEquiv.subringCongr P.quotientRing_eq_coinvariants).trans P.coinvSubringEquiv with
      commutes' := fun r ↦ Subtype.ext (by rfl) }

variable [Module.Free P.baseRing P.groupRing] [IsNoetherianRing P.baseRing]

/-- Artin--Tate for the actual raw quotient ring with its explicitly fixed geometric scalar map. -/
theorem quotientRing_finiteType :
    let _ : Algebra P.baseRing (G.quotientRing P.hstable) := (quotientBaseHom P).toAlgebra
    Algebra.FiniteType P.baseRing (G.quotientRing P.hstable) := by
  let : Algebra P.baseRing (G.quotientRing P.hstable) := (quotientBaseHom P).toAlgebra
  exact (ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft.chartCoinvariants_finiteType P).equiv
    (quotientCoinvariantsAlgEquiv P).symm

/-- The actual quotient scalar ring homomorphism is finite type. -/
theorem quotientBaseHom_finiteType : (quotientBaseHom P).FiniteType := by
  let : Algebra P.baseRing (G.quotientRing P.hstable) := (quotientBaseHom P).toAlgebra
  exact RingHom.finiteType_algebraMap.mpr (quotientRing_finiteType P)

example : (quotientBaseHom P).FiniteType := quotientBaseHom_finiteType P

#print axioms quotientBaseHom
#print axioms quotientBaseHom_comp_subtype
#print axioms quotientCoinvariantsAlgEquiv
#print axioms quotientRing_finiteType
#print axioms quotientBaseHom_finiteType
#print axioms quotientRing_eq_coinvariants

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

#print axioms fg_of_fg_of_fg
#print axioms ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft.chartCoinvariants_finite
