/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientGeometry

/-!
# Quasi-compactness of the actual subgroup quotient

Quasi-compactness of a composite descends to its second map when the first map
is surjective. The proof uses the continuous image of each compact composite
preimage and works for arbitrary schemes.

For the actual glued subgroup quotient, quasi-compactness follows directly
from the universally closed structure map proved in
`YZeroCoarseSubgroupQuotientGeometry`. The wrappers use the actual chosen killing
integer, and the constant-axis check uses its directly proved killing datum.
This proves quasi-compactness of the quotient structure map; separatedness,
finite type, properness, and a Weierstrass presentation remain separate goals.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Quasi-compactness descends to the second map through a surjective first map. -/
theorem QuasiCompact.of_comp_surjective {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [QuasiCompact (f ≫ g)] :
    QuasiCompact g := by
  constructor
  intro U hU hcompact
  have hpre : IsCompact (f ⁻¹' (g ⁻¹' U)) := by
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] using
      QuasiCompact.isCompact_preimage (f := f ≫ g) U hU hcompact
  simpa only [Set.image_preimage_eq _ f.surjective] using hpre.image f.continuous

example {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] : QuasiCompact g := by
  have : QuasiCompact (𝟙 X ≫ g) := by simpa only [Category.id_comp]
  exact QuasiCompact.of_comp_surjective (𝟙 X) g

#print axioms QuasiCompact.of_comp_surjective
#print axioms AlgebraicGeometry.QuasiCompact.isCompact_preimage
#print axioms Set.image_preimage_eq
#print axioms IsCompact.image

end AlgebraicGeometry

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : ModularCurves.EllipticCurve S}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

/-- The actual glued quotient is quasi-compact over the original base. -/
theorem gluedQuotientS_quasiCompact : QuasiCompact (G.gluedQuotientS N hkill) := by
  have : UniversallyClosed (G.gluedQuotientS N hkill) :=
    G.gluedQuotientS_universallyClosed N hkill
  infer_instance

/-- The public quotient is quasi-compact for its actual chosen killing integer. -/
theorem quotientS_quasiCompact [G.HasKillingInt] : QuasiCompact G.quotientS :=
  G.gluedQuotientS_quasiCompact G.killN G.killN_spec

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The literal marked constant-axis quotient is quasi-compact over any base ring. -/
theorem sectionAxis_quotient_quasiCompact (R : CommRingCat.{u}) (N : ℕ) [NeZero N]
    (E : ModularCurves.EllipticCurve (Spec R))
    (hinv : ModularCurves.NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup R N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
    QuasiCompact G.quotientS := by
  let G := sectionAxisSubgroup R N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
  exact G.quotientS_quasiCompact

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let G := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    QuasiCompact G.quotientS :=
  sectionAxis_quotient_quasiCompact (.of ℂ) 3
    (fullComplexPointEllObj 3 (by norm_num) p).curve
    (complexLevelNIsInvertible 3) (fullComplexPointLevel 3 (by norm_num) p)

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis

#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.gluedQuotientS_quasiCompact
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.quotientS_quasiCompact
#print axioms ModularPolynomialCurveTest.AINTLIB.ConstantAxis.sectionAxis_quotient_quasiCompact
