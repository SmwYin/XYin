/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Separatedness of the actual subgroup quotient

Separatedness of a composite descends to its second map if the first map is
universally closed and surjective. The proof uses the induced universally
closed product map to descend closedness of the second diagonal; the diagonal
is then a closed immersion. Finite surjective precomposition is a corollary.
No noetherian or finite-type assumption is needed.

The actual subgroup quotient projection is finite and surjective, and its
composite with the structure map is the original separated elliptic-curve
structure map. Thus the actual glued quotient and the public chosen-killing
quotient are separated over the original arbitrary base scheme. The literal
marked axis is checked over any `Spec R`, with an actual complex level-3 test.
This supplies separatedness of the raw quotient. Finite type, properness,
smooth relative dimension one, a Weierstrass model, and target-j are separate
conclusions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Separatedness descends through universally closed surjective precomposition. -/
theorem IsSeparated.of_comp_universallyClosed_surjective {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [UniversallyClosed f] [Surjective f] [IsSeparated (f ≫ g)] :
    IsSeparated g := by
  let p : pullback (f ≫ g) (f ≫ g) ⟶ pullback g g :=
    pullback.map (f ≫ g) (f ≫ g) g g f f (𝟙 S) (by simp) (by simp)
  have : UniversallyClosed p :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) (inferInstance) (inferInstance) rfl rfl
  have hdiag : f ≫ pullback.diagonal g = pullback.diagonal (f ≫ g) ≫ p := by
    apply pullback.hom_ext <;> simp [p]
  have : UniversallyClosed (f ≫ pullback.diagonal g) := by
    rw [hdiag]
    infer_instance
  have : UniversallyClosed (pullback.diagonal g) :=
    UniversallyClosed.of_comp_surjective f (pullback.diagonal g)
  constructor
  apply IsClosedImmersion.of_isPreimmersion
  rw [← Set.image_univ]
  exact (pullback.diagonal g).isClosedMap _ isClosed_univ

/-- Finite surjective precomposition is a special case of closed-surjective descent. -/
theorem IsSeparated.of_comp_finite_surjective {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [IsFinite f] [Surjective f] [IsSeparated (f ≫ g)] :
    IsSeparated g :=
  IsSeparated.of_comp_universallyClosed_surjective f g

example {X S : Scheme.{u}} (g : X ⟶ S) [IsSeparated g] : IsSeparated g := by
  have : IsSeparated (𝟙 X ≫ g) := by simpa only [Category.id_comp]
  exact IsSeparated.of_comp_universallyClosed_surjective (𝟙 X) g

#print axioms IsSeparated.of_comp_universallyClosed_surjective
#print axioms IsSeparated.of_comp_finite_surjective
#print axioms MorphismProperty.pullbackMap
#print axioms UniversallyClosed.of_comp_surjective
#print axioms IsClosedImmersion.of_isPreimmersion

end AlgebraicGeometry

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : ModularCurves.EllipticCurve S}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

/-- The actual quotient structure map is separated over the original base. -/
theorem gluedQuotientS_isSeparated : IsSeparated (G.gluedQuotientS N hkill) := by
  have : IsFinite (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_isFinite N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  have : IsSeparated (G.gluedQuotientπ N hkill ≫ G.gluedQuotientS N hkill) := by
    rw [G.gluedQuotientπ_gluedQuotientS N hkill]
    infer_instance
  exact IsSeparated.of_comp_finite_surjective
    (G.gluedQuotientπ N hkill) (G.gluedQuotientS N hkill)

/-- The public quotient structure map is separated for its chosen killing integer. -/
theorem quotientS_isSeparated [G.HasKillingInt] : IsSeparated G.quotientS :=
  G.gluedQuotientS_isSeparated G.killN G.killN_spec

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The literal marked constant-axis quotient is separated over any base ring. -/
theorem sectionAxis_quotient_isSeparated (R : CommRingCat.{u}) (N : ℕ) [NeZero N]
    (E : ModularCurves.EllipticCurve (Spec R))
    (hinv : ModularCurves.NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup R N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
    IsSeparated G.quotientS := by
  let G := sectionAxisSubgroup R N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
  exact G.quotientS_isSeparated

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let G := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    IsSeparated G.quotientS :=
  sectionAxis_quotient_isSeparated (.of ℂ) 3
    (fullComplexPointEllObj 3 (by norm_num) p).curve
    (complexLevelNIsInvertible 3) (fullComplexPointLevel 3 (by norm_num) p)

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis

#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.gluedQuotientS_isSeparated
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.quotientS_isSeparated
#print axioms ModularPolynomialCurveTest.AINTLIB.ConstantAxis.sectionAxis_quotient_isSeparated
