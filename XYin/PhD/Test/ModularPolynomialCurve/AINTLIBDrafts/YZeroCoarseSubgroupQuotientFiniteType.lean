/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseLocalQuotientFiniteType
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientSeparated
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite type and properness of the actual subgroup quotient

The raw local quotient scalar map is first turned into an honest morphism to
its actual affine base patch. Its triangle with the original chart map is
proved from the actual subtype scalar formula. The actual global quotient
structure map restricts to this morphism followed by the base open immersion;
the equality uses the real quotient projection's epimorphism property.

Over a locally Noetherian base scheme, the quotient structure map is locally
of finite type by the checked Artin--Tate ring result and source-locality on
the actual quotient chart cover. Mathlib's Noetherian instance then gives local
finite presentation. The already proved separatedness and universal closedness
give properness. No subgroup etaleness or domain assumption is imposed.

Public wrappers use the same chosen killing integer as the upstream raw
quotient. The literal axis is checked over any Noetherian base ring and on an
actual complex level-3 point. The Noetherian restriction is the scope of this
proof route; it is not asserted to be necessary for the mathematical quotient.
Smooth relative dimension one, a Weierstrass presentation, and target-j still
require independent proofs.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch)

/-- The raw local quotient's actual scalar map, viewed over its affine base patch. -/
noncomputable def quotientToBase : G.localQuotientOpen P.hstable ⟶ P.V.toScheme :=
  Spec.map (CommRingCat.ofHom (P.quotientBaseHom)) ≫ P.hV.isoSpec.inv

/-- The raw local quotient projection preserves the original chart structure map. -/
theorem localQuotientOpenπ_quotientToBase :
    G.localQuotientOpenπ P.hstable ≫ P.quotientToBase = P.chartToBase := by
  have hring : CommRingCat.ofHom (P.quotientBaseHom) ≫
      CommRingCat.ofHom (G.quotientRing P.hstable).subtype =
      E.π.appLE P.V P.U P.hover := by
    ext r
    exact congrArg (fun f : P.baseRing →+* P.chartRing => f r)
      (P.quotientBaseHom_comp_subtype)
  calc
    G.localQuotientOpenπ P.hstable ≫ P.quotientToBase =
        P.U.toSpecΓ ≫ (Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype) ≫
          Spec.map (CommRingCat.ofHom (P.quotientBaseHom))) ≫ P.hV.isoSpec.inv := by
      change (P.U.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype)) ≫
        (Spec.map (CommRingCat.ofHom (P.quotientBaseHom)) ≫ P.hV.isoSpec.inv) = _
      simp only [Category.assoc]
    _ = P.U.toSpecΓ ≫ Spec.map (E.π.appLE P.V P.U P.hover) ≫ P.hV.isoSpec.inv := by
      rw [← Spec.map_comp, hring]
    _ = P.chartToBase ≫ P.V.toSpecΓ ≫ P.hV.isoSpec.inv := by
      rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
      rfl
    _ = P.chartToBase := by simp

/-- The actual local quotient structure map is locally of finite type over its base patch. -/
theorem quotientToBase_locallyOfFiniteType [Module.Free P.baseRing P.groupRing]
    [IsNoetherianRing P.baseRing] : LocallyOfFiniteType P.quotientToBase := by
  have hf : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom P.quotientBaseHom)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (Q := RingHom.FiniteType)).mpr P.quotientBaseHom_finiteType
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom P.quotientBaseHom) ≫ P.hV.isoSpec.inv)
  exact MorphismProperty.comp_mem (@LocallyOfFiniteType) _ _ hf (inferInstance)

#print axioms quotientToBase
#print axioms localQuotientOpenπ_quotientToBase
#print axioms quotientToBase_locallyOfFiniteType

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch


namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : E.FiniteLocallyFreeSubgroup)
  (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

/-- The actual quotient structure map restricts to the actual affine-base scalar chart map. -/
theorem gluedQuotientι_gluedQuotientS (i : ↥E.E) :
    G.gluedQuotientι N hkill i ≫ G.gluedQuotientS N hkill =
      (G.gluePatch N hkill i).quotientToBase ≫ (G.gluePatch N hkill i).V.ι := by
  have : Module.Free (G.gluePatch N hkill i).baseRing
      (G.gluePatch N hkill i).groupRing := G.free_gluePatch N hkill i
  apply (G.gluePatch N hkill i).localQuotientOpenπ_hom_ext
  have hi : (G.gluePatch N hkill i).U.ι ≫ G.gluedQuotientπ N hkill =
      G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫
        G.gluedQuotientι N hkill i := G.ι_gluedQuotientπ N hkill i
  calc
    G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫
        (G.gluedQuotientι N hkill i ≫ G.gluedQuotientS N hkill) =
        (G.gluePatch N hkill i).U.ι ≫
          (G.gluedQuotientπ N hkill ≫ G.gluedQuotientS N hkill) := by
      rw [← Category.assoc, ← hi, Category.assoc]
    _ = (G.gluePatch N hkill i).U.ι ≫ E.π := by
      rw [G.gluedQuotientπ_gluedQuotientS N hkill]
    _ = (G.gluePatch N hkill i).chartToBase ≫ (G.gluePatch N hkill i).V.ι :=
      (G.gluePatch N hkill i).chartToBase_comp_ι.symm
    _ = G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫
        ((G.gluePatch N hkill i).quotientToBase ≫ (G.gluePatch N hkill i).V.ι) := by
      rw [← Category.assoc, AffineChartPatch.localQuotientOpenπ_quotientToBase]

#print axioms gluedQuotientι_gluedQuotientS

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup


namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : E.FiniteLocallyFreeSubgroup)
  (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

/-- The actual raw quotient is locally of finite type over a locally Noetherian base. -/
theorem gluedQuotientS_locallyOfFiniteType [IsLocallyNoetherian S] :
    LocallyOfFiniteType (G.gluedQuotientS N hkill) := by
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
      (Q := RingHom.FiniteType)
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
    (f := G.gluedQuotientS N hkill) (G.quotientGlueData N hkill).openCover).mpr ?_
  change ∀ i : ↥E.E, LocallyOfFiniteType
    (G.gluedQuotientι N hkill i ≫ G.gluedQuotientS N hkill)
  intro i
  have : Module.Free (G.gluePatch N hkill i).baseRing
      (G.gluePatch N hkill i).groupRing := G.free_gluePatch N hkill i
  have : IsNoetherianRing (G.gluePatch N hkill i).baseRing :=
    IsLocallyNoetherian.component_noetherian
      ⟨(G.gluePatch N hkill i).V, (G.gluePatch N hkill i).hV⟩
  rw [G.gluedQuotientι_gluedQuotientS N hkill i]
  have hf : LocallyOfFiniteType (G.gluePatch N hkill i).quotientToBase :=
    (G.gluePatch N hkill i).quotientToBase_locallyOfFiniteType
  exact MorphismProperty.comp_mem (@LocallyOfFiniteType) _ _ hf (inferInstance)

/-- The actual raw quotient is locally of finite presentation over a locally Noetherian base. -/
theorem gluedQuotientS_locallyOfFinitePresentation [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation (G.gluedQuotientS N hkill) := by
  have : LocallyOfFiniteType (G.gluedQuotientS N hkill) :=
    G.gluedQuotientS_locallyOfFiniteType N hkill
  infer_instance

/-- The actual raw quotient is proper over a locally Noetherian base. -/
theorem gluedQuotientS_isProper [IsLocallyNoetherian S] :
    IsProper (G.gluedQuotientS N hkill) := by
  have : IsSeparated (G.gluedQuotientS N hkill) := G.gluedQuotientS_isSeparated N hkill
  have : UniversallyClosed (G.gluedQuotientS N hkill) :=
    G.gluedQuotientS_universallyClosed N hkill
  have : LocallyOfFiniteType (G.gluedQuotientS N hkill) :=
    G.gluedQuotientS_locallyOfFiniteType N hkill
  exact {}

/-- The public chosen-killing quotient is locally of finite type over a locally Noetherian base. -/
theorem quotientS_locallyOfFiniteType [G.HasKillingInt] [IsLocallyNoetherian S] :
    LocallyOfFiniteType G.quotientS :=
  G.gluedQuotientS_locallyOfFiniteType G.killN G.killN_spec

/-- The public chosen-killing quotient is locally of finite presentation over that base. -/
theorem quotientS_locallyOfFinitePresentation [G.HasKillingInt] [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation G.quotientS :=
  G.gluedQuotientS_locallyOfFinitePresentation G.killN G.killN_spec

/-- The public chosen-killing quotient is proper over a locally Noetherian base. -/
theorem quotientS_isProper [G.HasKillingInt] [IsLocallyNoetherian S] : IsProper G.quotientS :=
  G.gluedQuotientS_isProper G.killN G.killN_spec

example [G.HasKillingInt] [IsLocallyNoetherian S] : IsProper G.quotientS := G.quotientS_isProper

#print axioms gluedQuotientS_locallyOfFinitePresentation
#print axioms gluedQuotientS_isProper
#print axioms quotientS_locallyOfFiniteType
#print axioms quotientS_locallyOfFinitePresentation
#print axioms quotientS_isProper

#print axioms gluedQuotientS_locallyOfFiniteType

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The literal marked constant-axis quotient is proper over every Noetherian base ring. -/
theorem sectionAxis_quotient_isProper (R : CommRingCat.{u}) [IsNoetherianRing R]
    (N : ℕ) [NeZero N] (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup R N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
    IsProper G.quotientS := by
  let G := sectionAxisSubgroup R N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
  exact G.quotientS_isProper

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let G := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    IsProper G.quotientS :=
  sectionAxis_quotient_isProper (.of ℂ) 3 (fullComplexPointEllObj 3 (by norm_num) p).curve
    (complexLevelNIsInvertible 3) (fullComplexPointLevel 3 (by norm_num) p)

#print axioms sectionAxis_quotient_isProper
#print axioms AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType
#print axioms AlgebraicGeometry.HasRingHomProperty.Spec_iff

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
