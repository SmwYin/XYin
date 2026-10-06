/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.GroupScheme.StableChartData
public import AINTLIBDrafts.YZeroCoarseConstantAxis
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Actual group-chart stalk rank from the subgroup rank predicate

An actual affine chart patch inherits the subgroup's genuine `HasRank r`
condition as stalk rank `r` for its group section ring over the base-patch ring.
The existing finite flat group projection, its actual affine restriction,
and the literal `toSpecΓ`/`appLE` square identify the scheme fibre rank with
the coordinate-module stalk rank. A prime of the base ring lifts through the
actual affine chart isomorphism, where `HasRank` supplies the stated value.

No free-module, Noetherian, domain, étale, or model assumption is added. The
two examples check the given `HasRank` API and the actual marked-axis subgroup
whose rank is proved to be `N`. Local/global quotient ranks and native
function-field degrees remain separate steps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch)

/-- The actual group chart inherits stalk rank from the genuine subgroup rank predicate. -/
theorem groupRing_rankAtStalk (r : ℕ) (hG : G.HasRank r) (p : PrimeSpectrum P.baseRing) :
    Module.rankAtStalk (R := P.baseRing) P.groupRing p = r := by
  have : Module.Flat P.baseRing P.groupRing := by
    change (G.π.appLE P.V P.groupOpen le_rfl).hom.Flat
    exact G.π.flat_appLE P.hV P.isAffineOpen_groupOpen le_rfl
  have : IsIso P.V.toSpecΓ := P.isIso_toSpecΓ_V
  have : IsIso P.groupOpen.toSpecΓ := P.isIso_toSpecΓ_groupOpen
  let f : Spec P.groupRing ⟶ Spec P.baseRing :=
    Spec.map (G.π.appLE P.V P.groupOpen le_rfl)
  have : IsFinite f := by
    apply (IsFinite.SpecMap_iff _).mpr
    change (algebraMap P.baseRing P.groupRing).Finite
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : Flat f := Flat.SpecMap_iff.mpr
    (G.π.flat_appLE P.hV P.isAffineOpen_groupOpen le_rfl)
  have hsquare : IsPullback P.groupOpen.toSpecΓ P.groupToBase f P.V.toSpecΓ := by
    apply IsPullback.of_horiz_isIso
    refine ⟨?_⟩
    change P.groupOpen.toSpecΓ ≫ Spec.map (G.π.appLE P.V P.groupOpen le_rfl) =
      P.groupToBase ≫ P.V.toSpecΓ
    rw [show P.groupToBase = G.π.resLE P.V P.groupOpen le_rfl from
      (Scheme.Hom.resLE_eq_morphismRestrict (f := G.π) (U := P.V)).symm]
    exact Scheme.Opens.toSpecΓ_SpecMap_appLE G.π P.V P.groupOpen le_rfl
  let s : Spec Γ(S, P.V) := p
  let v : P.V.toScheme := (asIso P.V.toSpecΓ).inv.base s
  have hv : P.V.toSpecΓ.base v = s := by
    dsimp only [v]
    rw [← Scheme.Hom.comp_apply]
    change ((asIso P.V.toSpecΓ).inv ≫ (asIso P.V.toSpecΓ).hom).base s = s
    rw [Iso.inv_hom_id]
    rfl
  have hloc := Scheme.Hom.finrank_of_isPullback
    P.groupOpen.toSpecΓ P.groupToBase f P.V.toSpecΓ hsquare v
  rw [hv] at hloc
  have hspec : f.finrank s = Module.rankAtStalk (R := P.baseRing) P.groupRing p := by
    change (Spec.map (CommRingCat.ofHom (algebraMap P.baseRing P.groupRing))).finrank p = _
    exact Scheme.Hom.finrank_SpecMap_algebraMap P.baseRing P.groupRing p
  have hrest : P.groupToBase.finrank v = G.π.finrank (P.V.ι.base v) :=
    Scheme.Hom.finrank_of_isPullback P.groupOpen.ι P.groupToBase G.π P.V.ι
      (isPullback_morphismRestrict G.π P.V).flip v
  exact hspec.symm.trans (hloc.symm.trans (hrest.trans (hG _)))

example (r : ℕ) (hG : G.HasRank r) :
    ∀ p : PrimeSpectrum P.baseRing, Module.rankAtStalk (R := P.baseRing) P.groupRing p = r :=
  groupRing_rankAtStalk P r hG

open ModularPolynomialCurveTest.AINTLIB.ConstantAxis

example (R : CommRingCat.{u}) (N : ℕ) [NeZero N] (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N)
    (P : (sectionAxisSubgroup R N E hinv L).AffineChartPatch)
    (p : PrimeSpectrum P.baseRing) :
    Module.rankAtStalk (R := P.baseRing) P.groupRing p = N :=
  groupRing_rankAtStalk P N (sectionAxisSubgroup_hasRank R N E hinv L) p

#print axioms groupRing_rankAtStalk
#print axioms Scheme.Hom.finrank_SpecMap_algebraMap
#print axioms Scheme.Hom.finrank_of_isPullback
#print axioms isPullback_morphismRestrict
#print axioms Scheme.Opens.toSpecΓ_SpecMap_appLE
#print axioms isIso_toSpecΓ_V
#print axioms isIso_toSpecΓ_groupOpen
#print axioms instModuleFiniteGroupRing
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.HasRank
#print axioms sectionAxisSubgroup_hasRank
#print axioms Flat.flat_appLE
#print axioms IsFinite.SpecMap_iff
#print axioms Flat.SpecMap_iff

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch
