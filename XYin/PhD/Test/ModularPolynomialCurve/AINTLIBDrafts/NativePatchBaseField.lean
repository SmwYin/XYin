/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.GroupScheme.SubgroupQuotientGlueData

/-!
# Base sections of a nonempty native elliptic-curve patch over a field

An actual affine chart patch with nonempty source open lies over the whole
one-point field spectrum. Its literal base-patch section ring identifies with
the original field through the genuine presheaf equality isomorphism and
`ΓSpecIso`. The actual chosen gluing patch supplies its own nonemptiness witness.

These two interfaces require no subgroup freeness, étale or Noetherian premise.
They install no field instance and assert no source-chart integral closedness.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  {G : E.FiniteLocallyFreeSubgroup} (P : G.AffineChartPatch)

/-- A nonempty curve patch lies over the whole one-point field spectrum. -/
theorem baseOpen_eq_top (hU : Nonempty P.U) : P.V = ⊤ := by
  obtain ⟨x⟩ := hU
  apply top_unique
  intro y _
  have hx : E.π.base x.val ∈ P.V := P.hover x.property
  exact (Subsingleton.elim (E.π.base x.val) y) ▸ hx

/-- The actual base-patch section ring identifies with the original field. -/
noncomputable def baseRingEquivFieldOfNonempty (hU : Nonempty P.U) : P.baseRing ≃+* k :=
  ((Spec (.of k)).presheaf.mapIso (eqToIso (P.baseOpen_eq_top hU).symm).op ≪≫
    Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv

example (x : E.E) (hx : x ∈ P.U) : P.V = ⊤ :=
  P.baseOpen_eq_top ⟨⟨x, hx⟩⟩

noncomputable example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
    (x : E.E) : (G.gluePatch N hkill x).baseRing ≃+* k :=
  (G.gluePatch N hkill x).baseRingEquivFieldOfNonempty ⟨⟨x, G.mem_gluePatch N hkill x⟩⟩

#print axioms baseOpen_eq_top
#print axioms baseRingEquivFieldOfNonempty
#print axioms Scheme.ΓSpecIso
#print axioms CategoryTheory.Functor.mapIso
#print axioms CategoryTheory.Iso.commRingCatIsoToRingEquiv
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.gluePatch
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.mem_gluePatch

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch
