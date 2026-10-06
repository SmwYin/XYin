/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseMarkedComplexCurves

/-!
# Equal fine classification points identify the original marked complex curves

The chosen full-level representation supplies a pointed comparison isomorphism
from each marked complex curve to the native universal-curve pullback at its
classification point. Equality of the actual fine points identifies those pullbacks
and their actual full-level markings. Composing the first comparison isomorphism,
this equality identification, and the inverse second comparison isomorphism gives
a pointed isomorphism between the original curves that transports their markings.

The construction uses the literal `complexFullMarkingNativeIso` objects and the
existing native marking-transport theorem. It needs no automorphism-freeness or
coarse-points classification theorem. The level-transport proof uses only equality
induction, functor composition, and the actual isomorphism inverse laws.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ModularCurves

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

/-- The marking transports along the native object identification of equal fine points. -/
theorem fullComplexPointLevel_eqToIso
    (p q : fullComplexSchemePoint N hN) (h : p = q) :
    (gammaFullNaiveProblem (.of ℂ) N).map
      (eqToIso (congrArg (fullComplexPointEllObj N hN) h)).hom.op
      (fullComplexPointLevel N hN q) = fullComplexPointLevel N hN p := by
  cases h
  simp

variable (E E' : ModularCurves.EllipticCurve (Spec (.of ℂ)))
variable (α : complexFullMarking N E) (β : complexFullMarking N E')

/-- Equal actual fine classification points identify the original pointed curve objects. -/
def complexFullMarkingIsoOfPointEq
    (hpoint : fullComplexSchemePointOfMarking N hN E α =
      fullComplexSchemePointOfMarking N hN E' β) :
    complexEllObj E ≅ complexEllObj E' :=
  complexFullMarkingNativeIso N hN E α ≪≫
    eqToIso (congrArg (fullComplexPointEllObj N hN) hpoint) ≪≫
      (complexFullMarkingNativeIso N hN E' β).symm

/-- The resulting pointed isomorphism transports the original target marking to the source. -/
theorem complexFullMarkingIsoOfPointEq_level
    (hpoint : fullComplexSchemePointOfMarking N hN E α =
      fullComplexSchemePointOfMarking N hN E' β) :
    (gammaFullNaiveProblem (.of ℂ) N).map
      (complexFullMarkingIsoOfPointEq N hN E E' α β hpoint).hom.op β = α := by
  let F := gammaFullNaiveProblem (.of ℂ) N
  let i := complexFullMarkingNativeIso N hN E α
  let j := complexFullMarkingNativeIso N hN E' β
  let k := eqToIso (congrArg (fullComplexPointEllObj N hN) hpoint)
  let t := fullComplexPointLevel N hN (fullComplexSchemePointOfMarking N hN E α)
  let t' := fullComplexPointLevel N hN (fullComplexSchemePointOfMarking N hN E' β)
  have hi : F.map i.hom.op t = α := complexFullMarkingNativeIso_level N hN E α
  have hj : F.map j.hom.op t' = β := complexFullMarkingNativeIso_level N hN E' β
  have hjInv : F.map j.inv.op β = t' := by
    calc
      F.map j.inv.op β = F.map j.inv.op (F.map j.hom.op t') :=
        congrArg (F.map j.inv.op) hj.symm
      _ = F.map (j.hom.op ≫ j.inv.op) t' := (F.map_comp_apply _ _ _).symm
      _ = t' := by
        rw [← op_comp, j.inv_hom_id, op_id, F.map_id_apply]
  have hk : F.map k.hom.op t' = t :=
    fullComplexPointLevel_eqToIso N hN _ _ hpoint
  change F.map (i ≪≫ k ≪≫ j.symm).hom.op β = α
  simp only [Iso.trans_hom, Iso.symm_hom, op_comp, Functor.map_comp_apply]
  rw [hjInv, hk, hi]

example : complexFullMarkingIsoOfPointEq N hN E E α α rfl = Iso.refl (complexEllObj E) := by
  simp [complexFullMarkingIsoOfPointEq]

example (E E' : ModularCurves.EllipticCurve (Spec (.of ℂ)))
    (α : complexFullMarking 3 E) (β : complexFullMarking 3 E')
    (hpoint : fullComplexSchemePointOfMarking 3 (by norm_num) E α =
      fullComplexSchemePointOfMarking 3 (by norm_num) E' β) :
    ∃ e : complexEllObj E ≅ complexEllObj E',
      (gammaFullNaiveProblem (.of ℂ) 3).map e.hom.op β = α :=
  ⟨complexFullMarkingIsoOfPointEq 3 (by norm_num) E E' α β hpoint,
    complexFullMarkingIsoOfPointEq_level 3 (by norm_num) E E' α β hpoint⟩

#print axioms fullComplexPointLevel_eqToIso
#print axioms complexFullMarkingIsoOfPointEq
#print axioms complexFullMarkingIsoOfPointEq_level
#print axioms complexFullMarkingNativeIso_level
#print axioms CategoryTheory.eqToIso

end ModularPolynomialCurveTest.AINTLIB
