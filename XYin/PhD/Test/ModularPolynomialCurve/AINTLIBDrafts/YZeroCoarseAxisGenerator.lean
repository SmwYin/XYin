/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseConstantAxis
public import ModularCurves.LevelStructure.Factorization
public import ModularCurves.ForMathlib.ClosedImmersionFinrankIso
public import ModularCurves.GroupScheme.CyclicSubgroup

/-!
# The actual constant axis has a Drinfeld generator

This integration test is checked against AINTLIB commit
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17` and its pinned Lean `v4.35.0-rc3` environment.

An `N`-killed section gives a map from the constant `ZMod N` scheme to its order divisor.
The divisor uses the sections `P, …, NP`, while the constant axis uses `0, …, (N-1)P`;
the index shift is justified modulo `N`, including the zero label.

For a full marking on `Spec R` with `N` invertible, the constant axis is a closed
immersion. Its map to the order divisor is a closed immersion between finite flat
locally finitely presented schemes of the same rank `N`, hence an isomorphism.
The kernel comparison identifies the literal bundled subgroup's divisor with the
order divisor. Factoring points transfer through this isomorphism for every test
scheme, proving the native `HasExactOrder`. The identity fppf cover then supplies the
native `IsCyclic` and `GammaZeroStructure`.

The actual complex-point specialization uses `fullComplexPointEllObj` and its literal
`fullComplexPointLevel`. Every actual coarse complex point has a full lift equipped
with this native Γ₀ datum. This is an existence statement on actual lifts; independence
of the lift and classification by Γ₀ isomorphism classes require further proofs.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves

noncomputable section

universe u

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

variable {S : Scheme.{u}} (E : EllipticCurve S) {N : ℕ} [NeZero N]

/-- The order-divisor index for the constant label `a`: its constituent is `(i+1)P`. -/
def orderIndex (a : ZMod N) : Fin N := ⟨(a - 1).val, ZMod.val_lt (a - 1)⟩

/-- The index shift gives the same section because its two coefficients agree modulo `N`. -/
theorem orderIndex_multiple (P : E.Section) (hP : (N : ℤ) • P = 0) (a : ZMod N) :
    ((((orderIndex a).val : ℤ) + 1) • P) = (a.val : ℤ) • P := by
  apply EllipticCurve.zsmul_eq_of_intCast_eq P hP
  simp only [orderIndex, Int.cast_add, Int.cast_natCast, Int.cast_one,
    ZMod.natCast_zmod_val, sub_add_cancel]

/-- Each constant-axis section factors through the actual finite-flat order divisor. -/
theorem axisSection_factors_orderDivisor (P : E.Section)
    (hP : (N : ℤ) • P = 0) (a : ZMod N) :
    ∃ h : S ⟶ (P.orderDivisor E N).ideal.subscheme,
      h ≫ (P.orderDivisor E N).ideal.subschemeι = ((a.val : ℤ) • P).val := by
  obtain ⟨h, hh⟩ := RelEffCartierDiv.factors_sectionsDivisor
    (fun i : Fin N ↦ ((((i.val : ℤ) + 1) • P) : E.Section))
    ⟨inferInstance, E.smooth⟩ (orderIndex a)
  refine ⟨h, hh.trans ?_⟩
  exact congrArg Subtype.val (orderIndex_multiple E P hP a)

/-- The coproduct of the constituent factorizations is a map to the order divisor. -/
def orderDivisorAxisLift (P : E.Section) (hP : (N : ℤ) • P = 0) :
    constScheme S (ZMod N) ⟶ (P.orderDivisor E N).ideal.subscheme :=
  Sigma.desc fun a ↦ (axisSection_factors_orderDivisor E P hP a).choose

/-- Composing the divisor lift with the subscheme immersion recovers the literal axis. -/
theorem orderDivisorAxisLift_ι (P : E.Section) (hP : (N : ℤ) • P = 0) :
    orderDivisorAxisLift E P hP ≫ (P.orderDivisor E N).ideal.subschemeι =
      sectionAxis (N := N) E P := by
  refine Sigma.hom_ext _ _ fun a ↦ ?_
  simp only [orderDivisorAxisLift, Sigma.ι_comp_desc_assoc, sectionAxis, Sigma.ι_comp_desc]
  exact (axisSection_factors_orderDivisor E P hP a).choose_spec

/-- The divisor lift is over the same base as the literal constant scheme. -/
theorem orderDivisorAxisLift_π (P : E.Section) (hP : (N : ℤ) • P = 0) :
    orderDivisorAxisLift E P hP ≫ ((P.orderDivisor E N).ideal.subschemeι ≫ E.π) =
      constSchemeπ S (ZMod N) := by
  rw [← Category.assoc, orderDivisorAxisLift_ι, sectionAxis_π]

section Affine

variable (R : CommRingCat.{u}) (N : ℕ) [NeZero N]

/-- The marked axis and the first section's order divisor are isomorphic over `Spec R`.
The finite/flat/lfp hypotheses below are the divisor's actual fields and the already
checked constant projection. The rank equality is the degree of the actual sections divisor. -/
theorem orderDivisorAxisLift_isIso (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    IsIso (orderDivisorAxisLift E L.val.1 L.property.1.1) := by
  let D := L.val.1.orderDivisor E N
  let j := orderDivisorAxisLift E L.val.1 L.property.1.1
  let g := D.ideal.subschemeι ≫ E.π
  have : IsFinite g := D.finite
  have : Flat g := D.flat
  have : LocallyOfFinitePresentation g := D.lfp
  have hι : j ≫ D.ideal.subschemeι = sectionAxis (N := N) E L.val.1 :=
    orderDivisorAxisLift_ι E L.val.1 L.property.1.1
  have hπ : j ≫ g = constSchemeπ (Spec R) (ZMod N) :=
    orderDivisorAxisLift_π E L.val.1 L.property.1.1
  have : IsClosedImmersion (j ≫ D.ideal.subschemeι) := by
    rw [hι]
    exact sectionAxis_isClosedImmersion R N E hinv L
  have : IsClosedImmersion j :=
    IsClosedImmersion.of_comp_isClosedImmersion j D.ideal.subschemeι
  have : IsFinite (j ≫ g) := by
    rw [hπ]
    exact constProjection_isFinite R N
  have : Flat (j ≫ g) := by
    rw [hπ]
    exact constProjection_flat R N
  have : LocallyOfFinitePresentation (j ≫ g) := by
    rw [hπ]
    exact constProjection_lfp R N
  apply isIso_of_isClosedImmersion_of_finrank_eq_isAffineBase g j
  intro s
  rw [hπ, constProjection_finrank R N]
  change N = D.degree s
  exact (RelEffCartierDiv.sectionsDivisor_degree E.π E.smooth
    (fun i : Fin N ↦ ((((i.val : ℤ) + 1) • L.val.1) : E.Section)) s).symm

/-- The literal bundled subgroup's divisor is the first section's actual order divisor. -/
theorem axisSubgroup_divisor_ideal (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    (sectionAxisSubgroup R N E hinv L).toRelEffCartierDiv.ideal =
      (L.val.1.orderDivisor E N).ideal := by
  have := orderDivisorAxisLift_isIso R N E hinv L
  rw [EllipticCurve.FiniteLocallyFreeSubgroup.toRelEffCartierDiv_ideal]
  change (sectionAxis (N := N) E L.val.1).ker = (L.val.1.orderDivisor E N).ideal
  rw [← orderDivisorAxisLift_ι E L.val.1 L.property.1.1,
    Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- The first section has native Drinfeld exact order, by subgroup transfer on every test scheme. -/
theorem firstSection_hasExactOrder (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    L.val.1.HasExactOrder E N := by
  change (L.val.1.orderDivisor E N).IsSubgroup E
  let j := orderDivisorAxisLift E L.val.1 L.property.1.1
  have : IsIso j := orderDivisorAxisLift_isIso R N E hinv L
  have hι : j ≫ (L.val.1.orderDivisor E N).ideal.subschemeι =
      sectionAxis (N := N) E L.val.1 :=
    orderDivisorAxisLift_ι E L.val.1 L.property.1.1
  intro T g
  obtain ⟨H, hH⟩ := sectionAxis_pointImage_isSubgroup E L.val.1 L.property.1.1 g
  refine ⟨H, fun Q ↦ (hH Q).trans ?_⟩
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h ≫ j, ?_⟩
    rw [Category.assoc, hι]
    exact hh
  · rintro ⟨h, hh⟩
    refine ⟨h ≫ inv j, ?_⟩
    rw [← hι, Category.assoc, IsIso.inv_hom_id_assoc]
    exact hh

/-- The actual constant-axis subgroup is cyclic in AINTLIB's fppf definition of record. -/
theorem axisSubgroup_isCyclic (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    (sectionAxisSubgroup R N E hinv L).IsCyclic N := by
  let t : Spec R ⟶ Spec R := 𝟙 (Spec R)
  let P₀ := EllipticCurve.Point.asSection E t (EllipticCurve.Point.pull E t L.val.1)
  refine EllipticCurve.FiniteLocallyFreeSubgroup.isCyclic_of_generator
    (sectionAxisSubgroup_hasRank R N E hinv L) t (fun x ↦ ⟨x, rfl⟩)
    (by infer_instance) (by infer_instance) P₀
    (EllipticCurve.Section.HasExactOrder.baseChange E
      (firstSection_hasExactOrder R N E hinv L) t) ?_
  have hD : (sectionAxisSubgroup R N E hinv L).toRelEffCartierDiv =
      L.val.1.orderDivisor E N := by
    apply RelEffCartierDiv.ext
    exact axisSubgroup_divisor_ideal R N E hinv L
  rw [hD, EllipticCurve.Section.orderDivisor_baseChange]

/-- The native Γ₀ datum supplied by a full marking over `Spec R` with `N` invertible. -/
def sectionAxisGammaZeroStructure (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) : E.GammaZeroStructure N :=
  EllipticCurve.GammaZeroStructure.ofIsCyclic (sectionAxisSubgroup R N E hinv L)
    (axisSubgroup_isCyclic R N E hinv L)

/-- Its subgroup is the literal constant-axis bundle. -/
theorem sectionAxisGammaZeroStructure_subgroup (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    (sectionAxisGammaZeroStructure R N E hinv L).subgroup =
      sectionAxisSubgroup R N E hinv L := rfl

/-- Its immersion is the literal section axis. -/
theorem sectionAxisGammaZeroStructure_ι (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    (sectionAxisGammaZeroStructure R N E hinv L).subgroup.ι =
      sectionAxis (N := N) E L.val.1 := rfl

/-- The native Γ₀ datum has the already checked rank `N`. -/
theorem sectionAxisGammaZeroStructure_hasRank (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    (sectionAxisGammaZeroStructure R N E hinv L).subgroup.HasRank N :=
  (sectionAxisGammaZeroStructure R N E hinv L).hasRank

/-- Its cyclicity is the native fppf predicate. -/
theorem sectionAxisGammaZeroStructure_isCyclic (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    (sectionAxisGammaZeroStructure R N E hinv L).subgroup.IsCyclic N :=
  (sectionAxisGammaZeroStructure R N E hinv L).isCyclic

end Affine

section ActualComplexPoints

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

/-- The actual pulled-back full marking has a first section of native exact order `N`. -/
theorem fullComplexPointFirstSection_hasExactOrder (p : fullComplexSchemePoint N hN) :
    (fullComplexPointLevel N hN p).val.1.HasExactOrder
      (fullComplexPointEllObj N hN p).curve N :=
  firstSection_hasExactOrder (R := .of ℂ) (N := N) (fullComplexPointEllObj N hN p).curve
    (complexLevelNIsInvertible N) (fullComplexPointLevel N hN p)

/-- The native Γ₀ structure on the actual elliptic object pulled back at a full complex point. -/
def fullComplexPointGammaZeroStructure (p : fullComplexSchemePoint N hN) :
    (fullComplexPointEllObj N hN p).curve.GammaZeroStructure N :=
  sectionAxisGammaZeroStructure (R := .of ℂ) (N := N) (fullComplexPointEllObj N hN p).curve
    (complexLevelNIsInvertible N) (fullComplexPointLevel N hN p)

/-- Its underlying subgroup is exactly the previously checked native constant-axis bundle. -/
theorem fullComplexPointGammaZeroStructure_subgroup (p : fullComplexSchemePoint N hN) :
    (fullComplexPointGammaZeroStructure N hN p).subgroup =
      fullComplexPointAxisSubgroup N hN p := rfl

/-- Its immersion is exactly the native pulled-back section axis. -/
theorem fullComplexPointGammaZeroStructure_ι (p : fullComplexSchemePoint N hN) :
    (fullComplexPointGammaZeroStructure N hN p).subgroup.ι =
      fullComplexPointAxis N hN p := rfl

/-- The actual native Γ₀ structure has rank `N`. -/
theorem fullComplexPointGammaZeroStructure_hasRank (p : fullComplexSchemePoint N hN) :
    (fullComplexPointGammaZeroStructure N hN p).subgroup.HasRank N :=
  (fullComplexPointGammaZeroStructure N hN p).hasRank

/-- The actual native Γ₀ structure is cyclic in the fppf sense. -/
theorem fullComplexPointGammaZeroStructure_isCyclic (p : fullComplexSchemePoint N hN) :
    (fullComplexPointGammaZeroStructure N hN p).subgroup.IsCyclic N :=
  (fullComplexPointGammaZeroStructure N hN p).isCyclic

/-- Every actual coarse complex point has a full lift with this honest native Γ₀ datum. -/
theorem yZeroComplexSchemePoint_lifts_withGammaZeroStructure
    (p : yZeroComplexSchemePoint N hN) :
    ∃ q : fullComplexSchemePoint N hN,
      yZeroComplexSchemePointOfFull N hN q = p ∧
        Nonempty ((fullComplexPointEllObj N hN q).curve.GammaZeroStructure N) := by
  obtain ⟨q, hq⟩ := yZeroComplexSchemePoint_lifts N hN p
  exact ⟨q, hq, ⟨fullComplexPointGammaZeroStructure N hN q⟩⟩

end ActualComplexPoints

#print axioms orderIndex_multiple
#print axioms axisSection_factors_orderDivisor
#print axioms orderDivisorAxisLift
#print axioms orderDivisorAxisLift_ι
#print axioms orderDivisorAxisLift_π
#print axioms orderDivisorAxisLift_isIso
#print axioms axisSubgroup_divisor_ideal
#print axioms firstSection_hasExactOrder
#print axioms axisSubgroup_isCyclic
#print axioms sectionAxisGammaZeroStructure
#print axioms sectionAxisGammaZeroStructure_subgroup
#print axioms sectionAxisGammaZeroStructure_ι
#print axioms sectionAxisGammaZeroStructure_hasRank
#print axioms sectionAxisGammaZeroStructure_isCyclic
#print axioms fullComplexPointFirstSection_hasExactOrder
#print axioms fullComplexPointGammaZeroStructure
#print axioms fullComplexPointGammaZeroStructure_subgroup
#print axioms fullComplexPointGammaZeroStructure_ι
#print axioms fullComplexPointGammaZeroStructure_hasRank
#print axioms fullComplexPointGammaZeroStructure_isCyclic
#print axioms yZeroComplexSchemePoint_lifts_withGammaZeroStructure

#print axioms AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι
#print axioms ModularCurves.EllipticCurve.Section.HasExactOrder.baseChange
#print axioms ModularCurves.EllipticCurve.Section.orderDivisor_baseChange
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.isCyclic_of_generator

example (q : fullComplexSchemePoint 3 (by decide)) :
    (fullComplexPointGammaZeroStructure 3 (by decide) q).subgroup.ι =
      fullComplexPointAxis 3 (by decide) q := rfl

example (q : fullComplexSchemePoint 3 (by decide)) :
    (fullComplexPointGammaZeroStructure 3 (by decide) q).subgroup.HasRank 3 :=
  fullComplexPointGammaZeroStructure_hasRank 3 (by decide) q

example (q : fullComplexSchemePoint 3 (by decide)) :
    (fullComplexPointGammaZeroStructure 3 (by decide) q).subgroup.IsCyclic 3 :=
  fullComplexPointGammaZeroStructure_isCyclic 3 (by decide) q

example (p : yZeroComplexSchemePoint 3 (by decide)) :
    ∃ q : fullComplexSchemePoint 3 (by decide),
      yZeroComplexSchemePointOfFull 3 (by decide) q = p ∧
        Nonempty ((fullComplexPointEllObj 3 (by decide) q).curve.GammaZeroStructure 3) :=
  yZeroComplexSchemePoint_lifts_withGammaZeroStructure 3 (by decide) p

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
