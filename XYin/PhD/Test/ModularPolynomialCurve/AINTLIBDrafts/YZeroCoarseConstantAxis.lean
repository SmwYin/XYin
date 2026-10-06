/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.GroupScheme.GLSchemeAction
public import ModularCurves.EllipticCurve.TorsionUnramifiedFibre
public import ModularCurves.GroupScheme.SubgroupQuotientInterface
public import AINTLIBDrafts.YZeroCoarseFineComplexPoints

/-!
# The constant first-coordinate axis of a naive full-level marking

An `N`-killed section gives a morphism from the constant `ZMod N` scheme to the curve.
For every test scheme, the image of this morphism on points is an additive subgroup:
locally constant `ZMod N` labels map additively to points, and the image consists exactly
of the points factoring through the morphism.

For a naive full-level marking, this morphism is the first-coordinate axis of AINTLIB's
actual `fullLevelHom` into `E[N]`. Hence every factoring point is killed by `N`, directly
from the torsion universal property. We instantiate these facts with the literal marking
on the elliptic object pulled back from an actual fine complex point.

Over `Spec R`, when `N` is invertible, the section axis is a closed immersion and its
structure morphism is finite, flat, locally of finite presentation, and of rank `N`.
We bundle the resulting actual finite locally free subgroup and prove its killing
integer directly from the torsion pullback. The divisor generator condition used by
`IsCyclic` is a separate comparison.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves

noncomputable section

universe u

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

variable {S : Scheme.{u}} (E : EllipticCurve S) {N : ℕ} [NeZero N]

/-- The first-coordinate inclusion of `ZMod N` in the full-level label set. -/
def axisLabel (a : ZMod N) : Fin 2 → ZMod N := ![a, 0]

/-- The first-coordinate morphism between the actual constant schemes. -/
def axisInclusion (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    constScheme S (ZMod N) ⟶ constScheme S (Fin 2 → ZMod N) :=
  Sigma.desc fun a ↦ Sigma.ι (fun _ : Fin 2 → ZMod N ↦ S) (axisLabel a)

/-- The axis inclusion respects the constant-scheme structure maps. -/
theorem axisInclusion_π :
    axisInclusion S N ≫ constSchemeπ S (Fin 2 → ZMod N) = constSchemeπ S (ZMod N) := by
  refine Sigma.hom_ext _ _ fun a ↦ ?_
  simp [axisInclusion, constSchemeπ]

/-- Send the label `a` to the section `(a.val : ℤ) • P`. -/
def sectionAxis (P : E.Section) : constScheme S (ZMod N) ⟶ E.E :=
  Sigma.desc fun a ↦ (((a.val : ℤ) • P : E.Section).val)

/-- The section axis is a morphism over the base. -/
theorem sectionAxis_π (P : E.Section) :
    sectionAxis (N := N) E P ≫ E.π = constSchemeπ S (ZMod N) := by
  refine Sigma.hom_ext _ _ fun a ↦ ?_
  simp only [sectionAxis, Sigma.ι_comp_desc_assoc, constSchemeπ, Sigma.ι_comp_desc]
  exact (((a.val : ℤ) • P : E.Section).property)

/-- The section axis is the first coordinate of the literal full-level torsion map. -/
theorem axisInclusion_fullLevelHom (L : E.FullLevelPt N) :
    axisInclusion S N ≫ E.fullLevelHom L ≫ E.torsionι N = sectionAxis E L.val.1 := by
  refine Sigma.hom_ext _ _ fun a ↦ ?_
  simp [axisInclusion, axisLabel, EllipticCurve.fullLevelHom, sectionAxis,
    E.pointToTorsion_torsionι]

/-- Evaluate the section axis on a locally constant label over any test scheme. -/
def axisPoint (P : E.Section) {T : Scheme.{u}} (g : T ⟶ S)
    (c : LocallyConstant T (ZMod N)) : E.Point g :=
  let h := (constSchemePointsEquiv S (ZMod N) g).symm c
  ⟨h.val ≫ sectionAxis E P, by
    rw [Category.assoc, sectionAxis_π, h.property]⟩

/-- On a constant-label piece, the axis point is the corresponding pulled section. -/
theorem axisPoint_on_piece (P : E.Section) {T : Scheme.{u}} (g : T ⟶ S)
    (c : LocallyConstant T (ZMod N)) (a : ZMod N) {U : T.Opens}
    (hU : U ≤ locConstPiece c a) :
    EllipticCurve.Point.restrict E U.ι (axisPoint E P g c) =
      EllipticCurve.Point.pull E (U.ι ≫ g) ((a.val : ℤ) • P) := by
  let h := (constSchemePointsEquiv S (ZMod N) g).symm c
  have hindex : constSchemePointsEquiv S (ZMod N) g ⟨h.val, h.property⟩ = c := by
    have heta : (⟨h.val, h.property⟩ :
        {f : T ⟶ constScheme S (ZMod N) // f ≫ constSchemeπ S (ZMod N) = g}) = h :=
      Subtype.ext rfl
    rw [heta]
    exact (constSchemePointsEquiv S (ZMod N) g).apply_symm_apply c
  have hf : U.ι ≫ h.val = (U.ι ≫ g) ≫ Sigma.ι (fun _ : ZMod N ↦ S) a :=
    constMap_factor_of_le h.val h.property a (by rw [hindex]; exact hU)
  apply Subtype.ext
  change U.ι ≫ (h.val ≫ sectionAxis E P) =
    (U.ι ≫ g) ≫ (((a.val : ℤ) • P : E.Section).val)
  rw [← Category.assoc, hf, Category.assoc, sectionAxis, Sigma.ι_comp_desc]

/-- An `N`-killed section makes evaluation on locally constant labels additive. -/
theorem axisPoint_add (P : E.Section) (hP : (N : ℤ) • P = 0)
    {T : Scheme.{u}} (g : T ⟶ S) (c₁ c₂ : LocallyConstant T (ZMod N)) :
    axisPoint E P g (c₁ + c₂) = axisPoint E P g c₁ + axisPoint E P g c₂ := by
  let c : LocallyConstant T (ZMod N × ZMod N) :=
    ⟨fun t ↦ (c₁ t, c₂ t), c₁.isLocallyConstant.prodMk c₂.isLocallyConstant⟩
  apply Subtype.ext
  apply locConst_hom_ext c
  intro a
  let U := locConstPiece c a
  have h₁ : U ≤ locConstPiece c₁ a.1 := by
    intro t ht
    exact congrArg Prod.fst ht
  have h₂ : U ≤ locConstPiece c₂ a.2 := by
    intro t ht
    exact congrArg Prod.snd ht
  have hsum : U ≤ locConstPiece (c₁ + c₂) (a.1 + a.2) := by
    intro t ht
    change c₁ t + c₂ t = a.1 + a.2
    rw [h₁ ht, h₂ ht]
  have heq : EllipticCurve.Point.restrict E U.ι (axisPoint E P g (c₁ + c₂)) =
      EllipticCurve.Point.restrict E U.ι (axisPoint E P g c₁ + axisPoint E P g c₂) := by
    rw [E.restrict_add, axisPoint_on_piece E P g _ _ hsum,
      axisPoint_on_piece E P g _ _ h₁, axisPoint_on_piece E P g _ _ h₂,
      ← EllipticCurve.Point.pull_add, ← E.val_smul_add P hP]
  exact congrArg Subtype.val heq

/-- The additive point map from the constant cyclic group scheme. -/
def axisPointAddHom (P : E.Section) (hP : (N : ℤ) • P = 0)
    {T : Scheme.{u}} (g : T ⟶ S) : LocallyConstant T (ZMod N) →+ E.Point g where
  toFun := axisPoint E P g
  map_add' := axisPoint_add E P hP g
  map_zero' := by
    have h := (axisPoint_add E P hP g 0 0).symm
    exact add_eq_left.mp (by simpa only [zero_add] using h)

/-- The point-map image is exactly the points factoring through the section axis. -/
theorem axisPoint_range_iff_factoring (P : E.Section) (hP : (N : ℤ) • P = 0)
    {T : Scheme.{u}} (g : T ⟶ S) (Q : E.Point g) :
    Q ∈ (axisPointAddHom E P hP g).range ↔
      ∃ h : T ⟶ constScheme S (ZMod N), h ≫ sectionAxis E P = Q.val := by
  change (∃ c, axisPoint E P g c = Q) ↔ _
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨((constSchemePointsEquiv S (ZMod N) g).symm c).val, rfl⟩
  · rintro ⟨h, hh⟩
    have hπ : h ≫ constSchemeπ S (ZMod N) = g := by
      rw [← sectionAxis_π E P, ← Category.assoc, hh, Q.property]
    refine ⟨constSchemePointsEquiv S (ZMod N) g ⟨h, hπ⟩, ?_⟩
    apply Subtype.ext
    change ((constSchemePointsEquiv S (ZMod N) g).symm
      ((constSchemePointsEquiv S (ZMod N) g) ⟨h, hπ⟩)).val ≫ sectionAxis E P = Q.val
    simpa only [Equiv.symm_apply_apply] using hh

/-- The subgroup condition holds for every test scheme, including nonreduced schemes. -/
theorem sectionAxis_pointImage_isSubgroup (P : E.Section) (hP : (N : ℤ) • P = 0)
    {T : Scheme.{u}} (g : T ⟶ S) :
    ∃ H : AddSubgroup (E.Point g), ∀ Q : E.Point g,
      Q ∈ H ↔ ∃ h : T ⟶ constScheme S (ZMod N), h ≫ sectionAxis E P = Q.val :=
  ⟨(axisPointAddHom E P hP g).range, axisPoint_range_iff_factoring E P hP g⟩

/-- The first-coordinate torsion factorization attached to an actual naive full marking. -/
def torsionAxis (L : E.FullLevelPt N) : constScheme S (ZMod N) ⟶ E.torsion N :=
  axisInclusion S N ≫ E.fullLevelHom L

/-- The torsion factorization gives the same section axis in the elliptic curve. -/
theorem torsionAxis_ι (L : E.FullLevelPt N) :
    torsionAxis E L ≫ E.torsionι N = sectionAxis E L.val.1 := by
  rw [torsionAxis, Category.assoc]
  exact axisInclusion_fullLevelHom E L

/-- The torsion axis is over the same base as the constant cyclic scheme. -/
theorem torsionAxis_π (L : E.FullLevelPt N) :
    torsionAxis E L ≫ E.torsionπ N = constSchemeπ S (ZMod N) := by
  rw [torsionAxis, Category.assoc, E.fullLevelHom_torsionπ, axisInclusion_π]

/-- Multiplication by `N` kills the literal section-axis morphism, by the torsion pullback. -/
theorem sectionAxis_mulByHom (L : E.FullLevelPt N) :
    sectionAxis (N := N) E L.val.1 ≫ E.mulByHom N =
      constSchemeπ S (ZMod N) ≫ E.zero := by
  have hcond : E.torsionι N ≫ E.mulByHom N = E.torsionπ N ≫ E.zero :=
    pullback.condition
  rw [← torsionAxis_ι E L, Category.assoc, hcond, ← Category.assoc, torsionAxis_π]

/-- Every point factoring through the marked section axis is killed by `N`.
This uses the actual `E[N]` universal property, without a rank-kills theorem. -/
theorem sectionAxis_factors_killed (L : E.FullLevelPt N) {T : Scheme.{u}} (g : T ⟶ S)
    (Q : E.Point g)
    (hQ : ∃ h : T ⟶ constScheme S (ZMod N), h ≫ sectionAxis E L.val.1 = Q.val) :
    (N : ℤ) • Q = 0 := by
  apply (E.torsionι_factors_iff N g Q).mp
  obtain ⟨h, hh⟩ := hQ
  refine ⟨h ≫ torsionAxis E L, ?_⟩
  rw [Category.assoc, torsionAxis_ι]
  exact hh

section AffineClosedAxis

variable (R : CommRingCat.{u}) (N : ℕ) [NeZero N]

/-- Restrict functions on the full-level label set to the first-coordinate axis. -/
def axisRestriction : ((Fin 2 → ZMod N) → R) →+* (ZMod N → R) :=
  RingHom.pi fun a ↦ Pi.evalRingHom (fun _ : Fin 2 → ZMod N ↦ R) (axisLabel a)

omit [NeZero N] in
/-- Extension along the first-coordinate projection is a right inverse to restriction. -/
theorem axisRestriction_surjective : Function.Surjective (axisRestriction R N) := by
  intro f
  exact ⟨fun v ↦ f (v 0), rfl⟩

/-- The constant-axis morphism is the spectrum of the literal restriction homomorphism. -/
theorem axisInclusion_comp_specIso :
    axisInclusion (Spec R) N ≫ (constSchemeSpecIso R (Fin 2 → ZMod N)).hom =
      (constSchemeSpecIso R (ZMod N)).hom ≫
        Spec.map (CommRingCat.ofHom (axisRestriction R N)) := by
  refine Sigma.hom_ext _ _ fun a ↦ ?_
  rw [axisInclusion, Sigma.ι_comp_desc_assoc, constSchemeSpecIso_ι_hom,
    constSchemeSpecIso_ι_hom_assoc, ← Spec.map_comp]
  congr 1

/-- Over `Spec R`, the constant first-coordinate axis is a closed immersion. -/
theorem axisInclusion_isClosedImmersion : IsClosedImmersion (axisInclusion (Spec R) N) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (axisRestriction R N))) :=
    IsClosedImmersion.spec_of_surjective _ (axisRestriction_surjective R N)
  have h : axisInclusion (Spec R) N = (constSchemeSpecIso R (ZMod N)).hom ≫
      Spec.map (CommRingCat.ofHom (axisRestriction R N)) ≫
        (constSchemeSpecIso R (Fin 2 → ZMod N)).inv := by
    apply (cancel_mono (constSchemeSpecIso R (Fin 2 → ZMod N)).hom).mp
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact axisInclusion_comp_specIso R N
  rw [h]
  infer_instance

/-- The first section of a naive full marking gives a closed axis when `N` is invertible. -/
theorem sectionAxis_isClosedImmersion (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    IsClosedImmersion (sectionAxis (N := N) E L.val.1) := by
  have := axisInclusion_isClosedImmersion R N
  have := E.torsionι_isClosedImmersion N
  have hmap : (E.fullLevelIso hinv L).hom = E.fullLevelHom L := rfl
  rw [← axisInclusion_fullLevelHom E L, ← hmap]
  infer_instance

/-- The constant cyclic scheme over an affine base is finite over that base. -/
theorem constProjection_isFinite : IsFinite (constSchemeπ (Spec R) (ZMod N)) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (Pi.constRingHom (ZMod N) R))) := by
    apply (IsFinite.SpecMap_iff _).mpr
    change (algebraMap R (ZMod N → R)).Finite
    exact RingHom.finite_algebraMap.mpr inferInstance
  rw [← constSchemeSpecIso_hom_π R (ZMod N)]
  infer_instance

/-- The constant cyclic scheme is flat over its affine base. -/
theorem constProjection_flat : Flat (constSchemeπ (Spec R) (ZMod N)) := by
  infer_instance

/-- The constant cyclic scheme is locally of finite presentation over its affine base. -/
theorem constProjection_lfp :
    LocallyOfFinitePresentation (constSchemeπ (Spec R) (ZMod N)) :=
  IsZariskiLocalAtSource.sigmaDesc (fun _ ↦ inferInstance)

/-- The constant cyclic scheme has rank `N`, including over an arbitrary base ring. -/
theorem constProjection_finrank (s : Spec R) :
    (constSchemeπ (Spec R) (ZMod N)).finrank s = N := by
  let p : PrimeSpectrum R := s
  have := constProjection_isFinite R N
  have := constProjection_flat R N
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (ZMod N → R)))) := by
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R (ZMod N → R)))) := by
    apply Flat.SpecMap_iff.mpr
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  rw [← constSchemeSpecIso_hom_π R (ZMod N)]
  change ((constSchemeSpecIso R (ZMod N)).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (ZMod N → R)))).finrank p = N
  rw [Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_SpecMap_algebraMap (R : Type u) (ZMod N → R) p]
  rw [Module.rankAtStalk_pi (R := R) (fun _ : ZMod N ↦ (R : Type u)) p]
  have : Nontrivial R := p.nontrivial
  simp [finsum_eq_sum_of_fintype]

/-- The first marked section gives an actual finite locally free subgroup over `Spec R`. -/
def sectionAxisSubgroup (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    E.FiniteLocallyFreeSubgroup where
  G := constScheme (Spec R) (ZMod N)
  ι := sectionAxis (N := N) E L.val.1
  closedImmersion := sectionAxis_isClosedImmersion R N E hinv L
  finite := by
    rw [sectionAxis_π]
    exact constProjection_isFinite R N
  flat := by
    rw [sectionAxis_π]
    exact constProjection_flat R N
  lfp := by
    rw [sectionAxis_π]
    exact constProjection_lfp R N
  subgroup := by
    intro T g
    exact sectionAxis_pointImage_isSubgroup E L.val.1 L.property.1.1 g

/-- Its rank is the cardinality of the literal constant label scheme. -/
theorem sectionAxisSubgroup_hasRank (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    (sectionAxisSubgroup R N E hinv L).HasRank N := by
  intro s
  change (sectionAxis (N := N) E L.val.1 ≫ E.π).finrank s = N
  rw [sectionAxis_π]
  exact constProjection_finrank R N s

/-- Its killing integer is `N`, proved independently of the generic rank-kills theorem. -/
theorem sectionAxisSubgroup_hasKillingInt (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    (sectionAxisSubgroup R N E hinv L).HasKillingInt := by
  refine ⟨N, NeZero.ne N, ?_⟩
  change sectionAxis (N := N) E L.val.1 ≫ E.mulByHom N =
    (sectionAxis (N := N) E L.val.1 ≫ E.π) ≫ E.zero
  rw [sectionAxis_π]
  exact sectionAxis_mulByHom E L

end AffineClosedAxis

section ActualComplexMarking

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

/-- The nonzero level is invertible in the actual global section ring of `Spec ℂ`. -/
theorem complexLevelNIsInvertible : NIsInvertible (Spec (.of ℂ)) N := by
  change IsUnit (N : Γ(Spec (.of ℂ), ⊤))
  simpa only [map_natCast] using
    (complexLevelIsUnit N).map (Scheme.ΓSpecIso (.of ℂ)).inv.hom

local instance constantAxisComplexPointAddCommGroup (p : fullComplexSchemePoint N hN)
    {T : Scheme} (g : T ⟶ Spec (.of ℂ)) :
    AddCommGroup ((fullComplexPointEllObj N hN p).curve.Point g) :=
  EllipticCurve.pointAddCommGroup (fullComplexPointEllObj N hN p).curve g

/-- The section axis of the actual marking on the native pulled-back elliptic object. -/
def fullComplexPointAxis (p : fullComplexSchemePoint N hN) :
    constScheme (Spec (.of ℂ)) (ZMod N) ⟶ (fullComplexPointEllObj N hN p).curve.E :=
  sectionAxis (N := N) (fullComplexPointEllObj N hN p).curve
    (fullComplexPointLevel N hN p).val.1

/-- Its explicit factorization through the native pulled-back curve's actual torsion. -/
def fullComplexPointTorsionAxis (p : fullComplexSchemePoint N hN) :
    constScheme (Spec (.of ℂ)) (ZMod N) ⟶
      (fullComplexPointEllObj N hN p).curve.torsion N :=
  torsionAxis (fullComplexPointEllObj N hN p).curve (fullComplexPointLevel N hN p)

/-- The native torsion factorization agrees with the native marked section axis. -/
theorem fullComplexPointTorsionAxis_ι (p : fullComplexSchemePoint N hN) :
    fullComplexPointTorsionAxis N hN p ≫ (fullComplexPointEllObj N hN p).curve.torsionι N =
      fullComplexPointAxis N hN p :=
  torsionAxis_ι (fullComplexPointEllObj N hN p).curve (fullComplexPointLevel N hN p)

/-- The actual complex marking supplies the point-image subgroup on every test scheme. -/
theorem fullComplexPointAxis_pointImage_isSubgroup (p : fullComplexSchemePoint N hN)
    {T : Scheme} (g : T ⟶ Spec (.of ℂ)) :
    ∃ H : AddSubgroup ((fullComplexPointEllObj N hN p).curve.Point g),
      ∀ Q : (fullComplexPointEllObj N hN p).curve.Point g,
        Q ∈ H ↔ ∃ h : T ⟶ constScheme (Spec (.of ℂ)) (ZMod N),
          h ≫ fullComplexPointAxis N hN p = Q.val :=
  sectionAxis_pointImage_isSubgroup (fullComplexPointEllObj N hN p).curve
    (fullComplexPointLevel N hN p).val.1 (fullComplexPointLevel N hN p).property.1.1 g

/-- The actual marked section-axis image is killed by `N` on every test scheme. -/
theorem fullComplexPointAxis_factors_killed (p : fullComplexSchemePoint N hN)
    {T : Scheme} (g : T ⟶ Spec (.of ℂ))
    (Q : (fullComplexPointEllObj N hN p).curve.Point g)
    (hQ : ∃ h : T ⟶ constScheme (Spec (.of ℂ)) (ZMod N),
      h ≫ fullComplexPointAxis N hN p = Q.val) : (N : ℤ) • Q = 0 :=
  sectionAxis_factors_killed (fullComplexPointEllObj N hN p).curve
    (fullComplexPointLevel N hN p) g Q hQ

/-- The first-coordinate axis of the actual pulled-back marking is a closed immersion. -/
theorem fullComplexPointAxis_isClosedImmersion (p : fullComplexSchemePoint N hN) :
    IsClosedImmersion (fullComplexPointAxis N hN p) :=
  sectionAxis_isClosedImmersion (R := .of ℂ) (N := N)
    (fullComplexPointEllObj N hN p).curve (complexLevelNIsInvertible N)
    (fullComplexPointLevel N hN p)

/-- The actual full complex marking gives a finite locally free rank-`N` axis subgroup. -/
def fullComplexPointAxisSubgroup (p : fullComplexSchemePoint N hN) :
    (fullComplexPointEllObj N hN p).curve.FiniteLocallyFreeSubgroup :=
  sectionAxisSubgroup (R := .of ℂ) (N := N) (fullComplexPointEllObj N hN p).curve
    (complexLevelNIsInvertible N) (fullComplexPointLevel N hN p)

/-- Its immersion is the literal section axis, without a presentation change. -/
theorem fullComplexPointAxisSubgroup_ι (p : fullComplexSchemePoint N hN) :
    (fullComplexPointAxisSubgroup N hN p).ι = fullComplexPointAxis N hN p := rfl

/-- The native bundled subgroup has rank `N`. -/
theorem fullComplexPointAxisSubgroup_hasRank (p : fullComplexSchemePoint N hN) :
    (fullComplexPointAxisSubgroup N hN p).HasRank N :=
  sectionAxisSubgroup_hasRank (R := .of ℂ) (N := N) (fullComplexPointEllObj N hN p).curve
    (complexLevelNIsInvertible N) (fullComplexPointLevel N hN p)

/-- The native bundled subgroup has the checked killing integer `N`. -/
theorem fullComplexPointAxisSubgroup_hasKillingInt (p : fullComplexSchemePoint N hN) :
    (fullComplexPointAxisSubgroup N hN p).HasKillingInt :=
  sectionAxisSubgroup_hasKillingInt (R := .of ℂ) (N := N)
    (fullComplexPointEllObj N hN p).curve (complexLevelNIsInvertible N)
    (fullComplexPointLevel N hN p)

end ActualComplexMarking

#print axioms axisInclusion_fullLevelHom
#print axioms axisPoint_add
#print axioms axisPoint_range_iff_factoring
#print axioms sectionAxis_pointImage_isSubgroup
#print axioms torsionAxis_ι
#print axioms torsionAxis_π
#print axioms sectionAxis_mulByHom
#print axioms sectionAxis_factors_killed
#print axioms axisInclusion_comp_specIso
#print axioms axisInclusion_isClosedImmersion
#print axioms sectionAxis_isClosedImmersion
#print axioms constProjection_isFinite
#print axioms constProjection_flat
#print axioms constProjection_lfp
#print axioms constProjection_finrank
#print axioms sectionAxisSubgroup
#print axioms sectionAxisSubgroup_hasRank
#print axioms sectionAxisSubgroup_hasKillingInt
#print axioms complexLevelNIsInvertible
#print axioms fullComplexPointAxis
#print axioms fullComplexPointTorsionAxis_ι
#print axioms fullComplexPointAxis_pointImage_isSubgroup
#print axioms fullComplexPointAxis_factors_killed
#print axioms fullComplexPointAxis_isClosedImmersion
#print axioms fullComplexPointAxisSubgroup
#print axioms fullComplexPointAxisSubgroup_ι
#print axioms fullComplexPointAxisSubgroup_hasRank
#print axioms fullComplexPointAxisSubgroup_hasKillingInt

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
