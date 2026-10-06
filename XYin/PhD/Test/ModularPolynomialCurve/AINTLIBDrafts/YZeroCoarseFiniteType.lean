/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseInvariantSpec
public import ModularCurves.ModularCurve.YFullSmoothAffine
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.Algebraize

/-!
# Finite type of the actual AINTLIB `YZeroCoarse`

The full-level representing scheme is smooth and affine over the original base. Its actual
Borel invariant ring is therefore of finite type over a Noetherian base by Artin–Tate.
The scalar map is induced by the actual coarse structure map. In particular, disconnected
full-level schemes cause no issue: no domain assumption is used.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

namespace FiniteTypeDescent

/-- Artin–Tate in the form needed for an invariant-ring inclusion. -/
theorem finiteType_of_injective_integral
    {R B A : Type*} [CommRing R] [CommRing B] [CommRing A] [IsNoetherianRing R]
    (f : R →+* B) (i : B →+* A) (hi : Function.Injective i)
    (hint : i.IsIntegral) (hfin : (i.comp f).FiniteType) : f.FiniteType := by
  algebraize [f, i, i.comp f]
  have : Algebra.IsIntegral B A := Algebra.isIntegral_def.mpr hint
  have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType R B A
  have : Module.Finite B A := Algebra.IsIntegral.finite
  exact ⟨fg_of_fg_of_fg R B A (Algebra.FiniteType.out (R := R))
    Module.Finite.fg_top hi⟩

end FiniteTypeDescent

variable {R : CommRingCat.{u}} (N : ℕ) [NeZero N]
variable (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R))

/-- Smoothness of the actual full-level representing object used by `YZeroCoarse`. -/
theorem fullObject_structMap_smooth : Smooth (fullObject N hN hinv).structMap :=
  ((ModularCurves.YFull.gammaFullNaive_representable_assembly R N
    (by exact_mod_cast hN) hinv).2 (fullObject N hN hinv)
      ⟨ModularCurves.xFullNaiveRepr (R := R) N hN hinv⟩).1

/-- The original base acts on full-level global sections through the structure morphism. -/
def fullCoefficientHom : R →+* Γ((fullObject N hN hinv).base, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ (fullObject N hN hinv).structMap.appTop).hom

/-- Scalars in the actual invariant ring, obtained from the actual coarse structure map. -/
def yZeroInvariantCoefficientHom : R →+* yZeroInvariantRing N hN hinv :=
  ((Scheme.ΓSpecIso R).inv ≫ (yZeroStruct N hN hinv).appTop ≫
    (yZeroSectionsIso N hN hinv).hom).hom

/-- The invariant-ring scalar map agrees with the original scalar map after inclusion. -/
theorem yZeroInvariantCoefficientHom_comp_inclusion :
    (yZeroInvariantRingι N hN hinv).hom.comp (yZeroInvariantCoefficientHom N hN hinv) =
      fullCoefficientHom N hN hinv := by
  change (((Scheme.ΓSpecIso R).inv ≫ (yZeroStruct N hN hinv).appTop ≫
    (yZeroSectionsIso N hN hinv).hom) ≫ yZeroInvariantRingι N hN hinv).hom =
      ((Scheme.ΓSpecIso R).inv ≫ (fullObject N hN hinv).structMap.appTop).hom
  rw [Category.assoc, Category.assoc, yZeroSectionsIso_hom_comp_inclusion,
    ← Scheme.Hom.comp_appTop, yZeroPr_comp_yZeroStruct]

theorem yZeroInvariantRingι_injective :
    Function.Injective (yZeroInvariantRingι N hN hinv).hom := by
  exact Subtype.val_injective

/-- The finite Borel action makes every fine-level section integral over invariant sections. -/
theorem yZeroInvariantRingι_isIntegral : (yZeroInvariantRingι N hN hinv).hom.IsIntegral := by
  let : MulSemiringAction (ModularCurves.borel N) ↑Γ((fullObject N hN hinv).base, ⊤) :=
    (borelAction N hN hinv).gammaMulSemiringAction
      (show (borelAction N hN hinv).IsStableOpen (⊤ : (fullObject N hN hinv).base.Opens) from
        (borelAction N hN hinv).isStableOpen_preimage (fullObject N hN hinv).structMap
          (borelAction_over N hN hinv) (⊤ : (Spec R).Opens))
  exact Algebra.isIntegral_def.mp
    (Algebra.IsInvariant.isIntegral
      (FixedPoints.subalgebra ℤ ↑Γ((fullObject N hN hinv).base, ⊤) (ModularCurves.borel N))
      ↑Γ((fullObject N hN hinv).base, ⊤) (ModularCurves.borel N))

theorem fullCoefficientHom_finiteType : (fullCoefficientHom N hN hinv).FiniteType := by
  have : Smooth (fullObject N hN hinv).structMap := fullObject_structMap_smooth N hN hinv
  have hfin : (fullObject N hN hinv).structMap.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  exact hfin.comp (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso R).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2)

/-- The actual Borel invariant ring is of finite type over the original Noetherian base. -/
theorem yZeroInvariantCoefficientHom_finiteType [IsNoetherianRing R] :
    (yZeroInvariantCoefficientHom N hN hinv).FiniteType := by
  apply FiniteTypeDescent.finiteType_of_injective_integral
    (yZeroInvariantCoefficientHom N hN hinv) (yZeroInvariantRingι N hN hinv).hom
    (yZeroInvariantRingι_injective N hN hinv) (yZeroInvariantRingι_isIntegral N hN hinv)
  rw [yZeroInvariantCoefficientHom_comp_inclusion]
  exact fullCoefficientHom_finiteType N hN hinv

/-- The scalar algebra on actual Borel invariants, retained explicitly to avoid imposing it
on unrelated presentations of the same fixed subring. -/
abbrev yZeroInvariantAlgebra : Algebra R (yZeroInvariantRing N hN hinv) :=
  (yZeroInvariantCoefficientHom N hN hinv).toAlgebra

theorem yZeroInvariantRing_finiteType [IsNoetherianRing R] :
    letI := yZeroInvariantAlgebra N hN hinv
    Algebra.FiniteType R (yZeroInvariantRing N hN hinv) :=
  yZeroInvariantCoefficientHom_finiteType N hN hinv

/-- Actual Borel invariants are Noetherian whenever the original base ring is Noetherian. -/
theorem yZeroInvariantRing_isNoetherianRing [IsNoetherianRing R] :
    IsNoetherianRing (yZeroInvariantRing N hN hinv) := by
  let : Algebra R (yZeroInvariantRing N hN hinv) := yZeroInvariantAlgebra (R := R) N hN hinv
  have : Algebra.FiniteType R (yZeroInvariantRing N hN hinv) :=
    yZeroInvariantRing_finiteType (R := R) N hN hinv
  exact Algebra.FiniteType.isNoetherianRing R (yZeroInvariantRing N hN hinv)

/-- The actual coarse structure map is locally of finite type over a Noetherian base. -/
theorem yZeroStruct_locallyOfFiniteType [IsNoetherianRing R] :
    LocallyOfFiniteType (yZeroStruct N hN hinv) := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
  have hfin := yZeroInvariantCoefficientHom_finiteType N hN hinv
  unfold yZeroInvariantCoefficientHom at hfin
  rw [CommRingCat.hom_comp,
    RingHom.finiteType_respectsIso.cancel_left_isIso] at hfin
  rw [CommRingCat.hom_comp,
    RingHom.finiteType_respectsIso.cancel_right_isIso] at hfin
  exact hfin

/-- The actual coarse structure map is quasi-compact because it is affine. -/
theorem yZeroStruct_quasiCompact : QuasiCompact (yZeroStruct N hN hinv) :=
  inferInstanceAs (QuasiCompact
    ((ModularCurves.xFullNaiveRepr (R := R) N hN hinv).coarseStruct
      (ModularCurves.gammaHAut R N (ModularCurves.borel N))))

/-- Both defining properties of a finite-type scheme morphism hold for the actual coarse map. -/
theorem yZeroStruct_finiteType [IsNoetherianRing R] :
    LocallyOfFiniteType (yZeroStruct N hN hinv) ∧ QuasiCompact (yZeroStruct N hN hinv) :=
  ⟨yZeroStruct_locallyOfFiniteType N hN hinv, yZeroStruct_quasiCompact N hN hinv⟩

/-- Over `ℂ` the required invertibility of the level is automatic. -/
theorem complexLevelIsUnit (N : ℕ) [NeZero N] : IsUnit (N : ℂ) :=
  isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))

/-- An API check on the actual Borel invariant ring over `ℂ`, for every `N ≥ 3`. -/
theorem yZeroComplexInvariantRing_finiteType (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) :
    letI := yZeroInvariantAlgebra (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)
    Algebra.FiniteType ℂ
      (yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) :=
  yZeroInvariantRing_finiteType (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)

theorem yZeroComplexInvariantRing_isNoetherianRing
    (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) :
    IsNoetherianRing
      (yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) :=
  yZeroInvariantRing_isNoetherianRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)

theorem yZeroComplexStruct_locallyOfFiniteType (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) :
    LocallyOfFiniteType
      (yZeroStruct (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) :=
  yZeroStruct_locallyOfFiniteType (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)

theorem yZeroComplexStruct_finiteType (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) :
    LocallyOfFiniteType (yZeroStruct (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) ∧
      QuasiCompact (yZeroStruct (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) :=
  yZeroStruct_finiteType (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)

#print axioms fullObject_structMap_smooth
#print axioms yZeroInvariantCoefficientHom_comp_inclusion
#print axioms yZeroInvariantRingι_isIntegral
#print axioms yZeroInvariantCoefficientHom_finiteType
#print axioms yZeroInvariantRing_finiteType
#print axioms yZeroInvariantRing_isNoetherianRing
#print axioms yZeroStruct_locallyOfFiniteType
#print axioms yZeroStruct_quasiCompact
#print axioms yZeroStruct_finiteType
#print axioms yZeroComplexInvariantRing_finiteType
#print axioms yZeroComplexInvariantRing_isNoetherianRing
#print axioms yZeroComplexStruct_locallyOfFiniteType
#print axioms yZeroComplexStruct_finiteType

end ModularPolynomialCurveTest.AINTLIB
