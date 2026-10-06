/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The actual finite projection to `YZeroCoarse`

The fine-level section ring is integral and of finite type over its Borel invariants,
so the actual quotient projection is finite. Its pullback on global sections is injective.
These facts need no Noetherian or domain hypothesis on the original base ring.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable {R : CommRingCat.{u}} (N : ℕ) [NeZero N]
variable (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R))

/-- Full-level sections form a finite module over their actual Borel invariants. -/
theorem yZeroInvariantRingι_finite : (yZeroInvariantRingι N hN hinv).hom.Finite := by
  apply RingHom.finite_iff_isIntegral_and_finiteType.mpr
  refine ⟨yZeroInvariantRingι_isIntegral N hN hinv, ?_⟩
  apply RingHom.FiniteType.of_comp_finiteType
    (f := yZeroInvariantCoefficientHom N hN hinv)
  rw [yZeroInvariantCoefficientHom_comp_inclusion]
  exact fullCoefficientHom_finiteType N hN hinv

/-- Pullback along the actual quotient projection is finite on global sections. -/
theorem yZeroPr_appTop_finite : (yZeroPr N hN hinv).appTop.hom.Finite := by
  rw [← yZeroSectionsIso_hom_comp_inclusion, CommRingCat.hom_comp,
    RingHom.finite_respectsIso.cancel_left_isIso]
  exact yZeroInvariantRingι_finite N hN hinv

/-- The actual fine-to-coarse scheme projection is finite over every allowed base ring. -/
theorem yZeroPr_isFinite : IsFinite (yZeroPr N hN hinv) := by
  have : IsFinite (Spec.map (yZeroInvariantRingι N hN hinv)) :=
    (IsFinite.SpecMap_iff _).mpr (yZeroInvariantRingι_finite N hN hinv)
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsFinite _
    (yZeroInvariantSpecIso N hN hinv).hom, yZeroPr_comp_invariantSpecIso_hom]
  infer_instance

/-- The actual quotient projection is surjective on scheme points. -/
theorem yZeroPr_surjective : Surjective (yZeroPr N hN hinv) :=
  inferInstanceAs (Surjective
    ((ModularCurves.xFullNaiveRepr (R := R) N hN hinv).coarsePr
      (ModularCurves.gammaHAut R N (ModularCurves.borel N))))

/-- Projection pullback is injective on all actual coarse global sections. -/
theorem yZeroPr_appTop_injective : Function.Injective (yZeroPr N hN hinv).appTop.hom := by
  rw [← yZeroSectionsIso_hom_comp_inclusion, CommRingCat.hom_comp]
  exact (yZeroInvariantRingι_injective N hN hinv).comp
    (ConcreteCategory.bijective_of_isIso (yZeroSectionsIso N hN hinv).hom).1

/-- An equality of coarse regular sections can be checked after fine-level pullback. -/
theorem yZeroPr_appTop_eq_iff
    (a b : Γ(ModularCurves.YZeroCoarse (R := R) N hN hinv, ⊤)) :
    (yZeroPr N hN hinv).appTop.hom a = (yZeroPr N hN hinv).appTop.hom b ↔ a = b :=
  (yZeroPr_appTop_injective N hN hinv).eq_iff

/-- Vanishing of a coarse regular section can be tested on the actual fine-level scheme. -/
theorem yZeroPr_appTop_eq_zero_iff
    (a : Γ(ModularCurves.YZeroCoarse (R := R) N hN hinv, ⊤)) :
    (yZeroPr N hN hinv).appTop.hom a = 0 ↔ a = 0 := by
  simpa only [map_zero] using yZeroPr_appTop_eq_iff N hN hinv a 0

#print axioms yZeroInvariantRingι_finite
#print axioms yZeroPr_isFinite
#print axioms yZeroPr_surjective
#print axioms yZeroPr_appTop_injective
#print axioms yZeroPr_appTop_eq_zero_iff

end ModularPolynomialCurveTest.AINTLIB
