/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.GroupTheory.Index
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.Ring

/-! # The lower quotient diagram of Janusz V.4.1

The induced map is the actual quotient map A/R → B/f(R). Finiteness of A/R is
proved from finite ker f and finite B/f(R), not included as an extra assumption.
-/

noncomputable section
namespace Cox.QuotientDiagram
variable {A B : Type*} [CommGroup A] [CommGroup B]
variable (f : A →* B) (R : Subgroup A)

/-- The actual induced map after quotienting by R and its image. -/
def quotientMap : (A ⧸ R) →* (B ⧸ R.map f) :=
  QuotientGroup.map R (R.map f) f (Subgroup.le_comap_map f R)

/-- The representative formula fixes the induced map. -/
theorem quotientMap_apply (a : A) :
    quotientMap f R (QuotientGroup.mk a) = QuotientGroup.mk (f a) := by
  rfl

/-- Lifting an element of the bottom kernel and dividing by an R-lift puts it in ker f. -/
theorem quotientMap_ker_eq :
    (quotientMap f R).ker = f.ker.map (QuotientGroup.mk' R) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H a =>
  rw [MonoidHom.mem_ker, quotientMap_apply, QuotientGroup.eq_one_iff, Subgroup.mem_map,
    Subgroup.mem_map]
  constructor
  · rintro ⟨r, hr, hfr⟩
    refine ⟨a * r⁻¹, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hfr, mul_inv_cancel]
    · rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
      simpa [mul_assoc] using hr
  · rintro ⟨b, hb, hba⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hba
    refine ⟨b⁻¹ * a, hba, ?_⟩
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp hb, inv_one, one_mul]

/-- The bottom kernel is the quotient of ker f by its intersection with R. -/
theorem quotientMap_ker_equiv :
    Nonempty ((f.ker ⧸ R.comap f.ker.subtype) ≃* (quotientMap f R).ker) := by
  let φ : f.ker →* (quotientMap f R).ker :=
    ((QuotientGroup.mk' R).comp f.ker.subtype).codRestrict _ fun x => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
        quotientMap_apply, MonoidHom.mem_ker.mp x.2, QuotientGroup.mk_one]
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [quotientMap_ker_eq] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨⟨b, hb⟩, rfl⟩
  have hker : φ.ker = R.comap f.ker.subtype := by
    ext x
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

/-- The range of the bottom map is the projected range of the original map. -/
theorem quotientMap_range_eq :
    (quotientMap f R).range = f.range.map (QuotientGroup.mk' (R.map f)) := by
  have hcomp : (quotientMap f R).comp (QuotientGroup.mk' R) =
      (QuotientGroup.mk' (R.map f)).comp f := by
    ext a
    rfl
  have h1 : ((quotientMap f R).comp (QuotientGroup.mk' R)).range = (quotientMap f R).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective R),
      ← MonoidHom.range_eq_map]
  rw [← h1, hcomp, MonoidHom.range_comp]

/-- Quotienting by a subgroup of the range preserves the cokernel. -/
theorem quotientMap_cokernel_equiv :
    Nonempty (((B ⧸ R.map f) ⧸ (quotientMap f R).range) ≃* (B ⧸ f.range)) := by
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (quotientMap_range_eq f R)).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ (Subgroup.map_le_range f R))⟩

/-- The actual finite upper kernel maps onto the lower kernel. -/
theorem quotientMap_ker_finite [Finite f.ker] : Finite (quotientMap f R).ker := by
  obtain ⟨e⟩ := quotientMap_ker_equiv f R
  exact Finite.of_equiv _ e.toEquiv

/-- Kernel cardinalities differ by exactly the kernel/ray intersection. -/
theorem quotientMap_ker_card [Finite f.ker] :
    Nat.card f.ker = Nat.card ↥(f.ker ⊓ R) * Nat.card (quotientMap f R).ker := by
  have e : (R.comap f.ker.subtype) ≃ ↥(f.ker ⊓ R) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨E⟩ := quotientMap_ker_equiv f R
  rw [← Subgroup.card_mul_index (R.comap f.ker.subtype), Nat.card_congr e, Subgroup.index,
    Nat.card_congr E.toEquiv]

/-- The two cokernel indices agree, without assuming their ambient groups finite. -/
theorem quotientMap_range_index : (quotientMap f R).range.index = f.range.index := by
  obtain ⟨e⟩ := quotientMap_cokernel_equiv f R
  rw [Subgroup.index, Subgroup.index, Nat.card_congr e.toEquiv]

/-- A finite lower target and finite kernel imply a finite lower source. -/
theorem quotientMap_domain_finite [Finite f.ker] [(R.map f).FiniteIndex] :
    Finite (A ⧸ R) := by
  haveI := quotientMap_ker_finite f R
  haveI : Finite (B ⧸ R.map f) := Subgroup.finite_quotient_of_finiteIndex
  exact (MonoidHom.finite_iff_finite_ker_range (quotientMap f R)).mpr ⟨inferInstance, inferInstance⟩

/-- Counting kernel, image and cokernel in the now-finite lower row. -/
theorem quotientMap_card_identity [Finite f.ker] [(R.map f).FiniteIndex] :
    (R.map f).index * Nat.card (quotientMap f R).ker =
      R.index * (quotientMap f R).range.index := by
  haveI := quotientMap_domain_finite f R
  have h1 : Nat.card (quotientMap f R).ker * (quotientMap f R).ker.index = R.index := by
    rw [Subgroup.card_mul_index, Subgroup.index]
  have h2 : (quotientMap f R).ker.index = Nat.card (quotientMap f R).range :=
    Subgroup.index_ker _
  have h3 : Nat.card (quotientMap f R).range * (quotientMap f R).range.index =
      (R.map f).index := by
    rw [Subgroup.card_mul_index, Subgroup.index]
  rw [← h1, ← h3, h2]
  ring

/-- The cleared form of Janusz V.4.1's index diagram formula. -/
theorem quotientMap_index_card [Finite f.ker] [(R.map f).FiniteIndex] :
    (R.map f).index * Nat.card f.ker =
      R.index * f.range.index * Nat.card ↥(f.ker ⊓ R) := by
  rw [quotientMap_ker_card f R, ← quotientMap_range_index f R]
  have h := quotientMap_card_identity f R
  calc (R.map f).index * (Nat.card ↥(f.ker ⊓ R) * Nat.card (quotientMap f R).ker)
      = ((R.map f).index * Nat.card (quotientMap f R).ker) * Nat.card ↥(f.ker ⊓ R) := by ring
    _ = R.index * (quotientMap f R).range.index * Nat.card ↥(f.ker ⊓ R) := by rw [h]

/-- Dividing only by the positive cardinal of the finite upper kernel gives the source formula. -/
theorem quotientMap_index_ratio [Finite f.ker] [(R.map f).FiniteIndex] :
    ((R.map f).index : ℚ) =
      R.index * (f.range.index : ℚ) / Nat.card f.ker * Nat.card ↥(f.ker ⊓ R) := by
  have h := quotientMap_index_card f R
  have hpos : (0 : ℚ) < Nat.card f.ker := by exact_mod_cast Nat.card_pos
  rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hpos.ne']
  exact_mod_cast h.symm

end Cox.QuotientDiagram
