/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.FieldTheory.Galois.Abelian

/-! # The cyclic factors in Janusz V.5.7

The same finite family has cyclic quotients and separates elements.
-/

noncomputable section
namespace Cox.ClassFieldTheory

/-- A finite abelian group has a finite separating family of cyclic quotients. -/
theorem exists_cyclic_quotients_iInf_eq_bot (G : Type*) [CommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (H : ι → Subgroup G),
      (∀ i, IsCyclic (G ⧸ H i)) ∧ iInf H = ⊥ := by
  obtain ⟨ι, hι, n, -, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  let f : ∀ i, G →* Multiplicative (ZMod (n i)) := fun i =>
    (Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i).comp e.toMonoidHom
  refine ⟨ι, hι, fun i => (f i).ker, fun i => ?_, ?_⟩
  · exact (QuotientGroup.quotientKerEquivRange (f i)).isCyclic.mpr inferInstance
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_iInf] at hg
    rw [Subgroup.mem_bot]
    apply e.injective
    rw [map_one]
    funext i
    exact MonoidHom.mem_ker.mp (hg i)

open scoped IsMulCommutative in
/-- A finite abelian extension has cyclic intermediate fields with trivial common fixer. -/
theorem exists_cyclic_subfields_iInf_fixing_eq_bot (K L : Type*)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] :
    ∃ (ι : Type) (_ : Fintype ι) (E : ι → IntermediateField K L),
      (∀ i, IsCyclic (E i ≃ₐ[K] E i)) ∧ (⨅ i, (E i).fixingSubgroup) = ⊥ := by
  obtain ⟨ι, hι, H, hcyc, hbot⟩ := exists_cyclic_quotients_iInf_eq_bot Gal(L/K)
  refine ⟨ι, hι, fun i => IntermediateField.fixedField (H i), fun i => ?_, ?_⟩
  · exact (IsGalois.normalAutEquivQuotient (H i)).isCyclic.mp (hcyc i)
  · simp_rw [IntermediateField.fixingSubgroup_fixedField]
    exact hbot

end Cox.ClassFieldTheory
