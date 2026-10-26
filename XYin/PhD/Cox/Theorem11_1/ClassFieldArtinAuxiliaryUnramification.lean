/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryCore
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicBaseChange
import Mathlib.Order.CompleteLattice.Finset

/-!
# Unramification in the actual auxiliary compositum

Janusz III.3, printed104/PDF115, and V.5.4–5.6, printed160–162/PDF171–173, use coprime-order
cyclotomic extensions and a finite family of chosen roots. These contracts repeatedly adjoin those
same roots to the actual prefix.
-/

open IntermediateField NumberField
noncomputable section
namespace Cox.ClassFieldTheory.ArtinAuxiliary
open Cox.Chebotarev

/-- Janusz III.3, p104, and V.5.4–5.6, pp160–162: adjoining the same
coprime-order root to the actual prefix preserves unramification. -/
theorem unramifiedIn_sup_rootField
    {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [NumberField L]
    (m : ℕ) (hm : 0 < m) (ξ : Ω) (hξ : IsPrimitiveRoot ξ m)
    (q : Ideal (𝓞 K)) [q.IsPrime] (hU : UnramifiedIn K L q)
    (hcop : q.absNorm.Coprime m) :
    UnramifiedIn K ↥(L ⊔ adjoin K {ξ} : IntermediateField K Ω) q := by
  have transport : ∀ X Y : IntermediateField K Ω, X = Y →
      UnramifiedIn K X q → UnramifiedIn K Y q := by
    rintro X Y rfl h
    exact h
  letI : NeZero m := ⟨hm.ne'⟩
  haveI := CyclotomicBaseChange.rootField_isCyclotomic (F := L) m hm ξ hξ
  haveI : FiniteDimensional L (adjoin L {ξ}) :=
    CyclotomicIntersection.finiteDimensional_adjoin_root (F := L) m hm ξ hξ
  haveI : NumberField (adjoin L {ξ}) := NumberField.of_module_finite L (adjoin L {ξ})
  have h1 : UnramifiedIn K (adjoin L {ξ}) q :=
    unramifiedIn_cyclotomic_tower K L (adjoin L {ξ}) m q hU hcop
  have h2 : UnramifiedIn K ((adjoin L {ξ}).restrictScalars K) q := h1
  exact transport _ _ (IntermediateField.restrictScalars_adjoin_eq_sup K L {ξ}) h2

/-- Janusz V.5.6, p162: repeat the coprime cyclotomic step in the actual finite
compositum. Every root order is required to be coprime to this prime norm. -/
theorem unramifiedIn_sup_iSup_rootField
    {K Ω ι : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [Finite ι] (L : IntermediateField K Ω) [NumberField L]
    (m : ι → ℕ) (ξ : ι → Ω)
    (hm : ∀ i, 0 < m i) (hξ : ∀ i, IsPrimitiveRoot (ξ i) (m i))
    (q : Ideal (𝓞 K)) [q.IsPrime] (hU : UnramifiedIn K L q)
    (hcop : ∀ i, q.absNorm.Coprime (m i)) :
    UnramifiedIn K ↥(L ⊔ ⨆ i, adjoin K {ξ i} : IntermediateField K Ω) q := by
  classical
  haveI := Fintype.ofFinite ι
  have transport : ∀ X Y : IntermediateField K Ω, X = Y →
      UnramifiedIn K X q → UnramifiedIn K Y q := by
    rintro X Y rfl h
    exact h
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI hfin : ∀ i, FiniteDimensional K (adjoin K {ξ i}) := fun i =>
    CyclotomicIntersection.finiteDimensional_adjoin_root (F := K) (m i) (hm i) (ξ i) (hξ i)
  have key : ∀ s : Finset ι,
      UnramifiedIn K ↥(L ⊔ ⨆ i ∈ s, adjoin K {ξ i} : IntermediateField K Ω) q := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact transport L _ (by simp) hU
    | insert a s ha ih =>
      haveI : NumberField ↥(L ⊔ ⨆ i ∈ s, adjoin K {ξ i} : IntermediateField K Ω) :=
        NumberField.of_module_finite K _
      have h := unramifiedIn_sup_rootField (L ⊔ ⨆ i ∈ s, adjoin K {ξ i}) (m a) (hm a) (ξ a)
        (hξ a) q ih (hcop a)
      refine transport _ _ ?_ h
      rw [Finset.iSup_insert, sup_assoc, sup_comm (⨆ i ∈ s, adjoin K {ξ i})]
  exact transport _ _ (by simp) (key Finset.univ)

end Cox.ClassFieldTheory.ArtinAuxiliary
