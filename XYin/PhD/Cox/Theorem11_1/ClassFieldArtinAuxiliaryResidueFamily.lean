/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryResidueData
import Mathlib.RingTheory.RootsOfUnity.Minpoly

/-!
# A coherent finite family of cyclotomic auxiliary data

Janusz V.5.6, printed162/PDF173, chooses the roots successively so that one common compositum has
the required product of Galois groups. Each selection below uses the whole preceding rational
compositum and the product of the preceding root orders.
-/

open IntermediateField
noncomputable section
namespace Cox.ClassFieldTheory.ArtinAuxiliary

/-- The same finite family preserves every successive cyclotomic exclusion and residue witness. -/
theorem exists_sequential_cyclotomic_residue_family
    {Ω : Type*} [Field Ω] [CharZero Ω]
    (hroots : ∀ m : ℕ, 0 < m → ∃ ξ : Ω, IsPrimitiveRoot ξ m)
    (L : IntermediateField ℚ Ω) [FiniteDimensional ℚ L]
    (r : ℕ) (a : Fin r → ℕ) (ha : ∀ i, 2 ≤ a i)
    (n s : ℕ) (hn : 0 < n) (hs : 0 < s) :
    ∃ (m : Fin r → ℕ) (ξ : Fin r → Ω)
      (u v : ∀ i, (ZMod (m i))ˣ),
      ∀ i, 0 < m i ∧
        (m i).Coprime (s * ∏ j : {j : Fin r // j < i}, m j.1) ∧
        (m i).Coprime (a i) ∧ IsPrimitiveRoot (ξ i) (m i) ∧
        ((L ⊔ ⨆ j : {j : Fin r // j < i}, adjoin ℚ {ξ j.1}) ⊓
          adjoin ℚ {ξ i}) = ⊥ ∧
        (u i : ZMod (m i)) = a i ∧ n ∣ orderOf (u i) ∧ n ∣ orderOf (v i) ∧
        Disjoint (Subgroup.zpowers (u i)) (Subgroup.zpowers (v i)) := by
  classical
  let D := Σ k : ℕ, Ω × (ZMod k)ˣ × (ZMod k)ˣ
  let Good : (i : Fin r) → ({j : Fin r // j < i} → D) → D → Prop := fun i p x =>
    0 < x.1 ∧ x.1.Coprime (s * ∏ j : {j : Fin r // j < i}, (p j).1) ∧ x.1.Coprime (a i) ∧
      IsPrimitiveRoot x.2.1 x.1 ∧
      ((L ⊔ ⨆ j : {j : Fin r // j < i}, adjoin ℚ {(p j).2.1}) ⊓ adjoin ℚ {x.2.1}) = ⊥ ∧
      ((x.2.2.1 : ZMod x.1) = a i) ∧ n ∣ orderOf x.2.2.1 ∧ n ∣ orderOf x.2.2.2 ∧
      Disjoint (Subgroup.zpowers x.2.2.1) (Subgroup.zpowers x.2.2.2)
  have key : ∀ k ≤ r, ∃ d : Fin r → D,
      ∀ i : Fin r, i.val < k → Good i (fun j => d j.1) (d i) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun _ => ⟨1, 1, 1, 1⟩, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨d, hd⟩ := ih (Nat.le_of_succ_le hk)
      have hprev : ∀ j : {j : Fin r // j < (⟨k, hk⟩ : Fin r)},
          Good j.1 (fun l => d l.1) (d j.1) := fun j => hd j.1 j.2
      haveI : ∀ j : {j : Fin r // j < (⟨k, hk⟩ : Fin r)},
          FiniteDimensional ℚ (adjoin ℚ {(d j.1).2.1}) := fun j =>
        CyclotomicIntersection.finiteDimensional_adjoin_root _ (hprev j).1 _ (hprev j).2.2.2.1
      haveI : Finite (IntermediateField ℚ
          ↥(L ⊔ ⨆ j : {j : Fin r // j < (⟨k, hk⟩ : Fin r)}, adjoin ℚ {(d j.1).2.1})) :=
        CyclotomicCapture.finite_intermediateFields_of_finite_separable ℚ _
      have hs' : 0 < s * ∏ j : {j : Fin r // j < (⟨k, hk⟩ : Fin r)}, (d j.1).1 :=
        Nat.mul_pos hs (Finset.prod_pos fun j _ => (hprev j).1)
      obtain ⟨m', ξ', hm', hcs, hca, hξ', hint, u', v', hu', hnu, hnv, hind⟩ :=
        exists_cyclotomic_residue_data hroots
          (L ⊔ ⨆ j : {j : Fin r // j < (⟨k, hk⟩ : Fin r)}, adjoin ℚ {(d j.1).2.1})
          (a ⟨k, hk⟩) n (s * ∏ j : {j : Fin r // j < (⟨k, hk⟩ : Fin r)}, (d j.1).1)
          (ha ⟨k, hk⟩) hn hs'
      let x : D := ⟨m', ξ', u', v'⟩
      have hx : Good ⟨k, hk⟩ (fun j => d j.1) x := ⟨hm', hcs, hca, hξ', hint, hu', hnu, hnv, hind⟩
      refine ⟨Function.update d ⟨k, hk⟩ x, fun i hi => ?_⟩
      have hpre : ∀ i : Fin r, i.val ≤ k →
          (fun j : {j : Fin r // j < i} => Function.update d ⟨k, hk⟩ x j.1) =
            (fun j => d j.1) := by
        intro i hi'
        funext j
        apply Function.update_of_ne
        intro h
        have h1 : (j.1 : Fin r).val < i.val := j.2
        rw [h] at h1
        change k < i.val at h1
        omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · have hne : i ≠ ⟨k, hk⟩ := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
        change Good i (fun j : {j : Fin r // j < i} => Function.update d ⟨k, hk⟩ x j.1)
          (Function.update d ⟨k, hk⟩ x i)
        rw [hpre i hlt.le, Function.update_of_ne hne]
        exact hd i hlt
      · obtain rfl : i = ⟨k, hk⟩ := Fin.ext heq
        change Good ⟨k, hk⟩
          (fun j : {j : Fin r // j < (⟨k, hk⟩ : Fin r)} => Function.update d ⟨k, hk⟩ x j.1)
          (Function.update d ⟨k, hk⟩ x ⟨k, hk⟩)
        rw [hpre ⟨k, hk⟩ le_rfl, Function.update_self]
        exact hx
  obtain ⟨d, hd⟩ := key r le_rfl
  exact ⟨fun i => (d i).1, fun i => (d i).2.1, fun i => (d i).2.2.1, fun i => (d i).2.2.2,
    fun i => hd i i.2⟩

end Cox.ClassFieldTheory.ArtinAuxiliary
