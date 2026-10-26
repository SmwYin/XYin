/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArithmetic
import XYin.PhD.Cox.Theorem11_1.ClassFieldRayAnalytic

/-! # Janusz IV.5.6: the first norm-index inequality

The proof uses complete-split density and the independent congruence-subgroup
prime-density upper bound in IV.4.7.
-/

open NumberField
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]
variable (m : Ideal (𝓞 K)) (L : Type*) [Field L] [NumberField L] [Algebra K L]
variable [Module.Finite (𝓞 K) (𝓞 L)]

/-- Good complete-split primes retain the inverse-degree density. -/
theorem density_splittingIdeals_away_modulus [IsGalois K L] (hm : m ≠ ⊥) :
    Chebotarev.HasDirichletDensity {q : Ideal (𝓞 K) | q ∈ splittingIdeals K L ∧ q ⊔ m = ⊤}
      (1 / (Module.finrank K L : ℝ)) := by
  set G := {q : Ideal (𝓞 K) | q ∈ splittingIdeals K L ∧ q ⊔ m = ⊤} with hG
  set B := {q : Ideal (𝓞 K) | q ∈ splittingIdeals K L ∧ ¬ q ⊔ m = ⊤} with hB
  have hsplit : splittingIdeals K L = G ∪ B := by
    ext q
    simp only [hG, hB, Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hdisj : Disjoint G B := Set.disjoint_left.mpr fun q hqG hqB => hqB.2 hqG.2
  have hBfin : B.Finite := by
    refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (Ideal.absNorm m)).subset ?_
    rintro q ⟨⟨hqp, hq0, -⟩, hqm⟩
    have hmq : m ≤ q := by
      by_contra hle
      haveI hqmax := hqp.isMaximal hq0
      exact hqm (hqmax.out.2 _ (lt_of_le_of_ne le_sup_left
        (fun h => hle (le_sup_right.trans (le_of_eq h.symm)))))
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero fun h => hm (Ideal.absNorm_eq_zero_iff.mp h))
      (Ideal.absNorm_dvd_absNorm_of_le hmq)
  have hD := density_splittingIdeals K L
  rw [hsplit] at hD
  have hB0 := Chebotarev.hasDirichletDensity_of_finite K hBfin
  unfold Chebotarev.HasDirichletDensity at hD hB0 ⊢
  have hsub := hD.sub hB0
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Chebotarev.primeIdealZetaSum_union_of_disjoint K hdisj hs, add_div, add_sub_cancel_right]

/-- A good split prime is itself an ideal norm, hence belongs to the norm-and-ray subgroup. -/
theorem splittingIdeals_away_subset_normRay :
    {q : Ideal (𝓞 K) | q ∈ splittingIdeals K L ∧ q ⊔ m = ⊤} ⊆
      primesInCongruenceSubgroup K m (normRaySubgroup K m L) := by
  rintro q ⟨hq, hqm⟩
  obtain ⟨u, hu⟩ := exists_coprimeIdealUnit K m q hq.2.1 hqm
  refine ⟨hq.1, hq.2.1, hqm, u, hu, ?_⟩
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_sup_left (mem_normImage_of_splits K m L hq hqm u hu)

/-- The first fundamental inequality used in Janusz V.5.1. -/
theorem normRaySubgroup_index_le [IsGalois K L] (hm : m ≠ ⊥) :
    (normRaySubgroup K m L).index ≤ Module.finrank K L := by
  haveI : (normRaySubgroup K m L).FiniteIndex :=
    finiteIndex_of_raySubgroup_le K m hm _ le_sup_right
  have hle := density_le_inv_index_of_subset_congruence K m (normRaySubgroup K m L) hm
    le_sup_right (splittingIdeals_away_subset_normRay K m L)
    (density_splittingIdeals_away_modulus K m L hm)
  have hn : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have hh : (0 : ℝ) < (normRaySubgroup K m L).index := by
    exact_mod_cast Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  exact_mod_cast (one_div_le_one_div hn hh).mp hle

end Cox.ClassFieldTheory
