/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldDefs
import XYin.PhD.Cox.Theorem11_1.ChebotarevFrobenius

/-! # A modulus containing all ramified primes

The finite product realizes the finite exceptional set in Janusz III.3, printed103.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory

/-- The finite ramified-prime set gives an actual nonzero modulus containing its support. -/
theorem exists_unramifiedAway_modulus
    (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsGalois K E] :
    ∃ m : Ideal (𝓞 K), m ≠ ⊥ ∧ IsUnramifiedAway K m E := by
  classical
  set S := (Chebotarev.finite_ramifiedIn K E).toFinset with hS
  refine ⟨∏ q ∈ S, q, ?_, ?_⟩
  · rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro q hq
    rw [Ideal.zero_eq_bot]
    exact ((Chebotarev.finite_ramifiedIn K E).mem_toFinset.mp hq).2.1
  · intro q hqp hq0 hcop P hP
    have hunr : Chebotarev.UnramifiedIn K E q := by
      by_contra hram
      have hmem : q ∈ S := (Chebotarev.finite_ramifiedIn K E).mem_toFinset.mpr ⟨hqp, hq0, hram⟩
      have hle : ∏ q' ∈ S, q' ≤ q := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hmem)
      exact hqp.ne_top (by rw [← hcop]; exact le_antisymm le_sup_left (sup_le le_rfl hle))
    haveI := hP.1
    haveI := hP.2
    have h1 := Chebotarev.UnramifiedIn.ramificationIdx_eq_one K E hunr P hP.2
    rwa [← hP.2.over] at h1

end Cox.ClassFieldTheory
