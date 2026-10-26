/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealGroups

/-! # Integral quotients in the good-ideal group

These four existing interfaces are lowered from Descent for the ideal norm calculation
in Janusz III.3.1. Public names and carriers are preserved; all theorem bodies remain sorries.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [hNF : NumberField K]

/-- Janusz V.7.2 uses quotients of integral ideals in each prime-to-modulus group. -/
theorem quotient_of_mem_closure {G : Type*} [CommGroup G] (S : Set G)
    (h1 : 1 ∈ S) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    {u : G} (hu : u ∈ Subgroup.closure S) :
    ∃ a ∈ S, ∃ b ∈ S, u = a / b := by
  induction hu using Subgroup.closure_induction with
  | mem x hx => exact ⟨x, hx, 1, h1, (div_one x).symm⟩
  | one => exact ⟨1, h1, 1, h1, (div_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨c, hc, d, hd, rfl⟩ := hy
    exact ⟨a * c, hmul a ha c hc, b * d, hmul b hb d hd, div_mul_div_comm a b c d⟩
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨b, hb, a, ha, inv_div a b⟩

/-- The integral unit ideal is prime to every finite modulus. -/
theorem one_mem_coprimeGenerators (m : Ideal (𝓞 K)) :
    1 ∈ coprimeGenerators K m := by
  refine ⟨⊤, top_ne_bot, top_sup_eq m, ?_⟩
  rw [Units.val_one, FractionalIdeal.coeIdeal_top]

/-- Product preserves integrality, nonzeroness, and prime-to-modulus status. -/
theorem mul_mem_coprimeGenerators (m : Ideal (𝓞 K))
    {u v : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hu : u ∈ coprimeGenerators K m) (hv : v ∈ coprimeGenerators K m) :
    u * v ∈ coprimeGenerators K m := by
  obtain ⟨A, hA0, hAm, hAu⟩ := hu
  obtain ⟨B, hB0, hBm, hBv⟩ := hv
  refine ⟨A * B, mul_ne_zero hA0 hB0, ?_, ?_⟩
  · rw [Ideal.mul_sup_eq_of_coprime_left hAm, hBm]
  · rw [Units.val_mul, hAu, hBv, FractionalIdeal.coeIdeal_mul]

/-- The source's fractional ideals have good integral numerator and denominator. -/
theorem exists_coprime_ideal_quotient (m : Ideal (𝓞 K)) (u : coprimeIdeals K m) :
    ∃ A B : Ideal (𝓞 K), A ≠ ⊥ ∧ B ≠ ⊥ ∧ A ⊔ m = ⊤ ∧ B ⊔ m = ⊤ ∧
      ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) * B = A := by
  obtain ⟨a, ⟨A, hA0, hAm, hAa⟩, b, ⟨B, hB0, hBm, hBb⟩, hu⟩ :=
    quotient_of_mem_closure (coprimeGenerators K m) (one_mem_coprimeGenerators K m)
      (fun a ha b hb => mul_mem_coprimeGenerators K m ha hb) u.2
  refine ⟨A, B, hA0, hB0, hAm, hBm, ?_⟩
  rw [← hAa, ← hBb, hu, ← Units.val_mul, div_mul_cancel]

end Cox.ClassFieldTheory
