/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealGroups

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The finite ideal product after deleting every modulus-prime coordinate. -/
def awayIdealProduct (m : Ideal (𝓞 K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  exponentIdealProduct K ((idealExponentVector K I).filter (fun v => ¬m ≤ v.asIdeal))

open scoped Classical in
/-- Prime counts of the projected product. -/
theorem count_awayIdealProduct (m : Ideal (𝓞 K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (awayIdealProduct K m I) =
      if m ≤ v.asIdeal then 0 else FractionalIdeal.count K v I := by
  rw [awayIdealProduct, count_exponentIdealProduct, Finsupp.filter_apply,
    idealExponentVector_apply]
  by_cases h : m ≤ v.asIdeal <;> simp [h]

/-- The projected product is prime to its modulus. -/
theorem awayIdealProduct_mem_coprime (m : Ideal (𝓞 K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    awayIdealProduct K m I ∈ coprimeIdeals K m := by
  classical
  rw [mem_coprimeIdeals_iff_count_eq_zero]
  intro p hp
  rw [count_awayIdealProduct, if_pos hp]

/-- Deleting prime coordinates respects multiplication. -/
theorem awayIdealProduct_mul (m : Ideal (𝓞 K)) (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    awayIdealProduct K m (I*J) = awayIdealProduct K m I * awayIdealProduct K m J := by
  classical
  rw [awayIdealProduct, awayIdealProduct, awayIdealProduct, idealExponentVector_mul,
    Finsupp.filter_add, exponentIdealProduct_add]

/-- The removed factor is supported on the modulus primes. -/
theorem awayIdealProduct_quotient_mem (m : Ideal (𝓞 K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    I * (awayIdealProduct K m I)⁻¹ ∈ modulusSupportedIdeals K m := by
  classical
  rw [mem_modulusSupportedIdeals_iff_count_eq_zero]
  intro p hp
  rw [Units.val_mul, FractionalIdeal.count_mul K p I.ne_zero (awayIdealProduct K m I)⁻¹.ne_zero,
    Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, count_awayIdealProduct, if_neg hp,
    add_neg_cancel]

/-- Unique ideal factorization removes the factors belonging to a prescribed modulus. -/
theorem exists_eraseModulusFactors (m : Ideal (𝓞 K)) :
    ∃ j : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* coprimeIdeals K m,
      ∀ I, I * (j I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹ ∈ modulusSupportedIdeals K m := by
  exact ⟨(MonoidHom.mk' (awayIdealProduct K m) (awayIdealProduct_mul K m)).codRestrict
    (coprimeIdeals K m) (awayIdealProduct_mem_coprime K m),
    fun I => awayIdealProduct_quotient_mem K m I⟩

/-- The source's ideal projection `j`, chosen from its prime-factor decomposition. -/
def eraseModulusFactors (m : Ideal (𝓞 K)) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* coprimeIdeals K m :=
  Classical.choose (exists_eraseModulusFactors K m)

/-- Removing the modulus factors leaves a quotient supported only at those factors. -/
theorem eraseModulusFactors_spec (m : Ideal (𝓞 K))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    I * (eraseModulusFactors K m I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹ ∈
      modulusSupportedIdeals K m := by
  exact Classical.choose_spec (exists_eraseModulusFactors K m) I

/-- The source projection j fixes each ideal already prime to the modulus. -/
theorem eraseModulusFactors_coprime (m : Ideal (𝓞 K)) (u : coprimeIdeals K m) :
    eraseModulusFactors K m (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = u := by
  have h1 := eraseModulusFactors_spec K m u
  have h2 : (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) *
      (eraseModulusFactors K m u : (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹ ∈ coprimeIdeals K m :=
    Subgroup.mul_mem _ u.2 (Subgroup.inv_mem _ (eraseModulusFactors K m u).2)
  have h3 : (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) *
      (eraseModulusFactors K m u : (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹ ∈
        modulusSupportedIdeals K m ⊓ coprimeIdeals K m := Subgroup.mem_inf.mpr ⟨h1, h2⟩
  rw [modulusSupportedIdeals_inf_coprime, Subgroup.mem_bot, mul_inv_eq_one] at h3
  exact Subtype.ext h3.symm

/-- The source projection j kills ideals supported on the modulus primes. -/
theorem eraseModulusFactors_supported (m : Ideal (𝓞 K))
    (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hu : u ∈ modulusSupportedIdeals K m) :
    eraseModulusFactors K m u = 1 := by
  have h1 := eraseModulusFactors_spec K m u
  have h2 : (eraseModulusFactors K m u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈
      modulusSupportedIdeals K m := by
    have h : (eraseModulusFactors K m u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        (u * (eraseModulusFactors K m u : (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹)⁻¹ * u := by
      group
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) hu
  have h3 : (eraseModulusFactors K m u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈
      modulusSupportedIdeals K m ⊓ coprimeIdeals K m :=
    Subgroup.mem_inf.mpr ⟨h2, (eraseModulusFactors K m u).2⟩
  rw [modulusSupportedIdeals_inf_coprime, Subgroup.mem_bot] at h3
  exact Subtype.ext h3

/-- The kernel of the actual chosen erasure is exactly the supported ideal subgroup. -/
theorem eraseModulusFactors_eq_one_iff (m : Ideal (𝓞 K))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    eraseModulusFactors K m I = 1 ↔ I ∈ modulusSupportedIdeals K m := by
  constructor
  · intro h
    have h1 := eraseModulusFactors_spec K m I
    rwa [h, OneMemClass.coe_one, inv_one, mul_one] at h1
  · exact eraseModulusFactors_supported K m I

end Cox.ClassFieldTheory
