import XYin.NumberField.FieldExamples.CyclotomicFive.Units

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicFive

/-! ## 7. Class group -/

/-- The class number of `ℚ(ζ₅)` is `1` (the Minkowski bound is `(4/π)² · 4!/4⁴ · √125 ≈ 1.7`,
so there is nothing to check beyond the unit ideal). -/
theorem classNumber_eq_one : NumberField.classNumber K = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hp hprime P hPmem _
  have hple : p ≤ 1 := by
    have h2 := (Finset.mem_Icc.mp hp).2
    have h5 : ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        (((Module.finrank ℚ K).factorial : ℝ) /
          ((Module.finrank ℚ K : ℝ)) ^ (Module.finrank ℚ K) *
            Real.sqrt (|NumberField.discr K| : ℝ))⌋₊ < 2 := by
      rw [Nat.floor_lt (by positivity)]
      rw [nrComplexPlaces_eq_two, degree_eq_four, numberField_discr_eq]
      have hsq : Real.sqrt |(125 : ℝ)| < 12 := by
        rw [show |(125 : ℝ)| = (125 : ℝ) by norm_num,
          show (12 : ℝ) = Real.sqrt (12 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have hπ : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
      have hx : (4 / Real.pi) ^ 2 * (((Nat.factorial 4 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) ^ (4 : ℕ) *
          Real.sqrt |((125 : ℤ) : ℝ)|) =
            3 * Real.sqrt |((125 : ℤ) : ℝ)| / (2 * Real.pi ^ 2) := by
        norm_num [Nat.factorial]
        ring
      rw [hx, div_lt_iff₀ (by positivity)]
      push_cast
      nlinarith [hsq, hπ, sq_nonneg (Real.pi - 3.14), Real.sqrt_nonneg |(125 : ℝ)|]
    omega
  have hpge := (Finset.mem_Icc.mp hp).1
  interval_cases p
  exact absurd hprime (by norm_num)

/-- The ring of integers `ℤ[ζ₅]` is a principal ideal domain. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 K) := by
  rw [← NumberField.classNumber_eq_one_iff]
  exact classNumber_eq_one

/-- The class group of `𝓞 K` is trivial. -/
theorem classGroupStructure : Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1)) := by
  have h1 : Nat.card (ClassGroup (𝓞 K)) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup (𝓞 K)) := (Nat.card_eq_one_iff_unique.mp h1).1
  haveI : Unique (ClassGroup (𝓞 K)) := uniqueOfSubsingleton 1
  exact ⟨MulEquiv.ofUnique⟩

/-- The unit ideal as the concrete representative of the unique ideal class. -/
abbrev unitIdealRepresentative : (Ideal (𝓞 K))⁰ := ⟨(⊤ : Ideal (𝓞 K)), by simp⟩

/-- Every ideal class is represented by the unit ideal. -/
theorem classGroupRepresentative (C : ClassGroup (𝓞 K)) :
    C = ClassGroup.mk0 unitIdealRepresentative := by
  have h1 : Nat.card (ClassGroup (𝓞 K)) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup (𝓞 K)) := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim _ _


end NumberField.CyclotomicFive
