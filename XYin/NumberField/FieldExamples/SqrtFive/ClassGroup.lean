import XYin.NumberField.FieldExamples.SqrtFive.Units

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace XYin.NumberField.SqrtFive

/-! ## 7. Class group -/

/-- The class number of `ℚ(√5)` is `1`. The Minkowski bound is `(1/2)·√5 ≈ 1.12 < 2`, so
every ideal class contains an ideal of norm `1` and the class group is trivial outright. -/
theorem classNumber_eq_one : NumberField.classNumber QSqrtFive = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hp hprime P hPmem _
  have hple : p ≤ 1 := by
    have h2 := (Finset.mem_Icc.mp hp).2
    have h5 : ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces QSqrtFive *
        (((Module.finrank ℚ QSqrtFive).factorial : ℝ) /
          ((Module.finrank ℚ QSqrtFive : ℝ)) ^ (Module.finrank ℚ QSqrtFive) *
            Real.sqrt (|NumberField.discr QSqrtFive| : ℝ))⌋₊ < 2 := by
      rw [Nat.floor_lt (by positivity)]
      rw [nrComplexPlaces_eq_zero, degree_eq_two, numberField_discr_eq]
      have hsq : Real.sqrt |(5 : ℝ)| < 3 := by
        rw [show |(5 : ℝ)| = (5 : ℝ) by norm_num,
          show (3 : ℝ) = Real.sqrt (3 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have hx : (4 / Real.pi) ^ 0 * (((Nat.factorial 2 : ℕ) : ℝ) /
          ((2 : ℕ) : ℝ) ^ (2 : ℕ) * Real.sqrt |((5 : ℤ) : ℝ)|) =
          Real.sqrt |(5 : ℝ)| / 2 := by
        norm_num [Nat.factorial]
        ring
      rw [hx, Nat.cast_ofNat]
      set s := Real.sqrt |(5 : ℝ)| with hs
      linarith [hsq]
    omega
  have hpge := (Finset.mem_Icc.mp hp).1
  interval_cases p
  exact absurd hprime (by norm_num)

/-- The ring of integers `ℤ[φ]` is a principal ideal domain — the ring-theoretic content of
class number one. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 QSqrtFive) := by
  rw [← NumberField.classNumber_eq_one_iff]
  exact classNumber_eq_one

/-- The class group of `𝓞 K` is trivial. -/
theorem classGroupStructure :
    Nonempty (ClassGroup (𝓞 QSqrtFive) ≃* Multiplicative (ZMod 1)) := by
  have h1 : Nat.card (ClassGroup (𝓞 QSqrtFive)) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup (𝓞 QSqrtFive)) := (Nat.card_eq_one_iff_unique.mp h1).1
  haveI : Unique (ClassGroup (𝓞 QSqrtFive)) := uniqueOfSubsingleton 1
  exact ⟨MulEquiv.ofUnique⟩

/-- The unit ideal as the concrete representative of the unique ideal class. -/
abbrev unitIdealRepresentative : (Ideal (𝓞 QSqrtFive))⁰ :=
  ⟨(⊤ : Ideal (𝓞 QSqrtFive)), by simp⟩

/-- Every ideal class is represented by the unit ideal. -/
theorem classGroupRepresentative (C : ClassGroup (𝓞 QSqrtFive)) :
    C = ClassGroup.mk0 unitIdealRepresentative := by
  have h1 : Nat.card (ClassGroup (𝓞 QSqrtFive)) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup (𝓞 QSqrtFive)) := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim _ _


end XYin.NumberField.SqrtFive
