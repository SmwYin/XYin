import XYin.NumberField.FieldExamples.SqrtNegSix.Units

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace NumberField.SqrtNegSix


/-! ## 7. Class group -/

/-- The ramified prime `(2, θ)` as an element of the monoid of nonzero ideals: the concrete
representative of the nontrivial ideal class. -/
noncomputable def ramifiedIdealOverTwo : (Ideal (𝓞 K))⁰ :=
  ⟨primeAboveTwo, by
    rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors]
    rw [absNorm_primeAboveTwo]
    norm_num⟩

/-- The ramified prime `(3, θ)` as a nonzero ideal. Its class equals the class of
`ramifiedIdealOverTwo`. -/
noncomputable def ramifiedIdealOverThree : (Ideal (𝓞 K))⁰ :=
  ⟨primeAboveThree, by
    rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors]
    rw [absNorm_primeAboveThree]
    norm_num⟩

/-- The unit ideal as the representative of the trivial ideal class. -/
abbrev unitIdealRepresentative : (Ideal (𝓞 K))⁰ := ⟨(⊤ : Ideal (𝓞 K)), by simp⟩

private theorem thetaInt_ne_zero : thetaInt ≠ 0 := by
  intro hθ0
  have hθK : (θ : K) = 0 := congrArg Subtype.val hθ0
  have hsq := theta_sq
  rw [hθK] at hsq
  norm_num at hsq

private theorem minkowskiBound_lt_four :
    (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        (((Module.finrank ℚ K).factorial : ℝ) /
          ((Module.finrank ℚ K : ℝ)) ^ (Module.finrank ℚ K) *
            Real.sqrt (|NumberField.discr K| : ℝ)) < 4 := by
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
    have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [nrRealPlaces_eq_zero, degree_eq_two] at h
    omega
  rw [hcomplex, degree_eq_two, numberField_discr_eq]
  have hsq : Real.sqrt |((-24 : ℤ) : ℝ)| < 5 := by
    rw [show |((-24 : ℤ) : ℝ)| = (24 : ℝ) by norm_num,
      show (5 : ℝ) = Real.sqrt (5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hx : (4 / Real.pi) ^ 1 *
      (((Nat.factorial 2 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) ^ (2 : ℕ) *
        Real.sqrt |((-24 : ℤ) : ℝ)|) = 2 * Real.sqrt |((-24 : ℤ) : ℝ)| / Real.pi := by
    rw [pow_one]
    norm_num [Nat.factorial]
    ring
  rw [hx, div_lt_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_three]

/-- The ramified prime over `2` represents the nontrivial ideal class. -/
theorem classGroup_mk0_ramified_ne_one :
    ClassGroup.mk0 ramifiedIdealOverTwo ≠ 1 := by
  intro h
  have hprincipal : (ramifiedIdealOverTwo : Ideal (𝓞 K)).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem ramifiedIdealOverTwo)]
    exact h
  exact not_isPrincipal_primeAboveTwo (by simpa [ramifiedIdealOverTwo] using hprincipal)

/-- The square of the ramified class is trivial, since `(2, θ)^2 = (2)`. -/
theorem classGroup_mk0_ramified_sq_eq_one :
    ClassGroup.mk0 ramifiedIdealOverTwo ^ 2 = 1 := by
  rw [pow_two]
  have hP2self : ClassGroup.mk0 ramifiedIdealOverTwo =
      (ClassGroup.mk0 ramifiedIdealOverTwo)⁻¹ := by
    rw [ClassGroup.mk0_eq_mk0_inv_iff]
    refine ⟨(2 : 𝓞 K), by norm_num, ?_⟩
    simpa [ramifiedIdealOverTwo, sq] using span_two_eq.symm
  nth_rewrite 2 [hP2self]
  exact mul_inv_cancel _

/-- The ramified prime over `2` has order `2` in the class group. -/
theorem orderOf_classGroup_mk0_ramified :
    orderOf (ClassGroup.mk0 ramifiedIdealOverTwo) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime classGroup_mk0_ramified_sq_eq_one
    classGroup_mk0_ramified_ne_one

/-- The two ramified primes over `2` and `3` represent the same ideal class. -/
theorem class_mk0_primeAboveThree_eq_ramified :
    ClassGroup.mk0 ramifiedIdealOverThree = ClassGroup.mk0 ramifiedIdealOverTwo := by
  have hP2self : ClassGroup.mk0 ramifiedIdealOverTwo =
      (ClassGroup.mk0 ramifiedIdealOverTwo)⁻¹ := by
    rw [ClassGroup.mk0_eq_mk0_inv_iff]
    refine ⟨(2 : 𝓞 K), by norm_num, ?_⟩
    simpa [ramifiedIdealOverTwo, sq] using span_two_eq.symm
  have hP2P3 : ClassGroup.mk0 ramifiedIdealOverTwo =
      (ClassGroup.mk0 ramifiedIdealOverThree)⁻¹ := by
    rw [ClassGroup.mk0_eq_mk0_inv_iff]
    exact ⟨thetaInt, thetaInt_ne_zero, by
      simpa [ramifiedIdealOverTwo, ramifiedIdealOverThree] using span_theta_eq.symm⟩
  calc
    ClassGroup.mk0 ramifiedIdealOverThree
        = ((ClassGroup.mk0 ramifiedIdealOverThree)⁻¹)⁻¹ := by simp
    _ = (ClassGroup.mk0 ramifiedIdealOverTwo)⁻¹ := by rw [← hP2P3]
    _ = ClassGroup.mk0 ramifiedIdealOverTwo := by rw [← hP2self]

private theorem classGroupRepresentatives_aux (C : ClassGroup (𝓞 K)) :
    C = 1 ∨ C = ClassGroup.mk0 ramifiedIdealOverTwo := by
  obtain ⟨I, hIC, hIle⟩ := NumberField.exists_ideal_in_class_of_norm_le (K := K) C
  have hnormlt4 : (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) < 4 :=
    lt_of_le_of_lt hIle minkowskiBound_lt_four
  have hnormle3 : Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 3 := by
    exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp hnormlt4)
  have hnormpos : 0 < Ideal.absNorm (I : Ideal (𝓞 K)) :=
    Ideal.absNorm_pos_of_nonZeroDivisors I
  set n := Ideal.absNorm (I : Ideal (𝓞 K)) with hn
  have hnpos : 0 < n := by simpa [hn] using hnormpos
  have hnle3 : n ≤ 3 := by simpa [hn] using hnormle3
  interval_cases n
  · have hI1 : Ideal.absNorm (I : Ideal (𝓞 K)) = 1 := by simpa using hn.symm
    left
    rw [← hIC]
    exact (ClassGroup.mk0_eq_one_iff (SetLike.coe_mem I)).mpr (by
      rw [Ideal.absNorm_eq_one_iff.mp hI1]
      exact top_isPrincipal)
  · have hI2 : Ideal.absNorm (I : Ideal (𝓞 K)) = 2 := by simpa using hn.symm
    right
    rw [← hIC]
    have hEq : (I : Ideal (𝓞 K)) = primeAboveTwo :=
      ideal_eq_primeAboveTwo_of_absNorm_eq_two (I : Ideal (𝓞 K)) hI2
    have hIeq : I = ramifiedIdealOverTwo := Subtype.ext hEq
    simp [hIeq]
  · have hI3 : Ideal.absNorm (I : Ideal (𝓞 K)) = 3 := by simpa using hn.symm
    right
    rw [← hIC]
    have hEq : (I : Ideal (𝓞 K)) = primeAboveThree :=
      ideal_eq_primeAboveThree_of_absNorm_eq_three (I : Ideal (𝓞 K)) hI3
    have hIeq : I = ramifiedIdealOverThree := Subtype.ext hEq
    calc
      ClassGroup.mk0 I = ClassGroup.mk0 ramifiedIdealOverThree := by
        simp [hIeq]
      _ = ClassGroup.mk0 ramifiedIdealOverTwo := class_mk0_primeAboveThree_eq_ramified

/-- **The class number of `ℚ(√-6)` is `2`**: the Minkowski bound is `(2/π)√24 ≈ 3.12`, the
primes `2` and `3` below it generate the class group, and their classes coincide and are
nontrivial (`(2,θ)(3,θ) = (θ)` is principal while `(2, θ)` is not). -/
theorem classNumber_eq_two : NumberField.classNumber K = 2 := by
  have hcard : Nat.card (ClassGroup (𝓞 K)) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ClassGroup.mk0 ramifiedIdealOverTwo, ?_, ?_⟩
    · intro h
      exact classGroup_mk0_ramified_ne_one h.symm
    · ext C
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact classGroupRepresentatives_aux C
  simpa [NumberField.classNumber, Nat.card_eq_fintype_card] using hcard

/-- The class group of `𝓞 K` is cyclic of order `2`. -/
theorem classGroupStructure : Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 2)) := by
  have hcard : Nat.card (ClassGroup (𝓞 K)) = 2 := by
    simpa [NumberField.classNumber, Nat.card_eq_fintype_card] using classNumber_eq_two
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨mulEquivOfPrimeCardEq hcard (by
    rw [show Nat.card (Multiplicative (ZMod 2)) = Nat.card (ZMod 2) from rfl, Nat.card_zmod])⟩

/-- The class of the ramified prime `(2, θ)` is nontrivial in the class group. -/
theorem classGroup_mk0_ramified_ne :
    ClassGroup.mk0 ramifiedIdealOverTwo ≠ ClassGroup.mk0 unitIdealRepresentative := by
  intro h
  have hprincipal : (ramifiedIdealOverTwo : Ideal (𝓞 K)).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem ramifiedIdealOverTwo)]
    rw [h]
    rw [ClassGroup.mk0_eq_one_iff (SetLike.coe_mem unitIdealRepresentative)]
    infer_instance
  exact not_isPrincipal_primeAboveTwo (by simpa [ramifiedIdealOverTwo] using hprincipal)

/-- Every ideal class is represented by either `𝓞 K` or the ramified prime `(2, θ)`. -/
theorem classGroupRepresentatives (C : ClassGroup (𝓞 K)) :
    C = ClassGroup.mk0 unitIdealRepresentative ∨ C = ClassGroup.mk0 ramifiedIdealOverTwo := by
  have hcard : Nat.card (ClassGroup (𝓞 K)) = 2 := by
    simpa [NumberField.classNumber, Nat.card_eq_fintype_card] using classNumber_eq_two
  obtain ⟨y, _hy_ne, hy_unique⟩ :=
    (Nat.card_eq_two_iff' (ClassGroup.mk0 unitIdealRepresentative)).mp hcard
  have hram_eq : ClassGroup.mk0 ramifiedIdealOverTwo = y :=
    hy_unique (ClassGroup.mk0 ramifiedIdealOverTwo) classGroup_mk0_ramified_ne
  by_cases hC : C = ClassGroup.mk0 unitIdealRepresentative
  · exact Or.inl hC
  · exact Or.inr ((hy_unique C hC).trans hram_eq.symm)

end NumberField.SqrtNegSix
