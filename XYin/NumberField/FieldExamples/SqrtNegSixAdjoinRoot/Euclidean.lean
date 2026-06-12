import XYin.NumberField.FieldExamples.SqrtNegSixAdjoinRoot.ClassGroup

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace XYin.NumberField.New.SqrtNegSixAdjoinRoot

/-- `ℤ[√-6]` is *not* a principal ideal domain — the smallest-discriminant imaginary
quadratic examples of class number `2` are `d = -5, -6`. -/
theorem not_isPrincipalIdealRing : ¬ IsPrincipalIdealRing (𝓞 K) := by
  intro hpid
  exact not_isPrincipal_primeAboveTwo (IsPrincipalIdealRing.principal primeAboveTwo)

/-- The ring of integers of `ℚ(√-6)` is not norm-Euclidean. -/
theorem not_normEuclidean :
    ¬ ∀ a b : 𝓞 K, b ≠ 0 →
      ∃ q r : 𝓞 K, a = b * q + r ∧
        (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  intro hE
  obtain ⟨q, r, hr, hlt⟩ := hE thetaInt (2 : 𝓞 K) (by norm_num)
  have hnorm2 : (Algebra.norm ℤ (2 : 𝓞 K)).natAbs = 4 := by
    have h := intNorm_eq_normForm 2 0
    have heq : (2 : 𝓞 K) = (2 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by
      simp
    rw [← heq] at h
    rw [h]
    rfl
  obtain ⟨x, y, hq⟩ := exists_eq_smul_one_add_smul_theta q
  have hr_repr : r = (-2 * x) • (1 : 𝓞 K) + (1 - 2 * y) • thetaInt := by
    have hr' : r = thetaInt - (2 : 𝓞 K) * q := by
      rw [eq_sub_iff_add_eq]
      rw [add_comm]
      exact hr.symm
    rw [hr', hq]
    simp only [zsmul_eq_mul, Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_one,
      Int.cast_ofNat]
    ring
  have hnormr : Algebra.norm ℤ r = (-2 * x) ^ 2 + 6 * (1 - 2 * y) ^ 2 := by
    rw [hr_repr, intNorm_eq_normForm]
  have hyodd : 1 - 2 * y ≠ 0 := by omega
  have hypos : (1 : ℤ) ≤ (1 - 2 * y) ^ 2 := by
    have hsqpos : 0 < (1 - 2 * y) ^ 2 := sq_pos_of_ne_zero hyodd
    omega
  have hnorm_ge : (4 : ℤ) ≤ (-2 * x) ^ 2 + 6 * (1 - 2 * y) ^ 2 := by
    nlinarith [sq_nonneg (-2 * x), hypos]
  have hnonneg : (0 : ℤ) ≤ (-2 * x) ^ 2 + 6 * (1 - 2 * y) ^ 2 := by
    nlinarith [sq_nonneg (-2 * x), sq_nonneg (1 - 2 * y)]
  have hltNat := hlt
  rw [hnorm2, hnormr] at hltNat
  have hltZ : ((-2 * x) ^ 2 + 6 * (1 - 2 * y) ^ 2 : ℤ) < 4 := by
    have hcast :
        ((((-2 * x) ^ 2 + 6 * (1 - 2 * y) ^ 2).natAbs : ℕ) : ℤ) < (4 : ℤ) := by
      exact_mod_cast hltNat
    rw [Int.natAbs_of_nonneg hnonneg] at hcast
    exact hcast
  exact not_lt_of_ge hnorm_ge hltZ


end XYin.NumberField.New.SqrtNegSixAdjoinRoot
