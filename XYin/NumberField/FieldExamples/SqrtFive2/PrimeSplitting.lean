import XYin.NumberField.FieldExamples.SqrtFive2.NormForm

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace XYin.NumberField.SqrtFiveGoldenAdjoinRoot

/-! ## 5. Splitting of primes -/

/-- `√5 = 2φ - 1` as an element of `𝓞 QSqrtFive`. -/
noncomputable def sqrtFiveIntO : 𝓞 QSqrtFive := 2 * goldenIntO - 1

/-- `5` is (totally) ramified: `(5) = (√5)²` as ideals of `𝓞 K`, directly from
`(2φ - 1)² = 5`. It is the unique ramified prime, matching the discriminant `5`. -/
theorem span_five_eq :
    Ideal.span {(5 : 𝓞 QSqrtFive)} = Ideal.span {sqrtFiveIntO} ^ 2 := by
  sorry

/-- The prime `(√5)` above `5` has norm `5` (residue degree `f = 1`). -/
theorem absNorm_span_sqrtFiveIntO : Ideal.absNorm (Ideal.span {sqrtFiveIntO}) = 5 := by
  sorry

/-- `(√5)` is a prime ideal — the unique prime of `𝓞 K` above `5`. -/
theorem isPrime_span_sqrtFiveIntO : (Ideal.span {sqrtFiveIntO}).IsPrime := by
  sorry

/-- `2` is inert in `ℚ(√5)`: `X² - X - 1` is irreducible mod `2`, so `(2)` is itself prime
(of norm `4`). -/
theorem isPrime_span_two : (Ideal.span {(2 : 𝓞 QSqrtFive)}).IsPrime := by
  sorry

/-- `3` is inert in `ℚ(√5)`: `5` is not a square mod `3`, so `(3)` is itself prime (of norm
`9`). -/
theorem isPrime_span_three : (Ideal.span {(3 : 𝓞 QSqrtFive)}).IsPrime := by
  sorry

/-- `11 ≡ 1 (mod 5)` splits: `11 = (3 + φ)(4 - φ)` and `(11)` is a product of two distinct
primes of norm `11`. -/
theorem span_eleven_eq :
    Ideal.span {(11 : 𝓞 QSqrtFive)} =
      Ideal.span {3 + goldenIntO} * Ideal.span {4 - goldenIntO} := by
  sorry

/-- The prime `(3 + φ)` above `11` has norm `11` (residue degree `f = 1`). -/
theorem absNorm_span_three_add_golden :
    Ideal.absNorm (Ideal.span {3 + goldenIntO}) = 11 := by
  sorry

/-- `(3 + φ)` is a prime ideal — one of the two primes of `𝓞 K` above `11`. -/
theorem isPrime_span_three_add_golden : (Ideal.span {3 + goldenIntO}).IsPrime := by
  sorry

/-- The splitting law at ramified primes: a rational prime `p` ramifies in `ℚ(√5)` iff
`p = 5`, i.e. iff `p` divides the discriminant `5`. -/
theorem ramified_iff_eq_five (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 QSqrtFive), P.IsPrime ∧
      Ideal.span {(p : 𝓞 QSqrtFive)} ≤ P ^ 2) ↔ p = 5 := by
  sorry

/-- The quadratic splitting law for `ℚ(√5)`: a rational prime `p ≠ 5` splits into two
distinct primes iff `p ≡ ±1 (mod 5)` (i.e. iff `5` is a quadratic residue mod `p`, by
quadratic reciprocity), and is inert otherwise. -/
theorem splits_iff_pm_one_mod_five (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    (∃ P Q : Ideal (𝓞 QSqrtFive), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 QSqrtFive)} = P * Q) ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  sorry


end XYin.NumberField.SqrtFiveGoldenAdjoinRoot
