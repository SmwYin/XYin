import XYin.NumberField.FieldExamples.SqrtTwo.ClassGroup

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace XYin.NumberField.SqrtTwo

/-! ## 8. Euclidean structure -/

private theorem exists_coords (x : QSqrtTwo) :
    ∃ a b : ℚ, x = a • (1 : QSqrtTwo) + b • sqrtTwoRoot := by
  obtain ⟨f, hf, hx⟩ := sqrtTwoPowerBasis.exists_eq_aeval x
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  have hdim : sqrtTwoPowerBasis.dim = 2 := sqrtTwoPowerBasis_dim
  have hdeg : f.natDegree ≤ 1 := by
    have := hdim ▸ hf
    omega
  conv_lhs => rw [hx, Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
  rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
  rw [Algebra.smul_def, Algebra.smul_def, mul_one]
  rw [show sqrtTwoPowerBasis.gen = sqrtTwoRoot by simp [sqrtTwoPowerBasis, sqrtTwoRoot]]
  simp [add_comm]

/-- `ℚ(√2)` is norm-Euclidean: division with remainder in `ℤ[√2]` with respect to the
absolute value of the field norm. This is the classical Euclidean algorithm for the real
quadratic field of smallest discriminant, and strengthens
`sqrtTwo_ringOfIntegers_isPrincipalIdealRing`. -/
theorem normEuclidean (a b : O2) (hb : b ≠ 0) :
    ∃ q r : O2, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  set aK := algebraMap O2 QSqrtTwo a with haK
  set bK := algebraMap O2 QSqrtTwo b with hbK
  have hbK0 : bK ≠ 0 := by
    intro h0
    rw [hbK] at h0
    exact hb (IsFractionRing.injective O2 QSqrtTwo (h0.trans (map_zero _).symm))
  set x := aK / bK with hxdef
  obtain ⟨xa, xb, hxab⟩ := exists_coords x
  set q : O2 := ((round xa : ℤ) : O2) + ((round xb : ℤ) : O2) * sqrtTwoInteger with hq
  refine ⟨q, a - b * q, by ring, ?_⟩
  set r : O2 := a - b * q with hr
  have hxbK : x * bK = aK := div_mul_cancel₀ aK hbK0
  have hqK : algebraMap O2 QSqrtTwo q =
      ((round xa : ℤ) : ℚ) • (1 : QSqrtTwo) +
        ((round xb : ℤ) : ℚ) • sqrtTwoRoot := by
    rw [hq]
    simp [sqrtTwoInteger, Algebra.smul_def]
  have hrK : algebraMap O2 QSqrtTwo r =
      bK * ((xa - ((round xa : ℤ) : ℚ)) • (1 : QSqrtTwo) +
        (xb - ((round xb : ℤ) : ℚ)) • sqrtTwoRoot) := by
    rw [hr, map_sub, map_mul, hqK, ← hbK, ← haK, ← hxbK, hxab]
    simp only [Algebra.smul_def, map_sub]
    ring
  have hs := abs_sub_round xa
  have ht := abs_sub_round xb
  have hfrac : |(xa - ((round xa : ℤ) : ℚ)) ^ 2 -
      2 * (xb - ((round xb : ℤ) : ℚ)) ^ 2| ≤ 1 / 2 := by
    rw [abs_le] at hs ht ⊢
    constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2,
      sq_nonneg (xa - ((round xa : ℤ) : ℚ)),
      sq_nonneg (xb - ((round xb : ℤ) : ℚ))]
  have hb_pos : 0 < |Algebra.norm ℚ bK| :=
    abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hbK0)
  have hlt : |((Algebra.norm ℤ r : ℤ) : ℚ)| < |((Algebra.norm ℤ b : ℤ) : ℚ)| := by
    rw [Algebra.coe_norm_int, Algebra.coe_norm_int]
    change |Algebra.norm ℚ (algebraMap O2 QSqrtTwo r)| <
      |Algebra.norm ℚ (algebraMap O2 QSqrtTwo b)|
    rw [hrK, map_mul, norm_eq_normForm, abs_mul, ← hbK]
    calc |Algebra.norm ℚ bK| *
        |(xa - ((round xa : ℤ) : ℚ)) ^ 2 -
          2 * (xb - ((round xb : ℤ) : ℚ)) ^ 2| ≤ |Algebra.norm ℚ bK| * (1 / 2) :=
          mul_le_mul_of_nonneg_left hfrac (abs_nonneg _)
      _ < |Algebra.norm ℚ bK| := by linarith [hb_pos]
  have hltZ : |Algebra.norm ℤ r| < |Algebra.norm ℤ b| := by exact_mod_cast hlt
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hltZ
  exact_mod_cast hltZ


end XYin.NumberField.SqrtTwo
