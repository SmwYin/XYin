import XYin.NumberField.FieldExamples.CyclotomicThree.ClassGroup

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace XYin.NumberField.CyclotomicThree

private theorem coe_zetaInt : algebraMap OK K zetaInt = ζ := rfl

/-! ## 8. Euclidean structure -/

private theorem exists_coords (x : K) :
    ∃ a b : ℚ, x = a • (1 : K) + b • ζ := by
  obtain ⟨f, hf, hx⟩ := (zeta_isPrimitiveRoot.powerBasis ℚ).exists_eq_aeval x
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  have hdim : (zeta_isPrimitiveRoot.powerBasis ℚ).dim = 2 := by
    rw [IsPrimitiveRoot.powerBasis_dim, ← zetaThreePolynomial_eq_minpoly]
    rw [zetaThreePolynomial]
    compute_degree!
  have hdeg : f.natDegree ≤ 1 := by
    have := hdim ▸ hf
    omega
  conv_lhs => rw [hx, Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
  rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X,
    IsPrimitiveRoot.powerBasis_gen]
  rw [Algebra.smul_def, Algebra.smul_def, mul_one]
  ring

/-- `ℤ[ζ₃]`, the ring of Eisenstein integers, is norm-Euclidean: division with remainder
with respect to the absolute value of the field norm. This strengthens
`isPrincipalIdealRing`. -/
theorem normEuclidean (a b : OK) (hb : b ≠ 0) :
    ∃ q r : OK, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  set aK := algebraMap OK K a with haK
  set bK := algebraMap OK K b with hbK
  have hbK0 : bK ≠ 0 := by
    intro h0
    rw [hbK] at h0
    exact hb (IsFractionRing.injective OK K (h0.trans (map_zero _).symm))
  set x := aK / bK with hxdef
  obtain ⟨xa, xb, hxab⟩ := exists_coords x
  set q : OK := ((round xa : ℤ) : OK) + ((round xb : ℤ) : OK) * zetaInt with hq
  refine ⟨q, a - b * q, by ring, ?_⟩
  set r : OK := a - b * q with hr
  have hxbK : x * bK = aK := div_mul_cancel₀ aK hbK0
  have hqK : algebraMap OK K q =
      ((round xa : ℤ) : ℚ) • (1 : K) + ((round xb : ℤ) : ℚ) • ζ := by
    rw [hq, map_add, map_mul, map_intCast, map_intCast, coe_zetaInt,
      Algebra.smul_def, Algebra.smul_def, mul_one, eq_ratCast (algebraMap ℚ K),
      eq_ratCast (algebraMap ℚ K), Rat.cast_intCast, Rat.cast_intCast]
  have hrK : algebraMap OK K r =
      bK * ((xa - ((round xa : ℤ) : ℚ)) • (1 : K) +
        (xb - ((round xb : ℤ) : ℚ)) • ζ) := by
    rw [hr, map_sub, map_mul, hqK, ← hbK, ← haK, ← hxbK, hxab]
    simp only [Algebra.smul_def, map_sub]
    ring
  have hs := abs_sub_round xa
  have ht := abs_sub_round xb
  have hfrac : |(xa - ((round xa : ℤ) : ℚ)) ^ 2 -
      (xa - ((round xa : ℤ) : ℚ)) * (xb - ((round xb : ℤ) : ℚ)) +
      (xb - ((round xb : ℤ) : ℚ)) ^ 2| ≤ 3 / 4 := by
    rw [abs_le] at hs ht ⊢
    constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2,
      sq_nonneg ((xa - ((round xa : ℤ) : ℚ)) + (xb - ((round xb : ℤ) : ℚ))),
      sq_nonneg ((xa - ((round xa : ℤ) : ℚ)) - (xb - ((round xb : ℤ) : ℚ)))]
  have hb_pos : 0 < |Algebra.norm ℚ bK| :=
    abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hbK0)
  have hlt : |((Algebra.norm ℤ r : ℤ) : ℚ)| < |((Algebra.norm ℤ b : ℤ) : ℚ)| := by
    rw [Algebra.coe_norm_int, Algebra.coe_norm_int]
    change |Algebra.norm ℚ (algebraMap OK K r)| < |Algebra.norm ℚ (algebraMap OK K b)|
    rw [hrK, map_mul, norm_eq_normForm, abs_mul, ← hbK]
    calc |Algebra.norm ℚ bK| *
        |(xa - ((round xa : ℤ) : ℚ)) ^ 2 -
          (xa - ((round xa : ℤ) : ℚ)) * (xb - ((round xb : ℤ) : ℚ)) +
          (xb - ((round xb : ℤ) : ℚ)) ^ 2| ≤ |Algebra.norm ℚ bK| * (3 / 4) :=
          mul_le_mul_of_nonneg_left hfrac (abs_nonneg _)
      _ < |Algebra.norm ℚ bK| := by linarith [hb_pos]
  have hltZ : |Algebra.norm ℤ r| < |Algebra.norm ℤ b| := by exact_mod_cast hlt
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hltZ
  exact_mod_cast hltZ


end XYin.NumberField.CyclotomicThree
