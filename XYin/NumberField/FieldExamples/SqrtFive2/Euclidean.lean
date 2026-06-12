import XYin.NumberField.FieldExamples.SqrtFive2.ClassGroup

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace XYin.NumberField.SqrtFiveGoldenAdjoinRoot

/-! ## 8. Euclidean structure -/

/-- `ℚ(√5)` is norm-Euclidean: division with remainder in `ℤ[φ]` with respect to the absolute
value of the field norm. It is one of the finitely many norm-Euclidean real quadratic
fields. -/
theorem normEuclidean (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  set aK := algebraMap (𝓞 K) K a with haK
  set bK := algebraMap (𝓞 K) K b with hbK
  have hbK0 : bK ≠ 0 := by
    intro h0
    rw [hbK] at h0
    exact hb (IsFractionRing.injective (𝓞 K) K (h0.trans (map_zero _).symm))
  set x := aK / bK with hxdef
  obtain ⟨xa, xb, hxab⟩ := exists_coords x
  set u := xa - xb with hu
  set v := 2 * xb with hv
  set q : 𝓞 K := ((round u : ℤ) : 𝓞 K) + ((round v : ℤ) : 𝓞 K) * goldenInt with hq
  refine ⟨q, a - b * q, by ring, ?_⟩
  set r : 𝓞 K := a - b * q with hr
  have hxbK : x * bK = aK := div_mul_cancel₀ aK hbK0
  have hxcoord : x = u • (1 : K) + v • goldenInteger := by
    rw [hxab, hu, hv, Algebra.smul_def, Algebra.smul_def, mul_one, map_sub, map_mul,
      map_ofNat, show goldenInteger = (1 + sqrtFive) / 2 from rfl]
    field_simp
    ring
  have hqK : algebraMap (𝓞 K) K q =
      ((round u : ℤ) : ℚ) • (1 : K) + ((round v : ℤ) : ℚ) • goldenInteger := by
    rw [hq, map_add, map_mul, map_intCast, map_intCast, coe_goldenInt,
      Algebra.smul_def, Algebra.smul_def, mul_one, eq_ratCast (algebraMap ℚ K),
      eq_ratCast (algebraMap ℚ K), Rat.cast_intCast, Rat.cast_intCast]
  have hrK : algebraMap (𝓞 K) K r =
      bK * ((u - ((round u : ℤ) : ℚ)) • (1 : K) +
        (v - ((round v : ℤ) : ℚ)) • goldenInteger) := by
    rw [hr, map_sub, map_mul, hqK, ← hbK, ← haK, ← hxbK, hxcoord]
    simp only [Algebra.smul_def, map_sub]
    ring
  have hs := abs_sub_round u
  have ht := abs_sub_round v
  have hfrac : |(u - ((round u : ℤ) : ℚ)) ^ 2 +
      (u - ((round u : ℤ) : ℚ)) * (v - ((round v : ℤ) : ℚ)) -
      (v - ((round v : ℤ) : ℚ)) ^ 2| ≤ 3 / 4 := by
    rw [abs_le] at hs ht ⊢
    constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2]
  have hb_pos : 0 < |Algebra.norm ℚ bK| :=
    abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hbK0)
  have hlt : |((Algebra.norm ℤ r : ℤ) : ℚ)| < |((Algebra.norm ℤ b : ℤ) : ℚ)| := by
    rw [Algebra.coe_norm_int, Algebra.coe_norm_int]
    change |Algebra.norm ℚ (algebraMap (𝓞 K) K r)| < |Algebra.norm ℚ (algebraMap (𝓞 K) K b)|
    rw [hrK, map_mul, norm_eq_normForm, abs_mul, ← hbK]
    calc |Algebra.norm ℚ bK| *
        |(u - ((round u : ℤ) : ℚ)) ^ 2 +
          (u - ((round u : ℤ) : ℚ)) * (v - ((round v : ℤ) : ℚ)) -
          (v - ((round v : ℤ) : ℚ)) ^ 2| ≤ |Algebra.norm ℚ bK| * (3 / 4) :=
          mul_le_mul_of_nonneg_left hfrac (abs_nonneg _)
      _ < |Algebra.norm ℚ bK| := by linarith [hb_pos]
  have hltZ : |Algebra.norm ℤ r| < |Algebra.norm ℤ b| := by exact_mod_cast hlt
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hltZ
  exact_mod_cast hltZ


end XYin.NumberField.SqrtFiveGoldenAdjoinRoot
