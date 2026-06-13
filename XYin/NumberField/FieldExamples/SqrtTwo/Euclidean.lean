/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.Common
import XYin.NumberField.FieldExamples.SqrtTwo.ClassGroup

/-!
# `ℚ(√2)` Euclidean structure

This file develops the Euclidean structure part of the `ℚ(√2)` number field example.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open NumberField.FieldExamples

namespace NumberField.SqrtTwo

private theorem abs_norm_int_lt_of_remainder_eq {b r : O2} {bK e : QSqrtTwo} {u v : ℚ}
    (hbK : bK = algebraMap O2 QSqrtTwo b)
    (hrK : algebraMap O2 QSqrtTwo r = bK * e)
    (hb_pos : 0 < |Algebra.norm ℚ bK|)
    (hnorm_e :
      |Algebra.norm ℚ e| =
        |(u - ((round u : ℤ) : ℚ)) ^ 2 - 2 * (v - ((round v : ℤ) : ℚ)) ^ 2|)
    (hfrac :
      |(u - ((round u : ℤ) : ℚ)) ^ 2 - 2 * (v - ((round v : ℤ) : ℚ)) ^ 2| ≤ 1 / 2) :
    |((Algebra.norm ℤ r : ℤ) : ℚ)| < |((Algebra.norm ℤ b : ℤ) : ℚ)| := by
  rw [Algebra.coe_norm_int, Algebra.coe_norm_int]
  change |Algebra.norm ℚ (algebraMap O2 QSqrtTwo r)| <
    |Algebra.norm ℚ (algebraMap O2 QSqrtTwo b)|
  rw [hrK, map_mul, abs_mul, ← hbK]
  calc |Algebra.norm ℚ bK| * |Algebra.norm ℚ e| =
        |Algebra.norm ℚ bK| *
          |(u - ((round u : ℤ) : ℚ)) ^ 2 - 2 * (v - ((round v : ℤ) : ℚ)) ^ 2| := by
        rw [hnorm_e]
    _ ≤ |Algebra.norm ℚ bK| * (1 / 2) :=
        mul_le_mul_of_nonneg_left hfrac (abs_nonneg _)
    _ < |Algebra.norm ℚ bK| := by linarith [hb_pos]

/-- `ℚ(√2)` is norm-Euclidean: division with remainder in `ℤ[√2]` with respect to the
absolute value of the field norm. This is the classical Euclidean algorithm for the real
quadratic field of smallest discriminant, and strengthens `isPrincipalIdealRing`. -/
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
  set u := x.re with hu
  set v := x.im with hv
  set q : O2 := ((round u : ℤ) : O2) + ((round v : ℤ) : O2) * sqrtTwoInteger with hq
  refine ⟨q, a - b * q, by ring, ?_⟩
  set r : O2 := a - b * q with hr
  have hxbK : x * bK = aK := div_mul_cancel₀ aK hbK0
  have hxcoord : x = u • (1 : QSqrtTwo) + v • sqrtTwoRoot := by
    ext <;> simp [u, v, sqrtTwoRoot, Algebra.smul_def]
  have hqK : algebraMap O2 QSqrtTwo q =
      ((round u : ℤ) : ℚ) • (1 : QSqrtTwo) +
        ((round v : ℤ) : ℚ) • sqrtTwoRoot := by
    rw [hq]
    simp [sqrtTwoInteger, sqrtTwoRoot, Algebra.smul_def]
  set e : QSqrtTwo := (u - ((round u : ℤ) : ℚ)) • (1 : QSqrtTwo) +
    (v - ((round v : ℤ) : ℚ)) • sqrtTwoRoot with he
  have hrK : algebraMap O2 QSqrtTwo r =
      bK * e := by
    rw [hr, map_sub, map_mul, hqK, ← hbK, ← haK, ← hxbK, hxcoord]
    rw [he]
    simp only [Algebra.smul_def, map_sub]
    ring
  have hs := abs_sub_round u
  have ht := abs_sub_round v
  have hfrac : |(u - ((round u : ℤ) : ℚ)) ^ 2 -
      2 * (v - ((round v : ℤ) : ℚ)) ^ 2| ≤ 1 / 2 := by
    rw [abs_le] at hs ht ⊢
    constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2,
      sq_nonneg (u - ((round u : ℤ) : ℚ)),
      sq_nonneg (v - ((round v : ℤ) : ℚ))]
  have hb_pos : 0 < |Algebra.norm ℚ bK| :=
    abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hbK0)
  have hnorm_e : |Algebra.norm ℚ e| =
      |(u - ((round u : ℤ) : ℚ)) ^ 2 -
        2 * (v - ((round v : ℤ) : ℚ)) ^ 2| := by
    rw [he, norm_eq_normForm]
    simp [sqrtTwoRoot, Algebra.smul_def]
  have hlt := abs_norm_int_lt_of_remainder_eq hbK hrK hb_pos hnorm_e hfrac
  exact natAbs_lt_of_abs_ratCast_lt hlt

end NumberField.SqrtTwo
