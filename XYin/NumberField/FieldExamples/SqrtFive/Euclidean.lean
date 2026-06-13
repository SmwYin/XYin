/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.Common
import XYin.NumberField.FieldExamples.SqrtFive.ClassGroup

/-!
# `ℚ(√5)` Euclidean structure

This file develops the Euclidean structure part of the `ℚ(√5)` number field example.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open NumberField.FieldExamples

namespace NumberField.SqrtFive

private theorem abs_norm_int_lt_of_remainder_eq {b r : 𝓞 QSqrtFive} {bK : QSqrtFive}
    {u v : ℚ}
    (hbK : bK = algebraMap (𝓞 QSqrtFive) QSqrtFive b)
    (hrK :
      algebraMap (𝓞 QSqrtFive) QSqrtFive r =
        bK * ((u - ((round u : ℤ) : ℚ)) • (1 : QSqrtFive) +
          (v - ((round v : ℤ) : ℚ)) • goldenRoot))
    (hb_pos : 0 < |Algebra.norm ℚ bK|)
    (hfrac :
      |(u - ((round u : ℤ) : ℚ)) ^ 2 +
        (u - ((round u : ℤ) : ℚ)) * (v - ((round v : ℤ) : ℚ)) -
        (v - ((round v : ℤ) : ℚ)) ^ 2| ≤ 3 / 4) :
    |((Algebra.norm ℤ r : ℤ) : ℚ)| < |((Algebra.norm ℤ b : ℤ) : ℚ)| := by
  rw [Algebra.coe_norm_int, Algebra.coe_norm_int]
  change |Algebra.norm ℚ (algebraMap (𝓞 QSqrtFive) QSqrtFive r)| <
    |Algebra.norm ℚ (algebraMap (𝓞 QSqrtFive) QSqrtFive b)|
  rw [hrK, map_mul, norm_eq_normForm, abs_mul, ← hbK]
  calc |Algebra.norm ℚ bK| *
      |(u - ((round u : ℤ) : ℚ)) ^ 2 +
        (u - ((round u : ℤ) : ℚ)) * (v - ((round v : ℤ) : ℚ)) -
        (v - ((round v : ℤ) : ℚ)) ^ 2| ≤ |Algebra.norm ℚ bK| * (3 / 4) :=
        mul_le_mul_of_nonneg_left hfrac (abs_nonneg _)
    _ < |Algebra.norm ℚ bK| := by linarith [hb_pos]

/-- `ℚ(√5)` is norm-Euclidean: division with remainder in `ℤ[φ]` with respect to the
absolute value of the field norm. This strengthens `isPrincipalIdealRing`. -/
theorem normEuclidean (a b : 𝓞 QSqrtFive) (hb : b ≠ 0) :
    ∃ q r : 𝓞 QSqrtFive, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  set aK := algebraMap (𝓞 QSqrtFive) QSqrtFive a with haK
  set bK := algebraMap (𝓞 QSqrtFive) QSqrtFive b with hbK
  have hbK0 : bK ≠ 0 := by
    intro h0
    rw [hbK] at h0
    exact hb (IsFractionRing.injective (𝓞 QSqrtFive) QSqrtFive (h0.trans (map_zero _).symm))
  set x := aK / bK with hxdef
  set u := x.re with hu
  set v := x.im with hv
  set q : 𝓞 QSqrtFive := ((round u : ℤ) : 𝓞 QSqrtFive) +
    ((round v : ℤ) : 𝓞 QSqrtFive) * goldenIntO with hq
  refine ⟨q, a - b * q, by ring, ?_⟩
  set r : 𝓞 QSqrtFive := a - b * q with hr
  have hxbK : x * bK = aK := div_mul_cancel₀ aK hbK0
  have hxcoord : x = u • (1 : QSqrtFive) + v • goldenRoot := by
    ext <;> simp [u, v]
  have hqK : algebraMap (𝓞 QSqrtFive) QSqrtFive q =
      ((round u : ℤ) : ℚ) • (1 : QSqrtFive) + ((round v : ℤ) : ℚ) • goldenRoot := by
    rw [hq]
    simp [goldenIntO, Algebra.smul_def]
  have hrK : algebraMap (𝓞 QSqrtFive) QSqrtFive r =
      bK * ((u - ((round u : ℤ) : ℚ)) • (1 : QSqrtFive) +
        (v - ((round v : ℤ) : ℚ)) • goldenRoot) := by
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
  have hlt := abs_norm_int_lt_of_remainder_eq hbK hrK hb_pos hfrac
  exact natAbs_lt_of_abs_ratCast_lt hlt


end NumberField.SqrtFive
