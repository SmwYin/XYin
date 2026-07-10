/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NFIL.NumberField.FieldExamples.SqrtFive.Units

/-!
# `ℚ(√5)` Euclidean

Euclidean or non-Euclidean properties and their arithmetic consequences.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Euclidean
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open NumberField.FieldExamples

namespace NumberField.SqrtFive

private theorem abs_norm_int_lt_of_remainder_eq {b r : 𝓞 K} {bK : K}
    {u v : ℚ}
    (hbK : bK = algebraMap (𝓞 K) K b)
    (hrK :
      algebraMap (𝓞 K) K r =
        bK * ((u - ((round u : ℤ) : ℚ)) • (1 : K) +
          (v - ((round v : ℤ) : ℚ)) • goldenRoot))
    (hb_pos : 0 < |Algebra.norm ℚ bK|)
    (hfrac :
      |(u - ((round u : ℤ) : ℚ)) ^ 2 +
        (u - ((round u : ℤ) : ℚ)) * (v - ((round v : ℤ) : ℚ)) -
        (v - ((round v : ℤ) : ℚ)) ^ 2| ≤ 3 / 4) :
    |((Algebra.norm ℤ r : ℤ) : ℚ)| < |((Algebra.norm ℤ b : ℤ) : ℚ)| := by
  refine abs_intNorm_lt_of_abs_norm_le hbK hrK hb_pos
    (show (3 : ℚ) / 4 < 1 by norm_num) ?_
  exact (norm_eq_normForm _ _).symm ▸ hfrac

/-- `ℚ(√5)` is norm-Euclidean: division with remainder in `ℤ[φ]` with respect to the
absolute value of the field norm. This strengthens `isPrincipalIdealRing`. -/
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
  set u := x.re with hu
  set v := x.im with hv
  set q : 𝓞 K := ((round u : ℤ) : 𝓞 K) +
    ((round v : ℤ) : 𝓞 K) * goldenIntO with hq
  refine ⟨q, a - b * q, by ring, ?_⟩
  set r : 𝓞 K := a - b * q with hr
  have hxbK : x * bK = aK := div_mul_cancel₀ aK hbK0
  have hxcoord : x = u • (1 : K) + v • goldenRoot := by
    ext <;> simp [u, v]
  have hqK : algebraMap (𝓞 K) K q =
      ((round u : ℤ) : ℚ) • (1 : K) + ((round v : ℤ) : ℚ) • goldenRoot := by
    rw [hq]
    simp [goldenIntO, Algebra.smul_def]
  have hrK : algebraMap (𝓞 K) K r =
      bK * ((u - ((round u : ℤ) : ℚ)) • (1 : K) +
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
