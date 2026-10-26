/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.LinearCombination

/-!
# Coordinate arithmetic in Cox Lemma 7.5

These elementary statements isolate the coefficient comparison and Bézout argument used to compute
the multiplier ring of `[1, τ]`.
-/

namespace Cox.OrderArithmetic

/-- Source: Cox Lemma 7.5, pp. 135–136, primitive quadratic coefficients. -/
theorem dvd_of_primitive_triple (A B C n : ℤ)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1)
    (hB : A ∣ B * n) (hC : A ∣ C * n) : A ∣ n := by
  have hg : Int.gcd (Int.gcd A B : ℤ) C = 1 := by simpa [Int.gcd] using hprim
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, (Int.gcd A B : ℤ) = A * a + B * b :=
    ⟨_, _, Int.gcd_eq_gcd_ab A B⟩
  obtain ⟨c, d, hcd⟩ : ∃ c d : ℤ, (1 : ℤ) = (Int.gcd A B : ℤ) * c + C * d :=
    ⟨_, _, by rw [← Int.gcd_eq_gcd_ab, hg, Nat.cast_one]⟩
  rw [hab] at hcd
  have key : n = A * (a * c * n) + B * n * (b * c) + C * n * d := by
    calc n = n * 1 := (mul_one n).symm
      _ = _ := by rw [hcd]; ring
  rw [key]
  exact ((dvd_mul_right A _).add (hB.mul_right _)).add (hC.mul_right _)

/-- Source: Cox Lemma 7.5, pp. 135–136, comparison of the constant coefficient. -/
theorem constant_coefficient_eq {F : Type*} [Field F] [CharZero F]
    (τ : F) (hτ : LinearIndependent ℚ ![1, τ]) (A B C m n u v : ℤ)
    (hq : (A : F) * τ ^ 2 + B * τ + C = 0)
    (hx : ((m : F) + n * τ) * τ = u + v * τ) : A * u = -(C * n) := by
  have key : ((A * u : ℤ) : ℚ) • (1 : F) + ((A * v : ℤ) : ℚ) • τ =
      ((-(C * n) : ℤ) : ℚ) • (1 : F) + ((A * m - B * n : ℤ) : ℚ) • τ := by
    simp only [Rat.smul_def, Rat.cast_intCast]
    push_cast
    linear_combination (-(A : F)) * hx + (n : F) * hq
  exact_mod_cast (hτ.eq_of_pair key).1

/-- Source: Cox Lemma 7.5, pp. 135–136, comparison of the linear coefficient. -/
theorem linear_coefficient_eq {F : Type*} [Field F] [CharZero F]
    (τ : F) (hτ : LinearIndependent ℚ ![1, τ]) (A B C m n u v : ℤ)
    (hq : (A : F) * τ ^ 2 + B * τ + C = 0)
    (hx : ((m : F) + n * τ) * τ = u + v * τ) : A * v = A * m - B * n := by
  have key : ((A * u : ℤ) : ℚ) • (1 : F) + ((A * v : ℤ) : ℚ) • τ =
      ((-(C * n) : ℤ) : ℚ) • (1 : F) + ((A * m - B * n : ℤ) : ℚ) • τ := by
    simp only [Rat.smul_def, Rat.cast_intCast]
    push_cast
    linear_combination (-(A : F)) * hx + (n : F) * hq
  exact_mod_cast (hτ.eq_of_pair key).2

/-- Source: Cox Lemma 7.5, pp. 135–136, divisibility of the linear coefficient. -/
theorem dvd_linear_of_mul_tau_mem {F : Type*} [Field F] [CharZero F]
    (τ : F) (hτ : LinearIndependent ℚ ![1, τ]) (A B C m n : ℤ)
    (hq : (A : F) * τ ^ 2 + B * τ + C = 0)
    (hx : ((m : F) + n * τ) * τ ∈ Submodule.span ℤ ({1, τ} : Set F)) :
    A ∣ B * n := by
  obtain ⟨u, v, huv⟩ := Submodule.mem_span_pair.mp hx
  have h := linear_coefficient_eq τ hτ A B C m n u v hq (by simpa [zsmul_eq_mul] using huv.symm)
  exact ⟨m - v, by linear_combination h⟩

/-- Source: Cox Lemma 7.5, pp. 135–136, divisibility of the constant coefficient. -/
theorem dvd_constant_of_mul_tau_mem {F : Type*} [Field F] [CharZero F]
    (τ : F) (hτ : LinearIndependent ℚ ![1, τ]) (A B C m n : ℤ)
    (hq : (A : F) * τ ^ 2 + B * τ + C = 0)
    (hx : ((m : F) + n * τ) * τ ∈ Submodule.span ℤ ({1, τ} : Set F)) :
    A ∣ C * n := by
  obtain ⟨u, v, huv⟩ := Submodule.mem_span_pair.mp hx
  have h := constant_coefficient_eq τ hτ A B C m n u v hq (by simpa [zsmul_eq_mul] using huv.symm)
  exact ⟨-u, by linear_combination h⟩

/-- Source: Cox Lemma 7.5, pp. 135–136, the converse multiplier calculation. -/
theorem mul_tau_mem_of_dvd {F : Type*} [Field F] [CharZero F]
    (τ : F) (A B C m n : ℤ)
    (hq : (A : F) * τ ^ 2 + B * τ + C = 0) (hn : A ∣ n) :
    ((m : F) + n * τ) * τ ∈ Submodule.span ℤ ({1, τ} : Set F) := by
  obtain ⟨k, rfl⟩ := hn
  refine Submodule.mem_span_pair.mpr ⟨-(k * C), m - k * B, ?_⟩
  simp only [zsmul_eq_mul, mul_one]
  push_cast
  linear_combination (-(k : F)) * hq

end Cox.OrderArithmetic
