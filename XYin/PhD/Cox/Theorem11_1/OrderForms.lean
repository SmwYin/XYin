/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.Orders
import Mathlib.Data.Nat.ChineseRemainder

/-! # The form argument for Cox Corollary 7.17

Cox uses Lemma 2.25 (proved in Exercise 2.18), the unimodular substitution
of Lemma 2.3, and the norm calculation in Theorem 7.7(iii). The generic
coefficient calculations do not require an imaginary quadratic field.
-/

open NumberField
open scoped nonZeroDivisors Pointwise
noncomputable section

namespace Cox.BinaryQuadratic

/-- Cox Exercise 2.18(a), p.45: one of the three displayed values avoids a given prime. -/
theorem exists_basic_value_not_dvd (A B C : ℤ)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1)
    (p : ℕ) (hp : p.Prime) :
    ¬ (p : ℤ) ∣ A ∨ ¬ (p : ℤ) ∣ C ∨ ¬ (p : ℤ) ∣ A + B + C := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨hA, hC, hABC⟩ := h
  have hB : (p : ℤ) ∣ B := by
    have h := dvd_sub (dvd_sub hABC hA) hC
    rwa [show A + B + C - A - C = B by ring] at h
  have h1 : p ∣ Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs :=
    Nat.dvd_gcd (Nat.dvd_gcd (Int.natCast_dvd.mp hA) (Int.natCast_dvd.mp hB))
      (Int.natCast_dvd.mp hC)
  rw [hprim] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-- Cox Exercise 2.18(b), p.45: solve the two coordinate congruence systems. -/
theorem exists_coordinate_congruences (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (x y : ℕ → ℕ) :
    ∃ u v : ℕ, ∀ p ∈ S, Nat.ModEq p u (x p) ∧ Nat.ModEq p v (y p) := by
  have hs : ∀ p ∈ S, id p ≠ 0 := fun p hp => (hS p hp).ne_zero
  have pp : Set.Pairwise (S : Set ℕ) (Function.onFun Nat.Coprime id) := fun p hp q hq hpq =>
    (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq
  obtain ⟨u, hu⟩ := Nat.chineseRemainderOfFinset x id S hs pp
  obtain ⟨v, hv⟩ := Nat.chineseRemainderOfFinset y id S hs pp
  exact ⟨u, v, fun p hp => ⟨hu p hp, hv p hp⟩⟩

/-- Cox Exercise 2.18(b): a quadratic polynomial respects coordinate congruences. -/
theorem value_modEq (A B C u v x y m : ℤ)
    (hx : Int.ModEq m u x) (hy : Int.ModEq m v y) :
    Int.ModEq m (A * u ^ 2 + B * u * v + C * v ^ 2)
      (A * x ^ 2 + B * x * y + C * y ^ 2) := by
  gcongr

/-- Cox Exercise 2.18(b): avoiding each prime divisor is coprimality with the modulus. -/
theorem coprime_of_primeFactors_not_dvd (z : ℤ) (M : ℕ) (hM : M ≠ 0)
    (hz : ∀ p ∈ M.primeFactors, ¬ (p : ℤ) ∣ z) : z.natAbs.Coprime M := by
  refine Nat.coprime_of_dvd fun k hk hkz hkM => ?_
  exact hz k (Nat.mem_primeFactors.mpr ⟨hk, hkM, hM⟩) (Int.natCast_dvd.mpr hkz)

/-- Cox Lemma 2.25 / Exercise 2.18: first construct a nonzero coordinate pair. -/
theorem exists_coprime_value (A B C : ℤ)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1)
    (M : ℕ) (hM : M ≠ 0) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧
      (A * x ^ 2 + B * x * y + C * y ^ 2).natAbs.Coprime M := by
  have hex : ∀ p ∈ M.primeFactors, ∃ a b : ℕ,
      ¬ (p : ℤ) ∣ A * (a : ℤ) ^ 2 + B * a * b + C * (b : ℤ) ^ 2 := by
    intro p hp
    rcases exists_basic_value_not_dvd A B C hprim p (Nat.prime_of_mem_primeFactors hp)
      with h | h | h
    · exact ⟨1, 0, by simpa using h⟩
    · exact ⟨0, 1, by simpa using h⟩
    · exact ⟨1, 1, by simpa using h⟩
  choose! a b hab using hex
  obtain ⟨u, v, huv⟩ := exists_coordinate_congruences M.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) a b
  refine ⟨u + M, v, Or.inl (by positivity), coprime_of_primeFactors_not_dvd _ M hM
    fun p hp hdvd => hab p hp ?_⟩
  have hpM : (p : ℤ) ∣ M := Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_primeFactors hp)
  have hx : Int.ModEq p ((u : ℤ) + M) (a p) := by
    have h1 : Int.ModEq p (u : ℤ) (a p) := Int.natCast_modEq_iff.mpr (huv p hp).1
    have h2 : Int.ModEq p (M : ℤ) 0 := (Int.modEq_zero_iff_dvd.mpr hpM)
    simpa using h1.add h2
  have hy : Int.ModEq p (v : ℤ) (b p) := Int.natCast_modEq_iff.mpr (huv p hp).2
  exact (value_modEq A B C _ _ _ _ p hx hy).dvd_iff.mp hdvd

/-- Cox Exercise 2.1, p.43: divide a nonzero coordinate pair by its positive gcd. -/
theorem exists_primitive_pair_factor (x y : ℤ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    ∃ (d : ℕ) (u v : ℤ), 0 < d ∧ IsCoprime u v ∧ x = d * u ∧ y = d * v := by
  have hd : 0 < Int.gcd x y := Int.gcd_pos_iff.mpr hxy
  refine ⟨Int.gcd x y, x / Int.gcd x y, y / Int.gcd x y, hd,
    Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hd), ?_, ?_⟩
  · exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left x y)).symm
  · exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right x y)).symm

/-- Cox Exercise 2.1: a degree-two form scales by the square of the common factor. -/
theorem value_mul_pair {R : Type*} [CommRing R] (A B C d x y : R) :
    A * (d * x) ^ 2 + B * (d * x) * (d * y) + C * (d * y) ^ 2 =
      d ^ 2 * (A * x ^ 2 + B * x * y + C * y ^ 2) := by
  ring

/-- Cox Lemma 2.25, p.35: a primitive form properly represents a good value. -/
theorem exists_proper_coprime_value (A B C : ℤ)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1)
    (M : ℕ) (hM : M ≠ 0) :
    ∃ x y : ℤ, IsCoprime x y ∧
      (A * x ^ 2 + B * x * y + C * y ^ 2).natAbs.Coprime M := by
  obtain ⟨x, y, hxy, hcop⟩ := exists_coprime_value A B C hprim M hM
  obtain ⟨d, u, v, -, huv, rfl, rfl⟩ := exists_primitive_pair_factor x y hxy
  refine ⟨u, v, huv, Nat.Coprime.coprime_dvd_left ?_ hcop⟩
  rw [value_mul_pair]
  exact Int.natAbs_dvd_natAbs.mpr (dvd_mul_left _ _)

/-- Cox Lemma 2.3: complete a primitive first column to a determinant-one matrix. -/
theorem exists_unimodular_completion (x y : ℤ) (hxy : IsCoprime x y) :
    ∃ r s : ℤ, x * s - y * r = 1 := by
  obtain ⟨a, b, h⟩ := hxy
  exact ⟨-b, a, by linear_combination h⟩

/-- Cox Lemma 2.3: expand the transformed coefficients. -/
theorem transformed_value {R : Type*} [CommRing R] (A B C x y r s u v : R) :
    A * (x * u + r * v) ^ 2 + B * (x * u + r * v) * (y * u + s * v) +
      C * (y * u + s * v) ^ 2 =
    (A * x ^ 2 + B * x * y + C * y ^ 2) * u ^ 2 +
      (2 * A * x * r + B * (x * s + y * r) + 2 * C * y * s) * u * v +
      (A * r ^ 2 + B * r * s + C * s ^ 2) * v ^ 2 := by
  ring

/-- Cox Exercise 2.2(d), p.43: unimodular substitution preserves primitivity. -/
theorem transformed_primitive (A B C x y r s : ℤ)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1)
    (hdet : x * s - y * r = 1) :
    Nat.gcd (Nat.gcd (A * x ^ 2 + B * x * y + C * y ^ 2).natAbs
      (2 * A * x * r + B * (x * s + y * r) + 2 * C * y * s).natAbs)
      (A * r ^ 2 + B * r * s + C * s ^ 2).natAbs = 1 := by
  set A' := A * x ^ 2 + B * x * y + C * y ^ 2
  set B' := 2 * A * x * r + B * (x * s + y * r) + 2 * C * y * s
  set C' := A * r ^ 2 + B * r * s + C * s ^ 2
  set g := Nat.gcd (Nat.gcd A'.natAbs B'.natAbs) C'.natAbs
  obtain ⟨a, ha⟩ : (g : ℤ) ∣ A' :=
    Int.natCast_dvd.mpr ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
  obtain ⟨b, hb⟩ : (g : ℤ) ∣ B' :=
    Int.natCast_dvd.mpr ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
  obtain ⟨c, hc⟩ : (g : ℤ) ∣ C' := Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  have eA : A = A' * s ^ 2 - B' * s * y + C' * y ^ 2 := by
    simp only [A', B', C']
    linear_combination (-A * (x * s - y * r + 1)) * hdet
  have eB : B = -2 * r * s * A' + (s * x + r * y) * B' - 2 * x * y * C' := by
    simp only [A', B', C']
    linear_combination (-B * (x * s - y * r + 1)) * hdet
  have eC : C = A' * r ^ 2 - B' * r * x + C' * x ^ 2 := by
    simp only [A', B', C']
    linear_combination (-C * (x * s - y * r + 1)) * hdet
  have hA : (g : ℤ) ∣ A := ⟨a * s ^ 2 - b * s * y + c * y ^ 2, by rw [eA, ha, hb, hc]; ring⟩
  have hB : (g : ℤ) ∣ B :=
    ⟨-2 * r * s * a + (s * x + r * y) * b - 2 * x * y * c, by rw [eB, ha, hb, hc]; ring⟩
  have hC : (g : ℤ) ∣ C := ⟨a * r ^ 2 - b * r * x + c * x ^ 2, by rw [eC, ha, hb, hc]; ring⟩
  have h1 : g ∣ Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs :=
    Nat.dvd_gcd (Nat.dvd_gcd (Int.natCast_dvd.mp hA) (Int.natCast_dvd.mp hB))
      (Int.natCast_dvd.mp hC)
  rw [hprim] at h1
  exact Nat.dvd_one.mp h1

/-- Cox Exercise 2.4(b), p.43: the completed-square identity proves positivity. -/
theorem value_pos (A B C x y : ℤ) (hA : 0 < A) (hD : B ^ 2 - 4 * A * C < 0)
    (hxy : x ≠ 0 ∨ y ≠ 0) : 0 < A * x ^ 2 + B * x * y + C * y ^ 2 := by
  have key : 4 * A * (A * x ^ 2 + B * x * y + C * y ^ 2) =
      (2 * A * x + B * y) ^ 2 + (4 * A * C - B ^ 2) * y ^ 2 := by ring
  rcases eq_or_ne y 0 with rfl | hy
  · have hx : x ≠ 0 := hxy.resolve_right (by simp)
    have hx2 : 0 < x ^ 2 := by positivity
    simpa using mul_pos hA hx2
  · have h1 : 0 < (4 * A * C - B ^ 2) * y ^ 2 := mul_pos (by linarith) (by positivity)
    have h2 : 0 < 4 * A * (A * x ^ 2 + B * x * y + C * y ^ 2) := by
      rw [key]; positivity
    exact pos_of_mul_pos_right h2 (by positivity)

end Cox.BinaryQuadratic

namespace Cox.Order
variable {K : IntermediateField ℚ ℂ} [hNF : NumberField K]
variable (O : Subalgebra ℤ K) [hO : IsOrder O] [hIQ : IsImaginaryQuadraticField K]
include hNF hO hIQ

omit hIQ in
/-- Cox 7.7, p.139: change the sign of the primitive relation to make its first coefficient
positive. -/
theorem exists_positive_normalized_relation [Algebra.IsQuadraticExtension ℚ K]
    (I : (FractionalIdeal O⁰ K)ˣ) :
    ∃ (α : Kˣ) (τ : K) (A B C : ℤ), 0 < A ∧ LinearIndependent ℚ ![1, τ] ∧
      (A : K) * τ ^ 2 + B * τ + C = 0 ∧
      Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1 ∧
      ((I : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
        (α : K) • Submodule.span ℤ ({1, τ} : Set K) := by
  obtain ⟨α, τ, hlin, hcoord⟩ := exists_normalized_basis O (I : FractionalIdeal O⁰ K) I.ne_zero
  obtain ⟨A, B, C, hA, hq, hprim⟩ := exists_primitive_quadratic_relation τ hlin
  rcases hA.lt_or_gt with hneg | hpos
  · refine ⟨α, τ, -A, -B, -C, by omega, hlin, ?_, ?_, hcoord⟩
    · push_cast
      linear_combination -hq
    · simpa only [Int.natAbs_neg] using hprim
  · exact ⟨α, τ, A, B, C, hpos, hlin, hq, hprim, hcoord⟩

omit hNF hO in
/-- Cox Exercise 7.12, used on p.139: a nonreal quadratic root has negative discriminant. -/
theorem normalized_discriminant_neg (τ : K) (A B C : ℤ) (hA : A ≠ 0)
    (hlin : LinearIndependent ℚ ![1, τ])
    (hq : (A : K) * τ ^ 2 + B * τ + C = 0) : B ^ 2 - 4 * A * C < 0 := by
  by_contra hD
  have hD' : 0 ≤ B ^ 2 - 4 * A * C := not_lt.mp hD
  have hqC : (A : ℂ) * (τ : ℂ) ^ 2 + B * (τ : ℂ) + C = 0 := by
    simpa using congrArg (fun w : K => (w : ℂ)) hq
  set w : ℂ := 2 * A * (τ : ℂ) + B with hwdef
  have hw : w ^ 2 = ((B ^ 2 - 4 * A * C : ℤ) : ℂ) := by
    rw [hwdef]
    push_cast
    linear_combination (4 * A : ℂ) * hqC
  rw [sq w] at hw
  have h1 := congrArg Complex.im hw
  have h2 := congrArg Complex.re hw
  simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_im, Complex.intCast_re] at h1 h2
  have hDR : (0 : ℝ) ≤ ((B ^ 2 - 4 * A * C : ℤ) : ℝ) := by exact_mod_cast hD'
  have hwim : w.im = 0 := by
    by_contra hne
    have hre : w.re = 0 := by
      have h3 : w.re * w.im = 0 := by linarith
      exact (mul_eq_zero.mp h3).resolve_right hne
    rw [hre] at h2
    have : 0 < w.im * w.im := mul_self_pos.mpr hne
    linarith
  have hτim : (τ : ℂ).im = 0 := by
    have h4 : w.im = 2 * A * (τ : ℂ).im := by simp [hwdef]
    rw [hwim] at h4
    have hA' : (2 * A : ℝ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero hA
    exact (mul_eq_zero.mp h4.symm).resolve_left hA'
  obtain ⟨q, hq'⟩ := (real_mem_iff_rat τ).mp hτim
  rw [LinearIndependent.pair_iff] at hlin
  have h5 := hlin q (-1) (by rw [hq']; simp [Rat.smul_def])
  norm_num at h5

omit hNF hO hIQ in
/-- Cox 7.5 and 7.7: the multiplier ring identifies the normalized order lattice. -/
theorem order_eq_normalized_multiplier [Algebra.IsQuadraticExtension ℚ K]
    (I : (FractionalIdeal O⁰ K)ˣ)
    (α : Kˣ) (τ : K) (A B C : ℤ) (hA : A ≠ 0)
    (hlin : LinearIndependent ℚ ![1, τ])
    (hq : (A : K) * τ ^ 2 + B * τ + C = 0)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1)
    (hcoord : ((I : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
      (α : K) • Submodule.span ℤ ({1, τ} : Set K)) :
    O.toSubmodule = Submodule.span ℤ ({1, (A : K) * τ} : Set K) :=
  toSubmodule_eq_normalized_span O (I : FractionalIdeal O⁰ K) I.isUnit α τ A B C hA hlin hq hprim
    hcoord

omit hNF hO hIQ in
/-- Cox 7.7, p. 139: with a unimodular first column `(x, y)`, the new basis vector
`x - yτ` is nonzero. -/
theorem sub_mul_ne_zero_of_det {F : Type*} [Field F] [CharZero F] (τ : F)
    (hlin : LinearIndependent ℚ ![1, τ]) (x y r s : ℤ) (hdet : x * s - y * r = 1) :
    (x : F) - y * τ ≠ 0 := by
  intro h
  rw [LinearIndependent.pair_iff] at hlin
  have h2 := hlin x (-y) (by
    simp only [Rat.smul_def, mul_one, Rat.cast_intCast, Rat.cast_neg]
    linear_combination h)
  have hx : x = 0 := by exact_mod_cast h2.1
  have hy : y = 0 := by exact_mod_cast (by linarith [h2.2] : (y : ℚ) = 0)
  rw [hx, hy] at hdet
  simp at hdet

omit hNF hO hIQ in
/-- Cox 7.7, pp.137–139: the determinant-one substitution changes the normalized basis. -/
theorem normalized_unimodular_span {F : Type*} [Field F] [CharZero F]
    (τ : F) (hlin : LinearIndependent ℚ ![1, τ])
    (x y r s : ℤ) (hdet : x * s - y * r = 1) :
    Submodule.span ℤ ({1, τ} : Set F) =
      ((x : F) - y * τ) •
        Submodule.span ℤ ({1, ((s : F) * τ - r) / ((x : F) - y * τ)} : Set F) := by
  have hne := sub_mul_ne_zero_of_det τ hlin x y r s hdet
  rw [Submodule.smul_span, Set.smul_set_insert, Set.smul_set_singleton, smul_eq_mul, mul_one,
    smul_eq_mul, mul_div_cancel₀ _ hne]
  have hdet' : (x : F) * s - y * r = 1 := by exact_mod_cast hdet
  apply le_antisymm <;> rw [Submodule.span_le] <;> intro z hz <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz <;> rcases hz with h | h <;>
    rw [h]
  · exact Submodule.mem_span_pair.mpr ⟨s, y, by simp [zsmul_eq_mul]; linear_combination hdet'⟩
  · exact Submodule.mem_span_pair.mpr ⟨r, x, by simp [zsmul_eq_mul]; linear_combination τ * hdet'⟩
  · exact Submodule.mem_span_pair.mpr ⟨x, -y, by simp [zsmul_eq_mul]; ring⟩
  · exact Submodule.mem_span_pair.mpr ⟨-r, s, by simp [zsmul_eq_mul]; ring⟩

omit hNF hO hIQ in
/-- Cox 7.7 and Lemma 2.3: transform the polynomial relation along the same basis change. -/
theorem normalized_unimodular_relation {F : Type*} [Field F] [CharZero F]
    (τ : F) (A B C x y r s : ℤ)
    (hlin : LinearIndependent ℚ ![1, τ]) (hdet : x * s - y * r = 1)
    (hq : (A : F) * τ ^ 2 + B * τ + C = 0) :
    let z := ((s : F) * τ - r) / ((x : F) - y * τ)
    ((A * x ^ 2 + B * x * y + C * y ^ 2 : ℤ) : F) * z ^ 2 +
      ((2 * A * x * r + B * (x * s + y * r) + 2 * C * y * s : ℤ) : F) * z +
      ((A * r ^ 2 + B * r * s + C * s ^ 2 : ℤ) : F) = 0 := by
  intro z
  have hne := sub_mul_ne_zero_of_det τ hlin x y r s hdet
  have hdet' : (x : F) * s - y * r = 1 := by exact_mod_cast hdet
  set u : F := (s : F) * τ - r
  set w : F := (x : F) - y * τ
  have h1 : τ = r * w + x * u := by
    simp only [u, w]
    linear_combination (-τ) * hdet'
  have h2 : (1 : F) = s * w + y * u := by
    simp only [u, w]
    linear_combination (-1 : F) * hdet'
  have key : (A : F) * (r * w + x * u) ^ 2 + B * (r * w + x * u) * (s * w + y * u) +
      C * (s * w + y * u) ^ 2 = 0 := by
    rw [← h1, ← h2]
    linear_combination hq
  have key' : ((A * x ^ 2 + B * x * y + C * y ^ 2 : ℤ) : F) * u ^ 2 +
      ((2 * A * x * r + B * (x * s + y * r) + 2 * C * y * s : ℤ) : F) * u * w +
      ((A * r ^ 2 + B * r * s + C * s ^ 2 : ℤ) : F) * w ^ 2 = 0 := by
    push_cast
    linear_combination key
  have hz : z = u / w := rfl
  rw [hz, div_pow]
  field_simp
  linear_combination key'

omit hNF hO hIQ in
/-- Cox p.140: the first basis coefficient identifies the quotient with `Z/AZ`. -/
theorem normalized_lattice_quotient_equiv (τ : K) (A : ℤ) (_hA : A ≠ 0)
    (hlin : LinearIndependent ℚ ![1, τ]) (a : Ideal O)
    (hOspan : O.toSubmodule = Submodule.span ℤ ({1, (A : K) * τ} : Set K))
    (hcoord : ((a : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
      (A : K) • Submodule.span ℤ ({1, τ} : Set K)) :
    Nonempty ((O ⧸ a) ≃+ ZMod A.natAbs) := by
  have hliZ : LinearIndependent ℤ ![(1 : K), τ] := LinearIndependent.restrict_scalars' (R := ℤ) hlin
  have hcO : ∀ x : O, ∃ m n : ℤ, (x : K) = m + n * (A * τ) := fun x => by
    have hx : (x : K) ∈ Submodule.span ℤ ({1, (A : K) * τ} : Set K) := by
      rw [← hOspan]
      exact x.2
    obtain ⟨m, n, h⟩ := Submodule.mem_span_pair.mp hx
    exact ⟨m, n, by rw [← h]; simp [zsmul_eq_mul]⟩
  have huniq : ∀ m n m' n' : ℤ, (m : K) + n * (A * τ) = m' + n' * (A * τ) → m = m' := by
    intro m n m' n' h
    refine (hliZ.eq_of_pair (s := m) (t := n * A) (s' := m') (t' := n' * A) ?_).1
    simp only [zsmul_eq_mul, mul_one]
    push_cast
    linear_combination h
  have hmemK : ∀ y : K, y ∈ (a : FractionalIdeal O⁰ K) ↔ ∃ p q : ℤ, y = A * (p + q * τ) := by
    intro y
    rw [← FractionalIdeal.mem_coe, ← Submodule.restrictScalars_mem ℤ, hcoord,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.mp hz
      exact ⟨p, q, by simp [smul_eq_mul, zsmul_eq_mul]⟩
    · rintro ⟨p, q, rfl⟩
      exact ⟨p + q * τ, Submodule.mem_span_pair.mpr ⟨p, q, by simp [zsmul_eq_mul]⟩, rfl⟩
  have hmem : ∀ x : O, x ∈ a ↔ ∃ p q : ℤ, (x : K) = A * (p + q * τ) := by
    intro x
    rw [← hmemK, FractionalIdeal.mem_coeIdeal]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨x', hx', e⟩ => by rwa [← Subtype.ext e]⟩
  let ψ : O →+ ZMod A.natAbs :=
    { toFun := fun x => ((hcO x).choose : ZMod A.natAbs)
      map_zero' := by
        obtain ⟨n, hn⟩ := (hcO 0).choose_spec
        have h0 : (hcO 0).choose = 0 := huniq _ n 0 0 (by rw [← hn]; simp)
        simp [h0]
      map_add' := fun x y => by
        obtain ⟨nx, hx⟩ := (hcO x).choose_spec
        obtain ⟨ny, hy⟩ := (hcO y).choose_spec
        obtain ⟨nxy, hxy⟩ := (hcO (x + y)).choose_spec
        have hsum : ((x + y : O) : K) = (x : K) + (y : K) := rfl
        have h : (hcO (x + y)).choose = (hcO x).choose + (hcO y).choose :=
          huniq _ nxy _ (nx + ny) (by push_cast; linear_combination -hxy + hsum + hx + hy)
        simp only [h, Int.cast_add] }
  have hψ : ∀ (x : O) (m n : ℤ), (x : K) = m + n * (A * τ) → ψ x = m := by
    intro x m n hx
    obtain ⟨n', hn'⟩ := (hcO x).choose_spec
    change (((hcO x).choose : ℤ) : ZMod A.natAbs) = m
    rw [huniq _ n' m n (hn'.symm.trans hx)]
  have hker : a.toAddSubgroup = ψ.ker := by
    ext x
    obtain ⟨m, n, hx⟩ := hcO x
    rw [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker, hψ x m n hx,
      ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd, hmem]
    constructor
    · rintro ⟨p, q, hpq⟩
      exact ⟨p, huniq m n (A * p) q (by rw [← hx, hpq]; push_cast; ring)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, n, by rw [hx]; push_cast; ring⟩
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨(k : O), hψ _ k 0 (by simp)⟩
  exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective ψ hsurj)⟩

omit hIQ in
/-- Cox 7.7 and (7.16): `A[1,τ]` is an integral representative of norm `A`. -/
theorem exists_normalized_integral_ideal [Algebra.IsQuadraticExtension ℚ K] (τ : K) (A B C : ℤ)
    (hA : 0 < A)
    (hlin : LinearIndependent ℚ ![1, τ])
    (hq : (A : K) * τ ^ 2 + B * τ + C = 0)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1)
    (hOspan : O.toSubmodule = Submodule.span ℤ ({1, (A : K) * τ} : Set K)) :
    ∃ a : Ideal O, ∃ _ha : IsUnit (a : FractionalIdeal O⁰ K),
      ((a : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
        (A : K) • Submodule.span ℤ ({1, τ} : Set K) ∧ idealNorm O a = A.natAbs := by
  set S := Submodule.span ℤ ({1, τ} : Set K) with hSdef
  have hAK : (A : K) ≠ 0 := by exact_mod_cast hA.ne'
  have hmult : ∀ x : K, x ∈ O ↔ ∀ z ∈ S, x * z ∈ S := fun x => by
    rw [← Subalgebra.mem_toSubmodule, hOspan,
      normalized_multiplier_iff τ hlin A B C hA.ne' hq hprim x]
  have hsub : ∀ y ∈ (A : K) • S, y ∈ O := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    obtain ⟨m, n, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [← Subalgebra.mem_toSubmodule, hOspan]
    exact Submodule.mem_span_pair.mpr ⟨A * m, n, by simp [smul_eq_mul, zsmul_eq_mul]; ring⟩
  let a : Ideal O :=
    { carrier := {x | (x : K) ∈ (A : K) • S}
      add_mem' := fun {x y} hx hy => by
        change ((x + y : O) : K) ∈ (A : K) • S
        rw [Subalgebra.coe_add]
        exact Submodule.add_mem _ hx hy
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        obtain ⟨z, hz, hzx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
        refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
          ⟨(c : K) * z, (hmult c).mp c.2 z hz, ?_⟩
        rw [smul_eq_mul] at hzx ⊢
        change _ = (c : K) * (x : K)
        rw [← hzx]
        ring }
  have hcoord : ((a : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ = (A : K) • S := by
    ext y
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hsub y hy⟩, hy, rfl⟩
  have hm : ∀ y : K, y ∈ (a : FractionalIdeal O⁰ K) ↔ ∃ z ∈ S, (A : K) * z = y := fun y => by
    rw [← FractionalIdeal.mem_coe, ← Submodule.restrictScalars_mem ℤ, hcoord,
      Submodule.mem_smul_pointwise_iff_exists]
    simp only [smul_eq_mul]
  have hproper : IsProper O (a : FractionalIdeal O⁰ K) := by
    refine ⟨fun h0 => hAK ?_, fun x => ?_⟩
    · have hAmem : (A : K) ∈ (a : FractionalIdeal O⁰ K) :=
        (hm _).mpr ⟨1, Submodule.subset_span (by simp), mul_one _⟩
      rwa [h0, FractionalIdeal.mem_zero_iff] at hAmem
    · rw [hmult]
      constructor
      · intro h z hz
        obtain ⟨w, hw, hw'⟩ := (hm _).mp (h _ ((hm _).mpr ⟨z, hz, rfl⟩))
        have e : x * z = w := mul_left_cancel₀ hAK (by rw [hw']; ring)
        rwa [e]
      · intro h y hy
        obtain ⟨z, hz, rfl⟩ := (hm y).mp hy
        exact (hm _).mpr ⟨x * z, h z hz, by ring⟩
  refine ⟨a, isUnit_of_isProper O hproper, hcoord, ?_⟩
  obtain ⟨e⟩ := normalized_lattice_quotient_equiv O τ A hA.ne' hlin a hOspan hcoord
  rw [idealNorm, Nat.card_congr e.toEquiv, Nat.card_zmod]

omit hNF hO hIQ in
/-- Cox 7.7, p. 139: a determinant-one substitution keeps the new basis vector irrational. -/
theorem linearIndependent_unimodular {F : Type*} [Field F] [CharZero F] (τ : F)
    (hlin : LinearIndependent ℚ ![1, τ]) (x y r s : ℤ) (hdet : x * s - y * r = 1) :
    LinearIndependent ℚ ![1, ((s : F) * τ - r) / ((x : F) - y * τ)] := by
  have hw := sub_mul_ne_zero_of_det τ hlin x y r s hdet
  have hdet' : (x : ℚ) * s - y * r = 1 := by exact_mod_cast hdet
  rw [LinearIndependent.pair_iff] at hlin ⊢
  intro a b hab
  simp only [Rat.smul_def, mul_one] at hab
  have e : (b : F) * (((s : F) * τ - r) / ((x : F) - y * τ)) * ((x : F) - y * τ) =
      b * ((s : F) * τ - r) := by
    rw [mul_assoc, div_mul_cancel₀ _ hw]
  have hab' : (a : F) * ((x : F) - y * τ) + b * ((s : F) * τ - r) = 0 := by
    linear_combination ((x : F) - y * τ) * hab - e
  have h2 := hlin (a * x - b * r) (b * s - a * y) (by
    simp only [Rat.smul_def, mul_one]
    push_cast
    linear_combination hab')
  have ha : a = 0 := by linear_combination (s : ℚ) * h2.1 + r * h2.2 - a * hdet'
  have hb : b = 0 := by linear_combination (y : ℚ) * h2.1 + x * h2.2 - b * hdet'
  exact ⟨ha, hb⟩

omit hIQ in
/-- Cox, §7.B: lattices `α[1, τ]` and `β[1, τ]` with the same `τ` lie in the same class. -/
theorem idealClass_eq_of_coord (I J : (FractionalIdeal O⁰ K)ˣ) (α β : Kˣ) (τ : K)
    (hI : ((I : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
      (α : K) • Submodule.span ℤ ({1, τ} : Set K))
    (hJ : ((J : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
      (β : K) • Submodule.span ℤ ({1, τ} : Set K)) :
    idealClass O I = idealClass O J := by
  have hmem : ∀ (L : FractionalIdeal O⁰ K) (γ : K),
      (L : Submodule O K).restrictScalars ℤ = γ • Submodule.span ℤ ({1, τ} : Set K) →
      ∀ y : K, y ∈ L ↔ ∃ z ∈ Submodule.span ℤ ({1, τ} : Set K), γ * z = y := by
    intro L γ hL y
    rw [← FractionalIdeal.mem_coe, ← Submodule.restrictScalars_mem ℤ, hL,
      Submodule.mem_smul_pointwise_iff_exists]
    simp only [smul_eq_mul]
  rw [idealClass_eq_iff_exists_principal]
  refine ⟨β * α⁻¹, Units.ext (FractionalIdeal.coeToSubmodule_injective ?_)⟩
  ext y
  rw [Units.val_mul, coe_toPrincipalIdeal, mul_comm, FractionalIdeal.mem_coe,
    FractionalIdeal.mem_singleton_mul, FractionalIdeal.mem_coe, hmem _ _ hJ]
  constructor
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨z, hz, rfl⟩ := (hmem _ _ hI y').mp hy'
    exact ⟨z, hz, by simp [mul_assoc]⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(α : K) * z, (hmem _ _ hI _).mpr ⟨z, hz, rfl⟩, by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp⟩

/-- Cox 7.7(iii), p.141: a proper form value is a norm in the corresponding ideal class. -/
theorem exists_ideal_norm_of_proper_representation (I : (FractionalIdeal O⁰ K)ˣ)
    (α : Kˣ) (τ : K) (A B C : ℤ) (hA : 0 < A)
    (hlin : LinearIndependent ℚ ![1, τ])
    (hq : (A : K) * τ ^ 2 + B * τ + C = 0)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1)
    (hcoord : ((I : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
      (α : K) • Submodule.span ℤ ({1, τ} : Set K))
    (x y : ℤ) (hxy : IsCoprime x y) :
    ∃ a : Ideal O, ∃ ha : IsUnit (a : FractionalIdeal O⁰ K),
      idealClass O (integralIdealUnit O a ha) = idealClass O I ∧
      idealNorm O a = (A * x ^ 2 + B * x * y + C * y ^ 2).natAbs := by
  obtain ⟨r, s, hdet⟩ := BinaryQuadratic.exists_unimodular_completion x y hxy
  have hw := sub_mul_ne_zero_of_det τ hlin x y r s hdet
  have hq' := normalized_unimodular_relation τ A B C x y r s hlin hdet hq
  have hprim' := BinaryQuadratic.transformed_primitive A B C x y r s hprim hdet
  have hlin' := linearIndependent_unimodular τ hlin x y r s hdet
  have hxy0 : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    rw [h.1, h.2] at hdet
    simp at hdet
  have hApos : 0 < A * x ^ 2 + B * x * y + C * y ^ 2 :=
    BinaryQuadratic.value_pos A B C x y hA (normalized_discriminant_neg τ A B C hA.ne' hlin hq)
      hxy0
  have hcoord' : ((I : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
      ((α * Units.mk0 _ hw : Kˣ) : K) •
        Submodule.span ℤ ({1, ((s : K) * τ - r) / ((x : K) - y * τ)} : Set K) := by
    rw [hcoord, normalized_unimodular_span τ hlin x y r s hdet, smul_smul_submodule, Units.val_mul,
      Units.val_mk0]
  have hOspan := order_eq_normalized_multiplier O I _ _ _ _ _ hApos.ne' hlin' hq' hprim' hcoord'
  obtain ⟨a, ha, hacoord, hanorm⟩ :=
    exists_normalized_integral_ideal O _ _ _ _ hApos hlin' hq' hprim' hOspan
  refine ⟨a, ha, idealClass_eq_of_coord O _ I
    (Units.mk0 ((A * x ^ 2 + B * x * y + C * y ^ 2 : ℤ) : K) (by exact_mod_cast hApos.ne')) _ _
    (by rw [coe_integralIdealUnit, Units.val_mk0]; exact hacoord) hcoord', hanorm⟩

end Cox.Order
