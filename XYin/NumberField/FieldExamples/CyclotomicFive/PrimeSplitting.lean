/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import XYin.NumberField.FieldExamples.Common
import XYin.NumberField.FieldExamples.CyclotomicFive.Discriminant

/-!
# `ℚ(ζ₅)` PrimeSplitting

Prime splitting, Kummer-Dedekind computations, ramification, and different-related statements.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

noncomputable section

open Module Polynomial
open NumberField.FieldExamples
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicFive
section PrivateMachinery

private theorem gen_eq_zetaInt : zeta_isPrimitiveRoot.integralPowerBasis.gen = zetaInt :=
  zeta_isPrimitiveRoot.integralPowerBasis_gen

private theorem autEq' (σ : K ≃ₐ[ℚ] K) : σ = 1 ∨ σ = sigmaTwo ∨ σ = sigmaThree ∨ σ = sigmaFour :=
  aut_eq σ

/-- The product of the four Galois conjugates computes the field norm. -/
private theorem prod_aut_apply (x : K) :
    ∏ σ : K ≃ₐ[ℚ] K, σ x = x * sigmaTwo x * sigmaThree x * sigmaFour x := by
  classical
  have hne : ∀ (i j : ℕ) (σ τ : K ≃ₐ[ℚ] K), i < 5 → j < 5 → i ≠ j →
      σ ζ = ζ ^ i → τ ζ = ζ ^ j → σ ≠ τ := fun i j σ τ hi hj hij hσ hτ hστ =>
    hij (zeta_isPrimitiveRoot.pow_inj hi hj (by rw [← hσ, ← hτ, hστ]))
  have hid : (1 : K ≃ₐ[ℚ] K) ζ = ζ ^ 1 := by rw [pow_one]; rfl
  have h1 : (1 : K ≃ₐ[ℚ] K) ≠ sigmaTwo :=
    hne 1 2 _ _ (by norm_num) (by norm_num) (by norm_num) hid sigmaTwo_apply_zeta
  have h2 : (1 : K ≃ₐ[ℚ] K) ≠ sigmaThree :=
    hne 1 3 _ _ (by norm_num) (by norm_num) (by norm_num) hid sigmaThree_apply_zeta
  have h3 : (1 : K ≃ₐ[ℚ] K) ≠ sigmaFour :=
    hne 1 4 _ _ (by norm_num) (by norm_num) (by norm_num) hid sigmaFour_apply_zeta
  have h4 : sigmaTwo ≠ sigmaThree := hne 2 3 _ _ (by norm_num) (by norm_num) (by norm_num)
    sigmaTwo_apply_zeta sigmaThree_apply_zeta
  have h5 : sigmaTwo ≠ sigmaFour := hne 2 4 _ _ (by norm_num) (by norm_num) (by norm_num)
    sigmaTwo_apply_zeta sigmaFour_apply_zeta
  have h6 : sigmaThree ≠ sigmaFour := hne 3 4 _ _ (by norm_num) (by norm_num) (by norm_num)
    sigmaThree_apply_zeta sigmaFour_apply_zeta
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, sigmaTwo, sigmaThree, sigmaFour} := by
    refine (Finset.eq_univ_iff_forall.mpr fun σ => ?_).symm
    rcases autEq' σ with h | h | h | h <;> simp [h]
  rw [huniv, Finset.prod_insert (by simp [h1, h2, h3]), Finset.prod_insert (by simp [h4, h5]),
    Finset.prod_pair h6]
  simp [mul_assoc]

private theorem intNorm_eq (x : 𝓞 K) (n : ℤ)
    (h : algebraMap (𝓞 K) K x * sigmaTwo (algebraMap (𝓞 K) K x) *
      sigmaThree (algebraMap (𝓞 K) K x) * sigmaFour (algebraMap (𝓞 K) K x) = (n : K)) :
    Algebra.norm ℤ x = n := by
  haveI := IsCyclotomicExtension.isGalois {5} ℚ K
  have h2 : Algebra.norm ℚ (algebraMap (𝓞 K) K x) = (n : ℚ) := by
    apply (algebraMap ℚ K).injective
    rw [eq_ratCast (algebraMap ℚ K) (n : ℚ), Algebra.norm_eq_prod_automorphisms,
      prod_aut_apply, h]
    push_cast
    ring
  exact_mod_cast (Algebra.coe_norm_int x).trans h2

private theorem minpoly_gen_eq :
    minpoly ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen =
      Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X +
        Polynomial.C 1 := by
  set q : Polynomial ℤ := Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 +
    Polynomial.X + Polynomial.C 1 with hq
  have hdeg : (minpoly ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen).natDegree = 4 := by
    rw [zeta_isPrimitiveRoot.integralPowerBasis.natDegree_minpoly,
      zeta_isPrimitiveRoot.integralPowerBasis_dim]
    rfl
  refine (minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly ?_ ?_ ?_).symm
  · rw [hq]
    monicity!
  · rw [gen_eq_zetaInt, hq]
    simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
    linear_combination zetaInt_sum_eq_zero
  · rw [hq, Polynomial.degree_eq_natDegree (minpoly.ne_zero
      zeta_isPrimitiveRoot.integralPowerBasis.isIntegral_gen), hdeg]
    compute_degree!

private theorem isMaximal_span_pair (p : ℕ) [Fact p.Prime] (r : ℤ)
    (hr : ((r : ZMod p)) ^ 4 + ((r : ZMod p)) ^ 3 + ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    (Ideal.span {(p : 𝓞 K), zetaInt - (r : 𝓞 K)}).IsMaximal := by
  rw [← gen_eq_zetaInt]
  exact NumberField.FieldExamples.isMaximal_span_gen_sub
    zeta_isPrimitiveRoot.integralPowerBasis p r
    (by rw [minpoly_gen_eq]
        simpa using hr)

private theorem absNorm_span_pair (p : ℕ) (r : ℤ)
    (hr : ((r : ZMod p)) ^ 4 + ((r : ZMod p)) ^ 3 + ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K), zetaInt - (r : 𝓞 K)}) = p := by
  rw [← gen_eq_zetaInt]
  exact NumberField.FieldExamples.absNorm_span_gen_sub
    zeta_isPrimitiveRoot.integralPowerBasis p r
    (by rw [minpoly_gen_eq]
        simpa using hr)

end PrivateMachinery

/-- The norm of `1 - ζ` is `Φ₅(1) = 5`: the standard generator of the unique prime above
`5`. -/
theorem norm_one_sub_zeta : Algebra.norm ℚ (1 - ζ) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := zeta_isPrimitiveRoot.sub_one_norm_isPrimePow
    ((by norm_num : Nat.Prime 5).isPrimePow)
    (Polynomial.cyclotomic.irreducible_rat (by norm_num)) (by norm_num)
  rw [show (1 : K) - ζ = (-1 : K) * (ζ - 1) by ring, map_mul,
    show (-1 : K) = algebraMap ℚ K (-1) by norm_num, Algebra.norm_algebraMap,
    degree_eq_four, h, show Nat.minFac 5 = 5 by norm_num]
  norm_num

/-- The norm of `1 + ζ` is `Φ₅(-1) = 1`: hence `1 + ζ` is a unit of `ℤ[ζ]` (a *cyclotomic
unit*). -/
theorem norm_one_add_zeta : Algebra.norm ℚ (1 + ζ) = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h2 : IsPrimitiveRoot (ζ ^ 2) 5 := zeta_isPrimitiveRoot.pow_of_coprime 2 (by norm_num)
  have hn2 : Algebra.norm ℚ (1 - ζ ^ 2) = 5 := by
    have h := h2.sub_one_norm_isPrimePow ((by norm_num : Nat.Prime 5).isPrimePow)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num)) (by norm_num)
    rw [show (1 : K) - ζ ^ 2 = (-1 : K) * (ζ ^ 2 - 1) by ring, map_mul,
      show (-1 : K) = algebraMap ℚ K (-1) by norm_num, Algebra.norm_algebraMap,
      degree_eq_four, h, show Nat.minFac 5 = 5 by norm_num]
    norm_num
  rw [show (1 : K) - ζ ^ 2 = (1 - ζ) * (1 + ζ) by ring, map_mul, norm_one_sub_zeta] at hn2
  linarith

/-- The quartic norm form of `ℚ(ζ₅)` in the integral basis `1, ζ, ζ², ζ³`. -/
def normForm {R : Type*} [CommRing R] (a b c d : R) : R :=
  a ^ 4 - a ^ 3 * b - a ^ 3 * c - a ^ 3 * d +
    a ^ 2 * b ^ 2 + 2 * a ^ 2 * b * c + 2 * a ^ 2 * b * d +
    a ^ 2 * c ^ 2 - 3 * a ^ 2 * c * d + a ^ 2 * d ^ 2 -
    a * b ^ 3 - 3 * a * b ^ 2 * c + 2 * a * b ^ 2 * d +
    2 * a * b * c ^ 2 - a * b * c * d - 3 * a * b * d ^ 2 -
    a * c ^ 3 + 2 * a * c ^ 2 * d + 2 * a * c * d ^ 2 - a * d ^ 3 +
    b ^ 4 - b ^ 3 * c - b ^ 3 * d + b ^ 2 * c ^ 2 +
    2 * b ^ 2 * c * d + b ^ 2 * d ^ 2 - b * c ^ 3 -
    3 * b * c ^ 2 * d + 2 * b * c * d ^ 2 - b * d ^ 3 +
    c ^ 4 - c ^ 3 * d + c ^ 2 * d ^ 2 - c * d ^ 3 + d ^ 4

private def zetaCoords (a b c d : ℚ) : K :=
  (a : K) + (b : K) * ζ + (c : K) * ζ ^ 2 + (d : K) * ζ ^ 3

private def normPairA (a b c d : ℚ) : K :=
  a ^ 2 - a * b + b ^ 2 - b * c + c ^ 2 - c * d + d ^ 2

private def normPairB (a b c d : ℚ) : K :=
  -c * d + b * d - b * c + a * d + a * c - a * b

private def normPairC (a b c d : ℚ) : K :=
  a ^ 2 - a * c - a * d + b ^ 2 - b * d + c ^ 2 + d ^ 2

private def zetaPair : K := ζ ^ 2 + ζ ^ 3

private theorem sig2_zetaCoords (a b c d : ℚ) :
    sigmaTwo (zetaCoords a b c d) =
      (a : K) - c + (d - c) * ζ + (b - c) * ζ ^ 2 - c * ζ ^ 3 := by
  simp only [zetaCoords, map_add, map_mul, map_pow, sigmaTwo_apply_zeta, map_ratCast]
  have h4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
    linear_combination zeta_sum_eq_zero
  have h6 : ζ ^ 6 = ζ := by linear_combination ζ * zeta_pow_five
  rw [show (ζ ^ 2) ^ 2 = ζ ^ 4 by ring,
    show (ζ ^ 2) ^ 3 = ζ ^ 6 by ring, h4, h6]
  ring

private theorem sig3_zetaCoords (a b c d : ℚ) :
    sigmaThree (zetaCoords a b c d) =
      (a : K) - d + (c - d) * ζ - d * ζ ^ 2 + (b - d) * ζ ^ 3 := by
  simp only [zetaCoords, map_add, map_mul, map_pow, map_ratCast, sigmaThree_apply_zeta]
  have h4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
    linear_combination zeta_sum_eq_zero
  have h6 : ζ ^ 6 = ζ := by linear_combination ζ * zeta_pow_five
  have h9 : ζ ^ 9 = ζ ^ 4 := by linear_combination ζ ^ 4 * zeta_pow_five
  rw [show (ζ ^ 3) ^ 2 = ζ ^ 6 by ring,
    show (ζ ^ 3) ^ 3 = ζ ^ 9 by ring, h6, h9, h4]
  ring

private theorem sig4_zetaCoords (a b c d : ℚ) :
    sigmaFour (zetaCoords a b c d) =
      (a : K) - b - b * ζ + (d - b) * ζ ^ 2 + (c - b) * ζ ^ 3 := by
  simp only [zetaCoords, map_add, map_mul, map_pow, sigmaFour_apply_zeta, map_ratCast]
  linear_combination (c * ζ ^ 3 + d * ζ ^ 2 * (ζ ^ 5 + 1)) * zeta_pow_five +
    b * zeta_sum_eq_zero

private theorem zetaCoords_mul_sig4 (a b c d : ℚ) :
    zetaCoords a b c d *
        ((a : K) - b - b * ζ + (d - b) * ζ ^ 2 + (c - b) * ζ ^ 3) =
      normPairA a b c d + normPairB a b c d * zetaPair := by
  dsimp [zetaCoords, normPairA, normPairB, zetaPair]
  have h4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
    linear_combination zeta_sum_eq_zero
  have h6 : ζ ^ 6 = ζ := by linear_combination ζ * zeta_pow_five
  ring_nf
  rw [zeta_pow_five, h6, h4]
  ring

private theorem sig2_zetaCoords_mul_sig3 (a b c d : ℚ) :
    ((a : K) - c + (d - c) * ζ + (b - c) * ζ ^ 2 - c * ζ ^ 3) *
        (a - d + (c - d) * ζ - d * ζ ^ 2 + (b - d) * ζ ^ 3) =
      normPairC a b c d - normPairB a b c d * zetaPair := by
  dsimp [normPairB, normPairC, zetaPair]
  have h4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
    linear_combination zeta_sum_eq_zero
  have h6 : ζ ^ 6 = ζ := by linear_combination ζ * zeta_pow_five
  ring_nf
  rw [zeta_pow_five, h6, h4]
  ring

private theorem normPair_mul_eq_normForm (a b c d : ℚ) :
    (normPairA a b c d + normPairB a b c d * zetaPair) *
        (normPairC a b c d - normPairB a b c d * zetaPair) =
      algebraMap ℚ K (normForm a b c d) := by
  have hT : zetaPair ^ 2 = 1 - zetaPair := by
    dsimp [zetaPair]
    have h4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
      linear_combination zeta_sum_eq_zero
    have h6 : ζ ^ 6 = ζ := by linear_combination ζ * zeta_pow_five
    ring_nf
    rw [zeta_pow_five, h6, h4]
    ring
  have hlin : normPairC a b c d - normPairA a b c d + normPairB a b c d = 0 := by
    dsimp [normPairA, normPairB, normPairC]
    ring
  calc
    (normPairA a b c d + normPairB a b c d * zetaPair) *
        (normPairC a b c d - normPairB a b c d * zetaPair) =
        normPairA a b c d * normPairC a b c d - normPairB a b c d ^ 2 +
          normPairB a b c d * zetaPair *
            (normPairC a b c d - normPairA a b c d + normPairB a b c d) -
          normPairB a b c d ^ 2 * (zetaPair ^ 2 - (1 - zetaPair)) := by ring
    _ = normPairA a b c d * normPairC a b c d - normPairB a b c d ^ 2 := by
      rw [hlin, hT]
      ring
    _ = algebraMap ℚ K (normForm a b c d) := by
      dsimp [normPairA, normPairB, normPairC, normForm]
      norm_num
      ring

/-- The field norm of `a + bζ + cζ² + dζ³` is the quartic norm form above. -/
theorem norm_eq_normForm (a b c d : ℚ) :
    Algebra.norm ℚ
        (a • (1 : K) + b • ζ + c • ζ ^ 2 + d • ζ ^ 3) =
      normForm a b c d := by
  have hx : a • (1 : K) + b • ζ + c • ζ ^ 2 + d • ζ ^ 3 =
      zetaCoords a b c d := by
    simp [zetaCoords, Algebra.smul_def]
  rw [hx]
  haveI := IsCyclotomicExtension.isGalois {5} ℚ K
  apply (algebraMap ℚ K).injective
  rw [Algebra.norm_eq_prod_automorphisms, prod_aut_apply, sig2_zetaCoords,
    sig3_zetaCoords, sig4_zetaCoords]
  rw [show zetaCoords a b c d *
        ((a - c) + (d - c) * ζ + (b - c) * ζ ^ 2 - c * ζ ^ 3) *
        ((a - d) + (c - d) * ζ - d * ζ ^ 2 + (b - d) * ζ ^ 3) *
        ((a - b) - b * ζ + (d - b) * ζ ^ 2 + (c - b) * ζ ^ 3) =
      (zetaCoords a b c d *
        ((a - b) - b * ζ + (d - b) * ζ ^ 2 + (c - b) * ζ ^ 3)) *
      (((a - c) + (d - c) * ζ + (b - c) * ζ ^ 2 - c * ζ ^ 3) *
        ((a - d) + (c - d) * ζ - d * ζ ^ 2 + (b - d) * ζ ^ 3)) by
      simp [zetaCoords]
      ring]
  rw [zetaCoords_mul_sig4, sig2_zetaCoords_mul_sig3, normPair_mul_eq_normForm]

/-- The integral norm of `a + bζ + cζ² + dζ³` is the same quartic form over `ℤ`. -/
theorem intNorm_eq_normForm (a b c d : ℤ) :
    Algebra.norm ℤ
        (a • (1 : 𝓞 K) + b • zetaInt + c • zetaInt ^ 2 + d • zetaInt ^ 3) =
      normForm a b c d := by
  let x : 𝓞 K := a • (1 : 𝓞 K) + b • zetaInt + c • zetaInt ^ 2 + d • zetaInt ^ 3
  change Algebra.norm ℤ x = normForm a b c d
  have hx : algebraMap (𝓞 K) K x =
      (a : ℚ) • (1 : K) + (b : ℚ) • ζ + (c : ℚ) • ζ ^ 2 + (d : ℚ) • ζ ^ 3 := by
    simp [x, zetaInt, Algebra.smul_def]
  have hcoe : ((Algebra.norm ℤ x : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap (𝓞 K) K x) :=
    Algebra.coe_norm_int x
  rw [hx, norm_eq_normForm] at hcoe
  norm_num [normForm] at hcoe ⊢
  exact_mod_cast hcoe

/-- The unit equation in `ℤ[ζ₅]`, written in the integral basis `1, ζ, ζ², ζ³`. -/
theorem isUnit_iff_normForm (a b c d : ℤ) :
    IsUnit (a • (1 : 𝓞 K) + b • zetaInt + c • zetaInt ^ 2 + d • zetaInt ^ 3) ↔
      (normForm a b c d).natAbs = 1 := by
  rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm, ← Algebra.coe_norm_int,
    intNorm_eq_normForm]
  constructor
  · intro h
    apply Nat.cast_injective (R := ℚ)
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact h
  · intro h
    have hq : ((normForm a b c d).natAbs : ℚ) = 1 := by exact_mod_cast h
    rwa [Nat.cast_natAbs, Int.cast_abs] at hq

/-- `5` is totally ramified: `(5) = (1 - ζ)⁴` as ideals of `𝓞 K` — ramification index
`e = 4` equals the full degree. -/
theorem span_five_eq : Ideal.span {(5 : 𝓞 K)} = Ideal.span {1 - zetaInt} ^ 4 := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
  refine ⟨⟨-zetaInt ^ 3 + zetaInt ^ 2 - zetaInt, zetaInt ^ 4 + 2 * zetaInt ^ 3 + zetaInt ^ 2,
    by linear_combination (-zetaInt ^ 3) * zetaInt_sum_eq_zero + zetaInt_pow_five,
    by linear_combination (-zetaInt ^ 3) * zetaInt_sum_eq_zero + zetaInt_pow_five⟩, ?_⟩
  linear_combination -zetaInt_sum_eq_zero

private theorem span_one_sub_zetaInt_eq_pair :
    Ideal.span {1 - zetaInt} = Ideal.span {((5 : ℕ) : 𝓞 K), zetaInt - ((1 : ℤ) : 𝓞 K)} := by
  refine le_antisymm ((Ideal.span_singleton_le_iff_mem _).mpr ?_) (Ideal.span_le.mpr ?_)
  · refine Ideal.mem_span_pair.mpr ⟨0, -1, ?_⟩
    push_cast
    ring
  · rintro y (rfl | rfl)
    · have h5 : ((5 : ℕ) : 𝓞 K) ∈ Ideal.span {(5 : 𝓞 K)} := by
        rw [Ideal.mem_span_singleton]
        exact ⟨1, by push_cast; ring⟩
      rw [span_five_eq] at h5
      exact Ideal.pow_le_self (by norm_num) h5
    · rw [SetLike.mem_coe, Ideal.mem_span_singleton]
      exact ⟨-1, by push_cast; ring⟩

/-- `(1 - ζ)` is a prime ideal — the unique prime of `𝓞 K` above `5`. -/
theorem isPrime_span_one_sub_zeta : (Ideal.span {1 - zetaInt}).IsPrime := by
  have hr : ((1 : ℤ) : ZMod 5) ^ 4 + ((1 : ℤ) : ZMod 5) ^ 3 + ((1 : ℤ) : ZMod 5) ^ 2 +
      ((1 : ℤ) : ZMod 5) + 1 = 0 := by decide
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [span_one_sub_zetaInt_eq_pair]
  exact (isMaximal_span_pair 5 1 hr).isPrime

/-- The prime `(1 - ζ)` above `5` has norm `5` (residue degree `f = 1`). -/
theorem absNorm_span_one_sub_zeta : Ideal.absNorm (Ideal.span {1 - zetaInt}) = 5 := by
  rw [span_one_sub_zetaInt_eq_pair]
  exact absNorm_span_pair 5 1 (by decide)

/-- The ramified prime `(1 - ζ)` lies over `(5)`. -/
theorem liesOver_span_one_sub_zeta :
    (Ideal.span {1 - zetaInt}).LiesOver (Ideal.span {(5 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_one_sub_zeta.ne_top
    (show Prime (5 : ℤ) by norm_num)]
  change (5 : 𝓞 K) ∈ Ideal.span {1 - zetaInt}
  have hmem : (5 : 𝓞 K) ∈ Ideal.span {(5 : 𝓞 K)} := Ideal.mem_span_singleton_self _
  rw [span_five_eq] at hmem
  exact Ideal.pow_le_self (by norm_num) hmem

/-- The ramified prime `(1 - ζ)` has inertia degree `1` over `5`. -/
theorem inertiaDeg_span_one_sub_zeta :
    (Ideal.span {(5 : ℤ)}).inertiaDeg (Ideal.span {1 - zetaInt}) = 1 := by
  haveI : (Ideal.span {1 - zetaInt}).LiesOver (Ideal.span {(5 : ℤ)}) :=
    liesOver_span_one_sub_zeta
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {1 - zetaInt})
    (p := 5) (by norm_num : Nat.Prime 5)
  rw [absNorm_span_one_sub_zeta] at h
  exact ((Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 5)).mp h.symm).2

/-- The ramified prime `(1 - ζ)` has ramification index `4` over `5`. -/
theorem ramificationIdx_span_one_sub_zeta :
    (Ideal.span {(5 : ℤ)}).ramificationIdx (Ideal.span {1 - zetaInt}) = 4 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(5 : 𝓞 K)} ≤ Ideal.span {1 - zetaInt} ^ 4
    rw [span_five_eq]
  · intro hle5
    have hdvd : Ideal.absNorm (Ideal.span {1 - zetaInt} ^ 5) ∣
        Ideal.absNorm (Ideal.span {((5 : ℤ) : 𝓞 K)}) := by
      simpa [Ideal.map_span, Set.image_singleton] using Ideal.absNorm_dvd_absNorm_of_le hle5
    have hnorm5 : Ideal.absNorm (Ideal.span {((5 : ℤ) : 𝓞 K)}) = 625 := by
      change Ideal.absNorm (Ideal.span {(5 : 𝓞 K)}) = 625
      have hfin : Module.finrank ℤ (𝓞 K) = 4 := by
        rw [Module.finrank_eq_card_basis concreteIntegralBasis, Fintype.card_fin]
      rw [Ideal.absNorm_span_singleton,
        show (5 : 𝓞 K) = algebraMap ℤ (𝓞 K) 5 from (map_ofNat _ 5).symm,
        Algebra.norm_algebraMap, hfin]
      rfl
    have hnormP5 : Ideal.absNorm (Ideal.span {1 - zetaInt} ^ 5) = 3125 := by
      rw [map_pow, absNorm_span_one_sub_zeta]
      norm_num
    rw [hnormP5, hnorm5] at hdvd
    norm_num at hdvd

/-- The inert prime `(2)` has norm `2⁴ = 16` (residue degree `f = 4`). -/
theorem absNorm_span_two : Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 16 := by
  have hfin : Module.finrank ℤ (𝓞 K) = 4 := by
    rw [Module.finrank_eq_card_basis concreteIntegralBasis, Fintype.card_fin]
  rw [Ideal.absNorm_span_singleton,
    show (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 from (map_ofNat _ 2).symm,
    Algebra.norm_algebraMap, hfin]
  rfl

private theorem quotient_zeta_ne_one_of_two_mem {M : Ideal (𝓞 K)} [M.IsMaximal]
    (h2mem : (2 : 𝓞 K) ∈ M) : Ideal.Quotient.mk M zetaInt ≠ 1 := by
  letI : Field ((𝓞 K) ⧸ M) := Ideal.Quotient.field M
  intro h1
  have hs := congrArg (Ideal.Quotient.mk M) zetaInt_sum_eq_zero
  rw [map_add, map_add, map_add, map_add, map_one, map_pow, map_pow, map_pow, map_zero,
    show Ideal.Quotient.mk M zetaInt = (1 : (𝓞 K) ⧸ M) from h1] at hs
  have h2q : (2 : (𝓞 K) ⧸ M) = 0 := by
    rw [show (2 : (𝓞 K) ⧸ M) = Ideal.Quotient.mk M 2 from (map_ofNat _ 2).symm,
      Ideal.Quotient.eq_zero_iff_mem]
    exact h2mem
  have h1q : (1 : (𝓞 K) ⧸ M) = 0 := by linear_combination hs - 2 * h2q
  exact one_ne_zero h1q

private theorem absNorm_maximal_over_span_two_eq_sixteen {M : Ideal (𝓞 K)}
    (hMmax : M.IsMaximal) (hMle : Ideal.span {(2 : 𝓞 K)} ≤ M) :
    Ideal.absNorm M = 16 := by
  haveI := hMmax
  letI : Field ((𝓞 K) ⧸ M) := Ideal.Quotient.field M
  have hdvd : Ideal.absNorm M ∣ 16 :=
    absNorm_span_two ▸ Ideal.absNorm_dvd_absNorm_of_le hMle
  have h2mem : (2 : 𝓞 K) ∈ M := hMle (Ideal.mem_span_singleton_self _)
  set ω : (𝓞 K) ⧸ M := Ideal.Quotient.mk M zetaInt with hω
  have hω5 : ω ^ 5 = 1 := by
    rw [hω, ← map_pow, zetaInt_pow_five, map_one]
  have hω1 : ω ≠ 1 := by
    simpa [hω] using quotient_zeta_ne_one_of_two_mem (M := M) h2mem
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have habs : Ideal.absNorm M = Nat.card ((𝓞 K) ⧸ M) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite ((𝓞 K) ⧸ M) := by
    refine Nat.finite_of_card_ne_zero fun h0 => ?_
    rw [habs, h0] at hdvd
    norm_num at hdvd
  haveI : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _
  have hM1 : Ideal.absNorm M ≠ 1 := by simpa [Ideal.absNorm_eq_one_iff] using hMmax.ne_top
  obtain ⟨k, hk4, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Ideal.absNorm M ∣ 2 ^ 4 from hdvd)
  have hcard_eq : Fintype.card ((𝓞 K) ⧸ M) = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card, ← habs, hkeq]
  have hpc := FiniteField.pow_card ω
  rw [hcard_eq] at hpc
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω5
    simp at hω5
  have hpow1 : ω ^ (2 ^ k - 1) = 1 := by
    refine mul_right_cancel₀ hω0 ?_
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
    exact hpc
  have h5dvd : (5 : ℕ) ∣ 2 ^ k - 1 := by
    have horderω : orderOf ω = 5 := orderOf_eq_prime hω5 hω1
    exact horderω ▸ orderOf_dvd_of_pow_eq_one hpow1
  rw [hkeq]
  interval_cases k
  · rw [hkeq] at hM1
    norm_num at hM1
  · norm_num at h5dvd
  · norm_num at h5dvd
  · norm_num at h5dvd
  · norm_num

/-- `2` is inert in `ℚ(ζ₅)`: `2` has order `4` in `(ℤ/5)ˣ`, so `Φ₅` is irreducible mod `2`. -/
theorem isPrime_span_two : (Ideal.span {(2 : 𝓞 K)}).IsPrime := by
  have htop : Ideal.span {(2 : 𝓞 K)} ≠ ⊤ := by
    intro h
    have h16 := absNorm_span_two
    rw [h, Ideal.absNorm_top] at h16
    norm_num at h16
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ htop
  have hM16 : Ideal.absNorm M = 16 := absNorm_maximal_over_span_two_eq_sixteen hMmax hMle
  have heq := eq_of_le_of_absNorm_eq hMle absNorm_span_two hM16 (by norm_num)
  rw [heq]
  exact hMmax.isPrime

/-- The inert prime `(2)` lies over `(2)`. -/
theorem liesOver_span_two :
    (Ideal.span {(2 : 𝓞 K)}).LiesOver (Ideal.span {(2 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_two.ne_top
    (show Prime (2 : ℤ) by norm_num)]
  change (2 : 𝓞 K) ∈ Ideal.span {(2 : 𝓞 K)}
  exact Ideal.mem_span_singleton_self _

/-- The inert prime `(2)` has inertia degree `4`. -/
theorem inertiaDeg_span_two :
    (Ideal.span {(2 : ℤ)}).inertiaDeg (Ideal.span {(2 : 𝓞 K)}) = 4 := by
  haveI : (Ideal.span {(2 : 𝓞 K)}).LiesOver (Ideal.span {(2 : ℤ)}) :=
    liesOver_span_two
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {(2 : 𝓞 K)})
    (p := 2) Nat.prime_two
  rw [absNorm_span_two] at h
  change 2 ^ 4 = 2 ^ (Ideal.span {(2 : ℤ)}).inertiaDeg
    (Ideal.span {(2 : 𝓞 K)}) at h
  exact Nat.pow_right_injective Nat.prime_two.one_lt h.symm

private theorem nineteen_x_eq : (19 : 𝓞 K) = (zetaInt ^ 2 + 5 * zetaInt + 1) *
    (5 * zetaInt ^ 4 + zetaInt ^ 2 + zetaInt) := by
  linear_combination (-(5 * zetaInt + 25)) * zetaInt_pow_five - 6 * zetaInt_sum_eq_zero

private theorem nineteen_y_eq : (19 : 𝓞 K) = (zetaInt ^ 2 - 4 * zetaInt + 1) *
    (-(4 * zetaInt ^ 4) + zetaInt ^ 2 + zetaInt) := by
  linear_combination (4 * zetaInt - 16) * zetaInt_pow_five + 3 * zetaInt_sum_eq_zero

private theorem span_pair_nineteen_left :
    Ideal.span {(19 : 𝓞 K), zetaInt ^ 2 + 5 * zetaInt + 1} =
      Ideal.span {zetaInt ^ 2 + 5 * zetaInt + 1} := by
  refine le_antisymm (Ideal.span_le.mpr ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · rintro w (rfl | rfl)
    · rw [SetLike.mem_coe, Ideal.mem_span_singleton]
      exact ⟨5 * zetaInt ^ 4 + zetaInt ^ 2 + zetaInt, nineteen_x_eq⟩
    · exact Ideal.mem_span_singleton_self _
  · exact Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩

private theorem span_pair_nineteen_right :
    Ideal.span {(19 : 𝓞 K), zetaInt ^ 2 + 15 * zetaInt + 1} =
      Ideal.span {zetaInt ^ 2 - 4 * zetaInt + 1} := by
  have h19 : (19 : 𝓞 K) ∈ Ideal.span {zetaInt ^ 2 - 4 * zetaInt + 1} := by
    rw [Ideal.mem_span_singleton]
    exact ⟨-(4 * zetaInt ^ 4) + zetaInt ^ 2 + zetaInt, nineteen_y_eq⟩
  refine le_antisymm (Ideal.span_le.mpr ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · rintro w (rfl | rfl)
    · exact h19
    · rw [SetLike.mem_coe, show zetaInt ^ 2 + 15 * zetaInt + 1 =
        (zetaInt ^ 2 - 4 * zetaInt + 1) + 19 * zetaInt from by ring]
      exact Ideal.add_mem _ (Ideal.mem_span_singleton_self _)
        (Ideal.mul_mem_right _ _ h19)
  · exact Ideal.mem_span_pair.mpr ⟨-zetaInt, 1, by ring⟩

private theorem absNorm_span_x :
    Ideal.absNorm (Ideal.span {zetaInt ^ 2 + 5 * zetaInt + 1}) = 361 := by
  have hn : Algebra.norm ℤ (zetaInt ^ 2 + 5 * zetaInt + 1) = 361 := by
    apply intNorm_eq
    have e0 : algebraMap (𝓞 K) K (zetaInt ^ 2 + 5 * zetaInt + 1) = ζ ^ 2 + 5 * ζ + 1 := by
      simp [map_add, map_mul, map_pow, map_one, map_ofNat, zetaInt]
    rw [e0]
    have e2 : sigmaTwo (ζ ^ 2 + 5 * ζ + 1) = ζ ^ 4 + 5 * ζ ^ 2 + 1 := by
      simp only [map_add, map_pow, map_mul, map_one, map_ofNat, sigmaTwo_apply_zeta]
      ring
    have e3 : sigmaThree (ζ ^ 2 + 5 * ζ + 1) = ζ + 5 * ζ ^ 3 + 1 := by
      simp only [map_add, map_pow, map_mul, map_one, map_ofNat, sigmaThree_apply_zeta]
      linear_combination ζ * zeta_pow_five
    have e4 : sigmaFour (ζ ^ 2 + 5 * ζ + 1) = ζ ^ 3 + 5 * ζ ^ 4 + 1 := by
      simp only [map_add, map_pow, map_mul, map_one, map_ofNat, sigmaFour_apply_zeta]
      linear_combination ζ ^ 3 * zeta_pow_five
    rw [e2, e3, e4]
    push_cast
    have h13 : (ζ ^ 2 + 5 * ζ + 1) * (ζ + 5 * ζ ^ 3 + 1) = 19 * ζ ^ 4 := by
      linear_combination 5 * zeta_pow_five + 6 * zeta_sum_eq_zero
    have h24 : (ζ ^ 4 + 5 * ζ ^ 2 + 1) * (ζ ^ 3 + 5 * ζ ^ 4 + 1) = 19 * ζ := by
      linear_combination (5 * ζ ^ 3 + ζ ^ 2 + 25 * ζ + 5) * zeta_pow_five +
        6 * zeta_sum_eq_zero
    calc (ζ ^ 2 + 5 * ζ + 1) * (ζ ^ 4 + 5 * ζ ^ 2 + 1) * (ζ + 5 * ζ ^ 3 + 1) *
        (ζ ^ 3 + 5 * ζ ^ 4 + 1)
        = ((ζ ^ 2 + 5 * ζ + 1) * (ζ + 5 * ζ ^ 3 + 1)) *
          ((ζ ^ 4 + 5 * ζ ^ 2 + 1) * (ζ ^ 3 + 5 * ζ ^ 4 + 1)) := by ring
      _ = (19 * ζ ^ 4) * (19 * ζ) := by rw [h13, h24]
      _ = 361 := by linear_combination 361 * zeta_pow_five
  rw [Ideal.absNorm_span_singleton, hn]
  rfl

private theorem absNorm_span_y :
    Ideal.absNorm (Ideal.span {zetaInt ^ 2 - 4 * zetaInt + 1}) = 361 := by
  have hn : Algebra.norm ℤ (zetaInt ^ 2 - 4 * zetaInt + 1) = 361 := by
    apply intNorm_eq
    have e0 : algebraMap (𝓞 K) K (zetaInt ^ 2 - 4 * zetaInt + 1) = ζ ^ 2 - 4 * ζ + 1 := by
      simp [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, zetaInt]
    rw [e0]
    have e2 : sigmaTwo (ζ ^ 2 - 4 * ζ + 1) = ζ ^ 4 - 4 * ζ ^ 2 + 1 := by
      simp only [map_add, map_sub, map_pow, map_mul, map_one, map_ofNat, sigmaTwo_apply_zeta]
      ring
    have e3 : sigmaThree (ζ ^ 2 - 4 * ζ + 1) = ζ - 4 * ζ ^ 3 + 1 := by
      simp only [map_add, map_sub, map_pow, map_mul, map_one, map_ofNat, sigmaThree_apply_zeta]
      linear_combination ζ * zeta_pow_five
    have e4 : sigmaFour (ζ ^ 2 - 4 * ζ + 1) = ζ ^ 3 - 4 * ζ ^ 4 + 1 := by
      simp only [map_add, map_sub, map_pow, map_mul, map_one, map_ofNat, sigmaFour_apply_zeta]
      linear_combination ζ ^ 3 * zeta_pow_five
    rw [e2, e3, e4]
    push_cast
    have h13 : (ζ ^ 2 - 4 * ζ + 1) * (ζ - 4 * ζ ^ 3 + 1) = 19 * ζ ^ 4 := by
      linear_combination (-4) * zeta_pow_five - 3 * zeta_sum_eq_zero
    have h24 : (ζ ^ 4 - 4 * ζ ^ 2 + 1) * (ζ ^ 3 - 4 * ζ ^ 4 + 1) = 19 * ζ := by
      linear_combination (-(4 * ζ ^ 3) + ζ ^ 2 + 16 * ζ - 4) * zeta_pow_five -
        3 * zeta_sum_eq_zero
    calc (ζ ^ 2 - 4 * ζ + 1) * (ζ ^ 4 - 4 * ζ ^ 2 + 1) * (ζ - 4 * ζ ^ 3 + 1) *
        (ζ ^ 3 - 4 * ζ ^ 4 + 1)
        = ((ζ ^ 2 - 4 * ζ + 1) * (ζ - 4 * ζ ^ 3 + 1)) *
          ((ζ ^ 4 - 4 * ζ ^ 2 + 1) * (ζ ^ 3 - 4 * ζ ^ 4 + 1)) := by ring
      _ = (19 * ζ ^ 4) * (19 * ζ) := by rw [h13, h24]
      _ = 361 := by linear_combination 361 * zeta_pow_five
  rw [Ideal.absNorm_span_singleton, hn]
  rfl

/-- There is no prime of `𝓞 K` with residue field `𝔽₁₉`: `Φ₅` has no root mod `19`. -/
private theorem absNorm_ne_nineteen (P : Ideal (𝓞 K)) : Ideal.absNorm P ≠ 19 := by
  intro hcard
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
  haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 K) ⧸ P) = 19 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) (by norm_num) hcard'
  obtain ⟨s, hs⟩ := e.surjective (Ideal.Quotient.mk P zetaInt)
  have hs5 : 1 + s + s ^ 2 + s ^ 3 + s ^ 4 = (0 : ZMod 19) := by
    apply e.injective
    rw [map_add, map_add, map_add, map_add, map_one, map_pow, map_pow, map_pow, hs, map_zero]
    have hmk := congrArg (Ideal.Quotient.mk P) zetaInt_sum_eq_zero
    rw [map_add, map_add, map_add, map_add, map_one, map_pow, map_pow, map_pow, map_zero] at hmk
    exact hmk
  clear hs
  revert s
  decide

private theorem isPrime_of_absNorm_361 {g : 𝓞 K}
    (h361 : Ideal.absNorm (Ideal.span {g}) = 361) : (Ideal.span {g}).IsPrime := by
  have htop : Ideal.span {g} ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at h361
    norm_num at h361
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ htop
  have hdvd : Ideal.absNorm M ∣ 361 := h361 ▸ Ideal.absNorm_dvd_absNorm_of_le hMle
  have hM1 : Ideal.absNorm M ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hMmax.ne_top
  have hM19 : Ideal.absNorm M ≠ 19 := absNorm_ne_nineteen M
  have hM361 : Ideal.absNorm M = 361 := by
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 19)).mp
      (show Ideal.absNorm M ∣ 19 ^ 2 from hdvd)
    interval_cases k
    · rw [pow_zero] at hkeq
      exact absurd hkeq hM1
    · rw [pow_one] at hkeq
      exact absurd hkeq hM19
    · rw [hkeq]
      norm_num
  have heq := eq_of_le_of_absNorm_eq hMle h361 hM361 (by norm_num)
  rw [heq]
  exact hMmax.isPrime

/-- `19` splits into two primes of degree `2`: `19 ≡ -1 (mod 5)` has order `2` in `(ℤ/5)ˣ`,
and `Φ₅ ≡ (X² + 5X + 1)(X² + 15X + 1) (mod 19)`. -/
theorem span_nineteen_eq :
    Ideal.span {(19 : 𝓞 K)} =
      Ideal.span {(19 : 𝓞 K), zetaInt ^ 2 + 5 * zetaInt + 1} *
        Ideal.span {(19 : 𝓞 K), zetaInt ^ 2 + 15 * zetaInt + 1} := by
  rw [span_pair_nineteen_left, span_pair_nineteen_right,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_span_singleton]
  refine ⟨⟨-zetaInt ^ 2, -zetaInt ^ 3, by linear_combination zetaInt_pow_five,
    by linear_combination zetaInt_pow_five⟩, ?_⟩
  change (19 : 𝓞 K) * (-zetaInt ^ 2) =
    (zetaInt ^ 2 + 5 * zetaInt + 1) * (zetaInt ^ 2 - 4 * zetaInt + 1)
  linear_combination -zetaInt_sum_eq_zero

/-- Both primes above `19` are prime ideals of norm `19² = 361`. -/
theorem isPrime_primesAboveNineteen :
    (Ideal.span {(19 : 𝓞 K), zetaInt ^ 2 + 5 * zetaInt + 1}).IsPrime ∧
      (Ideal.span {(19 : 𝓞 K), zetaInt ^ 2 + 15 * zetaInt + 1}).IsPrime := by
  constructor
  · rw [span_pair_nineteen_left]
    exact isPrime_of_absNorm_361 absNorm_span_x
  · rw [span_pair_nineteen_right]
    exact isPrime_of_absNorm_361 absNorm_span_y

private theorem elevenA : (ζ ^ 2 + ζ - 1) * (ζ ^ 3 + ζ - 1) = ζ ^ 4 - 2 * ζ + 2 := by
  linear_combination zeta_pow_five

private theorem elevenB : (ζ ^ 4 + ζ ^ 2 - 1) * (ζ ^ 4 + ζ ^ 3 - 1) = -(2 * ζ ^ 4) + ζ + 2 := by
  linear_combination (ζ ^ 3 + ζ ^ 2 + ζ + 1) * zeta_pow_five

private theorem elevenC : (ζ ^ 4 - 2 * ζ + 2) * (-(2 * ζ ^ 4) + ζ + 2) = 11 := by
  linear_combination (-(2 * ζ ^ 3) + 5) * zeta_pow_five - 2 * zeta_sum_eq_zero

/-- Norm computation shared by the four primes above `11`: the Galois orbit of `ζ² + ζ - 1`
is `{ζ² + ζ - 1, ζ⁴ + ζ² - 1, ζ³ + ζ - 1, ζ⁴ + ζ³ - 1}` with product `11`. -/
private theorem norm_eleven_orbit {w : 𝓞 K}
    (hw : algebraMap (𝓞 K) K w * sigmaTwo (algebraMap (𝓞 K) K w) *
      sigmaThree (algebraMap (𝓞 K) K w) * sigmaFour (algebraMap (𝓞 K) K w) =
        (ζ ^ 2 + ζ - 1) * (ζ ^ 3 + ζ - 1) * ((ζ ^ 4 + ζ ^ 2 - 1) * (ζ ^ 4 + ζ ^ 3 - 1))) :
    Ideal.absNorm (Ideal.span {w}) = 11 := by
  have hn : Algebra.norm ℤ w = 11 := by
    apply intNorm_eq
    rw [hw, elevenA, elevenB]
    push_cast
    linear_combination elevenC
  rw [Ideal.absNorm_span_singleton, hn]
  rfl

private theorem absNorm_span_u3 :
    Ideal.absNorm (Ideal.span {zetaInt ^ 2 + zetaInt - 1}) = 11 := by
  refine norm_eleven_orbit ?_
  have e0 : algebraMap (𝓞 K) K (zetaInt ^ 2 + zetaInt - 1) = ζ ^ 2 + ζ - 1 := by
    simp [map_add, map_sub, map_pow, map_one, zetaInt]
  rw [e0]
  have e2 : sigmaTwo (ζ ^ 2 + ζ - 1) = ζ ^ 4 + ζ ^ 2 - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sigmaTwo_apply_zeta]
    ring
  have e3 : sigmaThree (ζ ^ 2 + ζ - 1) = ζ ^ 3 + ζ - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sigmaThree_apply_zeta]
    linear_combination ζ * zeta_pow_five
  have e4 : sigmaFour (ζ ^ 2 + ζ - 1) = ζ ^ 4 + ζ ^ 3 - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sigmaFour_apply_zeta]
    linear_combination ζ ^ 3 * zeta_pow_five
  rw [e2, e3, e4]
  ring

private theorem absNorm_span_u4 :
    Ideal.absNorm (Ideal.span {zetaInt ^ 4 + zetaInt ^ 3 - 1}) = 11 := by
  refine norm_eleven_orbit ?_
  have e0 : algebraMap (𝓞 K) K (zetaInt ^ 4 + zetaInt ^ 3 - 1) = ζ ^ 4 + ζ ^ 3 - 1 := by
    simp [map_add, map_sub, map_pow, map_one, zetaInt]
  rw [e0]
  have e2 : sigmaTwo (ζ ^ 4 + ζ ^ 3 - 1) = ζ ^ 3 + ζ - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sigmaTwo_apply_zeta]
    linear_combination (ζ ^ 3 + ζ) * zeta_pow_five
  have e3 : sigmaThree (ζ ^ 4 + ζ ^ 3 - 1) = ζ ^ 4 + ζ ^ 2 - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sigmaThree_apply_zeta]
    linear_combination (ζ ^ 7 + ζ ^ 2 + ζ ^ 4) * zeta_pow_five
  have e4 : sigmaFour (ζ ^ 4 + ζ ^ 3 - 1) = ζ ^ 2 + ζ - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sigmaFour_apply_zeta]
    linear_combination (ζ ^ 11 + ζ ^ 6 + ζ + ζ ^ 7 + ζ ^ 2) * zeta_pow_five
  rw [e2, e3, e4]
  ring

private theorem absNorm_span_u5 :
    Ideal.absNorm (Ideal.span {zetaInt ^ 4 + zetaInt ^ 2 - 1}) = 11 := by
  refine norm_eleven_orbit ?_
  have e0 : algebraMap (𝓞 K) K (zetaInt ^ 4 + zetaInt ^ 2 - 1) = ζ ^ 4 + ζ ^ 2 - 1 := by
    simp [map_add, map_sub, map_pow, map_one, zetaInt]
  rw [e0]
  have e2 : sigmaTwo (ζ ^ 4 + ζ ^ 2 - 1) = ζ ^ 4 + ζ ^ 3 - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sigmaTwo_apply_zeta]
    linear_combination ζ ^ 3 * zeta_pow_five
  have e3 : sigmaThree (ζ ^ 4 + ζ ^ 2 - 1) = ζ ^ 2 + ζ - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sigmaThree_apply_zeta]
    linear_combination (ζ ^ 7 + ζ ^ 2 + ζ) * zeta_pow_five
  have e4 : sigmaFour (ζ ^ 4 + ζ ^ 2 - 1) = ζ ^ 3 + ζ - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sigmaFour_apply_zeta]
    linear_combination (ζ ^ 11 + ζ ^ 6 + ζ + ζ ^ 3) * zeta_pow_five
  rw [e2, e3, e4]
  ring

private theorem absNorm_span_u9 :
    Ideal.absNorm (Ideal.span {zetaInt ^ 3 + zetaInt - 1}) = 11 := by
  refine norm_eleven_orbit ?_
  have e0 : algebraMap (𝓞 K) K (zetaInt ^ 3 + zetaInt - 1) = ζ ^ 3 + ζ - 1 := by
    simp [map_add, map_sub, map_pow, map_one, zetaInt]
  rw [e0]
  have e2 : sigmaTwo (ζ ^ 3 + ζ - 1) = ζ ^ 2 + ζ - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sigmaTwo_apply_zeta]
    linear_combination ζ * zeta_pow_five
  have e3 : sigmaThree (ζ ^ 3 + ζ - 1) = ζ ^ 4 + ζ ^ 3 - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sigmaThree_apply_zeta]
    linear_combination ζ ^ 4 * zeta_pow_five
  have e4 : sigmaFour (ζ ^ 3 + ζ - 1) = ζ ^ 4 + ζ ^ 2 - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sigmaFour_apply_zeta]
    linear_combination (ζ ^ 7 + ζ ^ 2) * zeta_pow_five
  rw [e2, e3, e4]
  ring

private theorem span_pair_eleven_three :
    Ideal.span {(11 : 𝓞 K), zetaInt - 3} = Ideal.span {zetaInt ^ 2 + zetaInt - 1} := by
  have hr : ((3 : ℤ) : ZMod 11) ^ 4 + ((3 : ℤ) : ZMod 11) ^ 3 + ((3 : ℤ) : ZMod 11) ^ 2 +
      ((3 : ℤ) : ZMod 11) + 1 = 0 := by decide
  refine (eq_of_le_of_absNorm_eq ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    absNorm_span_u3 ?_ (by norm_num)).symm
  · exact Ideal.mem_span_pair.mpr ⟨1, zetaInt + 4, by ring⟩
  · have h := absNorm_span_pair 11 3 hr
    rwa [show ((11 : ℕ) : 𝓞 K) = (11 : 𝓞 K) from by norm_cast,
      show ((3 : ℤ) : 𝓞 K) = (3 : 𝓞 K) from by norm_cast] at h

private theorem span_pair_eleven_four :
    Ideal.span {(11 : 𝓞 K), zetaInt - 4} = Ideal.span {zetaInt ^ 4 + zetaInt ^ 3 - 1} := by
  have hr : ((4 : ℤ) : ZMod 11) ^ 4 + ((4 : ℤ) : ZMod 11) ^ 3 + ((4 : ℤ) : ZMod 11) ^ 2 +
      ((4 : ℤ) : ZMod 11) + 1 = 0 := by decide
  refine (eq_of_le_of_absNorm_eq ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    absNorm_span_u4 ?_ (by norm_num)).symm
  · exact Ideal.mem_span_pair.mpr
      ⟨29, zetaInt ^ 3 + 5 * zetaInt ^ 2 + 20 * zetaInt + 80, by ring⟩
  · have h := absNorm_span_pair 11 4 hr
    rwa [show ((11 : ℕ) : 𝓞 K) = (11 : 𝓞 K) from by norm_cast,
      show ((4 : ℤ) : 𝓞 K) = (4 : 𝓞 K) from by norm_cast] at h

private theorem span_pair_eleven_five :
    Ideal.span {(11 : 𝓞 K), zetaInt - 5} = Ideal.span {zetaInt ^ 4 + zetaInt ^ 2 - 1} := by
  have hr : ((5 : ℤ) : ZMod 11) ^ 4 + ((5 : ℤ) : ZMod 11) ^ 3 + ((5 : ℤ) : ZMod 11) ^ 2 +
      ((5 : ℤ) : ZMod 11) + 1 = 0 := by decide
  refine (eq_of_le_of_absNorm_eq ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    absNorm_span_u5 ?_ (by norm_num)).symm
  · exact Ideal.mem_span_pair.mpr
      ⟨59, zetaInt ^ 3 + 5 * zetaInt ^ 2 + 26 * zetaInt + 130, by ring⟩
  · have h := absNorm_span_pair 11 5 hr
    rwa [show ((11 : ℕ) : 𝓞 K) = (11 : 𝓞 K) from by norm_cast,
      show ((5 : ℤ) : 𝓞 K) = (5 : 𝓞 K) from by norm_cast] at h

private theorem span_pair_eleven_nine :
    Ideal.span {(11 : 𝓞 K), zetaInt - 9} = Ideal.span {zetaInt ^ 3 + zetaInt - 1} := by
  have hr : ((9 : ℤ) : ZMod 11) ^ 4 + ((9 : ℤ) : ZMod 11) ^ 3 + ((9 : ℤ) : ZMod 11) ^ 2 +
      ((9 : ℤ) : ZMod 11) + 1 = 0 := by decide
  refine (eq_of_le_of_absNorm_eq ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    absNorm_span_u9 ?_ (by norm_num)).symm
  · exact Ideal.mem_span_pair.mpr ⟨67, zetaInt ^ 2 + 9 * zetaInt + 82, by ring⟩
  · have h := absNorm_span_pair 11 9 hr
    rwa [show ((11 : ℕ) : 𝓞 K) = (11 : 𝓞 K) from by norm_cast,
      show ((9 : ℤ) : 𝓞 K) = (9 : 𝓞 K) from by norm_cast] at h

/-- `11` splits completely: `11 ≡ 1 (mod 5)`, and the roots of `Φ₅` mod `11` are
`3, 4, 5, 9` (the elements of order `5` in `(ℤ/11)ˣ`). -/
theorem span_eleven_eq :
    Ideal.span {(11 : 𝓞 K)} =
      Ideal.span {(11 : 𝓞 K), zetaInt - 3} * Ideal.span {(11 : 𝓞 K), zetaInt - 4} *
        Ideal.span {(11 : 𝓞 K), zetaInt - 5} * Ideal.span {(11 : 𝓞 K), zetaInt - 9} := by
  rw [span_pair_eleven_three, span_pair_eleven_four, span_pair_eleven_five,
    span_pair_eleven_nine, Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
  have hA : (zetaInt ^ 2 + zetaInt - 1) * (zetaInt ^ 3 + zetaInt - 1) =
      zetaInt ^ 4 - 2 * zetaInt + 2 := by
    linear_combination zetaInt_pow_five
  have hB : (zetaInt ^ 4 + zetaInt ^ 2 - 1) * (zetaInt ^ 4 + zetaInt ^ 3 - 1) =
      -(2 * zetaInt ^ 4) + zetaInt + 2 := by
    linear_combination (zetaInt ^ 3 + zetaInt ^ 2 + zetaInt + 1) * zetaInt_pow_five
  have hC : (zetaInt ^ 4 - 2 * zetaInt + 2) * (-(2 * zetaInt ^ 4) + zetaInt + 2) =
      (11 : 𝓞 K) := by
    linear_combination (-(2 * zetaInt ^ 3) + 5) * zetaInt_pow_five - 2 * zetaInt_sum_eq_zero
  rw [show (zetaInt ^ 2 + zetaInt - 1) * (zetaInt ^ 4 + zetaInt ^ 3 - 1) *
      (zetaInt ^ 4 + zetaInt ^ 2 - 1) * (zetaInt ^ 3 + zetaInt - 1) = (11 : 𝓞 K) from by
    linear_combination ((zetaInt ^ 4 + zetaInt ^ 2 - 1) * (zetaInt ^ 4 + zetaInt ^ 3 - 1)) * hA +
      (zetaInt ^ 4 - 2 * zetaInt + 2) * hB + hC]

/-- Each ideal `(11, ζ - r)` for `r ∈ {3, 4, 5, 9}` is a prime of norm `11`. -/
theorem isPrime_primeAboveEleven (r : ℤ) (hr : r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 9) :
    (Ideal.span {(11 : 𝓞 K), zetaInt - (r : 𝓞 K)}).IsPrime := by
  have hr' : ((r : ZMod 11)) ^ 4 + ((r : ZMod 11)) ^ 3 + ((r : ZMod 11)) ^ 2 +
      (r : ZMod 11) + 1 = 0 := by
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h := (isMaximal_span_pair 11 r hr').isPrime
  rwa [show ((11 : ℕ) : 𝓞 K) = (11 : 𝓞 K) from by norm_cast] at h

private theorem one_mod_five_of_splits_completely (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧
      Ideal.absNorm P = p) → p % 5 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rintro ⟨P, hPprime, hle, habs⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at habs
  haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by rw [habs]; exact hp.ne_zero)
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 K) ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact habs
  let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) hp hcard'
  obtain ⟨s, hs⟩ := e.surjective (Ideal.Quotient.mk P zetaInt)
  have hs5 : s ^ 5 = (1 : ZMod p) := by
    apply e.injective
    rw [map_pow, hs, ← map_pow (Ideal.Quotient.mk P), zetaInt_pow_five, map_one, map_one]
  have hssum : 1 + s + s ^ 2 + s ^ 3 + s ^ 4 = (0 : ZMod p) := by
    apply e.injective
    simpa [map_add, map_pow, hs] using congrArg (Ideal.Quotient.mk P) zetaInt_sum_eq_zero
  have hs1 : s ≠ 1 := by
    intro h1
    rw [h1] at hssum
    have h5 : ((5 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination hssum
    have hdvd := (CharP.cast_eq_zero_iff (ZMod p) p 5).mp h5
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp hdvd)
  set u : (ZMod p)ˣ := Units.mkOfMulEqOne s (s ^ 4) (by rw [← pow_succ']; exact hs5)
    with hudef
  have hu : (u : ZMod p) = s := rfl
  have horder : orderOf u = 5 := by
    refine orderOf_eq_prime ?_ ?_
    · ext
      rw [Units.val_pow_eq_pow_val, hu]
      exact hs5
    · intro h1
      apply hs1
      rw [← hu, h1, Units.val_one]
  have hdvd_card : (5 : ℕ) ∣ p - 1 := by
    have h := orderOf_dvd_natCard u
    rw [horder, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp] at h
    exact h
  have h2le := hp.two_le
  obtain ⟨m, hm⟩ := hdvd_card
  omega

private theorem splits_completely_of_one_mod_five (p : ℕ) (hp : p.Prime) :
    p % 5 = 1 →
      ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧
        Ideal.absNorm P = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hmod
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have h2le := hp.two_le
  obtain ⟨m, hm⟩ : (5 : ℕ) ∣ p - 1 := ⟨(p - 1) / 5, by omega⟩
  have hm0 : m ≠ 0 := by omega
  have hou : orderOf (g ^ m) = 5 := by
    rw [orderOf_pow, hog, hm]
    have hgcd : Nat.gcd (5 * m) m = m := Nat.gcd_eq_right ⟨5, by ring⟩
    rw [hgcd, Nat.mul_div_assoc 5 (dvd_refl m), Nat.div_self (show 0 < m by omega), mul_one]
  have hu5 : ((g ^ m : (ZMod p)ˣ) : ZMod p) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one (g ^ m)
    rw [hou] at h
    have hc := congrArg Units.val h
    simpa using hc
  have hu1 : ((g ^ m : (ZMod p)ˣ) : ZMod p) ≠ 1 := by
    intro h1
    have : (g ^ m) = 1 := Units.ext (by simpa using h1)
    rw [this, orderOf_one] at hou
    norm_num at hou
  have hr : (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) ^ 4 +
      (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) ^ 3 +
      (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) ^ 2 +
      (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) + 1 = 0 := by
    have hcast : (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) =
        ((g ^ m : (ZMod p)ˣ) : ZMod p) := by
      push_cast
      exact ZMod.natCast_rightInverse _
    rw [hcast]
    set v : ZMod p := ((g ^ m : (ZMod p)ˣ) : ZMod p)
    have hfactor : (v - 1) * (v ^ 4 + v ^ 3 + v ^ 2 + v + 1) = 0 := by
      linear_combination hu5
    rcases mul_eq_zero.mp hfactor with h | h
    · exact absurd (by linear_combination h) hu1
    · linear_combination h
  refine ⟨Ideal.span {((p : ℕ) : 𝓞 K),
    zetaInt - ((((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : 𝓞 K))},
    (isMaximal_span_pair p _ hr).isPrime, ?_, absNorm_span_pair p _ hr⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact Ideal.subset_span (by simp)

/-- The splitting law for `ℚ(ζ₅)`: a prime `p` splits completely iff `p ≡ 1 (mod 5)`. -/
theorem splits_completely_iff (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧ Ideal.absNorm P = p) ↔
      p % 5 = 1 := by
  constructor
  · exact one_mod_five_of_splits_completely p hp hp5
  · exact splits_completely_of_one_mod_five p hp

/-- A rational prime `p` ramifies in `ℚ(ζ₅)` iff `p = 5`, i.e. iff `p` divides the
discriminant `125`. -/
theorem ramified_iff_eq_five (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 5 := by
  constructor
  · rintro ⟨P, hP, hle2⟩
    haveI : P.IsPrime := hP
    have hple : Ideal.span {((p : ℕ) : 𝓞 K)} ≤ P :=
      hle2.trans (Ideal.pow_le_self (by norm_num))
    have hpmemP : ((p : ℕ) : 𝓞 K) ∈ P := hple (Ideal.mem_span_singleton_self _)
    have hpne : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hPbot : P ≠ ⊥ := by
      intro h
      rw [h] at hpmemP
      exact hpne (Ideal.mem_bot.mp hpmemP)
    have hfin : Module.finrank ℤ (𝓞 K) = 4 := by
      rw [Module.finrank_eq_card_basis concreteIntegralBasis, Fintype.card_fin]
    have habsp : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 4 := by
      rw [Ideal.absNorm_span_singleton]
      have hcast : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ((p : ℕ) : ℤ) := by push_cast; rfl
      rw [hcast, Algebra.norm_algebraMap, hfin, Int.natAbs_pow, Int.natAbs_natCast]
    have habsPp4 : Ideal.absNorm P ∣ p ^ 4 :=
      habsp ▸ Ideal.absNorm_dvd_absNorm_of_le hple
    obtain ⟨k, hk4, hkeq⟩ := (Nat.dvd_prime_pow hp).mp habsPp4
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hkeq
      exact hP.ne_top (Ideal.absNorm_eq_one_iff.mp hkeq)
    have hle2' : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 2 := by
      simpa [Ideal.map_span, Set.image_singleton] using hle2
    have hno5 : ¬ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 5 :=
      not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow hp habsp hkeq hk0
    have hunram : ¬ Algebra.IsUnramifiedAt ℤ P :=
      not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ hp hpmemP hPbot hle2'
        hno5
    have hPdiff : P ∣ differentIdeal ℤ (𝓞 K) := dvd_differentIdeal_iff.mpr hunram
    have habsP125 : Ideal.absNorm P ∣ 125 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPdiff)
      rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq] at h
      simpa using h
    have hpdvd : p ∣ 125 := (hkeq ▸ dvd_pow_self p hk0).trans habsP125
    have hp5 : p ∣ 5 := hp.dvd_of_dvd_pow (show p ∣ 5 ^ 3 by norm_num; exact hpdvd)
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp5
  · rintro rfl
    refine ⟨Ideal.span {1 - zetaInt}, isPrime_span_one_sub_zeta, ?_⟩
    have hcast : ((5 : ℕ) : 𝓞 K) = (5 : 𝓞 K) := by norm_num
    rw [hcast, span_five_eq]
    exact Ideal.pow_le_pow_right (by norm_num)

/-- The inert prime `(2)` is unramified. -/
theorem ramificationIdx_span_two :
    (Ideal.span {(2 : ℤ)}).ramificationIdx (Ideal.span {(2 : 𝓞 K)}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    simp
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(2 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {(2 : 𝓞 K)}, isPrime_span_two, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h := (ramified_iff_eq_five 2 Nat.prime_two).mp hram
    norm_num at h

end NumberField.CyclotomicFive

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open IsDedekindDomain

namespace NumberField.CyclotomicFive

theorem absNorm_differentIdeal_eq_oneHundredTwentyFive :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = 125 := by
  rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq]
  norm_num

theorem prime_dvd_differentIdeal_iff_eq_span_one_sub_zeta
    (P : Ideal (𝓞 K)) (_hP : P.IsPrime) (_hP0 : P ≠ ⊥) :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ P = Ideal.span {1 - zetaInt} := by
  constructor
  · intro hdiv
    haveI : P.IsPrime := _hP
    have hnormdvd : Ideal.absNorm P ∣ 125 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdiv)
      rw [absNorm_differentIdeal_eq_oneHundredTwentyFive] at h
      exact h
    rw [show (125 : ℕ) = 5 ^ 3 by norm_num] at hnormdvd
    obtain ⟨k, _hk, hkeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hnormdvd
    have hmem_norm := Ideal.absNorm_mem P
    rw [hkeq] at hmem_norm
    have hpow_mem : (5 : 𝓞 K) ^ k ∈ P := by
      simpa [Nat.cast_pow] using hmem_norm
    have h5mem : (5 : 𝓞 K) ∈ P := _hP.mem_of_pow_mem k hpow_mem
    have hle : Ideal.span {(5 : 𝓞 K)} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr h5mem
    have h4 : (1 - zetaInt) ^ 4 ∈ P := by
      apply hle
      rw [span_five_eq, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    have h1 : 1 - zetaInt ∈ P := _hP.mem_of_pow_mem 4 h4
    have hbot : Ideal.span {1 - zetaInt} ≠ ⊥ := by
      intro h
      have hnorm := absNorm_span_one_sub_zeta
      rw [h, Ideal.absNorm_bot] at hnorm
      norm_num at hnorm
    have hmax : (Ideal.span {1 - zetaInt}).IsMaximal :=
      isPrime_span_one_sub_zeta.isMaximal hbot
    exact (hmax.eq_of_le _hP.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr h1)).symm
  · intro h
    rw [h]
    have hpow : Ideal.span {1 - zetaInt} ^ (4 - 1) ∣ differentIdeal ℤ (𝓞 K) := by
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      haveI : (Ideal.span {(5 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 5
      refine pow_sub_one_dvd_differentIdeal (A := ℤ) (B := 𝓞 K)
        (p := Ideal.span {(5 : ℤ)}) (P := Ideal.span {1 - zetaInt}) 4 ?_ ?_
      · intro hbot
        have hzero : (5 : ℤ) = 0 := Ideal.span_singleton_eq_bot.mp hbot
        norm_num at hzero
      · rw [Ideal.map_span, Set.image_singleton]
        change Ideal.span {1 - zetaInt} ^ 4 ∣ Ideal.span {(5 : 𝓞 K)}
        rw [span_five_eq]
    exact (dvd_pow_self (Ideal.span {1 - zetaInt}) (by norm_num : 4 - 1 ≠ 0)).trans hpow

end NumberField.CyclotomicFive
