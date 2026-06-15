/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.Galois

/-!
# `ℚ(∛3)` Embeddings

Real and complex embeddings, signature, infinite places, and lightweight canonical embedding facts.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Signature and archimedean type
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.CubeRootThree

theorem not_totallyReal : ¬ NumberField.IsTotallyReal K := by
  intro h
  obtain ⟨c, hc3, hcim⟩ : ∃ c : ℂ, c ^ 3 = 3 ∧ c.im ≠ 0 := by
    obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 3 :=
      ⟨_, Complex.isPrimitiveRoot_exp 3 (by norm_num)⟩
    have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
    have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
    have hquad : ζ ^ 2 + ζ + 1 = 0 := by
      have hfac : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
      rcases mul_eq_zero.mp hfac with hh | hh
      · exact absurd (sub_eq_zero.mp hh) hζ1
      · exact hh
    have hζim : ζ.im ≠ 0 := by
      intro him
      have hre : (ζ ^ 2 + ζ + 1).re = 0 := by rw [hquad]; simp
      rw [sq] at hre
      simp only [Complex.add_re, Complex.mul_re, Complex.one_re, him, mul_zero, sub_zero] at hre
      nlinarith [hre, sq_nonneg ζ.re]
    obtain ⟨c0, hc0⟩ := IsAlgClosed.exists_pow_nat_eq (3 : ℂ) (n := 3) (by norm_num)
    have hc0ne : c0 ≠ 0 := by intro hh; rw [hh] at hc0; norm_num at hc0
    by_cases hc0im : c0.im = 0
    · refine ⟨c0 * ζ, by rw [mul_pow, hc0, hζ3]; ring, ?_⟩
      rw [Complex.mul_im, hc0im, zero_mul, add_zero]
      exact mul_ne_zero (fun hh => hc0ne (Complex.ext hh hc0im)) hζim
    · exact ⟨c0, hc0, hc0im⟩
  have hroot : eval₂ (algebraMap ℚ ℂ) c cubePolynomial = 0 := by
    simp only [cubePolynomial, eval₂_sub, eval₂_pow, eval₂_X, map_ofNat]
    rw [hc3]; norm_num
  let φ : K →+* ℂ := AdjoinRoot.lift (algebraMap ℚ ℂ) c hroot
  have hφ : φ cubeRootThree = c := AdjoinRoot.lift_root hroot
  have hreal : NumberField.ComplexEmbedding.IsReal φ := h.complexEmbedding_isReal φ
  rw [NumberField.ComplexEmbedding.isReal_iff] at hreal
  have hpt := RingHom.congr_fun hreal cubeRootThree
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, hφ] at hpt
  exact hcim (Complex.conj_eq_iff_im.mp hpt)

theorem nrComplexPlaces_eq_one : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
  have hsig : NumberField.InfinitePlace.nrRealPlaces K +
      2 * NumberField.InfinitePlace.nrComplexPlaces K = 3 := by
    rw [← degree_eq_three]; exact NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 := by
    rw [Ne, NumberField.nrComplexPlaces_eq_zero_iff]; exact not_totallyReal
  omega

theorem nrRealPlaces_eq_one : NumberField.InfinitePlace.nrRealPlaces K = 1 := by
  have hsig : NumberField.InfinitePlace.nrRealPlaces K +
      2 * NumberField.InfinitePlace.nrComplexPlaces K = 3 := by
    rw [← degree_eq_three]; exact NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [nrComplexPlaces_eq_one] at hsig
  omega
end NumberField.CubeRootThree


/-!
## Embeddings
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

theorem infinitePlace_card_eq_two :
    Fintype.card (NumberField.InfinitePlace K) = 2 := by
  sorry

theorem infinitePlace_signature :
    NumberField.InfinitePlace.nrRealPlaces K = 1 ∧
      NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
  sorry

theorem exists_realEmbedding_cubeRootThree :
    ∃ σ : K →ₐ[ℚ] ℝ, σ cubeRootThree = (3 : ℝ) ^ ((1 : ℝ) / 3) := by
  sorry

theorem exists_complexEmbedding_cubeRootThree :
    ∃ σ : K →+* ℂ, σ cubeRootThree ^ 3 = 3 := by
  sorry

end NumberField.CubeRootThree
