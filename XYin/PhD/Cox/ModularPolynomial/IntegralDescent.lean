/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.Polynomial.Lifts
import XYin.PhD.Cox.FormalCoxProduct
import XYin.PhD.Cox.LaurentPolynomialEvaluation
import XYin.PhD.Cox.ModularPolynomial.Construction
import XYin.PhD.LaurentQExpansion.Algebra

/-!
# Integral descent of Cox's modular polynomial

This file proves Hasse's coefficient principle and descends the complex modular polynomial to
its canonical monic representative in `ℤ[X][Y]` (same variable convention as
`Cox.modularPolynomialC`).
-/

open Complex Function MatrixGroups ModularForm UpperHalfPlane
open scoped Manifold Polynomial.Bivariate

noncomputable section

namespace Cox

/-- The Laurent series over `ℂ` with integral coefficients. -/
private abbrev integerCoeffLaurentSeries : Subring (LaurentSeries ℂ) :=
  HahnSeries.coeffSubring (Int.castRingHom ℂ).range

/-- Hasse's principle in subring form: if `P(j)` has integral Laurent coefficients, then `P` has
integral coefficients. The leading coefficient of `P` is the lowest coefficient of `P(j)`. -/
private lemma mem_lifts_of_eval₂_mem {P : Polynomial ℂ}
    (hP : P.eval₂ HahnSeries.C (laurentqExpansion 1 j) ∈ integerCoeffLaurentSeries) :
    P ∈ Polynomial.lifts (Int.castRingHom ℂ) := by
  induction hd : P.natDegree using Nat.strong_induction_on generalizing P with
  | h d ih =>
    have hlead : P.leadingCoeff ∈ (Int.castRingHom ℂ).range := by
      simpa using polynomial_eval₂_laurentSeries_coeff (laurentqExpansion 1 j) 1 one_pos
        (by simpa using laurentqExpansion_j_order_widthM 1)
        (by simpa using laurentqExpansion_j_leadingCoeff_widthM 1) P ▸ hP _
    rw [← P.eraseLead_add_monomial_natDegree_leadingCoeff]
    refine add_mem ?_ (Polynomial.monomial_mem_lifts _ hlead)
    rcases P.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt | h0
    · refine ih _ (hd ▸ hlt) ?_ rfl
      obtain ⟨k, hk⟩ := hlead
      rw [← Polynomial.self_sub_monomial_natDegree_leadingCoeff, Polynomial.eval₂_sub,
        Polynomial.eval₂_monomial, ← hk]
      have hj : laurentqExpansion 1 j ∈ integerCoeffLaurentSeries :=
        fun n ↦ ⟨jIntCoeff n, (jIntCoeff_spec n).symm⟩
      exact sub_mem hP (mul_mem (by simp) (pow_mem hj _))
    · rw [h0]
      exact zero_mem _

/-- Hasse's q-expansion principle: a polynomial `P` such that `P(j)` has integral Laurent
coefficients has integral coefficients. -/
theorem hasse_qExpansion_principle {P : Polynomial ℂ}
    (hint : laurentqExpansion 1 (polynomialIn P j) ∈
      HahnSeries.coeffSubring (Int.castRingHom ℂ).range) :
    P ∈ Polynomial.lifts (Int.castRingHom ℂ) :=
  mem_lifts_of_eval₂_mem <| by
    rwa [← laurentqExpansion_polynomial_eval one_pos j_cuspFunction_meromorphicAt P]

private def coxNegativeRoot (m : ℕ+) (σ : CoxMatrix m) : ℍ → ℂ :=
  -(fun τ ↦ j (σ.act τ))

private def coxNegativeRootSeries (m : ℕ+) (σ : CoxMatrix m) : LaurentSeries ℂ :=
  -transformedJSeries (zeta m) σ

private theorem coxNegativeRoot_cuspMeromorphicAt_aux (m : ℕ+) (σ : CoxMatrix m) :
    MeromorphicAt
      (cuspFunction ((m : ℕ) : ℝ) (coxNegativeRoot m σ)) 0 :=
  meromorphicAt_cuspFunction_neg (coxRoot_cuspMeromorphicAt m σ)

private theorem coxNegativeRoot_laurentqExpansion_aux (m : ℕ+) (σ : CoxMatrix m) :
    laurentqExpansion ((m : ℕ) : ℝ) (coxNegativeRoot m σ) =
      coxNegativeRootSeries m σ := by
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast PNat.pos m
  simpa [coxNegativeRoot, coxNegativeRootSeries] using
    (laurentqExpansion_neg hmpos (coxRoot_cuspMeromorphicAt m σ)).trans
      (congrArg Neg.neg (laurentqExpansion_coxAction m σ))

/-- The width-`m` Laurent expansion of a Cox-product coefficient is the corresponding
coefficient of the formal product from equation (11.13). -/
theorem coxPhiFunction_coeff_laurentqExpansion_widthM (m : ℕ+) (n : ℕ) :
    laurentqExpansion ((m : ℕ) : ℝ) ((coxPhiFunction m).coeff n) =
      (formalCoxPolynomial m (zeta m)).coeff n := by
  classical
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast PNat.pos m
  by_cases hn : n ≤ Fintype.card (CoxMatrix m)
  · have hfunction : (coxPhiFunction m).coeff n =
        ∑ t ∈ (Finset.univ : Finset (CoxMatrix m)).powersetCard
          (Fintype.card (CoxMatrix m) - n), ∏ σ ∈ t, coxNegativeRoot m σ := by
      have hcoeff := Finset.prod_X_add_C_coeff
        (R := ℍ → ℂ) (Finset.univ : Finset (CoxMatrix m)) (coxNegativeRoot m) hn
      simpa [coxPhiFunction, coxNegativeRoot, sub_eq_add_neg, Polynomial.C_neg] using hcoeff
    have hformal : (formalCoxPolynomial m (zeta m)).coeff n =
        ∑ t ∈ (Finset.univ : Finset (CoxMatrix m)).powersetCard
          (Fintype.card (CoxMatrix m) - n), ∏ σ ∈ t, coxNegativeRootSeries m σ := by
      have hcoeff := Finset.prod_X_add_C_coeff
        (R := LaurentSeries ℂ) (Finset.univ : Finset (CoxMatrix m))
        (coxNegativeRootSeries m) hn
      simpa [formalCoxPolynomial, coxNegativeRootSeries, sub_eq_add_neg,
        Polynomial.C_neg] using hcoeff
    rw [hfunction, hformal, laurentqExpansion_finset_sum hmpos]
    · apply Finset.sum_congr rfl
      intro t _
      rw [laurentqExpansion_finset_prod hmpos]
      · exact Finset.prod_congr rfl fun σ _ ↦ coxNegativeRoot_laurentqExpansion_aux m σ
      · exact fun σ _ ↦ coxNegativeRoot_cuspMeromorphicAt_aux m σ
    · exact fun t _ ↦ meromorphicAt_cuspFunction_finset_prod
        fun σ _ ↦ coxNegativeRoot_cuspMeromorphicAt_aux m σ
  · have hlt : Fintype.card (CoxMatrix m) < n := lt_of_not_ge hn
    have hfunction : (coxPhiFunction m).coeff n = 0 := by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      simpa [coxPhiFunction] using hlt
    have hformal : (formalCoxPolynomial m (zeta m)).coeff n = 0 := by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      simpa [formalCoxPolynomial] using hlt
    rw [hfunction, hformal, laurentqExpansion_zero]

/-- Galois descent from (11.13): every Laurent coefficient of every elementary symmetric
function in the Cox roots is an ordinary integer. -/
theorem coxPhiFunction_coeff_integerLaurent (m : ℕ+) (n : ℕ) :
    laurentqExpansion 1 ((coxPhiFunction m).coeff n) ∈
      HahnSeries.coeffSubring (Int.castRingHom ℂ).range := by
  intro k
  obtain ⟨z, hz⟩ := formalCoxPolynomial_coeff_isInteger m n ((m : ℤ) * k)
  have hscale := laurentqExpansion_nat_mul_coeff (h := 1) (m := (m : ℕ)) (PNat.ne_zero m)
    (coxPhiFunction_coeff_widthOne_cuspMeromorphicAt m n)
    (coxPhiFunction_coeff_cuspData m n).periodic k
  rw [mul_one, coxPhiFunction_coeff_laurentqExpansion_widthM, hz] at hscale
  exact ⟨z, hscale⟩

/-- Cox Theorem 11.18(i): the complex modular polynomial descends to `ℤ[X][Y]`. -/
theorem exists_modularPolynomialZ (m : ℕ+) :
    ∃ Φ : ℤ[X][Y],
      Φ.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = modularPolynomialC m :=
  (Polynomial.mem_lifts _).1 <| (Polynomial.lifts_iff_coeff_lifts _).2 fun n ↦
    (Polynomial.mem_lifts _).1 <| hasse_qExpansion_principle <| by
      rw [modularPolynomialC_coeff_polynomialIn]
      exact coxPhiFunction_coeff_integerLaurent m n

/-- The canonical integer descent of the modular polynomial: Cox's `Φ_m(X, Y) ∈ ℤ[X, Y]`, with
Cox's root variable `X` as the outer variable `Y` of `ℤ[X][Y]` and Cox's parameter `Y` as the
inner variable `C X`. -/
noncomputable def modularPolynomial (m : ℕ+) : ℤ[X][Y] :=
  (exists_modularPolynomialZ m).choose

/-- The integral modular polynomial maps to the complex one. -/
theorem modularPolynomial_map_complex (m : ℕ+) :
    (modularPolynomial m).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
      modularPolynomialC m :=
  (exists_modularPolynomialZ m).choose_spec

/-- Swapping the variables commutes with the complexification of `Φ_m`. -/
theorem modularPolynomial_map_complex_swap (m : ℕ+) :
    (Polynomial.Bivariate.swap (modularPolynomial m)).map
        (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
      Polynomial.Bivariate.swap (modularPolynomialC m) := by
  rw [Polynomial.Bivariate.map_mapRingHom_swap, modularPolynomial_map_complex]

/-- The integral modular polynomial retains the monic normalization in the root variable. -/
theorem modularPolynomial_monic (m : ℕ+) : (modularPolynomial m).Monic :=
  Polynomial.monic_of_injective (f := Polynomial.mapRingHom (Int.castRingHom ℂ))
    (Polynomial.map_injective _ Int.cast_injective)
    (modularPolynomial_map_complex m ▸ modularPolynomialC_monic m)

end Cox
