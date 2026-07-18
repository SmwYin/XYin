/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.Polynomial.Lifts
import XYin.PhD.Cox.ModularPolynomial.Construction
import XYin.PhD.LaurentQExpansion.Algebra

/-!
# Integral descent of Cox's modular polynomial

This file proves Hasse's coefficient principle and descends the complex modular polynomial to
its canonical monic representative in `ℤ[X,Y]`.
-/

open Complex Function MatrixGroups ModularForm UpperHalfPlane
open scoped Manifold Polynomial.Bivariate

noncomputable section

namespace Cox

private lemma laurentqExpansion_j_pow_aux (n : ℕ) :
    laurentqExpansion 1 (fun τ ↦ j τ ^ n) = (laurentqExpansion 1 j) ^ n := by
  have h := laurentqExpansion_finset_prod (h := (1 : ℝ)) (by positivity)
    (Finset.range n) (f := fun _ ↦ j) (fun _ _ ↦ j_cuspFunction_meromorphicAt)
  simpa using h

private lemma polynomialIn_cuspMeromorphicAt_aux (P : Polynomial ℂ) :
    MeromorphicAt (cuspFunction 1 (polynomialIn P j)) 0 := by
  simpa using (j_isLevelOneModularFunction.polynomialIn P).2.2 1

private lemma laurentqExpansion_polynomialIn_j_aux (P : Polynomial ℂ) :
    laurentqExpansion 1 (polynomialIn P j) =
      P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion 1 j) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      calc
        laurentqExpansion 1 (polynomialIn (P + Q) j) =
            laurentqExpansion 1
              (fun τ ↦ polynomialIn P j τ + polynomialIn Q j τ) := by
          congr 1
          funext τ
          simp [polynomialIn]
        _ = laurentqExpansion 1 (polynomialIn P j) +
              laurentqExpansion 1 (polynomialIn Q j) :=
          laurentqExpansion_add (by positivity) (polynomialIn_cuspMeromorphicAt_aux P)
            (polynomialIn_cuspMeromorphicAt_aux Q)
        _ = (P + Q).eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
              (laurentqExpansion 1 j) := by rw [hP, hQ, Polynomial.eval₂_add]
  | monomial n a =>
      have hjpow : MeromorphicAt (cuspFunction 1 (fun τ ↦ j τ ^ n)) 0 := by
        simpa [polynomialIn] using
          (j_isLevelOneModularFunction.polynomialIn (Polynomial.X ^ n)).2.2 1
      calc
        laurentqExpansion 1 (polynomialIn (Polynomial.monomial n a) j) =
            laurentqExpansion 1 (fun τ ↦ a * j τ ^ n) := by
          congr 1
          funext τ
          simp [polynomialIn]
        _ = HahnSeries.C a * laurentqExpansion 1 (fun τ ↦ j τ ^ n) := by
          simpa using laurentqExpansion_mul (h := (1 : ℝ)) (by positivity)
            (meromorphicAt_cuspFunction_const 1 a) hjpow
        _ = (Polynomial.monomial n a).eval₂
              (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion 1 j) := by
          rw [laurentqExpansion_j_pow_aux, Polynomial.eval₂_monomial]

private lemma laurentqExpansion_j_order_aux : (laurentqExpansion 1 j).order = -1 := by
  have h := laurentqExpansion.poleOrder_to_order
    j_cuspFunction_meromorphicAt (by simp [j_poleOrder])
  rw [j_poleOrder] at h
  change (1 : ℤ) = -(laurentqExpansion 1 j).order at h
  omega

private lemma laurentqExpansion_j_leadingCoeff_aux :
    (laurentqExpansion 1 j).leadingCoeff = 1 := by
  rw [HahnSeries.leadingCoeff_eq, laurentqExpansion_j_order_aux]
  simpa [jIntCoeff_neg_one] using jIntCoeff_spec (-1)

private lemma laurentqExpansion_j_pow_order_aux (n : ℕ) :
    ((laurentqExpansion 1 j) ^ n).order = -(n : ℤ) := by
  rw [HahnSeries.order_pow, laurentqExpansion_j_order_aux]
  simp

private lemma laurentqExpansion_j_pow_leadingCoeff_aux (n : ℕ) :
    ((laurentqExpansion 1 j) ^ n).leadingCoeff = 1 := by
  induction n with
  | zero => simp [HahnSeries.leadingCoeff_one]
  | succ n ih =>
      simp [pow_succ, HahnSeries.leadingCoeff_mul, ih,
        laurentqExpansion_j_leadingCoeff_aux]

private lemma eval₂_laurentqExpansion_j_coeff_neg_natDegree_aux (P : Polynomial ℂ) :
    (P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion 1 j)).coeff
      (-(P.natDegree : ℤ)) = P.leadingCoeff := by
  rw [Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum]
  calc
    ∑ i ∈ Finset.range (P.natDegree + 1),
        (HahnSeries.C (P.coeff i) * (laurentqExpansion 1 j) ^ i).coeff
          (-(P.natDegree : ℤ)) =
        (HahnSeries.C (P.coeff P.natDegree) *
          (laurentqExpansion 1 j) ^ P.natDegree).coeff (-(P.natDegree : ℤ)) := by
      apply Finset.sum_eq_single P.natDegree
      · intro n hn hne
        rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
        change P.coeff n * ((laurentqExpansion 1 j) ^ n).coeff
          (-(P.natDegree : ℤ)) = 0
        rw [HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
        rw [laurentqExpansion_j_pow_order_aux]
        have hnlt : n < P.natDegree := by
          have hnle : n ≤ P.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
          exact lt_of_le_of_ne hnle hne
        omega
      · simp
    _ = P.leadingCoeff := by
      rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
      change P.coeff P.natDegree *
        ((laurentqExpansion 1 j) ^ P.natDegree).coeff (-(P.natDegree : ℤ)) = _
      rw [← laurentqExpansion_j_pow_order_aux, ← HahnSeries.leadingCoeff_eq,
        laurentqExpansion_j_pow_leadingCoeff_aux, mul_one, Polynomial.coeff_natDegree]

private def integerCoeffLaurentSeries : Subring (LaurentSeries ℂ) where
  carrier := {F | ∀ n, F.coeff n ∈ (Int.castRingHom ℂ).range}
  zero_mem' := by
    intro n
    simp
  one_mem' := by
    intro n
    by_cases hn : n = 0
    · subst n
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [HahnSeries.coeff_one, hn]⟩
  add_mem' := by
    intro F G hF hG n
    rw [HahnSeries.coeff_add]
    exact Subring.add_mem _ (hF n) (hG n)
  neg_mem' := by
    intro F hF n
    rw [HahnSeries.coeff_neg]
    exact Subring.neg_mem _ (hF n)
  mul_mem' := by
    intro F G hF hG n
    rw [HahnSeries.coeff_mul]
    exact Subring.sum_mem _ fun ij _ ↦ Subring.mul_mem _ (hF ij.1) (hG ij.2)

private lemma laurentqExpansion_j_mem_integerCoeffLaurentSeries :
    laurentqExpansion 1 j ∈ integerCoeffLaurentSeries := by
  intro n
  obtain ⟨z, hz⟩ := j_laurentQExpansion_isIntegral (n := n)
  exact ⟨z, hz.symm⟩

private lemma intCast_C_mem_integerCoeffLaurentSeries (z : ℤ) :
    HahnSeries.C (z : ℂ) ∈ integerCoeffLaurentSeries := by
  intro n
  by_cases hn : n = 0
  · subst n
    refine ⟨z, ?_⟩
    change (z : ℂ) = (HahnSeries.single (0 : ℤ) (z : ℂ)).coeff 0
    simp
  · refine ⟨0, ?_⟩
    rw [map_zero]
    change (0 : ℂ) = (HahnSeries.single (0 : ℤ) (z : ℂ)).coeff n
    simp [hn]

private lemma leadingCoeff_eq_int_of_integer_laurent_aux {P : Polynomial ℂ}
    (hint : ∀ n : ℤ, ∃ k : ℤ,
      (laurentqExpansion 1 (polynomialIn P j)).coeff n = (k : ℂ)) :
    ∃ k : ℤ, P.leadingCoeff = (k : ℂ) := by
  obtain ⟨k, hk⟩ := hint (-(P.natDegree : ℤ))
  refine ⟨k, ?_⟩
  rw [laurentqExpansion_polynomialIn_j_aux,
    eval₂_laurentqExpansion_j_coeff_neg_natDegree_aux] at hk
  exact hk

private lemma eraseLead_integer_laurent_aux {P : Polynomial ℂ} {k : ℤ}
    (hint : ∀ n : ℤ, ∃ z : ℤ,
      (laurentqExpansion 1 (polynomialIn P j)).coeff n = (z : ℂ))
    (hleading : P.leadingCoeff = (k : ℂ)) (n : ℤ) :
    ∃ z : ℤ, (laurentqExpansion 1 (polynomialIn P.eraseLead j)).coeff n = (z : ℂ) := by
  have hPmem :
      P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion 1 j) ∈
        integerCoeffLaurentSeries := by
    rw [← laurentqExpansion_polynomialIn_j_aux]
    intro r
    obtain ⟨z, hz⟩ := hint r
    exact ⟨z, hz.symm⟩
  have hleadmem : HahnSeries.C (k : ℂ) * (laurentqExpansion 1 j) ^ P.natDegree ∈
      integerCoeffLaurentSeries :=
    integerCoeffLaurentSeries.mul_mem (intCast_C_mem_integerCoeffLaurentSeries k)
      (integerCoeffLaurentSeries.pow_mem
        laurentqExpansion_j_mem_integerCoeffLaurentSeries P.natDegree)
  have herase : P.eraseLead = P - Polynomial.monomial P.natDegree P.leadingCoeff :=
    eq_sub_iff_add_eq.mpr (Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff P)
  have hRmem :
      P.eraseLead.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
        (laurentqExpansion 1 j) ∈ integerCoeffLaurentSeries := by
    rw [herase, Polynomial.eval₂_sub, Polynomial.eval₂_monomial, hleading]
    exact integerCoeffLaurentSeries.sub_mem hPmem hleadmem
  obtain ⟨z, hz⟩ := hRmem n
  refine ⟨z, ?_⟩
  rw [laurentqExpansion_polynomialIn_j_aux]
  exact hz.symm

/-- Hasse's q-expansion principle in the coefficient form needed for integral descent. -/
theorem hasse_qExpansion_principle {P : Polynomial ℂ}
    (hint : ∀ n : ℤ, ∃ k : ℤ,
      (laurentqExpansion 1 (polynomialIn P j)).coeff n = (k : ℂ)) :
    ∃ Q : Polynomial ℤ, P = Q.map (Int.castRingHom ℂ) := by
  induction hd : P.natDegree using Nat.strong_induction_on generalizing P with
  | h d ih =>
      obtain ⟨k, hleading⟩ := leadingCoeff_eq_int_of_integer_laurent_aux hint
      by_cases hd0 : d = 0
      · refine ⟨Polynomial.C k, ?_⟩
        calc
          P = Polynomial.C (P.coeff 0) :=
            Polynomial.eq_C_of_natDegree_eq_zero (hd.trans hd0)
          _ = Polynomial.C (k : ℂ) := by
            rw [← hleading, ← Polynomial.coeff_natDegree, hd, hd0]
          _ = (Polynomial.C k).map (Int.castRingHom ℂ) := by simp
      · have hRdegree : P.eraseLead.natDegree < d := by
          rw [← hd]
          exact P.eraseLead_natDegree_le.trans_lt (Nat.sub_lt (by omega) zero_lt_one)
        obtain ⟨Q, hQ⟩ := ih P.eraseLead.natDegree hRdegree
          (eraseLead_integer_laurent_aux hint hleading) rfl
        refine ⟨Q + Polynomial.monomial P.natDegree k, ?_⟩
        rw [Polynomial.map_add, Polynomial.map_monomial, ← hQ]
        change P = P.eraseLead + Polynomial.monomial P.natDegree (k : ℂ)
        rw [← hleading]
        exact (Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff P).symm

private def coxNegativeRoot (m : ℕ+) (σ : CoxMatrix m) : ℍ → ℂ :=
  -(fun τ ↦ j (σ.act τ))

private def coxNegativeRootSeries (m : ℕ+) (σ : CoxMatrix m) : LaurentSeries ℂ :=
  -transformedJSeries (zeta m) σ

private theorem coxNegativeRoot_cuspMeromorphicAt_aux (m : ℕ+) (σ : CoxMatrix m) :
    MeromorphicAt
      (cuspFunction ((m : ℕ) : ℝ) (coxNegativeRoot m σ)) 0 := by
  simpa only [coxNegativeRoot, neg_one_mul] using
    meromorphicAt_cuspFunction_mul
      (meromorphicAt_cuspFunction_const ((m : ℕ) : ℝ) (-1))
      (coxRoot_cuspMeromorphicAt m σ)

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
theorem coxPhiFunction_coeff_integerLaurent (m : ℕ+) (n : ℕ) (k : ℤ) :
    ∃ z : ℤ,
      (laurentqExpansion 1 ((coxPhiFunction m).coeff n)).coeff k = (z : ℂ) := by
  obtain ⟨z, hz⟩ :=
    formalCoxPolynomial_coeff_isInteger m n ((m : ℤ) * k)
  refine ⟨z, ?_⟩
  have hscale := laurentqExpansion_nat_mul_coeff (h := 1) (m := (m : ℕ))
    (PNat.ne_zero m) (coxPhiFunction_coeff_widthOne_cuspMeromorphicAt m n)
    (periodic_comp_of_slashInvariant_one
      (coxPhiFunction_coeff_slashInvariant m n)) k
  have hbridge := congrArg
    (fun L : LaurentSeries ℂ ↦ L.coeff ((m : ℤ) * k))
    (coxPhiFunction_coeff_laurentqExpansion_widthM m n)
  calc
    (laurentqExpansion 1 ((coxPhiFunction m).coeff n)).coeff k =
        (laurentqExpansion ((m : ℕ) : ℝ) ((coxPhiFunction m).coeff n)).coeff
          ((m : ℤ) * k) := by simpa using hscale.symm
    _ = ((formalCoxPolynomial m (zeta m)).coeff n).coeff ((m : ℤ) * k) := hbridge
    _ = (z : ℂ) := hz

private theorem bivariate_exists_of_coeff_lifts (F : BivariatePolynomial ℂ)
    (hcoeff : ∀ n : ℕ, ∃ Q : Polynomial ℤ,
      F.coeff n = Q.map (Int.castRingHom ℂ)) :
    ∃ G : BivariatePolynomial ℤ,
      BivariatePolynomial.map (Int.castRingHom ℂ) G = F := by
  have hF : F ∈ Polynomial.lifts
      (Polynomial.mapRingHom (Int.castRingHom ℂ)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨Q, hQ⟩ := hcoeff n
    exact ⟨Q, hQ.symm⟩
  obtain ⟨G, hG, _⟩ := Polynomial.exists_support_eq_of_mem_lifts hF
  exact ⟨G, by simpa [BivariatePolynomial.map] using hG⟩

/-- The coefficient polynomials of `Φ_m` recover the function-valued Cox-product
coefficients after substituting `Y = j`. -/
theorem modularPolynomialC_coeff_polynomialIn (m : ℕ+) (n : ℕ) :
    polynomialIn ((modularPolynomialC m).coeff n) j =
      (coxPhiFunction m).coeff n := by
  funext τ
  have hcoeff := congrArg (fun P : Polynomial ℂ ↦ P.coeff n)
    (modularPolynomialC_specializeY m τ)
  rw [coxPhiFunction_coeff_apply]
  simpa [polynomialIn, BivariatePolynomial.specializeY,
    Polynomial.coeff_map] using hcoeff

/-- Cox Theorem 11.18(i): the complex modular polynomial descends to `ℤ[X,Y]`. -/
theorem exists_modularPolynomialZ (m : ℕ+) :
    ∃ Φ : BivariatePolynomial ℤ,
      BivariatePolynomial.map (Int.castRingHom ℂ) Φ = modularPolynomialC m := by
  apply bivariate_exists_of_coeff_lifts
  intro n
  apply hasse_qExpansion_principle
  intro k
  rw [modularPolynomialC_coeff_polynomialIn]
  exact coxPhiFunction_coeff_integerLaurent m n k

/-- The canonical integer descent of the modular polynomial. -/
noncomputable def modularPolynomial (m : ℕ+) : BivariatePolynomial ℤ :=
  (exists_modularPolynomialZ m).choose

theorem modularPolynomial_map_complex (m : ℕ+) :
    BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m) =
      modularPolynomialC m := by
  exact (exists_modularPolynomialZ m).choose_spec

/-- The integral modular polynomial retains the monic normalization in the root variable. -/
theorem modularPolynomial_monic (m : ℕ+) : (modularPolynomial m).Monic := by
  let f := Polynomial.mapRingHom (Int.castRingHom ℂ)
  have hf : Function.Injective f :=
    Polynomial.map_injective _ Int.cast_injective
  apply Polynomial.monic_of_injective hf
  change (BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m)).Monic
  rw [modularPolynomial_map_complex]
  exact modularPolynomialC_monic m

end Cox

