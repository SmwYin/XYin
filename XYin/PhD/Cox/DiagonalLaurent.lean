/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.ModularPolynomial

/-!
# The Laurent leading term of the diagonal modular polynomial

This file formalizes Cox equation (11.19). At the width-`m` cusp, `j` has order `-m`, while
the root indexed by `σ` has order `-σ.a ^ 2`. For nonsquare `m` these orders never agree, so
the leading coefficient of every difference is either `1` or a signed power of `ζ_m`.
-/

open UpperHalfPlane

noncomputable section

namespace Cox

private theorem j_widthM_cuspMeromorphicAt (m : ℕ+) :
    MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) j) 0 := by
  simpa using (j_isGamma0ModularFunction m).2.2 1

/-- In the local parameter `q^(1/m)`, the analytic `j`-function has order `-m`. -/
theorem laurentqExpansion_j_order_widthM (m : ℕ+) :
    (laurentqExpansion ((m : ℕ) : ℝ) j).order = -(m : ℤ) := by
  have hpole : poleOrder ((m : ℕ) : ℝ) j = (m : ℕ) := by
    simpa [j_poleOrder] using poleOrder_nat_mul (m := (m : ℕ)) (h := 1) (f := j)
      (PNat.ne_zero m) j_cuspFunction_meromorphicAt j_periodic
  have h := laurentqExpansion.poleOrder_to_order
    (j_widthM_cuspMeromorphicAt m) (by simp [hpole, PNat.ne_zero m])
  rw [hpole] at h
  omega

/-- The leading coefficient of `j` remains one in the width-`m` local parameter. -/
theorem laurentqExpansion_j_leadingCoeff_widthM (m : ℕ+) :
    (laurentqExpansion ((m : ℕ) : ℝ) j).leadingCoeff = 1 := by
  rw [HahnSeries.leadingCoeff_eq, laurentqExpansion_j_order_widthM]
  have h := laurentqExpansion_nat_mul_coeff (h := 1) (m := (m : ℕ))
    (PNat.ne_zero m) j_cuspFunction_meromorphicAt j_periodic (-1)
  rw [show (m : ℤ) * (-1) = -(m : ℤ) by ring] at h
  have h' : (laurentqExpansion ((m : ℕ) : ℝ) j).coeff (-(m : ℤ)) =
      (laurentqExpansion 1 j).coeff (-1) := by
    simpa using h
  rw [h', jIntCoeff_spec, jIntCoeff_neg_one]
  norm_num

private theorem transformedJSeries_coeff_order
    {K : Type*} [Field K] {m : ℕ+} (ζ : K) (σ : CoxMatrix m) :
    (transformedJSeries ζ σ).coeff (-((σ.a : ℤ) ^ 2)) =
      ζ ^ (-((σ.a : ℤ) * (σ.b : ℤ))) := by
  rw [transformedJSeries_coeff]
  have ha : (σ.a : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast σ.a_pos.ne')
  simp [ha, jIntCoeff_neg_one]

/-- A transformed `j`-series with nonzero phase has order `-σ.a ^ 2`. -/
theorem transformedJSeries_order
    {K : Type*} [Field K] {m : ℕ+} (ζ : K) (hζ : ζ ≠ 0) (σ : CoxMatrix m) :
    (transformedJSeries ζ σ).order = -((σ.a : ℤ) ^ 2) := by
  let T := transformedJSeries ζ σ
  have hcoeff : T.coeff (-((σ.a : ℤ) ^ 2)) ≠ 0 := by
    rw [transformedJSeries_coeff_order]
    exact zpow_ne_zero _ hζ
  have htop : T.orderTop = (-((σ.a : ℤ) ^ 2) : ℤ) := by
    apply HahnSeries.orderTop_eq_of_le hcoeff
    intro k hk
    change T.coeff k ≠ 0 at hk
    dsimp only [T] at hk
    rw [transformedJSeries_coeff] at hk
    split_ifs at hk with h
    · exact h.2
    · exact (hk rfl).elim
  have hordTop := HahnSeries.order_eq_orderTop_of_ne_zero
    (HahnSeries.ne_zero_of_coeff_ne_zero hcoeff)
  rw [htop] at hordTop
  exact_mod_cast hordTop

/-- The leading coefficient of a transformed root series is its phase from Cox (11.13). -/
theorem transformedJSeries_leadingCoeff
    {K : Type*} [Field K] {m : ℕ+} (ζ : K) (hζ : ζ ≠ 0) (σ : CoxMatrix m) :
    (transformedJSeries ζ σ).leadingCoeff =
      ζ ^ (-((σ.a : ℤ) * (σ.b : ℤ))) := by
  rw [HahnSeries.leadingCoeff_eq, transformedJSeries_order ζ hζ,
    transformedJSeries_coeff_order]

/-- For nonsquare `m`, the two possible principal exponents in a diagonal Cox factor are
distinct. This is the leading-term calculation in equation (11.19). -/
theorem cox_diagonal_factor_leadingCoeff (m : ℕ+) (hm : ¬ IsSquare (m : ℕ))
    (σ : CoxMatrix m) :
    (laurentqExpansion ((m : ℕ) : ℝ) j -
        transformedJSeries (zeta m) σ).leadingCoeff =
      if σ.a ^ 2 < (m : ℕ) then 1
      else -(zeta m ^ (-((σ.a : ℤ) * (σ.b : ℤ)))) := by
  let J := laurentqExpansion ((m : ℕ) : ℝ) j
  let T := transformedJSeries (zeta m) σ
  have hζ : zeta m ≠ 0 := (zeta_isPrimitiveRoot m).ne_zero (PNat.ne_zero m)
  have hJne : J ≠ 0 := by
    rw [← HahnSeries.leadingCoeff_ne_zero, laurentqExpansion_j_leadingCoeff_widthM]
    exact one_ne_zero
  have hTne : T ≠ 0 := by
    rw [← HahnSeries.leadingCoeff_ne_zero,
      transformedJSeries_leadingCoeff (zeta m) hζ]
    exact zpow_ne_zero _ hζ
  have hJtop : J.orderTop = (-(m : ℤ) : ℤ) := by
    have h := HahnSeries.order_eq_orderTop_of_ne_zero hJne
    rw [laurentqExpansion_j_order_widthM] at h
    exact h.symm
  have hTtop : T.orderTop = (-((σ.a : ℤ) ^ 2) : ℤ) := by
    have h := HahnSeries.order_eq_orderTop_of_ne_zero hTne
    rw [transformedJSeries_order (zeta m) hζ] at h
    exact h.symm
  have hne : σ.a ^ 2 ≠ (m : ℕ) := by
    intro h
    apply hm
    rw [isSquare_iff_exists_sq]
    exact ⟨σ.a, h.symm⟩
  by_cases hlt : σ.a ^ 2 < (m : ℕ)
  · rw [if_pos hlt]
    apply (HahnSeries.leadingCoeff_sub (x := J) (y := T) ?_).trans
      (laurentqExpansion_j_leadingCoeff_widthM m)
    rw [hJtop, hTtop]
    norm_cast
    omega
  · rw [if_neg hlt]
    have hgt : (m : ℕ) < σ.a ^ 2 := lt_of_le_of_ne (Nat.le_of_not_gt hlt) hne.symm
    calc
      (J - T).leadingCoeff = (-(T - J)).leadingCoeff := by congr 1; abel
      _ = -(T - J).leadingCoeff := HahnSeries.leadingCoeff_neg
      _ = -T.leadingCoeff := congrArg Neg.neg <| HahnSeries.leadingCoeff_sub <| by
        rw [hTtop, hJtop]
        norm_cast
        omega
      _ = -(zeta m ^ (-((σ.a : ℤ) * (σ.b : ℤ)))) := by
        rw [transformedJSeries_leadingCoeff (zeta m) hζ]

/-- Every diagonal Cox factor has root-of-unity leading coefficient of exponent `2m`. -/
theorem cox_diagonal_factor_leadingCoeff_pow (m : ℕ+) (hm : ¬ IsSquare (m : ℕ))
    (σ : CoxMatrix m) :
    (laurentqExpansion ((m : ℕ) : ℝ) j -
        transformedJSeries (zeta m) σ).leadingCoeff ^ (2 * (m : ℕ)) = 1 := by
  rw [cox_diagonal_factor_leadingCoeff m hm σ]
  split_ifs
  · simp
  · let x := zeta m ^ (-((σ.a : ℤ) * (σ.b : ℤ)))
    have hx : x ^ (m : ℕ) = 1 := by
      dsimp only [x]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        (zeta_isPrimitiveRoot m).zpow_eq_one, one_zpow]
    calc
      (-x) ^ (2 * (m : ℕ)) = ((-x) ^ 2) ^ (m : ℕ) := by rw [pow_mul]
      _ = (x ^ 2) ^ (m : ℕ) := by congr 1; ring
      _ = (x ^ (m : ℕ)) ^ 2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = 1 := by rw [hx, one_pow]

private theorem laurentqExpansion_j_pow_widthM (m : ℕ+) (n : ℕ) :
    laurentqExpansion ((m : ℕ) : ℝ) (fun τ ↦ j τ ^ n) =
      (laurentqExpansion ((m : ℕ) : ℝ) j) ^ n := by
  have h := laurentqExpansion_finset_prod (h := ((m : ℕ) : ℝ)) (by positivity)
    (Finset.range n) (f := fun _ ↦ j) (fun _ _ ↦ j_widthM_cuspMeromorphicAt m)
  simpa using h

private theorem polynomialIn_widthM_cuspMeromorphicAt (m : ℕ+) (P : Polynomial ℂ) :
    MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (polynomialIn P j)) 0 := by
  simpa using ((j_isGamma0ModularFunction m).polynomialIn P).2.2 1

/-- Laurent expansion commutes with evaluating a polynomial in `j`, at cusp width `m`. -/
theorem laurentqExpansion_polynomialIn_j_widthM (m : ℕ+) (P : Polynomial ℂ) :
    laurentqExpansion ((m : ℕ) : ℝ) (polynomialIn P j) =
      P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
        (laurentqExpansion ((m : ℕ) : ℝ) j) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      calc
        laurentqExpansion ((m : ℕ) : ℝ) (polynomialIn (P + Q) j) =
            laurentqExpansion ((m : ℕ) : ℝ)
              (fun τ ↦ polynomialIn P j τ + polynomialIn Q j τ) := by
          congr 1
          funext τ
          simp [polynomialIn]
        _ = laurentqExpansion ((m : ℕ) : ℝ) (polynomialIn P j) +
              laurentqExpansion ((m : ℕ) : ℝ) (polynomialIn Q j) :=
          laurentqExpansion_add (by positivity)
            (polynomialIn_widthM_cuspMeromorphicAt m P)
            (polynomialIn_widthM_cuspMeromorphicAt m Q)
        _ = (P + Q).eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
              (laurentqExpansion ((m : ℕ) : ℝ) j) := by
          rw [hP, hQ, Polynomial.eval₂_add]
  | monomial n a =>
      have hjpow : MeromorphicAt
          (cuspFunction ((m : ℕ) : ℝ) (fun τ ↦ j τ ^ n)) 0 := by
        simpa [polynomialIn] using
          ((j_isGamma0ModularFunction m).polynomialIn (Polynomial.X ^ n)).2.2 1
      calc
        laurentqExpansion ((m : ℕ) : ℝ)
            (polynomialIn (Polynomial.monomial n a) j) =
            laurentqExpansion ((m : ℕ) : ℝ) (fun τ ↦ a * j τ ^ n) := by
          congr 1
          funext τ
          simp [polynomialIn]
        _ = HahnSeries.C a *
              laurentqExpansion ((m : ℕ) : ℝ) (fun τ ↦ j τ ^ n) := by
          simpa using laurentqExpansion_mul (h := ((m : ℕ) : ℝ)) (by positivity)
            (meromorphicAt_cuspFunction_const ((m : ℕ) : ℝ) a) hjpow
        _ = (Polynomial.monomial n a).eval₂
              (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
              (laurentqExpansion ((m : ℕ) : ℝ) j) := by
          rw [laurentqExpansion_j_pow_widthM, Polynomial.eval₂_monomial]

/-- The formal Cox polynomial is obtained from `Φ_m` by substituting the width-`m` Laurent
series of `j` into its coefficient variable. -/
theorem formalCoxPolynomial_eq_modularPolynomialC_map_j (m : ℕ+) :
    formalCoxPolynomial m (zeta m) =
      Polynomial.map
        (Polynomial.eval₂RingHom (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
          (laurentqExpansion ((m : ℕ) : ℝ) j)) (modularPolynomialC m) := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map, ← coxPhiFunction_coeff_laurentqExpansion_widthM,
    ← modularPolynomialC_coeff_polynomialIn,
    laurentqExpansion_polynomialIn_j_widthM]
  rfl

/-- Substituting the width-`m` Laurent series of `j` into the diagonal of `Φ_m` gives the
product of the diagonal Cox factors. -/
theorem modularPolynomialC_diagonal_series (m : ℕ+) :
    (BivariatePolynomial.diagonal (modularPolynomialC m)).eval₂
        (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
        (laurentqExpansion ((m : ℕ) : ℝ) j) =
      ∏ σ : CoxMatrix m,
        (laurentqExpansion ((m : ℕ) : ℝ) j -
          transformedJSeries (zeta m) σ) := by
  rw [BivariatePolynomial.diagonal_eval₂, ← Polynomial.eval_map,
    ← formalCoxPolynomial_eq_modularPolynomialC_map_j]
  simp [formalCoxPolynomial, Polynomial.eval_prod]

private theorem laurentqExpansion_j_pow_order_widthM (m : ℕ+) (n : ℕ) :
    ((laurentqExpansion ((m : ℕ) : ℝ) j) ^ n).order =
      -((m : ℤ) * (n : ℤ)) := by
  rw [HahnSeries.order_pow, laurentqExpansion_j_order_widthM]
  ring

private theorem laurentqExpansion_j_pow_leadingCoeff_widthM (m : ℕ+) (n : ℕ) :
    ((laurentqExpansion ((m : ℕ) : ℝ) j) ^ n).leadingCoeff = 1 := by
  induction n with
  | zero => simp [HahnSeries.leadingCoeff_one]
  | succ n ih =>
      simp [pow_succ, HahnSeries.leadingCoeff_mul, ih,
        laurentqExpansion_j_leadingCoeff_widthM]

private theorem eval₂_laurentqExpansion_j_coeff_widthM (m : ℕ+) (P : Polynomial ℂ) :
    (P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
      (laurentqExpansion ((m : ℕ) : ℝ) j)).coeff
        (-((m : ℤ) * (P.natDegree : ℤ))) = P.leadingCoeff := by
  rw [Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum]
  calc
    ∑ i ∈ Finset.range (P.natDegree + 1),
        (HahnSeries.C (P.coeff i) *
          (laurentqExpansion ((m : ℕ) : ℝ) j) ^ i).coeff
            (-((m : ℤ) * (P.natDegree : ℤ))) =
        (HahnSeries.C (P.coeff P.natDegree) *
          (laurentqExpansion ((m : ℕ) : ℝ) j) ^ P.natDegree).coeff
            (-((m : ℤ) * (P.natDegree : ℤ))) := by
      apply Finset.sum_eq_single P.natDegree
      · intro n hn hne
        rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
        change P.coeff n *
          ((laurentqExpansion ((m : ℕ) : ℝ) j) ^ n).coeff
            (-((m : ℤ) * (P.natDegree : ℤ))) = 0
        have hnlt : n < P.natDegree := by
          have hnle : n ≤ P.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
          exact lt_of_le_of_ne hnle hne
        have hmpos : (0 : ℤ) < (m : ℕ) := by exact_mod_cast PNat.pos m
        have horder : -((m : ℤ) * (P.natDegree : ℤ)) <
            ((laurentqExpansion ((m : ℕ) : ℝ) j) ^ n).order := by
          rw [laurentqExpansion_j_pow_order_widthM]
          exact neg_lt_neg <| Int.mul_lt_mul_of_pos_left (by exact_mod_cast hnlt) hmpos
        rw [HahnSeries.coeff_eq_zero_of_lt_order horder, mul_zero]
      · simp
    _ = P.leadingCoeff := by
      rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
      change P.coeff P.natDegree *
        ((laurentqExpansion ((m : ℕ) : ℝ) j) ^ P.natDegree).coeff
          (-((m : ℤ) * (P.natDegree : ℤ))) = _
      rw [← laurentqExpansion_j_pow_order_widthM, ← HahnSeries.leadingCoeff_eq,
        laurentqExpansion_j_pow_leadingCoeff_widthM, mul_one,
        Polynomial.coeff_natDegree]

private theorem eval₂_laurentqExpansion_j_coeff_eq_zero_of_lt_widthM
    (m : ℕ+) (P : Polynomial ℂ) (k : ℤ)
    (hk : k < -((m : ℤ) * (P.natDegree : ℤ))) :
    (P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
      (laurentqExpansion ((m : ℕ) : ℝ) j)).coeff k = 0 := by
  rw [Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro n hn
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
  change P.coeff n * ((laurentqExpansion ((m : ℕ) : ℝ) j) ^ n).coeff k = 0
  have hnle : n ≤ P.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hmpos : (0 : ℤ) < (m : ℕ) := by exact_mod_cast PNat.pos m
  have horder : k < ((laurentqExpansion ((m : ℕ) : ℝ) j) ^ n).order := by
    rw [laurentqExpansion_j_pow_order_widthM]
    exact hk.trans_le <| neg_le_neg <| Int.mul_le_mul_of_nonneg_left
      (by exact_mod_cast hnle) hmpos.le
  rw [HahnSeries.coeff_eq_zero_of_lt_order horder, mul_zero]

private theorem eval₂_laurentqExpansion_j_leadingCoeff_widthM
    (m : ℕ+) (P : Polynomial ℂ) :
    (P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
      (laurentqExpansion ((m : ℕ) : ℝ) j)).leadingCoeff = P.leadingCoeff := by
  by_cases hP : P = 0
  · simp [hP]
  let F := P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
    (laurentqExpansion ((m : ℕ) : ℝ) j)
  let k := -((m : ℤ) * (P.natDegree : ℤ))
  have hcoeff : F.coeff k = P.leadingCoeff :=
    eval₂_laurentqExpansion_j_coeff_widthM m P
  have hcoeff0 : F.coeff k ≠ 0 :=
    hcoeff.trans_ne (Polynomial.leadingCoeff_ne_zero.mpr hP)
  have htop : F.orderTop = (k : ℤ) := by
    apply HahnSeries.orderTop_eq_of_le hcoeff0
    intro r hr
    by_contra hkr
    exact hr (eval₂_laurentqExpansion_j_coeff_eq_zero_of_lt_widthM
      m P r (lt_of_not_ge hkr))
  have hF : F ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hcoeff0
  have hord := HahnSeries.order_eq_orderTop_of_ne_zero hF
  rw [htop] at hord
  change F.leadingCoeff = P.leadingCoeff
  rw [HahnSeries.leadingCoeff_eq]
  change F.coeff F.order = P.leadingCoeff
  rw [show F.order = k by exact_mod_cast hord, hcoeff]

private theorem diagonal_cox_product_leadingCoeff_pow
    (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    (∏ σ : CoxMatrix m,
      (laurentqExpansion ((m : ℕ) : ℝ) j -
        transformedJSeries (zeta m) σ)).leadingCoeff ^ (2 * (m : ℕ)) = 1 := by
  classical
  have hprod : ∀ s : Finset (CoxMatrix m),
      (∏ σ ∈ s,
        (laurentqExpansion ((m : ℕ) : ℝ) j -
          transformedJSeries (zeta m) σ)).leadingCoeff ^ (2 * (m : ℕ)) = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [HahnSeries.leadingCoeff_one]
    | insert σ s hσ ih =>
        rw [Finset.prod_insert hσ, HahnSeries.leadingCoeff_mul, mul_pow,
          cox_diagonal_factor_leadingCoeff_pow m hm σ, ih, one_mul]
  simpa using hprod Finset.univ

/-- Cox equation (11.19): for nonsquare `m`, the complex diagonal leading coefficient has
`2m`-th power one. -/
theorem modularPolynomialC_diagonal_leadingCoeff_pow
    (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    (BivariatePolynomial.diagonal (modularPolynomialC m)).leadingCoeff ^
      (2 * (m : ℕ)) = 1 := by
  rw [← eval₂_laurentqExpansion_j_leadingCoeff_widthM m
    (BivariatePolynomial.diagonal (modularPolynomialC m)),
    modularPolynomialC_diagonal_series]
  exact diagonal_cox_product_leadingCoeff_pow m hm

end Cox
