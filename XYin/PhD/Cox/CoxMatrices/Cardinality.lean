/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import XYin.PhD.Cox.CoxMatrices.Basic

/-!
# Cardinality of the Cox representatives

This file proves Cox's formula `|C(m)| = m ∏_{p ∣ m} (1 + 1/p)` for the number of Cox
representatives, i.e. the Dedekind `ψ`-function of `m` (`card_coxMatrix`, with the `ℕ`-valued
form `card_coxMatrix_eq_factorization_prod`), and identifies it with the index of `Γ₀(m)` in
`SL₂(ℤ)` (`gamma0_index_eq_card_coxMatrix`).
-/

open Complex Function MatrixGroups UpperHalfPlane

noncomputable section

namespace Cox

private theorem card_filter_range_coprime_mul_aux (g k : ℕ) :
    ((Finset.range (k * g)).filter (g.Coprime ·)).card = k * g.totient := by
  rw [← Nat.count_eq_card_filter_range]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Nat.count_add']
      simp only [Nat.coprime_add_self_right]
      rw [ih, Nat.count_eq_card_filter_range, ← Nat.totient_eq_card_coprime, Nat.succ_mul]

private def coxFiberAux (m : ℕ+) (d : ℕ) :=
  {b : Fin d // (Nat.gcd ((m : ℕ) / d) d).Coprime b}

private instance (m : ℕ+) (d : ℕ) : Fintype (coxFiberAux m d) :=
  inferInstanceAs
    (Fintype {b : Fin d // (Nat.gcd ((m : ℕ) / d) d).Coprime b})

private theorem card_coxFiber_aux (m : ℕ+) (d : ℕ) :
    Fintype.card (coxFiberAux m d) =
      (d / Nat.gcd ((m : ℕ) / d) d) *
        (Nat.gcd ((m : ℕ) / d) d).totient := by
  let g := Nat.gcd ((m : ℕ) / d) d
  have hgd : g ∣ d := Nat.gcd_dvd_right _ _
  have hmul : d / g * g = d := Nat.div_mul_cancel hgd
  change Fintype.card {b : Fin d // g.Coprime b} = _
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fin.sum_univ_eq_sum_range (fun b ↦ if g.Coprime b then 1 else 0) d, ← Finset.sum_filter,
    ← Finset.card_eq_sum_ones]
  simpa only [hmul] using card_filter_range_coprime_mul_aux g (d / g)

private def coxMatrixToFiberSigmaAux (m : ℕ+) (σ : CoxMatrix m) :
    Σ d : {d : ℕ // d ∈ (m : ℕ).divisors}, coxFiberAux m d :=
  ⟨⟨σ.d, Nat.mem_divisors.mpr ⟨σ.d_dvd, PNat.ne_zero m⟩⟩,
    ⟨⟨σ.b, σ.b_lt⟩, by simpa only [σ.div_d] using σ.coprime_gcd_b⟩⟩

private def fiberSigmaToCoxMatrixAux (m : ℕ+)
    (x : Σ d : {d : ℕ // d ∈ (m : ℕ).divisors}, coxFiberAux m d) : CoxMatrix m where
  a := (m : ℕ) / x.1
  b := x.2.val
  d := x.1
  a_pos := Nat.div_pos (Nat.divisor_le x.1.2) (Nat.pos_of_mem_divisors x.1.2)
  determinant := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors x.1.2)
  b_lt := x.2.val.isLt
  primitive := by
    simpa only [Nat.Coprime, Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc] using x.2.property

private def coxMatrixEquivFiberSigmaAux (m : ℕ+) :
    CoxMatrix m ≃ Σ d : {d : ℕ // d ∈ (m : ℕ).divisors}, coxFiberAux m d where
  toFun := coxMatrixToFiberSigmaAux m
  invFun := fiberSigmaToCoxMatrixAux m
  left_inv σ := CoxMatrix.ext σ.div_d rfl rfl
  right_inv _ := rfl

private theorem card_coxMatrix_eq_divisorSum_aux (m : ℕ+) :
    Fintype.card (CoxMatrix m) =
      ∑ d ∈ (m : ℕ).divisors,
        (d / Nat.gcd ((m : ℕ) / d) d) *
          (Nat.gcd ((m : ℕ) / d) d).totient := by
  rw [Fintype.card_congr (coxMatrixEquivFiberSigmaAux m), Fintype.card_sigma,
    Finset.sum_subtype (m : ℕ).divisors (fun _ ↦ Iff.rfl)]
  exact Fintype.sum_congr _ _ fun d ↦ card_coxFiber_aux m d

private def coxDivisorTermAux (n d : ℕ) : ℕ :=
  (d / Nat.gcd (n / d) d) * (Nat.gcd (n / d) d).totient

private theorem coxDivisorTerm_mul_of_coprime_aux {m n d e : ℕ}
    (hmn : m.Coprime n) (hd : d ∣ m) (he : e ∣ n) :
    coxDivisorTermAux (m * n) (d * e) =
      coxDivisorTermAux m d * coxDivisorTermAux n e := by
  have hMd : m / d ∣ m := ⟨d, (Nat.div_mul_cancel hd).symm⟩
  have hNe : n / e ∣ n := ⟨e, (Nat.div_mul_cancel he).symm⟩
  have hde : d.Coprime e :=
    (hmn.coprime_dvd_left hd).coprime_dvd_right he
  have hNd : (n / e).Coprime d :=
    ((hmn.coprime_dvd_left hd).coprime_dvd_right hNe).symm
  have hMe : (m / d).Coprime e :=
    (hmn.coprime_dvd_left hMd).coprime_dvd_right he
  have hgcd : Nat.gcd (m / d * (n / e)) (d * e) =
      Nat.gcd (m / d) d * Nat.gcd (n / e) e := by
    rw [hde.gcd_mul, hNd.gcd_mul_right_cancel, hMe.gcd_mul_left_cancel]
  have hgg : (Nat.gcd (m / d) d).Coprime (Nat.gcd (n / e) e) :=
    (hmn.coprime_dvd_left ((Nat.gcd_dvd_right _ _).trans hd)).coprime_dvd_right
      ((Nat.gcd_dvd_right _ _).trans he)
  unfold coxDivisorTermAux
  rw [← Nat.div_mul_div_comm hd he, hgcd,
    ← Nat.div_mul_div_comm (Nat.gcd_dvd_right (m / d) d)
      (Nat.gcd_dvd_right (n / e) e), Nat.totient_mul hgg]
  ring

private def coxDivisorSumAux (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, coxDivisorTermAux n d

private theorem coxDivisorSum_mul_of_coprime_aux {m n : ℕ} (hmn : m.Coprime n) :
    coxDivisorSumAux (m * n) = coxDivisorSumAux m * coxDivisorSumAux n := by
  classical
  unfold coxDivisorSumAux
  rw [hmn.divisors_mul]
  rw [Finset.sum_map]
  change (∑ x ∈ (m.divisors ×ˢ n.divisors).attach,
    coxDivisorTermAux (m * n) (x.val.1 * x.val.2)) = _
  rw [Finset.sum_attach _ (fun x : ℕ × ℕ ↦ coxDivisorTermAux (m * n) (x.1 * x.2)),
    Finset.sum_product, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  exact coxDivisorTerm_mul_of_coprime_aux hmn
    (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors he)

private theorem coxDivisorTerm_prime_pow_of_lt_aux {p e i : ℕ}
    (hp : p.Prime) (hie : i < e) :
    coxDivisorTermAux (p ^ e) (p ^ i) = (p ^ i).totient := by
  have hle : i ≤ e := hie.le
  have hsub : 0 < e - i := Nat.sub_pos_of_lt hie
  rw [coxDivisorTermAux, Nat.pow_div hle hp.pos]
  by_cases hhalf : e - i ≤ i
  · have hgcd : Nat.gcd (p ^ (e - i)) (p ^ i) = p ^ (e - i) :=
      Nat.gcd_eq_left_iff_dvd.mpr (Nat.pow_dvd_pow p hhalf)
    have hi : 0 < i := by omega
    rw [hgcd, Nat.pow_div hhalf hp.pos,
      Nat.totient_prime_pow hp (n := e - i) hsub,
      Nat.totient_prime_pow hp (n := i) hi]
    rw [← mul_assoc, ← Nat.pow_add]
    have hexp : i - (e - i) + (e - i - 1) = i - 1 := by omega
    rw [hexp]
  · have hil : i ≤ e - i := Nat.le_of_not_ge hhalf
    have hgcd : Nat.gcd (p ^ (e - i)) (p ^ i) = p ^ i :=
      Nat.gcd_eq_right_iff_dvd.mpr (Nat.pow_dvd_pow p hil)
    rw [hgcd, Nat.div_self (pow_pos hp.pos i), one_mul]

private theorem coxDivisorTerm_prime_pow_self_aux {p e : ℕ} (hp : p.Prime) :
    coxDivisorTermAux (p ^ e) (p ^ e) = p ^ e := by
  rw [coxDivisorTermAux, Nat.div_self (pow_pos hp.pos e)]
  simp

private theorem coxDivisorSum_prime_pow_aux {p e : ℕ}
    (hp : p.Prime) (he : 0 < e) :
    coxDivisorSumAux (p ^ e) = p ^ e + p ^ (e - 1) := by
  rw [coxDivisorSumAux, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ]
  have hsum :
      (∑ i ∈ Finset.range e, coxDivisorTermAux (p ^ e) (p ^ i)) =
        p ^ (e - 1) := by
    calc
      _ = ∑ i ∈ Finset.range e, (p ^ i).totient := by
        apply Finset.sum_congr rfl
        intro i hi
        exact coxDivisorTerm_prime_pow_of_lt_aux hp (Finset.mem_range.mp hi)
      _ = ∑ d ∈ (p ^ (e - 1)).divisors, d.totient := by
        rw [Nat.sum_divisors_prime_pow hp]
        congr 2
        omega
      _ = p ^ (e - 1) := Nat.sum_totient _
  rw [hsum, coxDivisorTerm_prime_pow_self_aux hp, add_comm]

private def coxDivisorSumArithmeticFunctionAux : ArithmeticFunction ℕ :=
  ⟨coxDivisorSumAux, by simp [coxDivisorSumAux]⟩

private theorem coxDivisorSumAF_apply_aux (n : ℕ) :
    coxDivisorSumArithmeticFunctionAux n = coxDivisorSumAux n := rfl

private theorem coxDivisorSumArithmeticFunction_mult_aux :
    coxDivisorSumArithmeticFunctionAux.IsMultiplicative := by
  constructor
  · simp [coxDivisorSumArithmeticFunctionAux, coxDivisorSumAux, coxDivisorTermAux]
  · intro m n hmn
    simpa only [coxDivisorSumAF_apply_aux] using
      coxDivisorSum_mul_of_coprime_aux hmn

private theorem coxDivisorSum_eq_factorizationProd_aux (n : ℕ) (hn : n ≠ 0) :
    coxDivisorSumAux n =
      n.factorization.prod fun p e ↦ p ^ e + p ^ (e - 1) := by
  rw [← coxDivisorSumAF_apply_aux,
    coxDivisorSumArithmeticFunction_mult_aux.multiplicative_factorization
      coxDivisorSumArithmeticFunctionAux hn]
  apply Finsupp.prod_congr
  intro p hp
  have hp' : p.Prime :=
    Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  have he : 0 < n.factorization p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  exact coxDivisorSum_prime_pow_aux hp' he

private theorem cast_prime_pow_add_aux (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    ((p ^ e + p ^ (e - 1) : ℕ) : ℚ) =
      (p : ℚ) ^ e * (1 + 1 / (p : ℚ)) := by
  push_cast
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [mul_add, mul_one, mul_one_div]
  congr 1
  apply (eq_div_iff hpq).mpr
  exact pow_sub_one_mul he.ne' (p : ℚ)

private theorem cast_coxDivisorSum_eq_eulerProduct_aux (n : ℕ) (hn : n ≠ 0) :
    (coxDivisorSumAux n : ℚ) =
      (n : ℚ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ)) := by
  rw [coxDivisorSum_eq_factorizationProd_aux n hn]
  push_cast
  calc
    _ = n.factorization.prod (fun p e ↦
        (p : ℚ) ^ e * (1 + 1 / (p : ℚ))) := by
      apply Finsupp.prod_congr
      intro p hp
      have hp' : p.Prime :=
        Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
      have he : 0 < n.factorization p :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
      simpa only [Nat.cast_add, Nat.cast_pow] using
        cast_prime_pow_add_aux p (n.factorization p) hp' he
    _ = (n.factorization.prod fun p e ↦ (p : ℚ) ^ e) *
        n.factorization.prod fun p _ ↦ (1 + 1 / (p : ℚ)) := Finsupp.prod_mul
    _ = _ := by
      have hprod :
          (n.factorization.prod fun p e ↦ (p : ℚ) ^ e) = (n : ℚ) := by
        exact_mod_cast Nat.prod_factorization_pow_eq_self hn
      rw [hprod]
      rfl

/-- Cox's count `|C(m)| = m ∏_{p∣m}(1+1/p)`, written in `ℚ` to keep the displayed
Euler product literal. -/
theorem card_coxMatrix (m : ℕ+) :
    (Fintype.card (CoxMatrix m) : ℚ) =
      (m : ℚ) * ∏ p ∈ (m : ℕ).primeFactors, (1 + 1 / (p : ℚ)) := by
  calc
    (Fintype.card (CoxMatrix m) : ℚ) = (coxDivisorSumAux m : ℚ) := by
      exact_mod_cast card_coxMatrix_eq_divisorSum_aux m
    _ = _ := cast_coxDivisorSum_eq_eulerProduct_aux m (PNat.ne_zero m)

/-- Cox's count in `ℕ`: `|C(m)| = ∏_{p^e ∥ m} (p^e + p^(e-1))`, the Dedekind `ψ`-function
of `m`. -/
theorem card_coxMatrix_eq_factorization_prod (m : ℕ+) :
    Fintype.card (CoxMatrix m) =
      (m : ℕ).factorization.prod fun p e ↦ p ^ e + p ^ (e - 1) := by
  rw [card_coxMatrix_eq_divisorSum_aux, ← coxDivisorSum_eq_factorizationProd_aux m m.ne_zero]
  rfl

/-- For a prime level `p`, there are `p + 1` Cox matrices. -/
theorem card_coxMatrix_of_prime {p : ℕ+} (hp : (p : ℕ).Prime) :
    Fintype.card (CoxMatrix p) = p + 1 := by
  rw [card_coxMatrix_eq_factorization_prod, Nat.prod_factorization_eq_prod_primeFactors,
    hp.primeFactors, Finset.prod_singleton, hp.factorization_self]
  simp

/-- The index of `Γ₀(m)` in `SL₂(ℤ)` is the number of Cox matrices of determinant `m`. -/
theorem gamma0_index_eq_card_coxMatrix (m : ℕ+) :
    (CongruenceSubgroup.Gamma0 (m : ℕ)).index = Fintype.card (CoxMatrix m) := by
  rw [Subgroup.index_eq_card, Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel
      (s := CongruenceSubgroup.Gamma0 (m : ℕ))).symm,
    Nat.card_congr (coxMatrixEquivRightCosets m).symm, Nat.card_eq_fintype_card]

/-- The index of `Γ₀(m)` in `SL₂(ℤ)` is the Dedekind `ψ`-function `∏_{p^e ∥ m} (p^e + p^(e-1))`. -/
theorem gamma0_index_eq_factorization_prod (m : ℕ+) :
    (CongruenceSubgroup.Gamma0 (m : ℕ)).index =
      (m : ℕ).factorization.prod fun p e ↦ p ^ e + p ^ (e - 1) := by
  rw [gamma0_index_eq_card_coxMatrix, card_coxMatrix_eq_factorization_prod]

end Cox
