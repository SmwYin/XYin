/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import XYin.PhD.Cox.CoxMatrices.Basic

/-!
# Cardinality of the Cox representatives

This file proves Cox's Euler-product formula for the cardinality of `C(m)`.
-/

open Complex Function MatrixGroups UpperHalfPlane

noncomputable section

namespace Cox

private theorem card_filter_range_coprime_mul_aux (g k : ℕ) :
    ((Finset.range (k * g)).filter (g.Coprime ·)).card = k * g.totient := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hsplit :
          Finset.Ico 0 (k * g) ∪ Finset.Ico (k * g) (k * g + g) =
            Finset.Ico 0 (k * g + g) :=
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (Nat.le_add_right _ _)
      have hdisj : Disjoint
          ((Finset.Ico 0 (k * g)).filter (g.Coprime ·))
          ((Finset.Ico (k * g) (k * g + g)).filter (g.Coprime ·)) :=
        (Finset.Ico_disjoint_Ico_consecutive 0 (k * g) (k * g + g)).mono
          (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      rw [Nat.succ_mul, Finset.range_eq_Ico, ← hsplit, Finset.filter_union,
        Finset.card_union_of_disjoint hdisj, ← Finset.range_eq_Ico, ih,
        Nat.filter_coprime_Ico_eq_totient]
      ring

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
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range (fun b ↦ if g.Coprime b then 1 else 0) d]
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  change ((Finset.range d).filter (g.Coprime ·)).card = _
  change ((Finset.range d).filter (g.Coprime ·)).card = d / g * g.totient
  have hcard := card_filter_range_coprime_mul_aux g (d / g)
  rw [hmul] at hcard
  exact hcard

private def coxMatrixToFiberSigmaAux (m : ℕ+) (σ : CoxMatrix m) :
    Σ d : {d : ℕ // d ∈ (m : ℕ).divisors}, coxFiberAux m d := by
  have hdvd : σ.d ∣ (m : ℕ) :=
    ⟨σ.a, by rw [Nat.mul_comm, σ.determinant]⟩
  have hquot : (m : ℕ) / σ.d = σ.a := by
    rw [← σ.determinant, Nat.mul_div_left _ σ.d_pos]
  refine ⟨⟨σ.d, Nat.mem_divisors.mpr ⟨hdvd, PNat.ne_zero m⟩⟩,
    ⟨⟨σ.b, σ.b_lt⟩, ?_⟩⟩
  rw [hquot]
  simpa only [Nat.Coprime, Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc]
    using σ.primitive

private def fiberSigmaToCoxMatrixAux (m : ℕ+)
    (x : Σ d : {d : ℕ // d ∈ (m : ℕ).divisors}, coxFiberAux m d) :
    CoxMatrix m := by
  let d := x.1.val
  have hdvd : d ∣ (m : ℕ) := Nat.dvd_of_mem_divisors x.1.property
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (PNat.pos m)
  refine
    { a := (m : ℕ) / d
      b := x.2.val
      d := d
      a_pos := Nat.div_pos (Nat.le_of_dvd (PNat.pos m) hdvd) hdpos
      determinant := Nat.div_mul_cancel hdvd
      b_lt := x.2.val.isLt
      primitive := ?_ }
  have hprim := x.2.property
  change Nat.gcd (Nat.gcd ((m : ℕ) / d) x.2.val) d = 1
  simpa only [Nat.Coprime, Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc]
    using hprim

private def coxMatrixEquivFiberSigmaAux (m : ℕ+) :
    CoxMatrix m ≃ Σ d : {d : ℕ // d ∈ (m : ℕ).divisors}, coxFiberAux m d where
  toFun := coxMatrixToFiberSigmaAux m
  invFun := fiberSigmaToCoxMatrixAux m
  left_inv := by
    intro σ
    apply CoxMatrix.toFin_injective
    simp only [CoxMatrix.toFin, fiberSigmaToCoxMatrixAux, coxMatrixToFiberSigmaAux]
    have hquot : (m : ℕ) / σ.d = σ.a := by
      rw [← σ.determinant, Nat.mul_div_left _ σ.d_pos]
    simp [hquot]
  right_inv := by
    rintro ⟨d, b⟩
    rcases d with ⟨d, hd⟩
    rcases b with ⟨b, hb⟩
    rfl

private theorem card_coxMatrix_eq_divisorSum_aux (m : ℕ+) :
    Fintype.card (CoxMatrix m) =
      ∑ d ∈ (m : ℕ).divisors,
        (d / Nat.gcd ((m : ℕ) / d) d) *
          (Nat.gcd ((m : ℕ) / d) d).totient := by
  rw [Fintype.card_congr (coxMatrixEquivFiberSigmaAux m), Fintype.card_sigma]
  rw [Finset.sum_subtype (m : ℕ).divisors (fun _ ↦ Iff.rfl)]
  apply Fintype.sum_congr
  intro d
  exact card_coxFiber_aux m d

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
  trans ∑ x ∈ m.divisors ×ˢ n.divisors,
    coxDivisorTermAux (m * n) (x.1 * x.2)
  · exact Finset.sum_attach (m.divisors ×ˢ n.divisors)
      (fun x : ℕ × ℕ ↦ coxDivisorTermAux (m * n) (x.1 * x.2))
  rw [Finset.sum_product]
  rw [Finset.sum_mul_sum]
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

@[simp] private theorem coxDivisorSumAF_apply_aux (n : ℕ) :
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
  rw [mul_add, mul_one]
  congr 1
  calc
    (p : ℚ) ^ (e - 1) = (p : ℚ) ^ e / (p : ℚ) := by
      symm
      rw [div_eq_iff hpq]
      exact (pow_sub_one_mul he.ne' (p : ℚ)).symm
    _ = (p : ℚ) ^ e * (1 / (p : ℚ)) := by rw [div_eq_mul_inv, one_div]

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

end Cox
