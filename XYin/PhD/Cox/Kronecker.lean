/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

import XYin.PhD.Cox.DiagonalLaurent
import XYin.PhD.Cox.LaurentPolynomialEvaluation

/-!
# Kronecker's congruence for the modular polynomial

This file develops the cyclotomic descent and Laurent-series infrastructure used in the proof
of Cox Theorem 11.18(v). At a prime level, the Cox representatives consist of the `p` matrices
`(1,i;0,p)` and `(p,0;0,1)`. The final Frobenius factorization is proved in
`KroneckerFrobenius.lean`.

`Φ_p(X,Y) = (X^p - Y) * (X - Y^p) mod p`.

The final descent from a specialized identity uses the lowest Laurent coefficient of `P(j)`;
this is Cox Exercise 11.15, formalized in `LaurentPolynomialEvaluation.lean`.
-/

noncomputable section

namespace Cox

open UpperHalfPlane

/-- The prime-level representative `(1,i;0,p)`. -/
def primeLowerCoxMatrix (p : ℕ+) (i : Fin (p : ℕ)) : CoxMatrix p where
  a := 1
  b := i
  d := p
  a_pos := Nat.zero_lt_one
  determinant := Nat.one_mul p
  b_lt := i.isLt
  primitive := by simp

private def primeFinToCoxMatrix (p : ℕ+) : Fin ((p : ℕ) + 1) → CoxMatrix p :=
  Fin.lastCases (sigmaZero p) (primeLowerCoxMatrix p)

@[simp]
private theorem primeFinToCoxMatrix_castSucc (p : ℕ+) (i : Fin (p : ℕ)) :
    primeFinToCoxMatrix p i.castSucc = primeLowerCoxMatrix p i := by
  simp [primeFinToCoxMatrix]

@[simp]
private theorem primeFinToCoxMatrix_last (p : ℕ+) :
    primeFinToCoxMatrix p (Fin.last (p : ℕ)) = sigmaZero p := by
  simp [primeFinToCoxMatrix]

private theorem primeFinToCoxMatrix_surjective
    (p : ℕ+) [hp : Fact (Nat.Prime (p : ℕ))] :
    Function.Surjective (primeFinToCoxMatrix p) := by
  intro σ
  have ha_dvd : σ.a ∣ (p : ℕ) := ⟨σ.d, σ.determinant.symm⟩
  rcases hp.out.eq_one_or_self_of_dvd σ.a ha_dvd with ha | ha
  · have hd : σ.d = (p : ℕ) := by
      have hdet := σ.determinant
      rw [ha] at hdet
      simpa using hdet
    let i : Fin (p : ℕ) := ⟨σ.b, by simpa [hd] using σ.b_lt⟩
    refine ⟨i.castSucc, ?_⟩
    rw [primeFinToCoxMatrix_castSucc]
    apply CoxMatrix.toFin_injective
    simp [CoxMatrix.toFin, primeLowerCoxMatrix, i, ha, hd]
  · have hd : σ.d = 1 := by
      have hdet := σ.determinant
      rw [ha] at hdet
      nlinarith [PNat.pos p]
    have hb : σ.b = 0 := by
      have := σ.b_lt
      lia
    refine ⟨Fin.last (p : ℕ), ?_⟩
    rw [primeFinToCoxMatrix_last]
    apply CoxMatrix.toFin_injective
    simp [CoxMatrix.toFin, sigmaZero, ha, hb, hd]

private theorem primeFinToCoxMatrix_injective
    (p : ℕ+) [hp : Fact (Nat.Prime (p : ℕ))] :
    Function.Injective (primeFinToCoxMatrix p) := by
  intro i j h
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · apply Fin.ext
      have hb := congrArg CoxMatrix.b h
      simpa [primeLowerCoxMatrix] using hb
    · exfalso
      have ha := congrArg CoxMatrix.a h
      have ha' : 1 = (p : ℕ) := by
        simpa only [primeFinToCoxMatrix_castSucc, primeFinToCoxMatrix_last,
          primeLowerCoxMatrix, sigmaZero] using ha
      exact hp.out.ne_one ha'.symm
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · exfalso
      have ha := congrArg CoxMatrix.a h
      have ha' : (p : ℕ) = 1 := by
        simpa only [primeFinToCoxMatrix_castSucc, primeFinToCoxMatrix_last,
          primeLowerCoxMatrix, sigmaZero] using ha
      exact hp.out.ne_one ha'
    · rfl

private noncomputable def primeFinEquivCoxMatrix
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    Fin ((p : ℕ) + 1) ≃ CoxMatrix p :=
  Equiv.ofBijective (primeFinToCoxMatrix p) <|
    ⟨primeFinToCoxMatrix_injective p, primeFinToCoxMatrix_surjective p⟩

@[simp]
private theorem primeFinEquivCoxMatrix_apply_of_lt
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (i : Fin ((p : ℕ) + 1)) (hi : (i : ℕ) < (p : ℕ)) :
    primeFinEquivCoxMatrix p i = primeLowerCoxMatrix p ⟨i, hi⟩ := by
  let j : Fin (p : ℕ) := ⟨i, hi⟩
  have hij : i = j.castSucc := Fin.ext rfl
  change primeFinToCoxMatrix p i = primeLowerCoxMatrix p j
  rw [hij, primeFinToCoxMatrix_castSucc]

@[simp]
private theorem primeFinEquivCoxMatrix_apply_last
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    primeFinEquivCoxMatrix p (Fin.last (p : ℕ)) = sigmaZero p := by
  change primeFinToCoxMatrix p (Fin.last (p : ℕ)) = sigmaZero p
  exact primeFinToCoxMatrix_last p

/-- For a prime `p`, Cox's representatives are the `p` matrices `(1,i;0,p)` together with
`(p,0;0,1)`. -/
noncomputable def primeCoxMatrixEquiv
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    CoxMatrix p ≃ Fin ((p : ℕ) + 1) :=
  (primeFinEquivCoxMatrix p).symm

@[simp]
theorem primeCoxMatrixEquiv_symm_apply_of_lt
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (i : Fin ((p : ℕ) + 1)) (hi : (i : ℕ) < (p : ℕ)) :
    (primeCoxMatrixEquiv p).symm i = primeLowerCoxMatrix p ⟨i, hi⟩ := by
  exact primeFinEquivCoxMatrix_apply_of_lt p i hi

@[simp]
theorem primeCoxMatrixEquiv_symm_apply_last
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    (primeCoxMatrixEquiv p).symm (Fin.last (p : ℕ)) = sigmaZero p := by
  exact primeFinEquivCoxMatrix_apply_last p

/-- The integral Laurent coefficients of `j` vanish below its simple pole. -/
theorem jIntCoeff_eq_zero_of_lt {n : ℤ} (hn : n < -(1 : ℤ)) :
    jIntCoeff n = 0 := by
  have hcoeff : (laurentqExpansion 1 j).coeff n = 0 := by
    apply laurentqExpansion.coeff_eq_zero_of_lt
    simpa [j_poleOrder] using hn
  have hcast : (jIntCoeff n : ℂ) = 0 := by
    rw [← jIntCoeff_spec]
    exact hcoeff
  exact_mod_cast hcast

/-- The integral Laurent series whose coefficients are the integral coefficients of `j`. -/
def jIntegralLaurentSeries : LaurentSeries ℤ where
  coeff := jIntCoeff
  isPWO_support' := by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨-1, ?_⟩
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    by_contra h
    exact hn (jIntCoeff_eq_zero_of_lt (lt_of_not_ge h))

@[simp]
theorem jIntegralLaurentSeries_coeff (n : ℤ) :
    jIntegralLaurentSeries.coeff n = jIntCoeff n :=
  rfl

theorem jIntegralLaurentSeries_map_complex :
    jIntegralLaurentSeries.map (Int.castRingHom ℂ) =
      laurentqExpansion 1 j := by
  ext n
  change (jIntCoeff n : ℂ) = (laurentqExpansion 1 j).coeff n
  exact (jIntCoeff_spec n).symm

/-- The integral Laurent expansion of `j` in the local parameter of width `m`. -/
def jIntegralLaurentSeriesWidth (m : ℕ+) : LaurentSeries ℤ where
  coeff k := if (m : ℤ) ∣ k ∧ -(m : ℤ) ≤ k then
    jIntCoeff (k / (m : ℤ)) else 0
  isPWO_support' := by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨-(m : ℤ), ?_⟩
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    split_ifs at hk with h
    · exact h.2
    · exact (hk rfl).elim

@[simp]
theorem jIntegralLaurentSeriesWidth_coeff (m : ℕ+) (k : ℤ) :
    (jIntegralLaurentSeriesWidth m).coeff k =
      if (m : ℤ) ∣ k ∧ -(m : ℤ) ≤ k then
        jIntCoeff (k / (m : ℤ)) else 0 :=
  rfl

private theorem jIntegralLaurentSeriesWidth_coeff_mul_map_complex
    (m : ℕ+) (q : ℤ) :
    ((jIntegralLaurentSeriesWidth m).coeff ((m : ℤ) * q) : ℂ) =
      (laurentqExpansion ((m : ℕ) : ℝ) j).coeff ((m : ℤ) * q) := by
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast PNat.ne_zero m
  have hmpos : (0 : ℤ) < (m : ℕ) := by exact_mod_cast PNat.pos m
  have hscale :
      (laurentqExpansion ((m : ℕ) : ℝ) j).coeff ((m : ℤ) * q) =
        (laurentqExpansion 1 j).coeff q := by
    simpa using laurentqExpansion_nat_mul_coeff
      (h := 1) (m := (m : ℕ)) (PNat.ne_zero m)
      j_cuspFunction_meromorphicAt j_periodic q
  rw [jIntegralLaurentSeriesWidth_coeff]
  by_cases hq : -(1 : ℤ) ≤ q
  · have hlower : -(m : ℤ) ≤ (m : ℤ) * q := by
      simpa using Int.mul_le_mul_of_nonneg_left hq hmpos.le
    rw [if_pos ⟨dvd_mul_right (m : ℤ) q, hlower⟩,
      Int.mul_ediv_cancel_left q hmZ]
    simpa using (hscale.trans (jIntCoeff_spec q)).symm
  · have hlt : (m : ℤ) * q < -(m : ℤ) := by
      simpa using Int.mul_lt_mul_of_pos_left (lt_of_not_ge hq) hmpos
    rw [if_neg (fun h ↦ (not_le_of_gt hlt) h.2), hscale,
      jIntCoeff_spec, jIntCoeff_eq_zero_of_lt (lt_of_not_ge hq)]

/-- The integral width-`m` series recovers the analytic Laurent expansion over `ℂ`. -/
theorem jIntegralLaurentSeriesWidth_map_complex (m : ℕ+) :
    (jIntegralLaurentSeriesWidth m).map (Int.castRingHom ℂ) =
      laurentqExpansion ((m : ℕ) : ℝ) j := by
  ext k
  change ((jIntegralLaurentSeriesWidth m).coeff k : ℂ) =
    (laurentqExpansion ((m : ℕ) : ℝ) j).coeff k
  by_cases hdiv : (m : ℤ) ∣ k
  · obtain ⟨q, rfl⟩ := hdiv
    exact jIntegralLaurentSeriesWidth_coeff_mul_map_complex m q
  · rw [jIntegralLaurentSeriesWidth_coeff, if_neg (fun h ↦ hdiv h.1)]
    simpa using (laurentqExpansion_nat_mul_coeff_of_not_dvd
      (h := 1) (m := (m : ℕ)) (PNat.ne_zero m)
      j_cuspFunction_meromorphicAt j_periodic hdiv).symm

/-- The reduction of the unit-step integral `j`-series modulo `p`. -/
def jUnitLaurentSeriesMod (p : ℕ+) : LaurentSeries (ZMod (p : ℕ)) :=
  jIntegralLaurentSeries.map (Int.castRingHom (ZMod (p : ℕ)))

@[simp]
theorem jUnitLaurentSeriesMod_coeff (p : ℕ+) (n : ℤ) :
    (jUnitLaurentSeriesMod p).coeff n = (jIntCoeff n : ZMod (p : ℕ)) :=
  rfl

theorem jUnitLaurentSeriesMod_coeff_neg_one (p : ℕ+) :
    (jUnitLaurentSeriesMod p).coeff (-1) = 1 := by
  rw [jUnitLaurentSeriesMod_coeff, jIntCoeff_neg_one]
  simp

private theorem jUnitLaurentSeriesMod_coeff_eq_zero_of_lt
    (p : ℕ+) {n : ℤ} (hn : n < -(1 : ℤ)) :
    (jUnitLaurentSeriesMod p).coeff n = 0 := by
  rw [jUnitLaurentSeriesMod_coeff, jIntCoeff_eq_zero_of_lt hn]
  simp

private theorem jUnitLaurentSeriesMod_order
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    (jUnitLaurentSeriesMod p).order = -1 := by
  letI : Fact (1 < (p : ℕ)) := ⟨(Fact.out : Nat.Prime (p : ℕ)).one_lt⟩
  let F := jUnitLaurentSeriesMod p
  have hcoeff : F.coeff (-1) ≠ 0 := by
    dsimp only [F]
    rw [jUnitLaurentSeriesMod_coeff_neg_one p]
    exact one_ne_zero
  have htop : F.orderTop = (-1 : ℤ) := by
    apply HahnSeries.orderTop_eq_of_le hcoeff
    intro k hk
    by_contra h
    exact hk (jUnitLaurentSeriesMod_coeff_eq_zero_of_lt p (lt_of_not_ge h))
  have h := HahnSeries.order_eq_orderTop_of_ne_zero
    (HahnSeries.ne_zero_of_coeff_ne_zero hcoeff)
  rw [htop] at h
  exact_mod_cast h

private theorem powerSeries_pow_prime_eq_expand
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (F : PowerSeries (ZMod (p : ℕ))) :
    F ^ (p : ℕ) = F.expand (p : ℕ) (PNat.ne_zero p) := by
  have h := @MvPowerSeries.map_frobenius_expand Unit (ZMod (p : ℕ)) _
    (p : ℕ) (PNat.ne_zero p) _ (f := F)
  change PowerSeries.map (frobenius (ZMod (p : ℕ)) (p : ℕ))
      (F.expand (p : ℕ) (PNat.ne_zero p)) = F ^ (p : ℕ) at h
  have hmap : PowerSeries.map (frobenius (ZMod (p : ℕ)) (p : ℕ))
      (F.expand (p : ℕ) (PNat.ne_zero p)) =
        F.expand (p : ℕ) (PNat.ne_zero p) := by
    ext n
    rw [PowerSeries.coeff_map]
    exact ZMod.pow_card _
  rw [hmap] at h
  exact h.symm

/-- The reduction of `j` in the width-`p` parameter, whose exponents are multiples of `p`. -/
def jLaurentSeriesMod (p : ℕ+) : LaurentSeries (ZMod (p : ℕ)) where
  coeff k := if (p : ℤ) ∣ k ∧ -(p : ℤ) ≤ k then
    (jIntCoeff (k / (p : ℤ)) : ZMod (p : ℕ)) else 0
  isPWO_support' := by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨-(p : ℤ), ?_⟩
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    split_ifs at hk with h
    · exact h.2
    · exact (hk rfl).elim

theorem jLaurentSeriesMod_coeff (p : ℕ+) (k : ℤ) :
    (jLaurentSeriesMod p).coeff k =
      if (p : ℤ) ∣ k ∧ -(p : ℤ) ≤ k then
        (jIntCoeff (k / (p : ℤ)) : ZMod (p : ℕ)) else 0 :=
  rfl

/-- Reducing the integral width-`p` series gives the width-`p` series over `ZMod p`. -/
theorem jIntegralLaurentSeriesWidth_map_zmod (p : ℕ+) :
    (jIntegralLaurentSeriesWidth p).map
        (Int.castRingHom (ZMod (p : ℕ))) =
      jLaurentSeriesMod p := by
  ext k
  change ((jIntegralLaurentSeriesWidth p).coeff k : ZMod (p : ℕ)) =
    (jLaurentSeriesMod p).coeff k
  rw [jIntegralLaurentSeriesWidth_coeff, jLaurentSeriesMod_coeff]
  split_ifs <;> simp

private theorem jLaurentSeriesMod_coeff_neg_p (p : ℕ+) :
    (jLaurentSeriesMod p).coeff (-(p : ℤ)) = 1 := by
  rw [jLaurentSeriesMod_coeff]
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast PNat.ne_zero p
  rw [if_pos ⟨dvd_neg.mpr (dvd_refl (p : ℤ)), le_rfl⟩]
  rw [Int.ediv_eq_of_eq_mul_left (a := -(p : ℤ)) (b := (p : ℤ)) (c := -1)
    hp0 (by ring), jIntCoeff_neg_one]
  simp

theorem jLaurentSeriesMod_order (p : ℕ+) (hp : 1 < (p : ℕ)) :
    (jLaurentSeriesMod p).order = -(p : ℤ) := by
  letI : Fact (1 < (p : ℕ)) := ⟨hp⟩
  let F := jLaurentSeriesMod p
  have hcoeff : F.coeff (-(p : ℤ)) ≠ 0 := by
    dsimp only [F]
    rw [jLaurentSeriesMod_coeff_neg_p p]
    exact one_ne_zero
  have htop : F.orderTop = (-(p : ℤ) : ℤ) := by
    apply HahnSeries.orderTop_eq_of_le hcoeff
    intro k hk
    change F.coeff k ≠ 0 at hk
    dsimp only [F] at hk
    rw [jLaurentSeriesMod_coeff] at hk
    split_ifs at hk with h
    · exact h.2
    · exact (hk rfl).elim
  have h := HahnSeries.order_eq_orderTop_of_ne_zero
    (HahnSeries.ne_zero_of_coeff_ne_zero hcoeff)
  rw [htop] at h
  exact_mod_cast h

theorem jLaurentSeriesMod_leadingCoeff (p : ℕ+) (hp : 1 < (p : ℕ)) :
    (jLaurentSeriesMod p).leadingCoeff = 1 := by
  rw [HahnSeries.leadingCoeff_eq, jLaurentSeriesMod_order p hp,
    jLaurentSeriesMod_coeff_neg_p]

private noncomputable def jUnitLaurentSeriesModPrimeNormalForm
    (p : ℕ+) : LaurentSeries (ZMod (p : ℕ)) :=
  HahnSeries.single (-(p : ℤ)) 1 *
    (((jUnitLaurentSeriesMod p).powerSeriesPart.expand
      (p : ℕ) (PNat.ne_zero p) : PowerSeries (ZMod (p : ℕ))) :
        LaurentSeries (ZMod (p : ℕ)))

private theorem jUnitLaurentSeriesMod_pow_prime_normalForm
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    jUnitLaurentSeriesMod p ^ (p : ℕ) =
      jUnitLaurentSeriesModPrimeNormalForm p := by
  unfold jUnitLaurentSeriesModPrimeNormalForm
  let F := jUnitLaurentSeriesMod p
  let P := F.powerSeriesPart
  have hdecomp : HahnSeries.single (-1 : ℤ) 1 *
      (P : LaurentSeries (ZMod (p : ℕ))) = F := by
    have h := F.single_order_mul_powerSeriesPart
    have horder : F.order = -1 := jUnitLaurentSeriesMod_order p
    rw [horder] at h
    simpa only [P] using h
  calc
    F ^ (p : ℕ) =
        (HahnSeries.single (-1 : ℤ) 1 *
          (P : LaurentSeries (ZMod (p : ℕ)))) ^ (p : ℕ) := by
      rw [hdecomp]
    _ = (HahnSeries.single (-1 : ℤ) 1) ^ (p : ℕ) *
        (P : LaurentSeries (ZMod (p : ℕ))) ^ (p : ℕ) := mul_pow _ _ _
    _ = HahnSeries.single (-(p : ℤ)) 1 *
        ((P ^ (p : ℕ) : PowerSeries (ZMod (p : ℕ))) :
          LaurentSeries (ZMod (p : ℕ))) := by
      rw [HahnSeries.single_pow]
      simp only [nsmul_eq_mul, mul_neg, mul_one, one_pow]
      congr 1
      exact ((HahnSeries.ofPowerSeries ℤ (ZMod (p : ℕ))).map_pow P (p : ℕ)).symm
    _ = HahnSeries.single (-(p : ℤ)) 1 *
        ((P.expand (p : ℕ) (PNat.ne_zero p) :
          PowerSeries (ZMod (p : ℕ))) : LaurentSeries (ZMod (p : ℕ))) := by
      rw [powerSeries_pow_prime_eq_expand]

private theorem jUnitPrimeNormalForm_coeff_mul_of_lower
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (q : ℤ)
    (hq : -(1 : ℤ) ≤ q) :
    (jUnitLaurentSeriesModPrimeNormalForm p).coeff ((p : ℤ) * q) =
      (jIntCoeff q : ZMod (p : ℕ)) := by
  rw [jUnitLaurentSeriesModPrimeNormalForm, HahnSeries.coeff_single_mul]
  simp only [one_mul, sub_neg_eq_add]
  let n := Int.toNat (q + 1)
  have hn0 : 0 ≤ q + 1 := by lia
  have hncast : (n : ℤ) = q + 1 := by
    simp [n, Int.toNat_of_nonneg hn0]
  have hindex : (p : ℤ) * q + (p : ℤ) = ((p : ℕ) * n : ℕ) := by
    push_cast
    rw [hncast]
    ring
  rw [hindex, LaurentSeries.coeff_coe_powerSeries,
    PowerSeries.coeff_expand_mul]
  rw [LaurentSeries.powerSeriesPart_coeff, jUnitLaurentSeriesMod_order]
  rw [show (-1 : ℤ) + (n : ℤ) = q by
        rw [hncast]
        lia,
    jUnitLaurentSeriesMod_coeff]

private theorem jUnitPrimeNormalForm_coeff_mul_of_lt
    (p : ℕ+) (q : ℤ) (hq : q < -(1 : ℤ)) :
    (jUnitLaurentSeriesModPrimeNormalForm p).coeff ((p : ℤ) * q) = 0 := by
  rw [jUnitLaurentSeriesModPrimeNormalForm, HahnSeries.coeff_single_mul]
  simp only [one_mul, sub_neg_eq_add]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨n, hn⟩
  have hpZ : (0 : ℤ) < (p : ℕ) := by exact_mod_cast PNat.pos p
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  rw [show (p : ℤ) * q + (p : ℤ) = (p : ℤ) * (q + 1) by ring] at hn
  have hneg : (p : ℤ) * (q + 1) < 0 := by
    exact mul_neg_of_pos_of_neg hpZ (by lia)
  exact (not_le_of_gt hneg) (hn ▸ hn0)

private theorem jUnitPrimeNormalForm_coeff_mul
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (q : ℤ) :
    (jUnitLaurentSeriesModPrimeNormalForm p).coeff ((p : ℤ) * q) =
      (jLaurentSeriesMod p).coeff ((p : ℤ) * q) := by
  rw [jLaurentSeriesMod_coeff]
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast PNat.ne_zero p
  have hpZ : (0 : ℤ) < (p : ℕ) := by exact_mod_cast PNat.pos p
  by_cases hq : -(1 : ℤ) ≤ q
  · have hlower : -(p : ℤ) ≤ (p : ℤ) * q := by
      simpa using Int.mul_le_mul_of_nonneg_left hq hpZ.le
    rw [if_pos ⟨dvd_mul_right (p : ℤ) q, hlower⟩,
      Int.mul_ediv_cancel_left q hp0]
    exact jUnitPrimeNormalForm_coeff_mul_of_lower p q hq
  · have hlt : (p : ℤ) * q < -(p : ℤ) := by
      simpa using Int.mul_lt_mul_of_pos_left (lt_of_not_ge hq) hpZ
    rw [if_neg (fun h ↦ (not_le_of_gt hlt) h.2)]
    exact jUnitPrimeNormalForm_coeff_mul_of_lt p q (lt_of_not_ge hq)

private theorem jUnitPrimeNormalForm_coeff_of_not_dvd
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] {k : ℤ}
    (hdiv : ¬(p : ℤ) ∣ k) :
    (jUnitLaurentSeriesModPrimeNormalForm p).coeff k =
      (jLaurentSeriesMod p).coeff k := by
  rw [jLaurentSeriesMod_coeff, if_neg (fun h ↦ hdiv h.1)]
  rw [jUnitLaurentSeriesModPrimeNormalForm, HahnSeries.coeff_single_mul]
  simp only [one_mul, sub_neg_eq_add]
  by_cases hs : 0 ≤ k + (p : ℤ)
  · rw [← Int.toNat_of_nonneg hs, LaurentSeries.coeff_coe_powerSeries]
    apply PowerSeries.coeff_expand_of_not_dvd
    rintro ⟨a, ha⟩
    apply hdiv
    refine ⟨(a : ℤ) - 1, ?_⟩
    have haZ := congrArg (fun x : ℕ ↦ (x : ℤ)) ha
    push_cast at haZ
    rw [Int.toNat_of_nonneg hs] at haZ
    linear_combination haZ
  · apply HahnSeries.embDomain_notin_range
    rintro ⟨n, hn⟩
    exact hs (hn ▸ Int.natCast_nonneg n)

theorem jUnitLaurentSeriesMod_pow_prime
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    jUnitLaurentSeriesMod p ^ (p : ℕ) = jLaurentSeriesMod p := by
  rw [jUnitLaurentSeriesMod_pow_prime_normalForm]
  ext k
  by_cases hdiv : (p : ℤ) ∣ k
  · obtain ⟨q, rfl⟩ := hdiv
    exact jUnitPrimeNormalForm_coeff_mul p q
  · exact jUnitPrimeNormalForm_coeff_of_not_dvd p hdiv

/-- Substitute the width-`p` Laurent series of `j` for the coefficient variable `Y`. -/
noncomputable def specializeJMod (p : ℕ+) :
    BivariatePolynomial (ZMod (p : ℕ)) →+*
      Polynomial (LaurentSeries (ZMod (p : ℕ))) :=
  bivariateSpecializeLaurent (jLaurentSeriesMod p)

@[simp]
theorem specializeJMod_varX (p : ℕ+) :
    specializeJMod p
        (BivariatePolynomial.varX : BivariatePolynomial (ZMod (p : ℕ))) =
      Polynomial.X := by
  simp [specializeJMod, bivariateSpecializeLaurent, BivariatePolynomial.varX]

@[simp]
theorem specializeJMod_varY (p : ℕ+) :
    specializeJMod p
        (BivariatePolynomial.varY : BivariatePolynomial (ZMod (p : ℕ))) =
      Polynomial.C (jLaurentSeriesMod p) := by
  simp [specializeJMod, bivariateSpecializeLaurent, BivariatePolynomial.varY]

/-- Substitute the integral width-`m` expansion of `j` for the coefficient variable `Y`. -/
def specializeJIntegral (m : ℕ+) :
    BivariatePolynomial ℤ →+* Polynomial (LaurentSeries ℤ) :=
  bivariateSpecializeLaurent (jIntegralLaurentSeriesWidth m)

/-- Reduction modulo `p` commutes with integral specialization at the width-`p` `j`-series. -/
theorem specializeJIntegral_map_zmod (p : ℕ+) (F : BivariatePolynomial ℤ) :
    (specializeJIntegral p F).map
        (laurentSeriesMapRingHom (Int.castRingHom (ZMod (p : ℕ)))) =
      specializeJMod p
        (BivariatePolynomial.map (Int.castRingHom (ZMod (p : ℕ))) F) := by
  have hJ : (laurentSeriesMapRingHom (Int.castRingHom (ZMod (p : ℕ))))
      (jIntegralLaurentSeriesWidth p) = jLaurentSeriesMod p := by
    exact jIntegralLaurentSeriesWidth_map_zmod p
  simpa only [specializeJIntegral, specializeJMod, BivariatePolynomial.map] using
    bivariateSpecializeLaurent_map_apply
      (Int.castRingHom (ZMod (p : ℕ)))
      (jIntegralLaurentSeriesWidth p) (jLaurentSeriesMod p) hJ F

/-- Mapping the integral specialization to `ℂ` gives specialization at the analytic
width-`m` Laurent expansion of `j`. -/
theorem specializeJIntegral_map_complex (m : ℕ+) (F : BivariatePolynomial ℤ) :
    (specializeJIntegral m F).map
        (laurentSeriesMapRingHom (Int.castRingHom ℂ)) =
      Polynomial.map
        (Polynomial.eval₂RingHom (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
          (laurentqExpansion ((m : ℕ) : ℝ) j))
        (BivariatePolynomial.map (Int.castRingHom ℂ) F) := by
  have hJ : (laurentSeriesMapRingHom (Int.castRingHom ℂ))
      (jIntegralLaurentSeriesWidth m) =
        laurentqExpansion ((m : ℕ) : ℝ) j := by
    exact jIntegralLaurentSeriesWidth_map_complex m
  simpa only [specializeJIntegral, BivariatePolynomial.map,
    bivariateSpecializeLaurent] using
    bivariateSpecializeLaurent_map_apply
      (Int.castRingHom ℂ) (jIntegralLaurentSeriesWidth m)
      (laurentqExpansion ((m : ℕ) : ℝ) j) hJ F

/-- The integral specialization of the modular polynomial becomes its formal Cox product
after extending coefficients to `ℂ`. -/
theorem specializeJIntegral_modularPolynomial_map_complex (m : ℕ+) :
    (specializeJIntegral m (modularPolynomial m)).map
        (laurentSeriesMapRingHom (Int.castRingHom ℂ)) =
      formalCoxPolynomial m (zeta m) := by
  rw [specializeJIntegral_map_complex, modularPolynomial_map_complex,
    ← formalCoxPolynomial_eq_modularPolynomialC_map_j]

/-- Exercise 11.15, the coefficientwise Hasse q-expansion principle modulo `p`. -/
theorem specializeJMod_injective
    (p : ℕ+) [hp : Fact (Nat.Prime (p : ℕ))] :
    Function.Injective (specializeJMod p) := by
  apply Polynomial.map_injective
  exact polynomial_eval₂_laurentSeries_injective
    (jLaurentSeriesMod p) (p : ℕ) (PNat.pos p)
      (jLaurentSeriesMod_order p hp.out.one_lt)
      (jLaurentSeriesMod_leadingCoeff p hp.out.one_lt)

/-- An integral polynomial lift of a power of the `p`-th-root phase. -/
def phasePolynomial (p : ℕ+) (e : ℤ) : Polynomial ℤ :=
  Polynomial.X ^ Int.toNat (e % (p : ℤ))

private theorem phasePolynomial_eval_zeta (p : ℕ+) (e : ℤ) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (zeta p) (phasePolynomial p e) =
      zeta p ^ e := by
  rw [phasePolynomial, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    ← zpow_natCast, Int.toNat_of_nonneg]
  · let u : ℂˣ := Units.mk0 (zeta p)
      ((zeta_isPrimitiveRoot p).ne_zero (PNat.ne_zero p))
    have hu : u ^ (p : ℕ) = 1 := by
      apply Units.ext
      simpa [u] using (zeta_isPrimitiveRoot p).pow_eq_one
    have hemod := zpow_eq_zpow_emod' (x := u) e hu
    have hval := congrArg (fun v : ℂˣ ↦ (v : ℂ)) hemod
    simpa only [Units.val_zpow_eq_zpow_val] using hval.symm
  · exact Int.emod_nonneg e (by exact_mod_cast PNat.ne_zero p)

private theorem phasePolynomial_eval_one (p : ℕ+) (e : ℤ) :
    Polynomial.eval₂ (Int.castRingHom (ZMod (p : ℕ))) 1
        (phasePolynomial p e) = 1 := by
  simp [phasePolynomial]

/-- The integral cyclotomic lift of a transformed `j`-series. -/
noncomputable def cyclotomicTransformedJSeries
    (p : ℕ+) (σ : CoxMatrix p) : LaurentSeries (Polynomial ℤ) :=
  ⟨fun k ↦ if (σ.a : ℤ) ^ 2 ∣ k ∧ -((σ.a : ℤ) ^ 2) ≤ k
      then Polynomial.C (jIntCoeff (k / (σ.a : ℤ) ^ 2)) *
        phasePolynomial p (((σ.a : ℤ) * (σ.b : ℤ)) *
          (k / (σ.a : ℤ) ^ 2))
      else 0,
   by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨-((σ.a : ℤ) ^ 2), fun k hk ↦ ?_⟩
    simp only [Function.mem_support, ne_eq] at hk
    by_contra h
    apply hk
    rw [if_neg]
    exact fun h' ↦ h h'.2⟩

theorem cyclotomicTransformedJSeries_coeff
    (p : ℕ+) (σ : CoxMatrix p) (k : ℤ) :
    (cyclotomicTransformedJSeries p σ).coeff k =
      if (σ.a : ℤ) ^ 2 ∣ k ∧ -((σ.a : ℤ) ^ 2) ≤ k
      then Polynomial.C (jIntCoeff (k / (σ.a : ℤ) ^ 2)) *
        phasePolynomial p (((σ.a : ℤ) * (σ.b : ℤ)) *
          (k / (σ.a : ℤ) ^ 2))
      else 0 :=
  rfl

/-- Evaluate the integral phase variable at the analytic primitive root. -/
def phaseEvalComplex (p : ℕ+) : Polynomial ℤ →+* ℂ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℂ) (zeta p)

/-- Reduce the integral phase coefficients modulo `p` and set the phase variable to one. -/
def phaseEvalMod (p : ℕ+) : Polynomial ℤ →+* ZMod (p : ℕ) :=
  Polynomial.eval₂RingHom (Int.castRingHom (ZMod (p : ℕ))) 1

theorem cyclotomicTransformedJSeries_map_complex
    (p : ℕ+) (σ : CoxMatrix p) :
    laurentSeriesMapRingHom (phaseEvalComplex p)
        (cyclotomicTransformedJSeries p σ) =
      transformedJSeries (zeta p) σ := by
  ext k
  rw [laurentSeriesMapRingHom_coeff, cyclotomicTransformedJSeries_coeff,
    transformedJSeries_coeff]
  split_ifs
  · rw [map_mul]
    change Polynomial.eval₂ (Int.castRingHom ℂ) (zeta p)
        (Polynomial.C (jIntCoeff (k / (σ.a : ℤ) ^ 2))) *
        Polynomial.eval₂ (Int.castRingHom ℂ) (zeta p)
          (phasePolynomial p (((σ.a : ℤ) * (σ.b : ℤ)) *
            (k / (σ.a : ℤ) ^ 2))) = _
    rw [Polynomial.eval₂_C, phasePolynomial_eval_zeta]
    rfl
  · exact map_zero (phaseEvalComplex p)

theorem cyclotomicTransformedJSeries_map_mod
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (σ : CoxMatrix p) :
    laurentSeriesMapRingHom (phaseEvalMod p)
        (cyclotomicTransformedJSeries p σ) =
      transformedJSeries (1 : ZMod (p : ℕ)) σ := by
  ext k
  rw [laurentSeriesMapRingHom_coeff, cyclotomicTransformedJSeries_coeff,
    transformedJSeries_coeff]
  split_ifs
  · rw [map_mul]
    change Polynomial.eval₂ (Int.castRingHom (ZMod (p : ℕ))) 1
        (Polynomial.C (jIntCoeff (k / (σ.a : ℤ) ^ 2))) *
        Polynomial.eval₂ (Int.castRingHom (ZMod (p : ℕ))) 1
          (phasePolynomial p (((σ.a : ℤ) * (σ.b : ℤ)) *
            (k / (σ.a : ℤ) ^ 2))) = _
    rw [Polynomial.eval₂_C, phasePolynomial_eval_one]
    simp
  · exact map_zero (phaseEvalMod p)

/-- The finite Cox product over the integral cyclotomic lift. -/
noncomputable def cyclotomicCoxPolynomial
    (p : ℕ+) : Polynomial (LaurentSeries (Polynomial ℤ)) :=
  ∏ σ : CoxMatrix p,
    (Polynomial.X - Polynomial.C (cyclotomicTransformedJSeries p σ))

theorem cyclotomicCoxPolynomial_map_complex (p : ℕ+) :
    (cyclotomicCoxPolynomial p).map
        (laurentSeriesMapRingHom (phaseEvalComplex p)) =
      formalCoxPolynomial p (zeta p) := by
  classical
  simp [cyclotomicCoxPolynomial, formalCoxPolynomial,
    Polynomial.map_prod, cyclotomicTransformedJSeries_map_complex]

theorem cyclotomicCoxPolynomial_map_mod
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    (cyclotomicCoxPolynomial p).map
        (laurentSeriesMapRingHom (phaseEvalMod p)) =
      formalCoxPolynomial p (1 : ZMod (p : ℕ)) := by
  classical
  simp [cyclotomicCoxPolynomial, formalCoxPolynomial,
    Polynomial.map_prod, cyclotomicTransformedJSeries_map_mod]

/-- Exercise 11.13: an integral value at `ζ_p` is congruent modulo `p` to the value at one. -/
theorem cyclotomicDescent_dvd
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (F : Polynomial ℤ) (z : ℤ)
    (hF : Polynomial.eval₂ (Int.castRingHom ℂ) (zeta p) F = (z : ℂ)) :
    (p : ℤ) ∣ F.eval 1 - z := by
  have hroot : Polynomial.aeval (zeta p)
      ((F - Polynomial.C z).map (Int.castRingHom ℚ)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcast : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) =
        Int.castRingHom ℂ := by
      ext n
      simp
    rw [hcast, Polynomial.eval₂_sub, Polynomial.eval₂_C, hF]
    simp
  have hdivRat : Polynomial.cyclotomic (p : ℕ) ℚ ∣
      (F - Polynomial.C z).map (Int.castRingHom ℚ) := by
    rw [Polynomial.cyclotomic_eq_minpoly_rat
      (zeta_isPrimitiveRoot p) (PNat.pos p)]
    exact minpoly.dvd ℚ (zeta p) hroot
  have hdiv : Polynomial.cyclotomic (p : ℕ) ℤ ∣ F - Polynomial.C z := by
    apply (Polynomial.map_dvd_map (Int.castRingHom ℚ) Int.cast_injective
      (Polynomial.cyclotomic.monic (p : ℕ) ℤ)).mp
    rw [Polynomial.map_cyclotomic]
    exact hdivRat
  have heval := Polynomial.eval_dvd (x := (1 : ℤ)) hdiv
  simpa only [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_sub,
    Polynomial.eval_C] using heval

/-- Exercise 11.13 in its coefficientwise reduction-modulo-`p` form. -/
theorem cyclotomicDescent_zmod
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (F : Polynomial ℤ) (z : ℤ)
    (hF : Polynomial.eval₂ (Int.castRingHom ℂ) (zeta p) F = (z : ℂ)) :
    ((F.eval 1 : ℤ) : ZMod (p : ℕ)) = (z : ZMod (p : ℕ)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  simpa only [neg_sub] using dvd_neg.mpr (cyclotomicDescent_dvd p F z hF)

/-- Coefficientwise Exercise 11.13 for polynomials whose coefficients are Laurent series. -/
theorem cyclotomicDescent_polynomialLaurentSeries
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (A : Polynomial (LaurentSeries (Polynomial ℤ)))
    (B : Polynomial (LaurentSeries ℤ))
    (h : A.map
        (laurentSeriesMapRingHom
          (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (zeta p))) =
      B.map (laurentSeriesMapRingHom (Int.castRingHom ℂ))) :
    A.map
        (laurentSeriesMapRingHom
          (Polynomial.eval₂RingHom
            (Int.castRingHom (ZMod (p : ℕ))) 1)) =
      B.map
        (laurentSeriesMapRingHom
          (Int.castRingHom (ZMod (p : ℕ)))) := by
  apply Polynomial.ext
  intro n
  ext k
  have hcoeff := congrArg
    (fun P : Polynomial (LaurentSeries ℂ) ↦ (P.coeff n).coeff k) h
  simp only [Polynomial.coeff_map, laurentSeriesMapRingHom_coeff] at hcoeff ⊢
  change Polynomial.eval₂ (Int.castRingHom (ZMod (p : ℕ))) 1
      ((A.coeff n).coeff k) =
    (Int.castRingHom (ZMod (p : ℕ))) ((B.coeff n).coeff k)
  rw [show (1 : ZMod (p : ℕ)) =
    (Int.castRingHom (ZMod (p : ℕ))) (1 : ℤ) by simp,
    Polynomial.eval₂_at_apply]
  exact cyclotomicDescent_zmod p ((A.coeff n).coeff k)
    ((B.coeff n).coeff k) hcoeff

/-- After reduction modulo `p`, the integral modular polynomial specializes to the phase-one
formal Cox product. -/
theorem specializeJMod_modularPolynomial_eq_formal
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    specializeJMod p
        (BivariatePolynomial.map (Int.castRingHom (ZMod (p : ℕ)))
          (modularPolynomial p)) =
      formalCoxPolynomial p (1 : ZMod (p : ℕ)) := by
  let A := cyclotomicCoxPolynomial p
  let B := specializeJIntegral p (modularPolynomial p)
  have hcomplex : A.map
        (laurentSeriesMapRingHom
          (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (zeta p))) =
      B.map (laurentSeriesMapRingHom (Int.castRingHom ℂ)) := by
    change (cyclotomicCoxPolynomial p).map
        (laurentSeriesMapRingHom (phaseEvalComplex p)) =
      (specializeJIntegral p (modularPolynomial p)).map
        (laurentSeriesMapRingHom (Int.castRingHom ℂ))
    rw [cyclotomicCoxPolynomial_map_complex,
      specializeJIntegral_modularPolynomial_map_complex]
  have hdescent := cyclotomicDescent_polynomialLaurentSeries p A B hcomplex
  calc
    specializeJMod p
        (BivariatePolynomial.map (Int.castRingHom (ZMod (p : ℕ)))
          (modularPolynomial p)) =
        B.map
          (laurentSeriesMapRingHom
            (Int.castRingHom (ZMod (p : ℕ)))) := by
      exact (specializeJIntegral_map_zmod p (modularPolynomial p)).symm
    _ = A.map
          (laurentSeriesMapRingHom
            (Polynomial.eval₂RingHom
              (Int.castRingHom (ZMod (p : ℕ))) 1)) := hdescent.symm
    _ = formalCoxPolynomial p (1 : ZMod (p : ℕ)) := by
      exact cyclotomicCoxPolynomial_map_mod p

end Cox
