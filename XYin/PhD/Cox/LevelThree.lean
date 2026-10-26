/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum.BigOperators

import XYin.PhD.Cox.KroneckerFrobenius
import XYin.PhD.Cox.SymmetricCubicLaurent
import XYin.PhD.qExpansion_tactic.link

/-!
# The level-three modular polynomial

This file proves Cox's explicit formula for the level-three modular polynomial from a
complex-variable symmetry hypothesis. The numerical part is certified by kernel reduction of a
finite jet of the integral `q`-expansion of `j`; no native-code proof oracle is used.
-/

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

namespace Cox

open QExpansionTactic
open UpperHalfPlane

/-- Cox's explicit level-three modular polynomial (equation (11.22)), written in the letters of
`ℤ[X][Y]`: Cox's root variable `X` is the outer variable `Y` and Cox's parameter `Y` is the inner
variable `C X` (see `Cox.modularPolynomialC`). -/
def modularPolynomialThreeExplicit : ℤ[X][Y] :=
  Y * (Y + 2 ^ 15 * 3 * 5 ^ 3) ^ 3 +
  C X * (C X + 2 ^ 15 * 3 * 5 ^ 3) ^ 3 -
  Y ^ 3 * C X ^ 3 +
  2 ^ 3 * 3 ^ 2 * 31 * Y ^ 2 * C X ^ 2 * (Y + C X) -
  2 ^ 2 * 3 ^ 3 * 9907 * Y * C X * (Y ^ 2 + C X ^ 2) +
  2 * 3 ^ 4 * 13 * 193 * 6367 * Y ^ 2 * C X ^ 2 +
  2 ^ 16 * 3 ^ 5 * 5 ^ 3 * 17 * 263 * Y * C X * (Y + C X) -
  2 ^ 31 * 5 ^ 6 * 22973 * Y * C X

private def qjCoeffTableThree (n : ℕ) : ℤ :=
  [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600,
    4252023300096, 44656994071935, 401490886656000, 3176440229784420,
    22567393309593600, 146211911499519294].getD n 0

private theorem qjCoeffInt_eq_tableThree (n : Fin 13) :
    qjCoeffInt n = qjCoeffTableThree n := by
  fin_cases n <;> decide +kernel

private def explicitCoeffThree (i : Fin 5) (d : ℕ) : ℤ :=
  match (i : ℕ) with
  | 0 => [0, 1855425871872000000000, 452984832000000, 36864000, 1].getD d 0
  | 1 => [1855425871872000000000, -770845966336000000,
      8900222976000, -1069956, 0].getD d 0
  | 2 => [452984832000000, 8900222976000, 2587918086, 2232, 0].getD d 0
  | 3 => [36864000, -1069956, 2232, -1, 0].getD d 0
  | 4 => [1, 0, 0, 0, 0].getD d 0
  | _ => 0

private def modularPolynomialThreeTable : ℤ[X][Y] :=
  ∑ i : Fin 5, ∑ d : Fin 5, (explicitCoeffThree i d : ℤ[X][Y]) * Y ^ (i : ℕ) * C X ^ (d : ℕ)

private theorem modularPolynomialThreeExplicit_eq_table :
    modularPolynomialThreeExplicit = modularPolynomialThreeTable := by
  simp only [modularPolynomialThreeTable, modularPolynomialThreeExplicit,
    explicitCoeffThree, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.getD_cons_zero,
    List.getD_cons_succ, List.getD_nil]
  ring_nf

private theorem modularPolynomialThreeExplicit_monic :
    modularPolynomialThreeExplicit.Monic := by
  unfold modularPolynomialThreeExplicit
  ring_nf
  monicity!

private theorem modularPolynomialThreeExplicit_natDegree :
    modularPolynomialThreeExplicit.natDegree = 4 := by
  unfold modularPolynomialThreeExplicit
  ring_nf
  compute_degree!

private theorem modularPolynomialThreeExplicit_swap :
    Bivariate.swap modularPolynomialThreeExplicit = modularPolynomialThreeExplicit := by
  simp only [modularPolynomialThreeExplicit, map_add, map_sub, map_mul, map_pow, map_ofNat,
    Bivariate.swap_Y, Bivariate.swap_X]
  ring

private def jetMul (F G : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), F i * G (n - i)

private def jetPow (F : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0 => fun n ↦ if n = 0 then 1 else 0
  | d + 1 => jetMul (jetPow F d) F

private def jetShift (k : ℕ) (F : ℕ → ℤ) (n : ℕ) : ℤ :=
  if k ≤ n then F (n - k) else 0

private def jetExpand (k : ℕ) (F : ℕ → ℤ) (n : ℕ) : ℤ :=
  if k ∣ n then F (n / k) else 0

private def sigmaJetThree : ℕ → ℤ := jetExpand 9 qjCoeffTableThree

private def widthJetThree : ℕ → ℤ := jetExpand 3 qjCoeffTableThree

/-- The coefficient of `q^n` in `q³⁶ · Φ(j(9τ), j(3τ))` (Cox's notation, i.e.
`Φ.evalEval (j(3τ)) (j(9τ))`) for the explicit candidate `Φ`, computed from finite jets of the
`q`-expansion of `j`. -/
private def explicitCandidateClearedJetThree (n : ℕ) : ℤ :=
  ∑ i : Fin 5, ∑ d : Fin 5, explicitCoeffThree i d *
    jetShift (36 - (9 * (i : ℕ) + 3 * (d : ℕ)))
      (jetMul (jetPow sigmaJetThree i) (jetPow widthJetThree d)) n

/-- The numerical certificate, checked by kernel reduction: the ten triangular coefficients
of `q³⁶ · Φ(j(9τ), j(3τ))` vanish. -/
private theorem explicitCandidateClearedJetThree_triangular :
    ∀ i ≤ 3, ∀ j ≤ i, explicitCandidateClearedJetThree (36 - (9 * i + 3 * j)) = 0 := by
  decide +kernel

private def sigmaPowerSeriesThree : PowerSeries ℤ :=
  (jUnitPowerSeries ℤ).expand 9 (by norm_num)

private def widthPowerSeriesThree : PowerSeries ℤ :=
  (jUnitPowerSeries ℤ).expand 3 (by norm_num)

private theorem jLaurentSeriesWidth_nine :
    jLaurentSeriesWidth ℤ 9 =
      HahnSeries.single (-9 : ℤ) 1 * (sigmaPowerSeriesThree : LaurentSeries ℤ) :=
  jLaurentSeriesWidth_eq_single_mul_expand ℤ 9

private theorem jLaurentSeriesWidth_three :
    jLaurentSeriesWidth ℤ 3 =
      HahnSeries.single (-3 : ℤ) 1 * (widthPowerSeriesThree : LaurentSeries ℤ) :=
  jLaurentSeriesWidth_eq_single_mul_expand ℤ 3

private theorem shiftedPowerSeries_pow (a : ℤ) (F : PowerSeries ℤ) (n : ℕ) :
    (HahnSeries.single a 1 * (F : LaurentSeries ℤ)) ^ n =
      HahnSeries.single (n • a) 1 * ((F ^ n : PowerSeries ℤ) : LaurentSeries ℤ) := by
  rw [mul_pow, HahnSeries.single_pow, one_pow, PowerSeries.coe_pow]

private theorem shiftedPowerSeries_mul (a b : ℤ) (r s : ℤ)
    (F G : PowerSeries ℤ) :
    (HahnSeries.single a r * (F : LaurentSeries ℤ)) *
        (HahnSeries.single b s * (G : LaurentSeries ℤ)) =
      HahnSeries.single (a + b) (r * s) *
        ((F * G : PowerSeries ℤ) : LaurentSeries ℤ) := by
  rw [mul_mul_mul_comm, HahnSeries.single_mul_single, PowerSeries.coe_mul]

private theorem clearTwoShiftedPowerSeries (c a b : ℤ)
    (F G : PowerSeries ℤ) :
    HahnSeries.single (36 : ℤ) 1 *
        (HahnSeries.C c * (HahnSeries.single a 1 * (F : LaurentSeries ℤ)) *
          (HahnSeries.single b 1 * (G : LaurentSeries ℤ))) =
      HahnSeries.single (36 + a + b) c *
        ((F * G : PowerSeries ℤ) : LaurentSeries ℤ) := by
  rw [HahnSeries.C_apply, ← mul_assoc (HahnSeries.single 0 c), HahnSeries.single_mul_single,
    shiftedPowerSeries_mul, ← mul_assoc, HahnSeries.single_mul_single]
  simp only [zero_add, one_mul, mul_one, add_assoc]

private theorem explicitCandidateClearedLaurentTermThree (i d : Fin 5) :
    HahnSeries.single (36 : ℤ) 1 *
        (HahnSeries.C (explicitCoeffThree i d) *
          jLaurentSeriesWidth ℤ 9 ^ (i : ℕ) *
          jLaurentSeriesWidth ℤ 3 ^ (d : ℕ)) =
      ((PowerSeries.C (explicitCoeffThree i d) *
          PowerSeries.X ^ (36 - (9 * (i : ℕ) + 3 * (d : ℕ))) *
          (sigmaPowerSeriesThree ^ (i : ℕ) *
            widthPowerSeriesThree ^ (d : ℕ)) : PowerSeries ℤ) : LaurentSeries ℤ) := by
  rw [jLaurentSeriesWidth_nine, jLaurentSeriesWidth_three, shiftedPowerSeries_pow,
    shiftedPowerSeries_pow, clearTwoShiftedPowerSeries]
  simp only [map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow,
    HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  congr 1
  fin_cases i <;> fin_cases d <;> norm_num [explicitCoeffThree]

private theorem expand_jUnitPowerSeries_coeff_eq_jet (r : ℕ) (hr : r ≠ 0) (n : ℕ)
    (hn : n < 13 * r) :
    PowerSeries.coeff n ((jUnitPowerSeries ℤ).expand r hr) =
      jetExpand r qjCoeffTableThree n := by
  rw [PowerSeries.coeff_expand, jetExpand]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hr), coeff_jUnitPowerSeries,
      jIntCoeff_sub_one, qjCoeffs_eq_qjCoeffInt]
    exact qjCoeffInt_eq_tableThree ⟨q, by nlinarith⟩
  · rfl

private theorem powerSeries_coeff_mul_eq_jetMul
    (F G : PowerSeries ℤ) (f g : ℕ → ℤ)
    (hF : ∀ n, n < 37 → PowerSeries.coeff n F = f n)
    (hG : ∀ n, n < 37 → PowerSeries.coeff n G = g n)
    (n : ℕ) (hn : n < 37) :
    PowerSeries.coeff n (F * G) = jetMul f g n := by
  rw [PowerSeries.coeff_mul]
  unfold jetMul
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ PowerSeries.coeff i F * PowerSeries.coeff j G) n]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [hF i (by lia), hG (n - i) (by lia)]

private theorem powerSeries_coeff_pow_eq_jetPow
    (F : PowerSeries ℤ) (f : ℕ → ℤ)
    (hF : ∀ n, n < 37 → PowerSeries.coeff n F = f n)
    (d n : ℕ) (hn : n < 37) :
    PowerSeries.coeff n (F ^ d) = jetPow f d n := by
  induction d generalizing n with
  | zero => simp [jetPow, PowerSeries.coeff_one]
  | succ d ih =>
      rw [pow_succ]
      apply powerSeries_coeff_mul_eq_jetMul _ _ _ _ (fun m hm ↦ ih m hm) hF n hn

private theorem powerSeries_coeff_shift_eq_jetShift
    (F : PowerSeries ℤ) (f : ℕ → ℤ)
    (hF : ∀ n, n < 37 → PowerSeries.coeff n F = f n)
    (k n : ℕ) (hn : n < 37) :
    PowerSeries.coeff n (PowerSeries.X ^ k * F) = jetShift k f n := by
  rw [PowerSeries.coeff_X_pow_mul', jetShift]
  split_ifs with h
  · rw [hF (n - k) (by lia)]
  · rfl

private def explicitCandidateClearedPowerSeriesThree : PowerSeries ℤ :=
  ∑ i : Fin 5, ∑ d : Fin 5,
    PowerSeries.C (explicitCoeffThree i d) *
      (PowerSeries.X ^ (36 - (9 * (i : ℕ) + 3 * (d : ℕ))) *
        (sigmaPowerSeriesThree ^ (i : ℕ) * widthPowerSeriesThree ^ (d : ℕ)))

private theorem explicitCandidateClearedPowerSeriesThree_coeff_eq_jet
    (n : ℕ) (hn : n < 37) :
    PowerSeries.coeff n explicitCandidateClearedPowerSeriesThree =
      explicitCandidateClearedJetThree n := by
  simp only [explicitCandidateClearedPowerSeriesThree, explicitCandidateClearedJetThree,
    map_sum, PowerSeries.coeff_C_mul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
  congr 1
  refine powerSeries_coeff_shift_eq_jetShift _ _ (fun m hm ↦ ?_) _ _ hn
  refine powerSeries_coeff_mul_eq_jetMul _ _ _ _ (fun r hr ↦ ?_) (fun r hr ↦ ?_) m hm
  · exact powerSeries_coeff_pow_eq_jetPow _ _
      (fun r hr ↦ expand_jUnitPowerSeries_coeff_eq_jet 9 _ r (by lia)) i r hr
  · exact powerSeries_coeff_pow_eq_jetPow _ _
      (fun r hr ↦ expand_jUnitPowerSeries_coeff_eq_jet 3 _ r (by lia)) d r hr

/-- The explicit candidate evaluated at the integral Laurent series of `j(9τ)` and `j(3τ)`. -/
private def explicitCandidateLaurentEvalThree : LaurentSeries ℤ :=
  bivariateLaurentEvalHom (jLaurentSeriesWidth ℤ 9) (jLaurentSeriesWidth ℤ 3)
    modularPolynomialThreeExplicit

private theorem explicitCandidateClearedLaurentEvalThree :
    HahnSeries.single (36 : ℤ) 1 * explicitCandidateLaurentEvalThree =
      (explicitCandidateClearedPowerSeriesThree : LaurentSeries ℤ) := by
  rw [explicitCandidateLaurentEvalThree, modularPolynomialThreeExplicit_eq_table]
  simp only [modularPolynomialThreeTable, explicitCandidateClearedPowerSeriesThree, map_sum,
    map_mul, map_pow, map_intCast, bivariateLaurentEvalHom_X, bivariateLaurentEvalHom_C_X,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
  simpa only [eq_intCast (HahnSeries.C : ℤ →+* LaurentSeries ℤ), mul_assoc, map_mul,
    map_pow] using explicitCandidateClearedLaurentTermThree i d

private theorem explicitCandidateLaurentEvalThree_coeff_eq_jet
    (n : ℕ) (hn : n < 37) :
    explicitCandidateLaurentEvalThree.coeff ((n : ℤ) - 36) =
      explicitCandidateClearedJetThree n := by
  have h := congrArg (fun F : LaurentSeries ℤ ↦ F.coeff (n : ℤ))
    explicitCandidateClearedLaurentEvalThree
  simp only [HahnSeries.coeff_single_mul, one_mul, LaurentSeries.coeff_coe_powerSeries,
    explicitCandidateClearedPowerSeriesThree_coeff_eq_jet n hn] at h
  exact h

/-- The ten triangular Laurent coefficients of the explicit candidate vanish. -/
private theorem explicitCandidateLaurentEvalThree_coeff_triangular {i j : ℕ} (hji : j ≤ i)
    (hi : i ≤ 3) : explicitCandidateLaurentEvalThree.coeff (-(9 * (i : ℤ) + 3 * j)) = 0 := by
  have h := explicitCandidateLaurentEvalThree_coeff_eq_jet (36 - (9 * i + 3 * j)) (by lia)
  rw [show ((36 - (9 * i + 3 * j) : ℕ) : ℤ) - 36 = -(9 * (i : ℤ) + 3 * j) by lia] at h
  rw [h, explicitCandidateClearedJetThree_triangular i hi j hji]

private def modularPolynomialThreeComplexExplicit : ℂ[X][Y] :=
  modularPolynomialThreeExplicit.map (mapRingHom (Int.castRingHom ℂ))

private def modularPolynomialThreeDifference : ℂ[X][Y] :=
  modularPolynomialC (3 : ℕ+) - modularPolynomialThreeComplexExplicit

private theorem modularPolynomialThreeComplexExplicit_monic :
    modularPolynomialThreeComplexExplicit.Monic :=
  modularPolynomialThreeExplicit_monic.map (mapRingHom (Int.castRingHom ℂ))

private theorem modularPolynomialThreeComplexExplicit_natDegree :
    modularPolynomialThreeComplexExplicit.natDegree = 4 :=
  (modularPolynomialThreeExplicit_monic.natDegree_map
    (mapRingHom (Int.castRingHom ℂ))).trans modularPolynomialThreeExplicit_natDegree

private theorem modularPolynomialThreeDifference_swap
    (hsymm : Bivariate.swap (modularPolynomialC (3 : ℕ+)) = modularPolynomialC (3 : ℕ+)) :
    Bivariate.swap modularPolynomialThreeDifference = modularPolynomialThreeDifference := by
  rw [modularPolynomialThreeDifference, map_sub, hsymm, modularPolynomialThreeComplexExplicit,
    ← Bivariate.map_mapRingHom_swap, modularPolynomialThreeExplicit_swap]

private theorem modularPolynomialThreeDifference_natDegree_le :
    modularPolynomialThreeDifference.natDegree ≤ 3 := by
  rw [← Nat.lt_succ_iff]
  apply Polynomial.IsMonicOfDegree.natDegree_sub_lt (by norm_num)
  · refine ⟨?_, modularPolynomialC_monic (3 : ℕ+)⟩
    rw [modularPolynomialC_natDegree, card_coxMatrix_of_prime (p := 3) Nat.prime_three]
    rfl
  · exact ⟨modularPolynomialThreeComplexExplicit_natDegree,
      modularPolynomialThreeComplexExplicit_monic⟩

private theorem modularPolynomialThreeDifference_inner_natDegree_le
    (hsymm : Bivariate.swap (modularPolynomialC (3 : ℕ+)) =
      modularPolynomialC (3 : ℕ+)) (i : ℕ) :
    (modularPolynomialThreeDifference.coeff i).natDegree ≤ 3 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun n hn ↦ ?_
  rw [← Bivariate.coeff_coeff_swap, modularPolynomialThreeDifference_swap hsymm,
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (modularPolynomialThreeDifference_natDegree_le.trans_lt hn), Polynomial.coeff_zero]

private theorem modularPolynomialThreeDifference_eq_zero
    (hsymm : Bivariate.swap (modularPolynomialC (3 : ℕ+)) =
      modularPolynomialC (3 : ℕ+)) :
    modularPolynomialThreeDifference = 0 := by
  have hζ := zeta_ne_zero 3
  have hT : HahnSeries.mapRingHom (Int.castRingHom ℂ) (jLaurentSeriesWidth ℤ 9) =
      transformedJSeries (zeta 3) (sigmaZero 3) := by
    rw [transformedJSeries_eq_jLaurentSeriesWidth _ _ (by simp [sigmaZero])]
    exact jLaurentSeriesWidth_map _ 9
  have hJ : HahnSeries.mapRingHom (Int.castRingHom ℂ) (jLaurentSeriesWidth ℤ 3) =
      laurentqExpansion 3 j := by
    simpa using jLaurentSeriesWidth_map_complex 3
  have hroot : bivariateLaurentEvalHom (transformedJSeries (zeta 3) (sigmaZero 3))
      (laurentqExpansion 3 j) (modularPolynomialC 3) = 0 := by
    have hformal := formalCoxPolynomial_eq_modularPolynomialC_map_j 3
    norm_num at hformal
    rw [bivariateLaurentEvalHom_apply, Polynomial.eval₂_eq_eval_map, ← hformal,
      formalCoxPolynomial_eval_transformedJSeries]
  refine symmetric_bidegree_three_eq_zero_of_laurent_coeff
    (transformedJSeries (zeta 3) (sigmaZero 3)) (laurentqExpansion 3 j)
    (by simpa [sigmaZero] using transformedJSeries_order _ hζ (sigmaZero 3))
    (by simpa using laurentqExpansion_j_order_widthM 3)
    (by simpa [sigmaZero] using transformedJSeries_leadingCoeff _ hζ (sigmaZero 3))
    (by simpa using laurentqExpansion_j_leadingCoeff_widthM 3)
    _ modularPolynomialThreeDifference_natDegree_le
    (modularPolynomialThreeDifference_inner_natDegree_le hsymm)
    (modularPolynomialThreeDifference_swap hsymm) fun i j hji hi ↦ ?_
  rw [modularPolynomialThreeDifference, map_sub, hroot, zero_sub, HahnSeries.coeff_neg,
    neg_eq_zero, modularPolynomialThreeComplexExplicit, ← bivariateLaurentEvalHom_map _ hT hJ,
    HahnSeries.mapRingHom_coeff]
  exact (congrArg _ (explicitCandidateLaurentEvalThree_coeff_triangular hji hi)).trans
    (map_zero _)

private theorem modularPolynomialC_three_eq_explicit
    (hsymm : Bivariate.swap (modularPolynomialC (3 : ℕ+)) =
      modularPolynomialC (3 : ℕ+)) :
    modularPolynomialC (3 : ℕ+) = modularPolynomialThreeComplexExplicit := by
  rw [← sub_eq_zero]
  exact modularPolynomialThreeDifference_eq_zero hsymm

/-- Symmetry of the complex level-three modular polynomial implies Cox's explicit formula. -/
theorem modularPolynomial_three_of_complex_swap
    (hsymm : Bivariate.swap (modularPolynomialC (3 : ℕ+)) =
      modularPolynomialC (3 : ℕ+)) :
    modularPolynomial (3 : ℕ+) = modularPolynomialThreeExplicit := by
  have hmap : (modularPolynomial (3 : ℕ+)).map (mapRingHom (Int.castRingHom ℂ)) =
      modularPolynomialThreeExplicit.map (mapRingHom (Int.castRingHom ℂ)) := by
    rw [modularPolynomial_map_complex]
    exact modularPolynomialC_three_eq_explicit hsymm
  exact map_injective _ (map_injective _ Int.cast_injective) hmap

end Cox
