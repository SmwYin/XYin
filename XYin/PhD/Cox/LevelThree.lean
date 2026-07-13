/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.ComputeDegree

import XYin.PhD.Cox.KroneckerFrobenius
import XYin.PhD.Cox.SymmetricCubicLaurent
import XYin.PhD.qExpansion_tactic.link

/-!
# The level-three modular polynomial

This file proves Cox's explicit formula for the level-three modular polynomial from a
complex-variable symmetry hypothesis. The numerical part is certified by kernel reduction of a
finite jet of the integral `q`-expansion of `j`; no native-code proof oracle is used.
-/

noncomputable section

namespace Cox

open XYin.PhD.qExpansion_tactic
open UpperHalfPlane

/-- Cox's explicit level-three modular polynomial (equation (11.22)). -/
def modularPolynomialThreeExplicit : BivariatePolynomial ℤ :=
  let X : BivariatePolynomial ℤ := BivariatePolynomial.varX
  let Y : BivariatePolynomial ℤ := BivariatePolynomial.varY
  X * (X + 2 ^ 15 * 3 * 5 ^ 3) ^ 3 +
  Y * (Y + 2 ^ 15 * 3 * 5 ^ 3) ^ 3 -
  X ^ 3 * Y ^ 3 +
  2 ^ 3 * 3 ^ 2 * 31 * X ^ 2 * Y ^ 2 * (X + Y) -
  2 ^ 2 * 3 ^ 3 * 9907 * X * Y * (X ^ 2 + Y ^ 2) +
  2 * 3 ^ 4 * 13 * 193 * 6367 * X ^ 2 * Y ^ 2 +
  2 ^ 16 * 3 ^ 5 * 5 ^ 3 * 17 * 263 * X * Y * (X + Y) -
  2 ^ 31 * 5 ^ 6 * 22973 * X * Y

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

private def modularPolynomialThreeTable : BivariatePolynomial ℤ :=
  ∑ i : Fin 5, ∑ d : Fin 5,
    (explicitCoeffThree i d : BivariatePolynomial ℤ) *
      BivariatePolynomial.varX ^ (i : ℕ) * BivariatePolynomial.varY ^ (d : ℕ)

private theorem modularPolynomialThreeExplicit_eq_table :
    modularPolynomialThreeExplicit = modularPolynomialThreeTable := by
  simp only [modularPolynomialThreeTable, modularPolynomialThreeExplicit,
    explicitCoeffThree, BivariatePolynomial.varX, BivariatePolynomial.varY,
    Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, List.getD_cons_zero,
    List.getD_cons_succ, List.getD_nil]
  ring_nf

private theorem modularPolynomialThreeExplicit_monic :
    modularPolynomialThreeExplicit.Monic := by
  unfold modularPolynomialThreeExplicit BivariatePolynomial.varX BivariatePolynomial.varY
  ring_nf
  monicity!

private theorem modularPolynomialThreeExplicit_natDegree :
    modularPolynomialThreeExplicit.natDegree = 4 := by
  unfold modularPolynomialThreeExplicit BivariatePolynomial.varX BivariatePolynomial.varY
  ring_nf
  compute_degree!

private theorem modularPolynomialThreeExplicit_swap :
    Polynomial.Bivariate.swap modularPolynomialThreeExplicit =
      modularPolynomialThreeExplicit := by
  simp only [modularPolynomialThreeExplicit, BivariatePolynomial.varX,
    BivariatePolynomial.varY, map_add, map_sub, map_mul, map_pow, map_ofNat,
    Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_X]
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

private def explicitCandidateClearedJetTermThree (i d : Fin 5) (n : ℕ) : ℤ :=
  explicitCoeffThree i d *
    jetShift (36 - (9 * (i : ℕ) + 3 * (d : ℕ)))
      (jetMul (jetPow sigmaJetThree i) (jetPow widthJetThree d)) n

private def explicitCandidateClearedJetRowThree (i : Fin 5) (n : ℕ) : ℤ :=
  ∑ d : Fin 5, explicitCandidateClearedJetTermThree i d n

private def explicitCandidateClearedJetThree (n : ℕ) : ℤ :=
  ∑ i : Fin 5, explicitCandidateClearedJetRowThree i n

private theorem jIntCoeff_eq_qjCoeffInt_three (n : ℕ) :
    jIntCoeff ((n : ℤ) - 1) = qjCoeffInt n := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ ↦ (z : ℂ)))
  rw [← jIntCoeff_spec]
  have hlower : -(poleOrder 1 j : ℤ) ≤ (n : ℤ) - 1 := by
    rw [j_poleOrder]
    lia
  rw [laurentqExpansion.coeff_of_geq hlower, j_poleOrder]
  simpa [j_to_qExpansion, qj_qexpansion] using qj_qxp_coeff_link n

private def qjIntegralPowerSeriesThree : PowerSeries ℤ :=
  PowerSeries.mk fun n ↦ jIntCoeff ((n : ℤ) - 1)

private def sigmaPowerSeriesThree : PowerSeries ℤ :=
  qjIntegralPowerSeriesThree.expand 9 (by norm_num)

private def widthPowerSeriesThree : PowerSeries ℤ :=
  qjIntegralPowerSeriesThree.expand 3 (by norm_num)

private def sigmaLaurentSeriesThree : LaurentSeries ℤ :=
  HahnSeries.single (-9 : ℤ) 1 * (sigmaPowerSeriesThree : LaurentSeries ℤ)

private def widthLaurentSeriesThree : LaurentSeries ℤ :=
  HahnSeries.single (-3 : ℤ) 1 * (widthPowerSeriesThree : LaurentSeries ℤ)

private theorem shiftedPowerSeries_pow (a : ℤ) (F : PowerSeries ℤ) (n : ℕ) :
    (HahnSeries.single a 1 * (F : LaurentSeries ℤ)) ^ n =
      HahnSeries.single (n • a) 1 * ((F ^ n : PowerSeries ℤ) : LaurentSeries ℤ) := by
  rw [mul_pow, HahnSeries.single_pow]
  simp only [one_pow]
  rw [map_pow]

private theorem shiftedPowerSeries_mul (a b : ℤ) (r s : ℤ)
    (F G : PowerSeries ℤ) :
    (HahnSeries.single a r * (F : LaurentSeries ℤ)) *
        (HahnSeries.single b s * (G : LaurentSeries ℤ)) =
      HahnSeries.single (a + b) (r * s) *
        ((F * G : PowerSeries ℤ) : LaurentSeries ℤ) := by
  calc
    _ = (HahnSeries.single a r * HahnSeries.single b s) *
        ((F : LaurentSeries ℤ) * (G : LaurentSeries ℤ)) := by ac_rfl
    _ = _ := by
      rw [HahnSeries.single_mul_single]
      exact congrArg (HahnSeries.single (a + b) (r * s) * ·)
        ((HahnSeries.ofPowerSeries ℤ ℤ).map_mul F G).symm

private theorem clearTwoShiftedPowerSeries (c a b : ℤ)
    (F G : PowerSeries ℤ) :
    HahnSeries.single (36 : ℤ) 1 *
        (HahnSeries.C c * (HahnSeries.single a 1 * (F : LaurentSeries ℤ)) *
          (HahnSeries.single b 1 * (G : LaurentSeries ℤ))) =
      HahnSeries.single (36 + a + b) c *
        ((F * G : PowerSeries ℤ) : LaurentSeries ℤ) := by
  calc
    _ = HahnSeries.single (36 : ℤ) 1 *
        ((HahnSeries.single 0 c * ((1 : PowerSeries ℤ) : LaurentSeries ℤ)) *
          (HahnSeries.single a 1 * (F : LaurentSeries ℤ)) *
          (HahnSeries.single b 1 * (G : LaurentSeries ℤ))) := by
      simp
    _ = HahnSeries.single (36 : ℤ) 1 *
        ((HahnSeries.single a c * (F : LaurentSeries ℤ)) *
          (HahnSeries.single b 1 * (G : LaurentSeries ℤ))) := by
      rw [shiftedPowerSeries_mul 0 a c 1]
      simp
    _ = HahnSeries.single (36 : ℤ) 1 *
        (HahnSeries.single (a + b) c *
          ((F * G : PowerSeries ℤ) : LaurentSeries ℤ)) := by
      rw [shiftedPowerSeries_mul a b c 1]
      simp
    _ = _ := by
      rw [← mul_assoc, HahnSeries.single_mul_single, one_mul, ← add_assoc]

private theorem C_mul_single_one (c k : ℤ) :
    HahnSeries.C c * (HahnSeries.single k 1 : LaurentSeries ℤ) =
      HahnSeries.single k c := by
  rw [HahnSeries.C_apply, HahnSeries.single_mul_single]
  simp

private theorem explicitCandidateClearedLaurentTermThree (i d : Fin 5) :
    HahnSeries.single (36 : ℤ) 1 *
        (HahnSeries.C (explicitCoeffThree i d) *
          sigmaLaurentSeriesThree ^ (i : ℕ) *
          widthLaurentSeriesThree ^ (d : ℕ)) =
      ((PowerSeries.C (explicitCoeffThree i d) *
          PowerSeries.X ^ (36 - (9 * (i : ℕ) + 3 * (d : ℕ))) *
          (sigmaPowerSeriesThree ^ (i : ℕ) *
            widthPowerSeriesThree ^ (d : ℕ)) : PowerSeries ℤ) : LaurentSeries ℤ) := by
  rw [sigmaLaurentSeriesThree, widthLaurentSeriesThree,
    shiftedPowerSeries_pow, shiftedPowerSeries_pow]
  rw [(HahnSeries.ofPowerSeries ℤ ℤ).map_mul,
    (HahnSeries.ofPowerSeries ℤ ℤ).map_mul,
    HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow,
    C_mul_single_one]
  fin_cases i <;> fin_cases d <;>
    simp only [explicitCoeffThree, List.getD_cons_zero, List.getD_cons_succ,
      nsmul_eq_mul, Nat.cast_ofNat, mul_neg, mul_one] <;>
    rw [clearTwoShiftedPowerSeries] <;> norm_num

private theorem qjIntegralPowerSeriesThree_coeff_eq_table
    (n : ℕ) (hn : n < 13) :
    PowerSeries.coeff n qjIntegralPowerSeriesThree = qjCoeffTableThree n := by
  rw [qjIntegralPowerSeriesThree, PowerSeries.coeff_mk,
    jIntCoeff_eq_qjCoeffInt_three]
  exact qjCoeffInt_eq_tableThree ⟨n, hn⟩

private theorem sigmaPowerSeriesThree_coeff_eq_jet
    (n : ℕ) (hn : n < 37) :
    PowerSeries.coeff n sigmaPowerSeriesThree = sigmaJetThree n := by
  rw [sigmaPowerSeriesThree, PowerSeries.coeff_expand, sigmaJetThree, jetExpand]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [Nat.mul_comm 9 q, Nat.mul_div_left q (by norm_num)]
    apply qjIntegralPowerSeriesThree_coeff_eq_table
    lia
  · rfl

private theorem widthPowerSeriesThree_coeff_eq_jet
    (n : ℕ) (hn : n < 37) :
    PowerSeries.coeff n widthPowerSeriesThree = widthJetThree n := by
  rw [widthPowerSeriesThree, PowerSeries.coeff_expand, widthJetThree, jetExpand]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [Nat.mul_comm 3 q, Nat.mul_div_left q (by norm_num)]
    apply qjIntegralPowerSeriesThree_coeff_eq_table
    lia
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
  simp only [explicitCandidateClearedPowerSeriesThree,
    explicitCandidateClearedJetThree, explicitCandidateClearedJetRowThree,
    explicitCandidateClearedJetTermThree, map_sum, PowerSeries.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  apply powerSeries_coeff_shift_eq_jetShift _ _ _ _ _ hn
  intro m hm
  apply powerSeries_coeff_mul_eq_jetMul _ _ _ _ _ _ m hm
  · exact fun r hr ↦ powerSeries_coeff_pow_eq_jetPow _ _
      sigmaPowerSeriesThree_coeff_eq_jet i r hr
  · exact fun r hr ↦ powerSeries_coeff_pow_eq_jetPow _ _
      widthPowerSeriesThree_coeff_eq_jet d r hr

@[simp]
private theorem bivariateLaurentEval_intCastThree (z : ℤ) :
    Polynomial.eval₂
        (Polynomial.eval₂RingHom (HahnSeries.C : ℤ →+* LaurentSeries ℤ)
          widthLaurentSeriesThree)
        sigmaLaurentSeriesThree (z : BivariatePolynomial ℤ) = HahnSeries.C z := by
  rw [← Polynomial.C_eq_intCast z, Polynomial.eval₂_C,
    ← Polynomial.C_eq_intCast z, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C]
  simp

private def explicitCandidateLaurentEvalThree : LaurentSeries ℤ :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (HahnSeries.C : ℤ →+* LaurentSeries ℤ)
      widthLaurentSeriesThree)
    sigmaLaurentSeriesThree modularPolynomialThreeExplicit

private theorem explicitCandidateClearedLaurentEvalThree :
    HahnSeries.single (36 : ℤ) 1 *
        explicitCandidateLaurentEvalThree =
      (explicitCandidateClearedPowerSeriesThree : LaurentSeries ℤ) := by
  rw [explicitCandidateLaurentEvalThree]
  rw [modularPolynomialThreeExplicit_eq_table]
  simp only [modularPolynomialThreeTable,
    explicitCandidateClearedPowerSeriesThree, map_sum, map_mul, map_pow,
    BivariatePolynomial.varX, BivariatePolynomial.varY,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_C,
    HahnSeries.ofPowerSeries_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  simpa only [bivariateLaurentEval_intCastThree, mul_assoc, map_mul, map_pow,
    HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow] using
    explicitCandidateClearedLaurentTermThree i d

private theorem explicitCandidateClearedJetThree_zero :
    explicitCandidateClearedJetThree 0 = 0 := by decide +kernel

private theorem explicitCandidateClearedJetThree_three :
    explicitCandidateClearedJetThree 3 = 0 := by decide +kernel

private theorem explicitCandidateClearedJetThree_six :
    explicitCandidateClearedJetThree 6 = 0 := by decide +kernel

private theorem explicitCandidateClearedJetThree_nine :
    explicitCandidateClearedJetThree 9 = 0 := by decide +kernel

private theorem explicitCandidateClearedJetThree_twelve :
    explicitCandidateClearedJetThree 12 = 0 := by decide +kernel

private theorem explicitCandidateClearedJetRowThree_fifteen (i : Fin 5) :
    explicitCandidateClearedJetRowThree i 15 =
      [0, 0, 12756069900288, -12756069900288, 0].getD i 0 := by
  fin_cases i <;> decide +kernel

private theorem explicitCandidateClearedJetThree_fifteen :
    explicitCandidateClearedJetThree 15 = 0 := by
  simp [explicitCandidateClearedJetThree,
    explicitCandidateClearedJetRowThree_fifteen, Fin.sum_univ_succ]

private theorem explicitCandidateClearedJetRowThree_eighteen_zero :
    explicitCandidateClearedJetRowThree 0 18 = 0 := by decide +kernel

private theorem explicitCandidateClearedJetRowThree_eighteen_one :
    explicitCandidateClearedJetRowThree 1 18 = -1069956 := by decide +kernel

private theorem explicitCandidateClearedJetTermThree_eighteen_two_zero :
    explicitCandidateClearedJetTermThree 2 0 18 = 452984832000000 := by decide +kernel

private theorem explicitCandidateClearedJetTermThree_eighteen_two_one :
    explicitCandidateClearedJetTermThree 2 1 18 = 6621765894144000 := by decide +kernel

private theorem explicitCandidateClearedJetTermThree_eighteen_two_two :
    explicitCandidateClearedJetTermThree 2 2 18 = 2451545154540144 := by decide +kernel

private theorem explicitCandidateClearedJetTermThree_eighteen_two_three :
    explicitCandidateClearedJetTermThree 2 3 18 = 3024814720896 := by decide +kernel

private theorem explicitCandidateClearedJetTermThree_eighteen_two_four :
    explicitCandidateClearedJetTermThree 2 4 18 = 0 := by decide +kernel

private theorem explicitCandidateClearedJetRowThree_eighteen_two :
    explicitCandidateClearedJetRowThree 2 18 = 9529320695405040 := by
  simp [explicitCandidateClearedJetRowThree, Fin.sum_univ_succ,
    explicitCandidateClearedJetTermThree_eighteen_two_zero,
    explicitCandidateClearedJetTermThree_eighteen_two_one,
    explicitCandidateClearedJetTermThree_eighteen_two_two,
    explicitCandidateClearedJetTermThree_eighteen_two_three,
    explicitCandidateClearedJetTermThree_eighteen_two_four]

private theorem explicitCandidateClearedJetTermThree_eighteen_three_zero :
    explicitCandidateClearedJetTermThree 3 0 18 = 82280448000 := by decide +kernel

private theorem explicitCandidateClearedJetTermThree_eighteen_three_one :
    explicitCandidateClearedJetTermThree 3 1 18 = -926539716194568 := by decide +kernel

private theorem explicitCandidateClearedJetTermThree_eighteen_three_two :
    explicitCandidateClearedJetTermThree 3 2 18 = 21856278202594560 := by decide +kernel

private theorem explicitCandidateThreeThreeCore_left_lower :
    (∑ k ∈ Finset.range 5,
      jetPow sigmaJetThree 3 k * jetPow widthJetThree 3 (18 - k)) =
      30456116651640888 := by decide +kernel

private theorem explicitCandidateThreeThreeCore_left_upper :
    (∑ k ∈ Finset.Ico 5 10,
      jetPow sigmaJetThree 3 k * jetPow widthJetThree 3 (18 - k)) =
      3024811399680 := by decide +kernel

private theorem explicitCandidateThreeThreeCore_left :
    (∑ k ∈ Finset.range 10,
      jetPow sigmaJetThree 3 k * jetPow widthJetThree 3 (18 - k)) =
      30459141463040568 := by
  rw [← Finset.sum_range_add_sum_Ico _ (by norm_num : 5 ≤ 10),
    explicitCandidateThreeThreeCore_left_lower,
    explicitCandidateThreeThreeCore_left_upper]
  norm_num

private theorem explicitCandidateThreeThreeCore_right :
    (∑ k ∈ Finset.Ico 10 19,
      jetPow sigmaJetThree 3 k * jetPow widthJetThree 3 (18 - k)) =
      2251260 := by decide +kernel

private theorem explicitCandidateClearedJetTermThree_eighteen_three_three :
    explicitCandidateClearedJetTermThree 3 3 18 = -30459141465291828 := by
  norm_num [explicitCandidateClearedJetTermThree, explicitCoeffThree, jetShift]
  rw [jetMul]
  rw [← Finset.sum_range_add_sum_Ico _ (by norm_num : 10 ≤ 19),
    explicitCandidateThreeThreeCore_left, explicitCandidateThreeThreeCore_right]
  norm_num

private theorem explicitCandidateClearedJetTermThree_eighteen_three_four :
    explicitCandidateClearedJetTermThree 3 4 18 = 0 := by decide +kernel

private theorem explicitCandidateClearedJetRowThree_eighteen_three :
    explicitCandidateClearedJetRowThree 3 18 = -9529320698443836 := by
  simp [explicitCandidateClearedJetRowThree, Fin.sum_univ_succ,
    explicitCandidateClearedJetTermThree_eighteen_three_zero,
    explicitCandidateClearedJetTermThree_eighteen_three_one,
    explicitCandidateClearedJetTermThree_eighteen_three_two,
    explicitCandidateClearedJetTermThree_eighteen_three_three,
    explicitCandidateClearedJetTermThree_eighteen_three_four]

private theorem explicitCandidateClearedJetRowThree_eighteen_four :
    explicitCandidateClearedJetRowThree 4 18 = 4108752 := by decide +kernel

private theorem explicitCandidateClearedJetThree_eighteen :
    explicitCandidateClearedJetThree 18 = 0 := by
  simp [explicitCandidateClearedJetThree,
    explicitCandidateClearedJetRowThree_eighteen_zero,
    explicitCandidateClearedJetRowThree_eighteen_one,
    explicitCandidateClearedJetRowThree_eighteen_two,
    explicitCandidateClearedJetRowThree_eighteen_three,
    explicitCandidateClearedJetRowThree_eighteen_four, Fin.sum_univ_succ]

private theorem explicitCandidateClearedJetThree_twenty_four :
    explicitCandidateClearedJetThree 24 = 0 := by decide +kernel

private theorem explicitCandidateClearedJetThree_twenty_seven :
    explicitCandidateClearedJetThree 27 = 0 := by decide +kernel

private theorem explicitCandidateClearedJetRowThree_thirty_six_zero :
    explicitCandidateClearedJetRowThree 0 36 = 1380866012976278427391080 := by
  decide +kernel

private theorem explicitCandidateClearedJetRowThree_thirty_six_one :
    explicitCandidateClearedJetRowThree 1 36 = -578180419613894699719321392 := by
  decide +kernel

private theorem explicitCandidateClearedJetRowThree_thirty_six_two :
    explicitCandidateClearedJetRowThree 2 36 = 4714247207166783486045878412 := by
  decide +kernel

private theorem explicitCandidateClearedJetRowThree_thirty_six_three :
    explicitCandidateClearedJetRowThree 3 36 = -4137447653565867106877979180 := by
  decide +kernel

private theorem explicitCandidateClearedJetRowThree_thirty_six_four :
    explicitCandidateClearedJetRowThree 4 36 = 2042124031080 := by
  decide +kernel

private theorem explicitCandidateClearedJetThree_thirty_six :
    explicitCandidateClearedJetThree 36 = 0 := by
  simp [explicitCandidateClearedJetThree, Fin.sum_univ_succ,
    explicitCandidateClearedJetRowThree_thirty_six_zero,
    explicitCandidateClearedJetRowThree_thirty_six_one,
    explicitCandidateClearedJetRowThree_thirty_six_two,
    explicitCandidateClearedJetRowThree_thirty_six_three,
    explicitCandidateClearedJetRowThree_thirty_six_four]

private theorem explicitCandidateLaurentEvalThree_coeff_eq_jet
    (n : ℕ) (hn : n < 37) :
    explicitCandidateLaurentEvalThree.coeff ((n : ℤ) - 36) =
      explicitCandidateClearedJetThree n := by
  have h := congrArg (fun F : LaurentSeries ℤ ↦ F.coeff (n : ℤ))
    explicitCandidateClearedLaurentEvalThree
  change (HahnSeries.single (36 : ℤ) 1 *
      explicitCandidateLaurentEvalThree).coeff (n : ℤ) =
    (explicitCandidateClearedPowerSeriesThree : LaurentSeries ℤ).coeff (n : ℤ) at h
  rw [HahnSeries.coeff_single_mul, one_mul,
    LaurentSeries.coeff_coe_powerSeries,
    explicitCandidateClearedPowerSeriesThree_coeff_eq_jet n hn] at h
  exact h

private theorem explicitCandidateLaurentEvalThree_observed_coefficients :
    explicitCandidateLaurentEvalThree.coeff 0 = 0 ∧
    explicitCandidateLaurentEvalThree.coeff (-9) = 0 ∧
    explicitCandidateLaurentEvalThree.coeff (-12) = 0 ∧
    explicitCandidateLaurentEvalThree.coeff (-18) = 0 ∧
    explicitCandidateLaurentEvalThree.coeff (-21) = 0 ∧
    explicitCandidateLaurentEvalThree.coeff (-24) = 0 ∧
    explicitCandidateLaurentEvalThree.coeff (-27) = 0 ∧
    explicitCandidateLaurentEvalThree.coeff (-30) = 0 ∧
    explicitCandidateLaurentEvalThree.coeff (-33) = 0 ∧
    explicitCandidateLaurentEvalThree.coeff (-36) = 0 := by
  constructor
  · simpa using (explicitCandidateLaurentEvalThree_coeff_eq_jet 36 (by norm_num)).trans
      explicitCandidateClearedJetThree_thirty_six
  constructor
  · simpa using (explicitCandidateLaurentEvalThree_coeff_eq_jet 27 (by norm_num)).trans
      explicitCandidateClearedJetThree_twenty_seven
  constructor
  · simpa using (explicitCandidateLaurentEvalThree_coeff_eq_jet 24 (by norm_num)).trans
      explicitCandidateClearedJetThree_twenty_four
  constructor
  · simpa using (explicitCandidateLaurentEvalThree_coeff_eq_jet 18 (by norm_num)).trans
      explicitCandidateClearedJetThree_eighteen
  constructor
  · simpa using (explicitCandidateLaurentEvalThree_coeff_eq_jet 15 (by norm_num)).trans
      explicitCandidateClearedJetThree_fifteen
  constructor
  · simpa using (explicitCandidateLaurentEvalThree_coeff_eq_jet 12 (by norm_num)).trans
      explicitCandidateClearedJetThree_twelve
  constructor
  · simpa using (explicitCandidateLaurentEvalThree_coeff_eq_jet 9 (by norm_num)).trans
      explicitCandidateClearedJetThree_nine
  constructor
  · simpa using (explicitCandidateLaurentEvalThree_coeff_eq_jet 6 (by norm_num)).trans
      explicitCandidateClearedJetThree_six
  constructor
  · simpa using (explicitCandidateLaurentEvalThree_coeff_eq_jet 3 (by norm_num)).trans
      explicitCandidateClearedJetThree_three
  · simpa using (explicitCandidateLaurentEvalThree_coeff_eq_jet 0 (by norm_num)).trans
      explicitCandidateClearedJetThree_zero

private theorem int_dvd_iff_dvd_add_natAbs (d : ℕ) (k : ℤ) :
    (d : ℤ) ∣ k ↔ d ∣ (k + d).natAbs := by
  rw [← Int.natCast_dvd]
  constructor
  · intro h
    simpa only using h.add (dvd_refl (d : ℤ))
  · intro h
    simpa only [add_sub_cancel_right] using
      h.sub (dvd_refl (d : ℤ))

private theorem three_dvd_iff_dvd_shift_natAbs (k : ℤ) :
    (3 : ℤ) ∣ k ↔ 3 ∣ (k + 3).natAbs := by
  simpa using int_dvd_iff_dvd_add_natAbs 3 k

private theorem nine_dvd_iff_dvd_shift_natAbs (k : ℤ) :
    (9 : ℤ) ∣ k ↔ 9 ∣ (k + 9).natAbs := by
  simpa using int_dvd_iff_dvd_add_natAbs 9 k

private theorem widthLaurentSeriesThree_eq_integral :
    widthLaurentSeriesThree = jIntegralLaurentSeriesWidth (3 : ℕ+) := by
  ext k
  rw [widthLaurentSeriesThree, HahnSeries.coeff_single_mul,
    jIntegralLaurentSeriesWidth_coeff]
  norm_num
  by_cases hlower : (-3 : ℤ) ≤ k
  · rw [PowerSeries.coeff_coe]
    have hnonneg : 0 ≤ k + 3 := by lia
    rw [if_neg hnonneg.not_gt, widthPowerSeriesThree,
      PowerSeries.coeff_expand]
    by_cases hkdiv : (3 : ℤ) ∣ k
    · rw [if_pos ((three_dvd_iff_dvd_shift_natAbs k).mp hkdiv),
        if_pos ⟨hkdiv, hlower⟩,
        qjIntegralPowerSeriesThree, PowerSeries.coeff_mk]
      rw [Int.natCast_div, Int.natCast_natAbs, abs_of_nonneg hnonneg]
      obtain ⟨t, rfl⟩ := hkdiv
      rw [show (3 : ℤ) * t + 3 = 3 * (t + 1) by ring]
      norm_num [Int.mul_ediv_cancel_left]
    · rw [if_neg (fun h ↦ hkdiv ((three_dvd_iff_dvd_shift_natAbs k).mpr h)),
        if_neg (fun h ↦ hkdiv h.1)]
  · rw [if_neg (fun h ↦ hlower h.2), PowerSeries.coeff_coe]
    have hneg : k + 3 < 0 := by lia
    rw [if_pos hneg]

private theorem widthLaurentSeriesThree_map_complex :
    widthLaurentSeriesThree.map (Int.castRingHom ℂ) =
      laurentqExpansion 3 j := by
  rw [widthLaurentSeriesThree_eq_integral,
    jIntegralLaurentSeriesWidth_map_complex]
  norm_num

private theorem sigmaLaurentSeriesThree_map_complex :
    sigmaLaurentSeriesThree.map (Int.castRingHom ℂ) =
      transformedJSeries (zeta (3 : ℕ+)) (sigmaZero (3 : ℕ+)) := by
  ext k
  change ((sigmaLaurentSeriesThree.coeff k : ℤ) : ℂ) = _
  rw [sigmaLaurentSeriesThree, HahnSeries.coeff_single_mul,
    transformedJSeries_coeff]
  norm_num [sigmaZero]
  by_cases hlower : (-9 : ℤ) ≤ k
  · rw [PowerSeries.coeff_coe]
    have hnonneg : 0 ≤ k + 9 := by lia
    rw [if_neg hnonneg.not_gt, sigmaPowerSeriesThree,
      PowerSeries.coeff_expand]
    by_cases hkdiv : (9 : ℤ) ∣ k
    · rw [if_pos ((nine_dvd_iff_dvd_shift_natAbs k).mp hkdiv),
        if_pos ⟨hkdiv, hlower⟩,
        qjIntegralPowerSeriesThree, PowerSeries.coeff_mk]
      rw [Int.natCast_div, Int.natCast_natAbs, abs_of_nonneg hnonneg]
      obtain ⟨t, rfl⟩ := hkdiv
      rw [show (9 : ℤ) * t + 9 = 9 * (t + 1) by ring]
      norm_num [Int.mul_ediv_cancel_left]
    · rw [if_neg (fun h ↦ hkdiv ((nine_dvd_iff_dvd_shift_natAbs k).mpr h)),
        if_neg (fun h ↦ hkdiv h.1)]
      simp
  · rw [if_neg (fun h ↦ hlower h.2), PowerSeries.coeff_coe]
    have hneg : k + 9 < 0 := by lia
    rw [if_pos hneg]
    simp

private theorem bivariateLaurentEval_map
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (T J : LaurentSeries R) (T' J' : LaurentSeries S)
    (hT : laurentSeriesMapRingHom f T = T')
    (hJ : laurentSeriesMapRingHom f J = J')
    (P : BivariatePolynomial R) :
    laurentSeriesMapRingHom f
        (P.eval₂ (Polynomial.eval₂RingHom HahnSeries.C J) T) =
      (BivariatePolynomial.map f P).eval₂
        (Polynomial.eval₂RingHom HahnSeries.C J') T' := by
  let L := laurentSeriesMapRingHom f
  let innerR := Polynomial.eval₂RingHom (HahnSeries.C : R →+* LaurentSeries R) J
  let innerS := Polynomial.eval₂RingHom (HahnSeries.C : S →+* LaurentSeries S) J'
  have hC : L.comp (HahnSeries.C : R →+* LaurentSeries R) =
      (HahnSeries.C : S →+* LaurentSeries S).comp f := by
    apply DFunLike.ext _ _
    intro r
    exact HahnSeries.map_C r f
  have hinner : L.comp innerR = innerS.comp (Polynomial.mapRingHom f) := by
    apply DFunLike.ext _ _
    intro Q
    change L (Q.eval₂ HahnSeries.C J) = (Q.map f).eval₂ HahnSeries.C J'
    calc
      L (Q.eval₂ HahnSeries.C J) =
          Q.eval₂ (L.comp HahnSeries.C) (L J) :=
        Polynomial.hom_eval₂ Q HahnSeries.C L J
      _ = Q.eval₂ ((HahnSeries.C : S →+* LaurentSeries S).comp f) J' := by
        rw [hC, hJ]
      _ = (Q.map f).eval₂ HahnSeries.C J' :=
        (Polynomial.eval₂_map f HahnSeries.C J').symm
  calc
    L (P.eval₂ innerR T) = P.eval₂ (L.comp innerR) (L T) :=
      Polynomial.hom_eval₂ P innerR L T
    _ = P.eval₂ (innerS.comp (Polynomial.mapRingHom f)) T' := by
      rw [hinner, hT]
    _ = (BivariatePolynomial.map f P).eval₂ innerS T' := by
      exact (Polynomial.eval₂_map (Polynomial.mapRingHom f) innerS T').symm

private def explicitCandidateLaurentEvalComplexThree : LaurentSeries ℂ :=
  (BivariatePolynomial.map (Int.castRingHom ℂ) modularPolynomialThreeExplicit).eval₂
    (Polynomial.eval₂RingHom HahnSeries.C (laurentqExpansion 3 j))
    (transformedJSeries (zeta (3 : ℕ+)) (sigmaZero (3 : ℕ+)))

private theorem explicitCandidateLaurentEvalThree_map_complex :
    laurentSeriesMapRingHom (Int.castRingHom ℂ)
        explicitCandidateLaurentEvalThree =
      explicitCandidateLaurentEvalComplexThree := by
  apply bivariateLaurentEval_map
  · exact sigmaLaurentSeriesThree_map_complex
  · exact widthLaurentSeriesThree_map_complex

private theorem explicitCandidateLaurentEvalComplexThree_coeff (k : ℤ) :
    explicitCandidateLaurentEvalComplexThree.coeff k =
      (explicitCandidateLaurentEvalThree.coeff k : ℂ) := by
  rw [← explicitCandidateLaurentEvalThree_map_complex]
  rfl

private theorem explicitCandidateLaurentEvalComplexThree_observed_coefficients :
    explicitCandidateLaurentEvalComplexThree.coeff 0 = 0 ∧
    explicitCandidateLaurentEvalComplexThree.coeff (-9) = 0 ∧
    explicitCandidateLaurentEvalComplexThree.coeff (-12) = 0 ∧
    explicitCandidateLaurentEvalComplexThree.coeff (-18) = 0 ∧
    explicitCandidateLaurentEvalComplexThree.coeff (-21) = 0 ∧
    explicitCandidateLaurentEvalComplexThree.coeff (-24) = 0 ∧
    explicitCandidateLaurentEvalComplexThree.coeff (-27) = 0 ∧
    explicitCandidateLaurentEvalComplexThree.coeff (-30) = 0 ∧
    explicitCandidateLaurentEvalComplexThree.coeff (-33) = 0 ∧
    explicitCandidateLaurentEvalComplexThree.coeff (-36) = 0 := by
  simpa only [explicitCandidateLaurentEvalComplexThree_coeff, Int.cast_eq_zero] using
    explicitCandidateLaurentEvalThree_observed_coefficients

private theorem modularPolynomialC_three_laurent_root :
    (modularPolynomialC (3 : ℕ+)).eval₂
        (Polynomial.eval₂RingHom (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
          (laurentqExpansion 3 j))
        (transformedJSeries (zeta (3 : ℕ+)) (sigmaZero (3 : ℕ+))) = 0 := by
  rw [Polynomial.eval₂_eq_eval_map]
  have hformal := formalCoxPolynomial_eq_modularPolynomialC_map_j (3 : ℕ+)
  norm_num at hformal
  rw [← hformal]
  rw [formalCoxPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (sigmaZero (3 : ℕ+)))
  simp

private theorem transformedJSeries_three_sigmaZero_order :
    (transformedJSeries (zeta (3 : ℕ+)) (sigmaZero (3 : ℕ+))).order = -9 := by
  rw [transformedJSeries_order (zeta (3 : ℕ+))
    ((zeta_isPrimitiveRoot (3 : ℕ+)).ne_zero (PNat.ne_zero (3 : ℕ+)))]
  norm_num [sigmaZero]

private theorem transformedJSeries_three_sigmaZero_leadingCoeff :
    (transformedJSeries (zeta (3 : ℕ+))
      (sigmaZero (3 : ℕ+))).leadingCoeff = 1 := by
  rw [transformedJSeries_leadingCoeff (zeta (3 : ℕ+))
    ((zeta_isPrimitiveRoot (3 : ℕ+)).ne_zero (PNat.ne_zero (3 : ℕ+)))]
  norm_num [sigmaZero]

private theorem laurentqExpansion_j_order_three :
    (laurentqExpansion 3 j).order = -3 := by
  have h := laurentqExpansion_j_order_widthM (3 : ℕ+)
  norm_num at h ⊢
  exact h

private theorem laurentqExpansion_j_leadingCoeff_three :
    (laurentqExpansion 3 j).leadingCoeff = 1 := by
  have h := laurentqExpansion_j_leadingCoeff_widthM (3 : ℕ+)
  norm_num at h ⊢
  exact h

private def modularPolynomialThreeComplexExplicit : BivariatePolynomial ℂ :=
  BivariatePolynomial.map (Int.castRingHom ℂ) modularPolynomialThreeExplicit

private def modularPolynomialThreeDifference : BivariatePolynomial ℂ :=
  modularPolynomialC (3 : ℕ+) - modularPolynomialThreeComplexExplicit

private theorem modularPolynomialC_three_natDegree :
    (modularPolynomialC (3 : ℕ+)).natDegree = 4 := by
  rw [modularPolynomialC_natDegree]
  have hcard := Fintype.card_congr (primeCoxMatrixEquiv (3 : ℕ+))
  norm_num at hcard ⊢
  exact hcard

private theorem modularPolynomialThreeComplexExplicit_monic :
    modularPolynomialThreeComplexExplicit.Monic := by
  simpa only [modularPolynomialThreeComplexExplicit, BivariatePolynomial.map] using
    modularPolynomialThreeExplicit_monic.map
      (Polynomial.mapRingHom (Int.castRingHom ℂ))

private theorem modularPolynomialThreeComplexExplicit_natDegree :
    modularPolynomialThreeComplexExplicit.natDegree = 4 := by
  have h := modularPolynomialThreeExplicit_monic.natDegree_map
    (Polynomial.mapRingHom (Int.castRingHom ℂ))
  simpa only [modularPolynomialThreeComplexExplicit, BivariatePolynomial.map,
    modularPolynomialThreeExplicit_natDegree] using h

private theorem modularPolynomialThreeComplexExplicit_swap :
    Polynomial.Bivariate.swap modularPolynomialThreeComplexExplicit =
      modularPolynomialThreeComplexExplicit := by
  rw [modularPolynomialThreeComplexExplicit,
    ← BivariatePolynomial.map_swap, modularPolynomialThreeExplicit_swap]

private theorem modularPolynomialThreeDifference_swap
    (hsymm : Polynomial.Bivariate.swap (modularPolynomialC (3 : ℕ+)) =
      modularPolynomialC (3 : ℕ+)) :
    Polynomial.Bivariate.swap modularPolynomialThreeDifference =
      modularPolynomialThreeDifference := by
  rw [modularPolynomialThreeDifference, map_sub,
    hsymm, modularPolynomialThreeComplexExplicit_swap]

private theorem modularPolynomialThreeDifference_natDegree_le :
    modularPolynomialThreeDifference.natDegree ≤ 3 := by
  rw [← Nat.lt_succ_iff]
  apply Polynomial.IsMonicOfDegree.natDegree_sub_lt (by norm_num)
  · exact ⟨modularPolynomialC_three_natDegree,
      modularPolynomialC_monic (3 : ℕ+)⟩
  · exact ⟨modularPolynomialThreeComplexExplicit_natDegree,
      modularPolynomialThreeComplexExplicit_monic⟩

private theorem modularPolynomialThreeDifference_inner_natDegree_le
    (hsymm : Polynomial.Bivariate.swap (modularPolynomialC (3 : ℕ+)) =
      modularPolynomialC (3 : ℕ+)) (i : ℕ) :
    (modularPolynomialThreeDifference.coeff i).natDegree ≤ 3 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  calc
    (modularPolynomialThreeDifference.coeff i).coeff n =
        ((Polynomial.Bivariate.swap modularPolynomialThreeDifference).coeff n).coeff i :=
      (BivariatePolynomial.coeff_coeff_swap modularPolynomialThreeDifference n i).symm
    _ = (modularPolynomialThreeDifference.coeff n).coeff i := by
      rw [modularPolynomialThreeDifference_swap hsymm]
    _ = 0 := by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (modularPolynomialThreeDifference_natDegree_le.trans_lt hn)]
      simp

private def modularPolynomialThreeDifferenceLaurentEval : LaurentSeries ℂ :=
  modularPolynomialThreeDifference.eval₂
    (Polynomial.eval₂RingHom HahnSeries.C (laurentqExpansion 3 j))
    (transformedJSeries (zeta (3 : ℕ+)) (sigmaZero (3 : ℕ+)))

private theorem modularPolynomialThreeDifferenceLaurentEval_eq :
    modularPolynomialThreeDifferenceLaurentEval =
      -explicitCandidateLaurentEvalComplexThree := by
  rw [modularPolynomialThreeDifferenceLaurentEval,
    modularPolynomialThreeDifference, Polynomial.eval₂_sub,
    modularPolynomialC_three_laurent_root, zero_sub]
  rfl

private theorem modularPolynomialThreeDifference_observed_coefficients :
    modularPolynomialThreeDifferenceLaurentEval.coeff 0 = 0 ∧
    modularPolynomialThreeDifferenceLaurentEval.coeff (-9) = 0 ∧
    modularPolynomialThreeDifferenceLaurentEval.coeff (-12) = 0 ∧
    modularPolynomialThreeDifferenceLaurentEval.coeff (-18) = 0 ∧
    modularPolynomialThreeDifferenceLaurentEval.coeff (-21) = 0 ∧
    modularPolynomialThreeDifferenceLaurentEval.coeff (-24) = 0 ∧
    modularPolynomialThreeDifferenceLaurentEval.coeff (-27) = 0 ∧
    modularPolynomialThreeDifferenceLaurentEval.coeff (-30) = 0 ∧
    modularPolynomialThreeDifferenceLaurentEval.coeff (-33) = 0 ∧
    modularPolynomialThreeDifferenceLaurentEval.coeff (-36) = 0 := by
  simpa only [modularPolynomialThreeDifferenceLaurentEval_eq,
    HahnSeries.coeff_neg, neg_eq_zero] using
      explicitCandidateLaurentEvalComplexThree_observed_coefficients

private theorem modularPolynomialThreeDifference_eq_zero
    (hsymm : Polynomial.Bivariate.swap (modularPolynomialC (3 : ℕ+)) =
      modularPolynomialC (3 : ℕ+)) :
    modularPolynomialThreeDifference = 0 := by
  apply symmetric_bidegree_three_eq_zero_of_laurent_coeff
    (transformedJSeries (zeta (3 : ℕ+)) (sigmaZero (3 : ℕ+)))
    (laurentqExpansion 3 j)
  · exact transformedJSeries_three_sigmaZero_order
  · exact laurentqExpansion_j_order_three
  · exact transformedJSeries_three_sigmaZero_leadingCoeff
  · exact laurentqExpansion_j_leadingCoeff_three
  · exact modularPolynomialThreeDifference_natDegree_le
  · exact modularPolynomialThreeDifference_inner_natDegree_le hsymm
  · exact modularPolynomialThreeDifference_swap hsymm
  · simpa only [modularPolynomialThreeDifferenceLaurentEval] using
      modularPolynomialThreeDifference_observed_coefficients

private theorem modularPolynomialC_three_eq_explicit
    (hsymm : Polynomial.Bivariate.swap (modularPolynomialC (3 : ℕ+)) =
      modularPolynomialC (3 : ℕ+)) :
    modularPolynomialC (3 : ℕ+) = modularPolynomialThreeComplexExplicit := by
  rw [← sub_eq_zero]
  exact modularPolynomialThreeDifference_eq_zero hsymm

/-- Symmetry of the complex level-three modular polynomial implies Cox's explicit formula. -/
theorem modularPolynomial_three_of_complex_swap
    (hsymm : Polynomial.Bivariate.swap (modularPolynomialC (3 : ℕ+)) =
      modularPolynomialC (3 : ℕ+)) :
    modularPolynomial (3 : ℕ+) = modularPolynomialThreeExplicit := by
  have hmap :
      BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial (3 : ℕ+)) =
        BivariatePolynomial.map (Int.castRingHom ℂ) modularPolynomialThreeExplicit := by
    rw [modularPolynomial_map_complex]
    exact modularPolynomialC_three_eq_explicit hsymm
  exact Polynomial.map_injective (Polynomial.mapRingHom (Int.castRingHom ℂ))
    (Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective) hmap

end Cox
