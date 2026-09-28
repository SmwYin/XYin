/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.jFunction.jfunction
import XYin.PhD.qExpansion_tactic.Qj

/-!
# Soundness of the `q`-expansion tactic's integer coefficients

The computational definitions in `Qj` build integer coefficient arrays (`Array.ofFn`
tabulations, `Finset.range` convolutions and a power-series inversion loop).  This file proves
that those arrays compute the true analytic `q`-expansion coefficients: bridging lemmas relate
the array operations to `PowerSeries` coefficients, and the main theorems identify the
resulting formal `ℤ`-series with the analytic `q`-expansions after the base change `ℤ → ℂ`.

## Main results

* `deltaQExpansion_link`: `deltaQExpansion` maps to the `q`-expansion of `Δ` under
  `ℤ → ℂ`, so the array-computed coefficients are the Ramanujan `τ` values.
* `qjQExpansion_link`: `qjQExpansion` maps to the `q`-expansion of `q·j`, so the
  array-computed coefficients are the `j`-invariant Fourier coefficients.
* `discriminant_qxp_coeff_link`, `ramanujanTau_link`, `qj_qxp_coeff_link`, `qjCoeffs_eq_qjCoeffInt`:
  coefficientwise transfer statements consumed by `jFunction.qexp_coeffs` and `Cox.LevelThree`.
-/

open UpperHalfPlane PowerSeries ModularForm ModularFormClass
open QExpansionTactic
open IntegralPowerSeries

namespace QExpansionTactic

/-- `Array.getD` agrees with `List.getD` on the underlying list. -/
lemma array_getD_eq_toList_getD (arr : Array Int) (i : Nat) :
    arr.getD i 0 = arr.toList.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, ← List.getElem?_toArray,
      Array.toArray_toList]

/-- Reading off an entry of a tabulated list. -/
lemma getD_map_range (g : Nat → Int) (L j : Nat) (hj : j < L) :
    ((List.range L).map g).getD j 0 = g j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- The coefficient recursion of `PowerSeries.invOfUnit φ 1` at a successor index, in the
`range`-sum form matching the loop step `invStep`. -/
lemma coeff_invOfUnit_one_succ {R : Type*} [Ring R] (φ : PowerSeries R) (m : Nat) :
    (φ.invOfUnit 1).coeff (m + 1) =
      -∑ i ∈ Finset.range (m + 1), φ.coeff (i + 1) * (φ.invOfUnit 1).coeff (m - i) := by
  rw [PowerSeries.coeff_invOfUnit, if_neg (Nat.succ_ne_zero m),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun x y => if y < m + 1 then φ.coeff x * (φ.invOfUnit 1).coeff y else 0) (m + 1),
      Finset.sum_range_succ']
  simp [Nat.succ_sub_succ_eq_sub]

end QExpansionTactic

/-! ### Reading off the coefficient arrays -/

/-- Reading off an entry of a tabulated array gives the tabulated value. -/
lemma coeffArray_getD (f : Nat → Int) (n i : Nat) (hi : i ≤ n) :
    (coeffArray f n).getD i 0 = f i := by
  simp [coeffArray, Nat.lt_succ_of_le hi]

lemma convArrayUpTo_getD (A B : Array Int) (n i : Nat) (hi : i ≤ n) :
    (convArrayUpTo A B n).getD i 0 = convArrayCoeff A B i :=
  coeffArray_getD _ n i hi

/-- Convolution of two arrays (agreeing with the coefficients of `F`, `G` up to index `m`)
equals the coefficient of the product power series, for indices up to `m`. -/
lemma convArrayCoeff_eq_coeff_mul {A B : Array Int} {F G : PowerSeries ℤ} {m i : Nat}
    (hA : ∀ j ≤ m, A.getD j 0 = F.coeff j) (hB : ∀ j ≤ m, B.getD j 0 = G.coeff j)
    (hi : i ≤ m) : convArrayCoeff A B i = (F * G).coeff i := by
  rw [convArrayCoeff, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y ↦ F.coeff x * G.coeff y) i]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rw [hA k (by omega), hB (i - k) (by omega)]

private lemma coeffArray_getD_coeff_mk (f : Nat → Int) (N : Nat) :
    ∀ j ≤ N, (coeffArray f N).getD j 0 = (PowerSeries.mk f).coeff j := fun j hj ↦ by
  rw [coeffArray_getD f N j hj, coeff_mk]

/-- The "square" array (`convArrayUpTo` of `coeffArray f` with itself) reads off the
coefficients of `(mk f) ^ 2`. -/
lemma convArrayUpTo_self_coeff (f : Nat → Int) (N i : Nat) (hi : i ≤ N) :
    (convArrayUpTo (coeffArray f N) (coeffArray f N) N).getD i 0
      = ((PowerSeries.mk f) ^ 2).coeff i := by
  rw [convArrayUpTo_getD _ _ N i hi, pow_two]
  exact convArrayCoeff_eq_coeff_mul (coeffArray_getD_coeff_mk f N) (coeffArray_getD_coeff_mk f N)
    hi

/-- The "cube" array reads off the coefficients of `(mk f) ^ 3`. -/
lemma convArrayUpTo_cube_coeff (f : Nat → Int) (N i : Nat) (hi : i ≤ N) :
    (convArrayUpTo (convArrayUpTo (coeffArray f N) (coeffArray f N) N)
        (coeffArray f N) N).getD i 0
      = ((PowerSeries.mk f) ^ 3).coeff i := by
  rw [convArrayUpTo_getD _ _ N i hi, pow_succ]
  exact convArrayCoeff_eq_coeff_mul (fun j hj ↦ convArrayUpTo_self_coeff f N j hj)
    (coeffArray_getD_coeff_mk f N) hi

/-! ### The Eisenstein series and `Δ` -/

lemma e4CoeffInt_eq_integralE4_coeff (n : Nat) : e4CoeffInt n = integralE4.coeff n :=
  (integralE4_coeff n).symm

lemma e6CoeffInt_eq_integralE6_coeff (n : Nat) : e6CoeffInt n = integralE6.coeff n :=
  (integralE6_coeff n).symm

lemma E₄_int_series_eq : PowerSeries.mk e4CoeffInt = integralE4 :=
  PowerSeries.ext fun n ↦ (coeff_mk _ _).trans (e4CoeffInt_eq_integralE4_coeff n)

lemma E₆_int_series_eq : PowerSeries.mk e6CoeffInt = integralE6 :=
  PowerSeries.ext fun n ↦ (coeff_mk _ _).trans (e6CoeffInt_eq_integralE6_coeff n)

/-- The array-computed `E₄` coefficients form the q-expansion of `E₄`. -/
lemma E₄_int_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk e4CoeffInt) = qExpansion 1 E₄ := by
  rw [E₄_int_series_eq]
  exact mapAlgHom_ofId_toIntegralPowerSeries E₄_isIntegralPowerSeries

/-- Entry `k` of the `Δ`-coefficient table `deltaCoeffsArrayUpTo top` is the `k`-th
coefficient of the formal series `(E₄³ - E₆²) / 1728`, independently of the table size. -/
lemma deltaCoeffsArrayUpTo_getD (top k : Nat) (hk : k ≤ top) :
    (deltaCoeffsArrayUpTo top).getD k 0 =
      (((PowerSeries.mk e4CoeffInt) ^ 3 - (PowerSeries.mk e6CoeffInt) ^ 2).coeff k) / 1728 := by
  simp only [deltaCoeffsArrayUpTo]
  rw [coeffArray_getD _ top k hk, convArrayUpTo_cube_coeff e4CoeffInt top k hk,
      convArrayUpTo_self_coeff e6CoeffInt top k hk, map_sub]

/-- The array-based `deltaCoeffInt` agrees with the convolution definition of the
`Δ`-coefficients. -/
lemma deltaCoeffInt_eq (n : Nat) :
    deltaCoeffInt n =
      (((PowerSeries.mk e4CoeffInt) ^ 3 - (PowerSeries.mk e6CoeffInt) ^ 2).coeff n) / 1728 :=
  deltaCoeffsArrayUpTo_getD n n le_rfl

/-- Entries of the `Δ`-coefficient table are stable in the table size: any table large
enough to contain index `k` reads off `deltaCoeffInt k` there. -/
lemma delta_array_getD (top k : Nat) (hk : k ≤ top) :
    (deltaCoeffsArrayUpTo top).getD k 0 = deltaCoeffInt k := by
  rw [deltaCoeffsArrayUpTo_getD top k hk, ← deltaCoeffInt_eq]

/-- The complex cast of the `n`-th coefficient of `integralE4 ^ 3 - integralE6 ^ 2` is the
`n`-th `q`-expansion coefficient of the modular form `E₄³ - E₆²`. -/
lemma eisenstein_difference_coeff_cast (n : ℕ) :
    (((integralE4 ^ 3 - integralE6 ^ 2).coeff n : ℤ) : ℂ) =
      (qExpansion 1 (⇑E₄ ^ 3 - ⇑E₆ ^ 2)).coeff n := by
  rw [← coeToComplexPowerSeries.coeff_ringHom_int, map_integralE4_pow_three_sub_integralE6_pow_two]

/-- **Soundness for `Δ`**: the base change to `ℂ` of the array-computed series
`deltaQExpansion` is the q-expansion of `Δ`, so `deltaCoeffInt n` is the Ramanujan `τ(n)`. -/
theorem deltaQExpansion_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) deltaQExpansion = qExpansion 1 discriminant := by
  ext n
  rw [coeff_mapAlgHom_ofId_int, deltaQExpansion_coeff_eq, deltaCoeffInt_eq, E₄_int_series_eq,
    E₆_int_series_eq, discriminant_qExpansion_eq_smul_eisenstein_difference, PowerSeries.coeff_smul,
    ← eisenstein_difference_coeff_cast,
    Int.cast_div_charZero (Int.modEq_zero_iff_dvd.1 (eisenstein_difference_coeff_modEq_zero n)),
    smul_eq_mul, div_eq_inv_mul, one_div]
  push_cast
  rfl

/-- Coefficientwise form of `deltaQExpansion_link`. -/
theorem discriminant_qxp_coeff_link (n : ℕ) :
    (qExpansion 1 discriminant).coeff n = deltaQExpansion.coeff n :=
  (congrArg (PowerSeries.coeff n) deltaQExpansion_link).symm

/-- Cast form of `deltaQExpansion_link`: the array-computed integer `τ(n)`, viewed in `ℂ`,
is the `n`-th analytic `q`-expansion coefficient of `Δ`. -/
lemma deltaCoeffInt_cast (n : ℕ) :
    ((deltaCoeffInt n : ℤ) : ℂ) = (qExpansion 1 discriminant).coeff n := by
  rw [← deltaQExpansion_coeff_eq, ← coeff_mapAlgHom_ofId_int, deltaQExpansion_link]

/-- The Ramanujan tau values `ramanujanTau n` (the coefficients of the integral lift of the
q-expansion of `Δ`) are the array-computed coefficients. -/
theorem ramanujanTau_link (n : ℕ) : ramanujanTau n = deltaQExpansion.coeff n := by
  rw [deltaQExpansion_coeff_eq]
  exact_mod_cast (ramanujanTau_cast n).trans (deltaCoeffInt_cast n).symm

/-! ### The unit `Δ / q` and its inverse -/

/-- The shifted `Δ`-coefficients form the q-expansion of `deltaOverQ = Δ / q`. -/
lemma deltaOverQ_qexpansion_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk deltaOverQCoeffInt) =
      qExpansion 1 deltaOverQ := by
  ext n
  rw [coeff_mapAlgHom_ofId_int, coeff_mk, deltaOverQCoeffInt, deltaCoeffInt_cast,
    deltaOverQ_qExpansion_coeff]

lemma deltaOverQCoeffInt_zero : deltaOverQCoeffInt 0 = 1 := by
  exact_mod_cast (deltaCoeffInt_cast 1).trans discriminant_qExpansion_coeff_one

/-- Loop invariant for `inverseOnePlusCoeffsUpTo`: after `K` steps the accumulator array
tabulates the coefficients of `(PowerSeries.mk α).invOfUnit 1` on `0..K-1`, provided the
input array agrees with `α` up to index `N`. -/
lemma inverseOnePlusCoeffsUpTo_toList (a : Array Int) (α : Nat → Int) (N : Nat)
    (hα : ∀ j ≤ N, a.getD j 0 = α j) :
    ∀ K, K ≤ N + 1 →
      ((List.range K).foldl (invStep a) #[]).toList
        = (List.range K).map fun i => ((PowerSeries.mk α).invOfUnit 1).coeff i := by
  intro K
  induction K with
  | zero => intro _; simp
  | succ K ih =>
      intro hK
      rw [List.range_succ, List.foldl_concat]
      have hacc := ih (by omega)
      rcases K with _ | m
      · simp [invStep, PowerSeries.coeff_zero_eq_constantCoeff]
      · rw [invStep, Array.toList_push, hacc, List.map_append]
        congr 1
        simp only [List.map_cons, List.map_nil]
        congr 1
        rw [coeff_invOfUnit_one_succ]
        congr 1
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [Finset.mem_range] at hi
        rw [hα (i + 1) (by omega), array_getD_eq_toList_getD, hacc,
            getD_map_range _ _ _ (by omega), PowerSeries.coeff_mk]

lemma inverseOnePlusCoeffsUpTo_getD (a : Array Int) (α : Nat → Int) (N : Nat)
    (hα : ∀ j ≤ N, a.getD j 0 = α j) (i : Nat) (hi : i ≤ N) :
    (inverseOnePlusCoeffsUpTo a N).getD i 0 = ((PowerSeries.mk α).invOfUnit 1).coeff i := by
  rw [array_getD_eq_toList_getD, inverseOnePlusCoeffsUpTo,
    inverseOnePlusCoeffsUpTo_toList a α N hα (N + 1) le_rfl]
  exact getD_map_range _ (N + 1) i (by omega)

/-- Entry `j` of the shifted table `deltaOverQArrayUpTo n` is `deltaOverQCoeffInt j`. -/
lemma deltaOverQArrayUpTo_getD (n j : Nat) (hj : j ≤ n) :
    (deltaOverQArrayUpTo n).getD j 0 = deltaOverQCoeffInt j := by
  simp only [deltaOverQArrayUpTo]
  rw [coeffArray_getD _ n j hj, delta_array_getD (n + 1) (j + 1) (by omega)]
  rfl

/-- Entry `i` of `qoverDeltaCoeffsArrayUpTo n` is the `i`-th coefficient of the formal inverse
of `Δ/q`. -/
lemma qoverDelta_array_getD (n i : Nat) (hi : i ≤ n) :
    (qoverDeltaCoeffsArrayUpTo n).getD i 0 =
      ((PowerSeries.mk deltaOverQCoeffInt).invOfUnit 1).coeff i :=
  inverseOnePlusCoeffsUpTo_getD _ deltaOverQCoeffInt n
    (fun j hj => deltaOverQArrayUpTo_getD n j hj) i hi

/-- The array-based `qoverDeltaCoeffInt` computes the coefficients of the formal inverse
of the series `Δ/q`. -/
lemma qoverDeltaCoeffInt_eq (n : Nat) :
    qoverDeltaCoeffInt n = ((PowerSeries.mk deltaOverQCoeffInt).invOfUnit 1).coeff n :=
  qoverDelta_array_getD n n le_rfl

/-- The array-computed series of `Δ/q` and `q/Δ` are mutually inverse. -/
lemma qoverDelta_mul_eq_one :
    (PowerSeries.mk deltaOverQCoeffInt) * (PowerSeries.mk qoverDeltaCoeffInt) = 1 := by
  have h : PowerSeries.mk qoverDeltaCoeffInt =
      (PowerSeries.mk deltaOverQCoeffInt).invOfUnit 1 :=
    PowerSeries.ext fun n ↦ (coeff_mk _ _).trans (qoverDeltaCoeffInt_eq n)
  rw [h]
  exact PowerSeries.mul_invOfUnit _ 1 (by simp [deltaOverQCoeffInt_zero])

/-- The array-computed series of `q/Δ` is the q-expansion of `qOverDelta`. -/
lemma qOverDelta_qexpansion_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk qoverDeltaCoeffInt) =
      qExpansion 1 qOverDelta := by
  have hAunit : IsUnit (qExpansion 1 deltaOverQ) := by
    rw [← deltaOverQ_qexpansion_link, PowerSeries.isUnit_iff_constantCoeff,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_mapAlgHom_ofId_int, coeff_mk,
      deltaOverQCoeffInt_zero, Int.cast_one]
    exact isUnit_one
  apply hAunit.mul_left_cancel
  rw [← deltaOverQ_qexpansion_link, ← map_mul, qoverDelta_mul_eq_one, map_one,
    deltaOverQ_qexpansion_link, ← coeTo_integralDeltaOverQ]
  exact integralDeltaOverQ_mul_qExpansion_qOverDelta.symm

/-! ### The regularized `j`-function -/

/-- The array-based `qjCoeffInt` agrees with the convolution `(mk e4CoeffInt)^3 * (q/Δ)`. -/
lemma qjCoeffInt_eq (n : Nat) :
    qjCoeffInt n =
      ((PowerSeries.mk e4CoeffInt) ^ 3 * PowerSeries.mk qoverDeltaCoeffInt).coeff n := by
  simp only [qjCoeffInt, qjCoeffsArrayUpTo]
  rw [convArrayUpTo_getD _ _ n n le_rfl]
  exact convArrayCoeff_eq_coeff_mul
    (fun j hj ↦ convArrayUpTo_cube_coeff e4CoeffInt (n + 1) j (by omega))
    (fun j hj ↦ by rw [qoverDelta_array_getD n j hj, ← qoverDeltaCoeffInt_eq, coeff_mk]) le_rfl

lemma qj_series_eq :
    PowerSeries.mk qjCoeffInt =
      (PowerSeries.mk e4CoeffInt) ^ 3 * PowerSeries.mk qoverDeltaCoeffInt :=
  PowerSeries.ext fun n ↦ (coeff_mk _ _).trans (qjCoeffInt_eq n)

/-- **Soundness for `q·j`**: the base change to `ℂ` of the array-computed series
`qjQExpansion` is the q-expansion of `qj = q · j`, so `qjCoeffInt n` is the Fourier
coefficient `c(n - 1)` of `j`. -/
theorem qjQExpansion_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) qjQExpansion = qExpansion 1 qj := by
  rw [qjQExpansion, qj_series_eq, map_mul, map_pow, E₄_int_link, qOverDelta_qexpansion_link,
    ← E₄_pow_three_qExpansion, ← qExpansion_mul E₄_pow_three_cuspFunction_analyticAt
      qOverDelta_cuspFunction_analyticAt, E₄_pow_three_mul_qOverDelta_eq_qj]

/-- Coefficientwise form of `qjQExpansion_link`. -/
theorem qj_qxp_coeff_link (n : ℕ) :
    (qExpansion 1 qj).coeff n = qjQExpansion.coeff n :=
  (congrArg (PowerSeries.coeff n) qjQExpansion_link).symm

/-- The integral q-expansion coefficients `qjCoeffs n` of `qj` are the array-computed integers
`qjCoeffInt n`. -/
theorem qjCoeffs_eq_qjCoeffInt (n : ℕ) : qjCoeffs n = qjCoeffInt n := by
  rw [← qjQExpansion_coeff_eq]
  exact_mod_cast (qjCoeffs_cast n).trans (qj_qxp_coeff_link n)
