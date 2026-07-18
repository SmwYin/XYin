import XYin.PhD.jFunction.jfunction
import XYin.PhD.qExpansion_tactic.Qj

set_option linter.style.header false

/-!
# Soundness of the `q`-expansion tactic's integer coefficients

The computational definitions in `Qj` build integer coefficient arrays via
`Array.foldl`/`push` for speed.  This file proves that those arrays compute the true
analytic `q`-expansion coefficients: bridging lemmas relate the array operations to
`PowerSeries` coefficients, and the main theorems identify the resulting formal
`ℤ`-series with the analytic `q`-expansions after the base change `ℤ → ℂ`.

## Main results

* `Delta_qexpansion_link`: `Delta_qexpansion` maps to the `q`-expansion of `Δ` under
  `ℤ → ℂ`, so the array-computed coefficients are the Ramanujan `τ` values.
* `qj_qexpansion_link`: `qj_qexpansion` maps to the `q`-expansion of `q·j`, so the
  array-computed coefficients are the `j`-invariant Fourier coefficients.
* `Delta_qxp_coeff_link`, `ramanujanTau_link`, `qj_qxp_coeff_link`: coefficientwise
  transfer statements consumed by `jFunction.qexp_coeffs` and `Cox.LevelThree`.
-/

open UpperHalfPlane PowerSeries ModularForm ModularFormClass
open XYin.PhD.qExpansion_tactic
open IntegralPowerSeries
open ArithmeticFunction

lemma foldl_range_add_eq_sum (f : Nat → Int) (n : Nat) :
    List.foldl (fun acc i => acc + f i) 0 (List.range n) = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_concat, ih, Finset.sum_range_succ]

/-- The array produced by tabulating `g` over `range m` (via `foldl`/`push`) has the
expected underlying list. -/
lemma foldl_push_toList (g : Nat → Int) (m : Nat) :
    ((List.range m).foldl (fun acc j => acc.push (g j)) (#[] : Array Int)).toList
      = (List.range m).map g := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_concat, Array.toList_push, ih, List.map_append]
      simp

/-- Reading off an entry from a tabulated array gives the tabulated value. -/
lemma foldl_push_getD (g : Nat → Int) (m i : Nat) (hi : i < m) :
    ((List.range m).foldl (fun acc j => acc.push (g j)) (#[] : Array Int)).getD i 0 = g i := by
  have h : ((List.range m).foldl (fun acc j => acc.push (g j)) (#[] : Array Int))
      = ((List.range m).map g).toArray := by
    rw [← foldl_push_toList g m, Array.toArray_toList]
  rw [h, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range hi]
  rfl

lemma coeffArray_getD (f : Nat → Int) (n i : Nat) (hi : i ≤ n) :
    (coeffArray f n).getD i 0 = f i := by
  unfold coeffArray
  exact foldl_push_getD f (n + 1) i (by omega)

lemma convArrayUpTo_getD (A B : Array Int) (n i : Nat) (hi : i ≤ n) :
    (convArrayUpTo A B n).getD i 0 = convArrayCoeff A B i := by
  unfold convArrayUpTo
  exact foldl_push_getD (fun j => convArrayCoeff A B j) (n + 1) i (by omega)

/-- Convolution of two arrays (agreeing with `α`, `β` up to index `m`) equals the
coefficient of the product power series, for indices up to `m`. -/
lemma convArrayCoeff_eq_coeff_mul (A B : Array Int) (α β : Nat → Int) (m i : Nat)
    (hA : ∀ j ≤ m, A.getD j 0 = α j) (hB : ∀ j ≤ m, B.getD j 0 = β j) (hi : i ≤ m) :
    convArrayCoeff A B i = ((PowerSeries.mk α) * (PowerSeries.mk β)).coeff i := by
  rw [convArrayCoeff, foldl_range_add_eq_sum, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun x y => (PowerSeries.mk α).coeff x * (PowerSeries.mk β).coeff y) i]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [hA k (by omega), hB (i - k) (by omega), PowerSeries.coeff_mk, PowerSeries.coeff_mk]

/-- `mk`/`coeff` round-trip. -/
lemma mk_coeff_self (F : PowerSeries ℤ) :
    (PowerSeries.mk fun j => F.coeff j) = F := by
  ext j
  rw [PowerSeries.coeff_mk]

/-- The "square" array (`convArrayUpTo` of `coeffArray f` with itself) reads off the
coefficients of `(mk f) ^ 2`. -/
lemma convArrayUpTo_self_coeff (f : Nat → Int) (N i : Nat) (hi : i ≤ N) :
    (convArrayUpTo (coeffArray f N) (coeffArray f N) N).getD i 0
      = ((PowerSeries.mk f) ^ 2).coeff i := by
  rw [convArrayUpTo_getD _ _ N i hi,
      convArrayCoeff_eq_coeff_mul (coeffArray f N) (coeffArray f N) f f N i
        (fun j hj => coeffArray_getD f N j hj) (fun j hj => coeffArray_getD f N j hj) hi,
      pow_two]

/-- The "cube" array reads off the coefficients of `(mk f) ^ 3`. -/
lemma convArrayUpTo_cube_coeff (f : Nat → Int) (N i : Nat) (hi : i ≤ N) :
    (convArrayUpTo (convArrayUpTo (coeffArray f N) (coeffArray f N) N)
        (coeffArray f N) N).getD i 0
      = ((PowerSeries.mk f) ^ 3).coeff i := by
  rw [convArrayUpTo_getD _ _ N i hi,
      convArrayCoeff_eq_coeff_mul _ (coeffArray f N) (fun j => ((PowerSeries.mk f) ^ 2).coeff j) f
        N i (fun j hj => convArrayUpTo_self_coeff f N j hj)
        (fun j hj => coeffArray_getD f N j hj) hi,
      mk_coeff_self, ← pow_succ]

lemma foldl_sigma_search_eq_sum (k m n : Nat) :
    List.foldl
      (fun acc i =>
        let d := i + 1
        if m % d = 0 then acc + (d : Int) ^ k else acc)
      0 (List.range n) =
    ∑ i ∈ Finset.range n, if m % (i + 1) = 0 then ((i + 1 : Nat) : Int) ^ k else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_concat, ih, Finset.sum_range_succ]
      by_cases h : m % (n + 1) = 0 <;> simp [h]

lemma sigmaPow_eq_sigma (k n : Nat) : sigmaPow k n = (ArithmeticFunction.sigma k n : Int) := by
  unfold sigmaPow
  rw [foldl_sigma_search_eq_sum, ArithmeticFunction.sigma_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h : (∑ i ∈ Finset.range n, if n % (i + 1) = 0 then ((i + 1 : Nat) : Int) ^ k else 0)
        = ∑ i ∈ Finset.range (n + 1), if i ∣ n then ((i : Nat) : Int) ^ k else 0 := by
      rw [Finset.sum_range_succ', if_neg fun h => hn (Nat.eq_zero_of_zero_dvd h), add_zero]
      exact Finset.sum_congr rfl fun i _ =>
        if_congr ⟨Nat.dvd_of_mod_eq_zero, Nat.mod_eq_zero_of_dvd⟩ rfl rfl
    rw [h, ← Finset.sum_filter, Nat.filter_dvd_eq_divisors hn]
    norm_cast

lemma e4CoeffInt_eq_integralE4_coeff (n : Nat) : e4CoeffInt n = integralE4.coeff n := by
  unfold e4CoeffInt
  by_cases hn : n = 0
  · subst hn
    simp [integralE4_coeff_zero]
  · have hn1 : n ≥ 1 := by omega
    rw [if_neg hn, integralE4_coeff_of_pos n hn1, sigmaPow_eq_sigma]

lemma e6CoeffInt_eq_integralE6_coeff (n : Nat) : e6CoeffInt n = integralE6.coeff n := by
  unfold e6CoeffInt
  by_cases hn : n = 0
  · subst hn
    simp [integralE6_coeff_zero]
  · have hn1 : n ≥ 1 := by omega
    rw [if_neg hn, integralE6_coeff_of_pos n hn1, sigmaPow_eq_sigma]
    ring

lemma E4_int_series_eq : PowerSeries.mk e4CoeffInt = integralE4 := by
  ext n
  rw [PowerSeries.coeff_mk, e4CoeffInt_eq_integralE4_coeff]

lemma E6_int_series_eq : PowerSeries.mk e6CoeffInt = integralE6 := by
  ext n
  rw [PowerSeries.coeff_mk, e6CoeffInt_eq_integralE6_coeff]

lemma E4_int_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk e4CoeffInt) = qExpansion 1 E4 := by
  rw [E4_int_series_eq]
  simpa [integralE4, coeToComplexPowerSeries.ringHom, powerSeriesMapAlgHom] using
    coeTo_of_toIntegralPowerSeries E4_isIntegralPowerSeries

lemma E6_int_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk e6CoeffInt) = qExpansion 1 E6 := by
  rw [E6_int_series_eq]
  simpa [integralE6, coeToComplexPowerSeries.ringHom, powerSeriesMapAlgHom] using
    coeTo_of_toIntegralPowerSeries E6_isIntegralPowerSeries

/-- For `z ≡ 0 [ZMOD 1728]`, the complex cast of the exact integer quotient `z / 1728`
is `(1 / 1728) · z`. -/
lemma int_cast_div_eq_inv_mul_complex {z : Int} (hz : Int.ModEq 1728 z 0) :
    ((z / 1728 : Int) : ℂ) = (1 / 1728 : ℂ) * (z : ℂ) := by
  rw [Int.cast_div_charZero (Int.modEq_zero_iff_dvd.1 hz)]
  push_cast
  ring

/-- Entry `k` of the `Δ`-coefficient table `deltaCoeffsArrayUpTo top` is the `k`-th
coefficient of the formal series `(E₄³ - E₆²) / 1728`, independently of the table size. -/
lemma deltaCoeffsArrayUpTo_getD (top k : Nat) (hk : k ≤ top) :
    (deltaCoeffsArrayUpTo top).getD k 0 =
      (((PowerSeries.mk e4CoeffInt) ^ 3 - (PowerSeries.mk e6CoeffInt) ^ 2).coeff k) / 1728 := by
  simp only [deltaCoeffsArrayUpTo]
  rw [foldl_push_getD _ (top + 1) k (by omega), convArrayUpTo_cube_coeff e4CoeffInt top k hk,
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
      (qExpansion 1 (⇑E4 ^ 3 - ⇑E6 ^ 2)).coeff n := by
  have h := congrArg (PowerSeries.coeff n) map_integralE4_pow_three_sub_integralE6_pow_two
  change (PowerSeries.map (Int.castRingHom ℂ) (integralE4 ^ 3 - integralE6 ^ 2)).coeff n = _ at h
  rw [PowerSeries.coeff_map] at h
  exact h

theorem Delta_qexpansion_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) Delta_qexpansion = qExpansion 1 Delta := by
  ext n
  change ((Delta_qexpansion.coeff n : ℤ) : ℂ) = (qExpansion 1 Delta).coeff n
  rw [Delta_qexpansion_coeff_eq, deltaCoeffInt_eq, E4_int_series_eq, E6_int_series_eq,
      Delta_qExpansion_eq_smul_eisenstein_difference]
  calc (((integralE4 ^ 3 - integralE6 ^ 2).coeff n / 1728 : Int) : ℂ)
      = (1 / 1728 : ℂ) * (((integralE4 ^ 3 - integralE6 ^ 2).coeff n : ℤ) : ℂ) :=
        int_cast_div_eq_inv_mul_complex (eisenstein_difference_coeff_modEq_zero n)
    _ = (1 / 1728 : ℂ) * (qExpansion 1 (⇑E4 ^ 3 - ⇑E6 ^ 2)).coeff n := by
        rw [eisenstein_difference_coeff_cast]

theorem Delta_qxp_coeff_link (n : ℕ) :
    (qExpansion 1 Delta).coeff n = Delta_qexpansion.coeff n :=
  (congrArg (PowerSeries.coeff n) Delta_qexpansion_link).symm

/-- Cast form of `Delta_qexpansion_link`: the array-computed integer `τ(n)`, viewed in `ℂ`,
is the `n`-th analytic `q`-expansion coefficient of `Δ`. -/
lemma deltaCoeffInt_cast (n : ℕ) :
    ((deltaCoeffInt n : ℤ) : ℂ) = (qExpansion 1 Delta).coeff n := by
  have h := congrArg (PowerSeries.coeff n) Delta_qexpansion_link
  change ((Delta_qexpansion.coeff n : ℤ) : ℂ) = _ at h
  rwa [Delta_qexpansion_coeff_eq] at h

theorem ramanujanTau_link (n : ℕ) : ramanujanTau n = Delta_qexpansion.coeff n := by
  unfold ramanujanTau
  have h1 : ((integralDelta.coeff n : ℤ) : ℂ) = (qExpansion 1 Delta).coeff n := by
    have h := congrArg (PowerSeries.coeff n)
      (coeTo_of_toIntegralPowerSeries Delta_isIntegralPowerSeries)
    change (PowerSeries.map (Int.castRingHom ℂ) integralDelta).coeff n = _ at h
    rw [PowerSeries.coeff_map] at h
    exact h
  rw [Delta_qexpansion_coeff_eq]
  exact_mod_cast h1.trans (deltaCoeffInt_cast n).symm

lemma deltaOverQ_qexpansion_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk deltaOverQCoeffInt) =
      qExpansion 1 deltaOverQ := by
  ext n
  change ((PowerSeries.mk deltaOverQCoeffInt).coeff n : ℂ) = (qExpansion 1 deltaOverQ).coeff n
  rw [PowerSeries.coeff_mk, deltaOverQCoeffInt]
  have hq : qExpansion 1 deltaOverQ = qExpansion 1 deltaShiftedQSeries := by
    simpa using qExpansion_ext deltaOverQ deltaShiftedQSeries
      (deltaShiftedQSeries_eq_deltaOverQ.symm)
  rw [hq]
  exact (deltaCoeffInt_cast (n + 1)).trans (deltaShiftedQSeries_qExpansion_coeff n).symm

lemma deltaOverQCoeffInt_zero : deltaOverQCoeffInt 0 = 1 := by
  have hcast : ((deltaOverQCoeffInt 0 : ℤ) : ℂ) = 1 := by
    simpa [deltaOverQCoeffInt, Delta_q_one_term] using deltaCoeffInt_cast 1
  exact_mod_cast hcast

/-- The coefficient recursion of `PowerSeries.invOfUnit φ 1` at a successor index, in the
`range`-sum form matching the loop of `inverseOnePlusCoeffsUpTo`. -/
lemma coeff_invOfUnit_one_succ {R : Type*} [Ring R] (φ : PowerSeries R) (m : Nat) :
    (φ.invOfUnit 1).coeff (m + 1) =
      -∑ i ∈ Finset.range (m + 1), φ.coeff (i + 1) * (φ.invOfUnit 1).coeff (m - i) := by
  rw [PowerSeries.coeff_invOfUnit, if_neg (Nat.succ_ne_zero m),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun x y => if y < m + 1 then φ.coeff x * (φ.invOfUnit 1).coeff y else 0) (m + 1),
      Finset.sum_range_succ']
  simp [Nat.succ_sub_succ_eq_sub]

lemma array_getD_eq_toList_getD (arr : Array Int) (i : Nat) :
    arr.getD i 0 = arr.toList.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, ← List.getElem?_toArray,
      Array.toArray_toList]

lemma getD_map_range (g : Nat → Int) (L j : Nat) (hj : j < L) :
    ((List.range L).map g).getD j 0 = g j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- Loop invariant for `inverseOnePlusCoeffsUpTo`: after `K` steps the accumulator array
tabulates the coefficients of `(PowerSeries.mk α).invOfUnit 1` on `0..K-1`, provided the
input array agrees with `α` up to index `N`. -/
lemma inverseOnePlusCoeffsUpTo_toList (a : Array Int) (α : Nat → Int) (N : Nat)
    (hα : ∀ j ≤ N, a.getD j 0 = α j) :
    ∀ K, K ≤ N + 1 →
      ((List.range K).foldl
        (fun acc k =>
          match k with
          | 0 => acc.push 1
          | m + 1 =>
              acc.push (-((List.range (m + 1)).foldl
                (fun s i => s + a.getD (i + 1) 0 * acc.getD (m - i) 0) 0)))
        (#[] : Array Int)).toList
        = (List.range K).map fun i => ((PowerSeries.mk α).invOfUnit 1).coeff i := by
  intro K
  induction K with
  | zero => intro _; simp
  | succ K ih =>
      intro hK
      rw [List.range_succ, List.foldl_concat]
      have hacc := ih (by omega)
      rcases K with _ | m
      · simp [PowerSeries.coeff_zero_eq_constantCoeff]
      · rw [Array.toList_push, hacc, List.map_append]
        congr 1
        simp only [List.map_cons, List.map_nil]
        congr 1
        rw [foldl_range_add_eq_sum, coeff_invOfUnit_one_succ]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        rw [hα (i + 1) (by omega), array_getD_eq_toList_getD, hacc,
            getD_map_range _ _ _ (by omega), PowerSeries.coeff_mk]

lemma inverseOnePlusCoeffsUpTo_getD (a : Array Int) (α : Nat → Int) (N : Nat)
    (hα : ∀ j ≤ N, a.getD j 0 = α j) (i : Nat) (hi : i ≤ N) :
    (inverseOnePlusCoeffsUpTo a N).getD i 0 = ((PowerSeries.mk α).invOfUnit 1).coeff i := by
  have h := inverseOnePlusCoeffsUpTo_toList a α N hα (N + 1) le_rfl
  rw [array_getD_eq_toList_getD, show (inverseOnePlusCoeffsUpTo a N).toList
      = (List.range (N + 1)).map fun i => ((PowerSeries.mk α).invOfUnit 1).coeff i from h]
  exact getD_map_range _ (N + 1) i (by omega)

/-- Entry `j` of the shifted table `deltaOverQArrayUpTo n` is `deltaOverQCoeffInt j`. -/
lemma deltaOverQArrayUpTo_getD (n j : Nat) (hj : j ≤ n) :
    (deltaOverQArrayUpTo n).getD j 0 = deltaOverQCoeffInt j := by
  simp only [deltaOverQArrayUpTo]
  rw [foldl_push_getD _ (n + 1) j (by omega), delta_array_getD (n + 1) (j + 1) (by omega)]
  rfl

/-- Entry `i` of `qoverDeltaCoeffsArrayUpTo n` is the `i`-th coefficient of the formal
inverse of `Δ/q`. -/
lemma qoverDelta_array_getD (n i : Nat) (hi : i ≤ n) :
    (qoverDeltaCoeffsArrayUpTo n).getD i 0 =
      ((PowerSeries.mk deltaOverQCoeffInt).invOfUnit 1).coeff i := by
  simp only [qoverDeltaCoeffsArrayUpTo]
  exact inverseOnePlusCoeffsUpTo_getD _ deltaOverQCoeffInt n
    (fun j hj => deltaOverQArrayUpTo_getD n j hj) i hi

/-- The array-based `qoverDeltaCoeffInt` computes the coefficients of the formal inverse
of the series `Δ/q`. -/
lemma qoverDeltaCoeffInt_eq (n : Nat) :
    qoverDeltaCoeffInt n = ((PowerSeries.mk deltaOverQCoeffInt).invOfUnit 1).coeff n :=
  qoverDelta_array_getD n n le_rfl

lemma qoverDeltaCoeffInt_zero : qoverDeltaCoeffInt 0 = 1 := by
  rw [qoverDeltaCoeffInt_eq]
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

lemma qoverDelta_mul_eq_one :
    (PowerSeries.mk deltaOverQCoeffInt) * (PowerSeries.mk qoverDeltaCoeffInt) = 1 := by
  have h : PowerSeries.mk qoverDeltaCoeffInt =
      (PowerSeries.mk deltaOverQCoeffInt).invOfUnit 1 := by
    ext n
    rw [PowerSeries.coeff_mk, qoverDeltaCoeffInt_eq]
  rw [h]
  exact PowerSeries.mul_invOfUnit _ 1 (by simp [deltaOverQCoeffInt_zero])

lemma qOverDelta_qexpansion_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk qoverDeltaCoeffInt) =
      qExpansion 1 qOverDelta := by
  let A : PowerSeries ℂ :=
    mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk deltaOverQCoeffInt)
  have hAunit : IsUnit A := by
    dsimp [A]
    rw [PowerSeries.isUnit_iff_constantCoeff]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    change IsUnit ((((PowerSeries.mk deltaOverQCoeffInt).coeff 0 : ℤ) : ℂ))
    simp [deltaOverQCoeffInt_zero]
  apply hAunit.mul_left_cancel
  dsimp [A]
  calc
    mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk deltaOverQCoeffInt) *
        mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk qoverDeltaCoeffInt)
        = mapAlgHom (Algebra.ofId ℤ ℂ)
            ((PowerSeries.mk deltaOverQCoeffInt) * (PowerSeries.mk qoverDeltaCoeffInt)) := by
          rw [map_mul]
    _ = 1 := by rw [qoverDelta_mul_eq_one, map_one]
    _ = mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk deltaOverQCoeffInt) *
        qExpansion 1 qOverDelta := by
          rw [deltaOverQ_qexpansion_link]
          have hprod : qExpansion 1 deltaOverQ * qExpansion 1 qOverDelta = 1 := by
            rw [← coeTo_integralDeltaOverQ]
            simpa [coeToComplexPowerSeries.ringHom, powerSeriesMapAlgHom] using
              integralDeltaOverQ_mul_qExpansion_qOverDelta
          exact hprod.symm

/-- The array-based `qjCoeffInt` agrees with the convolution `(mk e4CoeffInt)^3 * (q/Δ)`. -/
lemma qjCoeffInt_eq (n : Nat) :
    qjCoeffInt n =
      ((PowerSeries.mk e4CoeffInt) ^ 3 * PowerSeries.mk qoverDeltaCoeffInt).coeff n := by
  simp only [qjCoeffInt, qjCoeffsArrayUpTo]
  rw [convArrayUpTo_getD _ _ n n le_rfl,
      convArrayCoeff_eq_coeff_mul _ _ (fun j => ((PowerSeries.mk e4CoeffInt) ^ 3).coeff j)
        qoverDeltaCoeffInt n n ?hA ?hB le_rfl, mk_coeff_self]
  case hA =>
    intro j hj
    exact convArrayUpTo_cube_coeff e4CoeffInt (n + 1) j (by omega)
  case hB =>
    intro j hj
    rw [qoverDelta_array_getD n j hj, ← qoverDeltaCoeffInt_eq]

lemma qj_series_eq :
    PowerSeries.mk qjCoeffInt =
      (PowerSeries.mk e4CoeffInt) ^ 3 * PowerSeries.mk qoverDeltaCoeffInt := by
  ext n
  rw [PowerSeries.coeff_mk, qjCoeffInt_eq]

theorem qj_qexpansion_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) qj_qexpansion = qExpansion 1 qj := by
  rw [qj_qexpansion, qj_series_eq]
  have hpow : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow
      (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ)) (k := (4 : ℤ))
      (hh := by norm_num) (hΓ := by simp) E4 3
  calc
    mapAlgHom (Algebra.ofId ℤ ℂ)
        ((PowerSeries.mk e4CoeffInt) ^ 3 * PowerSeries.mk qoverDeltaCoeffInt)
        = (mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk e4CoeffInt)) ^ 3 *
            mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk qoverDeltaCoeffInt) := by
          simp [map_mul, map_pow]
    _ = (qExpansion 1 E4) ^ 3 * qExpansion 1 qOverDelta := by
          rw [E4_int_link, qOverDelta_qexpansion_link]
    _ = qExpansion 1 (E4 ^ 3) * qExpansion 1 qOverDelta := by
          rw [hpow]
    _ = qExpansion 1 (E4 ^ 3 * qOverDelta) := by
          rw [qExpansion_mul E4_pow_three_cuspFunction_analyticAt
            qOverDelta_cuspFunction_analyticAt]
    _ = qExpansion 1 qj := by
          rw [E4_pow_three_mul_qOverDelta_eq_qj]

theorem qj_qxp_coeff_link (n : ℕ) :
    (qExpansion 1 qj).coeff n = qj_qexpansion.coeff n :=
  (congrArg (PowerSeries.coeff n) qj_qexpansion_link).symm
