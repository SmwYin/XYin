import XYin.jFunction.jfunction
import XYin.qExpansion_tactic.Qj

open UpperHalfPlane PowerSeries ModularForm ModularFormClass
open XYin.qExpansion_tactic
open IntegralPowerSeries
open ArithmeticFunction

lemma foldl_range_add_eq_sum (f : Nat → Int) (n : Nat) :
    List.foldl (fun acc i => acc + f i) 0 (List.range n) = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_concat, ih, Finset.sum_range_succ]

lemma convCoeff_eq_coeff_mul (a b : Nat → Int) (n : Nat) :
    convCoeff a b n = ((PowerSeries.mk a) * (PowerSeries.mk b)).coeff n := by
  rw [convCoeff, foldl_range_add_eq_sum, PowerSeries.coeff_mul]
  calc
    (∑ i ∈ Finset.range (n + 1), a i * b (n - i))
        = ∑ i ∈ Finset.range (n + 1),
            (PowerSeries.mk a).coeff i * (PowerSeries.mk b).coeff (n - i) := by
          simp
    _ = ∑ p ∈ Finset.antidiagonal n,
          (PowerSeries.mk a).coeff p.1 * (PowerSeries.mk b).coeff p.2 := by
          exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => (PowerSeries.mk a).coeff i * (PowerSeries.mk b).coeff j) n).symm

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
  by_cases hn : n = 0
  · subst hn
    simp
  · calc
      (∑ i ∈ Finset.range n,
          if n % (i + 1) = 0 then ((i + 1 : Nat) : Int) ^ k else 0)
          = ∑ i ∈ (Finset.range n).filter (fun i => n % (i + 1) = 0),
              ((i + 1 : Nat) : Int) ^ k := by
            exact (Finset.sum_filter (s := Finset.range n)
              (p := fun i => n % (i + 1) = 0)
              (f := fun i => ((i + 1 : Nat) : Int) ^ k)).symm
      _ = ∑ d ∈ n.divisors, ((d : Nat) : Int) ^ k := by
            exact Finset.sum_bij
              (fun i _ => i + 1)
              (by
                intro i hi
                rw [Nat.mem_divisors]
                exact ⟨Nat.dvd_of_mod_eq_zero (Finset.mem_filter.mp hi).2, hn⟩)
              (by
                intro i _ j _ hij
                exact Nat.succ.inj hij)
              (by
                intro d hd
                rw [Nat.mem_divisors] at hd
                have hdvd : d ∣ n := hd.1
                have hposn : 0 < n := Nat.pos_of_ne_zero hn
                have hposd : 0 < d := Nat.pos_of_dvd_of_pos hdvd hposn
                refine ⟨d - 1, ?_, ?_⟩
                · rw [Finset.mem_filter]
                  constructor
                  · rw [Finset.mem_range]
                    have hle : d ≤ n := Nat.le_of_dvd hposn hdvd
                    omega
                  · have hsucc : d - 1 + 1 = d := by omega
                    simpa [hsucc] using Nat.mod_eq_zero_of_dvd hdvd
                · have hsucc : d - 1 + 1 = d := by omega
                  simp [hsucc])
              (by
                intro i _
                simp)
      _ = (↑(∑ d ∈ n.divisors, d ^ k) : Int) := by norm_cast

lemma e4CoeffInt_eq_integralE4_coeff (n : Nat) : e4CoeffInt n = integralE4.coeff n := by
  unfold e4CoeffInt
  by_cases hn : n = 0
  · subst hn
    simp [integralE4_coeff_zero]
  · have hn1 : n ≥ 1 := by omega
    rw [if_neg hn, integralE4_coeff_pos n hn1, sigmaPow_eq_sigma]

lemma e6CoeffInt_eq_integralE6_coeff (n : Nat) : e6CoeffInt n = integralE6.coeff n := by
  unfold e6CoeffInt
  by_cases hn : n = 0
  · subst hn
    simp [integralE6_coeff_zero]
  · have hn1 : n ≥ 1 := by omega
    rw [if_neg hn, integralE6_coeff_pos n hn1, sigmaPow_eq_sigma]
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
    coeTo_of_toIntegralPowerSeries E4IsIntegralPowerSeries

lemma E6_int_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk e6CoeffInt) = qExpansion 1 E6 := by
  rw [E6_int_series_eq]
  simpa [integralE6, coeToComplexPowerSeries.ringHom, powerSeriesMapAlgHom] using
    coeTo_of_toIntegralPowerSeries E6IsIntegralPowerSeries

lemma e4SqCoeffInt_eq (n : Nat) :
    e4SqCoeffInt n = ((PowerSeries.mk e4CoeffInt) ^ 2).coeff n := by
  rw [e4SqCoeffInt, convCoeff_eq_coeff_mul]
  ring_nf

lemma e4CubeCoeffInt_eq (n : Nat) :
    e4CubeCoeffInt n = ((PowerSeries.mk e4CoeffInt) ^ 3).coeff n := by
  rw [e4CubeCoeffInt, convCoeff_eq_coeff_mul]
  rw [show PowerSeries.mk e4SqCoeffInt = (PowerSeries.mk e4CoeffInt) ^ 2 by
    ext n
    rw [PowerSeries.coeff_mk, e4SqCoeffInt_eq]]
  ring_nf

lemma e6SqCoeffInt_eq (n : Nat) :
    e6SqCoeffInt n = ((PowerSeries.mk e6CoeffInt) ^ 2).coeff n := by
  rw [e6SqCoeffInt, convCoeff_eq_coeff_mul]
  ring_nf

lemma deltaCoeffInt_eq (n : Nat) :
    deltaCoeffInt n =
      (((PowerSeries.mk e4CoeffInt) ^ 3 - (PowerSeries.mk e6CoeffInt) ^ 2).coeff n) /
        1728 := by
  simp [deltaCoeffInt, e4CubeCoeffInt_eq, e6SqCoeffInt_eq]

lemma int_cast_div_eq_inv_mul_complex {z : Int} (hz : Int.ModEq 1728 z 0) :
    ((z / 1728 : Int) : ℂ) = (1 / 1728 : ℂ) * (z : ℂ) := by
  have hdvd : (1728 : Int) ∣ z := (Int.modEq_zero_iff_dvd).1 hz
  rcases hdvd with ⟨t, ht⟩
  have hdiv : z / 1728 = t := by
    exact Int.ediv_eq_of_eq_mul_right (by decide : (1728 : Int) ≠ 0) ht
  rw [hdiv, ht]
  change (t : ℂ) = (1 / 1728 : ℂ) * ((1728 * t : Int) : ℂ)
  norm_num
  ring

theorem Delta_qexpansion_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) Delta_qexpansion = qExpansion 1 Delta := by
  ext n
  change ((Delta_qexpansion.coeff n : ℤ) : ℂ) = (qExpansion 1 Delta).coeff n
  rw [Delta_qexpansion_coeff_eq, deltaCoeffInt_eq, Deltaaux]
  have hseries :
      ((PowerSeries.mk e4CoeffInt) ^ 3 - (PowerSeries.mk e6CoeffInt) ^ 2).coeff n =
        (integralE4 ^ 3 - integralE6 ^ 2).coeff n := by
    rw [E4_int_series_eq, E6_int_series_eq]
  rw [hseries]
  let z : Int := (integralE4 ^ 3 - integralE6 ^ 2).coeff n
  have hz : Int.ModEq 1728 z 0 := by
    dsimp [z]
    rw [← aux1']
    exact mod1728' n
  have hcoeff :
      ((z : Int) : ℂ) = (qExpansion 1 (⇑E4 ^ 3 - ⇑E6 ^ 2)).coeff n := by
    have h := congrArg (PowerSeries.coeff n) aux1
    have hleft :
        ((coeToComplexPowerSeries.ringHom ℤ) (integralE4 ^ 3 - integralE6 ^ 2)).coeff n =
          (z : ℂ) := by
      change (PowerSeries.map (Int.castRingHom ℂ) (integralE4 ^ 3 - integralE6 ^ 2)).coeff n =
        (z : ℂ)
      rw [PowerSeries.coeff_map]
      rfl
    exact hleft.symm.trans h
  calc
    (((z : Int) / 1728 : Int) : ℂ) = (1 / 1728 : ℂ) * (z : ℂ) :=
      int_cast_div_eq_inv_mul_complex hz
    _ = (1 / 1728 : ℂ) * (qExpansion 1 (⇑E4 ^ 3 - ⇑E6 ^ 2)).coeff n := by
      rw [hcoeff]

theorem Delta_qxp_coeff_link (n : ℕ) :
    (qExpansion 1 Delta).coeff n = Delta_qexpansion.coeff n := by
  exact (congrArg (PowerSeries.coeff n) Delta_qexpansion_link).symm

lemma Deltaoverq_qexpansion_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk deltaOverQCoeffInt) =
      qExpansion 1 Deltaoverq := by
  ext n
  change ((PowerSeries.mk deltaOverQCoeffInt).coeff n : ℂ) =
    (qExpansion 1 Deltaoverq).coeff n
  rw [PowerSeries.coeff_mk, deltaOverQCoeffInt]
  have hDelta := congrArg (PowerSeries.coeff (n + 1)) Delta_qexpansion_link
  have hDeltaCoeff : ((deltaCoeffInt (n + 1) : ℤ) : ℂ) =
      (qExpansion 1 Delta).coeff (n + 1) := by
    have hleft :
        ((mapAlgHom (Algebra.ofId ℤ ℂ)) Delta_qexpansion).coeff (n + 1) =
          ((deltaCoeffInt (n + 1) : ℤ) : ℂ) := by
      change ((Delta_qexpansion.coeff (n + 1) : ℤ) : ℂ) =
        ((deltaCoeffInt (n + 1) : ℤ) : ℂ)
      rw [Delta_qexpansion_coeff_eq]
    exact hleft.symm.trans hDelta
  have hq : qExpansion 1 Deltaoverq = qExpansion 1 InfSumDeltashift := by
    simpa using qExpansion_ext Deltaoverq InfSumDeltashift
      (InfSumDeltashift_eq_Deltaoverq.symm)
  rw [hq]
  exact hDeltaCoeff.trans (InfSumDeltashift_coeff_eq n).symm

lemma deltaOverQCoeffInt_zero : deltaOverQCoeffInt 0 = 1 := by
  have hDelta := congrArg (PowerSeries.coeff 1) Delta_qexpansion_link
  have hcoeff : ((deltaCoeffInt 1 : ℤ) : ℂ) = (qExpansion 1 Delta).coeff 1 := by
    have hleft :
        ((mapAlgHom (Algebra.ofId ℤ ℂ)) Delta_qexpansion).coeff 1 =
          ((deltaCoeffInt 1 : ℤ) : ℂ) := by
      change ((Delta_qexpansion.coeff 1 : ℤ) : ℂ) = ((deltaCoeffInt 1 : ℤ) : ℂ)
      rw [Delta_qexpansion_coeff_eq]
    exact hleft.symm.trans hDelta
  have hcast : ((deltaOverQCoeffInt 0 : ℤ) : ℂ) = 1 := by
    simpa [deltaOverQCoeffInt, Delta_q_one_term] using hcoeff
  norm_num at hcast ⊢
  exact_mod_cast hcast

lemma qoverDelta_coeff_succ (n : Nat) :
    qoverDeltaCoeffInt (n + 1) =
      -∑ i ∈ Finset.range (n + 1),
        deltaOverQCoeffInt (i + 1) * qoverDeltaCoeffInt (n - i) := by
  simp [qoverDeltaCoeffInt, foldl_range_add_eq_sum]

lemma qoverDelta_mul_eq_one :
    (PowerSeries.mk deltaOverQCoeffInt) * (PowerSeries.mk qoverDeltaCoeffInt) = 1 := by
  ext n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_mul]
      simp [deltaOverQCoeffInt_zero, qoverDeltaCoeffInt]
  | succ n =>
      rw [PowerSeries.coeff_mul]
      simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte]
      calc
        (∑ p ∈ Finset.antidiagonal (n + 1),
            deltaOverQCoeffInt p.1 * qoverDeltaCoeffInt p.2)
            = ∑ i ∈ Finset.range (n + 2),
                deltaOverQCoeffInt i * qoverDeltaCoeffInt (n + 1 - i) := by
              exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i j => deltaOverQCoeffInt i * qoverDeltaCoeffInt j) (n + 1)
        _ = 0 := by
              rw [Finset.sum_range_succ']
              simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
              rw [deltaOverQCoeffInt_zero, one_mul]
              rw [qoverDelta_coeff_succ]
              ring

lemma qoverDelta_qexpansion_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk qoverDeltaCoeffInt) =
      qExpansion 1 qoverDelta := by
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
        qExpansion 1 qoverDelta := by
          rw [Deltaoverq_qexpansion_link]
          have hprod : qExpansion 1 Deltaoverq * qExpansion 1 qoverDelta = 1 := by
            rw [← coeTo_of_integralDeltaoverq]
            simpa [coeToComplexPowerSeries.ringHom, powerSeriesMapAlgHom] using
              integralDeltaoverq_mul_qoverDelta_qExpansion
          exact hprod.symm

lemma e4Cube_series_eq :
    PowerSeries.mk e4CubeCoeffInt = (PowerSeries.mk e4CoeffInt) ^ 3 := by
  ext n
  rw [PowerSeries.coeff_mk, e4CubeCoeffInt_eq]

lemma qj_series_eq :
    PowerSeries.mk qjCoeffInt =
      PowerSeries.mk e4CubeCoeffInt * PowerSeries.mk qoverDeltaCoeffInt := by
  ext n
  rw [PowerSeries.coeff_mk, qjCoeffInt, convCoeff_eq_coeff_mul]

theorem qj_qexpansion_link :
    mapAlgHom (Algebra.ofId ℤ ℂ) qj_qexpansion = qExpansion 1 qj := by
  rw [qj_qexpansion, qj_series_eq, e4Cube_series_eq]
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
    _ = (qExpansion 1 E4) ^ 3 * qExpansion 1 qoverDelta := by
          rw [E4_int_link, qoverDelta_qexpansion_link]
    _ = qExpansion 1 (E4 ^ 3) * qExpansion 1 qoverDelta := by
          rw [hpow]
    _ = qExpansion 1 (E4 ^ 3 * qoverDelta) := by
          rw [qExpansion_mul E4cubed_AnalyticAt qoverDelta_AnalyticAt]
    _ = qExpansion 1 qj := by
          rw [qjIdentity]

theorem qj_qxp_coeff_link (n : ℕ) :
    (qExpansion 1 qj).coeff n = qj_qexpansion.coeff n := by
  exact (congrArg (PowerSeries.coeff n) qj_qexpansion_link).symm
