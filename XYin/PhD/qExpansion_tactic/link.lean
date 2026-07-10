import XYin.PhD.jFunction.jfunction
import XYin.PhD.qExpansion_tactic.Qj

set_option linter.style.header false

open UpperHalfPlane PowerSeries ModularForm ModularFormClass
open XYin.PhD.qExpansion_tactic
open IntegralPowerSeries
open ArithmeticFunction

/-! ## Array bridging toolkit

The computational definitions in `Qj` build coefficient arrays via `Array.foldl`/`push`
for speed.  The lemmas below relate those array operations back to the `PowerSeries`
coefficients we need for the modular-form identities. -/

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

/-! ## Connecting the integer coefficients to the integral q-expansions -/

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

/-- The array-based `deltaCoeffInt` agrees with the convolution definition of the
δ-coefficients. -/
lemma deltaCoeffInt_eq (n : Nat) :
    deltaCoeffInt n =
      (((PowerSeries.mk e4CoeffInt) ^ 3 - (PowerSeries.mk e6CoeffInt) ^ 2).coeff n) / 1728 := by
  simp only [deltaCoeffInt, deltaCoeffsArrayUpTo]
  rw [foldl_push_getD _ (n + 1) n (by omega),
      convArrayUpTo_cube_coeff e4CoeffInt n n le_rfl,
      convArrayUpTo_self_coeff e6CoeffInt n n le_rfl, map_sub]

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

theorem Ramanujan_tau_link (n : ℕ) : Ramanujan_tau n = Delta_qexpansion.coeff n := by
  unfold Ramanujan_tau
  have h1 : ((IntegralDelta.coeff n : ℤ) : ℂ) = (qExpansion 1 Delta).coeff n := by
    have h := congrArg (PowerSeries.coeff n)
      (coeTo_of_toIntegralPowerSeries DeltaIsIntegralPowerSeries)
    change (PowerSeries.map (Int.castRingHom ℂ) IntegralDelta).coeff n = _ at h
    rw [PowerSeries.coeff_map] at h
    exact h
  have h2 : ((Delta_qexpansion.coeff n : ℤ) : ℂ) = (qExpansion 1 Delta).coeff n := by
    have h := congrArg (PowerSeries.coeff n) Delta_qexpansion_link
    change ((Delta_qexpansion.coeff n : ℤ) : ℂ) = _ at h
    exact h
  exact_mod_cast h1.trans h2.symm

/-! ## The `q/Δ` inverse series -/

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

/-- Abstract coefficients of the inverse of `1 + ∑ α(k+1) q^{k+1}`. -/
def invFn (α : Nat → Int) : Nat → Int
  | 0 => 1
  | m + 1 => -∑ i ∈ Finset.range (m + 1), α (i + 1) * invFn α (m - i)
  termination_by n => n
  decreasing_by omega

lemma invFn_succ (α : Nat → Int) (m : Nat) :
    invFn α (m + 1) = -∑ i ∈ Finset.range (m + 1), α (i + 1) * invFn α (m - i) := by
  rw [invFn]

lemma array_getD_eq_toList_getD (arr : Array Int) (i : Nat) :
    arr.getD i 0 = arr.toList.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, ← List.getElem?_toArray,
      Array.toArray_toList]

lemma getD_map_range (g : Nat → Int) (L j : Nat) (hj : j < L) :
    ((List.range L).map g).getD j 0 = g j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- The inverse-coefficient array (built by `inverseOnePlusCoeffsUpTo`) reads off the
abstract inverse coefficients `invFn α`, provided the input array agrees with `α`. -/
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
        (#[] : Array Int)).toList = (List.range K).map (invFn α) := by
  intro K
  induction K with
  | zero => intro _; simp
  | succ K ih =>
      intro hK
      rw [List.range_succ, List.foldl_concat]
      have hacc := ih (by omega)
      rcases K with _ | m
      · simp [invFn]
      · -- pushed index is m+1; identify the pushed value with `invFn α (m+1)`
        rw [Array.toList_push, hacc, List.map_append]
        congr 1
        simp only [List.map_cons, List.map_nil]
        congr 1
        rw [foldl_range_add_eq_sum, invFn_succ]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        rw [hα (i + 1) (by omega), array_getD_eq_toList_getD, hacc, getD_map_range _ _ _ (by omega)]

lemma inverseOnePlusCoeffsUpTo_getD (a : Array Int) (α : Nat → Int) (N : Nat)
    (hα : ∀ j ≤ N, a.getD j 0 = α j) (i : Nat) (hi : i ≤ N) :
    (inverseOnePlusCoeffsUpTo a N).getD i 0 = invFn α i := by
  have h := inverseOnePlusCoeffsUpTo_toList a α N hα (N + 1) le_rfl
  rw [array_getD_eq_toList_getD,
      show (inverseOnePlusCoeffsUpTo a N).toList = (List.range (N + 1)).map (invFn α) from h]
  exact getD_map_range (invFn α) (N + 1) i (by omega)

/-- An entry of the `delta` array (as built inside the `q/Δ` and `qj` array routines,
with size parameter `top`) equals `deltaCoeffInt`. -/
lemma delta_array_getD (top k : Nat) (hk : k ≤ top) :
    ((List.range (top + 1)).foldl
      (fun acc i => acc.push
        (((convArrayUpTo
              (convArrayUpTo (coeffArray e4CoeffInt top) (coeffArray e4CoeffInt top) top)
              (coeffArray e4CoeffInt top) top).getD i 0
          - (convArrayUpTo (coeffArray e6CoeffInt top) (coeffArray e6CoeffInt top) top).getD i 0)
          / 1728))
      (#[] : Array Int)).getD k 0 = deltaCoeffInt k := by
  rw [foldl_push_getD _ (top + 1) k (by omega),
      convArrayUpTo_cube_coeff e4CoeffInt top k hk,
      convArrayUpTo_self_coeff e6CoeffInt top k hk, ← map_sub, ← deltaCoeffInt_eq]

/-- The array-based `qoverDeltaCoeffInt` agrees with the abstract inverse recursion. -/
lemma qoverDeltaCoeffInt_eq (n : Nat) :
    qoverDeltaCoeffInt n = invFn deltaOverQCoeffInt n := by
  simp only [qoverDeltaCoeffInt, qoverDeltaCoeffsArrayUpTo]
  rw [inverseOnePlusCoeffsUpTo_getD _ deltaOverQCoeffInt n ?hα n le_rfl]
  case hα =>
    intro j hj
    rw [foldl_push_getD _ (n + 1) j (by omega), delta_array_getD (n + 1) (j + 1) (by omega)]
    rfl

lemma qoverDeltaCoeffInt_zero : qoverDeltaCoeffInt 0 = 1 := by
  rw [qoverDeltaCoeffInt_eq, invFn]

lemma qoverDelta_coeff_succ (n : Nat) :
    qoverDeltaCoeffInt (n + 1) =
      -∑ i ∈ Finset.range (n + 1),
        deltaOverQCoeffInt (i + 1) * qoverDeltaCoeffInt (n - i) := by
  rw [qoverDeltaCoeffInt_eq, invFn_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [qoverDeltaCoeffInt_eq]

lemma qoverDelta_mul_eq_one :
    (PowerSeries.mk deltaOverQCoeffInt) * (PowerSeries.mk qoverDeltaCoeffInt) = 1 := by
  ext n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_mul]
      simp [deltaOverQCoeffInt_zero, qoverDeltaCoeffInt_zero]
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
    rw [inverseOnePlusCoeffsUpTo_getD _ deltaOverQCoeffInt n ?hα j (by omega),
        ← qoverDeltaCoeffInt_eq]
    intro j' hj'
    rw [foldl_push_getD _ (n + 1) j' (by omega), delta_array_getD (n + 1) (j' + 1) (by omega)]
    rfl

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
