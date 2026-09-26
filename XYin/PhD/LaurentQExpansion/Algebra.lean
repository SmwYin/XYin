/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.LaurentQExpansion.LaurentQExpansion
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Algebra of Laurent q-expansions

This file proves that the analytic Laurent q-expansion respects the ring operations on
cusp-meromorphic functions. It also compares the expansions obtained from a period `h` with
those obtained from the enlarged period `m * h`.

## Main results

* `laurentqExpansion_add`, `laurentqExpansion_mul`: the Laurent q-expansion respects pointwise
  addition and multiplication of cusp-meromorphic functions; together with
  `laurentqExpansion_zero`, `_one`, `_const`, `_const_mul`, `_smul`, `_neg`, `_sub`, `_pow`,
  `_finset_sum` and `_finset_prod` it behaves like a ring homomorphism.
* `laurentqExpansion_polynomial_eval`: the Laurent q-expansion of `τ ↦ P.eval (f τ)` is
  `P.eval₂ HahnSeries.C (laurentqExpansion h f)`.
* `to_qExpansion_nat_mul`, `laurentqExpansion_nat_mul`: enlarging the period from `h` to `m * h`
  substitutes `q ↦ q ^ m` in the expansion, i.e. extends the domain of the Laurent series along
  `k ↦ m * k` (`HahnSeries.embDomain`); `laurentqExpansion_nat_mul_coeff` and
  `laurentqExpansion_nat_mul_coeff_of_not_dvd` are its coefficientwise forms.
-/

open Complex Function Filter LaurentSeries ModularForm Set UpperHalfPlane
open scoped Topology

noncomputable section

local notation "𝕢" => Periodic.qParam

/-! ### Multiplication by powers of `𝕢` -/

/-- Multiplying by `𝕢 h τ ^ n` preserves analyticity of the cusp function at `0`. -/
lemma analyticAt_cuspFunction_qpow_mul {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) :
    AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ)) 0 :=
  analyticAt_cuspFunction_of_eventuallyEq ((analyticAt_id.pow n).mul hf)
    (cuspFunction_qpow_mul_eventuallyEq hh f n)

/-- The cusp function of `τ ↦ 𝕢 h τ ^ n` is analytic at `0`. -/
lemma analyticAt_cuspFunction_qParam_pow {h : ℝ} (hh : 0 < h) (n : ℕ) :
    AnalyticAt ℂ (cuspFunction h (fun τ : ℍ ↦ (𝕢 h τ) ^ n)) 0 := by
  simpa using analyticAt_cuspFunction_qpow_mul hh (analyticAt_cuspFunction_const h 1) n

/-- The q-expansion of `τ ↦ 𝕢 h τ ^ n` is the monomial `X ^ n`. -/
lemma qExpansion_qParam_pow {h : ℝ} (hh : 0 < h) (n : ℕ) :
    qExpansion h (fun τ : ℍ ↦ (𝕢 h τ) ^ n) = (PowerSeries.X : PowerSeries ℂ) ^ n := by
  have hEq : cuspFunction h (fun τ : ℍ ↦ (𝕢 h τ) ^ n) =ᶠ[𝓝[≠] 0] fun q : ℂ ↦ q ^ n := by
    simpa [cuspFunction_const] using cuspFunction_qpow_mul_eventuallyEq hh (fun _ ↦ (1 : ℂ)) n
  ext k
  rw [qExpansion_coeff, (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hEq (cuspFunction_apply_zero_eq
    hEq (continuous_pow n).continuousAt)).iteratedDeriv_eq k, iteratedDeriv_fun_pow_zero]
  rcases eq_or_ne k n with rfl | hk
  · simp [Nat.factorial_ne_zero]
  · simp [PowerSeries.coeff_X_pow, hk]

/-- Multiplying by `𝕢 h τ ^ n` on functions is multiplying by `X ^ n` on q-expansions. -/
lemma qExpansion_qpow_mul {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) :
    qExpansion h (fun τ ↦ (𝕢 h τ) ^ n * f τ) =
      (PowerSeries.X : PowerSeries ℂ) ^ n * qExpansion h f := by
  rw [← qExpansion_qParam_pow hh n, ← qExpansion_mul (analyticAt_cuspFunction_qParam_pow hh n) hf]
  rfl

/-- The Laurent q-expansion of `τ ↦ 𝕢 h τ ^ n` is the monomial `q ^ n`. -/
lemma laurentqExpansion_qParam_pow {h : ℝ} (hh : 0 < h) (n : ℕ) :
    laurentqExpansion h (fun τ : ℍ ↦ (𝕢 h τ) ^ n) = HahnSeries.single (n : ℤ) 1 := by
  rw [laurentqExpansion.eq_qExpansion_of_analyticAt (analyticAt_cuspFunction_qParam_pow hh n),
    qExpansion_qParam_pow hh n, HahnSeries.ofPowerSeries_X_pow]

/-! ### The shifted presentation -/

/-- The "shift by `N`" presentation of a Laurent expansion:
`q ^ (-N)` times the power series of `𝕢 h τ ^ N * f τ`. For any `N` at least the pole order
this recovers the Laurent q-expansion (`laurentqExpansion_eq_shiftedLaurent`), so sums and
products can be computed with one common denominator exponent. -/
private def shiftedLaurent (h : ℝ) (N : ℕ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-(N : ℤ)) 1 *
    (HahnSeries.ofPowerSeries ℤ ℂ)
      (qExpansion h (fun τ ↦ (𝕢 h τ) ^ N * f τ))

/-- For `N` at least the pole order, `𝕢 h τ ^ N * f τ` factors through the pole-removed
function. -/
private lemma qpow_mul_eq_qpow_sub_mul_poleRemoved {h : ℝ} {f : ℍ → ℂ} {N : ℕ}
    (hN : poleOrder h f ≤ N) :
    (fun τ : ℍ ↦ (𝕢 h τ) ^ N * f τ) =
      fun τ : ℍ ↦ (𝕢 h τ) ^ (N - poleOrder h f) * poleRemoved h f τ := by
  funext τ
  rw [poleRemoved_apply, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hN]

/-- The Laurent q-expansion is independent of the chosen denominator exponent: any
`N ≥ poleOrder h f` gives the same series via the shifted presentation. -/
private lemma laurentqExpansion_eq_shiftedLaurent
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) {N : ℕ}
    (hN : poleOrder h f ≤ N) :
    laurentqExpansion h f = shiftedLaurent h N f := by
  have hq : qExpansion h (fun τ : ℍ ↦ (𝕢 h τ) ^ N * f τ) =
      (PowerSeries.X : PowerSeries ℂ) ^ (N - poleOrder h f) * to_qExpansion h f := by
    rw [qpow_mul_eq_qpow_sub_mul_poleRemoved hN,
      qExpansion_qpow_mul hh (analyticAt_cuspFunction_poleRemoved hf) (N - poleOrder h f)]
    rfl
  rw [UpperHalfPlane.laurentqExpansion, shiftedLaurent, hq, map_mul,
    HahnSeries.ofPowerSeries_X_pow, ← mul_assoc, HahnSeries.single_mul_single, one_mul,
    show -(N : ℤ) + ((N - poleOrder h f : ℕ) : ℤ) = -(poleOrder h f : ℤ) by omega]

private lemma analyticAt_cuspFunction_qpow_of_poleOrder_le
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) {N : ℕ}
    (hN : poleOrder h f ≤ N) :
    AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ N * f τ)) 0 := by
  rw [qpow_mul_eq_qpow_sub_mul_poleRemoved hN]
  exact analyticAt_cuspFunction_qpow_mul hh (analyticAt_cuspFunction_poleRemoved hf) _

/-- The shifted presentation is additive at a common shift `N`. -/
private lemma shiftedLaurent_add {h : ℝ} {f g : ℍ → ℂ} {N : ℕ}
    (hfN : AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ N * f τ)) 0)
    (hgN : AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ N * g τ)) 0) :
    shiftedLaurent h N (fun τ ↦ f τ + g τ) =
      shiftedLaurent h N f + shiftedLaurent h N g := by
  have hfun : (fun τ : ℍ ↦ (𝕢 h τ) ^ N * (f τ + g τ)) =
      (fun τ : ℍ ↦ (𝕢 h τ) ^ N * f τ) + fun τ : ℍ ↦ (𝕢 h τ) ^ N * g τ := by
    funext τ
    exact mul_add _ _ _
  simp only [shiftedLaurent]
  rw [hfun, qExpansion_add hfN hgN, map_add, mul_add]

/-- The shifted presentation is multiplicative, with the shifts adding up. -/
private lemma shiftedLaurent_mul {h : ℝ} {f g : ℍ → ℂ} {A B : ℕ}
    (hfA : AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ A * f τ)) 0)
    (hgB : AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ B * g τ)) 0) :
    shiftedLaurent h (A + B) (fun τ ↦ f τ * g τ) =
      shiftedLaurent h A f * shiftedLaurent h B g := by
  have hfun : (fun τ : ℍ ↦ (𝕢 h τ) ^ (A + B) * (f τ * g τ)) =
      (fun τ : ℍ ↦ (𝕢 h τ) ^ A * f τ) * fun τ : ℍ ↦ (𝕢 h τ) ^ B * g τ := by
    funext τ
    exact (congrArg (· * (f τ * g τ)) (pow_add (𝕢 h τ) A B)).trans
      (mul_mul_mul_comm _ _ _ _)
  simp only [shiftedLaurent]
  rw [hfun, qExpansion_mul hfA hgB, map_mul, mul_mul_mul_comm,
    HahnSeries.single_mul_single, one_mul,
    show -((A + B : ℕ) : ℤ) = -(A : ℤ) + -(B : ℤ) by omega]

/-! ### Ring operations -/

/-- Laurent q-expansion respects pointwise addition of cusp-meromorphic functions. -/
lemma laurentqExpansion_add
    {h : ℝ} (hh : 0 < h) {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentqExpansion h (fun τ ↦ f τ + g τ) =
      laurentqExpansion h f + laurentqExpansion h g := by
  -- rewrite all three expansions with a common shift dominating all three pole orders
  set N := poleOrder h f + poleOrder h g + poleOrder h (fun τ ↦ f τ + g τ)
  rw [laurentqExpansion_eq_shiftedLaurent hh (meromorphicAt_cuspFunction_add hf hg)
      (N := N) (by omega),
    laurentqExpansion_eq_shiftedLaurent hh hf (N := N) (by omega),
    laurentqExpansion_eq_shiftedLaurent hh hg (N := N) (by omega)]
  exact shiftedLaurent_add
    (analyticAt_cuspFunction_qpow_of_poleOrder_le hh hf (by omega))
    (analyticAt_cuspFunction_qpow_of_poleOrder_le hh hg (by omega))

/-- Laurent q-expansion respects pointwise multiplication of cusp-meromorphic functions. -/
lemma laurentqExpansion_mul
    {h : ℝ} (hh : 0 < h) {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentqExpansion h (fun τ ↦ f τ * g τ) =
      laurentqExpansion h f * laurentqExpansion h g := by
  -- split the total shift as `A + B` so that `A + B` also dominates the product's pole order
  set A := poleOrder h f + poleOrder h (fun τ ↦ f τ * g τ)
  set B := poleOrder h g
  rw [laurentqExpansion_eq_shiftedLaurent hh (meromorphicAt_cuspFunction_mul hf hg)
      (N := A + B) (by omega),
    laurentqExpansion_eq_shiftedLaurent hh hf (N := A) (by omega),
    laurentqExpansion_eq_shiftedLaurent hh hg (N := B) (by omega)]
  exact shiftedLaurent_mul
    (analyticAt_cuspFunction_qpow_of_poleOrder_le hh hf (by omega))
    (analyticAt_cuspFunction_qpow_of_poleOrder_le hh hg (by omega))

/-- The Laurent q-expansion of a constant function is the corresponding constant series. -/
@[simp] lemma laurentqExpansion_const (h : ℝ) (a : ℂ) :
    laurentqExpansion h (fun _ : ℍ ↦ a) = HahnSeries.C a := by
  rw [laurentqExpansion.eq_qExpansion_of_analyticAt (analyticAt_cuspFunction_const h a),
    qExpansion_const, HahnSeries.ofPowerSeries_C]

/-- The Laurent q-expansion of the zero function is zero. -/
@[simp] lemma laurentqExpansion_zero (h : ℝ) :
    laurentqExpansion h (0 : ℍ → ℂ) = 0 := by
  rw [Pi.zero_def, laurentqExpansion_const, map_zero]

/-- The Laurent q-expansion of the constant-one function is one. -/
@[simp] lemma laurentqExpansion_one (h : ℝ) :
    laurentqExpansion h (1 : ℍ → ℂ) = 1 := by
  rw [Pi.one_def, laurentqExpansion_const, map_one]

/-- Laurent q-expansion commutes with multiplication by a constant. -/
lemma laurentqExpansion_const_mul {h : ℝ} (hh : 0 < h) (a : ℂ) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    laurentqExpansion h (fun τ ↦ a * f τ) = HahnSeries.C a * laurentqExpansion h f := by
  rw [laurentqExpansion_mul hh (meromorphicAt_cuspFunction_const h a) hf,
    laurentqExpansion_const]

/-- Laurent q-expansion commutes with scalar multiplication. -/
lemma laurentqExpansion_smul {h : ℝ} (hh : 0 < h) (a : ℂ) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    laurentqExpansion h (a • f) = a • laurentqExpansion h f := by
  rw [← HahnSeries.C_mul_eq_smul]
  exact laurentqExpansion_const_mul hh a hf

/-- Laurent q-expansion respects pointwise negation. -/
lemma laurentqExpansion_neg
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    laurentqExpansion h (fun τ ↦ -f τ) = -laurentqExpansion h f := by
  simpa using laurentqExpansion_const_mul hh (-1) hf

/-- Laurent q-expansion respects pointwise subtraction. -/
lemma laurentqExpansion_sub {h : ℝ} (hh : 0 < h) {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentqExpansion h (fun τ ↦ f τ - g τ) =
      laurentqExpansion h f - laurentqExpansion h g := by
  simpa only [sub_eq_add_neg, laurentqExpansion_neg hh hg] using
    laurentqExpansion_add hh hf (meromorphicAt_cuspFunction_neg hg)

/-- Laurent q-expansion respects pointwise powers. -/
lemma laurentqExpansion_pow {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) (n : ℕ) :
    laurentqExpansion h (fun τ ↦ f τ ^ n) = laurentqExpansion h f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa only [pow_succ, ih] using
        laurentqExpansion_mul hh (meromorphicAt_cuspFunction_pow hf n) hf

/-- A map which is multiplicative on a multiplicatively closed predicate commutes with finite
products of elements satisfying the predicate. -/
@[to_additive /-- A map which is additive on an additively closed predicate commutes with finite
sums of elements satisfying the predicate. -/]
private theorem map_finset_prod_of_mul {ι M N : Type*} [CommMonoid M] [CommMonoid N]
    {p : M → Prop} {L : M → N} (hp_one : p 1) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (hL_one : L 1 = 1) (hL_mul : ∀ a b, p a → p b → L (a * b) = L a * L b)
    (s : Finset ι) {f : ι → M} (hf : ∀ i ∈ s, p (f i)) :
    L (∏ i ∈ s, f i) = ∏ i ∈ s, L (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hL_one
  | insert a s ha ih =>
      have hs : ∀ i ∈ s, p (f i) := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        hL_mul _ _ (hf a (Finset.mem_insert_self a s)) (Finset.prod_induction _ p hp_mul hp_one hs),
        ih hs]

/-- Laurent q-expansion commutes with a finite pointwise sum. -/
lemma laurentqExpansion_finset_sum
    {h : ℝ} (hh : 0 < h) {I : Type*} (s : Finset I) {f : I → ℍ → ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) :
    laurentqExpansion h (∑ i ∈ s, f i) =
      ∑ i ∈ s, laurentqExpansion h (f i) :=
  map_finset_sum_of_add (p := fun F ↦ MeromorphicAt (cuspFunction h F) 0)
    (meromorphicAt_cuspFunction_const h 0) (fun _ _ ↦ meromorphicAt_cuspFunction_add)
    (laurentqExpansion_zero h) (fun _ _ ↦ laurentqExpansion_add hh) s hf

/-- Laurent q-expansion commutes with a finite pointwise product. -/
lemma laurentqExpansion_finset_prod
    {h : ℝ} (hh : 0 < h) {I : Type*} (s : Finset I) {f : I → ℍ → ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) :
    laurentqExpansion h (∏ i ∈ s, f i) =
      ∏ i ∈ s, laurentqExpansion h (f i) :=
  map_finset_prod_of_mul (p := fun F ↦ MeromorphicAt (cuspFunction h F) 0)
    (meromorphicAt_cuspFunction_const h 1) (fun _ _ ↦ meromorphicAt_cuspFunction_mul)
    (laurentqExpansion_one h) (fun _ _ ↦ laurentqExpansion_mul hh) s hf

/-- Laurent q-expansion commutes with evaluating a polynomial: the Laurent q-expansion of
`τ ↦ P.eval (f τ)` is `P` evaluated at the Laurent q-expansion of `f`. -/
theorem laurentqExpansion_polynomial_eval {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) (P : Polynomial ℂ) :
    laurentqExpansion h (fun τ ↦ P.eval (f τ)) =
      P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion h f) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [Polynomial.eval_add, Polynomial.eval₂_add, hP, hQ] using
        laurentqExpansion_add hh (meromorphicAt_cuspFunction_polynomial_eval hf P)
          (meromorphicAt_cuspFunction_polynomial_eval hf Q)
  | monomial n a =>
      simpa only [Polynomial.eval_monomial, Polynomial.eval₂_monomial,
        laurentqExpansion_pow hh hf] using
        laurentqExpansion_const_mul hh a (meromorphicAt_cuspFunction_pow hf n)

/-! ### Enlarging the period -/

/-- The formal Taylor series `∑ (F⁽ⁿ⁾(0)/n!) Xⁿ` of a function at `0`; for cusp functions
this is `qExpansion` (`analyticTaylor_cuspFunction`). -/
private def analyticTaylor (F : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0

private lemma analyticTaylor_cuspFunction (h : ℝ) (f : ℍ → ℂ) :
    analyticTaylor (cuspFunction h f) = qExpansion h f :=
  rfl

/-- If `F` agrees near `0` with `G ∘ (· ^ m)`, then `F` is represented at `0` by the `m`-fold
expansion of the Taylor series of `G`. -/
private lemma hasFPowerSeriesAt_expand_analyticTaylor {G : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0)
    (hG : AnalyticAt ℂ G 0) {F : ℂ → ℂ}
    (hEq : F =ᶠ[𝓝 (0 : ℂ)] G ∘ fun q : ℂ ↦ q ^ m) :
    HasFPowerSeriesAt F
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ ((analyticTaylor G).expand m hm).coeff n)) 0 := by
  obtain ⟨R, hR, hGR⟩ := hG.exists_ball_analyticOnNhd
  have hpow : Tendsto (fun q : ℂ ↦ q ^ m) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun q : ℂ ↦ q ^ m) 0 := by fun_prop
    simpa [hm] using hcont.tendsto
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [hpow (Metric.ball_mem_nhds (0 : ℂ) hR), hEq] with q hq hqEq
  -- reindex the Taylor sum of `G` at `q ^ m` along the injection `n ↦ m * n`
  have hbase' : HasSum
      (fun n ↦ (analyticTaylor G).coeff n • (q ^ m) ^ n) (G (q ^ m)) := by
    simpa [analyticTaylor, sub_zero, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      Complex.hasSum_taylorSeries_on_ball hGR.analyticOn.differentiableOn hq
  have hreindexed : HasSum
      ((fun n ↦ ((analyticTaylor G).expand m hm).coeff n • q ^ n) ∘ fun n ↦ m * n)
      (G (q ^ m)) := by
    apply hbase'.congr_fun
    intro n
    simp only [Function.comp_apply]
    rw [PowerSeries.coeff_expand_mul]
    simp [pow_mul]
  have hinj : Function.Injective fun n ↦ m * n := fun i j hij ↦
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) hij
  have hsum : HasSum
      (fun n ↦ ((analyticTaylor G).expand m hm).coeff n • q ^ n) (G (q ^ m)) := by
    apply (hinj.hasSum_iff ?_).mp hreindexed
    intro n hn
    have hnotdvd : ¬m ∣ n := by
      rintro ⟨k, rfl⟩
      exact hn ⟨k, rfl⟩
    simp [PowerSeries.coeff_expand, hnotdvd]
  simpa [FormalMultilinearSeries.coeff_ofScalars, hqEq, Function.comp_apply,
    smul_eq_mul, mul_comm] using hsum

/-- If `F(q) = G(q ^ m)` near `0`, the Taylor series of `F` is the `m`-fold expansion
(`X ↦ X ^ m` substitution) of the Taylor series of `G`. -/
private lemma analyticTaylor_comp_pow {F G : ℂ → ℂ} {m : ℕ}
    (hm : m ≠ 0) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (hEq : F =ᶠ[𝓝 (0 : ℂ)] G ∘ fun q : ℂ ↦ q ^ m) :
    analyticTaylor F = (analyticTaylor G).expand m hm := by
  have hpEq := (hasFPowerSeriesAt_expand_analyticTaylor hm hG hEq).eq_formalMultilinearSeries
    hF.hasFPowerSeriesAt
  ext n
  have hn := congrArg (fun p ↦ p.coeff n) hpEq
  simpa [analyticTaylor, FormalMultilinearSeries.coeff_ofScalars, div_eq_inv_mul]
    using hn.symm

/-- On a punctured neighbourhood of `0`, the pole-removed cusp function for the enlarged
period `m * h` is the pole-removed cusp function for period `h` composed with `q ↦ q ^ m`. -/
private lemma cuspFunction_poleRemoved_nat_mul_eventuallyEq {h : ℝ} {m : ℕ} (hm : m ≠ 0)
    {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    cuspFunction ((m : ℝ) * h) (poleRemoved ((m : ℝ) * h) f) =ᶠ[𝓝[≠] (0 : ℂ)]
      (cuspFunction h (poleRemoved h f)) ∘ fun q : ℂ ↦ q ^ m := by
  filter_upwards [eventually_ne_zero_and_norm_lt_one] with q ⟨hq0, hqnorm⟩
  rw [Function.comp_apply, cuspFunction_poleRemoved_eq _ _ hq0 hqnorm,
    cuspFunction_poleRemoved_eq _ _ (pow_ne_zero _ hq0)
      (by simpa [norm_pow] using pow_lt_one₀ (norm_nonneg q) hqnorm hm),
    poleOrder_nat_mul hm hmero hfper, cuspFunction_nat_mul_eq_cuspFunction_pow hfper hq0,
    pow_mul]

/-- Enlarging a period by `m` expands the pole-removed q-expansion by `X ↦ X^m`. -/
lemma to_qExpansion_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    to_qExpansion ((m : ℝ) * h) f = (to_qExpansion h f).expand m hm := by
  have hFan : AnalyticAt ℂ (cuspFunction ((m : ℝ) * h) (poleRemoved ((m : ℝ) * h) f)) 0 :=
    analyticAt_cuspFunction_poleRemoved (meromorphicAt_cuspFunction_nat_mul hm hmero hfper)
  have hGan : AnalyticAt ℂ (cuspFunction h (poleRemoved h f)) 0 :=
    analyticAt_cuspFunction_poleRemoved hmero
  have hGcomp : AnalyticAt ℂ ((cuspFunction h (poleRemoved h f)) ∘ fun q : ℂ ↦ q ^ m) 0 :=
    AnalyticAt.comp (by simpa [hm] using hGan) (analyticAt_id.pow m)
  have hEq := (hFan.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hGcomp.continuousAt).mp (cuspFunction_poleRemoved_nat_mul_eventuallyEq hm hmero hfper)
  simpa only [analyticTaylor_cuspFunction] using analyticTaylor_comp_pow hm hFan hGan hEq

/-- For `m ≠ 0`, multiplication by `m` as an order embedding of `ℤ`. Extending the domain of a
Laurent series along it (`HahnSeries.embDomain`) substitutes `q ↦ q ^ m`. -/
def natMulOrderEmbedding (m : ℕ) (hm : m ≠ 0) : ℤ ↪o ℤ :=
  OrderEmbedding.ofStrictMono (fun k ↦ (m : ℤ) * k) fun _ _ hab ↦
    Int.mul_lt_mul_of_pos_left hab (by omega)

@[simp] lemma natMulOrderEmbedding_apply (m : ℕ) (hm : m ≠ 0) (k : ℤ) :
    natMulOrderEmbedding m hm k = m * k :=
  rfl

/-- Substituting `X ↦ X ^ m` in a power series corresponds, on Laurent series, to extending the
domain along `k ↦ m * k`. -/
theorem HahnSeries.ofPowerSeries_expand {R : Type*} [CommRing R] (m : ℕ) (hm : m ≠ 0)
    (F : PowerSeries R) :
    HahnSeries.ofPowerSeries ℤ R (F.expand m hm) =
      HahnSeries.embDomain (natMulOrderEmbedding m hm) (HahnSeries.ofPowerSeries ℤ R F) := by
  ext k
  rcases em ((m : ℤ) ∣ k) with ⟨j, rfl⟩ | hk
  · rw [← natMulOrderEmbedding_apply m hm, HahnSeries.embDomain_coeff, natMulOrderEmbedding_apply,
      PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    rcases lt_or_ge j 0 with hj | hj
    · rw [if_pos hj, if_pos (Int.mul_neg_of_pos_of_neg (by omega) hj)]
    · lift j to ℕ using hj
      rw [← Nat.cast_mul, if_neg (Int.natCast_nonneg _).not_gt,
        if_neg (Int.natCast_nonneg _).not_gt, Int.natAbs_natCast, Int.natAbs_natCast,
        PowerSeries.coeff_expand_mul]
  · rw [HahnSeries.embDomain_notin_range fun ⟨j, hj⟩ ↦ hk ⟨j, hj.symm⟩, PowerSeries.coeff_coe]
    split_ifs with hneg
    · rfl
    · refine PowerSeries.coeff_expand_of_not_dvd _ _ _ fun ⟨j, hj⟩ ↦ hk ⟨j, ?_⟩
      omega

/-- Enlarging the period from `h` to `m * h` substitutes `q ↦ q ^ m` in the Laurent
q-expansion: the Laurent series is extended along `k ↦ m * k`. -/
theorem laurentqExpansion_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    laurentqExpansion ((m : ℝ) * h) f =
      HahnSeries.embDomain (natMulOrderEmbedding m hm) (laurentqExpansion h f) := by
  rw [UpperHalfPlane.laurentqExpansion, UpperHalfPlane.laurentqExpansion,
    HahnSeries.embDomain_mul _ (fun _ _ ↦ by simp [mul_add]), HahnSeries.embDomain_single,
    ← HahnSeries.ofPowerSeries_expand, ← to_qExpansion_nat_mul hm hmero hfper,
    poleOrder_nat_mul hm hmero hfper, natMulOrderEmbedding_apply]
  congr 3
  push_cast
  ring

/-- The coefficient at `m * k` for period `m * h` is the coefficient at `k` for period `h`. -/
lemma laurentqExpansion_nat_mul_coeff {h : ℝ} {m : ℕ} (hm : m ≠ 0)
    {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) (k : ℤ) :
    (laurentqExpansion ((m : ℝ) * h) f).coeff ((m : ℤ) * k) =
      (laurentqExpansion h f).coeff k := by
  rw [laurentqExpansion_nat_mul hm hmero hfper, ← natMulOrderEmbedding_apply m hm,
    HahnSeries.embDomain_coeff]

/-- A Laurent coefficient at an enlarged period vanishes unless its exponent is divisible by
the enlargement factor. -/
lemma laurentqExpansion_nat_mul_coeff_of_not_dvd
    {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) {k : ℤ}
    (hk : ¬(m : ℤ) ∣ k) :
    (laurentqExpansion ((m : ℝ) * h) f).coeff k = 0 := by
  rw [laurentqExpansion_nat_mul hm hmero hfper]
  exact HahnSeries.embDomain_notin_range fun ⟨j, hj⟩ ↦ hk ⟨j, hj.symm⟩
