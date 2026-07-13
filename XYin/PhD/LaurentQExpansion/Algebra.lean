/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.LaurentQExpansion.LaurentQExpansion
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Algebra of Laurent q-expansions

This file proves that the analytic Laurent q-expansion respects finite sums and products of
cusp-meromorphic functions. It also compares the coefficients obtained from a period `h` with
those obtained from the enlarged period `m * h`.
-/

open Complex Function Filter LaurentSeries ModularForm UpperHalfPlane
open Set

noncomputable section

local notation "𝔢" => Periodic.qParam

private lemma cuspFunction_qpow_mul_eventuallyEq
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) :
    cuspFunction h (fun τ ↦ (𝔢 h τ) ^ n * f τ) =ᶠ[nhds (0 : ℂ)]
      fun q ↦ q ^ n * cuspFunction h f q := by
  let F : ℂ → ℂ := cuspFunction h (fun τ ↦ (𝔢 h τ) ^ n * f τ)
  let G : ℂ → ℂ := fun q ↦ q ^ n * cuspFunction h f q
  have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
    simpa [Metric.ball, dist_eq_norm] using
      (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds hnorm0
  have hEq : F =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] G := by
    filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
    exact cuspFunction_qpow_mul_eq hh f
      (Set.mem_compl_singleton_iff.mp hq) hqnorm
  have hGan : AnalyticAt ℂ G 0 := by
    simpa [G] using (analyticAt_id.pow n).mul hf
  have hF0 : F 0 = G 0 := by
    calc
      F 0 = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) F := by
        simpa [F, UpperHalfPlane.cuspFunction] using
          (Periodic.cuspFunction_zero_eq_limUnder_nhds_ne
            (h := h) (f := (fun τ : ℍ ↦ (𝔢 h τ) ^ n * f τ) ∘
              UpperHalfPlane.ofComplex))
      _ = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) G := by
        exact congrArg lim (Filter.map_congr hEq)
      _ = G 0 := by
        exact (hGan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  exact eventuallyEq_nhds_of_eventuallyEq_nhdsNE hEq hF0

private lemma analyticAt_cuspFunction_qpow_mul
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) :
    AnalyticAt ℂ
      (cuspFunction h (fun τ ↦ (𝔢 h τ) ^ n * f τ)) 0 := by
  exact ((analyticAt_id.pow n).mul hf).congr
    (cuspFunction_qpow_mul_eventuallyEq hh hf n).symm

private lemma qExpansion_qParam_pow (h : ℝ) (hh : 0 < h) (n : ℕ) :
    qExpansion h (fun τ : ℍ ↦ (𝔢 h τ) ^ n) =
      (PowerSeries.X : PowerSeries ℂ) ^ n := by
  have h1 : cuspFunction h (fun _ : ℍ ↦ (1 : ℂ)) = 1 := by
    ext q
    rcases eq_or_ne q 0 with rfl | hq
    · simpa [UpperHalfPlane.cuspFunction, Periodic.cuspFunction] using
        tendsto_const_nhds.limUnder_eq
    · simp [UpperHalfPlane.cuspFunction,
        Periodic.cuspFunction_eq_of_nonzero h _ hq]
  have hconst : AnalyticAt ℂ (cuspFunction h (fun _ : ℍ ↦ (1 : ℂ))) 0 := by
    simpa [h1] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) 0)
  have hEq : cuspFunction h (fun τ : ℍ ↦ (𝔢 h τ) ^ n) =ᶠ[nhds 0]
      fun q : ℂ ↦ q ^ n := by
    simpa [h1] using cuspFunction_qpow_mul_eventuallyEq hh hconst n
  ext k
  rw [qExpansion_coeff, hEq.iteratedDeriv_eq k]
  rw [iteratedDeriv_fun_pow_zero]
  by_cases hk : k = n
  · subst k
    have hn : (n.factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    simpa [PowerSeries.coeff_X_pow] using inv_mul_cancel₀ hn
  · simp [PowerSeries.coeff_X_pow, hk]

private lemma qExpansion_qpow_mul {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) :
    qExpansion h (fun τ ↦ (𝔢 h τ) ^ n * f τ) =
      (PowerSeries.X : PowerSeries ℂ) ^ n * qExpansion h f := by
  have hpow : AnalyticAt ℂ
      (cuspFunction h (fun τ : ℍ ↦ (𝔢 h τ) ^ n)) 0 := by
    have hconst : AnalyticAt ℂ (cuspFunction h (fun _ : ℍ ↦ (1 : ℂ))) 0 := by
      have h1 : cuspFunction h (fun _ : ℍ ↦ (1 : ℂ)) = 1 := by
        ext q
        rcases eq_or_ne q 0 with rfl | hq
        · simpa [UpperHalfPlane.cuspFunction, Periodic.cuspFunction] using
            tendsto_const_nhds.limUnder_eq
        · simp [UpperHalfPlane.cuspFunction,
            Periodic.cuspFunction_eq_of_nonzero h _ hq]
      simpa [h1] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) 0)
    simpa using analyticAt_cuspFunction_qpow_mul hh hconst n
  simpa [qExpansion_qParam_pow h hh n] using
    (qExpansion_mul (h := h) (f := fun τ : ℍ ↦ (𝔢 h τ) ^ n) (g := f) hpow hf)

private def shiftedLaurent (h : ℝ) (N : ℕ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-(N : ℤ)) 1 *
    (HahnSeries.ofPowerSeries ℤ ℂ)
      (qExpansion h (fun τ ↦ (𝔢 h τ) ^ N * f τ))

private lemma laurentqExpansion_eq_shiftedLaurent
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) {N : ℕ}
    (hN : poleOrder h f ≤ N) :
    laurentqExpansion h f = shiftedLaurent h N f := by
  let M := poleOrder h f
  let k := N - M
  have hMk : M + k = N := by
    simpa [M, k] using Nat.add_sub_of_le hN
  have hfun :
      (fun τ : ℍ ↦ (𝔢 h τ) ^ N * f τ) =
        fun τ : ℍ ↦ (𝔢 h τ) ^ k * poleRemoved h f τ := by
    funext τ
    simp only [UpperHalfPlane.poleRemoved]
    rw [← mul_assoc, ← pow_add]
    rw [Nat.add_comm k M, hMk]
  have hq :
      qExpansion h (fun τ : ℍ ↦ (𝔢 h τ) ^ N * f τ) =
        (PowerSeries.X : PowerSeries ℂ) ^ k * to_qExpansion h f := by
    rw [hfun, qExpansion_qpow_mul hh
      (analyticAt_cuspFunction_poleRemoved (h := h) (f := f) hf) k]
    rfl
  rw [UpperHalfPlane.laurentqExpansion, shiftedLaurent, hq]
  rw [map_mul, HahnSeries.ofPowerSeries_X_pow]
  rw [← mul_assoc, HahnSeries.single_mul_single]
  congr 1
  simp only [one_mul]
  have hMkZ : (M : ℤ) + (k : ℤ) = (N : ℤ) := by
    exact_mod_cast hMk
  have hexp : -(poleOrder h f : ℤ) = -(N : ℤ) + (k : ℤ) := by
    change -(M : ℤ) = -(N : ℤ) + (k : ℤ)
    omega
  rw [hexp]

private lemma analyticAt_cuspFunction_qpow_of_poleOrder_le
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) {N : ℕ}
    (hN : poleOrder h f ≤ N) :
    AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝔢 h τ) ^ N * f τ)) 0 := by
  let M := poleOrder h f
  let k := N - M
  have hMk : M + k = N := by
    simpa [M, k] using Nat.add_sub_of_le hN
  have hfun :
      (fun τ : ℍ ↦ (𝔢 h τ) ^ N * f τ) =
        fun τ : ℍ ↦ (𝔢 h τ) ^ k * poleRemoved h f τ := by
    funext τ
    simp only [UpperHalfPlane.poleRemoved]
    rw [← mul_assoc, ← pow_add]
    rw [Nat.add_comm k M, hMk]
  rw [hfun]
  exact analyticAt_cuspFunction_qpow_mul hh
    (analyticAt_cuspFunction_poleRemoved (h := h) (f := f) hf) k

/-- Laurent q-expansion respects pointwise addition of cusp-meromorphic functions. -/
lemma laurentqExpansion_add
    {h : ℝ} (hh : 0 < h) {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentqExpansion h (fun τ ↦ f τ + g τ) =
      laurentqExpansion h f + laurentqExpansion h g := by
  let N := poleOrder h f + poleOrder h g +
    poleOrder h (fun τ ↦ f τ + g τ)
  have hNf : poleOrder h f ≤ N := by simp only [N]; omega
  have hNg : poleOrder h g ≤ N := by simp only [N]; omega
  have hfg := meromorphicAt_cuspFunction_add hf hg
  have hNfg : poleOrder h (fun τ ↦ f τ + g τ) ≤ N := by
    simp only [N]
    omega
  rw [laurentqExpansion_eq_shiftedLaurent hh hfg hNfg,
    laurentqExpansion_eq_shiftedLaurent hh hf hNf,
    laurentqExpansion_eq_shiftedLaurent hh hg hNg]
  have hfN := analyticAt_cuspFunction_qpow_of_poleOrder_le hh hf hNf
  have hgN := analyticAt_cuspFunction_qpow_of_poleOrder_le hh hg hNg
  have hqadd :
      qExpansion h (fun τ ↦ (𝔢 h τ) ^ N * (f τ + g τ)) =
        qExpansion h (fun τ ↦ (𝔢 h τ) ^ N * f τ) +
          qExpansion h (fun τ ↦ (𝔢 h τ) ^ N * g τ) := by
    have hfun :
        (fun τ : ℍ ↦ (𝔢 h τ) ^ N * (f τ + g τ)) =
          (fun τ : ℍ ↦ (𝔢 h τ) ^ N * f τ) +
            fun τ : ℍ ↦ (𝔢 h τ) ^ N * g τ := by
      funext τ
      dsimp only [Pi.add_apply]
      ring
    rw [hfun, qExpansion_add hfN hgN]
  simp only [shiftedLaurent]
  rw [hqadd, map_add, mul_add]

/-- Laurent q-expansion respects pointwise multiplication of cusp-meromorphic functions. -/
lemma laurentqExpansion_mul
    {h : ℝ} (hh : 0 < h) {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentqExpansion h (fun τ ↦ f τ * g τ) =
      laurentqExpansion h f * laurentqExpansion h g := by
  let Mfg := poleOrder h (fun τ ↦ f τ * g τ)
  let A := poleOrder h f + Mfg
  let B := poleOrder h g
  let N := A + B
  have hAf : poleOrder h f ≤ A := by simp [A]
  have hBg : poleOrder h g ≤ B := by simp [B]
  have hNfg : Mfg ≤ N := by simp only [Mfg, N, A, B]; omega
  have hfg := meromorphicAt_cuspFunction_mul hf hg
  rw [laurentqExpansion_eq_shiftedLaurent hh hfg hNfg,
    laurentqExpansion_eq_shiftedLaurent hh hf hAf,
    laurentqExpansion_eq_shiftedLaurent hh hg hBg]
  have hfA := analyticAt_cuspFunction_qpow_of_poleOrder_le hh hf hAf
  have hgB := analyticAt_cuspFunction_qpow_of_poleOrder_le hh hg hBg
  have hqmul :
      qExpansion h (fun τ ↦ (𝔢 h τ) ^ N * (f τ * g τ)) =
        qExpansion h (fun τ ↦ (𝔢 h τ) ^ A * f τ) *
          qExpansion h (fun τ ↦ (𝔢 h τ) ^ B * g τ) := by
    have hfun :
        (fun τ : ℍ ↦ (𝔢 h τ) ^ N * (f τ * g τ)) =
          (fun τ : ℍ ↦ (𝔢 h τ) ^ A * f τ) *
            fun τ : ℍ ↦ (𝔢 h τ) ^ B * g τ := by
      funext τ
      dsimp only [Pi.mul_apply]
      rw [show N = A + B by rfl, pow_add]
      ring
    rw [hfun, qExpansion_mul hfA hgB]
  simp only [shiftedLaurent]
  rw [hqmul, map_mul]
  rw [mul_mul_mul_comm]
  rw [HahnSeries.single_mul_single]
  congr 1
  · simp only [one_mul]
    have hAB : (A : ℤ) + (B : ℤ) = (N : ℤ) := by
      exact_mod_cast (show A + B = N by rfl)
    have hexp : -(N : ℤ) = -(A : ℤ) + -(B : ℤ) := by omega
    rw [hexp]

private lemma analyticAt_cuspFunction_const (h : ℝ) (a : ℂ) :
    AnalyticAt ℂ (cuspFunction h (fun _ : ℍ ↦ a)) 0 := by
  have hconst : cuspFunction h (fun _ : ℍ ↦ a) = fun _ : ℂ ↦ a := by
    ext q
    rcases eq_or_ne q 0 with rfl | hq
    · simpa [UpperHalfPlane.cuspFunction, Periodic.cuspFunction] using
        tendsto_const_nhds.limUnder_eq
    · simp [UpperHalfPlane.cuspFunction,
        Periodic.cuspFunction_eq_of_nonzero h _ hq]
  simpa [hconst] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ a) 0)

/-- The Laurent q-expansion of the zero function is zero. -/
@[simp] lemma laurentqExpansion_zero (h : ℝ) :
    laurentqExpansion h (0 : ℍ → ℂ) = 0 := by
  have hmero : MeromorphicAt (cuspFunction h (0 : ℍ → ℂ)) 0 := by
    simpa only [Pi.zero_apply] using meromorphicAt_cuspFunction_const h 0
  have hpole : poleOrder h (0 : ℍ → ℂ) = 0 :=
    (analyticAt_iff hmero).1 (by
      simpa only [Pi.zero_apply] using analyticAt_cuspFunction_const h 0)
  calc
    laurentqExpansion h (0 : ℍ → ℂ) = qExpansion h (0 : ℍ → ℂ) :=
      (laurentqExpansion.eq_qExpansion_iff hmero).2 hpole
    _ = 0 := by
      simpa using congrArg (HahnSeries.ofPowerSeries ℤ ℂ) (qExpansion_zero h)

/-- The Laurent q-expansion of the constant-one function is one. -/
@[simp] lemma laurentqExpansion_one (h : ℝ) :
    laurentqExpansion h (1 : ℍ → ℂ) = 1 := by
  have hmero : MeromorphicAt (cuspFunction h (1 : ℍ → ℂ)) 0 := by
    simpa only [Pi.one_apply] using meromorphicAt_cuspFunction_const h 1
  have hpole : poleOrder h (1 : ℍ → ℂ) = 0 :=
    (analyticAt_iff hmero).1 (by
      simpa only [Pi.one_apply] using analyticAt_cuspFunction_const h 1)
  calc
    laurentqExpansion h (1 : ℍ → ℂ) = qExpansion h (1 : ℍ → ℂ) :=
      (laurentqExpansion.eq_qExpansion_iff hmero).2 hpole
    _ = 1 := by
      simpa using congrArg (HahnSeries.ofPowerSeries ℤ ℂ) (qExpansion_one h)

/-- The Laurent q-expansion of a constant function is the corresponding constant series. -/
@[simp] lemma laurentqExpansion_const (h : ℝ) (a : ℂ) :
    laurentqExpansion h (fun _ : ℍ ↦ a) = HahnSeries.C a := by
  have hmero := meromorphicAt_cuspFunction_const h a
  have hpole : poleOrder h (fun _ : ℍ ↦ a) = 0 :=
    (analyticAt_iff hmero).1 (analyticAt_cuspFunction_const h a)
  rw [(laurentqExpansion.eq_qExpansion_iff hmero).2 hpole]
  have hOne : AnalyticAt ℂ (cuspFunction h (1 : ℍ → ℂ)) 0 := by
    simpa only [Pi.one_apply] using analyticAt_cuspFunction_const h 1
  have hq : qExpansion h (fun _ : ℍ ↦ a) = PowerSeries.C a := by
    calc
      qExpansion h (fun _ : ℍ ↦ a) = qExpansion h (a • (1 : ℍ → ℂ)) := by
        congr 1
        ext τ
        simp
      _ = a • qExpansion h (1 : ℍ → ℂ) := qExpansion_smul hOne a
      _ = PowerSeries.C a := by
        rw [PowerSeries.smul_eq_C_mul, qExpansion_one, mul_one]
  rw [hq, HahnSeries.ofPowerSeries_C]

/-- Laurent q-expansion respects pointwise negation. -/
lemma laurentqExpansion_neg
    {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    laurentqExpansion h (fun τ ↦ -f τ) = -laurentqExpansion h f := by
  have hconst := meromorphicAt_cuspFunction_const h (-1)
  have hmul := laurentqExpansion_mul hh hconst hf
  have hC : HahnSeries.C (-1 : ℂ) = (-1 : LaurentSeries ℂ) := by simp
  calc
    laurentqExpansion h (fun τ ↦ -f τ) =
        laurentqExpansion h (fun τ ↦ (-1 : ℂ) * f τ) := by congr 1; funext τ; ring
    _ = HahnSeries.C (-1 : ℂ) * laurentqExpansion h f := by
      simpa only [laurentqExpansion_const] using hmul
    _ = -laurentqExpansion h f := by rw [hC]; ring

/-- Laurent q-expansion commutes with a finite pointwise sum. -/
lemma laurentqExpansion_finset_sum
    {h : ℝ} (hh : 0 < h) {I : Type*} (s : Finset I) {f : I → ℍ → ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) :
    laurentqExpansion h (∑ i ∈ s, f i) =
      ∑ i ∈ s, laurentqExpansion h (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have ih' := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      exact (laurentqExpansion_add hh (hf a (Finset.mem_insert_self a s))
        (meromorphicAt_cuspFunction_finset_sum
          (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))).trans
        (congrArg (laurentqExpansion h (f a) + ·) ih')

/-- Laurent q-expansion commutes with a finite pointwise product. -/
lemma laurentqExpansion_finset_prod
    {h : ℝ} (hh : 0 < h) {I : Type*} (s : Finset I) {f : I → ℍ → ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) :
    laurentqExpansion h (∏ i ∈ s, f i) =
      ∏ i ∈ s, laurentqExpansion h (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ih' := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      exact (laurentqExpansion_mul hh (hf a (Finset.mem_insert_self a s))
        (meromorphicAt_cuspFunction_finset_prod
          (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))).trans
        (congrArg (laurentqExpansion h (f a) * ·) ih')

private lemma analyticAt_hasFPowerSeriesAt_taylor {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) :
    HasFPowerSeriesAt F
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0)) 0 := by
  obtain ⟨R, hR, hFR⟩ := hF.exists_ball_analyticOnNhd
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with q hq
  have hs := Complex.hasSum_taylorSeries_on_ball
    hFR.analyticOn.differentiableOn hq
  simpa [FormalMultilinearSeries.coeff_ofScalars, sub_zero, smul_eq_mul,
    mul_assoc, mul_left_comm, mul_comm] using hs

private def analyticTaylor (F : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0

private lemma analyticTaylor_comp_pow {F G : ℂ → ℂ} {m : ℕ}
    (hm : m ≠ 0) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (hEq : F =ᶠ[nhds (0 : ℂ)] G ∘ fun q : ℂ ↦ q ^ m) :
    analyticTaylor F = (analyticTaylor G).expand m hm := by
  let P := (analyticTaylor G).expand m hm
  let pP := FormalMultilinearSeries.ofScalars ℂ (fun n ↦ P.coeff n)
  have hP : HasFPowerSeriesAt F pP 0 := by
    obtain ⟨R, hR, hGR⟩ := hG.exists_ball_analyticOnNhd
    have hpow : Tendsto (fun q : ℂ ↦ q ^ m) (nhds 0) (nhds 0) := by
      have hcont : ContinuousAt (fun q : ℂ ↦ q ^ m) 0 := by fun_prop
      simpa [hm] using hcont.tendsto
    have hball : ∀ᶠ q in nhds (0 : ℂ), q ^ m ∈ Metric.ball (0 : ℂ) R :=
      hpow (Metric.ball_mem_nhds (0 : ℂ) hR)
    rw [hasFPowerSeriesAt_iff]
    filter_upwards [hball, hEq] with q hq hqEq
    have hbase := Complex.hasSum_taylorSeries_on_ball
      hGR.analyticOn.differentiableOn hq
    have hbase' : HasSum
        (fun n ↦ (analyticTaylor G).coeff n • (q ^ m) ^ n) (G (q ^ m)) := by
      simpa [analyticTaylor, sub_zero, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
        using hbase
    have hreindexed : HasSum
        ((fun n ↦ P.coeff n • q ^ n) ∘ fun n ↦ m * n) (G (q ^ m)) := by
      apply hbase'.congr_fun
      intro n
      simp only [Function.comp_apply, P]
      rw [PowerSeries.coeff_expand_mul]
      simp [pow_mul]
    have hinj : Function.Injective (fun n ↦ m * n) := by
      intro i j hij
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) hij
    have hsum : HasSum (fun n ↦ P.coeff n • q ^ n) (G (q ^ m)) := by
      apply (hinj.hasSum_iff ?_).mp hreindexed
      intro n hn
      have hnotdvd : ¬m ∣ n := by
        rintro ⟨k, rfl⟩
        exact hn ⟨k, rfl⟩
      simp [P, PowerSeries.coeff_expand, hnotdvd]
    simpa [pP, FormalMultilinearSeries.coeff_ofScalars, hqEq,
      Function.comp_apply, smul_eq_mul, mul_comm] using hsum
  have hTaylor := analyticAt_hasFPowerSeriesAt_taylor hF
  have hpEq := hP.eq_formalMultilinearSeries hTaylor
  ext n
  have hn := congrArg (fun p ↦ p.coeff n) hpEq
  simpa [pP, P, analyticTaylor, FormalMultilinearSeries.coeff_ofScalars] using hn.symm

/-- Enlarging a period by `m` expands the pole-removed q-expansion by `X ↦ X^m`. -/
lemma to_qExpansion_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    to_qExpansion ((m : ℝ) * h) f = (to_qExpansion h f).expand m hm := by
  have hmeroM := meromorphicAt_cuspFunction_nat_mul hm hmero hfper
  have hpole := poleOrder_nat_mul hm hmero hfper
  let F : ℂ → ℂ := cuspFunction ((m : ℝ) * h) (poleRemoved ((m : ℝ) * h) f)
  let G : ℂ → ℂ := cuspFunction h (poleRemoved h f)
  have hFan : AnalyticAt ℂ F 0 := by
    simpa [F] using analyticAt_cuspFunction_poleRemoved hmeroM
  have hGan : AnalyticAt ℂ G 0 := by
    simpa [G] using analyticAt_cuspFunction_poleRemoved hmero
  have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
    simpa [Metric.ball, dist_eq_norm] using
      (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds hnorm0
  have hEqNE : F =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] G ∘ fun q : ℂ ↦ q ^ m := by
    filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
    have hqpow0 : q ^ m ≠ 0 := pow_ne_zero _ hq0
    have hqpowNorm : ‖q ^ m‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hqnorm hm
    have hshiftM := cuspFunction_poleRemoved_eq hmeroM hq0 hqnorm
    have hshift := cuspFunction_poleRemoved_eq hmero hqpow0 hqpowNorm
    have hcusp := cuspFunction_nat_mul_eq_cuspFunction_pow (m := m) hfper hq0
    calc
      F q = q ^ poleOrder ((m : ℝ) * h) f *
          cuspFunction ((m : ℝ) * h) f q := hshiftM
      _ = q ^ (m * poleOrder h f) * cuspFunction h f (q ^ m) := by
        rw [hpole, hcusp]
      _ = (q ^ m) ^ poleOrder h f * cuspFunction h f (q ^ m) := by
        rw [pow_mul]
      _ = G (q ^ m) := hshift.symm
      _ = (G ∘ fun z : ℂ ↦ z ^ m) q := rfl
  have hGcomp : AnalyticAt ℂ (G ∘ fun q : ℂ ↦ q ^ m) 0 := by
    have hpow : AnalyticAt ℂ (fun q : ℂ ↦ q ^ m) 0 := by fun_prop
    have hGan0 : AnalyticAt ℂ G ((fun q : ℂ ↦ q ^ m) 0) := by
      simpa [hm] using hGan
    exact AnalyticAt.comp (𝕜 := ℂ) (g := G) (f := fun q : ℂ ↦ q ^ m)
      (x := 0) hGan0 hpow
  have hEq : F =ᶠ[nhds (0 : ℂ)] G ∘ fun q : ℂ ↦ q ^ m :=
    (hFan.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      hGcomp.continuousAt).mp hEqNE
  have hTaylor := analyticTaylor_comp_pow hm hFan hGan hEq
  simpa [F, G, analyticTaylor, UpperHalfPlane.to_qExpansion,
    UpperHalfPlane.qExpansion] using hTaylor

/-- The coefficient at `m * k` for period `m * h` is the coefficient at `k` for period `h`. -/
lemma laurentqExpansion_nat_mul_coeff {h : ℝ} {m : ℕ} (hm : m ≠ 0)
    {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) (k : ℤ) :
    (laurentqExpansion ((m : ℝ) * h) f).coeff ((m : ℤ) * k) =
      (laurentqExpansion h f).coeff k := by
  have hpole := poleOrder_nat_mul hm hmero hfper
  have hmpos : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  by_cases hk : k < -(poleOrder h f : ℤ)
  · have hkM : (m : ℤ) * k <
        -(poleOrder ((m : ℝ) * h) f : ℤ) := by
      rw [hpole]
      push_cast
      simpa [mul_neg] using Int.mul_lt_mul_of_pos_left hk hmpos
    rw [laurentqExpansion.coeff_eq_zero_of_lt hkM,
      laurentqExpansion.coeff_eq_zero_of_lt hk]
  · have hkge : -(poleOrder h f : ℤ) ≤ k := le_of_not_gt hk
    have hkMge : -(poleOrder ((m : ℝ) * h) f : ℤ) ≤ (m : ℤ) * k := by
      rw [hpole]
      push_cast
      simpa [mul_neg] using Int.mul_le_mul_of_nonneg_left hkge hmpos.le
    rw [laurentqExpansion.coeff_of_geq hkMge,
      laurentqExpansion.coeff_of_geq hkge, to_qExpansion_nat_mul hm hmero hfper]
    have hsum : 0 ≤ k + (poleOrder h f : ℤ) := by linarith
    have hnat :
        Int.toNat ((m : ℤ) * k + poleOrder ((m : ℝ) * h) f) =
          m * Int.toNat (k + poleOrder h f) := by
      rw [hpole]
      have heq :
          (m : ℤ) * k + ((m * poleOrder h f : ℕ) : ℤ) =
            (m : ℤ) * (k + poleOrder h f) := by
        push_cast
        ring
      rw [heq, Int.toNat_mul (by exact_mod_cast Nat.zero_le m) hsum]
      simp
    rw [hnat, PowerSeries.coeff_expand_mul]

/-- A Laurent coefficient at an enlarged period vanishes unless its exponent is divisible by
the enlargement factor. -/
lemma laurentqExpansion_nat_mul_coeff_of_not_dvd
    {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) {k : ℤ}
    (hk : ¬(m : ℤ) ∣ k) :
    (laurentqExpansion ((m : ℝ) * h) f).coeff k = 0 := by
  have hpole := poleOrder_nat_mul hm hmero hfper
  by_cases hlt : k < -(poleOrder ((m : ℝ) * h) f : ℤ)
  · exact laurentqExpansion.coeff_eq_zero_of_lt hlt
  · have hge : -(poleOrder ((m : ℝ) * h) f : ℤ) ≤ k := le_of_not_gt hlt
    rw [laurentqExpansion.coeff_of_geq hge,
      to_qExpansion_nat_mul hm hmero hfper]
    apply PowerSeries.coeff_expand_of_not_dvd
    intro hdvd
    apply hk
    obtain ⟨a, ha⟩ := hdvd
    have hnonneg : 0 ≤ k + (poleOrder ((m : ℝ) * h) f : ℤ) := by
      omega
    have hcast : ((k + (poleOrder ((m : ℝ) * h) f : ℤ)).toNat : ℤ) =
        (m : ℤ) * a := by
      exact_mod_cast ha
    rw [Int.toNat_of_nonneg hnonneg, hpole] at hcast
    push_cast at hcast
    refine ⟨(a : ℤ) - poleOrder h f, ?_⟩
    linear_combination hcast
