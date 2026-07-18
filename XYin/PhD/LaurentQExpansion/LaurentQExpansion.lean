/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import XYin.PhD.Modularforms.Eisenstein

/-!
# Laurent q-expansions at the cusp

Mathlib's `UpperHalfPlane.qExpansion` handles functions whose cusp function is analytic at
`q = 0`. This file extends the theory to functions that are merely *meromorphic* at the cusp:
multiplying by `q ^ poleOrder` removes the pole, and the Taylor series of the pole-removed
function is reassembled into a Laurent series.

## Main definitions

* `UpperHalfPlane.poleOrder`: the order of the pole of `cuspFunction h f` at `q = 0`.
* `UpperHalfPlane.poleRemoved`: the pole-cancelled function `𝕢 h τ ^ poleOrder h f * f τ`.
* `UpperHalfPlane.to_qExpansion`: the q-expansion of the pole-removed function.
* `UpperHalfPlane.laurentqExpansion`: the Laurent q-expansion of `f` at the cusp.

## Main results

* `analyticAt_cuspFunction_poleRemoved`: multiplying by `q ^ poleOrder` removes the pole.
* `meromorphicAt_cuspFunction_of_nat_mul`: meromorphy at the cusp descends from a natural
  multiple of the period back to the period itself.
* `laurentqExpansion_coeff_eq_circleIntegral`: every Laurent coefficient is given by the
  Cauchy contour-integral formula.
-/

open ModularForm Complex Function Matrix.SpecialLinearGroup Metric
  ModularFormClass SlashInvariantFormClass Real Set Filter LaurentSeries
open UpperHalfPlane hiding I

local notation "𝕢" => Periodic.qParam

noncomputable section

variable {h : ℝ}

lemma cuspFunction_nat_mul_eq_cuspFunction_pow {h : ℝ} {m : ℕ} {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) {q : ℂ} (hq : q ≠ 0) :
    cuspFunction ((m : ℝ) * h) f q = cuspFunction h f (q ^ m) := by
  have hqpow : q ^ m ≠ 0 := pow_ne_zero _ hq
  rw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero _ _ hq]
  rw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero _ _ hqpow]
  have hexp :
      Complex.exp (Complex.log (q ^ m)) = Complex.exp ((m : ℂ) * Complex.log q) := by
    rw [Complex.exp_log hqpow, Complex.exp_nat_mul, Complex.exp_log hq]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hinv :
      Periodic.invQParam h (q ^ m) =
        Periodic.invQParam ((m : ℝ) * h) q + n * h := by
    rw [Periodic.invQParam, Periodic.invQParam, hn]
    simp only [mul_add, mul_assoc]
    ring_nf
    field_simp [two_pi_I_ne_zero]
    push_cast
    ring
  simpa [Function.comp_def, hinv] using
    (hfper.int_mul n (Periodic.invQParam ((m : ℝ) * h) q)).symm

private lemma cuspFunction_add_eventuallyEq (h : ℝ) (f g : ℍ → ℂ) :
    cuspFunction h (fun τ ↦ f τ + g τ) =ᶠ[nhdsWithin 0 ({0}ᶜ)]
      fun q ↦ cuspFunction h f q + cuspFunction h g q := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 := Set.mem_compl_singleton_iff.mp hq
  simp only [UpperHalfPlane.cuspFunction]
  rw [Periodic.cuspFunction_eq_of_nonzero _ _ hq0,
    Periodic.cuspFunction_eq_of_nonzero _ _ hq0,
    Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  rfl

private lemma cuspFunction_mul_eventuallyEq (h : ℝ) (f g : ℍ → ℂ) :
    cuspFunction h (fun τ ↦ f τ * g τ) =ᶠ[nhdsWithin 0 ({0}ᶜ)]
      fun q ↦ cuspFunction h f q * cuspFunction h g q := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 := Set.mem_compl_singleton_iff.mp hq
  simp only [UpperHalfPlane.cuspFunction]
  rw [Periodic.cuspFunction_eq_of_nonzero _ _ hq0,
    Periodic.cuspFunction_eq_of_nonzero _ _ hq0,
    Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  rfl

private lemma cuspFunction_const_eventuallyEq (h : ℝ) (a : ℂ) :
    cuspFunction h (fun _ : ℍ ↦ a) =ᶠ[nhdsWithin 0 ({0}ᶜ)] fun _ ↦ a := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 := Set.mem_compl_singleton_iff.mp hq
  simp only [UpperHalfPlane.cuspFunction]
  rw [Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  rfl

/-- Cusp meromorphicity is preserved by pointwise addition. -/
lemma meromorphicAt_cuspFunction_add {h : ℝ} {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    MeromorphicAt (cuspFunction h (fun τ ↦ f τ + g τ)) 0 :=
  (hf.add hg).congr (cuspFunction_add_eventuallyEq h f g).symm

/-- Cusp meromorphicity is preserved by pointwise multiplication. -/
lemma meromorphicAt_cuspFunction_mul {h : ℝ} {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    MeromorphicAt (cuspFunction h (fun τ ↦ f τ * g τ)) 0 :=
  (hf.mul hg).congr (cuspFunction_mul_eventuallyEq h f g).symm

/-- A constant function is meromorphic in every cusp parameter. -/
lemma meromorphicAt_cuspFunction_const (h : ℝ) (a : ℂ) :
    MeromorphicAt (cuspFunction h (fun _ : ℍ ↦ a)) 0 :=
  (MeromorphicAt.const a 0).congr (cuspFunction_const_eventuallyEq h a).symm

/-- A finite pointwise sum of cusp-meromorphic functions is cusp-meromorphic. -/
lemma meromorphicAt_cuspFunction_finset_sum
    {ι : Type*} {h : ℝ} {s : Finset ι} {f : ι → ℍ → ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) :
    MeromorphicAt (cuspFunction h (∑ i ∈ s, f i)) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using meromorphicAt_cuspFunction_const h 0
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      change MeromorphicAt (cuspFunction h (fun τ ↦ f a τ + (∑ i ∈ s, f i) τ)) 0
      exact meromorphicAt_cuspFunction_add (hf a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- A finite pointwise product of cusp-meromorphic functions is cusp-meromorphic. -/
lemma meromorphicAt_cuspFunction_finset_prod
    {ι : Type*} {h : ℝ} {s : Finset ι} {f : ι → ℍ → ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) :
    MeromorphicAt (cuspFunction h (∏ i ∈ s, f i)) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using meromorphicAt_cuspFunction_const h 1
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      change MeromorphicAt (cuspFunction h (fun τ ↦ f a τ * (∏ i ∈ s, f i) τ)) 0
      exact meromorphicAt_cuspFunction_mul (hf a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- Multiplying a cusp width by a nonzero natural number preserves meromorphicity at the
cusp. -/
lemma meromorphicAt_cuspFunction_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    MeromorphicAt (cuspFunction ((m : ℝ) * h) f) (0 : ℂ) := by
  have hg : AnalyticAt ℂ (fun q : ℂ ↦ q ^ m) 0 := by fun_prop
  have hmero0 : MeromorphicAt (cuspFunction h f) ((fun q : ℂ ↦ q ^ m) 0) := by
    simpa [hm] using hmero
  have hcomp : MeromorphicAt (cuspFunction h f ∘ fun q : ℂ ↦ q ^ m) (0 : ℂ) :=
    MeromorphicAt.comp_analyticAt (𝕜 := ℂ) (𝕜' := ℂ) hmero0 hg
  refine hcomp.congr ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (cuspFunction_nat_mul_eq_cuspFunction_pow hfper
    (Set.mem_compl_singleton_iff.mp hq)).symm

private lemma eventually_differentiableAt_pow_mul_of_meromorphicAt_comp_pow_aux
    {g : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0)
    (h : MeromorphicAt (g ∘ fun q : ℂ ↦ q ^ m) 0) (n : ℕ) :
    ∀ᶠ z in nhdsWithin (0 : ℂ) ({0}ᶜ),
      DifferentiableAt ℂ (fun z ↦ z ^ n * g z) z := by
  letI : NeZero m := ⟨hm⟩
  have hcompAna :
      ∀ᶠ q : ℂ in nhds (0 : ℂ),
        q = 0 ∨ AnalyticAt ℂ (g ∘ fun z : ℂ ↦ z ^ m) q := by
    have hpunctured := h.eventually_analyticAt
    rw [eventually_nhdsWithin_iff] at hpunctured
    filter_upwards [hpunctured] with q hq
    by_cases hq0 : q = 0
    · exact Or.inl hq0
    · exact Or.inr (hq (Set.mem_compl_singleton_iff.mpr hq0))
  let U : Set ℂ := {q | q = 0 ∨ AnalyticAt ℂ (g ∘ fun z : ℂ ↦ z ^ m) q}
  have hUimage : (fun q : ℂ ↦ q ^ m) '' U ∈ nhds (0 : ℂ) := by
    simpa [hm] using
      (Complex.isOpenQuotientMap_pow m).isOpenMap.image_mem_nhds
        (show U ∈ nhds 0 from hcompAna)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hUimage] with z hz hz0
  obtain ⟨q, hqU, rfl⟩ := hz
  have hq0 : q ≠ 0 := fun hq0 ↦ hz0 (by simp [hq0, hm])
  have hcompAt : AnalyticAt ℂ (g ∘ fun z : ℂ ↦ z ^ m) q := hqU.resolve_left hq0
  have hderiv : deriv (fun z : ℂ ↦ z ^ m) q ≠ 0 := by
    rw [deriv_pow_field]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hm) (pow_ne_zero _ hq0)
  have hgAt : AnalyticAt ℂ g (q ^ m) :=
    (analyticAt_comp_iff_of_deriv_ne_zero (analyticAt_id.pow m) hderiv).mp hcompAt
  exact ((analyticAt_id.pow n).mul hgAt).differentiableAt

/-- Meromorphicity descends along a nonconstant complex power map. -/
lemma meromorphicAt_of_comp_pow {g : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0)
    (h : MeromorphicAt (g ∘ fun q : ℂ ↦ q ^ m) 0) :
    MeromorphicAt g 0 := by
  letI : NeZero m := ⟨hm⟩
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  let G : ℂ → ℂ := fun z ↦ z ^ n * g z
  have hGcomp : AnalyticAt ℂ (G ∘ fun q : ℂ ↦ q ^ m) 0 := by
    have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hmn : m * n = (m - 1) * n + n := by
      calc
        m * n = ((m - 1) + 1) * n := by rw [Nat.sub_add_cancel hmpos]
        _ = (m - 1) * n + n := by simp [Nat.add_mul]
    have hpow : AnalyticAt ℂ (fun q : ℂ ↦ q ^ ((m - 1) * n)) 0 :=
      analyticAt_id.pow _
    convert hpow.mul hn using 1
    funext q
    simp only [G, Function.comp_apply, Pi.mul_apply, sub_zero, smul_eq_mul]
    rw [← pow_mul, hmn, pow_add]
    ring
  have hGcontinuous : ContinuousAt G 0 := by
    simpa [hm] using
      (Complex.isOpenQuotientMap_pow m).continuousAt_comp_iff.mp hGcomp.continuousAt
  have hGdiff := eventually_differentiableAt_pow_mul_of_meromorphicAt_comp_pow_aux hm
    ⟨n, hn⟩ n
  simpa [G] using Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hGdiff hGcontinuous

/-- If a periodic function is meromorphic in a natural multiple of its cusp parameter, then it
is already meromorphic in the original cusp parameter. -/
lemma meromorphicAt_cuspFunction_of_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction ((m : ℝ) * h) f) (0 : ℂ))
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    MeromorphicAt (cuspFunction h f) (0 : ℂ) := by
  apply meromorphicAt_of_comp_pow hm
  refine hmero.congr ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact cuspFunction_nat_mul_eq_cuspFunction_pow hfper
    (Set.mem_compl_singleton_iff.mp hq)

/-- The pole order of `f` at the cusp: `-ord₀ (cuspFunction h f)` when the meromorphic order
at `q = 0` is negative, and `0` otherwise (including the junk cases). -/
def UpperHalfPlane.poleOrder (h : ℝ) (f : ℍ → ℂ) : ℕ :=
  if meromorphicOrderAt (cuspFunction h f) 0 < 0 then
    Int.natAbs ((meromorphicOrderAt (cuspFunction h f) 0).untopD 0)
  else 0

/-- A meromorphic order of `-r` at the cusp reads off as pole order `r` (valid for `r = 0`
as well). -/
lemma poleOrder_eq_of_meromorphicOrderAt_eq {h : ℝ} {f : ℍ → ℂ} {r : ℕ}
    (hord : meromorphicOrderAt (cuspFunction h f) 0 = ((-(r : ℤ) : ℤ) : WithTop ℤ)) :
    poleOrder h f = r := by
  unfold UpperHalfPlane.poleOrder
  rw [hord]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · rw [if_pos (by exact_mod_cast show (-(r : ℤ) : ℤ) < 0 by omega), WithTop.untopD_coe]
    omega

/-- The pole order vanishes when the meromorphic order at the cusp is nonnegative (in
particular when it is `⊤`). -/
lemma poleOrder_eq_zero_of_meromorphicOrderAt_nonneg {h : ℝ} {f : ℍ → ℂ}
    (hord : 0 ≤ meromorphicOrderAt (cuspFunction h f) 0) : poleOrder h f = 0 := by
  simp [UpperHalfPlane.poleOrder, not_lt_of_ge hord]

/-- Closed formula for the pole order without the if-then-else: it is the positive part of
minus the meromorphic order (with junk value `0` when the order is `⊤`). -/
lemma poleOrder_eq_toNat_neg_meromorphicOrderAt (h : ℝ) (f : ℍ → ℂ) :
    poleOrder h f = Int.toNat (-(meromorphicOrderAt (cuspFunction h f) 0).untopD 0) := by
  cases ho : meromorphicOrderAt (cuspFunction h f) 0 with
  | top => simp [poleOrder_eq_zero_of_meromorphicOrderAt_nonneg (ho ▸ le_top)]
  | coe k =>
      rcases lt_or_ge k 0 with hk | hk
      · rw [poleOrder_eq_of_meromorphicOrderAt_eq (r := k.natAbs)
          (by rw [ho]; exact_mod_cast show k = -((k.natAbs : ℕ) : ℤ) by omega)]
        simp only [WithTop.untopD_coe]
        omega
      · rw [poleOrder_eq_zero_of_meromorphicOrderAt_nonneg (by rw [ho]; exact_mod_cast hk)]
        simp only [WithTop.untopD_coe]
        omega

lemma meromorphicOrderAt_cuspFunction_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    meromorphicOrderAt (cuspFunction ((m : ℝ) * h) f) (0 : ℂ) =
      meromorphicOrderAt (cuspFunction h f) (0 : ℂ) * m := by
  have hEq :
      cuspFunction ((m : ℝ) * h) f =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q =>
        cuspFunction h f (q ^ m) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact cuspFunction_nat_mul_eq_cuspFunction_pow hfper (Set.mem_compl_singleton_iff.mp hq)
  rw [meromorphicOrderAt_congr hEq]
  have hg_nc : ¬ EventuallyConst (fun q : ℂ => q ^ m) (nhds (0 : ℂ)) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top]
    have hpow0 : (0 : ℂ) ^ m = 0 := by
      simp [hm]
    have horderPow : analyticOrderAt (fun q : ℂ => q ^ m) (0 : ℂ) = m := by
      change analyticOrderAt (id ^ m) (0 : ℂ) = m
      simpa [analyticOrderAt_id] using
        (analyticOrderAt_pow (𝕜 := ℂ) (f := id) (z₀ := (0 : ℂ)) analyticAt_id m)
    have horder :
        analyticOrderAt (fun q : ℂ => q ^ m - (fun q : ℂ => q ^ m) 0) (0 : ℂ) = m := by
      rw [show (fun q : ℂ => q ^ m - (fun q : ℂ => q ^ m) 0) = fun q : ℂ => q ^ m by
        funext q
        simp [hpow0]]
      exact horderPow
    simp [horder]
  have hpow0 : (0 : ℂ) ^ m = 0 := by simp [hm]
  have horderPow : analyticOrderAt (fun q : ℂ => q ^ m) (0 : ℂ) = m := by
    change analyticOrderAt (id ^ m) (0 : ℂ) = m
    simpa [analyticOrderAt_id] using
      (analyticOrderAt_pow (𝕜 := ℂ) (f := id) (z₀ := (0 : ℂ)) analyticAt_id m)
  have hmero0 : MeromorphicAt (cuspFunction h f) ((fun q : ℂ => q ^ m) 0) := by
    simpa [hpow0] using hmero
  have hcomp := hmero0.meromorphicOrderAt_comp (g := fun q : ℂ => q ^ m) (x := (0 : ℂ))
    (hg := analyticAt_id.pow m) hg_nc
  simpa [Function.comp, hpow0, horderPow] using hcomp

lemma poleOrder_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    poleOrder ((m : ℝ) * h) f = m * poleOrder h f := by
  have hscale := meromorphicOrderAt_cuspFunction_nat_mul (h := h) (m := m) hm hmero hfper
  cases ho : meromorphicOrderAt (cuspFunction h f) (0 : ℂ) with
  | top =>
      rw [ho] at hscale
      have h1 : poleOrder h f = 0 :=
        poleOrder_eq_zero_of_meromorphicOrderAt_nonneg (by rw [ho]; exact le_top)
      have h2 : poleOrder ((m : ℝ) * h) f = 0 :=
        poleOrder_eq_zero_of_meromorphicOrderAt_nonneg (by
          have htop : meromorphicOrderAt (cuspFunction ((m : ℝ) * h) f) 0 = ⊤ := by
            simpa [hm] using hscale
          rw [htop]; exact le_top)
      rw [h1, h2, Nat.mul_zero]
  | coe k =>
      rw [ho] at hscale
      rcases lt_or_ge k 0 with hk | hk
      · have h1 : poleOrder h f = k.natAbs :=
          poleOrder_eq_of_meromorphicOrderAt_eq (by
            rw [ho]; exact_mod_cast show k = -((k.natAbs : ℕ) : ℤ) by omega)
        have h2 : poleOrder ((m : ℝ) * h) f = m * k.natAbs :=
          poleOrder_eq_of_meromorphicOrderAt_eq (by
            rw [hscale]
            exact_mod_cast show k * (m : ℤ) = -((m * k.natAbs : ℕ) : ℤ) by
              push_cast [abs_of_nonpos hk.le]
              ring)
        rw [h1, h2]
      · have h1 : poleOrder h f = 0 :=
          poleOrder_eq_zero_of_meromorphicOrderAt_nonneg (by rw [ho]; exact_mod_cast hk)
        have h2 : poleOrder ((m : ℝ) * h) f = 0 :=
          poleOrder_eq_zero_of_meromorphicOrderAt_nonneg (by
            rw [hscale]
            exact_mod_cast Int.mul_nonneg hk (Int.natCast_nonneg m))
        rw [h1, h2, Nat.mul_zero]

/-- Multiplying `f` by `𝕢 h τ ^ poleOrder h f` cancels the pole at the cusp, yielding a
function whose cusp function is analytic at `q = 0`. -/
def UpperHalfPlane.poleRemoved (h : ℝ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun τ ↦ (𝕢 h τ) ^ (poleOrder h f) * f τ

/-- The q-expansion of the pole-removed function, i.e. the regular part of the Laurent
q-expansion shifted so that its constant term is the leading Laurent coefficient. -/
def UpperHalfPlane.to_qExpansion (h : ℝ) (f : ℍ → ℂ) : PowerSeries ℂ :=
  qExpansion h (poleRemoved h f)

/-- The Laurent q-expansion of `f` at the cusp: `q ^ (-poleOrder h f)` times the power series
of the pole-removed function, realized in `LaurentSeries ℂ`. -/
def UpperHalfPlane.laurentqExpansion (h : ℝ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-(poleOrder h f : ℤ)) 1 * (HahnSeries.ofPowerSeries ℤ ℂ)
    (to_qExpansion h f)

lemma cuspFunction_qpow_mul_eq {h : ℝ} (hh : 0 < h) (f : ℍ → ℂ)
    {n : ℕ} {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) :
    cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ) q = q ^ n * cuspFunction h f q := by
  have him := Periodic.im_invQParam_pos_of_norm_lt_one hh hqnorm hq0
  have hleft : cuspFunction h (fun τ : ℍ ↦ (𝕢 h τ) ^ n * f τ) q =
      (fun τ : ℍ ↦ (𝕢 h τ) ^ n * f τ) (ofComplex (Periodic.invQParam h q)) := by
    simpa [cuspFunction] using (Periodic.cuspFunction_eq_of_nonzero h
      (((fun τ : ℍ ↦ (𝕢 h τ) ^ n * f τ) ∘ UpperHalfPlane.ofComplex)) hq0)
  have hright : cuspFunction h f q = f (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) := by
    simpa [cuspFunction] using
      (Periodic.cuspFunction_eq_of_nonzero h (f ∘ UpperHalfPlane.ofComplex) hq0)
  have hqparam : 𝕢 h (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) = q := by
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos him] using
      (Periodic.qParam_right_inv hh.ne' hq0)
  calc
  _ = (fun τ : ℍ ↦ (𝕢 h τ) ^ n * f τ) (ofComplex (Periodic.invQParam h q)) := hleft
  _ = q ^ n * f (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) := by simp [hqparam]
  _ = _ := by simp [hright]

/-- If the cusp function of `f` agrees with `G` on a punctured neighbourhood of `0` and `G` is
continuous at `0`, then the (`limUnder`-defined) value of the cusp function at `0` is `G 0`. -/
lemma cuspFunction_apply_zero_eq {h : ℝ} {f : ℍ → ℂ} {G : ℂ → ℂ}
    (hEq : cuspFunction h f =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] G) (hG : ContinuousAt G 0) :
    cuspFunction h f 0 = G 0 :=
  calc
    cuspFunction h f 0 = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) (cuspFunction h f) := by
      simpa [cuspFunction] using
        Periodic.cuspFunction_zero_eq_limUnder_nhds_ne (h := h)
          (f := f ∘ UpperHalfPlane.ofComplex)
    _ = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) G := congrArg lim (Filter.map_congr hEq)
    _ = G 0 := (tendsto_nhdsWithin_of_tendsto_nhds hG.tendsto).limUnder_eq

/-- If the cusp function of `f` agrees on a punctured neighbourhood of `0` with a function `G`
analytic at `0`, then the cusp function is itself analytic at `0`. -/
lemma analyticAt_cuspFunction_of_eventuallyEq {h : ℝ} {f : ℍ → ℂ} {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 0) (hEq : cuspFunction h f =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] G) :
    AnalyticAt ℂ (cuspFunction h f) 0 :=
  hG.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hEq
    (cuspFunction_apply_zero_eq hEq hG.continuousAt)).symm

lemma analyticAt_cuspFunction_of_not_pos {h : ℝ} {f : ℍ → ℂ} (hh : h ≤ 0) :
    AnalyticAt ℂ (cuspFunction h f) 0 := by
  let τ0 : ℍ := Classical.choice inferInstance
  refine analyticAt_cuspFunction_of_eventuallyEq (G := fun _ ↦ f τ0) analyticAt_const ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one),
    self_mem_nhdsWithin] with q hqnorm hq
  have him_nonpos : Complex.im (Periodic.invQParam h q) ≤ 0 := by
    rw [Periodic.im_invQParam]
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by linarith) (by positivity))
      (Real.log_nonpos (norm_nonneg _) (mem_ball_zero_iff.mp hqnorm).le)
  have hof : UpperHalfPlane.ofComplex (Periodic.invQParam h q) = τ0 := by
    simpa [τ0] using UpperHalfPlane.ofComplex_apply_of_im_nonpos him_nonpos
  rw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ (Set.mem_compl_singleton_iff.mp hq)]
  simp [hof]

lemma analyticAt_cuspFunction_poleRemoved {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    AnalyticAt ℂ (cuspFunction h (poleRemoved h f)) 0 := by
  by_cases hh : 0 < h
  · have hEq_shift : cuspFunction h (poleRemoved h f) =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        fun q ↦ q ^ poleOrder h f * cuspFunction h f q := by
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one),
        self_mem_nhdsWithin] with q hqnorm hq
      simpa [UpperHalfPlane.poleRemoved] using
        cuspFunction_qpow_mul_eq (h := h) hh (f := f) (n := poleOrder h f)
          (Set.mem_compl_singleton_iff.mp hq) (mem_ball_zero_iff.mp hqnorm)
    cases ho : meromorphicOrderAt (cuspFunction h f) (0 : ℂ) with
    | top =>
        refine analyticAt_cuspFunction_of_eventuallyEq (G := fun _ ↦ (0 : ℂ))
          analyticAt_const ?_
        have hzero : cuspFunction h f =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun _ ↦ (0 : ℂ) := by
          simpa using meromorphicOrderAt_eq_top_iff.1 ho
        filter_upwards [hEq_shift, hzero] with q hq hqzero
        simp [hq, hqzero]
    | coe k =>
        obtain ⟨g, hg_an, hg_ne, hg_eq0⟩ := (meromorphicOrderAt_eq_int_iff hmero).1 ho
        have hg_eq :
            cuspFunction h f =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q ↦ q ^ k * g q := by
          filter_upwards [hg_eq0] with q hq
          simpa [sub_zero, smul_eq_mul] using hq
        by_cases hk : k < 0
        · have hMZ : (poleOrder h f : ℤ) = -k := by
            have hk' : ((k : WithTop ℤ) < 0) := by exact_mod_cast hk
            simp [UpperHalfPlane.poleOrder, ho, hk',
              Int.ofNat_natAbs_of_nonpos (le_of_lt hk)]
          refine analyticAt_cuspFunction_of_eventuallyEq hg_an ?_
          filter_upwards [hEq_shift, hg_eq, self_mem_nhdsWithin] with q hq hqg hqne
          have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hqne
          rw [hq, hqg, ← zpow_natCast q (poleOrder h f), ← mul_assoc, ← zpow_add₀ hq0]
          simp [hMZ]
        · lift k to ℕ using le_of_not_gt hk with n hn
          have hM0 : poleOrder h f = 0 := by
            simp [UpperHalfPlane.poleOrder, ho]
          have hG_an : AnalyticAt ℂ (fun q : ℂ ↦ q ^ n * g q) 0 :=
            (analyticAt_id.pow n).mul hg_an
          refine analyticAt_cuspFunction_of_eventuallyEq hG_an ?_
          filter_upwards [hEq_shift, hg_eq] with q hq hqg
          simp [hq, hqg, hM0]
  · exact analyticAt_cuspFunction_of_not_pos (le_of_not_gt hh)

/-- A cusp-meromorphic function is analytic at the cusp iff its pole order vanishes. -/
lemma analyticAt_cuspFunction_iff_poleOrder_eq_zero {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    AnalyticAt ℂ (cuspFunction h f) 0 ↔ poleOrder h f = 0 := by
  constructor
  · intro han
    have hnonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 :=
      han.meromorphicOrderAt_nonneg
    have hnotlt : ¬ meromorphicOrderAt (cuspFunction h f) 0 < 0 := not_lt_of_ge hnonneg
    simp [UpperHalfPlane.poleOrder, hnotlt]
  · intro h0
    have hfun : poleRemoved h f = f := by
      funext τ
      simp [UpperHalfPlane.poleRemoved, h0]
    simpa [hfun] using
      (analyticAt_cuspFunction_poleRemoved (h := h) (f := f) hmero)

lemma cuspFunction_poleRemoved_eq {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) :
    cuspFunction h (poleRemoved h f) q = q ^ poleOrder h f * cuspFunction h f q := by
  by_cases hh : 0 < h
  · simpa [UpperHalfPlane.poleRemoved] using
      (cuspFunction_qpow_mul_eq (h := h) hh (f := f) (n := poleOrder h f) hq0 hqnorm)
  · have hpole : poleOrder h f = 0 := by
      exact (analyticAt_cuspFunction_iff_poleOrder_eq_zero (h := h) (f := f) hmero).1
        (analyticAt_cuspFunction_of_not_pos (h := h) (f := f) (le_of_not_gt hh))
    have hfun : poleRemoved h f = f := by
      funext τ
      simp [UpperHalfPlane.poleRemoved, hpole]
    simp [hfun, hpole]

lemma laurentqExpansion.coeff_eq_HahnSeries_add (h : ℝ) (f : ℍ → ℂ) {n : ℤ} :
    (laurentqExpansion h f).coeff n =
    ((HahnSeries.ofPowerSeries ℤ ℂ) (to_qExpansion h f)).coeff (n + poleOrder h f) := by
  rw [laurentqExpansion]
  simpa [UpperHalfPlane.poleOrder, sub_eq_add_neg] using
    (HahnSeries.coeff_single_mul
      (r := (1 : ℂ))
      (x := (HahnSeries.ofPowerSeries ℤ ℂ) (to_qExpansion h f))
      (a := n) (b := -poleOrder h f))

lemma laurentqExpansion.coeff_eq_zero_of_lt {h : ℝ} {f : ℍ → ℂ} {n : ℤ}
    (hn : n < -(poleOrder h f : ℤ)) : (laurentqExpansion h f).coeff n = 0 := by
  let m : ℤ := poleOrder h f
  have hneg : n + m < 0 := by
    linarith
  simpa [laurentqExpansion.coeff_eq_HahnSeries_add, m, hneg]
    using (PowerSeries.coeff_coe (f := to_qExpansion h f) (i := n + m))

lemma laurentqExpansion.coeff_neg_poleOrder_add (h : ℝ) (f : ℍ → ℂ) (n : ℕ) :
    (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ) + n) = (to_qExpansion h f).coeff n := by
  have hnonneg : (0 : ℤ) ≤ n := by
    exact_mod_cast Nat.zero_le n
  have hnotneg : ¬ ((n : ℤ) < 0) := not_lt_of_ge hnonneg
  calc
    (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ) + n)
        = ((HahnSeries.ofPowerSeries ℤ ℂ) (to_qExpansion h f)).coeff (n : ℤ) := by
            simp [laurentqExpansion.coeff_eq_HahnSeries_add]
    _ = (to_qExpansion h f).coeff n := by
          rw [PowerSeries.coeff_coe (f := to_qExpansion h f) (i := (n : ℤ))]
          simp [hnotneg]

lemma laurentqExpansion.coeff_of_geq {h : ℝ} {f : ℍ → ℂ} {n : ℤ}
    (hn : -(poleOrder h f : ℤ) ≤ n) :
    (laurentqExpansion h f).coeff n =
      (to_qExpansion h f).coeff (Int.toNat (n + poleOrder h f)) := by
  have hnonneg : 0 ≤ n + poleOrder h f := by
    linarith
  have hrewrite :
      (-(poleOrder h f : ℤ) + Int.toNat (n + poleOrder h f) : ℤ) = n := by
    rw [Int.toNat_of_nonneg hnonneg]
    linarith
  calc
    (laurentqExpansion h f).coeff n
        = (laurentqExpansion h f).coeff
            (-(poleOrder h f : ℤ) + Int.toNat (n + poleOrder h f)) := by
                conv_lhs => rw [hrewrite.symm]
    _ = (to_qExpansion h f).coeff (Int.toNat (n + poleOrder h f)) :=
          laurentqExpansion.coeff_neg_poleOrder_add (h := h) (f := f)
            (Int.toNat (n + poleOrder h f))

lemma laurentqExpansion.coeff_of_qExpansion (h : ℝ) (f : ℍ → ℂ) (n : ℤ) :
    (laurentqExpansion h f).coeff n = if n < -(poleOrder h f : ℤ) then 0
    else (to_qExpansion h f).coeff (Int.toNat (n + poleOrder h f)) := by
  by_cases hlt : n < -(poleOrder h f : ℤ)
  · simp [hlt, laurentqExpansion.coeff_eq_zero_of_lt (h := h) (f := f) hlt]
  · simp [hlt, laurentqExpansion.coeff_of_geq (h := h) (f := f)
      (hn := le_of_not_gt hlt)]

lemma laurentqExpansion.coeff_neg_poleOrder (h : ℝ) (f : ℍ → ℂ) :
    (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ)) = (to_qExpansion h f).coeff 0 := by
  simpa using laurentqExpansion.coeff_neg_poleOrder_add (h := h) (f := f) 0

lemma laurentqExpansion.coeff_zero (h : ℝ) (f : ℍ → ℂ) :
    (laurentqExpansion h f).coeff 0 = (to_qExpansion h f).coeff (poleOrder h f) := by
  have hn : -(poleOrder h f : ℤ) ≤ (0 : ℤ) := by
    exact neg_nonpos.mpr (by exact_mod_cast Nat.zero_le (poleOrder h f))
  simpa using laurentqExpansion.coeff_of_geq (h := h) (f := f) (n := 0) (hn := hn)

lemma meromorphicOrderAt_cuspFunction_eq_neg_poleOrder {h : ℝ} {f : ℍ → ℂ}
    (h0 : poleOrder h f ≠ 0) :
    meromorphicOrderAt (cuspFunction h f) 0 = -(poleOrder h f : ℤ) := by
  unfold UpperHalfPlane.poleOrder at h0 ⊢
  set o : WithTop ℤ := meromorphicOrderAt (cuspFunction h f) 0
  have ho_lt : o < 0 := by
    by_contra ho_ge
    simp [o, ho_ge] at h0
  cases ho : o with
  | top =>
      simp [ho] at ho_lt
  | coe k =>
      rw [ho] at ho_lt
      have hk : k < 0 := by
        exact_mod_cast ho_lt
      have hk_le : k ≤ 0 := le_of_lt hk
      have hnatAbs : ((Int.natAbs k : ℕ) : ℤ) = -k := Int.ofNat_natAbs_of_nonpos hk_le
      simp [hk, hnatAbs]

lemma to_qExpansion_coeff_zero_ne {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    (to_qExpansion h f).coeff 0 ≠ 0 := by
  have hGan : AnalyticAt ℂ (cuspFunction h (poleRemoved h f)) 0 :=
    analyticAt_cuspFunction_poleRemoved (h := h) (f := f) hmero
  have hEq : cuspFunction h f =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun z ↦
      (z - 0) ^ (meromorphicOrderAt (cuspFunction h f) 0).untop₀ •
        cuspFunction h (poleRemoved h f) z := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one),
      self_mem_nhdsWithin] with q hq hq'
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq'
    rw [cuspFunction_poleRemoved_eq hmero hq0 (mem_ball_zero_iff.mp hq),
      meromorphicOrderAt_cuspFunction_eq_neg_poleOrder h0]
    simp only [sub_zero, smul_eq_mul, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
      WithTop.untop₀_coe]
    rw [← zpow_natCast q (poleOrder h f), ← mul_assoc, ← zpow_add₀ hq0, neg_add_cancel,
      zpow_zero, one_mul]
  have hne := hmero.meromorphicTrailingCoeffAt_ne_zero (by
    rw [meromorphicOrderAt_cuspFunction_eq_neg_poleOrder h0]
    exact WithTop.coe_ne_top)
  rw [hGan.meromorphicTrailingCoeffAt_of_eq_nhdsNE hEq] at hne
  simpa [UpperHalfPlane.to_qExpansion, qExpansion_coeff] using hne

lemma to_qExpansion_ne_zero {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    to_qExpansion h f ≠ 0 := by
  intro hq
  have hcoeff := to_qExpansion_coeff_zero_ne (h := h) (f := f) hmero h0
  simp [hq] at hcoeff

lemma laurentqExpansion.ne_zero {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    laurentqExpansion h f ≠ 0 := by
  rw [laurentqExpansion]
  refine mul_ne_zero ?_ ?_
  · exact HahnSeries.single_ne_zero one_ne_zero
  · intro hq
    have hq' : (HahnSeries.ofPowerSeries ℤ ℂ) (to_qExpansion h f) =
        (HahnSeries.ofPowerSeries ℤ ℂ) 0 := by
      simpa using hq
    exact to_qExpansion_ne_zero (h := h) (f := f) hmero h0
      (HahnSeries.ofPowerSeries_injective hq')

lemma laurentqExpansion.poleOrder_to_order {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    poleOrder h f = -(laurentqExpansion h f).order := by
  have hcoeff :
      (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ)) ≠ 0 := by
    rw [laurentqExpansion.coeff_neg_poleOrder (h := h) (f := f)]
    exact to_qExpansion_coeff_zero_ne (h := h) (f := f) hmero h0
  have horder_le : (laurentqExpansion h f).order ≤ -(poleOrder h f : ℤ) :=
    HahnSeries.order_le_of_coeff_ne_zero hcoeff
  have horder_ge : -(poleOrder h f : ℤ) ≤ (laurentqExpansion h f).order := by
    by_contra hlt
    have hzero :
        (laurentqExpansion h f).coeff (laurentqExpansion h f).order = 0 := by
      exact laurentqExpansion.coeff_eq_zero_of_lt (h := h) (f := f) (lt_of_not_ge hlt)
    exact (HahnSeries.coeff_order_eq_zero.not.2 (laurentqExpansion.ne_zero hmero h0)) hzero
  have horder : (laurentqExpansion h f).order = -(poleOrder h f : ℤ) :=
    le_antisymm horder_le horder_ge
  simpa using (congrArg Neg.neg horder).symm

lemma laurentqExpansion.to_qExpansion_eq_powerSeriesPart {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    to_qExpansion h f = (laurentqExpansion h f).powerSeriesPart := by
  ext n
  rw [LaurentSeries.powerSeriesPart_coeff]
  have hm : (poleOrder h f : ℤ) = -(laurentqExpansion h f).order :=
    laurentqExpansion.poleOrder_to_order (h := h) (f := f) hmero h0
  have horder : (laurentqExpansion h f).order = -(poleOrder h f : ℤ) := by
    simpa using (congrArg Neg.neg hm).symm
  rw [horder]
  simpa using (laurentqExpansion.coeff_neg_poleOrder_add (h := h) (f := f) n).symm


lemma laurentqExpansion.eq_qExpansion_iff {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    laurentqExpansion h f = qExpansion h f ↔ poleOrder h f = 0 := by
  constructor
  · intro heq
    by_contra h0
    have hcoeff :
        (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ)) ≠ 0 := by
      rw [laurentqExpansion.coeff_neg_poleOrder (h := h) (f := f)]
      exact to_qExpansion_coeff_zero_ne (h := h) (f := f) hmero h0
    have hnatpos : 0 < poleOrder h f := Nat.pos_of_ne_zero h0
    have hpos : 0 < (poleOrder h f : ℤ) := by
      exact_mod_cast hnatpos
    have hneg : -(poleOrder h f : ℤ) < 0 := by
      linarith
    have hqcoeff :
        (qExpansion h f : LaurentSeries ℂ).coeff (-(poleOrder h f : ℤ)) = 0 := by
      simpa [hneg, hnatpos] using
        (PowerSeries.coeff_coe (f := qExpansion h f) (i := -(poleOrder h f : ℤ)))
    have hEqCoeff := congrArg
      (fun g : LaurentSeries ℂ ↦ g.coeff (-(poleOrder h f : ℤ))) heq
    have hEqCoeff' :
        (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ)) =
          (qExpansion h f : LaurentSeries ℂ).coeff (-(poleOrder h f : ℤ)) := by
      simpa using hEqCoeff
    rw [hqcoeff] at hEqCoeff'
    exact hcoeff hEqCoeff'
  · intro h0
    have hfun : (poleRemoved h f) = (f : ℍ → ℂ) := by
      funext τ
      simp [UpperHalfPlane.poleRemoved, h0]
    have hqexp : to_qExpansion h f = qExpansion h f := by
      rw [UpperHalfPlane.to_qExpansion, hfun]
    simp [laurentqExpansion, h0, hqexp]


lemma qExpansion_coeff_eq_circleIntegral_of_differentiableOn
    {g : ℍ → ℂ} {R : ℝ} (hR : 0 < R)
    (hDiff : DifferentiableOn ℂ (cuspFunction h g) (Metric.closedBall 0 R)) (n : ℕ) :
    (qExpansion h g).coeff n =
      ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h g z / z ^ (n + 1)) := by
  have hci := hDiff.circleIntegral_one_div_sub_center_pow_smul hR n
  calc
    (qExpansion h g).coeff n = (↑n.factorial)⁻¹ * iteratedDeriv n (cuspFunction h g) 0 := by
      simp [qExpansion]
    _ = (2 * π * I)⁻¹ *
        ((2 * π * I) / (↑n.factorial) * iteratedDeriv n (cuspFunction h g) 0) := by
      field_simp [two_pi_I_ne_zero]
    _ = (2 * π * I)⁻¹ *
          (∮ z in C(0, R), (1 / (z - 0) ^ (n + 1)) • cuspFunction h g z) := by
            have hci' := congrArg (fun t : ℂ => (2 * π * I)⁻¹ * t) hci
            simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hci'.symm
    _ = ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h g z / z ^ (n + 1)) := by
          simp [smul_eq_mul, sub_zero, div_eq_inv_mul, mul_assoc, mul_left_comm, mul_comm]

/-- There is a radius `0 < R < 1` on whose closed disc the pole-removed cusp function is
holomorphic, supplying a contour for the Cauchy coefficient formula. -/
lemma exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) : ∃ R : ℝ, 0 < R ∧ R < 1 ∧
      DifferentiableOn ℂ (cuspFunction h (poleRemoved h f)) (Metric.closedBall 0 R) := by
  rcases (analyticAt_cuspFunction_poleRemoved (h := h) (f := f) hmero).exists_ball_analyticOnNhd
    with ⟨R0, hR0pos, hR0⟩
  let R : ℝ := min (R0 / 2) (1 / 2)
  have hRpos : 0 < R := by
    refine lt_min ?_ ?_
    · linarith
    · norm_num
  have hRlt1 : R < 1 := by
    have hRle : R ≤ (1 / 2 : ℝ) := min_le_right _ _
    linarith
  have hRltR0 : R < R0 := by
    calc
      R ≤ R0 / 2 := min_le_left _ _
      _ < R0 := by linarith
  refine ⟨R, hRpos, hRlt1, ?_⟩
  exact (hR0.analyticOn.differentiableOn).mono (Metric.closedBall_subset_ball hRltR0)

/-- On a circle of radius `0 < R < 1`, dividing the pole-removed cusp function by `z ^ a` is
the same as dividing the original cusp function by `z ^ (a - poleOrder h f)`. -/
private lemma cuspFunction_poleRemoved_div_zpow_eq_of_mem_sphere {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) {R : ℝ} (hRpos : 0 < R) (hRlt1 : R < 1)
    {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) R) (a : ℤ) :
    cuspFunction h (poleRemoved h f) z / z ^ a =
      cuspFunction h f z / z ^ (a - (poleOrder h f : ℤ)) := by
  have hznorm : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [norm_zero] at hznorm
    linarith
  have hzlt : ‖z‖ < 1 := by rw [hznorm]; exact hRlt1
  rw [cuspFunction_poleRemoved_eq hmero hz0 hzlt, ← zpow_natCast z, zpow_sub₀ hz0,
    div_div_eq_mul_div]
  ring

/-- Below the principal-part cutoff the contour integrand of the cusp function extends
holomorphically over the disc, so its circle integral vanishes. -/
private lemma circleIntegral_cuspFunction_div_zpow_eq_zero {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) {R : ℝ} (hRpos : 0 < R) (hRlt1 : R < 1)
    (hDiff : DifferentiableOn ℂ (cuspFunction h (poleRemoved h f)) (Metric.closedBall 0 R))
    {n : ℤ} (hn : n < -(poleOrder h f : ℤ)) :
    (∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1)) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = -(n + poleOrder h f + 1) :=
    ⟨_, Int.toNat_of_nonneg (by linarith)⟩
  have hDiffF : DifferentiableOn ℂ (fun z : ℂ ↦ z ^ k * cuspFunction h (poleRemoved h f) z)
      (Metric.closedBall (0 : ℂ) R) := (differentiableOn_id.pow k).mul hDiff
  have hEqOn : Set.EqOn (fun z : ℂ ↦ cuspFunction h f z / z ^ (n + 1))
      (fun z : ℂ ↦ z ^ k * cuspFunction h (poleRemoved h f) z) (Metric.sphere (0 : ℂ) R) := by
    intro z hz
    have hdiv := cuspFunction_poleRemoved_div_zpow_eq_of_mem_sphere hmero hRpos hRlt1 hz
      (n + poleOrder h f + 1)
    rw [show (n + (poleOrder h f : ℤ) + 1 - poleOrder h f : ℤ) = n + 1 by ring] at hdiv
    change cuspFunction h f z / z ^ (n + 1) = z ^ k * cuspFunction h (poleRemoved h f) z
    rw [← hdiv, div_eq_mul_inv, ← zpow_neg, ← hk, zpow_natCast, mul_comm]
  rw [circleIntegral.integral_congr hRpos.le hEqOn]
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hRpos.le
    countable_empty hDiffF.continuousOn fun z hz ↦
      ((hDiffF.mono Metric.ball_subset_closedBall) z hz.1).differentiableAt
        (isOpen_ball.mem_nhds hz.1)

/-- Above the principal-part cutoff the contour integrals of the pole-removed and the original
cusp functions agree after the exponent shift by `poleOrder h f`. -/
private lemma circleIntegral_cuspFunction_poleRemoved_div_pow_eq {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) {R : ℝ} (hRpos : 0 < R) (hRlt1 : R < 1)
    {m : ℕ} {n : ℤ} (hm : (m : ℤ) = n + poleOrder h f) :
    (∮ z in C(0, R), cuspFunction h (poleRemoved h f) z / z ^ (m + 1)) =
      ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1) := by
  refine circleIntegral.integral_congr hRpos.le fun z hz ↦ ?_
  have hdiv := cuspFunction_poleRemoved_div_zpow_eq_of_mem_sphere hmero hRpos hRlt1 hz
    ((m : ℤ) + 1)
  rw [show ((m : ℤ) + 1 - poleOrder h f : ℤ) = n + 1 by rw [hm]; ring] at hdiv
  change cuspFunction h (poleRemoved h f) z / z ^ (m + 1) = cuspFunction h f z / z ^ (n + 1)
  rw [← zpow_natCast z (m + 1), Nat.cast_add, Nat.cast_one, hdiv]

/-- Cauchy integral formula for the Laurent q-expansion: on a suitable circle every
integer-indexed coefficient is the standard contour integral of the cusp function. -/
lemma laurentqExpansion_coeff_eq_circleIntegral {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧ ∀ n : ℤ,
      (laurentqExpansion h f).coeff n =
        ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1)) := by
  obtain ⟨R, hRpos, hRlt1, hDiff⟩ :=
    exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt (h := h) (f := f) hmero
  refine ⟨R, hRpos, hRlt1, fun n ↦ ?_⟩
  by_cases hn : n < -(poleOrder h f : ℤ)
  · rw [laurentqExpansion.coeff_eq_zero_of_lt hn,
      circleIntegral_cuspFunction_div_zpow_eq_zero hmero hRpos hRlt1 hDiff hn, mul_zero]
  · have hm : ((Int.toNat (n + poleOrder h f) : ℕ) : ℤ) = n + poleOrder h f :=
      Int.toNat_of_nonneg (by linarith [le_of_not_gt hn])
    rw [laurentqExpansion.coeff_of_geq (le_of_not_gt hn), UpperHalfPlane.to_qExpansion,
      qExpansion_coeff_eq_circleIntegral_of_differentiableOn hRpos hDiff _,
      circleIntegral_cuspFunction_poleRemoved_div_pow_eq hmero hRpos hRlt1 hm]
