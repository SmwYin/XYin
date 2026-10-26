/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries

/-!
# Laurent q-expansions at the cusp

Mathlib's `UpperHalfPlane.qExpansion` handles functions whose cusp function is analytic at
`q = 0`. This file extends the theory to functions that are merely *meromorphic* at the cusp:
multiplying by `q ^ poleOrder` removes the pole, and the Taylor series of the pole-removed
function is reassembled into a Laurent series.

## Main definitions

* `UpperHalfPlane.poleOrder`: the order of the pole of `cuspFunction h f` at `q = 0`.
* `UpperHalfPlane.poleRemoved`: the pole-cancelled function `𝕢 h τ ^ poleOrder h f * f τ`.
* `UpperHalfPlane.toQExpansion`: the q-expansion of the pole-removed function.
* `UpperHalfPlane.laurentqExpansion`: the Laurent q-expansion of `f` at the cusp.

## Main results

* `cuspFunction_eventuallyEq_comp`, `cuspFunction_comp_eventuallyEq`,
  `cuspFunction_comp₂_eventuallyEq`: away from `q = 0` the cusp function is computed pointwise,
  so it commutes with every pointwise operation on a punctured neighbourhood of `0`.
* `meromorphicAt_cuspFunction_add`, `_mul`, `_neg`, `_sub`, `_const_mul`, `_pow`, `_inv`,
  `_div`, `_polynomial_eval`, `_finset_sum`, `_finset_prod`: meromorphy at the cusp is closed
  under pointwise operations.
* `analyticAt_cuspFunction_poleRemoved`: multiplying by `q ^ poleOrder` removes the pole.
* `meromorphicAt_cuspFunction_of_nat_mul`: meromorphy at the cusp descends from a natural
  multiple of the period back to the period itself.
* `laurentqExpansion_coeff_eq_circleIntegral`: every Laurent coefficient is given by the
  Cauchy contour-integral formula.
-/

open ModularForm Complex Function Matrix.SpecialLinearGroup Metric
  ModularFormClass SlashInvariantFormClass Real Set Filter LaurentSeries
open UpperHalfPlane hiding I
open scoped Topology

local notation "𝕢" => Periodic.qParam

noncomputable section

variable {h : ℝ}

/-! ### The punctured unit disc and the transport lemmas -/

/-- The open unit disc is a punctured neighbourhood of `0`. -/
lemma norm_lt_one_mem_nhdsNE_zero : {q : ℂ | ‖q‖ < 1} ∈ 𝓝[≠] (0 : ℂ) :=
  nhdsWithin_le_nhds <| by
    simpa [Metric.ball, dist_eq_norm] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one

/-- Points of a small punctured neighbourhood of `0` are nonzero and lie in the unit disc. -/
lemma eventually_ne_zero_and_norm_lt_one : ∀ᶠ q : ℂ in 𝓝[≠] 0, q ≠ 0 ∧ ‖q‖ < 1 := by
  filter_upwards [self_mem_nhdsWithin, norm_lt_one_mem_nhdsNE_zero] with q hq hqn
  exact ⟨hq, hqn⟩

/-- Away from `q = 0` the cusp function is computed pointwise. -/
lemma cuspFunction_apply_of_ne_zero (h : ℝ) (f : ℍ → ℂ) {q : ℂ} (hq : q ≠ 0) :
    cuspFunction h f q = f (ofComplex (Periodic.invQParam h q)) :=
  Periodic.cuspFunction_eq_of_nonzero _ _ hq

/-- **Transport lemma**: on a punctured neighbourhood of `0`, the cusp function of `f` is
`f ∘ ofComplex ∘ invQParam h`. -/
lemma cuspFunction_eventuallyEq_comp (h : ℝ) (f : ℍ → ℂ) :
    cuspFunction h f =ᶠ[𝓝[≠] 0] f ∘ ofComplex ∘ Periodic.invQParam h := by
  filter_upwards [self_mem_nhdsWithin] with q hq using cuspFunction_apply_of_ne_zero h f hq

/-- The cusp function commutes with post-composition, on a punctured neighbourhood of `0`. -/
lemma cuspFunction_comp_eventuallyEq (h : ℝ) (φ : ℂ → ℂ) (f : ℍ → ℂ) :
    cuspFunction h (fun τ ↦ φ (f τ)) =ᶠ[𝓝[≠] 0] fun q ↦ φ (cuspFunction h f q) := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [cuspFunction_apply_of_ne_zero h _ hq]

/-- The cusp function commutes with binary pointwise operations, on a punctured neighbourhood
of `0`. -/
lemma cuspFunction_comp₂_eventuallyEq (h : ℝ) (op : ℂ → ℂ → ℂ) (f g : ℍ → ℂ) :
    cuspFunction h (fun τ ↦ op (f τ) (g τ)) =ᶠ[𝓝[≠] 0]
      fun q ↦ op (cuspFunction h f q) (cuspFunction h g q) := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [cuspFunction_apply_of_ne_zero h _ hq]

/-- The cusp function of a constant function is that constant. (Not `@[simp]`: it would turn
`meromorphicAt_cuspFunction_const` into `True` under `simpa`, while goals stated with
`(1 : ℍ → ℂ)` or `(0 : ℍ → ℂ)` keep their form.) -/
lemma cuspFunction_const (h : ℝ) (a : ℂ) :
    cuspFunction h (fun _ : ℍ ↦ a) = fun _ ↦ a := by
  ext q
  rcases eq_or_ne q 0 with rfl | hq
  · simpa [cuspFunction, Periodic.cuspFunction, Function.comp_def] using
      tendsto_const_nhds.limUnder_eq
  · exact cuspFunction_apply_of_ne_zero h _ hq

/-- The cusp function of a constant function is analytic at `0`. -/
lemma analyticAt_cuspFunction_const (h : ℝ) (a : ℂ) :
    AnalyticAt ℂ (cuspFunction h (fun _ : ℍ ↦ a)) 0 := by
  rw [cuspFunction_const]
  exact analyticAt_const

/-- The q-expansion of a constant function is the corresponding constant power series. -/
@[simp] lemma qExpansion_const (h : ℝ) (a : ℂ) :
    qExpansion h (fun _ : ℍ ↦ a) = PowerSeries.C a := by
  ext m
  rcases eq_or_ne m 0 with rfl | hm <;>
    simp [qExpansion_coeff, cuspFunction_const, iteratedDeriv_const, PowerSeries.coeff_C, *]

/-! ### Meromorphy at the cusp is closed under pointwise operations -/

/-- Cusp meromorphicity is preserved by pointwise addition. -/
lemma meromorphicAt_cuspFunction_add {h : ℝ} {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    MeromorphicAt (cuspFunction h (fun τ ↦ f τ + g τ)) 0 :=
  (hf.add hg).congr (cuspFunction_comp₂_eventuallyEq h (· + ·) f g).symm

/-- Cusp meromorphicity is preserved by pointwise multiplication. -/
lemma meromorphicAt_cuspFunction_mul {h : ℝ} {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    MeromorphicAt (cuspFunction h (fun τ ↦ f τ * g τ)) 0 :=
  (hf.mul hg).congr (cuspFunction_comp₂_eventuallyEq h (· * ·) f g).symm

/-- A constant function is meromorphic in every cusp parameter. -/
lemma meromorphicAt_cuspFunction_const (h : ℝ) (a : ℂ) :
    MeromorphicAt (cuspFunction h (fun _ : ℍ ↦ a)) 0 :=
  (analyticAt_cuspFunction_const h a).meromorphicAt

/-- Cusp meromorphicity is preserved by pointwise negation. -/
lemma meromorphicAt_cuspFunction_neg {h : ℝ} {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    MeromorphicAt (cuspFunction h (fun τ ↦ -f τ)) 0 :=
  hf.neg.congr (cuspFunction_comp_eventuallyEq h (-·) f).symm

/-- Cusp meromorphicity is preserved by pointwise subtraction. -/
lemma meromorphicAt_cuspFunction_sub {h : ℝ} {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    MeromorphicAt (cuspFunction h (fun τ ↦ f τ - g τ)) 0 :=
  (hf.sub hg).congr (cuspFunction_comp₂_eventuallyEq h (· - ·) f g).symm

/-- Cusp meromorphicity is preserved by multiplication with a constant. -/
lemma meromorphicAt_cuspFunction_const_mul {h : ℝ} (a : ℂ) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    MeromorphicAt (cuspFunction h (fun τ ↦ a * f τ)) 0 :=
  ((MeromorphicAt.const a 0).mul hf).congr (cuspFunction_comp_eventuallyEq h (a * ·) f).symm

/-- Cusp meromorphicity is preserved by scalar multiplication. -/
lemma meromorphicAt_cuspFunction_smul {h : ℝ} (a : ℂ) {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    MeromorphicAt (cuspFunction h (a • f)) 0 :=
  meromorphicAt_cuspFunction_const_mul a hf

/-- Cusp meromorphicity is preserved by pointwise powers. -/
lemma meromorphicAt_cuspFunction_pow {h : ℝ} {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) (n : ℕ) :
    MeromorphicAt (cuspFunction h (fun τ ↦ f τ ^ n)) 0 :=
  (hf.pow n).congr (cuspFunction_comp_eventuallyEq h (· ^ n) f).symm

/-- Cusp meromorphicity is preserved by pointwise inversion. -/
lemma meromorphicAt_cuspFunction_inv {h : ℝ} {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    MeromorphicAt (cuspFunction h (fun τ ↦ (f τ)⁻¹)) 0 :=
  hf.inv.congr (cuspFunction_comp_eventuallyEq h (·⁻¹) f).symm

/-- Cusp meromorphicity is preserved by pointwise division. -/
lemma meromorphicAt_cuspFunction_div {h : ℝ} {f g : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    MeromorphicAt (cuspFunction h (fun τ ↦ f τ / g τ)) 0 :=
  (hf.div hg).congr (cuspFunction_comp₂_eventuallyEq h (· / ·) f g).symm

/-- Evaluating a fixed polynomial along a meromorphic function gives a meromorphic function. -/
theorem MeromorphicAt.polynomial_eval {𝕜 : Type*} [NontriviallyNormedField 𝕜] {g : 𝕜 → 𝕜}
    {x : 𝕜} (hg : MeromorphicAt g x) (P : Polynomial 𝕜) :
    MeromorphicAt (fun w ↦ P.eval (g w)) x := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add] using hP.fun_add hQ
  | monomial n a =>
      simpa only [Polynomial.eval_monomial] using (MeromorphicAt.const a x).fun_mul (hg.fun_pow n)

/-- Cusp meromorphicity is preserved by evaluating a polynomial. -/
lemma meromorphicAt_cuspFunction_polynomial_eval {h : ℝ} {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0) (P : Polynomial ℂ) :
    MeromorphicAt (cuspFunction h (fun τ ↦ P.eval (f τ))) 0 :=
  (hf.polynomial_eval P).congr (cuspFunction_comp_eventuallyEq h (fun x ↦ P.eval x) f).symm

/-- A finite pointwise sum of cusp-meromorphic functions is cusp-meromorphic. -/
lemma meromorphicAt_cuspFunction_finset_sum
    {ι : Type*} {h : ℝ} {s : Finset ι} {f : ι → ℍ → ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) :
    MeromorphicAt (cuspFunction h (∑ i ∈ s, f i)) 0 :=
  Finset.sum_induction _ (fun F ↦ MeromorphicAt (cuspFunction h F) 0)
    (fun _ _ ↦ meromorphicAt_cuspFunction_add) (meromorphicAt_cuspFunction_const h 0) hf

/-- A finite pointwise product of cusp-meromorphic functions is cusp-meromorphic. -/
lemma meromorphicAt_cuspFunction_finset_prod
    {ι : Type*} {h : ℝ} {s : Finset ι} {f : ι → ℍ → ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) :
    MeromorphicAt (cuspFunction h (∏ i ∈ s, f i)) 0 :=
  Finset.prod_induction _ (fun F ↦ MeromorphicAt (cuspFunction h F) 0)
    (fun _ _ ↦ meromorphicAt_cuspFunction_mul) (meromorphicAt_cuspFunction_const h 1) hf

/-! ### Changing the period by a natural factor -/

/-- A function on `ℍ` invariant under the translation `τ ↦ h +ᵥ τ` is `h`-periodic after
extension to `ℂ` by `ofComplex`. -/
lemma periodic_comp_ofComplex_of_vadd {f : ℍ → ℂ} {h : ℝ} (hf : ∀ τ : ℍ, f (h +ᵥ τ) = f τ) :
    Periodic (f ∘ ofComplex) h := by
  intro z
  by_cases hz : 0 < z.im
  · have hzadd : 0 < (z + (h : ℂ)).im := by simpa using hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hzadd,
      ofComplex_apply_of_im_pos hz]
    convert hf ⟨z, hz⟩ using 2
    ext
    simp [coe_vadd, add_comm]
  · have hz' : z.im ≤ 0 := le_of_not_gt hz
    have hzadd : (z + (h : ℂ)).im ≤ 0 := by simpa using hz'
    simp [ofComplex_apply_of_im_nonpos hzadd, ofComplex_apply_of_im_nonpos hz']

/-- The monomial `q ↦ c * q ^ r` (with `c ≠ 0`) vanishes to order exactly `r` at `0`. -/
lemma analyticOrderAt_const_mul_pow {𝕜 : Type*} [NontriviallyNormedField 𝕜] {c : 𝕜}
    (hc : c ≠ 0) (r : ℕ) : analyticOrderAt (fun q : 𝕜 ↦ c * q ^ r) 0 = r := by
  change analyticOrderAt ((fun _ : 𝕜 ↦ c) * id ^ r) 0 = r
  rw [analyticOrderAt_mul analyticAt_const (analyticAt_id.pow r),
    analyticAt_const.analyticOrderAt_eq_zero.2 hc, analyticOrderAt_pow analyticAt_id,
    analyticOrderAt_id, zero_add, nsmul_one]

/-- Precomposing with the monomial `q ↦ c * q ^ r` (with `c ≠ 0`, `r ≠ 0`) multiplies the
meromorphic order at `0` by `r`. -/
lemma meromorphicOrderAt_comp_const_mul_pow {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : 𝕜 → E} (hF : MeromorphicAt F 0) {c : 𝕜}
    (hc : c ≠ 0) {r : ℕ} (hr : r ≠ 0) :
    meromorphicOrderAt (F ∘ fun q ↦ c * q ^ r) 0 = meromorphicOrderAt F 0 * r := by
  have h0 : c * (0 : 𝕜) ^ r = 0 := by simp [hr]
  have hord : analyticOrderAt (fun q : 𝕜 ↦ c * q ^ r - c * 0 ^ r) 0 = r := by
    simpa [h0] using analyticOrderAt_const_mul_pow hc r
  have hnc : ¬ EventuallyConst (fun q : 𝕜 ↦ c * q ^ r) (𝓝 0) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hord]
    exact ENat.coe_ne_top r
  rw [MeromorphicAt.meromorphicOrderAt_comp (g := fun q ↦ c * q ^ r) (x := 0)
    (by simpa only [h0] using hF) (by fun_prop) hnc, hord, h0, ENat.map_coe]
  norm_cast

/-- Away from `0`, the cusp function for the period `m * h` is the cusp function for the period
`h` composed with `q ↦ q ^ m`. -/
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
    field_simp [two_pi_I_ne_zero]
    push_cast
    ring
  simpa [Function.comp_def, hinv] using
    (hfper.int_mul n (Periodic.invQParam ((m : ℝ) * h) q)).symm

/-- On a punctured neighbourhood of `0`, enlarging the period by `m` composes the cusp function
with `q ↦ q ^ m`. -/
lemma cuspFunction_nat_mul_eventuallyEq {h : ℝ} {m : ℕ} {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    cuspFunction ((m : ℝ) * h) f =ᶠ[𝓝[≠] 0] cuspFunction h f ∘ fun q ↦ q ^ m := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact cuspFunction_nat_mul_eq_cuspFunction_pow hfper hq

/-- Multiplying a cusp width by a nonzero natural number preserves meromorphicity at the
cusp. -/
lemma meromorphicAt_cuspFunction_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    MeromorphicAt (cuspFunction ((m : ℝ) * h) f) (0 : ℂ) := by
  have hmero0 : MeromorphicAt (cuspFunction h f) ((fun q : ℂ ↦ q ^ m) 0) := by
    simpa [hm] using hmero
  exact (hmero0.comp_analyticAt (g := fun q : ℂ ↦ q ^ m) (analyticAt_id.pow m)).congr
    (cuspFunction_nat_mul_eventuallyEq hfper).symm

private lemma eventually_differentiableAt_pow_mul_of_meromorphicAt_comp_pow_aux
    {g : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0)
    (h : MeromorphicAt (g ∘ fun q : ℂ ↦ q ^ m) 0) (n : ℕ) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (fun z ↦ z ^ n * g z) z := by
  letI : NeZero m := ⟨hm⟩
  have hcompAna :
      ∀ᶠ q : ℂ in 𝓝 (0 : ℂ), q = 0 ∨ AnalyticAt ℂ (g ∘ fun z : ℂ ↦ z ^ m) q := by
    have hpunctured := h.eventually_analyticAt
    rw [eventually_nhdsWithin_iff] at hpunctured
    filter_upwards [hpunctured] with q hq
    by_cases hq0 : q = 0
    · exact Or.inl hq0
    · exact Or.inr (hq hq0)
  let U : Set ℂ := {q | q = 0 ∨ AnalyticAt ℂ (g ∘ fun z : ℂ ↦ z ^ m) q}
  have hUimage : (fun q : ℂ ↦ q ^ m) '' U ∈ 𝓝 (0 : ℂ) := by
    simpa [hm] using
      (Complex.isOpenQuotientMap_pow m).isOpenMap.image_mem_nhds
        (show U ∈ 𝓝 0 from hcompAna)
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
    have hmn : m * n = (m - 1) * n + n := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)]
    convert (analyticAt_id.pow ((m - 1) * n)).mul hn using 1
    funext q
    simp only [G, Function.comp_apply, Pi.mul_apply, Pi.pow_apply, id, sub_zero, smul_eq_mul]
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
    MeromorphicAt (cuspFunction h f) (0 : ℂ) :=
  meromorphicAt_of_comp_pow hm (hmero.congr (cuspFunction_nat_mul_eventuallyEq hfper))

/-! ### The pole order -/

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

/-- For `r ≠ 0`, the pole order is `r` exactly when the meromorphic order at the cusp is
`-r`. -/
lemma poleOrder_eq_iff {h : ℝ} {f : ℍ → ℂ} {r : ℕ} (hr : r ≠ 0) :
    poleOrder h f = r ↔
      meromorphicOrderAt (cuspFunction h f) 0 = ((-(r : ℤ) : ℤ) : WithTop ℤ) := by
  refine ⟨fun hp ↦ ?_, poleOrder_eq_of_meromorphicOrderAt_eq⟩
  rw [poleOrder_eq_toNat_neg_meromorphicOrderAt] at hp
  cases ho : meromorphicOrderAt (cuspFunction h f) 0 with
  | top => exact absurd (by simpa [ho] using hp.symm) hr
  | coe k =>
      simp only [ho, WithTop.untopD_coe] at hp
      exact_mod_cast (by omega : k = -(r : ℤ))

/-- The pole order is less than `m > 0` exactly when the meromorphic order at the cusp is
greater than `-m`. -/
lemma poleOrder_lt_iff {h : ℝ} {f : ℍ → ℂ} {m : ℕ} (hm : 0 < m) :
    poleOrder h f < m ↔
      ((-(m : ℤ) : ℤ) : WithTop ℤ) < meromorphicOrderAt (cuspFunction h f) 0 := by
  rw [poleOrder_eq_toNat_neg_meromorphicOrderAt]
  cases meromorphicOrderAt (cuspFunction h f) 0 with
  | top => exact iff_of_true (by simpa using hm) (WithTop.coe_lt_top _)
  | coe k =>
      simp only [WithTop.untopD_coe, WithTop.coe_lt_coe]
      omega

/-- A function whose cusp function is analytic at `0` has no pole at the cusp. -/
lemma poleOrder_eq_zero_of_analyticAt {h : ℝ} {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) : poleOrder h f = 0 :=
  poleOrder_eq_zero_of_meromorphicOrderAt_nonneg hf.meromorphicOrderAt_nonneg

@[simp] lemma poleOrder_const (h : ℝ) (a : ℂ) : poleOrder h (fun _ : ℍ ↦ a) = 0 :=
  poleOrder_eq_zero_of_analyticAt (analyticAt_cuspFunction_const h a)

@[simp] lemma poleOrder_zero (h : ℝ) : poleOrder h (0 : ℍ → ℂ) = 0 :=
  poleOrder_const h 0

@[simp] lemma poleOrder_one (h : ℝ) : poleOrder h (1 : ℍ → ℂ) = 0 :=
  poleOrder_const h 1

/-- Negation does not change the pole order. -/
lemma poleOrder_neg (h : ℝ) (f : ℍ → ℂ) : poleOrder h (fun τ ↦ -f τ) = poleOrder h f := by
  rw [poleOrder_eq_toNat_neg_meromorphicOrderAt, poleOrder_eq_toNat_neg_meromorphicOrderAt,
    meromorphicOrderAt_congr (cuspFunction_comp_eventuallyEq h (-·) f)]
  exact congrArg (fun o : WithTop ℤ ↦ (-o.untopD 0).toNat) meromorphicOrderAt_neg.symm

/-- Enlarging the period by `m ≠ 0` multiplies the meromorphic order at the cusp by `m`. -/
lemma meromorphicOrderAt_cuspFunction_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    meromorphicOrderAt (cuspFunction ((m : ℝ) * h) f) (0 : ℂ) =
      meromorphicOrderAt (cuspFunction h f) (0 : ℂ) * m := by
  rw [meromorphicOrderAt_congr (cuspFunction_nat_mul_eventuallyEq hfper)]
  simpa using meromorphicOrderAt_comp_const_mul_pow hmero one_ne_zero hm

/-- Enlarging the period by `m ≠ 0` multiplies the pole order by `m`. -/
lemma poleOrder_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    poleOrder ((m : ℝ) * h) f = m * poleOrder h f := by
  rw [poleOrder_eq_toNat_neg_meromorphicOrderAt, poleOrder_eq_toNat_neg_meromorphicOrderAt,
    meromorphicOrderAt_cuspFunction_nat_mul hm hmero hfper, WithTop.untopD_zero_mul]
  change (-((meromorphicOrderAt (cuspFunction h f) 0).untopD 0 * (m : ℤ))).toNat = _
  rw [← neg_mul]
  by_cases ho : 0 ≤ -(meromorphicOrderAt (cuspFunction h f) 0).untopD 0
  · rw [Int.toNat_mul ho (Int.natCast_nonneg _)]
    simp [Nat.mul_comm]
  · rw [Int.toNat_eq_zero.mpr (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ho)
      (Int.natCast_nonneg _)), Int.toNat_eq_zero.mpr (le_of_not_ge ho), mul_zero]

/-! ### Removing the pole -/

/-- Multiplying `f` by `𝕢 h τ ^ poleOrder h f` cancels the pole at the cusp, yielding a
function whose cusp function is analytic at `q = 0`. -/
def UpperHalfPlane.poleRemoved (h : ℝ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun τ ↦ (𝕢 h τ) ^ (poleOrder h f) * f τ

/-- The q-expansion of the pole-removed function, i.e. the regular part of the Laurent
q-expansion shifted so that its constant term is the leading Laurent coefficient. -/
def UpperHalfPlane.toQExpansion (h : ℝ) (f : ℍ → ℂ) : PowerSeries ℂ :=
  qExpansion h (poleRemoved h f)

/-- The Laurent q-expansion of `f` at the cusp: `q ^ (-poleOrder h f)` times the power series
of the pole-removed function, realized in `LaurentSeries ℂ`. -/
def UpperHalfPlane.laurentqExpansion (h : ℝ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-(poleOrder h f : ℤ)) 1 * (HahnSeries.ofPowerSeries ℤ ℂ)
    (toQExpansion h f)

@[simp] lemma poleRemoved_apply (h : ℝ) (f : ℍ → ℂ) (τ : ℍ) :
    poleRemoved h f τ = 𝕢 h τ ^ poleOrder h f * f τ :=
  rfl

/-- Without a pole there is nothing to remove. -/
lemma poleRemoved_of_poleOrder_eq_zero {h : ℝ} {f : ℍ → ℂ} (h0 : poleOrder h f = 0) :
    poleRemoved h f = f := by
  funext τ
  simp [h0]

/-- Without a pole, `toQExpansion` is the ordinary q-expansion. -/
lemma toQExpansion_of_poleOrder_eq_zero {h : ℝ} {f : ℍ → ℂ} (h0 : poleOrder h f = 0) :
    toQExpansion h f = qExpansion h f := by
  rw [UpperHalfPlane.toQExpansion, poleRemoved_of_poleOrder_eq_zero h0]

@[simp] lemma toQExpansion_const (h : ℝ) (a : ℂ) :
    toQExpansion h (fun _ : ℍ ↦ a) = PowerSeries.C a := by
  rw [toQExpansion_of_poleOrder_eq_zero (poleOrder_const h a), qExpansion_const]

/-- On the punctured unit disc, the cusp function of `𝕢 h τ ^ n * f τ` is `q ^ n` times the
cusp function of `f`. -/
lemma cuspFunction_qpow_mul_eq {h : ℝ} (hh : 0 < h) (f : ℍ → ℂ)
    {n : ℕ} {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) :
    cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ) q = q ^ n * cuspFunction h f q := by
  have him := Periodic.im_invQParam_pos_of_norm_lt_one hh hqnorm hq0
  simp only [cuspFunction_apply_of_ne_zero h _ hq0,
    UpperHalfPlane.ofComplex_apply_of_im_pos him, Periodic.qParam_right_inv hh.ne' hq0]

/-- On a punctured neighbourhood of `0`, the cusp function of `𝕢 h τ ^ n * f τ` is `q ^ n`
times the cusp function of `f`. -/
lemma cuspFunction_qpow_mul_eventuallyEq {h : ℝ} (hh : 0 < h) (f : ℍ → ℂ) (n : ℕ) :
    cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ) =ᶠ[𝓝[≠] 0]
      fun q ↦ q ^ n * cuspFunction h f q := by
  filter_upwards [eventually_ne_zero_and_norm_lt_one] with q hq
  exact cuspFunction_qpow_mul_eq hh f hq.1 hq.2

/-- If the cusp function of `f` agrees with `G` on a punctured neighbourhood of `0` and `G` is
continuous at `0`, then the (`limUnder`-defined) value of the cusp function at `0` is `G 0`. -/
lemma cuspFunction_apply_zero_eq {h : ℝ} {f : ℍ → ℂ} {G : ℂ → ℂ}
    (hEq : cuspFunction h f =ᶠ[𝓝[≠] (0 : ℂ)] G) (hG : ContinuousAt G 0) :
    cuspFunction h f 0 = G 0 :=
  calc
    cuspFunction h f 0 = limUnder (𝓝[≠] (0 : ℂ)) (cuspFunction h f) := by
      simpa [cuspFunction] using
        Periodic.cuspFunction_zero_eq_limUnder_nhds_ne (h := h)
          (f := f ∘ UpperHalfPlane.ofComplex)
    _ = limUnder (𝓝[≠] (0 : ℂ)) G := congrArg lim (Filter.map_congr hEq)
    _ = G 0 := (tendsto_nhdsWithin_of_tendsto_nhds hG.tendsto).limUnder_eq

/-- If the cusp function of `f` agrees on a punctured neighbourhood of `0` with a function `G`
analytic at `0`, then the cusp function is itself analytic at `0`. -/
lemma analyticAt_cuspFunction_of_eventuallyEq {h : ℝ} {f : ℍ → ℂ} {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 0) (hEq : cuspFunction h f =ᶠ[𝓝[≠] (0 : ℂ)] G) :
    AnalyticAt ℂ (cuspFunction h f) 0 :=
  hG.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hEq
    (cuspFunction_apply_zero_eq hEq hG.continuousAt)).symm

/-- For a nonpositive period the cusp function is constant (a junk value) near `0`, hence
analytic there. -/
lemma analyticAt_cuspFunction_of_not_pos {h : ℝ} {f : ℍ → ℂ} (hh : h ≤ 0) :
    AnalyticAt ℂ (cuspFunction h f) 0 := by
  let τ0 : ℍ := Classical.choice inferInstance
  refine analyticAt_cuspFunction_of_eventuallyEq (G := fun _ ↦ f τ0) analyticAt_const ?_
  filter_upwards [eventually_ne_zero_and_norm_lt_one] with q hq
  have him_nonpos : Complex.im (Periodic.invQParam h q) ≤ 0 := by
    rw [Periodic.im_invQParam]
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by linarith) (by positivity))
      (Real.log_nonpos (norm_nonneg _) hq.2.le)
  rw [cuspFunction_apply_of_ne_zero h f hq.1, UpperHalfPlane.ofComplex_apply_of_im_nonpos
    him_nonpos]

/-- On the punctured unit disc, the cusp function of the pole-removed function is
`q ^ poleOrder h f` times the cusp function of `f`. -/
lemma cuspFunction_poleRemoved_eq (h : ℝ) (f : ℍ → ℂ) {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) :
    cuspFunction h (poleRemoved h f) q = q ^ poleOrder h f * cuspFunction h f q := by
  rcases lt_or_ge 0 h with hh | hh
  · exact cuspFunction_qpow_mul_eq hh f hq0 hqnorm
  · have hpole : poleOrder h f = 0 :=
      poleOrder_eq_zero_of_analyticAt (analyticAt_cuspFunction_of_not_pos hh)
    simp [poleRemoved_of_poleOrder_eq_zero hpole, hpole]

/-- On a punctured neighbourhood of `0`, the cusp function of the pole-removed function is
`q ^ poleOrder h f` times the cusp function of `f`. -/
lemma cuspFunction_poleRemoved_eventuallyEq (h : ℝ) (f : ℍ → ℂ) :
    cuspFunction h (poleRemoved h f) =ᶠ[𝓝[≠] 0] fun q ↦ q ^ poleOrder h f * cuspFunction h f q := by
  filter_upwards [eventually_ne_zero_and_norm_lt_one] with q hq
  exact cuspFunction_poleRemoved_eq h f hq.1 hq.2

/-- Multiplying by `𝕢 h τ ^ poleOrder h f` removes the pole: the cusp function of the
pole-removed function is analytic at `0`. -/
lemma analyticAt_cuspFunction_poleRemoved {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    AnalyticAt ℂ (cuspFunction h (poleRemoved h f)) 0 := by
  have hEq_shift := cuspFunction_poleRemoved_eventuallyEq h f
  cases ho : meromorphicOrderAt (cuspFunction h f) (0 : ℂ) with
  | top =>
      refine analyticAt_cuspFunction_of_eventuallyEq (G := fun _ ↦ (0 : ℂ))
        analyticAt_const ?_
      filter_upwards [hEq_shift, meromorphicOrderAt_eq_top_iff.1 ho] with q hq hqzero
      simp [hq, hqzero]
  | coe k =>
      obtain ⟨g, hg_an, -, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hmero).1 ho
      have hpole : (poleOrder h f : ℤ) = (-k).toNat := by
        rw [poleOrder_eq_toNat_neg_meromorphicOrderAt, ho, WithTop.untopD_coe]
      refine analyticAt_cuspFunction_of_eventuallyEq
        (G := fun q ↦ q ^ (k + poleOrder h f).toNat * g q)
        ((analyticAt_id.pow _).mul hg_an) ?_
      filter_upwards [hEq_shift, hg_eq, self_mem_nhdsWithin] with q hq hqg (hq0 : q ≠ 0)
      rw [hq, hqg, sub_zero, smul_eq_mul, ← zpow_natCast q (poleOrder h f), ← mul_assoc,
        ← zpow_add₀ hq0, ← zpow_natCast q, Int.toNat_of_nonneg (by omega), add_comm]

/-- A cusp-meromorphic function is analytic at the cusp iff its pole order vanishes. -/
lemma analyticAt_cuspFunction_iff_poleOrder_eq_zero {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    AnalyticAt ℂ (cuspFunction h f) 0 ↔ poleOrder h f = 0 :=
  ⟨poleOrder_eq_zero_of_analyticAt, fun h0 ↦
    poleRemoved_of_poleOrder_eq_zero h0 ▸ analyticAt_cuspFunction_poleRemoved hmero⟩

/-! ### Coefficients of the Laurent q-expansion -/

/-- The coefficient of `laurentqExpansion h f` at `n` is the coefficient of `toQExpansion h f`
(as a Laurent series) at `n + poleOrder h f`. -/
lemma laurentqExpansion.coeff_eq_HahnSeries_add (h : ℝ) (f : ℍ → ℂ) {n : ℤ} :
    (laurentqExpansion h f).coeff n =
    ((HahnSeries.ofPowerSeries ℤ ℂ) (toQExpansion h f)).coeff (n + poleOrder h f) := by
  rw [laurentqExpansion, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add]

/-- The Laurent q-expansion vanishes below `-poleOrder h f`. -/
lemma laurentqExpansion.coeff_eq_zero_of_lt {h : ℝ} {f : ℍ → ℂ} {n : ℤ}
    (hn : n < -(poleOrder h f : ℤ)) : (laurentqExpansion h f).coeff n = 0 := by
  rw [laurentqExpansion.coeff_eq_HahnSeries_add, PowerSeries.coeff_coe, if_pos (by omega)]

/-- The coefficient at `-poleOrder h f + n` is the `n`-th coefficient of `toQExpansion h f`. -/
@[simp] lemma laurentqExpansion.coeff_neg_poleOrder_add (h : ℝ) (f : ℍ → ℂ) (n : ℕ) :
    (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ) + n) = (toQExpansion h f).coeff n := by
  simp [laurentqExpansion.coeff_eq_HahnSeries_add, PowerSeries.coeff_coe]

/-- From `-poleOrder h f` on, the Laurent coefficients are those of `toQExpansion h f`. -/
lemma laurentqExpansion.coeff_of_geq {h : ℝ} {f : ℍ → ℂ} {n : ℤ}
    (hn : -(poleOrder h f : ℤ) ≤ n) :
    (laurentqExpansion h f).coeff n =
      (toQExpansion h f).coeff (Int.toNat (n + poleOrder h f)) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(poleOrder h f : ℤ) + k := ⟨(n + poleOrder h f).toNat, by omega⟩
  rw [laurentqExpansion.coeff_neg_poleOrder_add,
    show (-(poleOrder h f : ℤ) + k + poleOrder h f).toNat = k by omega]

/-- `laurentqExpansion.coeff_eq_zero_of_lt` with the pole order given by an equation. -/
lemma laurentqExpansion.coeff_eq_zero_of_lt' {h : ℝ} {f : ℍ → ℂ} {M : ℕ} {n : ℤ}
    (hM : poleOrder h f = M) (hn : n < -(M : ℤ)) : (laurentqExpansion h f).coeff n = 0 := by
  subst hM
  exact laurentqExpansion.coeff_eq_zero_of_lt hn

/-- `laurentqExpansion.coeff_neg_poleOrder_add` with the pole order given by an equation. -/
lemma laurentqExpansion.coeff_neg_poleOrder_add' {h : ℝ} {f : ℍ → ℂ} {M : ℕ}
    (hM : poleOrder h f = M) (n : ℕ) :
    (laurentqExpansion h f).coeff (-(M : ℤ) + n) = (toQExpansion h f).coeff n := by
  subst hM
  exact laurentqExpansion.coeff_neg_poleOrder_add h f n

/-- `laurentqExpansion.coeff_of_geq` with the pole order given by an equation. -/
lemma laurentqExpansion.coeff_of_geq' {h : ℝ} {f : ℍ → ℂ} {M : ℕ} {n : ℤ}
    (hM : poleOrder h f = M) (hn : -(M : ℤ) ≤ n) :
    (laurentqExpansion h f).coeff n = (toQExpansion h f).coeff (Int.toNat (n + M)) := by
  subst hM
  exact laurentqExpansion.coeff_of_geq hn

/-- Every Laurent coefficient, as an `if`: zero below `-poleOrder h f`, a coefficient of
`toQExpansion h f` from there on. -/
lemma laurentqExpansion.coeff_of_qExpansion (h : ℝ) (f : ℍ → ℂ) (n : ℤ) :
    (laurentqExpansion h f).coeff n = if n < -(poleOrder h f : ℤ) then 0
    else (toQExpansion h f).coeff (Int.toNat (n + poleOrder h f)) := by
  split_ifs with hlt
  · exact laurentqExpansion.coeff_eq_zero_of_lt hlt
  · exact laurentqExpansion.coeff_of_geq (le_of_not_gt hlt)

/-- The leading Laurent coefficient is the constant coefficient of `toQExpansion h f`. -/
@[simp] lemma laurentqExpansion.coeff_neg_poleOrder (h : ℝ) (f : ℍ → ℂ) :
    (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ)) = (toQExpansion h f).coeff 0 := by
  simpa using laurentqExpansion.coeff_neg_poleOrder_add h f 0

/-- The constant Laurent coefficient. -/
lemma laurentqExpansion.coeff_zero (h : ℝ) (f : ℍ → ℂ) :
    (laurentqExpansion h f).coeff 0 = (toQExpansion h f).coeff (poleOrder h f) := by
  simpa using laurentqExpansion.coeff_neg_poleOrder_add h f (poleOrder h f)

/-- Without a pole, the Laurent q-expansion is the ordinary q-expansion. -/
lemma laurentqExpansion.eq_qExpansion_of_poleOrder_eq_zero {h : ℝ} {f : ℍ → ℂ}
    (h0 : poleOrder h f = 0) : laurentqExpansion h f = qExpansion h f := by
  simp [laurentqExpansion, toQExpansion_of_poleOrder_eq_zero h0, h0]

/-- If the cusp function is analytic at `0`, the Laurent q-expansion is the ordinary
q-expansion. -/
lemma laurentqExpansion.eq_qExpansion_of_analyticAt {h : ℝ} {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) : laurentqExpansion h f = qExpansion h f :=
  laurentqExpansion.eq_qExpansion_of_poleOrder_eq_zero (poleOrder_eq_zero_of_analyticAt hf)

/-- A genuine pole of order `poleOrder h f` is a meromorphic order `-poleOrder h f`. -/
lemma meromorphicOrderAt_cuspFunction_eq_neg_poleOrder {h : ℝ} {f : ℍ → ℂ}
    (h0 : poleOrder h f ≠ 0) :
    meromorphicOrderAt (cuspFunction h f) 0 = -(poleOrder h f : ℤ) :=
  (poleOrder_eq_iff h0).1 rfl

/-- At a genuine pole, the leading coefficient of the Laurent q-expansion does not vanish. -/
lemma toQExpansion_coeff_zero_ne {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    (toQExpansion h f).coeff 0 ≠ 0 := by
  have hord := meromorphicOrderAt_cuspFunction_eq_neg_poleOrder h0
  have hEq : cuspFunction h f =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦
      (z - 0) ^ (meromorphicOrderAt (cuspFunction h f) 0).untop₀ •
        cuspFunction h (poleRemoved h f) z := by
    filter_upwards [cuspFunction_poleRemoved_eventuallyEq h f, self_mem_nhdsWithin]
      with q hq (hq0 : q ≠ 0)
    rw [hq, hord, ← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe, sub_zero,
      smul_eq_mul, ← zpow_natCast q (poleOrder h f), ← mul_assoc, ← zpow_add₀ hq0,
      neg_add_cancel, zpow_zero, one_mul]
  have hne := hmero.meromorphicTrailingCoeffAt_ne_zero (by rw [hord]; exact WithTop.coe_ne_top)
  rw [(analyticAt_cuspFunction_poleRemoved hmero).meromorphicTrailingCoeffAt_of_eq_nhdsNE hEq]
    at hne
  simpa [UpperHalfPlane.toQExpansion, qExpansion_coeff] using hne

/-- At a genuine pole, `toQExpansion h f` is nonzero. -/
lemma toQExpansion_ne_zero {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    toQExpansion h f ≠ 0 := fun hq ↦ by
  simpa [hq] using toQExpansion_coeff_zero_ne hmero h0

/-- At a genuine pole, the Laurent q-expansion is nonzero. -/
lemma laurentqExpansion.ne_zero {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    laurentqExpansion h f ≠ 0 :=
  HahnSeries.ne_zero_of_coeff_ne_zero <| by
    rw [laurentqExpansion.coeff_neg_poleOrder]
    exact toQExpansion_coeff_zero_ne hmero h0

/-- A genuine pole of order `r` gives a Laurent q-expansion of order `-r`. -/
lemma laurentqExpansion.order_eq_neg_poleOrder {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    (laurentqExpansion h f).order = -(poleOrder h f : ℤ) := by
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) (le_of_not_gt fun hlt ↦ ?_)
  · rw [laurentqExpansion.coeff_neg_poleOrder]
    exact toQExpansion_coeff_zero_ne hmero h0
  · exact HahnSeries.coeff_order_eq_zero.not.2 (laurentqExpansion.ne_zero hmero h0)
      (laurentqExpansion.coeff_eq_zero_of_lt hlt)

/-- `laurentqExpansion.order_eq_neg_poleOrder`, solved for the pole order. -/
lemma laurentqExpansion.poleOrder_to_order {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    poleOrder h f = -(laurentqExpansion h f).order := by
  rw [laurentqExpansion.order_eq_neg_poleOrder hmero h0, neg_neg]

/-- At a genuine pole, `toQExpansion h f` is the power-series part of the Laurent
q-expansion. -/
lemma laurentqExpansion.toQExpansion_eq_powerSeriesPart {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    toQExpansion h f = (laurentqExpansion h f).powerSeriesPart := by
  ext n
  rw [LaurentSeries.powerSeriesPart_coeff, laurentqExpansion.order_eq_neg_poleOrder hmero h0,
    laurentqExpansion.coeff_neg_poleOrder_add]

/-- The Laurent q-expansion is the ordinary q-expansion exactly when there is no pole. -/
lemma laurentqExpansion.eq_qExpansion_iff {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    laurentqExpansion h f = qExpansion h f ↔ poleOrder h f = 0 := by
  refine ⟨fun heq ↦ by_contra fun h0 ↦ toQExpansion_coeff_zero_ne hmero h0 ?_,
    laurentqExpansion.eq_qExpansion_of_poleOrder_eq_zero⟩
  rw [← laurentqExpansion.coeff_neg_poleOrder, heq, PowerSeries.coeff_coe, if_pos (by omega)]

/-! ### The Cauchy integral formula for the Laurent coefficients -/

/-- Cauchy's formula for q-expansion coefficients, for a cusp function holomorphic on a closed
disc of radius `R` (mathlib's `qExpansion_coeff_eq_circleIntegral` instead assumes `f` periodic,
holomorphic on `ℍ` and bounded at `i∞`). -/
lemma qExpansion_coeff_eq_circleIntegral_of_differentiableOn
    {g : ℍ → ℂ} {R : ℝ} (hR : 0 < R)
    (hDiff : DifferentiableOn ℂ (cuspFunction h g) (Metric.closedBall 0 R)) (n : ℕ) :
    (qExpansion h g).coeff n =
      ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h g z / z ^ (n + 1)) := by
  have hci := hDiff.circleIntegral_one_div_sub_center_pow_smul hR n
  rw [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm,
    ← div_eq_iff two_pi_I_ne_zero] at hci
  simp_rw [qExpansion, PowerSeries.coeff_mk, ← hci, sub_zero, smul_eq_mul,
    one_div_mul_eq_div, div_eq_inv_mul]

/-- There is a radius `0 < R < 1` on whose closed disc the pole-removed cusp function is
holomorphic, supplying a contour for the Cauchy coefficient formula. -/
lemma exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) : ∃ R : ℝ, 0 < R ∧ R < 1 ∧
      DifferentiableOn ℂ (cuspFunction h (poleRemoved h f)) (Metric.closedBall 0 R) := by
  obtain ⟨R0, hR0pos, hR0⟩ :=
    (analyticAt_cuspFunction_poleRemoved hmero).exists_ball_analyticOnNhd
  refine ⟨min (R0 / 2) (1 / 2), by positivity, by linarith [min_le_right (R0 / 2) (1 / 2)], ?_⟩
  exact hR0.analyticOn.differentiableOn.mono (Metric.closedBall_subset_ball
    (by linarith [min_le_left (R0 / 2) (1 / 2)]))

/-- On a circle of radius `0 < R < 1`, dividing the pole-removed cusp function by `z ^ a` is
the same as dividing the original cusp function by `z ^ (a - poleOrder h f)`. -/
private lemma cuspFunction_poleRemoved_div_zpow_eq_of_mem_sphere (h : ℝ) (f : ℍ → ℂ)
    {R : ℝ} (hRpos : 0 < R) (hRlt1 : R < 1) {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) R) (a : ℤ) :
    cuspFunction h (poleRemoved h f) z / z ^ a =
      cuspFunction h f z / z ^ (a - (poleOrder h f : ℤ)) := by
  have hznorm : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [norm_zero] at hznorm
    linarith
  rw [cuspFunction_poleRemoved_eq h f hz0 (hznorm ▸ hRlt1), ← zpow_natCast z, zpow_sub₀ hz0,
    div_div_eq_mul_div]
  ring

/-- Below the principal-part cutoff the contour integrand of the cusp function extends
holomorphically over the disc, so its circle integral vanishes. -/
private lemma circleIntegral_cuspFunction_div_zpow_eq_zero {h : ℝ} {f : ℍ → ℂ}
    {R : ℝ} (hRpos : 0 < R) (hRlt1 : R < 1)
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
    have hdiv := cuspFunction_poleRemoved_div_zpow_eq_of_mem_sphere h f hRpos hRlt1 hz
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
    {R : ℝ} (hRpos : 0 < R) (hRlt1 : R < 1)
    {m : ℕ} {n : ℤ} (hm : (m : ℤ) = n + poleOrder h f) :
    (∮ z in C(0, R), cuspFunction h (poleRemoved h f) z / z ^ (m + 1)) =
      ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1) := by
  refine circleIntegral.integral_congr hRpos.le fun z hz ↦ ?_
  have hdiv := cuspFunction_poleRemoved_div_zpow_eq_of_mem_sphere h f hRpos hRlt1 hz
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
      circleIntegral_cuspFunction_div_zpow_eq_zero hRpos hRlt1 hDiff hn, mul_zero]
  · have hm : ((Int.toNat (n + poleOrder h f) : ℕ) : ℤ) = n + poleOrder h f :=
      Int.toNat_of_nonneg (by linarith [le_of_not_gt hn])
    rw [laurentqExpansion.coeff_of_geq (le_of_not_gt hn), UpperHalfPlane.toQExpansion,
      qExpansion_coeff_eq_circleIntegral_of_differentiableOn hRpos hDiff _,
      circleIntegral_cuspFunction_poleRemoved_div_pow_eq hRpos hRlt1 hm]
