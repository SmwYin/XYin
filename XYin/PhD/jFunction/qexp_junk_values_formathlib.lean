/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.ModularForms.QExpansion

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# q-expansions at nonpositive parameters and meromorphic poles

The total definition of `UpperHalfPlane.qExpansion` produces a constant power series in two cases:

* For a nonpositive parameter, the constant is the value of the function at the fallback point
  `UpperHalfPlane.ofComplex 0`.
* When the cusp function has a meromorphic pole at zero, the constant is the fallback value
  chosen by `limUnder`, and every positive coefficient vanishes.

Both results apply to arbitrary functions `f : ℍ → ℂ`. The fallback point and value are
classical choices; they are not identified with `I` or `0`.
-/

public section

open Filter Function
open scoped Topology

namespace UpperHalfPlane

/-- At a nonpositive parameter, the q-expansion of any function is the constant series given by
its value at the fallback point of `ofComplex`. -/
theorem qExpansion_eq_C_of_nonpos {h : ℝ} (hh : h ≤ 0) (f : ℍ → ℂ) :
    qExpansion h f = PowerSeries.C (f (ofComplex 0)) := by
  have hnorm : ∀ᶠ q : ℂ in 𝓝[≠] 0, ‖q‖ < 1 :=
    nhdsWithin_le_nhds <| by
      simpa [Metric.ball, dist_eq_norm] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one
  have hEq : cuspFunction h f =ᶠ[𝓝[≠] (0 : ℂ)] fun _ ↦ f (ofComplex 0) := by
    filter_upwards [self_mem_nhdsWithin, hnorm] with q hq hqn
    have him : (Periodic.invQParam h q).im ≤ 0 := by
      rw [Periodic.im_invQParam]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (neg_nonneg.mpr hh) (by positivity))
        (Real.log_nonpos (norm_nonneg _) hqn.le)
    change Periodic.cuspFunction h (f ∘ ofComplex) q = _
    rw [Periodic.cuspFunction_eq_of_nonzero h (f ∘ ofComplex) hq, comp_apply,
      ofComplex_apply_eq_of_im_nonpos (w' := (0 : ℂ)) him (by simp)]
  have hzero : cuspFunction h f 0 = f (ofComplex 0) := by
    change Periodic.cuspFunction h (f ∘ ofComplex) 0 = _
    rw [Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
    exact (tendsto_const_nhds.congr' hEq.symm).limUnder_eq
  ext n
  rw [qExpansion_coeff,
    (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hEq hzero).iteratedDeriv_eq n]
  cases n <;> simp [iteratedDeriv_const, PowerSeries.coeff_C]

/-- If the cusp function has a meromorphic pole at zero, the ordinary q-expansion is the
constant series at the fallback value chosen by `limUnder`. Negative meromorphic order already
implies meromorphicity, so no separate `MeromorphicAt` hypothesis is needed. -/
theorem qExpansion_eq_C_of_meromorphicOrderAt_neg {h : ℝ} {f : ℍ → ℂ}
    (ho : meromorphicOrderAt (cuspFunction h f) 0 < 0) :
    qExpansion h f = PowerSeries.C (Classical.choice (inferInstance : Nonempty ℂ)) := by
  have hzero : cuspFunction h f 0 = Classical.choice (inferInstance : Nonempty ℂ) := by
    change Periodic.cuspFunction h (f ∘ ofComplex) 0 = _
    rw [Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
    apply limUnder_of_not_tendsto
    change ¬ ∃ c, Tendsto (cuspFunction h f) (𝓝[≠] (0 : ℂ)) (𝓝 c)
    rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg
      (meromorphicAt_of_meromorphicOrderAt_ne_zero ho.ne)]
    exact ho.not_ge
  have horders (n : ℕ) : meromorphicOrderAt (iteratedDeriv n (cuspFunction h f)) 0 < 0 := by
    induction n with
    | zero => simpa using ho
    | succ n ih =>
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ih.ne_top
      have hmneg : m < 0 := by simpa [← hm] using ih
      rw [iteratedDeriv_succ,
        meromorphicOrderAt_deriv_eq_sub_one (Int.cast_ne_zero.mpr hmneg.ne) hm.symm]
      exact_mod_cast (sub_neg.mpr (hmneg.trans zero_lt_one))
  ext n
  cases n with
  | zero => simpa [qExpansion_coeff] using hzero
  | succ n =>
    have hderiv : iteratedDeriv (n + 1) (cuspFunction h f) 0 = 0 := by
      rw [iteratedDeriv_succ]
      apply deriv_zero_of_not_differentiableAt
      intro hd
      exact (horders n).not_ge <|
        ((meromorphicAt_of_meromorphicOrderAt_ne_zero (horders n).ne).analyticAt
          hd.continuousAt).meromorphicOrderAt_nonneg
    simp [qExpansion_coeff, hderiv]

end UpperHalfPlane
