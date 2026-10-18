/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Arguments and logarithms of powers

`arg (xⁿ) = n arg x` when `|arg x| < π / n` (`arg_pow_aux`), and the resulting eventual identities
`arg ((1 + f x)ⁿ) = n arg (1 + f x)` and `log ((1 + f x)ⁿ) = n log (1 + f x)` along any filter on
which `f → 0`.
-/

@[expose] public section

open Complex Filter

open scoped Real Topology

/-- `arg (xⁿ) = n arg x` as long as `|arg x| < π / n`. -/
lemma arg_pow_aux (n : ℕ) (x : ℂ) (hna : |arg x| < π / n) :
    Complex.arg (x ^ n) = n * Complex.arg x := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hlt : |n * arg x| < π := by
    rw [abs_mul, Nat.abs_cast, ← lt_div_iff₀' (Nat.cast_pos.mpr hn)]
    exact hna
  rw [← arg_coe_angle_toReal_eq_arg, arg_pow_coe_angle, ← Real.Angle.coe_nsmul, nsmul_eq_mul,
    Real.Angle.toReal_coe_eq_self_iff]
  exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩

/-- If `f → 0` along `l`, then eventually `arg ((1 + f x)ⁿ) = n arg (1 + f x)`. -/
lemma eventually_arg_pow {α : Type*} {l : Filter α}
    (n : ℕ) (f : α → ℂ) (hf : Tendsto f l (𝓝 0)) :
    ∀ᶠ x in l, arg ((1 + f x) ^ n) = n * arg (1 + f x) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have harg : Tendsto (fun x ↦ arg (1 + f x)) l (𝓝 0) := by
    simpa [Function.comp_def] using
      (Complex.continuousAt_arg Complex.one_mem_slitPlane).tendsto.comp
      (by simpa using hf.const_add 1)
  filter_upwards [(tendsto_order.1 harg.abs).2 (π / n)
    (by simpa using div_pos Real.pi_pos (Nat.cast_pos.mpr hn))] with x hx
  exact arg_pow_aux n (1 + f x) hx

/-- If `f → 0` along `l`, then eventually `log ((1 + f x)ⁿ) = n log (1 + f x)`. -/
lemma eventually_clog_pow {α : Type*} {l : Filter α}
    (n : ℕ) (f : α → ℂ) (hf : Tendsto f l (𝓝 0)) :
    ∀ᶠ x in l, Complex.log ((1 + f x) ^ n) = n * Complex.log (1 + f x) := by
  filter_upwards [eventually_arg_pow n f hf] with x hx
  simp only [Complex.log, hx, norm_pow, Real.log_pow, ofReal_mul, ofReal_natCast]
  ring

/-- If `∑ f` converges, then so does `∑ log ((1 + f n)ᵐ)`. -/
lemma log_summable_pow {ι : Type*} (f : ι → ℂ) (hf : Summable f) (m : ℕ) :
    Summable (fun n ↦ Complex.log ((1 + f n) ^ m)) :=
  ((Complex.summable_log_one_add_of_summable hf).mul_left (m : ℂ)).congr_cofinite
    ((eventually_clog_pow m f hf.tendsto_cofinite_zero).mono fun _ h ↦ h.symm)
