/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Tactic2.qexp_simp
import XYin.PhD.jFunction.Deltaqexpansions

/-!
# Tests for the `qexp_simp` tactic

Side conditions of mathlib's `q`-expansion API for pointwise combinations of general functions
(given the hypotheses as simp arguments) and for mathlib's level-one forms `ModularForm.E₄` and
`CuspForm.discriminant`.
-/

open ModularForm UpperHalfPlane
open scoped Manifold

section GeneralFunctions

variable {h : ℝ} {f g : ℍ → ℂ}

example (hh : 0 < h)
    (hfper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hgper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) h)
    (hfhol : MDiff f) (hghol : MDiff g)
    (hfbdd : IsBoundedAtImInfty f) (hgbdd : IsBoundedAtImInfty g) :
    AnalyticAt ℂ (cuspFunction h (f * g - f)) 0 := by
  qexp_simp [hh, hfper, hgper, hfhol, hghol, hfbdd, hgbdd]

example (hh : 0 < h)
    (hfper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hgper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) h)
    (hfhol : MDiff f) (hghol : MDiff g)
    (hfbdd : IsBoundedAtImInfty f) (hgbdd : IsBoundedAtImInfty g) :
    DifferentiableOn ℂ (cuspFunction h (f * g)) (Metric.ball 0 1) := by
  qexp_simp [hh, hfper, hgper, hfhol, hghol, hfbdd, hgbdd]

example (hh : 0 < h)
    (hfper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (τ : ℍ) :
    HasSum
      (fun m ↦ (qExpansion h f).coeff m • Function.Periodic.qParam h (τ : ℂ) ^ m)
      (f τ) := by
  qexp_simp [hh, hfper, hfhol, hfbdd]

end GeneralFunctions

section ModularAndCusp

example : Function.Periodic (E₄ ∘ UpperHalfPlane.ofComplex) 1 := by
  qexp_simp

example : MDiff E₄ := by
  qexp_simp

example : IsBoundedAtImInfty E₄ := by
  qexp_simp

example : IsZeroAtImInfty CuspForm.discriminant := by
  qexp_simp

example : cuspFunction 1 CuspForm.discriminant 0 = 0 := by
  qexp_simp

end ModularAndCusp
