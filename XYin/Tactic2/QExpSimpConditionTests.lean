import XYin.Tactic2.qexp_simp
import XYin.jFunction.Deltaqexpansions

open UpperHalfPlane
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

noncomputable example : Function.Periodic (E4 ∘ UpperHalfPlane.ofComplex) 1 := by
  qexp_simp

noncomputable example : MDiff E4 := by
  qexp_simp

noncomputable example : IsBoundedAtImInfty E4 := by
  qexp_simp

noncomputable example : IsZeroAtImInfty Delta := by
  qexp_simp

noncomputable example : cuspFunction 1 Delta 0 = 0 := by
  qexp_simp

end ModularAndCusp
