import XYin.Tactic2.qexp_simp
import XYin.jFunction.Deltaqexpansions
import XYin.jFunction.jfunction
import XYin.Tactics.ps_compute

open Function UpperHalfPlane

open scoped Manifold

section General

variable {h : ℝ} {f g : ℍ → ℂ}

example (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    qExpansion h (f * g) = qExpansion h f * qExpansion h g := by
  qexp_simp [hf, hg]

example (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    qExpansion h (f - g) = qExpansion h f - qExpansion h g := by
  qexp_simp [hf, hg]

example (hh : 0 < h) (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hgper : Periodic (g ∘ UpperHalfPlane.ofComplex) h) (hfhol : MDiff f) (hghol : MDiff g)
    (hfbdd : IsBoundedAtImInfty f) (hgbdd : IsBoundedAtImInfty g) :
    qExpansion h (f ^ 3 - g ^ 2) = (qExpansion h f) ^ 3 - (qExpansion h g) ^ 2 := by
  qexp_simp [hh, hfper, hgper, hfhol, hghol, hfbdd, hgbdd]

example (hh : 0 < h) (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hgper : Periodic (g ∘ UpperHalfPlane.ofComplex) h) (hfhol : MDiff f) (hghol : MDiff g)
    (hfbdd : IsBoundedAtImInfty f) (hgbdd : IsBoundedAtImInfty g) :
    AnalyticAt ℂ (cuspFunction h (f * g - f)) 0 := by
  qexp_simp [hh, hfper, hgper, hfhol, hghol, hfbdd, hgbdd]

example (hh : 0 < h) (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (τ : ℍ) :
    HasSum (fun m : ℕ => (qExpansion h f).coeff m • Function.Periodic.qParam h τ ^ m)
      (f τ) := by
  qexp_simp [hh, hfper, hfhol, hfbdd]

end General

section Modular

/-!
`qexp_simp` as a proof preprocessor:
it pushes `qExpansion` statements to plain PowerSeries algebraic identities.
-/

noncomputable example :
    qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
  qexp_simp

noncomputable example :
    qExpansion 1 (E6 ^ 2) = (qExpansion 1 E6) ^ 2 := by
  qexp_simp

-- Recommended pattern for non-modular factors:
-- pass analyticity explicitly to `qexp_simp`.
noncomputable example (hqoverDelta : AnalyticAt ℂ (cuspFunction 1 qoverDelta) 0) :
    qExpansion 1 (E4 ^ 3 * qoverDelta) = (qExpansion 1 E4) ^ 3 * qExpansion 1 qoverDelta := by
  qexp_simp [hqoverDelta]

noncomputable example :
    qExpansion 1 (E4 ^ 3 * qoverDelta) = (qExpansion 1 E4) ^ 3 * qExpansion 1 qoverDelta := by
  qexp_simp [qoverDelta_AnalyticAt]

noncomputable example :
    qExpansion 1 (E4 ^ 3 - E6 ^ 2) = (qExpansion 1 E4) ^ 3 - (qExpansion 1 E6) ^ 2 := by
  qexp_simp

noncomputable example :
    qExpansion 1 ((E4 ^ 3 - E6 ^ 2) * E4) =
      ((qExpansion 1 E4) ^ 3 - (qExpansion 1 E6) ^ 2) * qExpansion 1 E4 := by
  qexp_simp

example : Periodic (E4 ∘ UpperHalfPlane.ofComplex) 1 := by
  qexp_simp

example : MDiff E4 := by
  qexp_simp

example : IsBoundedAtImInfty E4 := by
  qexp_simp

example : AnalyticAt ℂ (cuspFunction 1 (E4 ^ 3 - E6 ^ 2)) 0 := by
  qexp_simp

example : cuspFunction 1 Delta 0 = 0 := by
  qexp_simp

end Modular

section Bridge

open PowerSeries

lemma E4_qExpansion_coeff (n : ℕ) :
    PowerSeries.coeff n (qExpansion 1 E4) =
      if n = 0 then 1 else (240 : ℂ) * ArithmeticFunction.sigma 3 n := by
  by_cases hn : n = 0
  · simpa [hn, E4] using congr_fun E4_q_exp n
  · simpa [hn, E4] using congr_fun E4_q_exp n

lemma E6_qExpansion_coeff (n : ℕ) :
    PowerSeries.coeff n (qExpansion 1 E6) =
      if n = 0 then 1 else -(504 : ℂ) * ArithmeticFunction.sigma 5 n := by
  by_cases hn : n = 0
  · simpa [hn, E6] using congr_fun E6_q_exp n
  · simpa [hn, E6] using congr_fun E6_q_exp n

lemma qExpansion_E4_pow_three_sub_E6_pow_two :
    qExpansion 1 (E4 ^ 3 - E6 ^ 2) = (qExpansion 1 E4) ^ 3 - (qExpansion 1 E6) ^ 2 := by
  qexp_simp

noncomputable example
    (hE4pow2 : ((qExpansion 1 E4) ^ 3).coeff 2 = 179280)
    (hE6pow2 : ((qExpansion 1 E6) ^ 2).coeff 2 = 220752) :
    (qExpansion 1 Delta).coeff 2 = -24 := by
  rw [Deltaaux, qExpansion_E4_pow_three_sub_E6_pow_two]
  ps_compute

noncomputable example
    (hF0 : (((qExpansion 1 E4) ^ 3 - (qExpansion 1 E6) ^ 2)).coeff 0 = 0)
    (hF1 : (((qExpansion 1 E4) ^ 3 - (qExpansion 1 E6) ^ 2)).coeff 1 = 1728)
    (hF2 : (((qExpansion 1 E4) ^ 3 - (qExpansion 1 E6) ^ 2)).coeff 2 = -41472)
    (hE40 : (qExpansion 1 E4).coeff 0 = 1)
    (hE41 : (qExpansion 1 E4).coeff 1 = 240)
    (hE42 : (qExpansion 1 E4).coeff 2 = 2160) :
    (qExpansion 1 ((E4 ^ 3 - E6 ^ 2) * E4)).coeff 2 = 373248 := by
  have hpre :
      qExpansion 1 ((E4 ^ 3 - E6 ^ 2) * E4) =
        ((qExpansion 1 E4) ^ 3 - (qExpansion 1 E6) ^ 2) * qExpansion 1 E4 := by
    qexp_simp
  rw [hpre]
  change ((((qExpansion 1 E4) ^ 3 - (qExpansion 1 E6) ^ 2) * qExpansion 1 E4).coeff 2) = 373248
  ps_compute

end Bridge
