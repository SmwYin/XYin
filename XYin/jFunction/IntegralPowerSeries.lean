import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace IntegralPowerSeries

--TODO: generalise to more rings
-- define some R-module inside space of modular forms
-- isRIntegral
abbrev hom : ℤ →+* ℂ := Int.castRingHom ℂ
def coeToComplexPowerSeries.ringHom : PowerSeries ℤ →+* PowerSeries ℂ :=
    PowerSeries.map (hom)
noncomputable def IntegralPowerSeriesSubring : Subring (PowerSeries ℂ) :=
    coeToComplexPowerSeries.ringHom.range
def IsIntegralPowerSeries (x : PowerSeries ℂ) : Prop := x ∈ IntegralPowerSeriesSubring

lemma int_iff (f : PowerSeries ℂ) : IsIntegralPowerSeries f ↔
    ∀ n : ℕ , ∃ z : ℤ, (PowerSeries.coeff n) f = z := by
  constructor
  · intro h n
    obtain ⟨g, rfl⟩ := h
    use PowerSeries.coeff n g
    change (PowerSeries.coeff n) ((PowerSeries.map hom) g) = ↑((PowerSeries.coeff n) g)
    exact PowerSeries.coeff_map hom n g
  · intro h
    choose z hz using h
    let g : PowerSeries ℤ := PowerSeries.mk z
    use g
    ext n
    calc
    _ = hom ((PowerSeries.coeff n) g) := by
      simp [coeToComplexPowerSeries.ringHom]
    _ = (z n : ℂ) := by simp [hom, g]
    _ = _ := by simp [hz n]

noncomputable def toIntegralPowerSeries {f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) :
    PowerSeries ℤ := Classical.choose hf

lemma coeTo_of_toIntegralPowerSeries {f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) :
    coeToComplexPowerSeries.ringHom (toIntegralPowerSeries hf) = f :=
  Classical.choose_spec hf
-- Question: keep this lemma?

lemma IsIntegralPowerSeriesmod {c : ℤ} (hc : c ≠ 0) {f : PowerSeries ℂ}
    (hf : IsIntegralPowerSeries f) (hmod : ∀ n : ℕ, Int.ModEq c
    ((toIntegralPowerSeries hf).coeff n) 0) : IsIntegralPowerSeries ((1/c : ℂ) • f) := by
  rw [int_iff]
  intro n
  let g : PowerSeries ℤ := toIntegralPowerSeries hf
  have hg : coeToComplexPowerSeries.ringHom g = f := by
    simpa [g] using coeTo_of_toIntegralPowerSeries hf
  have h0 : Int.ModEq c (g.coeff n) 0 := by simpa [g] using hmod n
  have hdiv : c ∣ g.coeff n := by
    have hneg : c ∣ -g.coeff n := by
      simpa [Int.sub_eq_add_neg] using (Int.modEq_iff_dvd.mp h0)
    exact Int.dvd_neg.mp hneg
  rcases hdiv with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have hgn : (g.coeff n : ℂ) = f.coeff n := congrArg (PowerSeries.coeff n) hg
  calc
  _ = (1 / c : ℂ) * f.coeff n := by simp
  _ = (1 / c : ℂ) * (g.coeff n : ℂ) := by simp [hgn]
  _ = (1 / c : ℂ) * ((c * t : ℤ) : ℂ) := by simp [ht]
  _ = (1 / c : ℂ) * ((c : ℂ) * (t : ℂ)) := by norm_cast
  _ = _ := by simp [hc]

end IntegralPowerSeries

#min_imports
