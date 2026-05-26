import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace IntegralPowerSeries
--ask on zulip
def coeToComplexPowerSeries.ringHom (R : Type*) [CommRing R] [Algebra R ℂ] :
    PowerSeries R →+* PowerSeries ℂ :=
  PowerSeries.map (algebraMap R ℂ)

noncomputable def RIntegralPowerSeriesSubring (R : Type*) [CommRing R] [Algebra R ℂ] :
    Subring (PowerSeries ℂ) :=
  (coeToComplexPowerSeries.ringHom R).range

def IsRIntegralPowerSeries (R : Type*) [CommRing R] [Algebra R ℂ]
    (x : PowerSeries ℂ) : Prop :=
  x ∈ RIntegralPowerSeriesSubring R

lemma isRIntegralPowerSeries_iff_coeff (R : Type*) [CommRing R] [Algebra R ℂ]
    (f : PowerSeries ℂ) :
    IsRIntegralPowerSeries R f ↔
      ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n f = algebraMap R ℂ r := by
  constructor
  · intro h n
    obtain ⟨g, rfl⟩ := h
    refine ⟨PowerSeries.coeff n g, ?_⟩
    change PowerSeries.coeff n (PowerSeries.map (algebraMap R ℂ) g) =
      algebraMap R ℂ (PowerSeries.coeff n g)
    exact PowerSeries.coeff_map (algebraMap R ℂ) n g
  · intro h
    choose r hr using h
    refine ⟨PowerSeries.mk r, ?_⟩
    ext n
    calc
      PowerSeries.coeff n
          ((coeToComplexPowerSeries.ringHom R) (PowerSeries.mk r)) =
          algebraMap R ℂ (PowerSeries.coeff n (PowerSeries.mk r)) := by
        exact PowerSeries.coeff_map (algebraMap R ℂ) n (PowerSeries.mk r)
      _ = algebraMap R ℂ (r n) := by simp
      _ = PowerSeries.coeff n f := (hr n).symm

noncomputable def toRIntegralPowerSeries (R : Type*) [CommRing R] [Algebra R ℂ]
    {f : PowerSeries ℂ} (hf : IsRIntegralPowerSeries R f) : PowerSeries R :=
  Classical.choose hf

lemma coeToComplexPowerSeries_of_toRIntegralPowerSeries
    (R : Type*) [CommRing R] [Algebra R ℂ] {f : PowerSeries ℂ}
    (hf : IsRIntegralPowerSeries R f) :
    (coeToComplexPowerSeries.ringHom R) (toRIntegralPowerSeries R hf) = f :=
  Classical.choose_spec hf

/-! ### The old integer-specialised API -/

abbrev hom : ℤ →+* ℂ :=
  algebraMap ℤ ℂ

noncomputable abbrev IntegralPowerSeriesSubring : Subring (PowerSeries ℂ) :=
  RIntegralPowerSeriesSubring ℤ

abbrev IsIntegralPowerSeries (x : PowerSeries ℂ) : Prop :=
  IsRIntegralPowerSeries ℤ x

lemma int_iff (f : PowerSeries ℂ) : IsIntegralPowerSeries f ↔
    ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n f = z := by
  simpa [IsIntegralPowerSeries] using
    (isRIntegralPowerSeries_iff_coeff ℤ f)

noncomputable abbrev toIntegralPowerSeries {f : PowerSeries ℂ}
    (hf : IsIntegralPowerSeries f) : PowerSeries ℤ :=
  toRIntegralPowerSeries ℤ hf

lemma coeTo_of_toIntegralPowerSeries {f : PowerSeries ℂ}
    (hf : IsIntegralPowerSeries f) :
    (coeToComplexPowerSeries.ringHom ℤ) (toIntegralPowerSeries hf) = f :=
  coeToComplexPowerSeries_of_toRIntegralPowerSeries ℤ hf

lemma IsIntegralPowerSeriesmod {c : ℤ} (hc : c ≠ 0) {f : PowerSeries ℂ}
    (hf : IsIntegralPowerSeries f) (hmod : ∀ n : ℕ, Int.ModEq c
    ((toIntegralPowerSeries hf).coeff n) 0) : IsIntegralPowerSeries ((1 / c : ℂ) • f) := by
  rw [int_iff]
  intro n
  let g : PowerSeries ℤ := toIntegralPowerSeries hf
  have hg : (coeToComplexPowerSeries.ringHom ℤ) g = f := by
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
    PowerSeries.coeff n ((1 / c : ℂ) • f) = (1 / c : ℂ) * f.coeff n := by simp
    _ = (1 / c : ℂ) * (g.coeff n : ℂ) := by simp [hgn]
    _ = (1 / c : ℂ) * ((c * t : ℤ) : ℂ) := by simp [ht]
    _ = (1 / c : ℂ) * ((c : ℂ) * (t : ℂ)) := by norm_cast
    _ = t := by simp [hc]

end IntegralPowerSeries

#min_imports
