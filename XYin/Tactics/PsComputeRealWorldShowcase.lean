import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Schroder
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import XYin.Tactics.ps_compute

open PowerSeries

namespace PsComputeRealWorldShowcase

noncomputable section

abbrev QSeries := PowerSeries ℚ

noncomputable abbrev geom : QSeries := PowerSeries.invUnitsSub (1 : ℚˣ)

private lemma coeff_geom (n : ℕ) : PowerSeries.coeff n geom = (1 : ℚ) := by
  simp [geom, PowerSeries.coeff_invUnitsSub]

noncomputable abbrev fibDen : QSeries := (1 : QSeries) - PowerSeries.X - PowerSeries.X ^ 2

noncomputable abbrev fibGF : QSeries := fibDen⁻¹

noncomputable abbrev binom8 : QSeries := (PowerSeries.invOneSubPow ℚ 8).val

private lemma coeff_binom8 (n : ℕ) :
    PowerSeries.coeff n binom8 = ((Nat.choose (7 + n) 7 : ℕ) : ℚ) := by
  simp [binom8, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]

noncomputable abbrev binom9 : QSeries := (PowerSeries.invOneSubPow ℚ 9).val

private lemma coeff_binom9 (n : ℕ) :
    PowerSeries.coeff n binom9 = ((Nat.choose (8 + n) 8 : ℕ) : ℚ) := by
  simp [binom9, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]

noncomputable abbrev binom13 : QSeries := (PowerSeries.invOneSubPow ℚ 13).val

private lemma coeff_binom13 (n : ℕ) :
    PowerSeries.coeff n binom13 = ((Nat.choose (12 + n) 12 : ℕ) : ℚ) := by
  simp [binom13, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]

noncomputable abbrev binom21 : QSeries := (PowerSeries.invOneSubPow ℚ 21).val

private lemma coeff_binom21 (n : ℕ) :
    PowerSeries.coeff n binom21 = ((Nat.choose (20 + n) 20 : ℕ) : ℚ) := by
  simp [binom21, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]

private lemma binom8_mul_binom13 : binom8 * binom13 = binom21 := by
  change (PowerSeries.invOneSubPow ℚ 8).val * (PowerSeries.invOneSubPow ℚ 13).val =
      (PowerSeries.invOneSubPow ℚ 21).val
  simpa using Eq.symm
    (congrArg Units.val (PowerSeries.invOneSubPow_add (S := ℚ) (d := 8) (e := 13)))

private lemma geom_mul_binom8 : geom * binom8 = binom9 := by
  change PowerSeries.invUnitsSub (1 : ℚˣ) * (PowerSeries.invOneSubPow ℚ 8).val =
      (PowerSeries.invOneSubPow ℚ 9).val
  rw [← PowerSeries.invOneSubPow_val_one_eq_invUnitSub_one]
  simpa using Eq.symm
    (congrArg Units.val (PowerSeries.invOneSubPow_add (S := ℚ) (d := 1) (e := 8)))

noncomputable abbrev expQ : QSeries := PowerSeries.exp ℚ

private lemma coeff_expQ (n : ℕ) :
    PowerSeries.coeff n expQ = (1 / (Nat.factorial n : ℚ)) := by
  simp [expQ]

noncomputable abbrev polyShift : QSeries :=
  PowerSeries.C (5 : ℚ) - PowerSeries.C (2 : ℚ) * PowerSeries.X + (PowerSeries.X : QSeries) ^ 3

-- Geometric series and a Fibonacci-like denominator inverse.
example : ∃ x : ℚ, PowerSeries.coeff 12 geom = x := by
  have hgeom : ∀ n, PowerSeries.coeff n geom = (1 : ℚ) := coeff_geom
  ps_compute

example : ∃ x : ℚ, PowerSeries.coeff 6 fibGF = x := by
  ps_compute

example : ∃ x : ℚ, PowerSeries.coeff 5 (((1 : QSeries) + PowerSeries.X) * fibGF) = x := by
  ps_compute

-- High-order binomial inverse convolution.
example : ∃ x : ℚ, PowerSeries.coeff 16 (binom8 * binom13) = x := by
  rw [binom8_mul_binom13]
  have hbinom21 : ∀ n, PowerSeries.coeff n binom21 = ((Nat.choose (20 + n) 20 : ℕ) : ℚ) :=
    coeff_binom21
  ps_compute

example : ∃ x : ℚ, PowerSeries.coeff 40 (binom8 * binom13) = x := by
  rw [binom8_mul_binom13]
  have hbinom21 : ∀ n, PowerSeries.coeff n binom21 = ((Nat.choose (20 + n) 20 : ℕ) : ℚ) :=
    coeff_binom21
  ps_compute

-- Exponential generating series convolution.
example : ∃ x : ℚ, PowerSeries.coeff 6 (expQ * expQ) = x := by
  have hexp : ∀ n, PowerSeries.coeff n expQ = (1 / (Nat.factorial n : ℚ)) := coeff_expQ
  ps_compute

example : ∃ x : ℚ, PowerSeries.coeff 6 (expQ * expQ * expQ) = x := by
  have hexp : ∀ n, PowerSeries.coeff n expQ = (1 / (Nat.factorial n : ℚ)) := coeff_expQ
  ps_compute

-- A mixed composite expression with polynomial shifts and known series.
example : ∃ x : ℚ, PowerSeries.coeff 5 (polyShift * geom * binom8) = x := by
  rw [mul_assoc, geom_mul_binom8]
  have hbinom9 : ∀ n, PowerSeries.coeff n binom9 = ((Nat.choose (8 + n) 8 : ℕ) : ℚ) :=
    coeff_binom9
  ps_compute

-- Other coefficient rings: keep these lightweight but concrete.
example : ∃ x : ℂ, PowerSeries.coeff 4
    (PowerSeries.C (Complex.I : ℂ) * (PowerSeries.X : PowerSeries ℂ) ^ 4
      + PowerSeries.C (3 : ℂ) * (PowerSeries.X : PowerSeries ℂ) ^ 2) = x := by
  ps_compute

example : ∃ x : ℝ, PowerSeries.coeff 3
    ((PowerSeries.C (2 : ℝ) + PowerSeries.C (5 : ℝ) * PowerSeries.X)
      * PowerSeries.invUnitsSub (1 : ℝˣ)) = x := by
  have hgeomR : ∀ n, PowerSeries.coeff n (PowerSeries.invUnitsSub (1 : ℝˣ)) = (1 : ℝ) := by
    intro n
    simp [PowerSeries.coeff_invUnitsSub]
  ps_compute

-- Catalan / Large Schröder generating-function examples.
example : ∃ x : ℕ, PowerSeries.coeff 12 PowerSeries.catalanSeries = x := by
  ps_compute

example :
    ∃ x : ℕ, PowerSeries.coeff 9 (PowerSeries.catalanSeries ^ 2 * PowerSeries.X + 1) = x := by
  rw [PowerSeries.catalanSeries_sq_mul_X_add_one]
  ps_compute

example : ∃ x : ℕ, PowerSeries.coeff 10 PowerSeries.largeSchroderSeries = x := by
  ps_compute

example :
    ∃ x : ℕ, PowerSeries.coeff 8
      (1 + PowerSeries.X * PowerSeries.largeSchroderSeries
        + PowerSeries.X * PowerSeries.largeSchroderSeries ^ 2) = x := by
  rw [← PowerSeries.largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq]
  ps_compute

end

end PsComputeRealWorldShowcase
