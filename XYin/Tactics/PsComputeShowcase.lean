import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Schroder
import XYin.Tactics.ps_compute

open PowerSeries

namespace PsComputeShowcase

noncomputable section

abbrev QSeries := PowerSeries ℚ

noncomputable abbrev geom : QSeries := PowerSeries.invUnitsSub (1 : ℚˣ)

private lemma coeff_geom (n : ℕ) : PowerSeries.coeff n geom = (1 : ℚ) := by
  simp [geom, PowerSeries.coeff_invUnitsSub]

noncomputable abbrev binom3 : QSeries := (PowerSeries.invOneSubPow ℚ 3).val

private lemma coeff_binom3 (n : ℕ) :
    PowerSeries.coeff n binom3 = ((Nat.choose (2 + n) 2 : ℕ) : ℚ) := by
  simp [binom3, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]

private lemma one_sub_cube_mul_binom3 : ((1 : QSeries) - PowerSeries.X) ^ 3 * binom3 = 1 := by
  change ((1 : QSeries) - PowerSeries.X) ^ (0 + 3) *
      (PowerSeries.invOneSubPow ℚ 3).val = ((1 : QSeries) - PowerSeries.X) ^ 0
  simpa [binom3] using
    PowerSeries.one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow (S := ℚ) (d := 0) (e := 3)

noncomputable abbrev expQ : QSeries := PowerSeries.exp ℚ

private lemma coeff_expQ (n : ℕ) :
    PowerSeries.coeff n expQ = (1 / (Nat.factorial n : ℚ)) := by
  simp [expQ]

noncomputable abbrev fibDen : QSeries :=
  (1 : QSeries) - PowerSeries.X - PowerSeries.X ^ 2

noncomputable abbrev fibGF : QSeries := fibDen⁻¹

noncomputable abbrev binom12 : QSeries := (PowerSeries.invOneSubPow ℚ 12).val

private lemma coeff_binom12 (n : ℕ) :
    PowerSeries.coeff n binom12 = ((Nat.choose (11 + n) 11 : ℕ) : ℚ) := by
  simp [binom12, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]

noncomputable abbrev binom21 : QSeries := (PowerSeries.invOneSubPow ℚ 21).val

private lemma coeff_binom21 (n : ℕ) :
    PowerSeries.coeff n binom21 = ((Nat.choose (20 + n) 20 : ℕ) : ℚ) := by
  simp [binom21, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]

noncomputable abbrev binom33 : QSeries := (PowerSeries.invOneSubPow ℚ 33).val

private lemma coeff_binom33 (n : ℕ) :
    PowerSeries.coeff n binom33 = ((Nat.choose (32 + n) 32 : ℕ) : ℚ) := by
  simp [binom33, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]

private lemma binom21_mul_binom12 : binom21 * binom12 = binom33 := by
  change (PowerSeries.invOneSubPow ℚ 21).val * (PowerSeries.invOneSubPow ℚ 12).val =
      (PowerSeries.invOneSubPow ℚ 33).val
  simpa [Nat.add_comm] using
    Eq.symm (congrArg Units.val (PowerSeries.invOneSubPow_add (S := ℚ) (d := 21) (e := 12)))

-- Basic polynomial coefficient.
example :
    ∃ x : ℚ, PowerSeries.coeff 7
      (PowerSeries.C (3 : ℚ) * (PowerSeries.X : QSeries) ^ 5
        + (PowerSeries.X : QSeries) ^ 7
        - PowerSeries.C (2 : ℚ) * (PowerSeries.X : QSeries) ^ 3) = x := by
  ps_compute

-- Geometric series examples.
example :
    ∃ x : ℚ, PowerSeries.coeff 5
      ((PowerSeries.C (2 : ℚ) + PowerSeries.C (3 : ℚ) * (PowerSeries.X : QSeries)) * geom) =
      x := by
  have hgeom : ∀ n, PowerSeries.coeff n geom = (1 : ℚ) := coeff_geom
  ps_compute

example : ∃ x : ℚ, PowerSeries.coeff 6 (geom ^ 3) = x := by
  have hgeom : ∀ n, PowerSeries.coeff n geom = (1 : ℚ) := coeff_geom
  ps_compute

-- Binomial inverse examples.
example : ∃ x : ℚ, PowerSeries.coeff 6 binom3 = x := by
  have hbinom3 : ∀ n, PowerSeries.coeff n binom3 = ((Nat.choose (2 + n) 2 : ℕ) : ℚ) :=
    coeff_binom3
  ps_compute

example :
    ∃ x : ℚ, PowerSeries.coeff 2 (((1 : QSeries) - PowerSeries.X) ^ 3 * binom3) = x := by
  rw [one_sub_cube_mul_binom3]
  ps_compute

-- Exponential series example.
example : ∃ x : ℚ, PowerSeries.coeff 5 (expQ * expQ) = x := by
  have hexp : ∀ n, PowerSeries.coeff n expQ = (1 / (Nat.factorial n : ℚ)) := coeff_expQ
  ps_compute

-- Fibonacci generating function examples.
example : ∃ x : ℚ, PowerSeries.coeff 6 fibGF = x := by
  ps_compute

example : ∃ x : ℚ, PowerSeries.coeff 7 fibGF = x := by
  ps_compute

-- Larger coefficient from a high-order binomial inverse.
example : ∃ x : ℚ, PowerSeries.coeff 50 binom21 = x := by
  have hbinom21 : ∀ n, PowerSeries.coeff n binom21 = ((Nat.choose (20 + n) 20 : ℕ) : ℚ) :=
    coeff_binom21
  ps_compute

-- Multi-step convolution with two large inverse-binomial series.
example : ∃ x : ℚ, PowerSeries.coeff 18 (binom21 * binom12) = x := by
  rw [binom21_mul_binom12]
  have hbinom33 : ∀ n, PowerSeries.coeff n binom33 = ((Nat.choose (32 + n) 32 : ℕ) : ℚ) :=
    coeff_binom33
  ps_compute

-- Catalan numbers: a classical combinatorial generating function.
example : ∃ x : ℕ, PowerSeries.coeff 12 PowerSeries.catalanSeries = x := by
  ps_compute

-- Same Catalan data through its functional equation side.
example :
    ∃ x : ℕ, PowerSeries.coeff 10 (PowerSeries.catalanSeries ^ 2 * PowerSeries.X + 1) = x := by
  rw [PowerSeries.catalanSeries_sq_mul_X_add_one]
  ps_compute

-- Large Schröder numbers from their generating series.
example : ∃ x : ℕ, PowerSeries.coeff 10 PowerSeries.largeSchroderSeries = x := by
  ps_compute

-- Schröder functional equation side, forcing deeper coefficient algebra.
example :
    ∃ x : ℕ, PowerSeries.coeff 8
      (1 + PowerSeries.X * PowerSeries.largeSchroderSeries
        + PowerSeries.X * PowerSeries.largeSchroderSeries ^ 2) = x := by
  rw [← PowerSeries.largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq]
  ps_compute

end

end PsComputeShowcase
