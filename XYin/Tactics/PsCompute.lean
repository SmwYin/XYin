import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import XYin.Tactics.ps_compute

open scoped BigOperators
open PowerSeries

namespace PsComputeTests

section CommRing

variable {R : Type*} [CommRing R]
variable {F G H : PowerSeries R}

/-! ## Basic local coefficient data -/

example {x : R} (hx : PowerSeries.coeff 2 F = x) :
    PowerSeries.coeff 2 F = x := by
  ps_compute

example {x : R} (hx : x = PowerSeries.coeff 2 F) :
    PowerSeries.coeff 2 F = x := by
  ps_compute

example {a : ℕ → R} (ha : ∀ n, PowerSeries.coeff n F = a n) :
    PowerSeries.coeff 7 F = a 7 := by
  ps_compute

example {a : ℕ → R} (ha : ∀ n, a n = PowerSeries.coeff n F) :
    PowerSeries.coeff 7 F = a 7 := by
  ps_compute

example {a : ℕ → R} :
    PowerSeries.coeff 3 (PowerSeries.mk a) = a 3 := by
  ps_compute

/-! ## Direct data for composite expressions must be used before decomposition -/

example {s : R} (hs : PowerSeries.coeff 2 (F + G) = s) :
    PowerSeries.coeff 2 (F + G) = s := by
  ps_compute

example {s : R} (hs : s = PowerSeries.coeff 2 (F * G)) :
    PowerSeries.coeff 2 (F * G) = s := by
  ps_compute

/-! ## Constants, numerals, X -/

example {c : R} :
    PowerSeries.coeff 0 (PowerSeries.C c) = c := by
  ps_compute

example {c : R} :
    ∃ x : R, PowerSeries.coeff 3 (PowerSeries.C c) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 0 (0 : PowerSeries R) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 4 (0 : PowerSeries R) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 0 (1 : PowerSeries R) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 3 (1 : PowerSeries R) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 0 (2 : PowerSeries R) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 5 (2 : PowerSeries R) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 1 (PowerSeries.X : PowerSeries R) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 0 (PowerSeries.X : PowerSeries R) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 4 (PowerSeries.X : PowerSeries R) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 3 ((PowerSeries.X : PowerSeries R) ^ 3) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 2 ((PowerSeries.X : PowerSeries R) ^ 3) = x := by
  ps_compute

/-! ## Addition, negation, subtraction -/

example {f2 g2 : R}
    (hf2 : PowerSeries.coeff 2 F = f2)
    (hg2 : PowerSeries.coeff 2 G = g2) :
    PowerSeries.coeff 2 (F + G) = f2 + g2 := by
  ps_compute

example {f2 : R}
    (hf2 : PowerSeries.coeff 2 F = f2) :
    PowerSeries.coeff 2 (-F) = -f2 := by
  ps_compute

example {f2 g2 : R}
    (hf2 : PowerSeries.coeff 2 F = f2)
    (hg2 : PowerSeries.coeff 2 G = g2) :
    PowerSeries.coeff 2 (F - G) = f2 - g2 := by
  ps_compute

/-! ## Multiplication from point coefficients -/

example {f0 f1 f2 g0 g1 g2 : R}
    (hf0 : PowerSeries.coeff 0 F = f0)
    (hf1 : PowerSeries.coeff 1 F = f1)
    (hf2 : PowerSeries.coeff 2 F = f2)
    (hg0 : PowerSeries.coeff 0 G = g0)
    (hg1 : PowerSeries.coeff 1 G = g1)
    (hg2 : PowerSeries.coeff 2 G = g2) :
    PowerSeries.coeff 2 (F * G) =
      f0 * g2 + f1 * g1 + f2 * g0 := by
  ps_compute

example {f0 f1 f2 g0 g1 g2 : R}
    (hf0 : PowerSeries.coeff 0 F = f0)
    (hf1 : PowerSeries.coeff 1 F = f1)
    (hf2 : PowerSeries.coeff 2 F = f2)
    (hg0 : PowerSeries.coeff 0 G = g0)
    (hg1 : PowerSeries.coeff 1 G = g1)
    (hg2 : PowerSeries.coeff 2 G = g2) :
    f0 * g2 + f1 * g1 + f2 * g0 =
      PowerSeries.coeff 2 (F * G) := by
  ps_compute

/- Lean 4.30 resolves explicit declaration-header `_` before tactic bodies.
   These examples test the same ps_compute metavariable assignment behavior in
   proof-state goals. -/
example {f0 f1 f2 g0 g1 g2 : R}
    (hf0 : PowerSeries.coeff 0 F = f0)
    (hf1 : PowerSeries.coeff 1 F = f1)
    (hf2 : PowerSeries.coeff 2 F = f2)
    (hg0 : PowerSeries.coeff 0 G = g0)
    (hg1 : PowerSeries.coeff 1 G = g1)
    (hg2 : PowerSeries.coeff 2 G = g2) :
    ∃ x : R, PowerSeries.coeff 2 (F * G) = x := by
  ps_compute

/-! ## Multiplication from forall coefficient data -/

example {a b : ℕ → R}
    (ha : ∀ n, PowerSeries.coeff n F = a n)
    (hb : ∀ n, PowerSeries.coeff n G = b n) :
    PowerSeries.coeff 3 (F * G) =
      a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0 := by
  ps_compute

example {a b : ℕ → R}
    (ha : ∀ n, a n = PowerSeries.coeff n F)
    (hb : ∀ n, b n = PowerSeries.coeff n G) :
    PowerSeries.coeff 3 (F * G) =
      a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0 := by
  ps_compute

/-! ## Truncation data -/

example {p : Polynomial R}
    (hp : PowerSeries.trunc 4 F = p) :
    PowerSeries.coeff 3 F = p.coeff 3 := by
  ps_compute

example {p : Polynomial R}
    (hp : p = PowerSeries.trunc 4 F) :
    PowerSeries.coeff 3 F = p.coeff 3 := by
  ps_compute

example {p q : Polynomial R}
    (hp : PowerSeries.trunc 3 F = p)
    (hq : q = PowerSeries.trunc 3 G) :
    PowerSeries.coeff 2 (F * G) =
      p.coeff 0 * q.coeff 2 +
      p.coeff 1 * q.coeff 1 +
      p.coeff 2 * q.coeff 0 := by
  ps_compute

example {a : ℕ → R} {q : Polynomial R}
    (ha : ∀ n, PowerSeries.coeff n F = a n)
    (hq : PowerSeries.trunc 4 G = q) :
    PowerSeries.coeff 3 (F * G) =
      a 0 * q.coeff 3 +
      a 1 * q.coeff 2 +
      a 2 * q.coeff 1 +
      a 3 * q.coeff 0 := by
  ps_compute

/-! ## Multiplication by constants and sparse series should not require unnecessary coefficients -/

example {c f3 : R}
    (hf3 : PowerSeries.coeff 3 F = f3) :
    PowerSeries.coeff 3 (PowerSeries.C c * F) = c * f3 := by
  ps_compute

example {c f3 : R}
    (hf3 : PowerSeries.coeff 3 F = f3) :
    PowerSeries.coeff 3 (F * PowerSeries.C c) = f3 * c := by
  ps_compute

example {f3 : R}
    (hf3 : PowerSeries.coeff 3 F = f3) :
    PowerSeries.coeff 4 ((PowerSeries.X : PowerSeries R) * F) = f3 := by
  ps_compute

example {f3 : R}
    (hf3 : PowerSeries.coeff 3 F = f3) :
    PowerSeries.coeff 4 (F * (PowerSeries.X : PowerSeries R)) = f3 := by
  ps_compute

example {f2 : R}
    (hf2 : PowerSeries.coeff 2 F = f2) :
    PowerSeries.coeff 5 (((PowerSeries.X : PowerSeries R) ^ 3) * F) = f2 := by
  ps_compute

example {f2 : R}
    (hf2 : PowerSeries.coeff 2 F = f2) :
    PowerSeries.coeff 5 (F * ((PowerSeries.X : PowerSeries R) ^ 3)) = f2 := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 2 (((PowerSeries.X : PowerSeries R) ^ 3) * F) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 4 ((0 : PowerSeries R) * F) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 4 (F * (0 : PowerSeries R)) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 4 (PowerSeries.C (0 : R) * F) = x := by
  ps_compute

/-! ## Powers -/

example :
    ∃ x : R, PowerSeries.coeff 0 (F ^ 0) = x := by
  ps_compute

example :
    ∃ x : R, PowerSeries.coeff 3 (F ^ 0) = x := by
  ps_compute

example {f2 : R}
    (hf2 : PowerSeries.coeff 2 F = f2) :
    PowerSeries.coeff 2 (F ^ 1) = f2 := by
  ps_compute

example {f0 f1 f2 : R}
    (hf0 : PowerSeries.coeff 0 F = f0)
    (hf1 : PowerSeries.coeff 1 F = f1)
    (hf2 : PowerSeries.coeff 2 F = f2) :
    PowerSeries.coeff 2 (F ^ 2) =
      f0 * f2 + f1 * f1 + f2 * f0 := by
  ps_compute

example {f0 f1 f2 : R}
    (hF0 : PowerSeries.coeff 0 F = f0)
    (hF1 : PowerSeries.coeff 1 F = f1)
    (hF2 : PowerSeries.coeff 2 F = f2) :
    PowerSeries.coeff 2 (F ^ 2) =
      f0 * f2 + f1 * f1 + f2 * f0 := by
  ps_compute

example {f0 f1 f2 f3 : R}
    (hf0 : PowerSeries.coeff 0 F = f0)
    (hf1 : PowerSeries.coeff 1 F = f1)
    (hf2 : PowerSeries.coeff 2 F = f2)
    (hf3 : PowerSeries.coeff 3 F = f3) :
    PowerSeries.coeff 3 (F ^ 2) =
      f0 * f3 + f1 * f2 + f2 * f1 + f3 * f0 := by
  ps_compute

example {f0 f1 f2 g0 g1 g2 : R}
    (hf0 : PowerSeries.coeff 0 F = f0)
    (hf1 : PowerSeries.coeff 1 F = f1)
    (hf2 : PowerSeries.coeff 2 F = f2)
    (hg0 : PowerSeries.coeff 0 G = g0)
    (hg1 : PowerSeries.coeff 1 G = g1)
    (hg2 : PowerSeries.coeff 2 G = g2) :
    PowerSeries.coeff 2 ((F + G) ^ 2) =
      (f0 + g0) * (f2 + g2) +
      (f1 + g1) * (f1 + g1) +
      (f2 + g2) * (f0 + g0) := by
  ps_compute

/-! ## Nested expressions -/

example {c f0 f1 f2 g0 g1 g2 : R}
    (hf0 : PowerSeries.coeff 0 F = f0)
    (hf1 : PowerSeries.coeff 1 F = f1)
    (hf2 : PowerSeries.coeff 2 F = f2)
    (hg0 : PowerSeries.coeff 0 G = g0)
    (hg1 : PowerSeries.coeff 1 G = g1)
    (hg2 : PowerSeries.coeff 2 G = g2) :
    PowerSeries.coeff 2 ((F - PowerSeries.C c * G) * (F + G)) =
      (f0 - c * g0) * (f2 + g2) +
      (f1 - c * g1) * (f1 + g1) +
      (f2 - c * g2) * (f0 + g0) := by
  ps_compute

/-! ## mk expressions in products -/

example {a b : ℕ → R} :
    PowerSeries.coeff 2 (PowerSeries.mk a * PowerSeries.mk b) =
      a 0 * b 2 + a 1 * b 1 + a 2 * b 0 := by
  ps_compute

/-! ## Scalar smul -/

example {a f2 : R}
    (hF2 : PowerSeries.coeff 2 F = f2) :
    PowerSeries.coeff 2 (a • F) = a * f2 := by
  ps_compute

example {a f2 : R}
    (hF2 : PowerSeries.coeff 2 F = f2) :
    a * f2 = PowerSeries.coeff 2 (a • F) := by
  ps_compute

example {a f0 f1 f2 g0 g1 g2 : R}
    (hf0 : PowerSeries.coeff 0 F = f0)
    (hf1 : PowerSeries.coeff 1 F = f1)
    (hf2 : PowerSeries.coeff 2 F = f2)
    (hg0 : PowerSeries.coeff 0 G = g0)
    (hg1 : PowerSeries.coeff 1 G = g1)
    (hg2 : PowerSeries.coeff 2 G = g2) :
    PowerSeries.coeff 2 ((a : R) • (F ^ 3 - G ^ 2)) =
      a * (((f0 * f0) * f2 + (f0 * f1 + f1 * f0) * f1 +
        (f0 * f2 + f1 * f1 + f2 * f0) * f0) -
        (g0 * g2 + g1 * g1 + g2 * g0)) := by
  ps_compute

/-! ## Failure behavior: ordinary ps_compute should not produce partial results -/

example {f0 g0 : R}
    (_hf0 : PowerSeries.coeff 0 F = f0)
    (_hg0 : PowerSeries.coeff 0 G = g0) :
    True := by
  fail_if_success
    have h : PowerSeries.coeff 1 (F * G) = f0 * g0 := by
      ps_compute
  trivial

example {p : Polynomial R}
    (hp : PowerSeries.trunc 1 F = p) :
    True := by
  have hp_use := hp
  clear hp_use
  fail_if_success
    have h : PowerSeries.coeff 1 F = p.coeff 1 := by
      ps_compute
  trivial

example {n : ℕ} {x : R} :
    True := by
  have hn_use : n = n := rfl
  have hx_use : x = x := rfl
  clear hn_use hx_use
  fail_if_success
    have h : PowerSeries.coeff n F = x := by
      ps_compute
  trivial

end CommRing

/-! ## It must work over ℤ, not just fields -/

section Integers

variable {F G : PowerSeries ℤ}

example {f0 f1 f2 g0 g1 g2 : ℤ}
    (hf0 : PowerSeries.coeff 0 F = f0)
    (hf1 : PowerSeries.coeff 1 F = f1)
    (hf2 : PowerSeries.coeff 2 F = f2)
    (hg0 : PowerSeries.coeff 0 G = g0)
    (hg1 : PowerSeries.coeff 1 G = g1)
    (hg2 : PowerSeries.coeff 2 G = g2) :
    PowerSeries.coeff 2 (F * G) =
      f0 * g2 + f1 * g1 + f2 * g0 := by
  ps_compute

example {p q : Polynomial ℤ}
    (hp : PowerSeries.trunc 3 F = p)
    (hq : PowerSeries.trunc 3 G = q) :
    PowerSeries.coeff 2 (F * G) =
      p.coeff 0 * q.coeff 2 +
      p.coeff 1 * q.coeff 1 +
      p.coeff 2 * q.coeff 0 := by
  ps_compute

end Integers

/-! ## Deltaaux-shaped complex coefficient -/

section Complex

variable {F G : PowerSeries ℂ}

example
    (hF0 : PowerSeries.coeff 0 F = 0)
    (hF1 : PowerSeries.coeff 1 F = 0)
    (hF2 : PowerSeries.coeff 2 F = 0)
    (hG0 : PowerSeries.coeff 0 G = 1)
    (hG1 : PowerSeries.coeff 1 G = 0)
    (hG2 : PowerSeries.coeff 2 G = 20736) :
    ∃ x : ℂ, PowerSeries.coeff 2 (((1 / 1728 : ℂ) • (F ^ 3 - G ^ 2))) = x := by
  ps_compute

end Complex

/-!
Manual InfoView tests for `ps_compute?`.
These are not automated because exact message formatting is not stable.
Run them interactively and check that the report contains:
- target;
- sufficient coefficient data;
- found coefficients with source hypotheses;
- missing coefficients;
- no metavariable assignment;
- no goal closure.

Example 1: missing data.
```lean
example {R : Type*} [CommRing R]
    {F G : PowerSeries R} {f0 g0 g1 g2 : R}
    (hf0 : PowerSeries.coeff 0 F = f0)
    (hg0 : PowerSeries.coeff 0 G = g0)
    (hg1 : PowerSeries.coeff 1 G = g1)
    (hg2 : PowerSeries.coeff 2 G = g2) :
    PowerSeries.coeff 2 (F * G) = f0 * g2 := by
  ps_compute?
```
-/

/-! ## Smoke tests formerly local to `ps_compute.lean` -/

section SmokeTest

example : ∃ x : ℤ, PowerSeries.coeff (R := ℤ) 2 (PowerSeries.mk fun n => (n : ℤ) + 1) = x := by
  ps_compute

example : ∃ x : ℤ, PowerSeries.coeff (R := ℤ) 3 (PowerSeries.C (5 : ℤ)) = x := by
  ps_compute

example : ∃ x : ℤ, PowerSeries.coeff (R := ℤ) 1 (PowerSeries.X : PowerSeries ℤ) = x := by
  ps_compute

example : ∃ x : ℤ, PowerSeries.coeff (R := ℤ) 2 ((PowerSeries.X : PowerSeries ℤ) ^ 5) = x := by
  ps_compute

example : ∃ x : ℤ, PowerSeries.coeff (R := ℤ) 0 (7 : PowerSeries ℤ) = x := by
  ps_compute

example (f : PowerSeries ℤ) (x : ℤ) (h : PowerSeries.coeff 4 f = x) :
    ∃ y : ℤ, PowerSeries.coeff 4 f = y := by
  ps_compute

example (f : PowerSeries ℤ) (x : ℤ) (h : x = PowerSeries.coeff 4 f) :
    ∃ y : ℤ, PowerSeries.coeff 4 f = y := by
  ps_compute

example (F G : PowerSeries ℤ) (x : ℤ) (h : PowerSeries.coeff 2 (F + G) = x) :
    ∃ y : ℤ, PowerSeries.coeff 2 (F + G) = y := by
  ps_compute

example (f : PowerSeries ℤ) (a : ℕ → ℤ) (h : ∀ n, PowerSeries.coeff n f = a n) :
    ∃ x : ℤ, PowerSeries.coeff 3 f = x := by
  ps_compute

example (f : PowerSeries ℤ) (a : ℕ → ℤ) (h : ∀ n, a n = PowerSeries.coeff n f) :
    ∃ x : ℤ, PowerSeries.coeff 5 f = x := by
  ps_compute

example (f : PowerSeries ℤ) (p : Polynomial ℤ) (h : PowerSeries.trunc 4 f = p) :
    ∃ x : ℤ, PowerSeries.coeff 2 f = x := by
  ps_compute

example (f : PowerSeries ℤ) (p : Polynomial ℤ) (h : p = PowerSeries.trunc 7 f) :
    ∃ x : ℤ, PowerSeries.coeff 5 f = x := by
  ps_compute

example (f g : PowerSeries ℤ) (a b : ℤ)
    (hf : PowerSeries.coeff 3 f = a) (hg : PowerSeries.coeff 3 g = b) :
    ∃ x : ℤ, PowerSeries.coeff 3 (f + g) = x := by
  ps_compute

example (f : PowerSeries ℤ) (a : ℤ) (hf : PowerSeries.coeff 2 f = a) :
    ∃ x : ℤ, PowerSeries.coeff 2 (-f) = x := by
  ps_compute

example (f g : PowerSeries ℤ) (a b : ℤ)
    (hf : PowerSeries.coeff 1 f = a) (hg : PowerSeries.coeff 1 g = b) :
    ∃ x : ℤ, PowerSeries.coeff 1 (f - g) = x := by
  ps_compute

example (f g : PowerSeries ℤ) (f0 f1 f2 g0 g1 g2 : ℤ)
    (hf0 : PowerSeries.coeff 0 f = f0) (hf1 : PowerSeries.coeff 1 f = f1)
    (hf2 : PowerSeries.coeff 2 f = f2) (hg0 : PowerSeries.coeff 0 g = g0)
    (hg1 : PowerSeries.coeff 1 g = g1) (hg2 : PowerSeries.coeff 2 g = g2) :
    ∃ x : ℤ, PowerSeries.coeff 2 (f * g) = x := by
  ps_compute

example (f g : PowerSeries ℤ) (a b : ℕ → ℤ)
    (hf : ∀ n, PowerSeries.coeff n f = a n) (hg : ∀ n, PowerSeries.coeff n g = b n) :
    ∃ x : ℤ, PowerSeries.coeff 3 (f * g) = x := by
  ps_compute

example (f : PowerSeries ℤ) : ∃ x : ℤ, PowerSeries.coeff 0 (f ^ 0) = x := by
  ps_compute

example (f : PowerSeries ℤ) : ∃ x : ℤ, PowerSeries.coeff 3 (f ^ 0) = x := by
  ps_compute

example (f : PowerSeries ℤ) (f2 : ℤ) (hf2 : PowerSeries.coeff 2 f = f2) :
    ∃ x : ℤ, PowerSeries.coeff 2 (f ^ 1) = x := by
  ps_compute

example (f : PowerSeries ℤ) (f0 f1 f2 : ℤ)
    (hf0 : PowerSeries.coeff 0 f = f0)
    (hf1 : PowerSeries.coeff 1 f = f1)
    (hf2 : PowerSeries.coeff 2 f = f2) :
    ∃ x : ℤ, PowerSeries.coeff 2 (f ^ 2) = x := by
  ps_compute

example (f : PowerSeries ℤ) (f0 f1 f2 f3 : ℤ)
    (hf0 : PowerSeries.coeff 0 f = f0)
    (hf1 : PowerSeries.coeff 1 f = f1)
    (hf2 : PowerSeries.coeff 2 f = f2)
    (hf3 : PowerSeries.coeff 3 f = f3) :
    ∃ x : ℤ, PowerSeries.coeff 3 (f ^ 2) = x := by
  ps_compute

example (F G : PowerSeries ℤ) (s0 s1 s2 : ℤ)
    (hs0 : PowerSeries.coeff 0 (F + G) = s0)
    (hs1 : PowerSeries.coeff 1 (F + G) = s1)
    (hs2 : PowerSeries.coeff 2 (F + G) = s2) :
    ∃ x : ℤ, PowerSeries.coeff 2 ((F + G) ^ 2) = x := by
  ps_compute

example (f : PowerSeries ℤ) (c f2 : ℤ) (hf2 : PowerSeries.coeff 2 f = f2) :
    ∃ x : ℤ, PowerSeries.coeff 2 (PowerSeries.C c * f) = x := by
  ps_compute

example (f : PowerSeries ℤ) (c f2 : ℤ) (hf2 : PowerSeries.coeff 2 f = f2) :
    ∃ x : ℤ, PowerSeries.coeff 2 (f * PowerSeries.C c) = x := by
  ps_compute

example (f : PowerSeries ℤ) (f3 : ℤ) (hf3 : PowerSeries.coeff 3 f = f3) :
    ∃ x : ℤ, PowerSeries.coeff 4 ((PowerSeries.X : PowerSeries ℤ) * f) = x := by
  ps_compute

example (f : PowerSeries ℤ) (f3 : ℤ) (hf3 : PowerSeries.coeff 3 f = f3) :
    ∃ x : ℤ, PowerSeries.coeff 4 (f * (PowerSeries.X : PowerSeries ℤ)) = x := by
  ps_compute

example (f : PowerSeries ℤ) (f2 : ℤ) (hf2 : PowerSeries.coeff 2 f = f2) :
    ∃ x : ℤ, PowerSeries.coeff 5 (((PowerSeries.X : PowerSeries ℤ) ^ 3) * f) = x := by
  ps_compute

example (f : PowerSeries ℤ) (f2 : ℤ) (hf2 : PowerSeries.coeff 2 f = f2) :
    ∃ x : ℤ, PowerSeries.coeff 5 (f * ((PowerSeries.X : PowerSeries ℤ) ^ 3)) = x := by
  ps_compute

example (f : PowerSeries ℤ) :
    ∃ x : ℤ, PowerSeries.coeff 2 (((PowerSeries.X : PowerSeries ℤ) ^ 3) * f) = x := by
  ps_compute

end SmokeTest

end PsComputeTests
