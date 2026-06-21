import XYin.Test.JLevelN.Theorem1118

open Polynomial

/-!
# Cox Theorem 11.18(iii) / Lang Theorem 3(ii): symmetry — the algebraic endgame

This file formalises **Lang's symmetry argument** (Lang, *Elliptic Functions* §2, Theorem 3(ii);
Cox 11.18(iii)) in its purely algebraic form, needing **no modular function field**.

`modularPolynomial_swap_of_dvd_of_irreducible`: if `Φ_m` is irreducible, has degree `> 1` in the
outer variable, and divides its own `Bivariate.swap`, then it equals its swap.  The two
hypotheses (`Irreducible` and the self-divisibility) are exactly the input that Cox Exercise 11.10
/ the transitive-action / function-field work (T021/T023) supply; everything downstream — the
Gauss `swap Φ = g·Φ`, `g·gˢʷᵃᵖ = 1`, `g = ±1`, and the `g = −1` contradiction via the diagonal —
is discharged here with no new infrastructure.
-/

noncomputable section

namespace ModularSymmetry

/-- The diagonal `Φ ↦ Φ(X,X)` (evaluating the outer variable at the inner `X`) is invariant under
`Bivariate.swap`. -/
theorem swap_eval_X (p : Polynomial (Polynomial ℤ)) :
    (Polynomial.Bivariate.swap p).eval Polynomial.X = p.eval Polynomial.X := by
  have hsX : Polynomial.Bivariate.swap (Polynomial.X : Polynomial (Polynomial ℤ)) =
      Polynomial.C Polynomial.X := by
    rw [← Polynomial.Bivariate.swap_X (R := ℤ), Polynomial.Bivariate.swap_swap_apply]
  induction p using Polynomial.induction_on with
  | C q => simp [Polynomial.Bivariate.swap_C, Polynomial.eval_map, Polynomial.eval₂_C_X]
  | add p q hp hq => simp [hp, hq]
  | monomial n a _ =>
      simp [map_mul, map_pow, Polynomial.Bivariate.swap_C, Polynomial.eval_map,
        Polynomial.eval₂_C_X, hsX]

/-- **Lang's symmetry endgame** (Cox 11.18(iii) / Lang Thm 3(ii)), algebraic core. -/
theorem modularPolynomial_swap_of_dvd_of_irreducible (m : ℕ+)
    (hdeg : 1 < (modularPolynomial m).natDegree)
    (hirr : Irreducible (modularPolynomial m))
    (hdvd : modularPolynomial m ∣ Polynomial.Bivariate.swap (modularPolynomial m)) :
    Polynomial.Bivariate.swap (modularPolynomial m) = modularPolynomial m := by
  obtain ⟨g, hg⟩ := hdvd
  -- hg : swap Φ = Φ * g
  have hΦ0 : modularPolynomial m ≠ 0 := hirr.ne_zero
  -- g * swap g = 1
  have h2 : modularPolynomial m =
      modularPolynomial m * g * Polynomial.Bivariate.swap g := by
    have := congrArg Polynomial.Bivariate.swap hg
    rwa [Polynomial.Bivariate.swap_swap_apply, map_mul, hg] at this
  have hunit : g * Polynomial.Bivariate.swap g = 1 := by
    have h3 : modularPolynomial m * (g * Polynomial.Bivariate.swap g) =
        modularPolynomial m * 1 := by rw [mul_one, ← mul_assoc]; exact h2.symm
    exact mul_left_cancel₀ hΦ0 h3
  have hgunit : IsUnit g := IsUnit.of_mul_eq_one (Polynomial.Bivariate.swap g) hunit
  -- g = ±1
  obtain ⟨r, hr_unit, hr⟩ := Polynomial.isUnit_iff.mp hgunit
  obtain ⟨s, hs_unit, hs⟩ := Polynomial.isUnit_iff.mp hr_unit
  rcases Int.isUnit_iff.mp hs_unit with hs1 | hsm1
  · -- s = 1 ⟹ g = 1 ⟹ swap Φ = Φ
    have hg1 : g = 1 := by rw [← hr, ← hs, hs1]; simp
    rw [hg, hg1, mul_one]
  · -- s = -1 ⟹ g = -1 ⟹ contradiction via the diagonal
    exfalso
    have hgm1 : g = -1 := by rw [← hr, ← hs, hsm1]; simp
    rw [hgm1, mul_neg, mul_one] at hg   -- hg : swap Φ = -Φ
    -- diagonal vanishes
    have hdiag : (modularPolynomial m).eval Polynomial.X = 0 := by
      have e := swap_eval_X (modularPolynomial m)
      rw [hg, Polynomial.eval_neg] at e   -- -(Φ.eval X) = Φ.eval X
      have h2x : (2 : Polynomial ℤ) * (modularPolynomial m).eval Polynomial.X = 0 := by
        linear_combination -e
      exact (mul_eq_zero.mp h2x).resolve_left two_ne_zero
    -- (Y - C X) ∣ Φ
    have hfac : (Polynomial.X - Polynomial.C (Polynomial.X : Polynomial ℤ)) ∣
        modularPolynomial m := Polynomial.dvd_iff_isRoot.mpr hdiag
    -- irreducible ⟹ Φ ~ (Y - C X) ⟹ degree 1, contradicting hdeg
    obtain ⟨h, hh⟩ := hfac
    rcases hirr.isUnit_or_isUnit hh with hu | hu
    · exact (Polynomial.not_isUnit_X_sub_C _) hu
    · have hdeg1 : (modularPolynomial m).natDegree = 1 := by
        rw [hh, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _)
          (by rintro rfl; rw [mul_zero] at hh; exact hΦ0 hh),
          Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu]
      omega

end ModularSymmetry
