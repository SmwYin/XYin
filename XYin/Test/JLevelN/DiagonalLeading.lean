import XYin.Test.JLevelN.Theorem1118
import XYin.Test.JLevelN.QExpansion1113

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups
  PowerSeries SlashInvariantFormClass Real Function IntegralPowerSeries Polynomial
open scoped Manifold

/-!
# Cox Theorem 11.18(iv): the diagonal `Φ_m(X,X)` (skeleton)

Cox pp. 232–233.  For non-square `m`, the most-negative `q`-coefficient of
`Φ_m(j(τ),j(τ)) = ∏_{σ∈C(m)} (j(τ) − j(στ))` is a root of unity: each factor's
most-negative term (11.19) has coefficient `1` or `−ζ_m^{-ab}` (since `a ≠ d`, the `t^{-m}`
and `t^{-a²}` terms do not combine), and the product of roots of unity is a root of unity.
Being an integer (Theorem 11.18(i)), it is `±1`.

The root-of-unity → `±1` step is discharged here; the geometric "bottom coefficient is a
root of unity" claim is the remaining `sorry`.
-/

noncomputable section

section IntRootOfUnity

/-- An integer that is a `k`-th root of unity (`k > 0`) is `±1`. -/
theorem Int.eq_one_or_neg_one_of_pow_eq_one {n : ℤ} {k : ℕ} (hk : 0 < k) (h : n ^ k = 1) :
    n = 1 ∨ n = -1 := by
  rw [← Int.isUnit_iff]
  exact IsUnit.of_pow_eq_one h hk.ne'

end IntRootOfUnity

section Diagonal

/-- (iv) core (Cox p. 233): for non-square `m`, the leading coefficient of `Φ_m(X,X)` is a
root of unity.  (Most-negative `q`-coefficient of `Φ_m(j,j)` = product of the `1`/`−ζ^{-ab}`
per-factor terms of (11.19).) -/
theorem modularPolynomialDiagonal_leadingCoeff_isRootOfUnity (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    ∃ k : ℕ, 0 < k ∧ (modularPolynomialDiagonal m).leadingCoeff ^ k = 1 := by
  sorry -- T015: needs jSigma product bottom-coeff multiplicativity + part (i) integrality (T013); blocked

/-- **Cox Theorem 11.18(iv), leading coefficient = ±1**, derived from the root-of-unity core
plus integrality.  (This matches `Theorem1118.modularPolynomialDiagonal_leadingCoeff`.) -/
theorem modularPolynomialDiagonal_leadingCoeff_eq_pm_one (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    (modularPolynomialDiagonal m).leadingCoeff = 1 ∨
      (modularPolynomialDiagonal m).leadingCoeff = -1 := by
  obtain ⟨k, hk, h⟩ := modularPolynomialDiagonal_leadingCoeff_isRootOfUnity m hm
  exact Int.eq_one_or_neg_one_of_pow_eq_one hk h

end Diagonal
