import XYin.Tactics.j_coeffs

open PowerSeries
open scoped ArithmeticFunction.sigma

open XYin.Tactics

def E4q : PowerSeries ℂ := PowerSeries.mk (Function.update (fun m => (240 : ℂ) * σ 3 m) 0 1)
def E6q : PowerSeries ℂ := PowerSeries.mk (Function.update (fun m => -(504 : ℂ) * σ 5 m) 0 1)

noncomputable abbrev Delta_qexpansion := (1 / 1728 : ℂ) • (E4q ^ 3 - E6q ^ 2)
noncomputable abbrev Deltaoverq_qexpansion :=
  PowerSeries.mk (fun m => Delta_qexpansion.coeff (m + 1))
noncomputable abbrev qoverDelta_qexpansion := Deltaoverq_qexpansion⁻¹
noncomputable abbrev qj_qexpansion := E4q ^ 3 * Deltaoverq_qexpansion⁻¹

example : ∃ x, qj_qexpansion.coeff 0 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 1 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 2 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 3 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 4 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 5 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 6 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 7 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 8 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 9 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 10 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 15 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 20 = x := by
  j_coeffs

example : ∃ x, qj_qexpansion.coeff 50 = x := by
  j_coeffs
