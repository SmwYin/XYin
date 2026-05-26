import XYin.Tactics.qexp_coeffs

open PowerSeries
open scoped ArithmeticFunction.sigma

open XYin.Tactics

def E4q : PowerSeries ℂ := PowerSeries.mk (Function.update (fun m => (240 : ℂ) * σ 3 m) 0 1)
def E6q : PowerSeries ℂ := PowerSeries.mk (Function.update (fun m => -(504 : ℂ) * σ 5 m) 0 1)

noncomputable abbrev Delta_qexpansion : PowerSeries ℂ :=
  (1 / 1728 : ℂ) • (E4q ^ 3 - E6q ^ 2)

noncomputable abbrev Deltaoverq_qexpansion : PowerSeries ℂ :=
  PowerSeries.mk (fun m => Delta_qexpansion.coeff (m + 1))

noncomputable abbrev DeltaShift2_qexpansion : PowerSeries ℂ :=
  PowerSeries.mk (fun m => Delta_qexpansion.coeff (m + 2))

noncomputable abbrev qj_qexpansion := E4q ^ 3 * Deltaoverq_qexpansion⁻¹

example : ∃ x : ℂ, PowerSeries.coeff 4 (E4q ^ 2 + E6q) = x := by
  qexp_coeffs

example : ∃ x : ℂ, PowerSeries.coeff 5 ((3 : ℂ) • (E4q * E6q) - E6q ^ 2) = x := by
  qexp_coeffs

example : ∃ x : ℂ, PowerSeries.coeff 3 ((E4q ^ 2 - E6q) * (E4q + E6q)) = x := by
  qexp_coeffs

example : ∃ x : ℂ, PowerSeries.coeff 2 ((E4q ^ 2 + E6q) * E4q⁻¹) = x := by
  qexp_coeffs

example : ∃ x : ℂ, PowerSeries.coeff 20 (E4q * E6q⁻¹) = x := by
  qexp_coeffs

example : ∃ x : ℂ, PowerSeries.coeff 10 ((E4q ^ 2 + E6q) * (E4q ^ 2)⁻¹) = x := by
  qexp_coeffs

-- `E4^3 / Delta` has pole order 1, so the power series tested here is
-- `q * E4^3 / Delta = E4^3 / (Delta / q)`.
example : ∃ x : ℂ, PowerSeries.coeff 10 (E4q ^ 3 * Deltaoverq_qexpansion⁻¹) = x := by
  qexp_coeffs

-- `E4^2 * E6 / Delta` also has pole order 1.
example : ∃ x : ℂ, PowerSeries.coeff 10 (E4q ^ 2 * E6q * Deltaoverq_qexpansion⁻¹) = x := by
  qexp_coeffs

-- `1 / Delta^2` has pole order 2, so multiplying by `q^2` gives `(Delta / q)⁻²`.
example :
    ∃ x : ℂ, PowerSeries.coeff 10 (Deltaoverq_qexpansion⁻¹ * Deltaoverq_qexpansion⁻¹) = x := by
  qexp_coeffs

example : ∃ x : ℂ, PowerSeries.coeff 5 (DeltaShift2_qexpansion * E6q⁻¹) = x := by
  qexp_coeffs

example : ∃ x, qj_qexpansion.coeff 20 = x := by
  qexp_coeffs
