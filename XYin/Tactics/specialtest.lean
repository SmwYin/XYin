import XYin.Tactics.ps_compute

open PowerSeries
open scoped ArithmeticFunction.sigma

def E4q : PowerSeries ℂ := PowerSeries.mk (Function.update (fun m => (240 : ℂ) * σ 3 m) 0 1)
def E6q : PowerSeries ℂ := PowerSeries.mk (Function.update (fun m => -(504 : ℂ) * σ 5 m) 0 1)
-- def Deltaq : PowerSeries ℂ := (1 / 1728 : ℂ) • (E4q ^ 3 - E6q ^ 2)


noncomputable abbrev Delta_qexpansion := (1 / 1728 : ℂ) • (E4q ^ 3 - E6q ^ 2)
noncomputable abbrev Deltaoverq_qexpansion :=
  PowerSeries.mk (fun m => Delta_qexpansion.coeff (m + 1))
noncomputable abbrev qoverDelta_qexpansion := Deltaoverq_qexpansion⁻¹

noncomputable abbrev qj_qexpansion := E4q ^ 3 * Deltaoverq_qexpansion⁻¹

example {y : ℂ} (h : PowerSeries.coeff 5 (E4q ^ 3 - E6q ^ 2) = y) :
    PowerSeries.coeff 5 ((1 / 1728 : ℂ) • (E4q ^ 3 - E6q ^ 2)) = (1 / 1728 : ℂ) * y := by
  simp only [PowerSeries.coeff_smul, h, smul_eq_mul]

set_option maxHeartbeats 1000000 in
example : ∃ x, Delta_qexpansion.coeff 0 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Delta_qexpansion.coeff 1 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Delta_qexpansion.coeff 2 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Delta_qexpansion.coeff 3 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Delta_qexpansion.coeff 4 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Delta_qexpansion.coeff 5 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Delta_qexpansion.coeff 6 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Deltaoverq_qexpansion.coeff 0 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Deltaoverq_qexpansion.coeff 1 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Deltaoverq_qexpansion.coeff 2 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Deltaoverq_qexpansion.coeff 3 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Deltaoverq_qexpansion.coeff 4 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Deltaoverq_qexpansion.coeff 5 = x := by
  ps_compute

set_option maxHeartbeats 1000000 in
example : ∃ x, Deltaoverq_qexpansion.coeff 6 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qoverDelta_qexpansion.coeff 0 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qoverDelta_qexpansion.coeff 1 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qoverDelta_qexpansion.coeff 2 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qoverDelta_qexpansion.coeff 3 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qoverDelta_qexpansion.coeff 4 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qoverDelta_qexpansion.coeff 5 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qoverDelta_qexpansion.coeff 6 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qj_qexpansion.coeff 0 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qj_qexpansion.coeff 1 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qj_qexpansion.coeff 2 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qj_qexpansion.coeff 3 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qj_qexpansion.coeff 4 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qj_qexpansion.coeff 5 = x := by
  ps_compute

set_option maxHeartbeats 10000000 in
example : ∃ x, qj_qexpansion.coeff 6 = x := by
  ps_compute
