/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.qExpansion_tactic.link

/-!
# Initial q-expansion coefficients of the discriminant and the j-function

This file computes initial coefficients of the discriminant and the normalized `j`-function,
then records the corresponding Laurent q-expansion coefficients of `j`.

## Main results

* `ramanujanTau_one`, `ramanujanTau_two`, `ramanujanTau_three`: the first Ramanujan tau values.
* `Delta_qExpansion_coeff_two`: the start of the discriminant q-expansion coefficient API.
* `qjCoeffs_one`: the start of the integral regularized-`j` coefficient API.
* `exists_int_coeff_j_eq_principal_part_add_tsum_with_initial`: an explicit convergent expansion.
* `j_laurentQExpansion_coeff_neg_one`: the start of the Laurent q-expansion coefficient API.
-/

open Complex ModularForm ModularFormClass UpperHalfPlane Real IntegralPowerSeries
open XYin.PhD.qExpansion_tactic
open scoped Manifold

noncomputable section

/-- The first Ramanujan tau value: `τ(1) = 1`. -/
lemma ramanujanTau_one : ramanujanTau 1 = 1 := by
  rw [ramanujanTau_link, Delta_qexpansion_coeff_eq]
  rfl

/-- The second Ramanujan tau value: `τ(2) = -24`. -/
lemma ramanujanTau_two : ramanujanTau 2 = -24 := by
  rw [ramanujanTau_link, Delta_qexpansion_coeff_eq]
  rfl

/-- The third Ramanujan tau value: `τ(3) = 252`. -/
lemma ramanujanTau_three : ramanujanTau 3 = 252 := by
  rw [ramanujanTau_link, Delta_qexpansion_coeff_eq]
  rfl

/-- The integer coefficients `qjCoeffs` of the regularized `j`-function agree with the
tactic-computed integer power series `qj_qexpansion`, coefficientwise. -/
private lemma qjCoeffs_eq_qjQExpansion_coeff_aux (n : ℕ) :
    qjCoeffs n = qj_qexpansion.coeff n := by
  have h : ((qjCoeffs n : ℤ) : ℂ) = (qExpansion 1 qj).coeff n := by
    simpa [qjCoeffs] using
      congrArg (PowerSeries.coeff n) (coeTo_of_toIntegralPowerSeries qj_isIntegralPowerSeries)
  exact_mod_cast h.trans (qj_qxp_coeff_link n)

/-- The regularized `j`-function `qj` has constant coefficient `1`: at the cusp, `j` has a
simple pole with leading coefficient `1`. -/
lemma qjCoeffs_zero : qjCoeffs 0 = 1 := by
  rw [qjCoeffs_eq_qjQExpansion_coeff_aux, qj_qexpansion_coeff_eq]
  rfl

/-- The `q²`-coefficient of the q-expansion of `Δ` is `τ(2) = -24`. -/
lemma Delta_qExpansion_coeff_two : (qExpansion 1 Delta).coeff 2 = -24 := by
  rw [Delta_qxp_coeff_link, Delta_qexpansion_coeff_eq]
  exact_mod_cast (rfl : deltaCoeffInt 2 = -24)

/-- The `q³`-coefficient of the q-expansion of `Δ` is `τ(3) = 252`. -/
lemma Delta_qExpansion_coeff_three : (qExpansion 1 Delta).coeff 3 = 252 := by
  rw [Delta_qxp_coeff_link, Delta_qexpansion_coeff_eq]
  exact_mod_cast (rfl : deltaCoeffInt 3 = 252)

/-- The `q⁴`-coefficient of the q-expansion of `Δ` is `τ(4) = -1472`. -/
lemma Delta_qExpansion_coeff_four : (qExpansion 1 Delta).coeff 4 = -1472 := by
  rw [Delta_qxp_coeff_link, Delta_qexpansion_coeff_eq]
  exact_mod_cast (rfl : deltaCoeffInt 4 = -1472)

/-- The `q⁵`-coefficient of the q-expansion of `Δ` is `τ(5) = 4830`. -/
lemma Delta_qExpansion_coeff_five : (qExpansion 1 Delta).coeff 5 = 4830 := by
  rw [Delta_qxp_coeff_link, Delta_qexpansion_coeff_eq]
  exact_mod_cast (rfl : deltaCoeffInt 5 = 4830)

private lemma qj_qExpansion_coeff_one_aux : (qExpansion 1 qj).coeff 1 = 744 := by
  rw [qj_qxp_coeff_link, qj_qexpansion_coeff_eq]
  exact_mod_cast (rfl : qjCoeffInt 1 = 744)

/-- The first regular coefficient of `j` is its celebrated constant term `744`. -/
lemma qjCoeffs_one : qjCoeffs 1 = 744 := by
  rw [qjCoeffs_eq_qjQExpansion_coeff_aux, qj_qexpansion_coeff_eq]
  rfl

private lemma qj_qExpansion_coeff_two_aux : (qExpansion 1 qj).coeff 2 = 196884 := by
  rw [qj_qxp_coeff_link, qj_qexpansion_coeff_eq]
  exact_mod_cast (rfl : qjCoeffInt 2 = 196884)

/-- The second regular coefficient of `j` is `196884`, the first Monstrous-Moonshine
coefficient `c(1)`. -/
lemma qjCoeffs_two : qjCoeffs 2 = 196884 := by
  rw [qjCoeffs_eq_qjQExpansion_coeff_aux, qj_qexpansion_coeff_eq]
  rfl

private lemma qj_qExpansion_coeff_three_aux : (qExpansion 1 qj).coeff 3 = 21493760 := by
  rw [qj_qxp_coeff_link, qj_qexpansion_coeff_eq]
  exact_mod_cast (rfl : qjCoeffInt 3 = 21493760)

/-- The third regular coefficient of `j` is `c(2) = 21493760`. -/
lemma qjCoeffs_three : qjCoeffs 3 = 21493760 := by
  rw [qjCoeffs_eq_qjQExpansion_coeff_aux, qj_qexpansion_coeff_eq]
  rfl

private lemma qj_qExpansion_coeff_four_aux : (qExpansion 1 qj).coeff 4 = 864299970 := by
  rw [qj_qxp_coeff_link, qj_qexpansion_coeff_eq]
  exact_mod_cast (rfl : qjCoeffInt 4 = 864299970)

/-- The fourth regular coefficient of `j` is `c(3) = 864299970`. -/
lemma qjCoeffs_four : qjCoeffs 4 = 864299970 := by
  rw [qjCoeffs_eq_qjQExpansion_coeff_aux, qj_qexpansion_coeff_eq]
  rfl

/--
The first four regular coefficients in the convergent q-series reconstruction of `j` are
`744`, `196884`, `21493760`, and `864299970`.
-/
theorem exists_int_coeff_j_eq_principal_part_add_tsum_with_initial :
    ∃ c : ℕ → ℤ,
      c 0 = 744 ∧ c 1 = 196884 ∧ c 2 = 21493760 ∧ c 3 = 864299970 ∧
        ∀ z : ℍ, j z = 1 / cexp (2 * π * Complex.I * z) +
          ∑' n, c n * cexp (2 * π * Complex.I * z) ^ n := by
  let c : ℕ → ℤ := fun n ↦ qjCoeffs (n + 1)
  refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [c] using qjCoeffs_one
  · simpa [c] using qjCoeffs_two
  · simpa [c] using qjCoeffs_three
  · simpa [c] using qjCoeffs_four
  · intro z
    have h := j_eq_qjCoeffs_tsum z
    rw [qjCoeffs_zero] at h
    simpa [c] using h

/-- The Laurent q-expansion coefficients of `j` at index `n - 1` are the power-series
coefficients of `qj` at index `n`: the index shift by the pole order `1` of `j` at infinity. -/
private lemma j_laurentQExpansion_coeff_eq_qj_coeff_aux (n : ℕ) :
    (laurentqExpansion 1 j).coeff ((n : ℤ) - 1) = (qExpansion 1 qj).coeff n := by
  rw [← j_to_qExpansion]
  simpa [j_poleOrder] using laurentqExpansion.coeff_neg_poleOrder_add (h := 1) (f := j) n

/-- The principal part of `j` at the cusp is exactly `q⁻¹`. -/
theorem j_laurentQExpansion_coeff_neg_one : (laurentqExpansion 1 j).coeff (-1) = 1 := by
  simpa using (j_laurentQExpansion_coeff_eq_qj_coeff_aux 0).trans qj_qExpansion_coeff_zero

/-- The constant Laurent coefficient of `j` is `744`. -/
theorem j_laurentQExpansion_coeff_zero : (laurentqExpansion 1 j).coeff 0 = 744 := by
  simpa using (j_laurentQExpansion_coeff_eq_qj_coeff_aux 1).trans qj_qExpansion_coeff_one_aux

/-- The `q`-coefficient of `j` is `196884`, the first Monstrous-Moonshine coefficient. -/
theorem j_laurentQExpansion_coeff_one : (laurentqExpansion 1 j).coeff 1 = 196884 := by
  simpa using (j_laurentQExpansion_coeff_eq_qj_coeff_aux 2).trans qj_qExpansion_coeff_two_aux

/-- The `q²`-coefficient of `j` is `21493760`. -/
theorem j_laurentQExpansion_coeff_two : (laurentqExpansion 1 j).coeff 2 = 21493760 := by
  simpa using (j_laurentQExpansion_coeff_eq_qj_coeff_aux 3).trans qj_qExpansion_coeff_three_aux

/-- The `q³`-coefficient of `j` is `864299970`. -/
theorem j_laurentQExpansion_coeff_three : (laurentqExpansion 1 j).coeff 3 = 864299970 := by
  simpa using (j_laurentQExpansion_coeff_eq_qj_coeff_aux 4).trans qj_qExpansion_coeff_four_aux

end
