/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.qExpansion_tactic.link

/-!
# Initial q-expansion coefficients of the discriminant and the j-function

This file computes initial coefficients of the discriminant and the normalized `j`-function,
then records the corresponding Laurent q-expansion coefficients of `j`. Each value is certified
once, on the integer side, by kernel evaluation (`rfl`) of the integer engine of
`QExpansionTactic`; the complex-valued statements are derived from it through the
cast lemmas `ramanujanTau_cast` and `qjCoeffs_cast`.

## Main results

* `ramanujanTau_one`, …, `ramanujanTau_five`: the first Ramanujan tau values.
* `discriminant_qExpansion_coeff_two`: the continuation (after mathlib's
  `ModularForm.discriminant_qExpansion_coeff_one`) of the discriminant q-expansion coefficient API.
* `qjCoeffs_one`: the continuation (after `qjCoeffs_zero`, proved analytically in
  `XYin.PhD.jFunction.jfunction`) of the integral regularized-`j` coefficient API.
* `exists_int_coeff_j_eq_principal_part_add_tsum_with_initial`: an explicit convergent expansion.
* `j_laurentQExpansion_coeff_neg_one`: the start of the Laurent q-expansion coefficient API.
-/

open Complex ModularForm ModularFormClass UpperHalfPlane Real IntegralPowerSeries
open QExpansionTactic
open scoped Manifold

noncomputable section

/-- The first Ramanujan tau value: `τ(1) = 1`. -/
lemma ramanujanTau_one : ramanujanTau 1 = 1 := by
  rw [ramanujanTau_link, deltaQExpansion_coeff_eq]
  rfl

/-- The second Ramanujan tau value: `τ(2) = -24`. -/
lemma ramanujanTau_two : ramanujanTau 2 = -24 := by
  rw [ramanujanTau_link, deltaQExpansion_coeff_eq]
  rfl

/-- The third Ramanujan tau value: `τ(3) = 252`. -/
lemma ramanujanTau_three : ramanujanTau 3 = 252 := by
  rw [ramanujanTau_link, deltaQExpansion_coeff_eq]
  rfl

/-- The fourth Ramanujan tau value: `τ(4) = -1472`. -/
lemma ramanujanTau_four : ramanujanTau 4 = -1472 := by
  rw [ramanujanTau_link, deltaQExpansion_coeff_eq]
  rfl

/-- The fifth Ramanujan tau value: `τ(5) = 4830`. -/
lemma ramanujanTau_five : ramanujanTau 5 = 4830 := by
  rw [ramanujanTau_link, deltaQExpansion_coeff_eq]
  rfl

/-- The `q²`-coefficient of the q-expansion of `Δ` is `τ(2) = -24`. -/
lemma discriminant_qExpansion_coeff_two : (qExpansion 1 discriminant).coeff 2 = -24 := by
  rw [← ramanujanTau_cast, ramanujanTau_two]
  norm_num

/-- The `q³`-coefficient of the q-expansion of `Δ` is `τ(3) = 252`. -/
lemma discriminant_qExpansion_coeff_three : (qExpansion 1 discriminant).coeff 3 = 252 := by
  rw [← ramanujanTau_cast, ramanujanTau_three]
  norm_num

/-- The `q⁴`-coefficient of the q-expansion of `Δ` is `τ(4) = -1472`. -/
lemma discriminant_qExpansion_coeff_four : (qExpansion 1 discriminant).coeff 4 = -1472 := by
  rw [← ramanujanTau_cast, ramanujanTau_four]
  norm_num

/-- The `q⁵`-coefficient of the q-expansion of `Δ` is `τ(5) = 4830`. -/
lemma discriminant_qExpansion_coeff_five : (qExpansion 1 discriminant).coeff 5 = 4830 := by
  rw [← ramanujanTau_cast, ramanujanTau_five]
  norm_num

/-- The first regular coefficient of `j` is its celebrated constant term `744`. -/
lemma qjCoeffs_one : qjCoeffs 1 = 744 := by
  rw [qjCoeffs_eq_qjCoeffInt]
  rfl

/-- The second regular coefficient of `j` is `196884`, the first Monstrous-Moonshine
coefficient `c(1)`. -/
lemma qjCoeffs_two : qjCoeffs 2 = 196884 := by
  rw [qjCoeffs_eq_qjCoeffInt]
  rfl

/-- The third regular coefficient of `j` is `c(2) = 21493760`. -/
lemma qjCoeffs_three : qjCoeffs 3 = 21493760 := by
  rw [qjCoeffs_eq_qjCoeffInt]
  rfl

/-- The fourth regular coefficient of `j` is `c(3) = 864299970`. -/
lemma qjCoeffs_four : qjCoeffs 4 = 864299970 := by
  rw [qjCoeffs_eq_qjCoeffInt]
  rfl

/--
The first four regular coefficients in the convergent q-series reconstruction of `j` are
`744`, `196884`, `21493760`, and `864299970`.
-/
theorem exists_int_coeff_j_eq_principal_part_add_tsum_with_initial :
    ∃ c : ℕ → ℤ,
      c 0 = 744 ∧ c 1 = 196884 ∧ c 2 = 21493760 ∧ c 3 = 864299970 ∧
        ∀ z : ℍ, j z = 1 / cexp (2 * π * Complex.I * z) +
          ∑' n, c n * cexp (2 * π * Complex.I * z) ^ n :=
  ⟨fun n ↦ qjCoeffs (n + 1), qjCoeffs_one, qjCoeffs_two, qjCoeffs_three, qjCoeffs_four,
    fun z ↦ by simpa [qjCoeffs_zero] using j_eq_qjCoeffs_tsum z⟩

/-- The principal part of `j` at the cusp is exactly `q⁻¹`. -/
theorem j_laurentQExpansion_coeff_neg_one : (laurentqExpansion 1 j).coeff (-1) = 1 := by
  simpa using (j_laurentQExpansion_coeff_sub_one 0).trans qj_qExpansion_coeff_zero

/-- The constant Laurent coefficient of `j` is `744`. -/
theorem j_laurentQExpansion_coeff_zero : (laurentqExpansion 1 j).coeff 0 = 744 := by
  simpa [← qjCoeffs_cast, qjCoeffs_one] using j_laurentQExpansion_coeff_sub_one 1

/-- The `q`-coefficient of `j` is `196884`, the first Monstrous-Moonshine coefficient. -/
theorem j_laurentQExpansion_coeff_one : (laurentqExpansion 1 j).coeff 1 = 196884 := by
  simpa [← qjCoeffs_cast, qjCoeffs_two] using j_laurentQExpansion_coeff_sub_one 2

/-- The `q²`-coefficient of `j` is `21493760`. -/
theorem j_laurentQExpansion_coeff_two : (laurentqExpansion 1 j).coeff 2 = 21493760 := by
  simpa [← qjCoeffs_cast, qjCoeffs_three] using j_laurentQExpansion_coeff_sub_one 3

/-- The `q³`-coefficient of `j` is `864299970`. -/
theorem j_laurentQExpansion_coeff_three : (laurentqExpansion 1 j).coeff 3 = 864299970 := by
  simpa [← qjCoeffs_cast, qjCoeffs_four] using j_laurentQExpansion_coeff_sub_one 4

end
