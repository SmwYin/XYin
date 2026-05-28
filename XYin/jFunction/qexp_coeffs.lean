import XYin.qExpansion_tactic.link

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups PowerSeries
  SlashInvariantFormClass Real Function IntegralPowerSeries
open XYin.qExpansion_tactic
open scoped Manifold

noncomputable section

private lemma qj_coeffs_eq_qj_qexpansion_coeff (n : ℕ) :
    qj_coeffs n = qj_qexpansion.coeff n := by
  have h1 : ((qj_coeffs n : ℤ) : ℂ) = (qExpansion 1 qj).coeff n := by
    simpa [qj_coeffs] using
      congrArg (PowerSeries.coeff n) (coeTo_of_toIntegralPowerSeries qjIsIntegralPowerSeries)
  have h2 : (qExpansion 1 qj).coeff n = (qj_qexpansion.coeff n : ℂ) :=
    qj_qxp_coeff_link n
  exact_mod_cast h1.trans h2

lemma qj_exp_zero : (qExpansion 1 qj).coeff 0 = 1 := by
  rw [qj_qxp_coeff_link]
  exact_mod_cast (qexp_coeff qj 0 1)

lemma qj_exp_zero' : qj_coeffs 0 = 1 := by
  rw [qj_coeffs_eq_qj_qexpansion_coeff]
  exact qexp_coeff qj 0 1

lemma Delta_exp_two : (qExpansion 1 Delta).coeff 2 = -24 := by
  rw [Delta_qxp_coeff_link]
  exact_mod_cast (qexp_coeff Delta 2 (-24))

lemma Delta_exp_three : (qExpansion 1 Delta).coeff 3 = 252 := by
  rw [Delta_qxp_coeff_link]
  exact_mod_cast (qexp_coeff Delta 3 252)

lemma Delta_exp_four : (qExpansion 1 Delta).coeff 4 = -1472 := by
  rw [Delta_qxp_coeff_link]
  exact_mod_cast (qexp_coeff Delta 4 (-1472))

lemma Delta_exp_five : (qExpansion 1 Delta).coeff 5 = 4830 := by
  rw [Delta_qxp_coeff_link]
  exact_mod_cast (qexp_coeff Delta 5 4830)

lemma qj_exp_one : (qExpansion 1 qj).coeff 1 = 744 := by
  rw [qj_qxp_coeff_link]
  exact_mod_cast (qexp_coeff qj 1 744)

lemma qj_exp_one' : qj_coeffs 1 = 744 := by
  rw [qj_coeffs_eq_qj_qexpansion_coeff]
  exact qexp_coeff qj 1 744

lemma qj_exp_two : (qExpansion 1 qj).coeff 2 = 196884 := by
  rw [qj_qxp_coeff_link]
  exact_mod_cast (qexp_coeff qj 2 196884)

lemma qj_exp_two' : qj_coeffs 2 = 196884 := by
  rw [qj_coeffs_eq_qj_qexpansion_coeff]
  exact qexp_coeff qj 2 196884

lemma qj_exp_three : (qExpansion 1 qj).coeff 3 = 21493760 := by
  rw [qj_qxp_coeff_link]
  exact_mod_cast (qexp_coeff qj 3 21493760)

lemma qj_exp_three' : qj_coeffs 3 = 21493760 := by
  rw [qj_coeffs_eq_qj_qexpansion_coeff]
  exact qexp_coeff qj 3 21493760

lemma qj_exp_four : (qExpansion 1 qj).coeff 4 = 864299970 := by
  rw [qj_qxp_coeff_link]
  exact_mod_cast (qexp_coeff qj 4 864299970)

lemma qj_exp_four' : qj_coeffs 4 = 864299970 := by
  rw [qj_coeffs_eq_qj_qexpansion_coeff]
  exact qexp_coeff qj 4 864299970

lemma j_exp : ∀ z : ℍ, j z = (qj_coeffs 0 / cexp (2 * π * Complex.I * z))
    + ∑' n, (qj_coeffs (n + 1)) * cexp (2 * π * Complex.I * z) ^ n := by
  intro z
  rw [← cancelout1, ← cancelout2]
  exact qj_exp_dvd z

lemma j_exp' : ∃ (c : ℕ → ℤ), ∀ z : ℍ, j z = (c 0 / cexp (2 * π * Complex.I * z))
    + ∑' n, (c (n + 1)) * cexp (2 * π * Complex.I * z) ^ n := by
  refine ⟨qj_coeffs, ?_⟩
  exact j_exp

lemma j_exp_to_minusone : ∃ (c : ℕ → ℤ), ∀ z : ℍ, j z =
    (1 / cexp (2 * π * Complex.I * z)) + ∑' n, (c n) * cexp (2 * π * Complex.I * z) ^ n := by
  let c : ℕ → ℤ := fun n ↦ qj_coeffs (n + 1)
  use c
  intro z
  have h := j_exp z
  rw [qj_exp_zero'] at h
  exact_mod_cast h

lemma j_exp_to_three : ∃ (c : ℕ → ℤ),
    c 0 = 744 ∧ c 1 = 196884 ∧ c 2 = 21493760 ∧ c 3 = 864299970
      ∧ ∀ z : ℍ, j z =
        (1 / cexp (2 * π * Complex.I * z))
          + ∑' n, (c n) * cexp (2 * π * Complex.I * z) ^ n := by
  let c : ℕ → ℤ := fun n ↦ qj_coeffs (n + 1)
  refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [c] using qj_exp_one'
  · simpa [c] using qj_exp_two'
  · simpa [c] using qj_exp_three'
  · simpa [c] using qj_exp_four'
  · intro z
    have h := j_exp z
    rw [qj_exp_zero'] at h
    simpa [c] using h

theorem jLaurentqExpansion_minusone : (laurentqExpansion 1 j).coeff (-1) = 1 := by
  calc
    (laurentqExpansion 1 j).coeff (-1) = (to_qExpansion 1 j).coeff 0 := by
      simpa [j_poleOrder] using (laurentqExpansion.coeff_neg_poleOrder (h := 1) (f := j))
    _ = (qExpansion 1 qj).coeff 0 := by rw [j_to_qExpansion]
    _ = 1 := qj_exp_zero

theorem jLaurentqExpansion_zero : (laurentqExpansion 1 j).coeff 0 = 744 := by
  calc
    (laurentqExpansion 1 j).coeff 0 = (to_qExpansion 1 j).coeff 1 := by
      simpa [j_poleOrder] using (laurentqExpansion.coeff_neg_poleOrder_add (h := 1) (f := j) 1)
    _ = (qExpansion 1 qj).coeff 1 := by rw [j_to_qExpansion]
    _ = 744 := qj_exp_one

theorem jLaurentqExpansion_one : (laurentqExpansion 1 j).coeff 1 = 196884 := by
  calc
    (laurentqExpansion 1 j).coeff 1 = (to_qExpansion 1 j).coeff 2 := by
      simpa [j_poleOrder] using (laurentqExpansion.coeff_neg_poleOrder_add (h := 1) (f := j) 2)
    _ = (qExpansion 1 qj).coeff 2 := by rw [j_to_qExpansion]
    _ = 196884 := qj_exp_two

theorem jLaurentqExpansion_two : (laurentqExpansion 1 j).coeff 2 = 21493760 := by
  calc
    (laurentqExpansion 1 j).coeff 2 = (to_qExpansion 1 j).coeff 3 := by
      simpa [j_poleOrder] using (laurentqExpansion.coeff_neg_poleOrder_add (h := 1) (f := j) 3)
    _ = (qExpansion 1 qj).coeff 3 := by rw [j_to_qExpansion]
    _ = 21493760 := qj_exp_three

theorem jLaurentqExpansion_three : (laurentqExpansion 1 j).coeff 3 = 864299970 := by
  calc
    (laurentqExpansion 1 j).coeff 3 = (to_qExpansion 1 j).coeff 4 := by
      simpa [j_poleOrder] using (laurentqExpansion.coeff_neg_poleOrder_add (h := 1) (f := j) 4)
    _ = (qExpansion 1 qj).coeff 4 := by rw [j_to_qExpansion]
    _ = 864299970 := qj_exp_four

end
