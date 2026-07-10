import Mathlib
import XYin.PhD.Test.jfunction

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups
  PowerSeries SlashInvariantFormClass Real Function IntegralPowerSeries
open scoped Manifold

local notation "𝕢" => Periodic.qParam
local notation "ℍₒ" => upperHalfPlaneSet

noncomputable section

lemma qj_cuspFunction_DifferentiableOn :
    DifferentiableOn ℂ (cuspFunction 1 qj) (Metric.ball 0 1) :=
  UpperHalfPlane.differentiableOn_cuspFunction_ball (h := 1) (f := qj) (by norm_num)
    qj_periodic qj_MDifferentiable qj_IsBoundedAtImInfty

lemma qj_cuspFunction_AnalyticAt : AnalyticAt ℂ (cuspFunction 1 qj) 0 :=
  DifferentiableOn.analyticAt
    (fun q hq => qj_cuspFunction_DifferentiableOn q hq)
    (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

lemma j_cuspFunction_Meromorphic : MeromorphicAt (cuspFunction 1 j) (0 : ℂ) := by
  have hqj_mer : MeromorphicAt (cuspFunction 1 qj) (0 : ℂ) :=
    qj_cuspFunction_AnalyticAt.meromorphicAt
  have hdiv : MeromorphicAt (fun q : ℂ => q⁻¹ * cuspFunction 1 qj q) (0 : ℂ) := by
    exact ((MeromorphicAt.id (0 : ℂ)).inv).mul hqj_mer
  refine hdiv.congr ?_
  simpa [qj, Periodic.qParam, pow_one, Pi.mul_apply] using
    (cuspFunction_eq_inv_mul_cuspFunction_mul_qParam_eventuallyEq
      (h := 1) (hh := by norm_num) (f := j)).symm

lemma j_cuspFunction_notAnalytic : ¬ AnalyticAt ℂ (cuspFunction 1 j) 0 := by
  have hqj0 : cuspFunction 1 qj 0 = 1 := by
    simpa [qExpansion_coeff] using qj_exp_zero
  intro hjan
  have hmul_tendsto :
      Tendsto (fun q : ℂ ↦ q * cuspFunction 1 j q)
        (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (0 : ℂ)) := by
    have hcont : ContinuousAt (fun q : ℂ ↦ q * cuspFunction 1 j q) (0 : ℂ) :=
      continuousAt_id.mul hjan.continuousAt
    simpa using hcont.continuousWithinAt.tendsto
  have hEq :
      (fun q : ℂ ↦ q * cuspFunction 1 j q) =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        cuspFunction 1 qj := by
    simpa [qj, Periodic.qParam, pow_one, Pi.mul_apply] using
      (cuspFunction_mul_qParam_eventuallyEq (h := 1) (hh := by norm_num) (f := j))
  have hqj_tendsto_zero :
      Tendsto (cuspFunction 1 qj) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (0 : ℂ)) :=
    hmul_tendsto.congr' hEq
  have hqj_tendsto_one :
      Tendsto (cuspFunction 1 qj) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (1 : ℂ)) := by
    simpa [hqj0] using qj_cuspFunction_AnalyticAt.continuousAt.continuousWithinAt.tendsto
  have : (1 : ℂ) = 0 := tendsto_nhds_unique hqj_tendsto_one hqj_tendsto_zero
  exact one_ne_zero this

lemma j_poleOrder : poleOrder 1 j = 1 := by
  let F : ℂ → ℂ := cuspFunction 1 qj
  have hqj0 : F 0 = 1 := by
    simpa [F, qExpansion_coeff] using qj_exp_zero
  have hEq :
      cuspFunction 1 j =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q : ℂ => q⁻¹ * F q := by
    simpa [F, qj, Periodic.qParam, pow_one, Pi.mul_apply] using
      (cuspFunction_eq_inv_mul_cuspFunction_mul_qParam_eventuallyEq
        (h := 1) (hh := by norm_num) (f := j))
  have hFan : AnalyticAt ℂ F 0 := by
    simpa [F] using qj_cuspFunction_AnalyticAt
  have hF0 : F 0 ≠ 0 := by simp [hqj0]
  exact poleOrder_eq_one_of_eventuallyEq_inv_mul_analyticAt (h := 1) (f := j) (F := F)
    hEq hFan hF0

lemma j_poleRemoved : poleRemoved 1 j = qj := by
  ext τ
  simp [UpperHalfPlane.poleRemoved, qj, j_poleOrder, Periodic.qParam, pow_one]

lemma j_to_qExpansion : to_qExpansion 1 j = qExpansion 1 qj := by
  simp [UpperHalfPlane.to_qExpansion, j_poleRemoved]

lemma jLaurentqExpansion_coeff_eq (n : ℤ) :
    (laurentqExpansion 1 j).coeff n =
      if n < -1 then 0 else (qExpansion 1 qj).coeff (Int.toNat (n + 1)) := by
  exact laurentqExpansion_coeff_eq_if_lt_neg_one_of_poleOrder_eq_one_and_to_qExpansion_eq
    (h := 1) (f := j) (g := qj) j_poleOrder j_to_qExpansion n

theorem jLaurentqExpansion_lt_minusone {n : ℤ} (hn : n < -1) :
    (laurentqExpansion 1 j).coeff n = 0 := by
  simp [jLaurentqExpansion_coeff_eq, hn]

theorem jLaurentqExpansion_isIntegral {n : ℤ} :
    ∃ m : ℤ, (laurentqExpansion 1 j).coeff n = m := by
  by_cases hn : n < -1
  · refine ⟨0, ?_⟩
    simp [jLaurentqExpansion_coeff_eq, hn]
  · refine ⟨qj_coeffs (Int.toNat (n + 1)), ?_⟩
    have hcoeff :
        (((qj_coeffs (Int.toNat (n + 1)) : ℤ) : ℂ)) =
          (qExpansion 1 qj).coeff (Int.toNat (n + 1)) := by
      simpa [qj_coeffs] using congrArg (PowerSeries.coeff (Int.toNat (n + 1)))
        (coeTo_of_toIntegralPowerSeries qjIsIntegralPowerSeries)
    simpa [jLaurentqExpansion_coeff_eq, hn] using hcoeff.symm

theorem jLaurentqExpansion_minusone : (laurentqExpansion 1 j).coeff (-1) = 1 := by
  simpa [jLaurentqExpansion_coeff_eq] using qj_exp_zero

theorem jLaurentqExpansion_zero : (laurentqExpansion 1 j).coeff 0 = 744 := by
  simpa [jLaurentqExpansion_coeff_eq] using qj_exp_one

theorem jLaurentqExpansion_one : (laurentqExpansion 1 j).coeff 1 = 196884 := by
  simpa [jLaurentqExpansion_coeff_eq] using qj_exp_two

theorem jLaurentqExpansion_two : (laurentqExpansion 1 j).coeff 2 = 21493760 := by
  simpa [jLaurentqExpansion_coeff_eq] using qj_exp_three

theorem jLaurentqExpansion_three : (laurentqExpansion 1 j).coeff 3 = 864299970 := by
  simpa [jLaurentqExpansion_coeff_eq] using qj_exp_four
