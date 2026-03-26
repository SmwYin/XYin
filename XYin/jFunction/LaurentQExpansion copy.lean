/-
import XYin.Modularforms.Eisenstein
import XYin.jFunction.HasIntegralQExpansion
import XYin.jFunction.generalised

open ModularForm Complex Function Matrix.SpecialLinearGroup Metric
  ModularFormClass SlashInvariantFormClass Real Set Filter LaurentSeries
  IntegralPowerSeries
open UpperHalfPlane hiding I

variable {h : ℝ} {f : ℍ → ℂ}

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam

noncomputable section

/-
/-- This proof is similar to the Mathlib version. -/
theorem eq_cuspFunction' (τ : ℍ) (hh : h ≠ 0) (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    cuspFunction h f (𝕢 h τ) = f τ := by
  simpa [cuspFunction] using (Periodic.eq_cuspFunction hh hfper τ)

/-- This proof is different from the Mathlib version. -/
theorem differentiableAt_comp_ofComplex'
    (hfhol : ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    {z : ℂ} (hz : 0 < im z) :
    DifferentiableAt ℂ (f ∘ ofComplex) z :=
  by simpa using hfhol z hz

/-- This proof is different from the Mathlib version. -/
theorem bounded_at_infty_comp_ofComplex' (hfbdd : IsBoundedAtImInfty f) :
    BoundedAtFilter I∞ (f ∘ ofComplex) :=
  hfbdd.comp_tendsto tendsto_comap_im_ofComplex

/-- This proof is similar to the Mathlib version. -/
theorem differentiableAt_cuspFunction' (hh : 0 < h)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hfhol : ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    (hfbdd : IsBoundedAtImInfty f) {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (cuspFunction h f) q := by
  rcases eq_or_ne q 0 with rfl | hq'
  · exact hfper.differentiableAt_cuspFunction_zero hh
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun z hz ↦ differentiableAt_comp_ofComplex' hfhol hz))
      (bounded_at_infty_comp_ofComplex' hfbdd)
  · exact Periodic.qParam_right_inv hh.ne' hq' ▸
      hfper.differentiableAt_cuspFunction hh.ne' <|
        hfhol _ (Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq')

/-- This proof is similar to the Mathlib version. -/
lemma differentiableOn_cuspFunction_ball' (hh : 0 < h)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hfhol : ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    (hfbdd : IsBoundedAtImInfty f) : DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1) :=
  fun _ hz ↦ (differentiableAt_cuspFunction' hh hfper hfhol hfbdd <| mem_ball_zero_iff.mp hz)
  |>.differentiableWithinAt
-/

/-- This proof is different from the Mathlib version. -/
lemma cuspFunction_apply_zero' (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0)
  (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) (hh : 0 < h) :
    cuspFunction h f 0 = valueAtInfty f := by
  refine (Tendsto.limUnder_eq ?_).symm
  have hq :
      Tendsto (fun τ : ℍ ↦ cuspFunction h f (𝕢 h τ)) atImInfty (nhds (cuspFunction h f 0)) :=
    hfanalytic.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)
  have hEq : (fun τ : ℍ ↦ cuspFunction h f (𝕢 h τ)) = f := by
    funext τ
    simpa using eq_cuspFunction' τ hh.ne' hfper
  simpa [hEq] using hq

lemma meromorphicAt_zero_to_diff
    {g : ℂ → ℂ} (hg : MeromorphicAt g (0 : ℂ)) :
    ∃ N : ℕ, ∃ R : ℝ, 0 < R ∧
      DifferentiableOn ℂ (fun q : ℂ => q ^ N * g q) (Metric.ball (0 : ℂ) R) := by
  rcases hg with ⟨N, hN⟩
  -- `MeromorphicAt` is defined using `•`; for `ℂ → ℂ` this is just multiplication.
  have hA : AnalyticAt ℂ (fun q : ℂ => q ^ N * g q) (0 : ℂ) := by
    simpa [smul_eq_mul] using hN
  rcases hA.exists_ball_analyticOnNhd with ⟨R, hRpos, hR⟩
  refine ⟨N, R, hRpos, ?_⟩
  -- `AnalyticOnNhd` ⇒ `AnalyticOn` ⇒ `DifferentiableOn`
  exact (hR.analyticOn.differentiableOn)

lemma cuspFunction_exists_pow_mul_diff
    (h : ℝ) (f : ℍ → ℂ) (hcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    ∃ N : ℕ, ∃ R : ℝ, 0 < R ∧
      DifferentiableOn ℂ (fun q : ℂ => q ^ N * cuspFunction h f q) (Metric.ball (0 : ℂ) R) := by
  simpa using (meromorphicAt_zero_to_diff (g := cuspFunction h f) hcusp)

lemma LaurentCoeff_pre
  (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    ∃ M : ℤ, M < 0 ∧ ∀ n : ℤ, n ≤ M →
    ∃ R : ℝ, 0 < R ∧ (2 * π * I)⁻¹ * ∮ z in C(0, R/2), cuspFunction h f z / z ^ (n + 1) = 0 := by
  rcases cuspFunction_exists_pow_mul_diff h f hfcusp with ⟨N, R0, hR0, hDiff⟩
  refine ⟨-((N : ℤ) + 1), ?_⟩
  constructor
  · linarith [Int.natCast_nonneg N]
  intro n hn
  refine ⟨R0, hR0, ?_⟩
  let k : ℕ := Int.toNat (-(n + (N : ℤ) + 1))
  let F : ℂ → ℂ := fun z => z ^ k * (z ^ N * cuspFunction h f z)
  have hk_nonneg : 0 ≤ -(n + (N : ℤ) + 1) := by linarith
  have hk : (k : ℤ) = -(n + (N : ℤ) + 1) := by
    simpa [k] using (Int.toNat_of_nonneg hk_nonneg)
  have hRhalf : 0 < R0 / 2 := by linarith
  have hDiffF_big : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) R0) := by
    intro z hz
    have hDiffAt : DifferentiableAt ℂ (fun q : ℂ => q ^ N * cuspFunction h f q) z :=
      (hDiff z hz).differentiableAt (isOpen_ball.mem_nhds hz)
    exact ((differentiableAt_id.pow k).mul hDiffAt).differentiableWithinAt
  have hDiffF : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) (R0 / 2)) :=
    hDiffF_big.mono <| Metric.ball_subset_ball (by linarith [hR0])
  have hContF_closed : ContinuousOn F (Metric.closedBall (0 : ℂ) (R0 / 2)) := by
    exact hDiffF_big.continuousOn.mono (Metric.closedBall_subset_ball (by linarith [hR0]))
  have hDiffAtF : ∀ z ∈ Metric.ball (0 : ℂ) (R0 / 2), DifferentiableAt ℂ F z := by
    intro z hz
    exact (hDiffF_big z (Metric.ball_subset_ball (by linarith [hR0]) hz)).differentiableAt
      (isOpen_ball.mem_nhds (Metric.ball_subset_ball (by linarith [hR0]) hz))
  have hIntF : ∮ z in C(0, R0 / 2), F z = 0 := by
    exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      (c := 0) (R := R0 / 2) hRhalf.le countable_empty hContF_closed
      (fun z hz => hDiffAtF z hz.1)
  have hEqOn : Set.EqOn
      (fun z : ℂ => cuspFunction h f z / z ^ (n + 1)) F (Metric.sphere (0 : ℂ) (R0 / 2)) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hz'
      have : ‖z‖ = 0 := by simp [hz', (norm_zero : ‖(0 : ℂ)‖ = 0)]
      have hz_norm : ‖z‖ = R0 / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      linarith
    have hk0 : (k : ℤ) + (N : ℤ) + (n + 1) = 0 := by
      linarith [hk]
    exact (div_eq_iff (zpow_ne_zero (n + 1) hz0)).2 <| by
      simp only [F]
      rw [← zpow_natCast, ← zpow_natCast]
      have haux :
          (z ^ (k : ℤ) * (z ^ (N : ℤ) * cuspFunction h f z)) * z ^ (n + 1)
            = cuspFunction h f z := by
        calc
          (z ^ (k : ℤ) * (z ^ (N : ℤ) * cuspFunction h f z)) * z ^ (n + 1)
              = (z ^ (k : ℤ) * z ^ (N : ℤ) * z ^ (n + 1)) * cuspFunction h f z := by
                  simp [mul_assoc, mul_left_comm, mul_comm]
          _ = (z ^ ((k : ℤ) + (N : ℤ)) * z ^ (n + 1)) * cuspFunction h f z := by
                have hKN : z ^ (k : ℤ) * z ^ (N : ℤ) = z ^ ((k : ℤ) + (N : ℤ)) := by
                  simpa using (zpow_add₀ hz0 (k : ℤ) (N : ℤ)).symm
                simpa [mul_assoc, mul_left_comm, mul_comm] using
                  congrArg (fun t : ℂ => t * z ^ (n + 1) * cuspFunction h f z) hKN
          _ = (z ^ ((k : ℤ) + (N : ℤ) + (n + 1))) * cuspFunction h f z := by
                have hKNN :
                    z ^ ((k : ℤ) + (N : ℤ)) * z ^ (n + 1) =
                      z ^ (((k : ℤ) + (N : ℤ)) + (n + 1)) := by
                  simpa using (zpow_add₀ hz0 (((k : ℤ) + (N : ℤ))) (n + 1)).symm
                simpa [mul_assoc] using
                  congrArg (fun t : ℂ => t * cuspFunction h f z) hKNN
          _ = cuspFunction h f z := by simp [hk0]
      exact haux.symm
  have hIntEq :
      ∮ z in C(0, R0 / 2), cuspFunction h f z / z ^ (n + 1) = ∮ z in C(0, R0 / 2), F z := by
    exact circleIntegral.integral_congr hRhalf.le hEqOn
  calc
    (2 * π * I)⁻¹ * ∮ z in C(0, R0 / 2), cuspFunction h f z / z ^ (n + 1)
        = (2 * π * I)⁻¹ * ∮ z in C(0, R0 / 2), F z := by simp [hIntEq]
    _ = 0 := by simp [hIntF]

noncomputable def laurentCoeffCutoff (h : ℝ) (f : ℍ → ℂ)
    (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) : ℤ :=
  Classical.choose (LaurentCoeff_pre hfcusp)

noncomputable def laurentCoeffRadius (h : ℝ) (f : ℍ → ℂ)
    (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) : ℝ :=
  let M : ℤ := laurentCoeffCutoff h f hfcusp
  let R0 : ℝ := Classical.choose ((Classical.choose_spec (LaurentCoeff_pre hfcusp)).2 M (le_rfl))
  min R0 1

lemma laurentCoeffRadius_pos (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    0 < laurentCoeffRadius h f hfcusp := by
  dsimp [laurentCoeffRadius]
  refine lt_min ?_ zero_lt_one
  exact
    (Classical.choose_spec
      ((Classical.choose_spec (LaurentCoeff_pre (h := h) (f := f) hfcusp)).2
        (laurentCoeffCutoff h f hfcusp) le_rfl)).1

lemma laurentCoeffRadius_le_one (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    laurentCoeffRadius h f hfcusp ≤ 1 := by
  simp [laurentCoeffRadius]

noncomputable def laurentCoeff (h : ℝ) (f : ℍ → ℂ)
    (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    (n : ℤ) : ℂ :=
  if n < laurentCoeffCutoff h f hfcusp then 0
  else (2 * π * I)⁻¹ * ∮ z in C(0, laurentCoeffRadius h f hfcusp / 2),
    cuspFunction h f z / z ^ (n + 1)

lemma LaurentCoeff_eq_zero_of_lt
    (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    {n : ℤ} (hn : n < laurentCoeffCutoff h f hfcusp) :
    laurentCoeff h f hfcusp n = 0 := by
  simp [laurentCoeff, hn]

lemma LaurentqExpansion_pre (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    (Function.support (fun n : ℤ => laurentCoeff h f hfcusp n)).IsPWO := by
  let M : ℤ := laurentCoeffCutoff h f hfcusp
  have hSub : Function.support (fun n : ℤ => laurentCoeff h f hfcusp n) ⊆ Set.Ici M := by
    intro n hn
    by_contra hle
    have hlt : n < M := lt_of_not_ge hle
    have hz : laurentCoeff h f hfcusp n = 0 :=
      LaurentCoeff_eq_zero_of_lt (h := h) (f := f) hfcusp hlt
    exact hn (by simpa [Function.mem_support] using hz)
  have hIci : (Set.Ici M : Set ℤ).IsPWO := by
    have hNat : (Set.univ : Set ℕ).IsPWO := Set.IsPWO.of_linearOrder _
    have hImg : (Set.image (fun n : ℕ => (M + n : ℤ)) Set.univ).IsPWO := by
      exact hNat.image_of_monotone <| by
        intro a b hab
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left (Int.ofNat_le.mpr hab) M
    have hImg' : (Set.range fun n : ℕ => (M + n : ℤ)).IsPWO := by
      simpa [Set.image_univ] using hImg
    have hEq : Set.range (fun n : ℕ => (M + n : ℤ)) = Set.Ici M := by
      ext z
      constructor
      · rintro ⟨n, rfl⟩
        exact le_add_of_nonneg_right (Int.natCast_nonneg n)
      · intro hz
        refine ⟨Int.toNat (z - M), ?_⟩
        have hz' : 0 ≤ z - M := sub_nonneg.mpr hz
        calc
          M + (Int.toNat (z - M) : ℤ) = M + (z - M) := by simp [Int.toNat_of_nonneg hz']
          _ = z := by ring
    simpa [hEq] using hImg'
  exact hIci.mono hSub

def LaurentqExpansion (h : ℝ) (f : ℍ → ℂ)
    (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    LaurentSeries ℂ :=
  HahnSeries.mk (fun n : ℤ => laurentCoeff h f hfcusp n) (LaurentqExpansion_pre hfcusp)

lemma hol_to_mer_at_cusp (hh : 0 < h)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hfhol : ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    (hfbdd : IsBoundedAtImInfty f) :
    MeromorphicAt (cuspFunction h f) (0 : ℂ) := by
  have hDiffOn : DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1) :=
    differentiableOn_cuspFunction_ball' hh hfper hfhol hfbdd
  have hAn0 : AnalyticAt ℂ (cuspFunction h f) 0 :=
    DifferentiableOn.analyticAt
      (fun q hq ↦ hDiffOn q hq)
      (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  exact hAn0.meromorphicAt

theorem Laurent_to_qExpansion'
    (hh : 0 < h)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hfhol : ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    (hfbdd : IsBoundedAtImInfty f) :
    LaurentqExpansion h f (hol_to_mer_at_cusp hh hfper hfhol hfbdd) = qExpansion h f := by
  let hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ) :=
    hol_to_mer_at_cusp (h := h) (f := f) hh hfper hfhol hfbdd
  let R : ℝ := laurentCoeffRadius h f hfcusp
  have hRpos : 0 < R := by
    simpa [R] using laurentCoeffRadius_pos (h := h) (f := f) hfcusp
  have hRle1 : R ≤ 1 := by
    simpa [R] using laurentCoeffRadius_le_one (h := h) (f := f) hfcusp
  have hRhalf_le : (0 : ℝ) ≤ R / 2 := by positivity
  have hRhalf_lt1 : R / 2 < 1 := by
    linarith
  have hcut_lt0 : laurentCoeffCutoff h f hfcusp < 0 :=
    (Classical.choose_spec (LaurentCoeff_pre (h := h) (f := f) hfcusp)).1
  have hDiffBall : DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1) :=
    differentiableOn_cuspFunction_ball' hh hfper hfhol hfbdd
  have hDiffClosed : DifferentiableOn ℂ (cuspFunction h f) (Metric.closedBall 0 (R / 2)) :=
    hDiffBall.mono (Metric.closedBall_subset_ball hRhalf_lt1)
  have hCoeffInt (m : ℕ) :
      (qExpansion h f).coeff m =
        ((2 * π * I)⁻¹ * ∮ z in C(0, R / 2), cuspFunction h f z / z ^ (m + 1)) := by
    have hci := hDiffClosed.circleIntegral_one_div_sub_center_pow_smul (half_pos hRpos) m
    calc
      (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0 := by
        simp [qExpansion]
      _ = (2 * π * I)⁻¹ *
            ((2 * π * I) / (↑m.factorial) * iteratedDeriv m (cuspFunction h f) 0) := by
            field_simp [two_pi_I_ne_zero]
      _ = (2 * π * I)⁻¹ *
            (∮ z in C(0, R / 2), (1 / (z - 0) ^ (m + 1)) • cuspFunction h f z) := by
            have hci' := congrArg (fun t : ℂ => (2 * π * I)⁻¹ * t) hci
            simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hci'.symm
      _ = ((2 * π * I)⁻¹ * ∮ z in C(0, R / 2), cuspFunction h f z / z ^ (m + 1)) := by
            simp [smul_eq_mul, sub_zero, div_eq_inv_mul, mul_assoc, mul_comm,
              mul_left_comm]
  ext n
  rcases lt_or_ge n 0 with hnneg | hnnonneg
  · have hqrhs :
        ((HahnSeries.ofPowerSeries ℤ ℂ) (qExpansion h f)).coeff n = 0 := by
      rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
      intro hmem
      simp only [Set.mem_range, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at hmem
      rcases hmem with ⟨m, hm⟩
      linarith [Int.natCast_nonneg m, hm]
    by_cases hcut : n < laurentCoeffCutoff h f hfcusp
    · simp [LaurentqExpansion, laurentCoeff, hcut, hqrhs]
    · let k : ℕ := Int.toNat (-(n + 1))
      let F : ℂ → ℂ := fun z => z ^ k * cuspFunction h f z
      have hk_nonneg : 0 ≤ -(n + 1) := by linarith
      have hk : (k : ℤ) = -(n + 1) := by
        simpa [k] using (Int.toNat_of_nonneg hk_nonneg)
      have hDiffF_big : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1) := by
        intro z hz
        have hDiffAt : DifferentiableAt ℂ (cuspFunction h f) z :=
          (hDiffBall z hz).differentiableAt (isOpen_ball.mem_nhds hz)
        exact ((differentiableAt_id.pow k).mul hDiffAt).differentiableWithinAt
      have hContF_closed : ContinuousOn F (Metric.closedBall (0 : ℂ) (R / 2)) := by
        exact hDiffF_big.continuousOn.mono (Metric.closedBall_subset_ball hRhalf_lt1)
      have hDiffAtF : ∀ z ∈ Metric.ball (0 : ℂ) (R / 2), DifferentiableAt ℂ F z := by
        intro z hz
        exact (hDiffF_big z (Metric.ball_subset_ball (le_of_lt hRhalf_lt1) hz)).differentiableAt
          (isOpen_ball.mem_nhds (Metric.ball_subset_ball (le_of_lt hRhalf_lt1) hz))
      have hIntF : ∮ z in C(0, R / 2), F z = 0 := by
        exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
          (c := 0) (R := R / 2) hRhalf_le countable_empty hContF_closed
          (fun z hz => hDiffAtF z hz.1)
      have hEqOn : Set.EqOn
          (fun z : ℂ => cuspFunction h f z / z ^ (n + 1)) F (Metric.sphere (0 : ℂ) (R / 2)) := by
        intro z hz
        have hz0 : z ≠ 0 := by
          intro hz'
          have hz_norm : ‖z‖ = R / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
          simp [hz'] at hz_norm
          linarith [hRpos]
        have hk0 : (k : ℤ) + (n + 1) = 0 := by linarith [hk]
        exact (div_eq_iff (zpow_ne_zero (n + 1) hz0)).2 <| by
          simp only [F]
          rw [← zpow_natCast]
          have haux :
              (z ^ (k : ℤ) * cuspFunction h f z) * z ^ (n + 1) = cuspFunction h f z := by
            calc
              (z ^ (k : ℤ) * cuspFunction h f z) * z ^ (n + 1)
                  = (z ^ (k : ℤ) * z ^ (n + 1)) * cuspFunction h f z := by
                      simp [mul_assoc, mul_comm]
              _ = (z ^ ((k : ℤ) + (n + 1))) * cuspFunction h f z := by
                    have hkz : z ^ (k : ℤ) * z ^ (n + 1) = z ^ ((k : ℤ) + (n + 1)) := by
                      simpa using (zpow_add₀ hz0 (k : ℤ) (n + 1)).symm
                    simpa [mul_assoc] using congrArg (fun t : ℂ => t * cuspFunction h f z) hkz
              _ = cuspFunction h f z := by simp [hk0]
          exact haux.symm
      have hIntEq :
          ∮ z in C(0, R / 2), cuspFunction h f z / z ^ (n + 1) = ∮ z in C(0, R / 2), F z := by
        exact circleIntegral.integral_congr hRhalf_le hEqOn
      have hIntZero : ∮ z in C(0, R / 2), cuspFunction h f z / z ^ (n + 1) = 0 := by
        calc
          ∮ z in C(0, R / 2), cuspFunction h f z / z ^ (n + 1)
              = ∮ z in C(0, R / 2), F z := hIntEq
          _ = 0 := hIntF
      simp [LaurentqExpansion, laurentCoeff, hcut, hqrhs, R, hIntZero]
  · have hcut_false : ¬ n < laurentCoeffCutoff h f hfcusp := by linarith
    let m : ℕ := Int.toNat n
    have hm : (m : ℤ) = n := by simpa [m] using (Int.toNat_of_nonneg hnnonneg).symm
    have hcut_false_m : ¬ (m : ℤ) < laurentCoeffCutoff h f hfcusp := by
      simpa [hm] using hcut_false
    rw [← hm]
    have hpow :
        ((HahnSeries.ofPowerSeries ℤ ℂ) (qExpansion h f)).coeff (m : ℤ) = (qExpansion h f).coeff m
        := by rw [HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (R := ℂ) (qExpansion h f) m]
    calc
      ((LaurentqExpansion h f hfcusp).coeff (m : ℤ))
          = (2 * π * I)⁻¹ * ∮ z in C(0, R / 2), cuspFunction h f z / z ^ (m + 1 : ℤ) := by
            simp [LaurentqExpansion, laurentCoeff, hcut_false_m, R]
      _ = (qExpansion h f).coeff m := by
            simpa [zpow_natCast] using (hCoeffInt m).symm
      _ = ((HahnSeries.ofPowerSeries ℤ ℂ) (qExpansion h f)).coeff (m : ℤ) := hpow.symm

lemma BB (hh : 0 < h) (n : ℤ) (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    MeromorphicAt (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ)) (0 : ℂ) := by
  have hmul : MeromorphicAt (fun q : ℂ ↦ q ^ n * cuspFunction h f q) (0 : ℂ) := by
    exact ((MeromorphicAt.id (0 : ℂ)).zpow n).mul hfcusp
  refine hmul.congr ?_
  have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
    simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds hnorm0
  filter_upwards [self_mem_nhdsWithin, hnorm] with q hq0 hqnorm
  have hq0' : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq0
  have him : 0 < Complex.im (Periodic.invQParam h q) :=
    Periodic.im_invQParam_pos_of_norm_lt_one hh hqnorm hq0'
  have hleft :
      cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ) q =
        (fun τ : ℍ ↦ (𝕢 h τ) ^ n * f τ) (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) := by
    simpa [cuspFunction] using
      (Periodic.cuspFunction_eq_of_nonzero h
        ((fun τ : ℍ ↦ (𝕢 h τ) ^ n * f τ) ∘ UpperHalfPlane.ofComplex) hq0')
  have hright :
      cuspFunction h f q = f (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) := by
    simpa [cuspFunction] using
      (Periodic.cuspFunction_eq_of_nonzero h (f ∘ UpperHalfPlane.ofComplex) hq0')
  have hqparam : 𝕢 h (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) = q := by
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos him] using
      (Periodic.qParam_right_inv hh.ne' hq0')
  calc
    q ^ n * cuspFunction h f q
        = q ^ n * f (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) := by simp [hright]
    _ = (𝕢 h (UpperHalfPlane.ofComplex (Periodic.invQParam h q))) ^ n *
          f (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) := by simp [hqparam]
    _ = cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ) q := by simp [hleft]

lemma A1 {n : ℤ} (hh : 0 < h)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) : Periodic ((fun (τ : ℍ) ↦
    (𝕢 h τ) ^ n * f τ) ∘ UpperHalfPlane.ofComplex) h := by
  have hqper : Periodic (fun z : ℂ ↦ 𝕢 h (UpperHalfPlane.ofComplex z)) h := by
    intro z
    by_cases hz : 0 < Complex.im z
    · have hz' : 0 < Complex.im (z + h) := by simp [Complex.add_im, hz]
      change 𝕢 h (UpperHalfPlane.ofComplex (z + h)) = 𝕢 h (UpperHalfPlane.ofComplex z)
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz,
        Periodic.qParam, Periodic.qParam]
      calc
        Complex.exp (2 * π * I * (z + h) / h)
            = Complex.exp (2 * π * I * z / h + 2 * π * I) := by
                field_simp [hh.ne']
        _ = Complex.exp (2 * π * I * z / h) * Complex.exp (2 * π * I) := by
              rw [Complex.exp_add]
        _ = Complex.exp (2 * π * I * z / h) := by
              simp [Complex.exp_two_pi_mul_I]
    · have hz' : ¬ 0 < Complex.im (z + h) := by simpa [Complex.add_im] using hz
      simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz),
        UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz')]
  have hqpow : Periodic (fun z : ℂ ↦ (𝕢 h (UpperHalfPlane.ofComplex z)) ^ n) h := by
    simpa [Function.comp] using hqper.comp (fun w : ℂ ↦ w ^ n)
  simpa [Function.comp] using hqpow.mul hfper

lemma A2 {n : ℤ} (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    (hfhol : ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z) :
    ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ ((fun (τ : ℍ) ↦
    (𝕢 h τ) ^ n * f τ) ∘ UpperHalfPlane.ofComplex) z := by
  intro z hz
  have _ := hfcusp
  have hpos : {w : ℂ | 0 < Complex.im w} ∈ nhds z :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
  have hqevent :
      (fun w : ℂ ↦ 𝕢 h (UpperHalfPlane.ofComplex w)) =ᶠ[nhds z] Function.Periodic.qParam h := by
    filter_upwards [hpos] with w hw
    simp [Function.Periodic.qParam, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have hqdiff : DifferentiableAt ℂ (fun w : ℂ ↦ 𝕢 h (UpperHalfPlane.ofComplex w)) z :=
    (Function.Periodic.differentiable_qParam (h := h) z).congr_of_eventuallyEq hqevent
  have hqne : 𝕢 h (UpperHalfPlane.ofComplex z) ≠ 0 := by
    simp [Function.Periodic.qParam]
  have hqpow : DifferentiableAt ℂ (fun w : ℂ ↦ (𝕢 h (UpperHalfPlane.ofComplex w)) ^ n) z :=
    hqdiff.zpow (Or.inl hqne)
  simpa [Function.comp] using hqpow.mul (hfhol z hz)

lemma meromorphicAt_align_LaurentqExpansion_order
    (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    ∃ N : ℕ,
      AnalyticAt ℂ (fun q : ℂ => q ^ N * cuspFunction h f q) 0 ∧
      (-(LaurentqExpansion h f hfcusp).order : ℤ) ≤ N := by
  sorry

lemma preA3 (hh : 0 < h) (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    AnalyticAt ℂ (fun q : ℂ ↦ q ^ (-(LaurentqExpansion h f hfcusp).order) * cuspFunction h f q) 0 := by
  sorry

lemma A3 (hh : 0 < h) (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hhol : AnalyticAt ℂ
      (fun q : ℂ ↦ q ^ (-(LaurentqExpansion h f hfcusp).order) * cuspFunction h f q) 0) :
    IsBoundedAtImInfty (fun (τ : ℍ) ↦ (𝕢 h τ) ^ (-(LaurentqExpansion h f hfcusp).order) * f τ) := by
  let k : ℤ := -(LaurentqExpansion h f hfcusp).order
  let gq : ℂ → ℂ := fun q : ℂ ↦ q ^ k * cuspFunction h f q
  let gτ : ℍ → ℂ := fun τ : ℍ ↦ (𝕢 h τ) ^ k * f τ
  have hbd_q : BoundedAtFilter (nhds (0 : ℂ)) gq :=
    hhol.continuousAt.tendsto.isBigO_one ℝ
  have hbd_τ :
      BoundedAtFilter atImInfty (fun τ : ℍ ↦ gq (𝕢 h τ)) :=
    hbd_q.comp_tendsto (qParam_tendsto_atImInfty hh)
  have hEq : (fun τ : ℍ ↦ gq (𝕢 h τ)) = gτ := by
    funext τ
    simp [gq, gτ, eq_cuspFunction' (h := h) (f := f) τ hh.ne' hfper]
  have hbd_τ' : BoundedAtFilter atImInfty gτ := by simpa [hEq] using hbd_τ
  simpa [IsBoundedAtImInfty, gτ, k] using hbd_τ'

theorem CC (hh : 0 < h) (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    (LaurentqExpansion h f hfcusp).powerSeriesPart
    = qExpansion h (fun τ ↦ (𝕢 h τ) ^ (-(LaurentqExpansion h f hfcusp).order) * f τ) := by
  sorry

theorem Laurent_to_qExpansion (hh : 0 < h) (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    LaurentqExpansion h (fun τ ↦ (𝕢 h τ) ^ (LaurentqExpansion h f hfcusp).order * f τ)
    (BB hh (LaurentqExpansion h f hfcusp).order hfcusp)
    = qExpansion h (fun τ ↦ (𝕢 h τ) ^ (-(LaurentqExpansion h f hfcusp).order) * f τ) := by
  sorry
/-
Maybe want: given a q-expansion as a formal Laurent series, can be converted to a
formal power series via `.powerSeriesPart`, use results on the latter, and then be converted
back to a formal Laurent series.
-/

theorem AB (hh : 0 < h) (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    LaurentqExpansion h f hfcusp =
    HahnSeries.single ((LaurentqExpansion h f hfcusp).order) (1 : ℂ)
    * qExpansion h ((fun τ ↦ (𝕢 h τ) ^ (-(LaurentqExpansion h f hfcusp).order) * f τ)) := by
  simpa [CC (h := h) (f := f) hh hfcusp] using
    (LaurentSeries.single_order_mul_powerSeriesPart (x := LaurentqExpansion h f hfcusp)).symm

theorem AA (hfcusp : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (n : ℕ)
    (h1 : IsIntegralPowerSeries (qExpansion h ((fun τ ↦ (𝕢 h τ) ^ n * f τ))))
    (h2 : (qExpansion h (fun (τ : ℍ) ↦ (𝕢 h τ) ^ n * f τ)).coeff 0 ≠ 0) :
    LaurentqExpansion h f hfcusp =
    (HahnSeries.single (-(n : ℤ)) (1 : ℂ)) *
      ((qExpansion h (fun (τ : ℍ) ↦ (𝕢 h τ) ^ n * f τ)) : LaurentSeries ℂ) := by
  sorry

#min_imports
-/
