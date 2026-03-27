import XYin.Modularforms.Eisenstein
import XYin.ForMathlib.QExpansion
import XYin.jFunction.HasIntegralQExpansion
import XYin.jFunction.generalised

open ModularForm Complex Function Matrix.SpecialLinearGroup Metric
  ModularFormClass SlashInvariantFormClass Real Set Filter LaurentSeries
  IntegralPowerSeries
open UpperHalfPlane hiding I



local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam

noncomputable section

variable {h : ℝ}

lemma cuspFunction_nat_mul_eq_cuspFunction_pow
    {h : ℝ} {m : ℕ} {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) {q : ℂ} (hq : q ≠ 0) :
    cuspFunction ((m : ℝ) * h) f q = cuspFunction h f (q ^ m) := by
  have hqpow : q ^ m ≠ 0 := pow_ne_zero _ hq
  rw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero _ _ hq]
  rw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero _ _ hqpow]
  have hexp :
      Complex.exp (Complex.log (q ^ m)) = Complex.exp ((m : ℂ) * Complex.log q) := by
    rw [Complex.exp_log hqpow, Complex.exp_nat_mul, Complex.exp_log hq]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hinv :
      Periodic.invQParam h (q ^ m) =
        Periodic.invQParam ((m : ℝ) * h) q + n * h := by
    rw [Periodic.invQParam, Periodic.invQParam, hn]
    simp only [mul_add, mul_assoc]
    ring_nf
    field_simp [two_pi_I_ne_zero]
    push_cast
    ring
  simpa [Function.comp_def, hinv] using
    (hfper.int_mul n (Periodic.invQParam ((m : ℝ) * h) q)).symm

def UpperHalfPlane.poleOrder (h : ℝ) (f : ℍ → ℂ) : ℕ :=
  if meromorphicOrderAt (cuspFunction h f) 0 < 0 then
    Int.natAbs ((meromorphicOrderAt (cuspFunction h f) 0).untopD 0)
  else 0

lemma meromorphicOrderAt_cuspFunction_nat_mul
    {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    meromorphicOrderAt (cuspFunction ((m : ℝ) * h) f) (0 : ℂ) =
      meromorphicOrderAt (cuspFunction h f) (0 : ℂ) * m := by
  have hEq :
      cuspFunction ((m : ℝ) * h) f =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q =>
        cuspFunction h f (q ^ m) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact cuspFunction_nat_mul_eq_cuspFunction_pow hfper (Set.mem_compl_singleton_iff.mp hq)
  rw [meromorphicOrderAt_congr hEq]
  have hg_nc : ¬ EventuallyConst (fun q : ℂ => q ^ m) (nhds (0 : ℂ)) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top]
    have hpow0 : (0 : ℂ) ^ m = 0 := by
      simp [hm]
    have horderPow : analyticOrderAt (fun q : ℂ => q ^ m) (0 : ℂ) = m := by
      change analyticOrderAt (id ^ m) (0 : ℂ) = m
      simpa [analyticOrderAt_id] using
        (analyticOrderAt_pow (𝕜 := ℂ) (f := id) (z₀ := (0 : ℂ)) analyticAt_id m)
    have horder :
        analyticOrderAt (fun q : ℂ => q ^ m - (fun q : ℂ => q ^ m) 0) (0 : ℂ) = m := by
      rw [show (fun q : ℂ => q ^ m - (fun q : ℂ => q ^ m) 0) = fun q : ℂ => q ^ m by
        funext q
        simp [hpow0]]
      exact horderPow
    simp [horder]
  have hpow0 : (0 : ℂ) ^ m = 0 := by simp [hm]
  have horderPow : analyticOrderAt (fun q : ℂ => q ^ m) (0 : ℂ) = m := by
    change analyticOrderAt (id ^ m) (0 : ℂ) = m
    simpa [analyticOrderAt_id] using
      (analyticOrderAt_pow (𝕜 := ℂ) (f := id) (z₀ := (0 : ℂ)) analyticAt_id m)
  have hmero0 : MeromorphicAt (cuspFunction h f) ((fun q : ℂ => q ^ m) 0) := by
    simpa [hpow0] using hmero
  have hcomp := hmero0.meromorphicOrderAt_comp (g := fun q : ℂ => q ^ m) (x := (0 : ℂ))
    (hg := analyticAt_id.pow m) hg_nc
  simpa [Function.comp, hpow0, horderPow] using hcomp

lemma poleOrder_nat_mul
    {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    poleOrder ((m : ℝ) * h) f = m * poleOrder h f := by
  unfold UpperHalfPlane.poleOrder
  cases ho : meromorphicOrderAt (cuspFunction h f) (0 : ℂ) with
  | top =>
      have hscale := meromorphicOrderAt_cuspFunction_nat_mul (h := h) (m := m) hm hmero hfper
      rw [ho] at hscale
      have hscale' : meromorphicOrderAt (cuspFunction ((m : ℝ) * h) f) (0 : ℂ) = ⊤ := by
        simpa [hm] using hscale
      simp [hscale']
  | coe k =>
      have hscale := meromorphicOrderAt_cuspFunction_nat_mul (h := h) (m := m) hm hmero hfper
      rw [ho] at hscale
      have hscale' :
          meromorphicOrderAt (cuspFunction ((m : ℝ) * h) f) (0 : ℂ) = (k * m : ℤ) := by
        simpa using hscale
      by_cases hk : k < 0
      · have hmpos : (0 : ℤ) < m := by
          exact_mod_cast Nat.pos_of_ne_zero hm
        have hkm : (k * m : ℤ) < 0 := Int.mul_neg_of_neg_of_pos hk hmpos
        have hkm' : (((k * m : ℤ) : WithTop ℤ) < 0) := by
          exact_mod_cast hkm
        have hk' : ((k : WithTop ℤ) < 0) := by
          exact_mod_cast hk
        rw [hscale']
        rw [if_pos hkm', if_pos hk', WithTop.untopD_coe, WithTop.untopD_coe]
        rw [Int.natAbs_mul]
        simp only [Int.natAbs_natCast]
        rw [Nat.mul_comm]
      · have hk_nonneg : 0 ≤ k := le_of_not_gt hk
        have hkm_nonneg : ¬ (k * m : ℤ) < 0 := by
          exact not_lt_of_ge (Int.mul_nonneg hk_nonneg (Int.natCast_nonneg m))
        have hkm_nonneg' : ¬ (((k * m : ℤ) : WithTop ℤ) < 0) := by
          exact_mod_cast hkm_nonneg
        have hk' : ¬ ((k : WithTop ℤ) < 0) := by
          exact_mod_cast hk
        rw [hscale']
        rw [if_neg hkm_nonneg', if_neg hk']
        simp

def UpperHalfPlane.poleRemoved (h : ℝ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun τ ↦ (𝕢 h τ) ^ (poleOrder h f) * f τ

def UpperHalfPlane.laurentqExpansion (h : ℝ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-(poleOrder h f : ℤ)) 1 * (HahnSeries.ofPowerSeries ℤ ℂ)
    (qExpansion h (poleRemoved h f))

lemma cuspFunction_qpow_mul_eq (hh : 0 < h) (f : ℍ → ℂ)
    {n : ℕ} {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) :
    cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ) q = q ^ n * cuspFunction h f q := by
  have him : 0 < Complex.im (Periodic.invQParam h q) :=
    Periodic.im_invQParam_pos_of_norm_lt_one hh hqnorm hq0
  have hleft :
      cuspFunction h (fun τ : ℍ ↦ (𝕢 h τ) ^ n * f τ) q =
        (fun τ : ℍ ↦ (𝕢 h τ) ^ n * f τ)
          (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) := by
    simpa [cuspFunction] using
      (Periodic.cuspFunction_eq_of_nonzero h
        (((fun τ : ℍ ↦ (𝕢 h τ) ^ n * f τ) ∘ UpperHalfPlane.ofComplex)) hq0)
  have hright :
      cuspFunction h f q = f (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) := by
    simpa [cuspFunction] using
      (Periodic.cuspFunction_eq_of_nonzero h (f ∘ UpperHalfPlane.ofComplex) hq0)
  have hqparam : 𝕢 h (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) = q := by
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos him] using
      (Periodic.qParam_right_inv hh.ne' hq0)
  calc
    cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ) q
        = (fun τ : ℍ ↦ (𝕢 h τ) ^ n * f τ)
            (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) := hleft
    _ = q ^ n * f (UpperHalfPlane.ofComplex (Periodic.invQParam h q)) := by simp [hqparam]
    _ = q ^ n * cuspFunction h f q := by simp [hright]

lemma analyticAt_cuspFunction_poleRemoved (h : ℝ) (f : ℍ → ℂ)
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    AnalyticAt ℂ (cuspFunction h (poleRemoved h f)) 0 := by
  by_cases hh : 0 < h
  · let M := poleOrder h f
    let F : ℂ → ℂ := cuspFunction h (poleRemoved h f)
    have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
      simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
    have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
      nhdsWithin_le_nhds hnorm0
    have hEq_shift :
        F =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q ↦ q ^ M * cuspFunction h f q := by
      filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
      have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
      simpa [F, M, UpperHalfPlane.poleRemoved] using
        (cuspFunction_qpow_mul_eq (h := h) hh (f := f) (n := M) hq0 hqnorm)
    cases ho : meromorphicOrderAt (cuspFunction h f) (0 : ℂ) with
    | top =>
        have hM0 : M = 0 := by
          simp [M, UpperHalfPlane.poleOrder, ho]
        have hEq_punctured : F =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun _ ↦ (0 : ℂ) := by
          have hzero : cuspFunction h f =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun _ ↦ (0 : ℂ) := by
            simpa using meromorphicOrderAt_eq_top_iff.1 ho
          filter_upwards [hEq_shift, hzero] with q hq hqzero
          calc
            F q = q ^ M * cuspFunction h f q := hq
            _ = 0 := by simp [hM0, hqzero]
        have hF0eq : F 0 = 0 := by
          calc
            F 0 = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) F := by
              simpa [F, cuspFunction] using
                (Periodic.cuspFunction_zero_eq_limUnder_nhds_ne
                  (h := h) (f := (poleRemoved h f) ∘ UpperHalfPlane.ofComplex))
            _ = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) (fun _ ↦ (0 : ℂ)) := by
              exact congrArg lim (Filter.map_congr hEq_punctured)
            _ = 0 := by
              simpa using (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).limUnder_eq
        exact analyticAt_const.congr
          (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hEq_punctured hF0eq).symm
    | coe k =>
        obtain ⟨g, hg_an, hg_ne, hg_eq0⟩ := (meromorphicOrderAt_eq_int_iff hmero).1 ho
        have hg_eq :
            cuspFunction h f =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q ↦ q ^ k * g q := by
          filter_upwards [hg_eq0] with q hq
          simpa [sub_zero, smul_eq_mul] using hq
        by_cases hk : k < 0
        · have hM : M = Int.natAbs k := by
            have hk' : ((k : WithTop ℤ) < 0) := by exact_mod_cast hk
            simp [M, UpperHalfPlane.poleOrder, ho, hk']
          have hMZ : (M : ℤ) = -k := by
            rw [hM, Int.ofNat_natAbs_of_nonpos (le_of_lt hk)]
          have hEq_punctured : F =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] g := by
            filter_upwards [hEq_shift, hg_eq, self_mem_nhdsWithin] with q hq hqg hqne
            have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hqne
            calc
              F q = q ^ M * (q ^ k * g q) := by rw [hq, hqg]
              _ = g q := by
                rw [← zpow_natCast, ← mul_assoc, ← zpow_add₀ hq0]
                simp [hMZ]
          have hF0eq : F 0 = g 0 := by
            calc
              F 0 = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) F := by
                simpa [F, cuspFunction] using
                  (Periodic.cuspFunction_zero_eq_limUnder_nhds_ne
                    (h := h) (f := (poleRemoved h f) ∘ UpperHalfPlane.ofComplex))
              _ = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) g := by
                exact congrArg lim (Filter.map_congr hEq_punctured)
              _ = g 0 := by
                exact (tendsto_nhdsWithin_of_tendsto_nhds hg_an.continuousAt.tendsto).limUnder_eq
          exact hg_an.congr
            (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hEq_punctured hF0eq).symm
        · have hk_nonneg : 0 ≤ k := le_of_not_gt hk
          lift k to ℕ using hk_nonneg with n hn
          let G : ℂ → ℂ := fun q ↦ q ^ n * g q
          have hM0 : M = 0 := by
            simp [M, UpperHalfPlane.poleOrder, ho]
          have hEq_punctured : F =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] G := by
            filter_upwards [hEq_shift, hg_eq] with q hq hqg
            calc
              F q = q ^ M * (q ^ (n : ℤ) * g q) := by rw [hq, hqg]
              _ = q ^ M * (q ^ n * g q) := by
                rw [zpow_natCast]
              _ = G q := by
                simp [G, hM0]
          have hG_an : AnalyticAt ℂ G 0 := by
            simpa [G] using (analyticAt_id.pow n).mul hg_an
          have hF0eq : F 0 = G 0 := by
            calc
              F 0 = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) F := by
                simpa [F, cuspFunction] using
                  (Periodic.cuspFunction_zero_eq_limUnder_nhds_ne
                    (h := h) (f := (poleRemoved h f) ∘ UpperHalfPlane.ofComplex))
              _ = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) G := by
                exact congrArg lim (Filter.map_congr hEq_punctured)
              _ = G 0 := by
                exact (tendsto_nhdsWithin_of_tendsto_nhds hG_an.continuousAt.tendsto).limUnder_eq
          exact hG_an.congr
            (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hEq_punctured hF0eq).symm
  · let F : ℂ → ℂ := cuspFunction h (poleRemoved h f)
    let τ0 : ℍ := Classical.choice inferInstance
    let c : ℂ := poleRemoved h f τ0
    have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
      simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
    have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
      nhdsWithin_le_nhds hnorm0
    have hconst :
        F =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun _ ↦ c := by
      filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
      have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
      have hlog_nonpos : Real.log ‖q‖ ≤ 0 :=
        Real.log_nonpos (norm_nonneg _) (le_of_lt hqnorm)
      have hh' : h ≤ 0 := le_of_not_gt hh
      have hnonneg : 0 ≤ -h := by linarith
      have hfac_nonneg : 0 ≤ -h / (2 * π) := div_nonneg hnonneg (by positivity)
      have him_nonpos : Complex.im (Periodic.invQParam h q) ≤ 0 := by
        rw [Periodic.im_invQParam]
        exact mul_nonpos_of_nonneg_of_nonpos hfac_nonneg hlog_nonpos
      have hof :
          UpperHalfPlane.ofComplex (Periodic.invQParam h q) = τ0 := by
        simpa [τ0] using UpperHalfPlane.ofComplex_apply_of_im_nonpos him_nonpos
      change cuspFunction h (poleRemoved h f) q = c
      rw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ hq0]
      simp [c, hof]
    have hF0eq : F 0 = c := by
      calc
        F 0 = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) F := by
          simpa [F, cuspFunction] using
            (Periodic.cuspFunction_zero_eq_limUnder_nhds_ne
              (h := h) (f := (poleRemoved h f) ∘ UpperHalfPlane.ofComplex))
        _ = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) (fun _ ↦ c) := by
          exact congrArg lim (Filter.map_congr hconst)
        _ = c := by
          simpa using (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).limUnder_eq
    exact analyticAt_const.congr
      (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hconst hF0eq).symm

lemma analyticAt_iff (h : ℝ) (f : ℍ → ℂ) :
    AnalyticAt ℂ (cuspFunction h f) 0 ↔ poleOrder h f = 0 := by
  sorry
