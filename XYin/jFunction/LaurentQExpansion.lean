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

lemma cuspFunction_nat_mul_eq_cuspFunction_pow {h : ℝ} {m : ℕ} {f : ℍ → ℂ}
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

lemma meromorphicOrderAt_cuspFunction_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
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

lemma poleOrder_nat_mul {h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ}
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

def UpperHalfPlane.to_qExpansion (h : ℝ) (f : ℍ → ℂ) : PowerSeries ℂ :=
  qExpansion h (poleRemoved h f)

def UpperHalfPlane.laurentqExpansion (h : ℝ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-(poleOrder h f : ℤ)) 1 * (HahnSeries.ofPowerSeries ℤ ℂ)
    (to_qExpansion h f)

lemma cuspFunction_qpow_mul_eq {h : ℝ} (hh : 0 < h) (f : ℍ → ℂ)
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

lemma analyticAt_cuspFunction_poleRemoved {h : ℝ} {f : ℍ → ℂ}
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

lemma analyticAt_iff {h : ℝ} {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    AnalyticAt ℂ (cuspFunction h f) 0 ↔ poleOrder h f = 0 := by
  constructor
  · intro han
    have hnonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 :=
      han.meromorphicOrderAt_nonneg
    have hnotlt : ¬ meromorphicOrderAt (cuspFunction h f) 0 < 0 := not_lt_of_ge hnonneg
    simp [UpperHalfPlane.poleOrder, hnotlt]
  · intro h0
    have hfun : poleRemoved h f = f := by
      funext τ
      simp [UpperHalfPlane.poleRemoved, h0]
    simpa [hfun] using
      (analyticAt_cuspFunction_poleRemoved (h := h) (f := f) hmero)

lemma analyticAt_cuspFunction_of_not_pos {h : ℝ} {f : ℍ → ℂ} (hh : h ≤ 0) :
    AnalyticAt ℂ (cuspFunction h f) 0 := by
  let F : ℂ → ℂ := cuspFunction h f
  let τ0 : ℍ := Classical.choice inferInstance
  let c : ℂ := f τ0
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
    have hnonneg : 0 ≤ -h := by linarith
    have hfac_nonneg : 0 ≤ -h / (2 * π) := div_nonneg hnonneg (by positivity)
    have him_nonpos : Complex.im (Periodic.invQParam h q) ≤ 0 := by
      rw [Periodic.im_invQParam]
      exact mul_nonpos_of_nonneg_of_nonpos hfac_nonneg hlog_nonpos
    have hof :
        UpperHalfPlane.ofComplex (Periodic.invQParam h q) = τ0 := by
      simpa [τ0] using UpperHalfPlane.ofComplex_apply_of_im_nonpos him_nonpos
    change cuspFunction h f q = c
    rw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ hq0]
    simp [c, hof]
  have hF0eq : F 0 = c := by
    calc
      F 0 = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) F := by
        simpa [F, cuspFunction] using
          (Periodic.cuspFunction_zero_eq_limUnder_nhds_ne
            (h := h) (f := f ∘ UpperHalfPlane.ofComplex))
      _ = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) (fun _ ↦ c) := by
        exact congrArg lim (Filter.map_congr hconst)
      _ = c := by
        simpa using (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).limUnder_eq
  exact analyticAt_const.congr
    (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hconst hF0eq).symm

lemma cuspFunction_poleRemoved_eq {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ))
    {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) :
    cuspFunction h (poleRemoved h f) q = q ^ poleOrder h f * cuspFunction h f q := by
  by_cases hh : 0 < h
  · simpa [UpperHalfPlane.poleRemoved] using
      (cuspFunction_qpow_mul_eq (h := h) hh (f := f) (n := poleOrder h f) hq0 hqnorm)
  · have hpole : poleOrder h f = 0 := by
      exact (analyticAt_iff (h := h) (f := f) hmero).1
        (analyticAt_cuspFunction_of_not_pos (h := h) (f := f) (le_of_not_gt hh))
    have hfun : poleRemoved h f = f := by
      funext τ
      simp [UpperHalfPlane.poleRemoved, hpole]
    simp [hfun, hpole]

lemma laurentqExpansion.coeff_eq_HahnSeries_add (h : ℝ) (f : ℍ → ℂ) {n : ℤ} :
    (laurentqExpansion h f).coeff n =
    ((HahnSeries.ofPowerSeries ℤ ℂ) (to_qExpansion h f)).coeff (n + poleOrder h f) := by
  rw [laurentqExpansion]
  simpa [UpperHalfPlane.poleOrder, sub_eq_add_neg] using
    (HahnSeries.coeff_single_mul
      (r := (1 : ℂ))
      (x := (HahnSeries.ofPowerSeries ℤ ℂ) (to_qExpansion h f))
      (a := n) (b := -poleOrder h f))

lemma laurentqExpansion.coeff_eq_zero_of_lt {h : ℝ} {f : ℍ → ℂ} {n : ℤ}
    (hn : n < -(poleOrder h f : ℤ)) : (laurentqExpansion h f).coeff n = 0 := by
  let m : ℤ := poleOrder h f
  have hneg : n + m < 0 := by
    linarith
  simpa [laurentqExpansion.coeff_eq_HahnSeries_add, m, hneg]
    using (PowerSeries.coeff_coe (f := to_qExpansion h f) (i := n + m))

lemma laurentqExpansion.coeff_neg_poleOrder_add (h : ℝ) (f : ℍ → ℂ) (n : ℕ) :
    (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ) + n) = (to_qExpansion h f).coeff n := by
  have hnonneg : (0 : ℤ) ≤ n := by
    exact_mod_cast Nat.zero_le n
  have hnotneg : ¬ ((n : ℤ) < 0) := not_lt_of_ge hnonneg
  calc
    (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ) + n)
        = ((HahnSeries.ofPowerSeries ℤ ℂ) (to_qExpansion h f)).coeff (n : ℤ) := by
            simp [laurentqExpansion.coeff_eq_HahnSeries_add]
    _ = (to_qExpansion h f).coeff n := by
          rw [PowerSeries.coeff_coe (f := to_qExpansion h f) (i := (n : ℤ))]
          simp [hnotneg]

lemma laurentqExpansion.coeff_of_geq {h : ℝ} {f : ℍ → ℂ} {n : ℤ} (hn : n ≥ -(poleOrder h f : ℤ)) :
    (laurentqExpansion h f).coeff n = (to_qExpansion h f).coeff (Int.toNat (n + poleOrder h f))
    := by
  have hnonneg : 0 ≤ n + poleOrder h f := by
    linarith
  have hrewrite :
      (-(poleOrder h f : ℤ) + Int.toNat (n + poleOrder h f) : ℤ) = n := by
    rw [Int.toNat_of_nonneg hnonneg]
    linarith
  calc
    (laurentqExpansion h f).coeff n
        = (laurentqExpansion h f).coeff
            (-(poleOrder h f : ℤ) + Int.toNat (n + poleOrder h f)) := by
                conv_lhs => rw [hrewrite.symm]
    _ = (to_qExpansion h f).coeff (Int.toNat (n + poleOrder h f)) :=
          laurentqExpansion.coeff_neg_poleOrder_add (h := h) (f := f)
            (Int.toNat (n + poleOrder h f))

lemma laurentqExpansion.coeff_of_qExpansion (h : ℝ) (f : ℍ → ℂ) (n : ℤ) :
    (laurentqExpansion h f).coeff n = if n < -(poleOrder h f : ℤ) then 0
    else (to_qExpansion h f).coeff (Int.toNat (n + poleOrder h f)) := by
  by_cases hlt : n < -(poleOrder h f : ℤ)
  · simp [hlt, laurentqExpansion.coeff_eq_zero_of_lt (h := h) (f := f) hlt]
  · simp [hlt, laurentqExpansion.coeff_of_geq (h := h) (f := f)
      (hn := le_of_not_gt hlt)]

lemma laurentqExpansion.coeff_neg_poleOrder (h : ℝ) (f : ℍ → ℂ) :
    (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ)) = (to_qExpansion h f).coeff 0 := by
  simpa using laurentqExpansion.coeff_neg_poleOrder_add (h := h) (f := f) 0

lemma laurentqExpansion.coeff_zero (h : ℝ) (f : ℍ → ℂ) :
    (laurentqExpansion h f).coeff 0 = (to_qExpansion h f).coeff (poleOrder h f) := by
  have hn : -(poleOrder h f : ℤ) ≤ (0 : ℤ) := by
    exact neg_nonpos.mpr (by exact_mod_cast Nat.zero_le (poleOrder h f))
  simpa using laurentqExpansion.coeff_of_geq (h := h) (f := f) (n := 0) (hn := hn)

lemma meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero {h : ℝ} {f : ℍ → ℂ}
    (h0 : poleOrder h f ≠ 0) :
    meromorphicOrderAt (cuspFunction h f) 0 = -(poleOrder h f : ℤ) := by
  unfold UpperHalfPlane.poleOrder at h0 ⊢
  set o : WithTop ℤ := meromorphicOrderAt (cuspFunction h f) 0
  have ho_lt : o < 0 := by
    by_contra ho_ge
    simp [o, ho_ge] at h0
  cases ho : o with
  | top =>
      simp [ho] at ho_lt
  | coe k =>
      rw [ho] at ho_lt
      have hk : k < 0 := by
        exact_mod_cast ho_lt
      have hk_le : k ≤ 0 := le_of_lt hk
      have hnatAbs : ((Int.natAbs k : ℕ) : ℤ) = -k := Int.ofNat_natAbs_of_nonpos hk_le
      simp [hk, hnatAbs]

lemma to_qExpansion_coeff_zero_ne {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    (to_qExpansion h f).coeff 0 ≠ 0 := by
  let M := poleOrder h f
  let G : ℂ → ℂ := cuspFunction h (poleRemoved h f)
  have hGan : AnalyticAt ℂ G 0 := by
    simpa [G] using analyticAt_cuspFunction_poleRemoved (h := h) (f := f) hmero
  have horderF : meromorphicOrderAt (cuspFunction h f) 0 = -(poleOrder h f : ℤ) := by
    exact meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero (h := h) (f := f) h0
  have hpow_mer : MeromorphicAt (fun q : ℂ ↦ q ^ M) (0 : ℂ) := by
    simpa [M] using (analyticAt_id.pow (poleOrder h f)).meromorphicAt
  have hpow_ord : meromorphicOrderAt (fun q : ℂ ↦ q ^ M) (0 : ℂ) = (M : WithTop ℤ) := by
    calc
      meromorphicOrderAt (fun q : ℂ ↦ q ^ M) (0 : ℂ)
          = M * meromorphicOrderAt (𝕜 := ℂ) id 0 := by
              simpa [M] using
                (meromorphicOrderAt_pow
                  (f := id) (x := (0 : ℂ))
                  (hf := (analyticAt_id : AnalyticAt ℂ id (0 : ℂ)).meromorphicAt)
                  (n := poleOrder h f))
      _ = (M : WithTop ℤ) := by
            simp [M, meromorphicOrderAt_id]
  have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
    simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds hnorm0
  have hG_eq :
      G =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q ↦ q ^ M * cuspFunction h f q := by
    filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
    simpa [G, M] using
      (cuspFunction_poleRemoved_eq (h := h) (f := f) hmero hq0 hqnorm)
  have hGord : meromorphicOrderAt G (0 : ℂ) = 0 := by
    rw [meromorphicOrderAt_congr hG_eq]
    change meromorphicOrderAt ((fun q : ℂ ↦ q ^ M) * cuspFunction h f) 0 = 0
    rw [meromorphicOrderAt_mul hpow_mer hmero, hpow_ord, horderF]
    simp [M]
  have hGanalyticOrder0 : analyticOrderAt G (0 : ℂ) = 0 := by
    rw [AnalyticAt.meromorphicOrderAt_eq (f := G) (x := (0 : ℂ)) hGan] at hGord
    simpa using hGord
  have hG0ne : G 0 ≠ 0 := (hGan.analyticOrderAt_eq_zero).1 hGanalyticOrder0
  simpa [G, UpperHalfPlane.to_qExpansion, qExpansion_coeff] using hG0ne

lemma to_qExpansion_ne_zero {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    to_qExpansion h f ≠ 0 := by
  intro hq
  have hcoeff := to_qExpansion_coeff_zero_ne (h := h) (f := f) hmero h0
  simp [hq] at hcoeff

lemma meromorphicOrderAt_cuspFunction_eq_neg_poleOrder {h : ℝ} {f : ℍ → ℂ}
    (h0 : poleOrder h f ≠ 0) : meromorphicOrderAt (cuspFunction h f) 0 = -(poleOrder h f : ℤ) :=
  meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero (h := h) (f := f) h0

theorem order (h : ℝ) (f : ℍ → ℂ) :
    poleOrder h f = Int.toNat (-(meromorphicOrderAt (cuspFunction h f) 0).untopD 0) := by
  unfold UpperHalfPlane.poleOrder
  set o : WithTop ℤ := meromorphicOrderAt (cuspFunction h f) 0
  cases ho : o with
  | top => simp
  | coe k =>
      by_cases hk : k < 0
      · have hk_le : k ≤ 0 := le_of_lt hk
        have hk_nonneg : 0 ≤ -k := by linarith
        rw [if_pos (by simpa [o, ho] using hk)]
        have hnatAbs : ((Int.natAbs k : ℕ) : ℤ) = -k := Int.ofNat_natAbs_of_nonpos hk_le
        have hnatAbs' : Int.natAbs k = (-k).toNat := by
          apply Int.ofNat.inj
          simpa [Int.toNat_of_nonneg hk_nonneg] using hnatAbs
        simp [hnatAbs']
      · have hk_nonneg : 0 ≤ k := le_of_not_gt hk
        have hnotlt : ¬ ((k : WithTop ℤ) < 0) := by
          exact_mod_cast hk
        rw [if_neg (by simpa [o, ho] using hnotlt)]
        have hnonpos : -k ≤ 0 := by linarith
        simp [Int.toNat_of_nonpos hnonpos]

lemma laurentqExpansion.ne_zero {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    laurentqExpansion h f ≠ 0 := by
  rw [laurentqExpansion]
  refine mul_ne_zero ?_ ?_
  · exact HahnSeries.single_ne_zero one_ne_zero
  · intro hq
    have hq' : (HahnSeries.ofPowerSeries ℤ ℂ) (to_qExpansion h f) =
        (HahnSeries.ofPowerSeries ℤ ℂ) 0 := by
      simpa using hq
    exact to_qExpansion_ne_zero (h := h) (f := f) hmero h0
      (HahnSeries.ofPowerSeries_injective hq')

lemma laurentqExpansion.poleOrder_to_order {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    poleOrder h f = -(laurentqExpansion h f).order := by
  have hcoeff :
      (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ)) ≠ 0 := by
    rw [laurentqExpansion.coeff_neg_poleOrder (h := h) (f := f)]
    exact to_qExpansion_coeff_zero_ne (h := h) (f := f) hmero h0
  have horder_le : (laurentqExpansion h f).order ≤ -(poleOrder h f : ℤ) :=
    HahnSeries.order_le_of_coeff_ne_zero hcoeff
  have horder_ge : -(poleOrder h f : ℤ) ≤ (laurentqExpansion h f).order := by
    by_contra hlt
    have hzero :
        (laurentqExpansion h f).coeff (laurentqExpansion h f).order = 0 := by
      exact laurentqExpansion.coeff_eq_zero_of_lt (h := h) (f := f) (lt_of_not_ge hlt)
    exact (HahnSeries.coeff_order_eq_zero.not.2 (laurentqExpansion.ne_zero hmero h0)) hzero
  have horder : (laurentqExpansion h f).order = -(poleOrder h f : ℤ) :=
    le_antisymm horder_le horder_ge
  simpa using (congrArg Neg.neg horder).symm

lemma laurentqExpansion.to_qExpansion_eq_powerSeriesPart {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) (h0 : poleOrder h f ≠ 0) :
    to_qExpansion h f = (laurentqExpansion h f).powerSeriesPart := by
  ext n
  rw [LaurentSeries.powerSeriesPart_coeff]
  have hm : (poleOrder h f : ℤ) = -(laurentqExpansion h f).order :=
    laurentqExpansion.poleOrder_to_order (h := h) (f := f) hmero h0
  have horder : (laurentqExpansion h f).order = -(poleOrder h f : ℤ) := by
    simpa using (congrArg Neg.neg hm).symm
  rw [horder]
  simpa using (laurentqExpansion.coeff_neg_poleOrder_add (h := h) (f := f) n).symm


lemma laurentqExpansion.eq_qExpansion_iff {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    laurentqExpansion h f = qExpansion h f ↔ poleOrder h f = 0 := by
  constructor
  · intro heq
    by_contra h0
    have hcoeff :
        (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ)) ≠ 0 := by
      rw [laurentqExpansion.coeff_neg_poleOrder (h := h) (f := f)]
      exact to_qExpansion_coeff_zero_ne (h := h) (f := f) hmero h0
    have hnatpos : 0 < poleOrder h f := Nat.pos_of_ne_zero h0
    have hpos : 0 < (poleOrder h f : ℤ) := by
      exact_mod_cast hnatpos
    have hneg : -(poleOrder h f : ℤ) < 0 := by
      linarith
    have hqcoeff :
        (qExpansion h f : LaurentSeries ℂ).coeff (-(poleOrder h f : ℤ)) = 0 := by
      simpa [hneg, hnatpos] using
        (PowerSeries.coeff_coe (f := qExpansion h f) (i := -(poleOrder h f : ℤ)))
    have hEqCoeff := congrArg
      (fun g : LaurentSeries ℂ ↦ g.coeff (-(poleOrder h f : ℤ))) heq
    have hEqCoeff' :
        (laurentqExpansion h f).coeff (-(poleOrder h f : ℤ)) =
          (qExpansion h f : LaurentSeries ℂ).coeff (-(poleOrder h f : ℤ)) := by
      simpa using hEqCoeff
    rw [hqcoeff] at hEqCoeff'
    exact hcoeff hEqCoeff'
  · intro h0
    have hfun : (poleRemoved h f) = (f : ℍ → ℂ) := by
      funext τ
      simp [UpperHalfPlane.poleRemoved, h0]
    have hqexp : to_qExpansion h f = qExpansion h f := by
      rw [UpperHalfPlane.to_qExpansion, hfun]
    simp [laurentqExpansion, h0, hqexp]


lemma qExpansion_coeff_eq_circleIntegral_of_differentiableOn
    {g : ℍ → ℂ} {R : ℝ} (hR : 0 < R)
    (hDiff : DifferentiableOn ℂ (cuspFunction h g) (Metric.closedBall 0 R)) (n : ℕ) :
    (qExpansion h g).coeff n =
      ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h g z / z ^ (n + 1)) := by
  have hci := hDiff.circleIntegral_one_div_sub_center_pow_smul hR n
  calc
    (qExpansion h g).coeff n = (↑n.factorial)⁻¹ * iteratedDeriv n (cuspFunction h g) 0 := by
      simp [qExpansion]
    _ = (2 * π * I)⁻¹ * ((2 * π * I) / (↑n.factorial) * iteratedDeriv n (cuspFunction h g) 0) := by
      field_simp [two_pi_I_ne_zero]
    _ = (2 * π * I)⁻¹ *
          (∮ z in C(0, R), (1 / (z - 0) ^ (n + 1)) • cuspFunction h g z) := by
            have hci' := congrArg (fun t : ℂ => (2 * π * I)⁻¹ * t) hci
            simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hci'.symm
    _ = ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h g z / z ^ (n + 1)) := by
          simp [smul_eq_mul, sub_zero, div_eq_inv_mul, mul_assoc, mul_left_comm, mul_comm]

lemma cuspFunction_to_analyticAt_meromorphicAt {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    MeromorphicAt (cuspFunction h (poleRemoved h f)) (0 : ℂ) := by
  exact (analyticAt_cuspFunction_poleRemoved (h := h) (f := f) hmero).meromorphicAt

lemma cuspFunction_to_analyticAt_analyticAt {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    AnalyticAt ℂ (cuspFunction h (poleRemoved h f)) (0 : ℂ) := by
  exact analyticAt_cuspFunction_poleRemoved (h := h) (f := f) hmero

-- double check
lemma exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) : ∃ R : ℝ, 0 < R ∧ R < 1 ∧
      DifferentiableOn ℂ (cuspFunction h (poleRemoved h f)) (Metric.closedBall 0 R) := by
  rcases (cuspFunction_to_analyticAt_analyticAt (h := h) (f := f) hmero).exists_ball_analyticOnNhd
    with ⟨R0, hR0pos, hR0⟩
  let R : ℝ := min (R0 / 2) (1 / 2)
  have hRpos : 0 < R := by
    refine lt_min ?_ ?_
    · linarith
    · norm_num
  have hRlt1 : R < 1 := by
    have hRle : R ≤ (1 / 2 : ℝ) := min_le_right _ _
    linarith
  have hRltR0 : R < R0 := by
    calc
      R ≤ R0 / 2 := min_le_left _ _
      _ < R0 := by linarith
  refine ⟨R, hRpos, hRlt1, ?_⟩
  exact (hR0.analyticOn.differentiableOn).mono (Metric.closedBall_subset_ball hRltR0)

lemma laurentqExpansion_coeff_eq_circleIntegral {h : ℝ} {f : ℍ → ℂ}
    (hmero : MeromorphicAt (cuspFunction h f) (0 : ℂ)) : ∃ R : ℝ, 0 < R ∧ R < 1 ∧ ∀ n : ℤ,
      (laurentqExpansion h f).coeff n =
        ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1)) := by
  rcases exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt (h := h) (f := f) hmero with
      ⟨R, hRpos, hRlt1, hDiff⟩
  refine ⟨R, hRpos, hRlt1, ?_⟩
  intro n
  by_cases hn : n < -(poleOrder h f : ℤ)
  · have hcoeff0 : (laurentqExpansion h f).coeff n = 0 :=
      laurentqExpansion.coeff_eq_zero_of_lt (h := h) (f := f) hn
    let k : ℕ := Int.toNat (-(n + poleOrder h f + 1))
    let F : ℂ → ℂ := fun z ↦ z ^ k * cuspFunction h (poleRemoved h f) z
    have hk_nonneg : 0 ≤ -(n + poleOrder h f + 1) := by
      linarith
    have hk : (k : ℤ) = -(n + poleOrder h f + 1) := by
      simpa [k] using (Int.toNat_of_nonneg hk_nonneg)
    have hDiffF : DifferentiableOn ℂ F (Metric.closedBall (0 : ℂ) R) := by
      exact (differentiableOn_id.pow k).mul hDiff
    have hDiffF_ball : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) R) :=
      hDiffF.mono Metric.ball_subset_closedBall
    have hContF : ContinuousOn F (Metric.closedBall (0 : ℂ) R) := hDiffF.continuousOn
    have hIntF : ∮ z in C(0, R), F z = 0 := by
      exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
        (c := 0) (R := R) hRpos.le countable_empty hContF
        (fun z hz => (hDiffF_ball z hz.1).differentiableAt (isOpen_ball.mem_nhds hz.1))
    have hEqOn :
        Set.EqOn (fun z : ℂ ↦ cuspFunction h f z / z ^ (n + 1)) F (Metric.sphere (0 : ℂ) R) := by
      intro z hz
      have hz0 : z ≠ 0 := by
        intro hz'
        have hz_norm : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
        simp [hz'] at hz_norm
        linarith
      have hqnorm : ‖z‖ < 1 := by
        calc
          ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
          _ < 1 := hRlt1
      have hcf :
          cuspFunction h (poleRemoved h f) z = z ^ poleOrder h f * cuspFunction h f z := by
        simpa using (cuspFunction_poleRemoved_eq (h := h) (f := f) hmero hz0 hqnorm)
      have hk0 : (k : ℤ) + (poleOrder h f : ℤ) + (n + 1) = 0 := by
        linarith [hk]
      exact (div_eq_iff (zpow_ne_zero (n + 1) hz0)).2 <| by
        simp only [F]
        rw [hcf, ← zpow_natCast, ← zpow_natCast]
        have haux :
            (z ^ (k : ℤ) * (z ^ (poleOrder h f : ℤ) * cuspFunction h f z)) * z ^ (n + 1) =
              cuspFunction h f z := by
          calc
            (z ^ (k : ℤ) * (z ^ (poleOrder h f : ℤ) * cuspFunction h f z)) * z ^ (n + 1)
                = (z ^ (k : ℤ) * z ^ (poleOrder h f : ℤ) * z ^ (n + 1)) *
                    cuspFunction h f z := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
            _ = (z ^ ((k : ℤ) + (poleOrder h f : ℤ)) * z ^ (n + 1)) * cuspFunction h f z := by
                  have hkm :
                      z ^ (k : ℤ) * z ^ (poleOrder h f : ℤ) =
                        z ^ ((k : ℤ) + (poleOrder h f : ℤ)) := by
                    simpa using (zpow_add₀ hz0 (k : ℤ) (poleOrder h f : ℤ)).symm
                  simpa [mul_assoc, mul_left_comm, mul_comm] using
                    congrArg (fun t : ℂ ↦ t * z ^ (n + 1) * cuspFunction h f z) hkm
            _ = (z ^ ((k : ℤ) + (poleOrder h f : ℤ) + (n + 1))) * cuspFunction h f z := by
                  have hkmn :
                      z ^ ((k : ℤ) + (poleOrder h f : ℤ)) * z ^ (n + 1) =
                        z ^ (((k : ℤ) + (poleOrder h f : ℤ)) + (n + 1)) := by
                    simpa using
                      (zpow_add₀ hz0 (((k : ℤ) + (poleOrder h f : ℤ))) (n + 1)).symm
                  simpa [mul_assoc] using
                    congrArg (fun t : ℂ ↦ t * cuspFunction h f z) hkmn
            _ = cuspFunction h f z := by simp [hk0]
        exact haux.symm
    have hIntEq :
        ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1) = ∮ z in C(0, R), F z := by
      exact circleIntegral.integral_congr hRpos.le hEqOn
    have hIntZero : ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1) = 0 := by
      calc
        ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1) = ∮ z in C(0, R), F z := hIntEq
        _ = 0 := hIntF
    calc
      (laurentqExpansion h f).coeff n = 0 := hcoeff0
      _ = ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1)) := by
            simp [hIntZero]
  · have hn' : -(poleOrder h f : ℤ) ≤ n := by
      exact le_of_not_gt hn
    let m : ℕ := Int.toNat (n + poleOrder h f)
    have hm_nonneg : 0 ≤ n + poleOrder h f := by
      linarith
    have hm : (m : ℤ) = n + poleOrder h f := by
      simpa [m] using (Int.toNat_of_nonneg hm_nonneg).symm
    have hcoeff :
        (laurentqExpansion h f).coeff n = (to_qExpansion h f).coeff m := by
      simpa [m] using (laurentqExpansion.coeff_of_geq (h := h) (f := f) (hn := hn'))
    have hCoeffInt :
        (to_qExpansion h f).coeff m =
          ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h (poleRemoved h f) z / z ^ (m + 1)) := by
      simpa [UpperHalfPlane.to_qExpansion] using
        (qExpansion_coeff_eq_circleIntegral_of_differentiableOn
          (h := h) (g := poleRemoved h f) (R := R) hRpos hDiff m)
    have hEqOn :
        Set.EqOn
          (fun z : ℂ ↦ cuspFunction h (poleRemoved h f) z / z ^ (m + 1))
          (fun z : ℂ ↦ cuspFunction h f z / z ^ (n + 1))
          (Metric.sphere (0 : ℂ) R) := by
      intro z hz
      have hz0 : z ≠ 0 := by
        intro hz'
        have hz_norm : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
        simp [hz'] at hz_norm
        linarith
      have hqnorm : ‖z‖ < 1 := by
        calc
          ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
          _ < 1 := hRlt1
      have hcf :
          cuspFunction h (poleRemoved h f) z = z ^ poleOrder h f * cuspFunction h f z := by
        simpa using (cuspFunction_poleRemoved_eq (h := h) (f := f) hmero hz0 hqnorm)
      have hpow :
          z ^ (((m + 1 : ℕ) : ℤ)) / z ^ (n + 1) = z ^ (poleOrder h f : ℤ) := by
        have hm' : (m : ℤ) - n = (poleOrder h f : ℤ) := by
          linarith [hm]
        have hsub : (((m + 1 : ℕ) : ℤ) - (n + 1)) = (m : ℤ) - n := by
          calc
            (((m + 1 : ℕ) : ℤ) - (n + 1)) = ((m : ℤ) + 1) - (n + 1) := by norm_num
            _ = (m : ℤ) - n := by ring
        calc
          z ^ (((m + 1 : ℕ) : ℤ)) / z ^ (n + 1)
              = z ^ ((((m + 1 : ℕ) : ℤ) - (n + 1))) := by
                  simpa using (zpow_sub₀ hz0 (((m + 1 : ℕ) : ℤ)) (n + 1)).symm
          _ = z ^ ((m : ℤ) - n) := by rw [hsub]
          _ = z ^ (poleOrder h f : ℤ) := by rw [hm']
      exact (div_eq_iff (pow_ne_zero (m + 1) hz0)).2 <| by
        rw [hcf]
        have hcalc :
          cuspFunction h f z / z ^ (n + 1) * z ^ (m + 1)
              = (z ^ (((m + 1 : ℕ) : ℤ)) / z ^ (n + 1)) * cuspFunction h f z := by
                    rw [zpow_natCast]
                    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        calc
          z ^ poleOrder h f * cuspFunction h f z
              = z ^ (poleOrder h f : ℤ) * cuspFunction h f z := by rw [zpow_natCast]
          _ = (z ^ (((m + 1 : ℕ) : ℤ)) / z ^ (n + 1)) * cuspFunction h f z := by rw [hpow]
          _ = cuspFunction h f z / z ^ (n + 1) * z ^ (m + 1) := hcalc.symm
    have hIntEq :
        ∮ z in C(0, R), cuspFunction h (poleRemoved h f) z / z ^ (m + 1) =
          ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1) := by
      exact circleIntegral.integral_congr hRpos.le hEqOn
    calc
      (laurentqExpansion h f).coeff n = (to_qExpansion h f).coeff m := hcoeff
      _ = ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h (poleRemoved h f) z / z ^ (m + 1)) :=
        hCoeffInt
      _ = ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1)) := by
            simp [hIntEq]
