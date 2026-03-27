/-
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

structure MeromorphicCuspFunction (h : ℝ) where
  toFun : ℍ → ℂ
  width_pos : 0 < h
  meromorphicAtZero : MeromorphicAt (cuspFunction h toFun) (0 : ℂ)

instance (priority := 100) MeromorphicCuspFunction.funLike :
    FunLike (MeromorphicCuspFunction h) ℍ ℂ where
  coe := MeromorphicCuspFunction.toFun
  coe_injective' f g h := by cases f; cases g; congr

def MeromorphicCuspFunction.Simps.coe (f : MeromorphicCuspFunction h) : ℍ → ℂ := f

initialize_simps_projections MeromorphicCuspFunction (toFun → coe, as_prefix coe)

@[simp]
theorem MeromorphicCuspFunction.toFun_eq_coe {f : MeromorphicCuspFunction h} :
    f.toFun = (f : ℍ → ℂ) := rfl

@[simp]
theorem MeromorphicCuspFunction.coe_mk (f : ℍ → ℂ) (hh : 0 < h)
    (hf : MeromorphicAt (cuspFunction h f) (0 : ℂ)) : ⇑(mk f hh hf) = f := rfl

@[ext]
theorem MeromorphicCuspFunction.ext {f g : MeromorphicCuspFunction h} (hfg : ∀ x, f x = g x) :
    f = g :=
  DFunLike.ext f g hfg

protected def MeromorphicCuspFunction.copy (f : MeromorphicCuspFunction h) (f' : ℍ → ℂ)
    (h0 : f' = ⇑f) : MeromorphicCuspFunction h where
  toFun := f'
  width_pos := f.width_pos
  meromorphicAtZero := h0.symm ▸ f.meromorphicAtZero

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

lemma MeromorphicCuspFunction.cuspFunction_qpow_mul_eq (f : MeromorphicCuspFunction h)
    {n : ℕ} {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) :
    cuspFunction h (fun τ ↦ (𝕢 h τ) ^ n * f τ) q = q ^ n * cuspFunction h f q := by
  simpa using _root_.cuspFunction_qpow_mul_eq f.width_pos (f := (f : ℍ → ℂ))
    (n := n) hq0 hqnorm

lemma cuspFunction_analyticAt_iff (hh : 0 < h) (f : ℍ → ℂ) :
    ∃ (M : ℕ), AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ M * f τ)) (0 : ℂ)
    ↔ MeromorphicAt (cuspFunction h f) (0 : ℂ) := by
  have hleft :
      ∀ M : ℕ, AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ M * f τ)) (0 : ℂ) →
        MeromorphicAt (cuspFunction h f) (0 : ℂ) := by
    intro M hFAn
    rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
    refine ⟨-(M : ℤ), cuspFunction h (fun τ ↦ (𝕢 h τ) ^ M * f τ), hFAn, ?_⟩
    have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
      simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
    have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
      nhdsWithin_le_nhds hnorm0
    filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
    have hshift := cuspFunction_qpow_mul_eq (h := h) hh f (n := M) hq0 hqnorm
    have hpow_ne : (q ^ M : ℂ) ≠ 0 := pow_ne_zero M hq0
    simpa [smul_eq_mul, sub_zero] using
      calc
        cuspFunction h f q = (q ^ M)⁻¹ * (q ^ M * cuspFunction h f q) := by
          rw [← mul_assoc, inv_mul_cancel₀ hpow_ne, one_mul]
        _ = q ^ (-(M : ℤ)) * cuspFunction h (fun τ ↦ (𝕢 h τ) ^ M * f τ) q := by
          rw [hshift, ← zpow_natCast]
          simp
  by_cases hmer : MeromorphicAt (cuspFunction h f) (0 : ℂ)
  · rcases hmer with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    constructor
    · exact hleft M
    · intro _
      let F : ℂ → ℂ := cuspFunction h (fun τ ↦ (𝕢 h τ) ^ M * f τ)
      let G : ℂ → ℂ := fun q : ℂ ↦ q ^ M * cuspFunction h f q
      have hGAn : AnalyticAt ℂ G 0 := by
        simpa [G, smul_eq_mul] using hM
      have hEq_nonzero : ∀ {q : ℂ}, q ≠ 0 → ‖q‖ < 1 → F q = G q := by
        intro q hq0 hqnorm
        simpa [F, G] using (cuspFunction_qpow_mul_eq (h := h) hh f (n := M) hq0 hqnorm)
      have hEq_punctured : F =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] G := by
        have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
          simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
        have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
          nhdsWithin_le_nhds hnorm0
        filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
        exact hEq_nonzero (Set.mem_compl_singleton_iff.mp hq) hqnorm
      have hF0eq : F 0 = G 0 := by
        calc
          F 0 = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) F := by
            simpa [F, cuspFunction] using
              (Periodic.cuspFunction_zero_eq_limUnder_nhds_ne
                (h := h) (f := ((fun τ : ℍ ↦ (𝕢 h τ) ^ M * f τ) ∘ UpperHalfPlane.ofComplex)))
          _ = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) G := by
            exact congrArg lim (Filter.map_congr hEq_punctured)
          _ = G 0 := by
            exact (tendsto_nhdsWithin_of_tendsto_nhds hGAn.continuousAt.tendsto).limUnder_eq
      have hEq_nhds : F =ᶠ[nhds (0 : ℂ)] G := by
        have hball := Metric.ball_mem_nhds (0 : ℂ) zero_lt_one
        refine Filter.mem_of_superset hball ?_
        intro q hqball
        have hqnorm : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hqball
        by_cases hq0 : q = 0
        · simpa [F, G, hq0] using hF0eq
        · exact hEq_nonzero hq0 hqnorm
      exact (hGAn.congr hEq_nhds.symm)
  · refine ⟨0, ?_⟩
    constructor
    · intro hA
      exact hleft 0 hA
    · intro hA
      exact False.elim (hmer hA)

lemma cuspFunction_meromorphicAt_to_analyticAt (hh : 0 < h) (f : ℍ → ℂ)
    (hf : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    ∃ (M : ℕ), AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ M * f τ)) (0 : ℂ) := by
  rcases cuspFunction_analyticAt_iff (hh := hh) f with ⟨M, hM⟩
  exact ⟨M, hM.2 hf⟩
/-
lemma cuspFunction_meromorphicAt_to_analyticAt (hh : 0 < h) (f : ℍ → ℂ)
    (hf : MeromorphicAt (cuspFunction h f) (0 : ℂ)) :
    ∃ (M : ℕ), DifferentiableAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ M * f τ)) (0 : ℂ) := by
  rcases hf with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  let F : ℂ → ℂ := cuspFunction h (fun τ : ℍ ↦ (𝕢 h τ) ^ M * f τ)
  let G : ℂ → ℂ := fun q : ℂ ↦ q ^ M * cuspFunction h f q
  have hGAn : AnalyticAt ℂ G 0 := by
    simpa [G, cuspFunction, smul_eq_mul] using hM
  have hEq_nonzero : ∀ {q : ℂ}, q ≠ 0 → ‖q‖ < 1 → F q = G q := by
    intro q hq0 hqnorm
    simpa [F, G] using (cuspFunction_qpow_mul_eq (h := h) hh f (n := M) hq0 hqnorm)
  have hEq_punctured : F =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] G := by
    have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
      simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
    have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
      nhdsWithin_le_nhds hnorm0
    filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
    exact hEq_nonzero (Set.mem_compl_singleton_iff.mp hq) hqnorm
  have hF0eq : F 0 = G 0 := by
    calc
      F 0 = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) F := by
        simpa [F, cuspFunction] using
          (Periodic.cuspFunction_zero_eq_limUnder_nhds_ne
            (h := h) (f := ((fun τ : ℍ ↦ (𝕢 h τ) ^ M * f τ) ∘ UpperHalfPlane.ofComplex)))
      _ = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) G := by
        exact congrArg lim (Filter.map_congr hEq_punctured)
      _ = G 0 := by
        exact (tendsto_nhdsWithin_of_tendsto_nhds hGAn.continuousAt.tendsto).limUnder_eq
  have hEq_nhds : F =ᶠ[nhds (0 : ℂ)] G := by
    have hball : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) := Metric.ball_mem_nhds (0 : ℂ) zero_lt_one
    refine Filter.mem_of_superset hball ?_
    intro q hqball
    have hqnorm : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hqball
    by_cases hq0 : q = 0
    · simpa [F, G, hq0] using hF0eq
    · exact hEq_nonzero hq0 hqnorm
  exact hGAn.differentiableAt.congr_of_eventuallyEq hEq_nhds
-/

open MeromorphicCuspFunction

lemma MeromorphicCuspFunction.poleOrder_to_analyticAt (f : MeromorphicCuspFunction h) :
    ∃ (M : ℕ), AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ M * f τ)) (0 : ℂ) :=
  cuspFunction_meromorphicAt_to_analyticAt f.width_pos (f : ℍ → ℂ) f.meromorphicAtZero

def MeromorphicCuspFunction.poleOrder (f : MeromorphicCuspFunction h) : ℕ := by
  classical
  exact Nat.find (poleOrder_to_analyticAt f)

def MeromorphicCuspFunction.poleOrder' (f : ℍ → ℂ) : ℕ :=
  if meromorphicOrderAt (cuspFunction h f) 0 < 0 then
    Int.natAbs ((meromorphicOrderAt (cuspFunction h f) 0).untopD 0)
  else 0

lemma MeromorphicCuspFunction.AnalyticAt_iff (f : MeromorphicCuspFunction h) :
    AnalyticAt ℂ (cuspFunction h f) 0 ↔ f.poleOrder = 0 := by
  classical
  constructor
  · intro han
    have hzero :
        AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝕢 h τ) ^ 0 * f τ)) (0 : ℂ) := by
      simpa using han
    have hmin :
        Nat.find (MeromorphicCuspFunction.poleOrder_to_analyticAt f) ≤ 0 :=
      Nat.find_min' (MeromorphicCuspFunction.poleOrder_to_analyticAt f) hzero
    have hmin' : f.poleOrder ≤ 0 := by
      simpa [MeromorphicCuspFunction.poleOrder] using hmin
    exact Nat.le_zero.mp hmin'
  · intro h0
    have hm : Nat.find (MeromorphicCuspFunction.poleOrder_to_analyticAt f) = 0 := by
      simpa [MeromorphicCuspFunction.poleOrder] using h0
    have han := Nat.find_spec (MeromorphicCuspFunction.poleOrder_to_analyticAt f)
    rw [hm] at han
    simpa using han

def MeromorphicCuspFunction.to_analyticAt (f : MeromorphicCuspFunction h) : ℍ → ℂ :=
  fun τ ↦ (𝕢 h τ) ^ (f.poleOrder) * f τ

def MeromorphicCuspFunction.to_qExpansion (f : MeromorphicCuspFunction h) : PowerSeries ℂ :=
  qExpansion h (f.to_analyticAt)

def laurentqExpansion (h : ℝ) (f : MeromorphicCuspFunction h) : LaurentSeries ℂ :=
  HahnSeries.single (-(f.poleOrder : ℤ)) 1 * (HahnSeries.ofPowerSeries ℤ ℂ)
    (f.to_qExpansion)

lemma laurentqExpansion.coeff_eq_HahnSeries_add (f : MeromorphicCuspFunction h) {n : ℤ} :
    (laurentqExpansion h f).coeff n =
    ((HahnSeries.ofPowerSeries ℤ ℂ) (f.to_qExpansion)).coeff (n + f.poleOrder) := by
  rw [laurentqExpansion]
  simpa [poleOrder, sub_eq_add_neg] using
    (HahnSeries.coeff_single_mul
      (r := (1 : ℂ))
      (x := (HahnSeries.ofPowerSeries ℤ ℂ) (f.to_qExpansion))
      (a := n) (b := -f.poleOrder))

lemma laurentqExpansion.coeff_eq_zero_of_lt (f : MeromorphicCuspFunction h) {n : ℤ}
    (hn : n < -(f.poleOrder : ℤ)) : (laurentqExpansion h f).coeff n = 0 := by
  let m : ℤ := f.poleOrder
  have hneg : n + m < 0 := by
    linarith
  simpa [laurentqExpansion.coeff_eq_HahnSeries_add, m, hneg]
    using (PowerSeries.coeff_coe (f := f.to_qExpansion) (i := n + m))

lemma laurentqExpansion.coeff_neg_poleOrder_add (f : MeromorphicCuspFunction h) (n : ℕ) :
    (laurentqExpansion h f).coeff (-(f.poleOrder : ℤ) + n) = (f.to_qExpansion).coeff n := by
  have hnonneg : (0 : ℤ) ≤ n := by
    exact_mod_cast Nat.zero_le n
  have hnotneg : ¬ ((n : ℤ) < 0) := not_lt_of_ge hnonneg
  calc
    (laurentqExpansion h f).coeff (-(f.poleOrder : ℤ) + n)
        = ((HahnSeries.ofPowerSeries ℤ ℂ) (f.to_qExpansion)).coeff (n : ℤ) := by
            simp [laurentqExpansion.coeff_eq_HahnSeries_add]
    _ = (f.to_qExpansion).coeff n := by
          rw [PowerSeries.coeff_coe (f := f.to_qExpansion) (i := (n : ℤ))]
          simp [hnotneg]

lemma laurentqExpansion.coeff_of_geq (f : MeromorphicCuspFunction h) {n : ℤ}
    (hn : n ≥ -(f.poleOrder : ℤ)) : (laurentqExpansion h f).coeff n
    = (f.to_qExpansion).coeff (Int.toNat (n + f.poleOrder)) := by
  have hnonneg : 0 ≤ n + f.poleOrder := by
    linarith
  have hrewrite :
      (-(f.poleOrder : ℤ) + Int.toNat (n + f.poleOrder) : ℤ) = n := by
    rw [Int.toNat_of_nonneg hnonneg]
    linarith
  calc
    (laurentqExpansion h f).coeff n
        = (laurentqExpansion h f).coeff
            (-(f.poleOrder : ℤ) + Int.toNat (n + f.poleOrder)) := by
                conv_lhs => rw [hrewrite.symm]
    _ = (f.to_qExpansion).coeff (Int.toNat (n + f.poleOrder)) :=
          laurentqExpansion.coeff_neg_poleOrder_add (h := h) f (Int.toNat (n + f.poleOrder))

lemma laurentqExpansion.coeff_of_qExpansion (f : MeromorphicCuspFunction h) (n : ℤ) :
    (laurentqExpansion h f).coeff n = if n < -(f.poleOrder : ℤ) then 0
    else (f.to_qExpansion).coeff (Int.toNat (n + f.poleOrder))
    := by
  by_cases hlt : n < -(f.poleOrder : ℤ)
  · simp [hlt, laurentqExpansion.coeff_eq_zero_of_lt (h := h) f hlt]
  · simp [hlt, laurentqExpansion.coeff_of_geq (h := h) f (hn := le_of_not_gt hlt)]

lemma laurentqExpansion.coeff_neg_poleOrder (f : MeromorphicCuspFunction h) :
    (laurentqExpansion h f).coeff (-(f.poleOrder : ℤ)) = (f.to_qExpansion).coeff 0 := by
  simp [laurentqExpansion.coeff_of_qExpansion]

lemma laurentqExpansion.coeff_zero (f : MeromorphicCuspFunction h) :
    (laurentqExpansion h f).coeff 0 = (f.to_qExpansion).coeff f.poleOrder := by
  simp [laurentqExpansion.coeff_of_qExpansion]

--需化简
lemma MeromorphicCuspFunction.to_qExpansion_coeff_zero_ne (f : MeromorphicCuspFunction h)
    (h0 : f.poleOrder ≠ 0) : (f.to_qExpansion).coeff 0 ≠ 0 := by
  classical
  rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨m, hm⟩
  let F : ℂ → ℂ := cuspFunction h (fun τ ↦ (𝕢 h τ) ^ (m + 1) * f τ)
  let H : ℂ → ℂ := cuspFunction h (fun τ ↦ (𝕢 h τ) ^ m * f τ)
  have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
    simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds hnorm0
  have hmfind : Nat.find (MeromorphicCuspFunction.poleOrder_to_analyticAt f) = m + 1 := by
    simpa [MeromorphicCuspFunction.poleOrder] using hm
  have hFan : AnalyticAt ℂ F (0 : ℂ) := by
    have hFan' := Nat.find_spec (MeromorphicCuspFunction.poleOrder_to_analyticAt f)
    rw [hmfind] at hFan'
    simpa [F] using hFan'
  have hFmer : MeromorphicAt F (0 : ℂ) := by
    let G : ℂ → ℂ := fun q ↦ q ^ (m + 1) * cuspFunction h f q
    have hGmer : MeromorphicAt G (0 : ℂ) := by
      exact ((analyticAt_id.pow (m + 1)).meromorphicAt.mul f.meromorphicAtZero)
    have hFG : F =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] G := by
      filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
      exact f.cuspFunction_qpow_mul_eq (n := m + 1) (Set.mem_compl_singleton_iff.mp hq) hqnorm
    exact (MeromorphicAt.meromorphicAt_congr hFG).2 hGmer
  by_contra hcoeff0
  have hF0 : F 0 = 0 := by
    have hcoeff0' : cuspFunction h f.to_analyticAt 0 = 0 := by
      simpa [MeromorphicCuspFunction.to_qExpansion, qExpansion_coeff] using hcoeff0
    have hFdef : F = cuspFunction h f.to_analyticAt := by
      funext q
      change cuspFunction h (fun τ ↦ (𝕢 h τ) ^ (m + 1) * f τ) q =
        cuspFunction h (fun τ ↦ (𝕢 h τ) ^ f.poleOrder * f τ) q
      simp [hm]
    exact hFdef.symm ▸ hcoeff0'
  have hFtend : Tendsto F (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (0 : ℂ)) := by
    simpa [hF0] using
      (hFan.continuousAt.continuousWithinAt.tendsto :
        Tendsto F (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (F 0)))
  have hForder_pos : 0 < meromorphicOrderAt F (0 : ℂ) :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hFmer).1 hFtend
  have hHmer : MeromorphicAt H (0 : ℂ) := by
    let G : ℂ → ℂ := fun q ↦ q ^ m * cuspFunction h f q
    have hGmer : MeromorphicAt G (0 : ℂ) := by
      exact ((analyticAt_id.pow m).meromorphicAt.mul f.meromorphicAtZero)
    have hHG : H =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] G := by
      filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
      exact f.cuspFunction_qpow_mul_eq (n := m) (Set.mem_compl_singleton_iff.mp hq) hqnorm
    exact (MeromorphicAt.meromorphicAt_congr hHG).2 hGmer
  have hHG :
      H =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun q ↦ q⁻¹ * F q := by
    filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
    have hmul :
        q ^ m * cuspFunction h f q = q⁻¹ * (q ^ (m + 1) * cuspFunction h f q) := by
      field_simp [hq0]
      rw [pow_succ']
      ring
    calc
      H q = q ^ m * cuspFunction h f q := f.cuspFunction_qpow_mul_eq (n := m) hq0 hqnorm
      _ = q⁻¹ * (q ^ (m + 1) * cuspFunction h f q) := hmul
      _ = q⁻¹ * F q := by simp [F, f.cuspFunction_qpow_mul_eq (n := m + 1) hq0 hqnorm]
  have hqorder : meromorphicOrderAt (fun q : ℂ ↦ q) (0 : ℂ) = (1 : WithTop ℤ) := by
    have hidorder : analyticOrderAt (fun q : ℂ ↦ q) (0 : ℂ) = 1 := by
      simpa using
        (analyticAt_id.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (x := (0 : ℂ)) (by simp))
    have hqid :
        meromorphicOrderAt (fun q : ℂ ↦ q) (0 : ℂ) =
          (analyticOrderAt (fun q : ℂ ↦ q) (0 : ℂ)).map (↑) :=
      AnalyticAt.meromorphicOrderAt_eq (f := fun q : ℂ ↦ q) (x := (0 : ℂ)) analyticAt_id
    rw [hqid, hidorder]
    simp
  have hqinvorder : meromorphicOrderAt (fun q : ℂ ↦ q⁻¹) (0 : ℂ) = (-1 : WithTop ℤ) := by
    calc
      meromorphicOrderAt (fun q : ℂ ↦ q⁻¹) (0 : ℂ)
          = -meromorphicOrderAt (fun q : ℂ ↦ q) (0 : ℂ) := by
              simpa using (meromorphicOrderAt_inv (f := fun q : ℂ ↦ q) (x := (0 : ℂ)))
      _ = (-1 : WithTop ℤ) := by simp [hqorder]
  have hHorder_nonneg : 0 ≤ meromorphicOrderAt H (0 : ℂ) := by
    have hqinvmer : MeromorphicAt (fun q : ℂ ↦ q⁻¹) (0 : ℂ) :=
      (AnalyticAt.meromorphicAt (f := fun q : ℂ ↦ q) (x := (0 : ℂ)) analyticAt_id).inv
    rw [meromorphicOrderAt_congr hHG]
    change 0 ≤ meromorphicOrderAt (((fun q : ℂ ↦ q⁻¹) * F)) (0 : ℂ)
    rw [meromorphicOrderAt_mul hqinvmer hFmer, hqinvorder]
    cases horderF : meromorphicOrderAt F (0 : ℂ) with
    | top =>
        simp
    | coe n =>
        have hn : 0 < n := by simpa [horderF] using hForder_pos
        have : 0 ≤ n - 1 := by linarith
        have hnonneg' : (0 : WithTop ℤ) ≤ ((n - 1 : ℤ) : WithTop ℤ) := by
          exact_mod_cast this
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hnonneg'
  obtain ⟨c, hc⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg hHmer).2 hHorder_nonneg
  have hH0 : H 0 = c := by
    calc
      H 0 = limUnder (nhdsWithin (0 : ℂ) ({0}ᶜ)) H := by
        simpa [H, cuspFunction] using
          (Periodic.cuspFunction_zero_eq_limUnder_nhds_ne
            (h := h) (f := ((fun τ : ℍ ↦ (𝕢 h τ) ^ m * f τ) ∘ UpperHalfPlane.ofComplex)))
      _ = c := hc.limUnder_eq
  have hHan : AnalyticAt ℂ H (0 : ℂ) := by
    have hHcont : ContinuousAt H (0 : ℂ) := by
      rw [continuousAt_iff_punctured_nhds, hH0]
      exact hc
    exact hHmer.analyticAt hHcont
  have hmin : f.poleOrder ≤ m := Nat.find_min'
    (MeromorphicCuspFunction.poleOrder_to_analyticAt f) (by simpa [H] using hHan)
  rw [hm] at hmin
  exact Nat.not_succ_le_self m hmin

lemma MeromorphicCuspFunction.to_qExpansion_ne_zero (f : MeromorphicCuspFunction h)
    (h0 : f.poleOrder ≠ 0) : f.to_qExpansion ≠ 0 := by
  intro hq
  have hcoeff := MeromorphicCuspFunction.to_qExpansion_coeff_zero_ne f h0
  simp [hq] at hcoeff

lemma MeromorphicCuspFunction.meromorphicOrderAt_cuspFunction_eq_neg_poleOrder
    (f : MeromorphicCuspFunction h) (h0 : f.poleOrder ≠ 0) :
    meromorphicOrderAt (cuspFunction h f) 0 = -(f.poleOrder : ℤ) := by
  classical
  let G : ℂ → ℂ := cuspFunction h f.to_analyticAt
  have hGan : AnalyticAt ℂ G 0 := by
    simpa [G, MeromorphicCuspFunction.to_analyticAt, MeromorphicCuspFunction.poleOrder] using
      Nat.find_spec (MeromorphicCuspFunction.poleOrder_to_analyticAt f)
  have hG0 : G 0 ≠ 0 := by
    have hcoeff0 : (f.to_qExpansion).coeff 0 ≠ 0 :=
      MeromorphicCuspFunction.to_qExpansion_coeff_zero_ne f h0
    simpa [G, MeromorphicCuspFunction.to_qExpansion, qExpansion_coeff] using hcoeff0
  refine
    (meromorphicOrderAt_eq_int_iff
      (f := cuspFunction h (f : ℍ → ℂ)) (x := 0) (n := -(f.poleOrder : ℤ))
      f.meromorphicAtZero).2 ?_
  refine ⟨G, hGan, hG0, ?_⟩
  have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
    simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds hnorm0
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
  have hshift : G q = q ^ f.poleOrder * cuspFunction h f q := by
    simpa [G, MeromorphicCuspFunction.to_analyticAt] using
      (f.cuspFunction_qpow_mul_eq (n := f.poleOrder) hq0 hqnorm)
  have hpow_ne : (q ^ f.poleOrder : ℂ) ≠ 0 := pow_ne_zero _ hq0
  calc
    cuspFunction h f q = (q ^ f.poleOrder)⁻¹ * (q ^ f.poleOrder * cuspFunction h f q) := by
      rw [← mul_assoc, inv_mul_cancel₀ hpow_ne, one_mul]
    _ = (q ^ f.poleOrder)⁻¹ * G q := by rw [← hshift]
    _ = q ^ (-(f.poleOrder : ℤ)) * G q := by
      rw [← zpow_natCast]
      simp
    _ = (q - 0) ^ (-(f.poleOrder : ℤ)) • G q := by
      simp [sub_zero, smul_eq_mul]

theorem order (f : MeromorphicCuspFunction h) :
    f.poleOrder = Int.toNat (-(meromorphicOrderAt (cuspFunction h f) 0).untopD 0) := by
  by_cases h0 : f.poleOrder = 0
  · rw [h0]
    have han : AnalyticAt ℂ (cuspFunction h f) 0 :=
      (MeromorphicCuspFunction.AnalyticAt_iff f).2 h0
    have hnonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 :=
      han.meromorphicOrderAt_nonneg
    cases ho : meromorphicOrderAt (cuspFunction h f) 0 with
    | top =>
        simp
    | coe n =>
        have hn : 0 ≤ n := by simpa [ho] using hnonneg
        have hnonpos : -n ≤ 0 := by linarith
        rw [WithTop.untopD_coe, Int.toNat_of_nonpos hnonpos]
  · rw [MeromorphicCuspFunction.meromorphicOrderAt_cuspFunction_eq_neg_poleOrder f h0]
    have hnonneg : 0 ≤ (f.poleOrder : ℤ) := by
      exact_mod_cast Nat.zero_le f.poleOrder
    change f.poleOrder = Int.toNat (-WithTop.untopD 0 ((-(f.poleOrder : ℤ)) : WithTop ℤ))
    have huntop : WithTop.untopD 0 ((-(f.poleOrder : ℤ)) : WithTop ℤ) = -(f.poleOrder : ℤ) := by
      simpa using (WithTop.untopD_coe (d := (0 : ℤ)) (x := (-(f.poleOrder : ℤ))))
    have harg : -WithTop.untopD 0 ((-(f.poleOrder : ℤ)) : WithTop ℤ) = (f.poleOrder : ℤ) := by
      simpa using congrArg Neg.neg huntop
    rw [harg]
    have hnat : ((f.poleOrder : ℤ).toNat) = f.poleOrder := by
      exact_mod_cast (Int.toNat_of_nonneg hnonneg)
    exact hnat.symm

lemma laurentqExpansion.ne_zero (f : MeromorphicCuspFunction h) (h0 : f.poleOrder ≠ 0) :
    laurentqExpansion h f ≠ 0 := by
  rw [laurentqExpansion]
  refine mul_ne_zero ?_ ?_
  · exact HahnSeries.single_ne_zero one_ne_zero
  · intro hq
    have hq' : (HahnSeries.ofPowerSeries ℤ ℂ) (f.to_qExpansion) =
        (HahnSeries.ofPowerSeries ℤ ℂ) 0 := by
      simpa using hq
    exact MeromorphicCuspFunction.to_qExpansion_ne_zero f h0
      (HahnSeries.ofPowerSeries_injective hq')

lemma laurentqExpansion.poleOrder_to_order (f : MeromorphicCuspFunction h)
    (h0 : f.poleOrder ≠ 0) : f.poleOrder = -(laurentqExpansion h f).order := by
  have hcoeff :
      (laurentqExpansion h f).coeff (-(f.poleOrder : ℤ)) ≠ 0 := by
    simpa [laurentqExpansion.coeff_neg_poleOrder] using
      (MeromorphicCuspFunction.to_qExpansion_coeff_zero_ne f h0)
  have horder_le : (laurentqExpansion h f).order ≤ -(f.poleOrder : ℤ) :=
    HahnSeries.order_le_of_coeff_ne_zero hcoeff
  have horder_ge : -(f.poleOrder : ℤ) ≤ (laurentqExpansion h f).order := by
    by_contra hlt
    have hzero :
        (laurentqExpansion h f).coeff (laurentqExpansion h f).order = 0 := by
      exact laurentqExpansion.coeff_eq_zero_of_lt f (lt_of_not_ge hlt)
    exact (HahnSeries.coeff_order_eq_zero.not.2 (laurentqExpansion.ne_zero f h0)) hzero
  have horder : (laurentqExpansion h f).order = -(f.poleOrder : ℤ) :=
    le_antisymm horder_le horder_ge
  simpa using (congrArg Neg.neg horder).symm

lemma laurentqExpansion.to_qExpansion_eq_powerSeriesPart (f : MeromorphicCuspFunction h)
    (h0 : f.poleOrder ≠ 0) : f.to_qExpansion = (laurentqExpansion h f).powerSeriesPart := by
  ext n
  rw [LaurentSeries.powerSeriesPart_coeff]
  have hm : (f.poleOrder : ℤ) = -(laurentqExpansion h f).order :=
    laurentqExpansion.poleOrder_to_order (h := h) f h0
  have horder : (laurentqExpansion h f).order = -(f.poleOrder : ℤ) := by
    simpa using (congrArg Neg.neg hm).symm
  rw [horder]
  simpa using (laurentqExpansion.coeff_neg_poleOrder_add (h := h) f n).symm

lemma laurentqExpansion.eq_qExpansion_iff (f : MeromorphicCuspFunction h) :
    laurentqExpansion h f = qExpansion h f ↔ f.poleOrder = 0 := by
  constructor
  · intro heq
    by_contra h0
    have hcoeff :
        (laurentqExpansion h f).coeff (-(f.poleOrder : ℤ)) ≠ 0 := by
      simpa [laurentqExpansion.coeff_neg_poleOrder] using
        (MeromorphicCuspFunction.to_qExpansion_coeff_zero_ne f h0)
    have hnatpos : 0 < f.poleOrder := Nat.pos_of_ne_zero h0
    have hpos : 0 < (f.poleOrder : ℤ) := by
      exact_mod_cast hnatpos
    have hneg : -(f.poleOrder : ℤ) < 0 := by
      linarith
    have hqcoeff :
        (qExpansion h f : LaurentSeries ℂ).coeff (-(f.poleOrder : ℤ)) = 0 := by
      simpa [hneg, hnatpos] using
        (PowerSeries.coeff_coe (f := qExpansion h f) (i := -(f.poleOrder : ℤ)))
    have hEqCoeff := congrArg
      (fun g : LaurentSeries ℂ => g.coeff (-(f.poleOrder : ℤ))) heq
    have hEqCoeff' :
        (laurentqExpansion h f).coeff (-(f.poleOrder : ℤ)) =
          (qExpansion h f : LaurentSeries ℂ).coeff (-(f.poleOrder : ℤ)) := by
      simpa using hEqCoeff
    rw [hqcoeff] at hEqCoeff'
    exact hcoeff hEqCoeff'
  · intro h0
    have hfun : f.to_analyticAt = (f : ℍ → ℂ) := by
      funext τ
      simp [MeromorphicCuspFunction.to_analyticAt, h0]
    have hqexp : f.to_qExpansion = qExpansion h f := by
      rw [MeromorphicCuspFunction.to_qExpansion, hfun]
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

lemma MeromorphicCuspFunction.cuspFunction_to_analyticAt_meromorphicAt
    (f : MeromorphicCuspFunction h) :
    MeromorphicAt (cuspFunction h f.to_analyticAt) (0 : ℂ) := by
  let G : ℂ → ℂ := fun q ↦ q ^ f.poleOrder * cuspFunction h f q
  have hGmer : MeromorphicAt G (0 : ℂ) := by
    exact ((analyticAt_id.pow f.poleOrder).meromorphicAt.mul f.meromorphicAtZero)
  have hnorm0 : {q : ℂ | ‖q‖ < 1} ∈ nhds (0 : ℂ) := by
    simpa [Metric.ball, dist_eq_norm] using (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds hnorm0
  have hFG : cuspFunction h f.to_analyticAt =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)] G := by
    filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
    simpa [G, MeromorphicCuspFunction.to_analyticAt] using
      (f.cuspFunction_qpow_mul_eq (n := f.poleOrder) hq0 hqnorm)
  exact (MeromorphicAt.meromorphicAt_congr hFG).2 hGmer

lemma MeromorphicCuspFunction.cuspFunction_to_analyticAt_analyticAt
    (f : MeromorphicCuspFunction h) :
    AnalyticAt ℂ (cuspFunction h f.to_analyticAt) (0 : ℂ) := by
  classical
  simpa [MeromorphicCuspFunction.to_analyticAt, MeromorphicCuspFunction.poleOrder] using
    Nat.find_spec (MeromorphicCuspFunction.poleOrder_to_analyticAt f)

lemma MeromorphicCuspFunction.exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt
    (f : MeromorphicCuspFunction h) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧
      DifferentiableOn ℂ (cuspFunction h f.to_analyticAt) (Metric.closedBall 0 R) := by
  rcases (f.cuspFunction_to_analyticAt_analyticAt).exists_ball_analyticOnNhd with
      ⟨R0, hR0pos, hR0⟩
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

lemma laurentqExpansion_coeff_eq_circleIntegral
    (f : MeromorphicCuspFunction h) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧ ∀ n : ℤ,
      (laurentqExpansion h f).coeff n =
        ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1)) := by
  rcases f.exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt with
      ⟨R, hRpos, hRlt1, hDiff⟩
  refine ⟨R, hRpos, hRlt1, ?_⟩
  intro n
  by_cases hn : n < -(f.poleOrder : ℤ)
  · have hcoeff0 : (laurentqExpansion h f).coeff n = 0 :=
      laurentqExpansion.coeff_eq_zero_of_lt (h := h) (f := f) hn
    let k : ℕ := Int.toNat (-(n + f.poleOrder + 1))
    let F : ℂ → ℂ := fun z ↦ z ^ k * cuspFunction h f.to_analyticAt z
    have hk_nonneg : 0 ≤ -(n + f.poleOrder + 1) := by
      linarith
    have hk : (k : ℤ) = -(n + f.poleOrder + 1) := by
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
        Set.EqOn (fun z : ℂ => cuspFunction h f z / z ^ (n + 1)) F (Metric.sphere (0 : ℂ) R) := by
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
          cuspFunction h f.to_analyticAt z = z ^ f.poleOrder * cuspFunction h f z := by
        simpa [MeromorphicCuspFunction.to_analyticAt] using
          (f.cuspFunction_qpow_mul_eq (n := f.poleOrder) hz0 hqnorm)
      have hk0 : (k : ℤ) + (f.poleOrder : ℤ) + (n + 1) = 0 := by
        linarith [hk]
      exact (div_eq_iff (zpow_ne_zero (n + 1) hz0)).2 <| by
        simp only [F]
        rw [hcf, ← zpow_natCast, ← zpow_natCast]
        have haux :
            (z ^ (k : ℤ) * (z ^ (f.poleOrder : ℤ) * cuspFunction h f z)) * z ^ (n + 1) =
              cuspFunction h f z := by
          calc
            (z ^ (k : ℤ) * (z ^ (f.poleOrder : ℤ) * cuspFunction h f z)) * z ^ (n + 1)
                = (z ^ (k : ℤ) * z ^ (f.poleOrder : ℤ) * z ^ (n + 1)) *
                    cuspFunction h f z := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
            _ = (z ^ ((k : ℤ) + (f.poleOrder : ℤ)) * z ^ (n + 1)) * cuspFunction h f z := by
                  have hkm :
                      z ^ (k : ℤ) * z ^ (f.poleOrder : ℤ) =
                        z ^ ((k : ℤ) + (f.poleOrder : ℤ)) := by
                    simpa using (zpow_add₀ hz0 (k : ℤ) (f.poleOrder : ℤ)).symm
                  simpa [mul_assoc, mul_left_comm, mul_comm] using
                    congrArg (fun t : ℂ => t * z ^ (n + 1) * cuspFunction h f z) hkm
            _ = (z ^ ((k : ℤ) + (f.poleOrder : ℤ) + (n + 1))) * cuspFunction h f z := by
                  have hkmn :
                      z ^ ((k : ℤ) + (f.poleOrder : ℤ)) * z ^ (n + 1) =
                        z ^ (((k : ℤ) + (f.poleOrder : ℤ)) + (n + 1)) := by
                    simpa using
                      (zpow_add₀ hz0 (((k : ℤ) + (f.poleOrder : ℤ))) (n + 1)).symm
                  simpa [mul_assoc] using
                    congrArg (fun t : ℂ => t * cuspFunction h f z) hkmn
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
  · have hn' : -(f.poleOrder : ℤ) ≤ n := by
      exact le_of_not_gt hn
    let m : ℕ := Int.toNat (n + f.poleOrder)
    have hm_nonneg : 0 ≤ n + f.poleOrder := by
      linarith
    have hm : (m : ℤ) = n + f.poleOrder := by
      simpa [m] using (Int.toNat_of_nonneg hm_nonneg).symm
    have hcoeff :
        (laurentqExpansion h f).coeff n = f.to_qExpansion.coeff m := by
      simpa [m] using (laurentqExpansion.coeff_of_geq (h := h) (f := f) (hn := hn'))
    have hCoeffInt :
        f.to_qExpansion.coeff m =
          ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h f.to_analyticAt z / z ^ (m + 1)) := by
      simpa [MeromorphicCuspFunction.to_qExpansion] using
        (qExpansion_coeff_eq_circleIntegral_of_differentiableOn
          (h := h) (g := f.to_analyticAt) (R := R) hRpos hDiff m)
    have hEqOn :
        Set.EqOn
          (fun z : ℂ => cuspFunction h f.to_analyticAt z / z ^ (m + 1))
          (fun z : ℂ => cuspFunction h f z / z ^ (n + 1))
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
          cuspFunction h f.to_analyticAt z = z ^ f.poleOrder * cuspFunction h f z := by
        simpa [MeromorphicCuspFunction.to_analyticAt] using
          (f.cuspFunction_qpow_mul_eq (n := f.poleOrder) hz0 hqnorm)
      have hpow :
          z ^ (((m + 1 : ℕ) : ℤ)) / z ^ (n + 1) = z ^ (f.poleOrder : ℤ) := by
        have hm' : (m : ℤ) - n = (f.poleOrder : ℤ) := by
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
          _ = z ^ (f.poleOrder : ℤ) := by rw [hm']
      exact (div_eq_iff (pow_ne_zero (m + 1) hz0)).2 <| by
        rw [hcf]
        have hcalc :
          cuspFunction h f z / z ^ (n + 1) * z ^ (m + 1)
              = (z ^ (((m + 1 : ℕ) : ℤ)) / z ^ (n + 1)) * cuspFunction h f z := by
                    rw [zpow_natCast]
                    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        calc
          z ^ f.poleOrder * cuspFunction h f z
              = z ^ (f.poleOrder : ℤ) * cuspFunction h f z := by rw [zpow_natCast]
          _ = (z ^ (((m + 1 : ℕ) : ℤ)) / z ^ (n + 1)) * cuspFunction h f z := by rw [hpow]
          _ = cuspFunction h f z / z ^ (n + 1) * z ^ (m + 1) := hcalc.symm
    have hIntEq :
        ∮ z in C(0, R), cuspFunction h f.to_analyticAt z / z ^ (m + 1) =
          ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1) := by
      exact circleIntegral.integral_congr hRpos.le hEqOn
    calc
      (laurentqExpansion h f).coeff n = f.to_qExpansion.coeff m := hcoeff
      _ = ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h f.to_analyticAt z / z ^ (m + 1)) :=
        hCoeffInt
      _ = ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h f z / z ^ (n + 1)) := by
            simp [hIntEq]

#min_imports
-/
