/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import XYin.PhD.Cox.CoxMatrices.Basic

/-!
# Laurent expansions of the Cox roots

This file constructs the transformed Laurent series from equation (11.13), identifies it with
the analytic expansion of each Cox root, and defines the Galois reindexing of `C(m)`.
-/

open Complex Function MatrixGroups UpperHalfPlane

noncomputable section

namespace Cox

/-- The primitive `m`-th root used in equation (11.13). -/
def zeta (m : ℕ+) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))

theorem zeta_isPrimitiveRoot (m : ℕ+) : IsPrimitiveRoot (zeta m) (m : ℕ) := by
  simpa only [zeta] using
    Complex.isPrimitiveRoot_exp (m : ℕ) (PNat.ne_zero m)

/-- The integral Laurent coefficient of the analytic `j`-function. -/
noncomputable def jIntCoeff (n : ℤ) : ℤ :=
  (j_laurentQExpansion_isIntegral (n := n)).choose

theorem jIntCoeff_spec (n : ℤ) :
    (laurentqExpansion 1 j).coeff n = (jIntCoeff n : ℂ) := by
  exact (j_laurentQExpansion_isIntegral (n := n)).choose_spec

theorem jIntCoeff_neg_one : jIntCoeff (-1) = 1 := by
  have hcoeff : (jIntCoeff (-1) : ℂ) = 1 := by
    rw [← jIntCoeff_spec]
    calc
      (laurentqExpansion 1 j).coeff (-1) = (to_qExpansion 1 j).coeff 0 := by
        simpa [j_poleOrder] using
          (laurentqExpansion.coeff_neg_poleOrder (h := 1) (f := j))
      _ = (qExpansion 1 qj).coeff 0 := by rw [j_to_qExpansion]
      _ = 1 := qj_qExpansion_coeff_zero
  exact_mod_cast hcoeff

/-- Equation (11.13) as a formal Laurent series in `t=q^(1/m)`. -/
noncomputable def transformedJSeries {K : Type*} [Field K] {m : ℕ+}
    (ζ : K) (σ : CoxMatrix m) : LaurentSeries K :=
  ⟨fun k ↦ if (σ.a : ℤ) ^ 2 ∣ k ∧ -((σ.a : ℤ) ^ 2) ≤ k
      then (jIntCoeff (k / (σ.a : ℤ) ^ 2) : K) *
        ζ ^ (((σ.a : ℤ) * (σ.b : ℤ)) * (k / (σ.a : ℤ) ^ 2))
      else 0,
   by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨-((σ.a : ℤ) ^ 2), fun k hk ↦ ?_⟩
    simp only [Function.mem_support, ne_eq] at hk
    by_contra h
    apply hk
    rw [if_neg]
    exact fun h' ↦ h h'.2⟩

theorem transformedJSeries_coeff {K : Type*} [Field K] {m : ℕ+}
    (ζ : K) (σ : CoxMatrix m) (k : ℤ) :
    (transformedJSeries ζ σ).coeff k =
      if (σ.a : ℤ) ^ 2 ∣ k ∧ -((σ.a : ℤ) ^ 2) ≤ k
      then (jIntCoeff (k / (σ.a : ℤ) ^ 2) : K) *
        ζ ^ (((σ.a : ℤ) * (σ.b : ℤ)) * (k / (σ.a : ℤ) ^ 2))
      else 0 := rfl

private def coxPhaseAux (m : ℕ+) (σ : CoxMatrix m) : ℂ :=
  zeta m ^ (σ.a * σ.b)

private theorem qParam_coxAction_aux (m : ℕ+) (σ : CoxMatrix m) (τ : ℍ) :
    Periodic.qParam 1 (σ.act τ) =
      coxPhaseAux m σ * Periodic.qParam ((m : ℕ) : ℝ) τ ^ (σ.a ^ 2) := by
  rw [Periodic.qParam, Periodic.qParam, CoxMatrix.coe_act, coxPhaseAux, zeta]
  simp only [Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have hm : (m : ℂ) = σ.a * σ.d := by
    exact_mod_cast σ.determinant.symm
  rw [hm]
  field_simp [show (σ.a : ℂ) ≠ 0 by exact_mod_cast σ.a_pos.ne',
    show (σ.d : ℂ) ≠ 0 by exact_mod_cast σ.d_pos.ne']
  push_cast
  rw [hm]
  ring

private theorem periodic_comp_ofComplex_of_vadd_aux {g : ℍ → ℂ} {h : ℝ}
    (hg : ∀ τ, g (h +ᵥ τ) = g τ) :
    Periodic (g ∘ UpperHalfPlane.ofComplex) (h : ℂ) := by
  intro z
  by_cases hz : 0 < z.im
  · have hzadd : 0 < (z + (h : ℂ)).im := by simpa using hz
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hzadd,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    convert hg ⟨z, hz⟩ using 2
    ext
    simp [UpperHalfPlane.coe_vadd, add_comm]
  · have hz' : z.im ≤ 0 := le_of_not_gt hz
    have hzadd : (z + (h : ℂ)).im ≤ 0 := by simpa using hz'
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos hzadd,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hz']

private theorem j_periodic_aux : Periodic (j ∘ UpperHalfPlane.ofComplex) 1 := by
  have hperiod (z : ℍ) : j ((1 : ℝ) +ᵥ z) = j z := by
    rw [← UpperHalfPlane.modular_T_smul]
    exact j_modularGroup_smul _ _
  simpa only [Complex.ofReal_one] using periodic_comp_ofComplex_of_vadd_aux hperiod

private theorem cuspFunction_coxCompose_aux (m : ℕ+) (σ : CoxMatrix m) (f : ℍ → ℂ)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) 1) {q : ℂ}
    (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) :
    cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ f (σ.act τ)) q =
      cuspFunction 1 f (coxPhaseAux m σ * q ^ (σ.a ^ 2)) := by
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast PNat.pos m
  have him := Periodic.im_invQParam_pos_of_norm_lt_one hmpos hqnorm hq0
  let τ : ℍ := ⟨Periodic.invQParam ((m : ℕ) : ℝ) q, him⟩
  let w : ℍ := σ.act τ
  have hleft : cuspFunction ((m : ℕ) : ℝ) (fun z : ℍ ↦ f (σ.act z)) q = f w := by
    change Periodic.cuspFunction ((m : ℕ) : ℝ) _ q = f w
    rw [Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
    simp only [Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hqparam : Periodic.qParam 1 w = coxPhaseAux m σ * q ^ (σ.a ^ 2) := by
    rw [show w = σ.act τ from rfl, qParam_coxAction_aux]
    rw [show Periodic.qParam ((m : ℕ) : ℝ) τ = q by
      simpa [τ] using Periodic.qParam_right_inv
        (show (((m : ℕ) : ℝ)) ≠ 0 by positivity) hq0]
  rw [hleft, ← hqparam]
  exact (UpperHalfPlane.eq_cuspFunction w one_ne_zero hfper).symm

private theorem cuspFunction_coxAction_aux (m : ℕ+) (σ : CoxMatrix m) {q : ℂ}
    (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) :
    cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ)) q =
      cuspFunction 1 j (coxPhaseAux m σ * q ^ (σ.a ^ 2)) :=
  cuspFunction_coxCompose_aux m σ j j_periodic_aux hq0 hqnorm

private theorem coxPhase_ne_zero_aux (m : ℕ+) (σ : CoxMatrix m) :
    coxPhaseAux m σ ≠ 0 := by
  exact pow_ne_zero _ (Complex.exp_ne_zero _)

private theorem cuspFunction_coxAction_eventuallyEq_aux (m : ℕ+) (σ : CoxMatrix m) :
    cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ)) =ᶠ[nhdsWithin 0 ({0}ᶜ)]
      cuspFunction 1 j ∘ fun q ↦ coxPhaseAux m σ * q ^ (σ.a ^ 2) := by
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds (by simpa [Metric.ball, dist_eq_norm]
      using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
  exact cuspFunction_coxAction_aux m σ (Set.mem_compl_singleton_iff.mp hq) hqnorm

private theorem cuspFunction_coxAction_meromorphicAt_aux (m : ℕ+) (σ : CoxMatrix m) :
    MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ))) 0 := by
  let φ : ℂ → ℂ := fun q ↦ coxPhaseAux m σ * q ^ (σ.a ^ 2)
  have hφ0 : φ 0 = 0 := by simp [φ, σ.a_pos.ne']
  have hφan : AnalyticAt ℂ φ 0 := by fun_prop
  have hbase : MeromorphicAt (cuspFunction 1 j) (φ 0) := by
    simpa [hφ0] using j_cuspFunction_meromorphicAt
  have hcomp : MeromorphicAt ((cuspFunction 1 j) ∘ φ) 0 :=
    hbase.comp_analyticAt hφan
  exact hcomp.congr
    (by simpa [φ] using (cuspFunction_coxAction_eventuallyEq_aux m σ).symm)

private theorem poleOrder_coxAction_aux (m : ℕ+) (σ : CoxMatrix m) :
    poleOrder ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ)) = σ.a ^ 2 := by
  let η := coxPhaseAux m σ
  let r := σ.a ^ 2
  let φ : ℂ → ℂ := fun q ↦ η * q ^ r
  have hη : η ≠ 0 := coxPhase_ne_zero_aux m σ
  have hφ0 : φ 0 = 0 := by simp [φ, r, σ.a_pos.ne']
  have hφan : AnalyticAt ℂ φ 0 := by fun_prop
  have hφeq : φ = (fun _ : ℂ ↦ η) * id ^ r := by
    funext q
    simp [φ]
  have hηorder : analyticOrderAt (fun _ : ℂ ↦ η) 0 = 0 :=
    (analyticAt_const.analyticOrderAt_eq_zero).2 (by simpa using hη)
  have hpoworder : analyticOrderAt (id ^ r : ℂ → ℂ) 0 = r := by
    rw [analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
    simp
  have hφorder : analyticOrderAt φ 0 = r := by
    rw [hφeq, analyticOrderAt_mul analyticAt_const (analyticAt_id.pow r),
      hηorder, hpoworder, zero_add]
  have hsubeq : (fun q ↦ φ q - φ 0) = φ := by
    funext q
    simp [hφ0]
  have hsuborder : analyticOrderAt (fun q ↦ φ q - φ 0) 0 = r := by
    rw [hsubeq, hφorder]
  have hφnc : ¬Filter.EventuallyConst φ (nhds 0) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hsuborder]
    simp
  have hbaseOrder :
      meromorphicOrderAt (cuspFunction 1 j) 0 = (-1 : WithTop ℤ) := by
    simpa [j_poleOrder] using
      (meromorphicOrderAt_cuspFunction_eq_neg_poleOrder
        (h := 1) (f := j) (by simp [j_poleOrder]))
  have hbaseMer : MeromorphicAt (cuspFunction 1 j) (φ 0) := by
    simpa [hφ0] using j_cuspFunction_meromorphicAt
  have hcompOrder :
      meromorphicOrderAt ((cuspFunction 1 j) ∘ φ) 0 = (-(r : ℤ) : ℤ) := by
    rw [hbaseMer.meromorphicOrderAt_comp hφan hφnc,
      hsuborder, hφ0, hbaseOrder, ENat.map_coe]
    change ((-1 : ℤ) : WithTop ℤ) * ((r : ℤ) : WithTop ℤ) =
      ((-(r : ℤ) : ℤ) : WithTop ℤ)
    norm_cast
    simp
  have horder :
      meromorphicOrderAt
          (cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ))) 0 =
        (-(r : ℤ) : ℤ) := by
    rw [meromorphicOrderAt_congr (by simpa [φ, η, r] using
      cuspFunction_coxAction_eventuallyEq_aux m σ)]
    exact hcompOrder
  unfold UpperHalfPlane.poleOrder
  rw [horder]
  have hrpos : 0 < r := pow_pos σ.a_pos 2
  have hneg : (((-(r : ℤ) : ℤ) : WithTop ℤ) < 0) := by
    exact_mod_cast (show (-(r : ℤ) : ℤ) < 0 by omega)
  rw [if_pos hneg, WithTop.untopD_coe]
  simp [r]

private theorem poleRemoved_coxAction_aux (m : ℕ+) (σ : CoxMatrix m) :
    poleRemoved ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ)) =
      fun τ ↦ (coxPhaseAux m σ)⁻¹ * qj (σ.act τ) := by
  funext τ
  rw [UpperHalfPlane.poleRemoved, poleOrder_coxAction_aux]
  rw [show qj (σ.act τ) = Periodic.qParam 1 (σ.act τ) * j (σ.act τ) by
    simp [qj, Pi.mul_apply, Periodic.qParam]]
  rw [qParam_coxAction_aux]
  field_simp [coxPhase_ne_zero_aux m σ]

private theorem to_qExpansion_coxAction_aux (m : ℕ+) (σ : CoxMatrix m) :
    to_qExpansion ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ)) =
      (coxPhaseAux m σ)⁻¹ •
        (PowerSeries.rescale (coxPhaseAux m σ) (qExpansion 1 qj)).expand
          (σ.a ^ 2) (pow_ne_zero _ σ.a_pos.ne') := by
  let η := coxPhaseAux m σ
  let r := σ.a ^ 2
  let g := poleRemoved ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ))
  let P : PowerSeries ℂ :=
    η⁻¹ • (PowerSeries.rescale η (qExpansion 1 qj)).expand r
      (pow_ne_zero _ σ.a_pos.ne')
  have hrpos : 0 < r := pow_pos σ.a_pos 2
  have hgan : AnalyticAt ℂ (cuspFunction ((m : ℕ) : ℝ) g) 0 :=
    analyticAt_cuspFunction_poleRemoved
      (cuspFunction_coxAction_meromorphicAt_aux m σ)
  have hsum : ∀ τ : ℍ,
      HasSum (fun n ↦ P.coeff n • Periodic.qParam ((m : ℕ) : ℝ) τ ^ n) (g τ) := by
    intro τ
    let x := Periodic.qParam ((m : ℕ) : ℝ) τ
    have hbase := (hasSum_qExpansion_qj (τ := σ.act τ)).mul_left η⁻¹
    have hreindexed : HasSum
        ((fun n ↦ P.coeff n • x ^ n) ∘ fun n ↦ r * n) (g τ) := by
      rw [show g τ = η⁻¹ * qj (σ.act τ) by
        simpa [g, η] using congrFun (poleRemoved_coxAction_aux m σ) τ]
      apply hbase.congr_fun
      intro n
      simp only [Function.comp_apply, smul_eq_mul]
      rw [show P.coeff (r * n) = η⁻¹ * (η ^ n * (qExpansion 1 qj).coeff n) by
        simp [P, PowerSeries.coeff_expand_mul,
          PowerSeries.coeff_rescale]]
      rw [qParam_coxAction_aux]
      simp only [η, r, x, mul_pow, pow_mul]
      ring
    have hinj : Function.Injective (fun n ↦ r * n) := by
      intro i j hij
      exact Nat.mul_left_cancel hrpos hij
    apply (hinj.hasSum_iff ?_).mp hreindexed
    intro n hn
    have hnotdvd : ¬r ∣ n := by
      rintro ⟨k, rfl⟩
      exact hn ⟨k, rfl⟩
    simp [P, PowerSeries.coeff_expand, hnotdvd]
  apply PowerSeries.ext
  intro n
  change (qExpansion ((m : ℕ) : ℝ) g).coeff n = P.coeff n
  exact (qExpansion_coeff_unique g (by positivity) hgan hsum n).symm

private theorem inv_mul_pow_toNat_add_one_aux {η : ℂ} (hη : η ≠ 0) {t : ℤ}
    (ht : -1 ≤ t) :
    η⁻¹ * η ^ Int.toNat (t + 1) = η ^ t := by
  have hnonneg : 0 ≤ t + 1 := by omega
  rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg, ← zpow_neg_one]
  rw [← zpow_add₀ hη]
  congr 1
  omega

private theorem coxPhase_zpow_aux (m : ℕ+) (σ : CoxMatrix m) (t : ℤ) :
    coxPhaseAux m σ ^ t =
      zeta m ^ (((σ.a : ℤ) * (σ.b : ℤ)) * t) := by
  rw [coxPhaseAux, ← zpow_natCast, zpow_mul]
  norm_cast

private theorem laurentqExpansion_coxAction_coeff_aux
    (m : ℕ+) (σ : CoxMatrix m) (k : ℤ) :
    (laurentqExpansion ((m : ℕ) : ℝ) (fun τ ↦ j (σ.act τ))).coeff k =
      (transformedJSeries (zeta m) σ).coeff k := by
  rw [transformedJSeries_coeff]
  let r := σ.a ^ 2
  let η := coxPhaseAux m σ
  have hrpos : 0 < r := pow_pos σ.a_pos 2
  have hrzpos : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hrpos
  have hpole :
      poleOrder ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ)) = r := by
    simpa [r] using poleOrder_coxAction_aux m σ
  by_cases hklt : k < -(r : ℤ)
  · have hklt' :
        k < -(poleOrder ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ)) : ℤ) := by
      rw [hpole]
      exact hklt
    rw [laurentqExpansion.coeff_eq_zero_of_lt hklt']
    rw [if_neg]
    intro h
    have hge : -(r : ℤ) ≤ k := by simpa [r] using h.2
    omega
  · have hkge : -(r : ℤ) ≤ k := le_of_not_gt hklt
    have hkge' :
        -(poleOrder ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ)) : ℤ) ≤ k := by
      rw [hpole]
      exact hkge
    rw [laurentqExpansion.coeff_of_geq hkge']
    rw [hpole, to_qExpansion_coxAction_aux]
    by_cases hdiv : (r : ℤ) ∣ k
    · rw [if_pos (by simpa [r] using And.intro hdiv hkge)]
      let t := k / (r : ℤ)
      have hkeq : k = t * (r : ℤ) := (Int.ediv_mul_cancel hdiv).symm
      have ht : -1 ≤ t := by
        apply (Int.le_ediv_iff_mul_le hrzpos).2
        simpa [t] using hkge
      have htadd : 0 ≤ t + 1 := by omega
      have htoNat : Int.toNat (k + (r : ℤ)) = r * Int.toNat (t + 1) := by
        have heq : k + (r : ℤ) = (t + 1) * (r : ℤ) := by
          rw [hkeq]
          ring
        rw [heq, Int.toNat_mul htadd hrzpos.le]
        simp [mul_comm]
      have hjcoeff :
          (qExpansion 1 qj).coeff (Int.toNat (t + 1)) = (jIntCoeff t : ℂ) := by
        calc
          _ = (to_qExpansion 1 j).coeff (Int.toNat (t + 1)) := by
            rw [j_to_qExpansion]
          _ = (laurentqExpansion 1 j).coeff t := by
            symm
            have ht' : -(poleOrder 1 j : ℤ) ≤ t := by
              simpa [j_poleOrder] using ht
            simpa [j_poleOrder] using
              (laurentqExpansion.coeff_of_geq (h := 1) (f := j) (n := t) ht')
          _ = _ := jIntCoeff_spec t
      change
        (η⁻¹ • (PowerSeries.rescale η (qExpansion 1 qj)).expand r
          (pow_ne_zero _ σ.a_pos.ne')).coeff (Int.toNat (k + (r : ℤ))) = _
      rw [htoNat]
      calc
        _ = η⁻¹ *
            (η ^ Int.toNat (t + 1) *
              (qExpansion 1 qj).coeff (Int.toNat (t + 1))) := by
          simp [PowerSeries.coeff_expand_mul, PowerSeries.coeff_rescale]
        _ = (jIntCoeff t : ℂ) * η ^ t := by
          rw [hjcoeff]
          rw [← inv_mul_pow_toNat_add_one_aux (coxPhase_ne_zero_aux m σ) ht]
          ring
        _ = (jIntCoeff (k / (σ.a : ℤ) ^ 2) : ℂ) *
            zeta m ^ (((σ.a : ℤ) * (σ.b : ℤ)) * (k / (σ.a : ℤ) ^ 2)) := by
          rw [coxPhase_zpow_aux]
          simp [t, r]
    · rw [if_neg]
      · have hnonneg : 0 ≤ k + (r : ℤ) := by omega
        have hnotdvd : ¬r ∣ Int.toNat (k + (r : ℤ)) := by
          intro hd
          rcases hd with ⟨n, hn⟩
          apply hdiv
          refine ⟨(n : ℤ) - 1, ?_⟩
          have hcast := congrArg (fun x : ℕ ↦ (x : ℤ)) hn
          change (Int.toNat (k + (r : ℤ)) : ℤ) = (r * n : ℕ) at hcast
          rw [Int.toNat_of_nonneg hnonneg] at hcast
          push_cast at hcast
          linear_combination hcast
        change
          ((coxPhaseAux m σ)⁻¹ •
            (PowerSeries.rescale (coxPhaseAux m σ) (qExpansion 1 qj)).expand r
              (pow_ne_zero _ σ.a_pos.ne')).coeff (Int.toNat (k + (r : ℤ))) = 0
        simp [PowerSeries.coeff_expand, hnotdvd]
      · intro h
        apply hdiv
        simpa [r] using h.1

/-- The exact analytic/formal bridge for (11.13).  The width is `m`, not `1`: its local
parameter is `q^(1/m)`. -/
theorem laurentqExpansion_coxAction (m : ℕ+) (σ : CoxMatrix m) :
    laurentqExpansion ((m : ℕ) : ℝ) (fun τ ↦ j (σ.act τ)) =
      transformedJSeries (zeta m) σ := by
  ext k
  exact laurentqExpansion_coxAction_coeff_aux m σ k

/-- Galois reindexing `b ↦ bk (mod d)` from the proof of Theorem 11.18(i). -/
def reindex {m : ℕ+} (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) :
    CoxMatrix m → CoxMatrix m := fun σ ↦ by
  have hdvd : σ.d ∣ (m : ℕ) :=
    ⟨σ.a, by rw [Nat.mul_comm, σ.determinant]⟩
  have hkd : Nat.Coprime k σ.d := hk.coprime_dvd_right hdvd
  refine
    { a := σ.a
      b := (σ.b * k) % σ.d
      d := σ.d
      a_pos := σ.a_pos
      determinant := σ.determinant
      b_lt := Nat.mod_lt _ σ.d_pos
      primitive := ?_ }
  calc
    Nat.gcd (Nat.gcd σ.a ((σ.b * k) % σ.d)) σ.d =
        Nat.gcd σ.a (Nat.gcd ((σ.b * k) % σ.d) σ.d) := by
      ac_rfl
    _ = Nat.gcd σ.a (Nat.gcd (σ.b * k) σ.d) := by
      congr 1
      calc
        Nat.gcd ((σ.b * k) % σ.d) σ.d = Nat.gcd σ.d (σ.b * k) :=
          (Nat.gcd_rec σ.d (σ.b * k)).symm
        _ = Nat.gcd (σ.b * k) σ.d := Nat.gcd_comm _ _
    _ = Nat.gcd σ.a (Nat.gcd σ.b σ.d) := by
      rw [hkd.gcd_mul_right_cancel]
    _ = Nat.gcd (Nat.gcd σ.a σ.b) σ.d := by
      ac_rfl
    _ = 1 := σ.primitive

theorem reindex_bijective {m : ℕ+} (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) :
    Function.Bijective (reindex k hk) := by
  have hinj : Function.Injective (reindex k hk) := by
    intro σ τ h
    have ha : σ.a = τ.a := by
      simpa only [reindex] using congrArg (fun ρ ↦ ρ.a) h
    have hd : σ.d = τ.d := by
      simpa only [reindex] using congrArg (fun ρ ↦ ρ.d) h
    have hbmod : (σ.b * k) % σ.d = (τ.b * k) % σ.d := by
      have hb := congrArg (fun ρ ↦ ρ.b) h
      simpa only [reindex, hd] using hb
    have hdvd : σ.d ∣ (m : ℕ) :=
      ⟨σ.a, by rw [Nat.mul_comm, σ.determinant]⟩
    have hkd : Nat.gcd σ.d k = 1 :=
      (hk.coprime_dvd_right hdvd).symm.gcd_eq_one
    have hmul : σ.b * k ≡ τ.b * k [MOD σ.d] := hbmod
    have hbCongr : σ.b ≡ τ.b [MOD σ.d] :=
      hmul.cancel_right_of_coprime hkd
    have hb : σ.b = τ.b := by
      apply hbCongr.eq_of_lt_of_lt σ.b_lt
      simpa only [hd] using τ.b_lt
    apply CoxMatrix.toFin_injective
    apply Prod.ext
    · apply Fin.ext
      exact ha
    · apply Prod.ext
      · apply Fin.ext
        exact hb
      · apply Fin.ext
        exact hd
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

end Cox

