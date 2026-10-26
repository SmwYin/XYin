/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import XYin.PhD.Cox.CoxMatrices.Basic
import XYin.PhD.Cox.LaurentSeriesAux
import XYin.PhD.LaurentQExpansion.Algebra

/-!
# Laurent expansions of the Cox roots

This file constructs the formal Laurent series of `j` in the width-`m` local parameter and the
transformed Laurent series from equation (11.13), identifies them with the analytic expansions of
`j` and of each Cox root, and defines the Galois reindexing of `C(m)`.

## Main definitions and results

* `jIntCoeff`: the integral Laurent coefficients of `j`.
* `jLaurentSeriesWidth R m`: the Laurent series of `j` in the parameter `q^(1/m)`, over any ring
  `R`; `jLaurentSeriesWidth_complex` identifies it over `ℂ` with `laurentqExpansion m j`.
* `transformedJSeries ζ σ`: the Laurent series (11.13) of the Cox root indexed by `σ`;
  `laurentqExpansion_coxAction` identifies it with the analytic expansion of `j ∘ σ`, and
  `transformedJSeries_injective` shows that distinct `σ` give distinct series.
* `reindex`: the Galois reindexing `b ↦ bk (mod d)` of `C(m)`.
-/

open Complex Function MatrixGroups UpperHalfPlane

noncomputable section

namespace Cox

/-- The primitive `m`-th root used in equation (11.13). -/
def zeta (m : ℕ+) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))

theorem zeta_isPrimitiveRoot (m : ℕ+) : IsPrimitiveRoot (zeta m) (m : ℕ) := by
  simpa only [zeta] using
    Complex.isPrimitiveRoot_exp (m : ℕ) (PNat.ne_zero m)

theorem zeta_ne_zero (m : ℕ+) : zeta m ≠ 0 :=
  (zeta_isPrimitiveRoot m).ne_zero m.ne_zero

/-- The integral Laurent coefficients `c(n)` of the analytic `j`-function
(`j = ∑ₙ c(n) qⁿ`, see `jIntCoeff_spec`): they vanish below the simple pole at `-1`, and from
there on they are the coefficients `qjCoeffs` of `q · j`, shifted by one. -/
def jIntCoeff (n : ℤ) : ℤ :=
  if n < -1 then 0 else qjCoeffs (n + 1).toNat

/-- `jIntCoeff n` is the `n`-th Laurent `q`-expansion coefficient of `j`. -/
theorem jIntCoeff_spec (n : ℤ) :
    (laurentqExpansion 1 j).coeff n = (jIntCoeff n : ℂ) :=
  j_laurentQExpansion_coeff n

/-- The residue of `j` at its simple pole: `c(-1) = 1`. -/
theorem jIntCoeff_neg_one : jIntCoeff (-1) = 1 := by
  simp [jIntCoeff, qjCoeffs_zero]

/-- The integral Laurent coefficients of `j` vanish below its simple pole. -/
theorem jIntCoeff_eq_zero_of_lt {n : ℤ} (hn : n < -(1 : ℤ)) : jIntCoeff n = 0 :=
  if_pos hn

/-- The Laurent coefficient `c(n - 1)` of `j` is the `n`-th coefficient of `q · j`. -/
theorem jIntCoeff_sub_one (n : ℕ) : jIntCoeff ((n : ℤ) - 1) = qjCoeffs n := by
  rw [jIntCoeff, if_neg (by omega), sub_add_cancel, Int.toNat_natCast]

/-! ### The Laurent series of `j` in the width-`m` local parameter -/

/-- The power series `∑ₙ c(n - 1) qⁿ` of `q · j`, where `j = ∑ₙ c(n) qⁿ`, with coefficients in an
arbitrary ring. -/
def jUnitPowerSeries (R : Type*) [Ring R] : PowerSeries R :=
  PowerSeries.mk fun n ↦ (jIntCoeff ((n : ℤ) - 1) : R)

@[simp]
theorem coeff_jUnitPowerSeries (R : Type*) [Ring R] (n : ℕ) :
    PowerSeries.coeff n (jUnitPowerSeries R) = (jIntCoeff ((n : ℤ) - 1) : R) :=
  PowerSeries.coeff_mk _ _

/-- The Laurent expansion of `j` in the width-`m` local parameter `t = q^(1/m)`, with
coefficients in an arbitrary ring: the coefficient of `tᵏ` is `c(k/m)` when `m ∣ k` and
`-m ≤ k`, and zero otherwise, where `j = ∑ₙ c(n) qⁿ`. -/
def jLaurentSeriesWidth (R : Type*) [Ring R] (m : ℕ+) : LaurentSeries R :=
  HahnSeries.ofSuppBddBelow
    (fun k ↦ if (m : ℤ) ∣ k ∧ -(m : ℤ) ≤ k then (jIntCoeff (k / m) : R) else 0)
    ⟨-(m : ℤ), fun _ hk ↦ by_contra fun h ↦ hk (if_neg fun h' ↦ h h'.2)⟩

theorem jLaurentSeriesWidth_coeff (R : Type*) [Ring R] (m : ℕ+) (k : ℤ) :
    (jLaurentSeriesWidth R m).coeff k =
      if (m : ℤ) ∣ k ∧ -(m : ℤ) ≤ k then (jIntCoeff (k / m) : R) else 0 :=
  rfl

@[simp]
theorem jLaurentSeriesWidth_coeff_mul (R : Type*) [Ring R] (m : ℕ+) (q : ℤ) :
    (jLaurentSeriesWidth R m).coeff ((m : ℤ) * q) = (jIntCoeff q : R) := by
  have hm : (0 : ℤ) < m := by positivity
  rw [jLaurentSeriesWidth_coeff, Int.mul_ediv_cancel_left _ hm.ne']
  split_ifs with h
  · rfl
  · rw [jIntCoeff_eq_zero_of_lt, Int.cast_zero]
    by_contra hq
    exact h ⟨dvd_mul_right _ _, by nlinarith⟩

theorem jLaurentSeriesWidth_coeff_of_not_dvd (R : Type*) [Ring R] (m : ℕ+) {k : ℤ}
    (hk : ¬(m : ℤ) ∣ k) : (jLaurentSeriesWidth R m).coeff k = 0 :=
  if_neg fun h ↦ hk h.1

@[simp]
theorem jLaurentSeriesWidth_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (m : ℕ+) :
    (jLaurentSeriesWidth R m).map f = jLaurentSeriesWidth S m := by
  ext k
  simp only [HahnSeries.map_coeff, jLaurentSeriesWidth_coeff]
  split_ifs <;> simp

theorem jLaurentSeriesWidth_order (R : Type*) [Ring R] [Nontrivial R] (m : ℕ+) :
    (jLaurentSeriesWidth R m).order = -(m : ℤ) := by
  refine HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt ?_
    fun k hk ↦ if_neg fun h ↦ (not_le.2 hk) h.2
  rw [← mul_neg_one, jLaurentSeriesWidth_coeff_mul, jIntCoeff_neg_one, Int.cast_one]
  exact one_ne_zero

theorem jLaurentSeriesWidth_leadingCoeff (R : Type*) [Ring R] [Nontrivial R] (m : ℕ+) :
    (jLaurentSeriesWidth R m).leadingCoeff = 1 := by
  rw [HahnSeries.leadingCoeff_eq, jLaurentSeriesWidth_order, ← mul_neg_one,
    jLaurentSeriesWidth_coeff_mul, jIntCoeff_neg_one, Int.cast_one]

/-- The width-`m` series of `j` is `t⁻ᵐ · (q j)(tᵐ)`. -/
theorem jLaurentSeriesWidth_eq_single_mul_expand (R : Type*) [CommRing R] (m : ℕ+) :
    jLaurentSeriesWidth R m = HahnSeries.single (-(m : ℤ)) 1 *
      ((jUnitPowerSeries R).expand m m.ne_zero : LaurentSeries R) := by
  ext k
  rw [LaurentSeries.coeff_single_neg_mul_coe_expand, jLaurentSeriesWidth_coeff]
  split_ifs with h
  · obtain ⟨⟨t, rfl⟩, ht⟩ := h
    have hm : (0 : ℤ) < m := by positivity
    rw [coeff_jUnitPowerSeries, Int.mul_ediv_cancel_left _ hm.ne',
      Int.toNat_of_nonneg (by nlinarith), add_sub_cancel_right]
  · rfl

/-- Over `ℂ`, the width-`m` series of `j` is the analytic Laurent expansion of `j` at the
width-`m` cusp. -/
theorem jLaurentSeriesWidth_complex (m : ℕ+) :
    jLaurentSeriesWidth ℂ m = laurentqExpansion ((m : ℕ) : ℝ) j := by
  have h := laurentqExpansion_nat_mul (h := 1) m.ne_zero j_cuspFunction_meromorphicAt
    ModularFunction.j_periodic
  rw [mul_one] at h
  ext k
  rw [h]
  rcases em ((m : ℤ) ∣ k) with ⟨q, rfl⟩ | hk
  · rw [jLaurentSeriesWidth_coeff_mul, ← natMulOrderEmbedding_apply _ m.ne_zero,
      HahnSeries.embDomain_coeff, jIntCoeff_spec]
  · rw [jLaurentSeriesWidth_coeff_of_not_dvd _ _ hk,
      HahnSeries.embDomain_notin_range fun ⟨q, hq⟩ ↦ hk ⟨q, hq.symm⟩]

/-- The integral width-`m` series recovers the analytic Laurent expansion over `ℂ`. -/
theorem jLaurentSeriesWidth_map_complex (m : ℕ+) :
    (jLaurentSeriesWidth ℤ m).map (Int.castRingHom ℂ) = laurentqExpansion ((m : ℕ) : ℝ) j := by
  rw [jLaurentSeriesWidth_map, jLaurentSeriesWidth_complex]

/-- In the local parameter `q^(1/m)`, the analytic `j`-function has order `-m`. -/
theorem laurentqExpansion_j_order_widthM (m : ℕ+) :
    (laurentqExpansion ((m : ℕ) : ℝ) j).order = -(m : ℤ) := by
  rw [← jLaurentSeriesWidth_complex, jLaurentSeriesWidth_order]

/-- The leading coefficient of `j` remains one in the width-`m` local parameter. -/
theorem laurentqExpansion_j_leadingCoeff_widthM (m : ℕ+) :
    (laurentqExpansion ((m : ℕ) : ℝ) j).leadingCoeff = 1 := by
  rw [← jLaurentSeriesWidth_complex, jLaurentSeriesWidth_leadingCoeff]

/-! ### The transformed series of equation (11.13) -/

/-- Equation (11.13) as a formal Laurent series in `t=q^(1/m)`. -/
noncomputable def transformedJSeries {K : Type*} [Field K] {m : ℕ+}
    (ζ : K) (σ : CoxMatrix m) : LaurentSeries K :=
  HahnSeries.ofSuppBddBelow
    (fun k ↦ if (σ.a : ℤ) ^ 2 ∣ k ∧ -((σ.a : ℤ) ^ 2) ≤ k
      then (jIntCoeff (k / (σ.a : ℤ) ^ 2) : K) *
        ζ ^ (((σ.a : ℤ) * (σ.b : ℤ)) * (k / (σ.a : ℤ) ^ 2))
      else 0)
    ⟨-((σ.a : ℤ) ^ 2), fun _ hk ↦ by_contra fun h ↦ hk (if_neg fun h' ↦ h h'.2)⟩

theorem transformedJSeries_coeff {K : Type*} [Field K] {m : ℕ+}
    (ζ : K) (σ : CoxMatrix m) (k : ℤ) :
    (transformedJSeries ζ σ).coeff k =
      if (σ.a : ℤ) ^ 2 ∣ k ∧ -((σ.a : ℤ) ^ 2) ≤ k
      then (jIntCoeff (k / (σ.a : ℤ) ^ 2) : K) *
        ζ ^ (((σ.a : ℤ) * (σ.b : ℤ)) * (k / (σ.a : ℤ) ^ 2))
      else 0 := rfl

/-- When the phase `ζ ^ (ab)` is trivial (for instance `ζ = 1`, or `b = 0`), the transformed
series is the width-`a²` Laurent series of `j`. -/
theorem transformedJSeries_eq_jLaurentSeriesWidth {K : Type*} [Field K] {m : ℕ+} (ζ : K)
    (σ : CoxMatrix m) (hζ : ζ ^ ((σ.a : ℤ) * σ.b) = 1) :
    transformedJSeries ζ σ = jLaurentSeriesWidth K ⟨σ.a ^ 2, pow_pos σ.a_pos 2⟩ := by
  let w : ℕ+ := ⟨σ.a ^ 2, pow_pos σ.a_pos 2⟩
  change transformedJSeries ζ σ = jLaurentSeriesWidth K w
  ext k
  rw [transformedJSeries_coeff, jLaurentSeriesWidth_coeff]
  simp only [w, PNat.mk_coe, Nat.cast_pow,
    zpow_mul, hζ, one_zpow, mul_one]

/-- The coefficient of a transformed series at its principal exponent `-a²` is its phase. -/
theorem transformedJSeries_coeff_neg_sq {K : Type*} [Field K] {m : ℕ+} (ζ : K)
    (σ : CoxMatrix m) :
    (transformedJSeries ζ σ).coeff (-((σ.a : ℤ) ^ 2)) = ζ ^ (-((σ.a : ℤ) * (σ.b : ℤ))) := by
  have ha : (σ.a : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast σ.a_pos.ne')
  simp [transformedJSeries_coeff, ha, jIntCoeff_neg_one]

/-- A transformed `j`-series with nonzero phase has order `-σ.a ^ 2`. -/
theorem transformedJSeries_order {K : Type*} [Field K] {m : ℕ+} (ζ : K) (hζ : ζ ≠ 0)
    (σ : CoxMatrix m) : (transformedJSeries ζ σ).order = -((σ.a : ℤ) ^ 2) :=
  HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt
    (by rw [transformedJSeries_coeff_neg_sq]; exact zpow_ne_zero _ hζ)
    fun _ hk ↦ if_neg fun h ↦ (not_le.2 hk) h.2

/-- The leading coefficient of a transformed root series is its phase from Cox (11.13). -/
theorem transformedJSeries_leadingCoeff {K : Type*} [Field K] {m : ℕ+} (ζ : K) (hζ : ζ ≠ 0)
    (σ : CoxMatrix m) :
    (transformedJSeries ζ σ).leadingCoeff = ζ ^ (-((σ.a : ℤ) * (σ.b : ℤ))) := by
  rw [HahnSeries.leadingCoeff_eq, transformedJSeries_order ζ hζ, transformedJSeries_coeff_neg_sq]

/-- Distinct Cox matrices give distinct transformed series (11.13): the order `-a²` recovers `a`
(hence `d = m / a`), and the phase `ζ_m ^ (-ab)` recovers `b` modulo `d`. -/
theorem transformedJSeries_injective (m : ℕ+) :
    Function.Injective (transformedJSeries (zeta m) : CoxMatrix m → LaurentSeries ℂ) := by
  intro σ τ h
  have hζ := zeta_ne_zero m
  have ha : σ.a = τ.a := by
    have ho := congrArg HahnSeries.order h
    rw [transformedJSeries_order _ hζ, transformedJSeries_order _ hζ, neg_inj] at ho
    have ho' : σ.a ^ 2 = τ.a ^ 2 := by exact_mod_cast ho
    exact Nat.pow_left_injective two_ne_zero ho'
  have hd : σ.d = τ.d :=
    Nat.eq_of_mul_eq_mul_left σ.a_pos (by rw [σ.determinant, ha, τ.determinant])
  have hphase := congrArg HahnSeries.leadingCoeff h
  rw [transformedJSeries_leadingCoeff _ hζ, transformedJSeries_leadingCoeff _ hζ, ← ha,
    ← div_eq_one_iff_eq (zpow_ne_zero _ hζ), ← zpow_sub₀ hζ,
    (zeta_isPrimitiveRoot m).zpow_eq_one_iff_dvd,
    show ((m : ℕ) : ℤ) = σ.a * σ.d by exact_mod_cast σ.determinant.symm,
    show -((σ.a : ℤ) * σ.b) - -((σ.a : ℤ) * τ.b) = σ.a * (τ.b - σ.b) by ring,
    mul_dvd_mul_iff_left (by exact_mod_cast σ.a_pos.ne')] at hphase
  exact CoxMatrix.ext ha ((Nat.modEq_iff_dvd.2 hphase).eq_of_lt_of_lt σ.b_lt (hd ▸ τ.b_lt)) hd

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
    rw [cuspFunction_apply_of_ne_zero _ _ hq0, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hqparam : Periodic.qParam 1 w = coxPhaseAux m σ * q ^ (σ.a ^ 2) := by
    rw [show w = σ.act τ from rfl, qParam_coxAction_aux]
    rw [show Periodic.qParam ((m : ℕ) : ℝ) τ = q by
      simpa [τ] using Periodic.qParam_right_inv
        (show (((m : ℕ) : ℝ)) ≠ 0 by positivity) hq0]
  rw [hleft, ← hqparam]
  exact (UpperHalfPlane.eq_cuspFunction w one_ne_zero hfper).symm

private theorem coxPhase_ne_zero_aux (m : ℕ+) (σ : CoxMatrix m) :
    coxPhaseAux m σ ≠ 0 :=
  pow_ne_zero _ (Complex.exp_ne_zero _)

private theorem cuspFunction_coxAction_eventuallyEq_aux (m : ℕ+) (σ : CoxMatrix m) :
    cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ)) =ᶠ[nhdsWithin 0 ({0}ᶜ)]
      cuspFunction 1 j ∘ fun q ↦ coxPhaseAux m σ * q ^ (σ.a ^ 2) := by
  filter_upwards [eventually_ne_zero_and_norm_lt_one] with q hq
  exact cuspFunction_coxCompose_aux m σ j ModularFunction.j_periodic hq.1 hq.2

private theorem cuspFunction_coxAction_meromorphicAt_aux (m : ℕ+) (σ : CoxMatrix m) :
    MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ))) 0 := by
  have hbase : MeromorphicAt (cuspFunction 1 j)
      (coxPhaseAux m σ * (0 : ℂ) ^ (σ.a ^ 2)) := by
    simpa [σ.a_pos.ne'] using j_cuspFunction_meromorphicAt
  exact (MeromorphicAt.comp_analyticAt
    (g := fun q : ℂ ↦ coxPhaseAux m σ * q ^ (σ.a ^ 2)) hbase (by fun_prop)).congr
    (cuspFunction_coxAction_eventuallyEq_aux m σ).symm

private theorem poleOrder_coxAction_aux (m : ℕ+) (σ : CoxMatrix m) :
    poleOrder ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ)) = σ.a ^ 2 := by
  refine poleOrder_eq_of_meromorphicOrderAt_eq ?_
  rw [meromorphicOrderAt_congr (cuspFunction_coxAction_eventuallyEq_aux m σ),
    meromorphicOrderAt_comp_const_mul_pow j_cuspFunction_meromorphicAt
      (coxPhase_ne_zero_aux m σ) (pow_ne_zero 2 σ.a_pos.ne'),
    meromorphicOrderAt_cuspFunction_eq_neg_poleOrder (by simp [j_poleOrder]), j_poleOrder]
  change ((-((1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) * (((σ.a ^ 2 : ℕ) : ℤ) : WithTop ℤ) = _
  norm_cast
  simp

private theorem poleRemoved_coxAction_aux (m : ℕ+) (σ : CoxMatrix m) :
    poleRemoved ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ)) =
      fun τ ↦ (coxPhaseAux m σ)⁻¹ * qj (σ.act τ) := by
  funext τ
  rw [poleRemoved_apply, poleOrder_coxAction_aux, qj_apply, qParam_coxAction_aux]
  field_simp [coxPhase_ne_zero_aux m σ]

private theorem toQExpansion_coxAction_aux (m : ℕ+) (σ : CoxMatrix m) :
    toQExpansion ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ)) =
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
  -- `qExpansion_coeff_unique` is stated for `FunLike` types; view `g` as one.
  letI : FunLike (ℍ → ℂ) ℍ ℂ := { coe := id, coe_injective := fun _ _ h ↦ h }
  ext n
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
  let r := σ.a ^ 2
  let η := coxPhaseAux m σ
  have hrpos : (0 : ℤ) < r := by exact_mod_cast pow_pos σ.a_pos 2
  have hpole : poleOrder ((m : ℕ) : ℝ) (fun τ ↦ j (σ.act τ)) = r :=
    poleOrder_coxAction_aux m σ
  rw [transformedJSeries_coeff, laurentqExpansion.coeff_of_qExpansion, hpole]
  simp only [← Nat.cast_pow]
  change (if k < -(r : ℤ) then 0 else _) =
    if (r : ℤ) ∣ k ∧ -(r : ℤ) ≤ k then
      (jIntCoeff (k / (r : ℤ)) : ℂ) *
        zeta m ^ (((σ.a : ℤ) * (σ.b : ℤ)) * (k / (r : ℤ))) else 0
  by_cases hk : k < -(r : ℤ)
  · simp [hk, not_le_of_gt hk]
  rw [if_neg hk, toQExpansion_coxAction_aux]
  have hkge : 0 ≤ k + (r : ℤ) := by lia
  by_cases hdiv : (r : ℤ) ∣ k
  · obtain ⟨t, rfl⟩ := hdiv
    have ht : -1 ≤ t := by nlinarith
    have hindex : Int.toNat ((r : ℤ) * t + r) = r * Int.toNat (t + 1) := by
      rw [show (r : ℤ) * t + r = r * (t + 1) by ring,
        Int.toNat_mul hrpos.le (by lia)]
      simp
    have hjcoeff : (qExpansion 1 qj).coeff (Int.toNat (t + 1)) = (jIntCoeff t : ℂ) :=
      (j_laurentQExpansion_coeff_of_neg_one_le ht).symm.trans (jIntCoeff_spec t)
    simp only [Int.mul_ediv_cancel_left _ hrpos.ne', dvd_mul_right,
      le_of_not_gt hk, and_self, if_true]
    change (η⁻¹ • (PowerSeries.rescale η (qExpansion 1 qj)).expand r
      (pow_ne_zero _ σ.a_pos.ne')).coeff (Int.toNat ((r : ℤ) * t + r)) = _
    rw [hindex]
    simp only [PowerSeries.coeff_smul, PowerSeries.coeff_expand_mul,
      PowerSeries.coeff_rescale, smul_eq_mul, hjcoeff]
    rw [← mul_assoc, inv_mul_pow_toNat_add_one_aux (coxPhase_ne_zero_aux m σ) ht,
      mul_comm, coxPhase_zpow_aux]
  · have hnotdvd : ¬r ∣ Int.toNat (k + (r : ℤ)) := by
      simpa only [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg hkge,
        dvd_add_self_right] using hdiv
    change ¬σ.a ^ 2 ∣ Int.toNat (k + (r : ℤ)) at hnotdvd
    simp [hdiv, PowerSeries.coeff_expand, hnotdvd]

/-- The exact analytic/formal bridge for (11.13).  The width is `m`, not `1`: its local
parameter is `q^(1/m)`. -/
theorem laurentqExpansion_coxAction (m : ℕ+) (σ : CoxMatrix m) :
    laurentqExpansion ((m : ℕ) : ℝ) (fun τ ↦ j (σ.act τ)) =
      transformedJSeries (zeta m) σ := by
  ext k
  exact laurentqExpansion_coxAction_coeff_aux m σ k

/-- Galois reindexing `b ↦ bk (mod d)` from the proof of Theorem 11.18(i). -/
def reindex {m : ℕ+} (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) (σ : CoxMatrix m) : CoxMatrix m where
  a := σ.a
  b := (σ.b * k) % σ.d
  d := σ.d
  a_pos := σ.a_pos
  determinant := σ.determinant
  b_lt := Nat.mod_lt _ σ.d_pos
  primitive := by
    rw [Nat.gcd_assoc, ← Nat.gcd_rec, Nat.gcd_comm σ.d,
      (hk.coprime_dvd_right σ.d_dvd).gcd_mul_right_cancel, ← Nat.gcd_assoc]
    exact σ.primitive

section reindex

variable {m : ℕ+} (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) (σ : CoxMatrix m)

@[simp] theorem reindex_a : (reindex k hk σ).a = σ.a := rfl

@[simp] theorem reindex_b : (reindex k hk σ).b = σ.b * k % σ.d := rfl

@[simp] theorem reindex_d : (reindex k hk σ).d = σ.d := rfl

end reindex

theorem reindex_bijective {m : ℕ+} (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) :
    Function.Bijective (reindex k hk) := by
  have hinj : Function.Injective (reindex k hk) := fun σ τ h ↦ by
    have hd : σ.d = τ.d := (congrArg CoxMatrix.d h :)
    have hb : σ.b * k ≡ τ.b * k [MOD σ.d] := by
      simpa [Nat.ModEq, hd] using congrArg CoxMatrix.b h
    exact CoxMatrix.ext (congrArg CoxMatrix.a h :)
      ((hb.cancel_right_of_coprime (hk.coprime_dvd_right σ.d_dvd).symm).eq_of_lt_of_lt
        σ.b_lt (hd ▸ τ.b_lt)) hd
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

end Cox
