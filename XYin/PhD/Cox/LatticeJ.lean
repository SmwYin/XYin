/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.NormTrace

import XYin.PhD.Modularforms.ForMathlib_Cusps
import XYin.PhD.jFunction.jfunction
import XYin.uniqueness

/-!
# The analytic and lattice `j`-invariants

This file proves Cox Theorems 10.9 and 11.2 by relating the analytic `j`-function to lattice
invariants, classifying equal lattice invariants up to homothety, and identifying normalized
homothety classes with `SL₂(ℤ)`-orbits.
-/

open Complex EisensteinSeries Filter Function MatrixGroups ModularForm ModularFormClass
  PowerSeries Real SlashInvariantFormClass UpperHalfPlane
open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped CongruenceSubgroup Manifold

local notation "𝕢" => Periodic.qParam

noncomputable section

namespace PeriodPair

/-- Scale both periods by a nonzero complex number. -/
protected def smul (a : ℂˣ) (L : PeriodPair) : PeriodPair where
  ω₁ := a * L.ω₁
  ω₂ := a * L.ω₂
  indep := by
    refine LinearIndependent.pair_iff.mpr fun s t hst =>
      LinearIndependent.pair_iff.mp L.indep s t ?_
    have h : (a : ℂ) * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [mul_add, mul_smul_comm, mul_smul_comm]
      exact hst
    exact (mul_eq_zero.mp h).resolve_left a.ne_zero

instance : SMul ℂˣ PeriodPair := ⟨PeriodPair.smul⟩

@[simp] theorem smul_ω₁ (a : ℂˣ) (L : PeriodPair) : (a • L).ω₁ = a * L.ω₁ := rfl

@[simp] theorem smul_ω₂ (a : ℂˣ) (L : PeriodPair) : (a • L).ω₂ = a * L.ω₂ := rfl

/-- Two period pairs are homothetic when one period lattice becomes the other after a
nonzero complex scaling. -/
def Homothetic (L M : PeriodPair) : Prop :=
  ∃ a : ℂˣ, (a • L).lattice = M.lattice

/-- Cox's lattice discriminant `g₂³ - 27 g₃²`. -/
def discriminant (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

/-- Cox's lattice invariant `1728 g₂³ / Δ`. -/
def j (L : PeriodPair) : ℂ := 1728 * L.g₂ ^ 3 / L.discriminant

/-- Scaling carries the period lattice to its scalar multiple. -/
theorem mem_smul_lattice (L : PeriodPair) {a : ℂˣ} {x : ℂ} :
    x ∈ (a • L).lattice ↔ ∃ y ∈ L.lattice, x = (a : ℂ) * y := by
  simp only [mem_lattice, smul_ω₁, smul_ω₂]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨(m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂, ⟨m, n, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by ring⟩

/-- Multiplication by a unit maps a period lattice onto the scaled period lattice. -/
theorem map_lattice_mulLeftLinearEquiv (a : ℂˣ) (L : PeriodPair) :
    L.lattice.map (a.mulLeftLinearEquiv ℤ ℂ : ℂ →ₗ[ℤ] ℂ) =
      (a • L).lattice := by
  ext x
  rw [Submodule.mem_map, L.mem_smul_lattice]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

/-- Scaling by a unit, restricted to the corresponding period lattices. -/
def smulLatticeEquiv (a : ℂˣ) (L : PeriodPair) :
    L.lattice ≃ₗ[ℤ] (a • L).lattice :=
  (a.mulLeftLinearEquiv ℤ ℂ).ofSubmodules L.lattice (a • L).lattice
    (map_lattice_mulLeftLinearEquiv a L)

@[simp]
theorem coe_smulLatticeEquiv_apply (a : ℂˣ) (L : PeriodPair) (x : L.lattice) :
    ((smulLatticeEquiv a L x : (a • L).lattice) : ℂ) = (a : ℂ) * x :=
  rfl

@[simp]
theorem coe_smulLatticeEquiv_symm_apply
    (a : ℂˣ) (L : PeriodPair) (x : (a • L).lattice) :
    (((smulLatticeEquiv a L).symm x : L.lattice) : ℂ) =
      (a : ℂ)⁻¹ * x := by
  rw [smulLatticeEquiv, LinearEquiv.ofSubmodules_symm_apply]
  simpa using Units.symm_mulLeftLinearEquiv_apply ℤ a (x : ℂ)

/-- Eisenstein sums have weight `n` under scaling. -/
theorem G_smul (L : PeriodPair) (a : ℂˣ) (n : ℕ) :
    (a • L).G n = ((a : ℂ) ^ n)⁻¹ * L.G n := by
  let e : L.lattice ≃ (a • L).lattice :=
    { toFun := fun l ↦ ⟨a * l, L.mem_smul_lattice.mpr ⟨l, l.2, rfl⟩⟩
      invFun := fun l' ↦ ⟨(a : ℂ)⁻¹ * l', by
        obtain ⟨y, hy, hxy⟩ := L.mem_smul_lattice.mp l'.2
        rw [hxy, inv_mul_cancel_left₀ a.ne_zero]
        exact hy⟩
      left_inv := fun l ↦ Subtype.ext (inv_mul_cancel_left₀ a.ne_zero (l : ℂ))
      right_inv := fun l' ↦ Subtype.ext (mul_inv_cancel_left₀ a.ne_zero (l' : ℂ)) }
  simp only [G]
  rw [← e.tsum_eq, ← tsum_mul_left]
  exact tsum_congr fun l ↦ by
    change (((a : ℂ) * (l : ℂ)) ^ n)⁻¹ = ((a : ℂ) ^ n)⁻¹ * ((l : ℂ) ^ n)⁻¹
    rw [mul_pow, mul_inv]

/-- The invariant `g₂` has weight four under scaling. -/
theorem g₂_smul (L : PeriodPair) (a : ℂˣ) :
    (a • L).g₂ = ((a : ℂ) ^ 4)⁻¹ * L.g₂ := by
  simp only [g₂, G_smul]
  ring

/-- The invariant `g₃` has weight six under scaling. -/
theorem g₃_smul (L : PeriodPair) (a : ℂˣ) :
    (a • L).g₃ = ((a : ℂ) ^ 6)⁻¹ * L.g₃ := by
  simp only [g₃, G_smul]
  ring

/-- The lattice discriminant has weight twelve under scaling. -/
theorem discriminant_smul (L : PeriodPair) (a : ℂˣ) :
    (a • L).discriminant = ((a : ℂ) ^ 12)⁻¹ * L.discriminant := by
  simp only [discriminant, g₂_smul, g₃_smul]
  ring

/-- The lattice `j`-invariant is homothety-invariant. -/
theorem j_smul (L : PeriodPair) (a : ℂˣ) : (a • L).j = L.j := by
  have ha : ((a : ℂ) ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ a.ne_zero)
  simp only [j, g₂_smul, discriminant_smul]
  rw [show 1728 * (((a : ℂ) ^ 4)⁻¹ * L.g₂) ^ 3
        = ((a : ℂ) ^ 12)⁻¹ * (1728 * L.g₂ ^ 3) by ring,
    mul_div_mul_left _ _ ha]

/-- `g₂` depends only on the lattice, not on the chosen ordered period basis. -/
theorem g₂_congr {L M : PeriodPair} (h : L.lattice = M.lattice) : L.g₂ = M.g₂ := by
  unfold g₂ G
  rw [h]

/-- `g₃` depends only on the lattice, not on the chosen ordered period basis. -/
theorem g₃_congr {L M : PeriodPair} (h : L.lattice = M.lattice) : L.g₃ = M.g₃ := by
  unfold g₃ G
  rw [h]

/-- The lattice `j`-invariant is independent of the chosen ordered period basis. -/
theorem j_congr {L M : PeriodPair} (h : L.lattice = M.lattice) : L.j = M.j := by
  simp [j, discriminant, g₂_congr h, g₃_congr h]

end PeriodPair

namespace UpperHalfPlane

/-- The normalized period pair `[1, τ]`. -/
noncomputable def periodPair (τ : ℍ) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := by
    refine LinearIndependent.pair_iff.mpr fun a b hab => ?_
    have hb_im : b * τ.im = 0 := by
      simpa [Complex.real_smul] using congrArg Complex.im hab
    have hb : b = 0 := (mul_eq_zero.mp hb_im).resolve_right τ.im_ne_zero
    have ha : a = 0 := by
      simpa [Complex.real_smul, hb] using congrArg Complex.re hab
    exact ⟨ha, hb⟩

end UpperHalfPlane

private lemma periodPair_G_eq_aux (τ : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    (UpperHalfPlane.periodPair τ).G k = riemannZeta k * eisensteinSeries (N := 1) 0 k τ := by
  rw [← tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ, PeriodPair.G,
    ← (((finTwoArrowEquiv ℤ).trans (Equiv.prodComm ℤ ℤ)).trans
    (UpperHalfPlane.periodPair τ).latticeEquivProd.toEquiv.symm).tsum_eq
    (f := fun l : (UpperHalfPlane.periodPair τ).lattice ↦ ((l : ℂ) ^ k)⁻¹)]
  refine tsum_congr fun v ↦ ?_
  have hcoe : (((UpperHalfPlane.periodPair τ).latticeEquivProd.symm (v 1, v 0) : ℂ)) =
      (v 1 : ℂ) + (v 0 : ℂ) * τ := by
    simpa [UpperHalfPlane.periodPair] using
      (UpperHalfPlane.periodPair τ).latticeEquiv_symm_apply (v 1, v 0)
  simp only [Equiv.trans_apply, finTwoArrowEquiv_apply, Equiv.prodComm_apply,
    Prod.swap_prod_mk, eisSummand, zpow_neg, zpow_natCast, Equiv.toFun_as_coe,
    piFinTwoEquiv_apply, LinearEquiv.coe_toEquiv_symm, EquivLike.coe_coe]
  rw [show ((UpperHalfPlane.periodPair τ).latticeEquivProd.symm (v 1, v 0) : ℂ) =
      (v 1 : ℂ) + (v 0 : ℂ) * τ from hcoe]
  ring_nf

private lemma riemannZeta_six_aux : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_six, Nat.factorial] at h
  rw [h]
  ring

/-- The lattice Eisenstein invariant `g₂([1,τ])` in terms of the normalized `E₄`. -/
theorem periodPair_g₂_eq_E4 (τ : ℍ) :
    (UpperHalfPlane.periodPair τ).g₂ = 4 * (π : ℂ) ^ 4 / 3 * E4 τ := by
  rw [PeriodPair.g₂, periodPair_G_eq_aux τ (by norm_num)]
  norm_num [riemannZeta_four]
  rw [show eisensteinSeries (N := 1) 0 4 τ = 2 * E4 τ by
    rw [show E4 τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 4 τ from rfl,
      eisensteinSeriesSIF_apply]
    simp]
  ring

/-- The lattice Eisenstein invariant `g₃([1,τ])` in terms of the normalized `E₆`. -/
theorem periodPair_g₃_eq_E6 (τ : ℍ) :
    (UpperHalfPlane.periodPair τ).g₃ = 8 * (π : ℂ) ^ 6 / 27 * E6 τ := by
  rw [PeriodPair.g₃, periodPair_G_eq_aux τ (by norm_num)]
  norm_num [riemannZeta_six_aux]
  rw [show eisensteinSeries (N := 1) 0 6 τ = 2 * E6 τ by
    rw [show E6 τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 6 τ from rfl,
      eisensteinSeriesSIF_apply]
    simp]
  ring

/-- The project discriminant equals `(E₄³ - E₆²) / 1728` pointwise. -/
theorem Delta_eq_E4_E6 (τ : ℍ) : Delta τ = (E4 τ ^ 3 - E6 τ ^ 2) / 1728 := by
  rw [Delta_apply, Delta_eq_eta_pow]
  change ModularForm.discriminant τ = _
  exact ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ

/-- The analytic modular `j` agrees with the lattice invariant of `[1,τ]`. -/
theorem j_eq_periodPair_j (τ : ℍ) : j τ = (UpperHalfPlane.periodPair τ).j := by
  rw [j, PeriodPair.j, PeriodPair.discriminant, periodPair_g₂_eq_E4,
    periodPair_g₃_eq_E6, Delta_eq_E4_E6]
  have hK : (64 * (π : ℂ) ^ 12 / 27) ≠ 0 := by
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  rw [show (4 * (π : ℂ) ^ 4 / 3 * E4 τ) ^ 3 -
        27 * (8 * (π : ℂ) ^ 6 / 27 * E6 τ) ^ 2 =
      (64 * (π : ℂ) ^ 12 / 27) * (E4 τ ^ 3 - E6 τ ^ 2) by ring,
    show 1728 * (4 * (π : ℂ) ^ 4 / 3 * E4 τ) ^ 3 =
      (64 * (π : ℂ) ^ 12 / 27) * (1728 * E4 τ ^ 3) by ring,
    mul_div_mul_left _ _ hK, div_div_eq_mul_div]
  ring

/-- Every complex period lattice is homothetic to `[1,τ]` for some `τ ∈ ℍ`. -/
theorem exists_homothetic_periodPair (L : PeriodPair) :
    ∃ τ : ℍ, L.Homothetic (UpperHalfPlane.periodPair τ) := by
  have hω₁ : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have hω₂ : L.ω₂ ≠ 0 := by simpa using L.indep.ne_zero 1
  have him : (L.ω₂ / L.ω₁).im ≠ 0 := by
    intro h0
    have hτ : (L.ω₂ / L.ω₁ : ℂ) = ((L.ω₂ / L.ω₁).re : ℝ) := by
      exact Complex.ext (by simp) (by simpa using h0)
    have hzero : ((L.ω₂ / L.ω₁).re : ℝ) • L.ω₁ + (-1 : ℝ) • L.ω₂ = 0 := by
      rw [Complex.real_smul, Complex.real_smul, ← hτ]
      push_cast
      field_simp
      ring
    obtain ⟨-, ht⟩ := LinearIndependent.pair_iff.mp L.indep _ _ hzero
    norm_num at ht
  rcases lt_or_gt_of_ne him with hneg | hpos
  · refine ⟨⟨L.ω₁ / L.ω₂, ?_⟩, Units.mk0 L.ω₂⁻¹ (inv_ne_zero hω₂), ?_⟩
    · rw [show L.ω₁ / L.ω₂ = (L.ω₂ / L.ω₁)⁻¹ from (inv_div L.ω₂ L.ω₁).symm,
        Complex.inv_im]
      have hns : 0 < Complex.normSq (L.ω₂ / L.ω₁) :=
        Complex.normSq_pos.mpr (div_ne_zero hω₂ hω₁)
      exact div_pos (by linarith) hns
    · rw [PeriodPair.lattice, PeriodPair.lattice]
      congr 1
      rw [PeriodPair.smul_ω₁, PeriodPair.smul_ω₂]
      rw [show ((Units.mk0 L.ω₂⁻¹ (inv_ne_zero hω₂) : ℂˣ) : ℂ) =
        L.ω₂⁻¹ from rfl]
      rw [Set.pair_comm]
      congr 1
      · exact inv_mul_cancel₀ hω₂
      · exact congrArg _ (inv_mul_eq_div _ _)
  · refine ⟨⟨L.ω₂ / L.ω₁, hpos⟩, Units.mk0 L.ω₁⁻¹ (inv_ne_zero hω₁), ?_⟩
    rw [PeriodPair.lattice, PeriodPair.lattice]
    congr 1
    rw [PeriodPair.smul_ω₁, PeriodPair.smul_ω₂]
    rw [show ((Units.mk0 L.ω₁⁻¹ (inv_ne_zero hω₁) : ℂˣ) : ℂ) = L.ω₁⁻¹ from rfl]
    congr 1
    · exact inv_mul_cancel₀ hω₁
    · exact congrArg _ (inv_mul_eq_div _ _)

private lemma E4_cube_sub_E6_sq_ne_zero_aux (τ : ℍ) : E4 τ ^ 3 - E6 τ ^ 2 ≠ 0 := by
  intro h
  have hΔ : Delta τ ≠ 0 := by
    rw [Delta_apply, Delta_eq_eta_pow]
    exact ModularForm.discriminant_ne_zero τ
  exact hΔ (by rw [Delta_eq_E4_E6, h, zero_div])

private lemma periodPair_discriminant_eq_aux (τ : ℍ) :
    (UpperHalfPlane.periodPair τ).discriminant =
      64 * (π : ℂ) ^ 12 / 27 * (E4 τ ^ 3 - E6 τ ^ 2) := by
  rw [PeriodPair.discriminant, periodPair_g₂_eq_E4, periodPair_g₃_eq_E6]
  ring

namespace PeriodPair

/-- Cox Proposition 10.7: the discriminant of a complex lattice never vanishes. -/
theorem discriminant_ne_zero (L : PeriodPair) : L.discriminant ≠ 0 := by
  obtain ⟨τ, a, ha⟩ := exists_homothetic_periodPair L
  have hcongr : (a • L).discriminant = (UpperHalfPlane.periodPair τ).discriminant := by
    rw [discriminant, discriminant, g₂_congr ha, g₃_congr ha]
  rw [L.discriminant_smul a] at hcongr
  intro h0
  rw [h0, mul_zero] at hcongr
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hne : (UpperHalfPlane.periodPair τ).discriminant ≠ 0 := by
    rw [periodPair_discriminant_eq_aux]
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hπ)) (by norm_num))
      (E4_cube_sub_E6_sq_ne_zero_aux τ)
  exact hne hcongr.symm

/-- Cox Theorem 10.9, easy direction. -/
theorem j_eq_of_homothetic {L M : PeriodPair} (h : L.Homothetic M) : L.j = M.j := by
  obtain ⟨a, ha⟩ := h
  exact (L.j_smul a).symm.trans (j_congr ha)

private lemma j_eq_zero_iff_g₂_eq_zero_aux {L : PeriodPair} (hΔ : L.discriminant ≠ 0) :
    L.j = 0 ↔ L.g₂ = 0 := by
  constructor
  · intro h
    rw [j, div_eq_zero_iff] at h
    rcases h with h | h
    · have h3 : L.g₂ ^ 3 = 0 := by linear_combination h / 1728
      exact pow_eq_zero_iff (by norm_num) |>.mp h3
    · exact absurd h hΔ
  · intro h
    simp [j, h]

private lemma j_eq_1728_iff_g₃_eq_zero_aux {L : PeriodPair} (hΔ : L.discriminant ≠ 0) :
    L.j = 1728 ↔ L.g₃ = 0 := by
  constructor
  · intro h
    rw [j, div_eq_iff hΔ, discriminant] at h
    have h2 : L.g₃ ^ 2 = 0 := by linear_combination h / 46656
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  · intro h
    have hg₂ : L.g₂ ≠ 0 := fun h₂ ↦ hΔ <| by
      rw [discriminant, h, h₂]
      ring
    rw [j, discriminant, h]
    rw [show (27 : ℂ) * 0 ^ 2 = 0 by ring, sub_zero, mul_div_assoc,
      div_self (pow_ne_zero 3 hg₂), mul_one]

private theorem homothetic_of_j_eq_of_g₂_eq_zero_aux {L M : PeriodPair} (h : L.j = M.j)
    (hg₂L : L.g₂ = 0) : L.Homothetic M := by
  have hΔL := L.discriminant_ne_zero
  have hΔM := M.discriminant_ne_zero
  have hg₂M : M.g₂ = 0 := (j_eq_zero_iff_g₂_eq_zero_aux hΔM).mp <| by
    rw [← h]
    exact (j_eq_zero_iff_g₂_eq_zero_aux hΔL).mpr hg₂L
  have hg₃L : L.g₃ ≠ 0 := fun h₃ ↦ hΔL <| by
    rw [discriminant, hg₂L, h₃]
    ring
  have hg₃M : M.g₃ ≠ 0 := fun h₃ ↦ hΔM <| by
    rw [discriminant, hg₂M, h₃]
    ring
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₃ / M.g₃) (n := 6) (by norm_num)
  have hc0 : c ≠ 0 := by
    intro h0
    apply hg₃L
    have hd : L.g₃ / M.g₃ = 0 := by
      rw [← hc, h0]
      norm_num
    exact (div_eq_zero_iff.mp hd).resolve_right hg₃M
  refine ⟨Units.mk0 c hc0, lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_⟩
  · rw [g₂_smul, hg₂L, hg₂M, mul_zero]
  · rw [g₃_smul]
    rw [show ((Units.mk0 c hc0 : ℂˣ) : ℂ) = c from rfl, hc]
    field_simp

private theorem homothetic_of_j_eq_of_g₃_eq_zero_aux {L M : PeriodPair} (h : L.j = M.j)
    (hg₂L : L.g₂ ≠ 0) (hg₃L : L.g₃ = 0) : L.Homothetic M := by
  have hΔL := L.discriminant_ne_zero
  have hΔM := M.discriminant_ne_zero
  have hg₃M : M.g₃ = 0 := (j_eq_1728_iff_g₃_eq_zero_aux hΔM).mp <| by
    rw [← h]
    exact (j_eq_1728_iff_g₃_eq_zero_aux hΔL).mpr hg₃L
  have hg₂M : M.g₂ ≠ 0 := fun h₂ ↦ hΔM <| by
    rw [discriminant, hg₃M, h₂]
    ring
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ / M.g₂) (n := 4) (by norm_num)
  have hc0 : c ≠ 0 := by
    intro h0
    apply hg₂L
    have hd : L.g₂ / M.g₂ = 0 := by
      rw [← hc, h0]
      norm_num
    exact (div_eq_zero_iff.mp hd).resolve_right hg₂M
  refine ⟨Units.mk0 c hc0, lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_⟩
  · rw [g₂_smul]
    rw [show ((Units.mk0 c hc0 : ℂˣ) : ℂ) = c from rfl, hc]
    field_simp
  · rw [g₃_smul, hg₃L, hg₃M, mul_zero]

private theorem homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux {L M : PeriodPair}
    (h : L.j = M.j) (hg₂L : L.g₂ ≠ 0) (hg₃L : L.g₃ ≠ 0) : L.Homothetic M := by
  have hΔL := L.discriminant_ne_zero
  have hΔM := M.discriminant_ne_zero
  have hg₂M : M.g₂ ≠ 0 := fun h0 ↦ hg₂L <|
    (j_eq_zero_iff_g₂_eq_zero_aux hΔL).mp <| by
      rw [h]
      exact (j_eq_zero_iff_g₂_eq_zero_aux hΔM).mpr h0
  have hg₃M : M.g₃ ≠ 0 := fun h0 ↦ hg₃L <|
    (j_eq_1728_iff_g₃_eq_zero_aux hΔL).mp <| by
      rw [h]
      exact (j_eq_1728_iff_g₃_eq_zero_aux hΔM).mpr h0
  have hcross : L.g₂ ^ 3 * M.g₃ ^ 2 = M.g₂ ^ 3 * L.g₃ ^ 2 := by
    rw [j, j, div_eq_div_iff hΔL hΔM, discriminant, discriminant] at h
    linear_combination -h / 46656
  obtain ⟨c, hc⟩ :=
    IsAlgClosed.exists_pow_nat_eq (L.g₃ * M.g₂ / (M.g₃ * L.g₂)) (n := 2) (by norm_num)
  have hb0 : L.g₃ * M.g₂ / (M.g₃ * L.g₂) ≠ 0 :=
    div_ne_zero (mul_ne_zero hg₃L hg₂M) (mul_ne_zero hg₃M hg₂L)
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0] at hc
    apply hb0
    rw [← hc]
    norm_num
  have hc4 : c ^ 4 = L.g₂ / M.g₂ := by
    rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc, div_pow, div_eq_div_iff
      (pow_ne_zero _ (mul_ne_zero hg₃M hg₂L)) hg₂M]
    linear_combination -hcross
  have hc6 : c ^ 6 = L.g₃ / M.g₃ := by
    rw [show c ^ 6 = (c ^ 2) ^ 3 by ring, hc, div_pow, div_eq_div_iff
      (pow_ne_zero _ (mul_ne_zero hg₃M hg₂L)) hg₃M]
    linear_combination -L.g₃ * M.g₃ * hcross
  refine ⟨Units.mk0 c hc0, lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_⟩
  · rw [g₂_smul]
    rw [show ((Units.mk0 c hc0 : ℂˣ) : ℂ) = c from rfl, hc4]
    field_simp
  · rw [g₃_smul]
    rw [show ((Units.mk0 c hc0 : ℂˣ) : ℂ) = c from rfl, hc6]
    field_simp

/-- Cox Theorem 10.9: period pairs with equal `j`-invariants are homothetic. -/
theorem homothetic_of_j_eq {L M : PeriodPair} (h : L.j = M.j) : L.Homothetic M := by
  by_cases hg₂L : L.g₂ = 0
  · exact homothetic_of_j_eq_of_g₂_eq_zero_aux h hg₂L
  · by_cases hg₃L : L.g₃ = 0
    · exact homothetic_of_j_eq_of_g₃_eq_zero_aux h hg₂L hg₃L
    · exact homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux h hg₂L hg₃L

/-- Cox Theorem 10.9 in iff form. -/
theorem j_eq_iff_homothetic {L M : PeriodPair} : L.j = M.j ↔ L.Homothetic M :=
  ⟨homothetic_of_j_eq, j_eq_of_homothetic⟩

end PeriodPair

private lemma mem_periodPair_lattice_aux {τ : ℍ} {x : ℂ} :
    x ∈ (UpperHalfPlane.periodPair τ).lattice ↔ ∃ m n : ℤ, (m : ℂ) + n * τ = x := by
  rw [PeriodPair.mem_lattice]
  simp [UpperHalfPlane.periodPair]

private lemma int_comb_injective_aux {τ : ℍ} {m n m' n' : ℤ}
    (h : (m : ℂ) + n * τ = (m' : ℂ) + n' * τ) : m = m' ∧ n = n' := by
  have hzero : ((m - m' : ℤ) : ℝ) • (UpperHalfPlane.periodPair τ).ω₁ +
      ((n - n' : ℤ) : ℝ) • (UpperHalfPlane.periodPair τ).ω₂ = 0 := by
    change ((m - m' : ℤ) : ℝ) • (1 : ℂ) + ((n - n' : ℤ) : ℝ) • (τ : ℂ) = 0
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    linear_combination h
  obtain ⟨h1, h2⟩ :=
    LinearIndependent.pair_iff.mp (UpperHalfPlane.periodPair τ).indep _ _ hzero
  constructor
  · have hm : ((m - m' : ℤ) : ℝ) = 0 := h1
    exact sub_eq_zero.mp (by exact_mod_cast hm)
  · have hn : ((n - n' : ℤ) : ℝ) = 0 := h2
    exact sub_eq_zero.mp (by exact_mod_cast hn)

private theorem exists_sl2_smul_eq_of_det_mul_eq_one_aux {z w : ℍ} (a b c d k : ℤ)
    (hdet : (a * d - b * c) * k = 1)
    (hzval : (z : ℂ) = ((b : ℂ) + a * w) / ((d : ℂ) + c * w)) :
    ∃ γ : SL(2, ℤ), γ • z = w := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨hD, -⟩ | ⟨hD, -⟩
  · have hdet1 : Matrix.det !![a, b; c, d] = 1 := by
      rw [Matrix.det_fin_two_of]
      omega
    set γ' : SL(2, ℤ) := ⟨!![a, b; c, d], hdet1⟩ with hγ'
    refine ⟨γ'⁻¹, ?_⟩
    have hcoe : ((γ' • w : ℍ) : ℂ) = (z : ℂ) := by
      rw [UpperHalfPlane.coe_specialLinearGroup_apply, hzval, hγ']
      simp [algebraMap_int_eq]
      ring
    have hsmul : γ' • w = z := UpperHalfPlane.ext hcoe
    rw [← hsmul, inv_smul_smul]
  · exfalso
    have hdet1 : Matrix.det !![-a, -b; c, d] = 1 := by
      rw [Matrix.det_fin_two_of]
      have hD' : a * d - b * c = -1 := hD
      ring_nf
      omega
    set γ'' : SL(2, ℤ) := ⟨!![-a, -b; c, d], hdet1⟩ with hγ''
    have hcoe : ((γ'' • w : ℍ) : ℂ) = -(z : ℂ) := by
      rw [UpperHalfPlane.coe_specialLinearGroup_apply, hzval, hγ'']
      simp [algebraMap_int_eq]
      ring
    have him := (γ'' • w).im_pos
    rw [UpperHalfPlane.im, hcoe, Complex.neg_im, UpperHalfPlane.coe_im] at him
    linarith [z.im_pos]

private theorem exists_sl2_smul_eq_of_periodPair_homothetic_aux {z w : ℍ}
    (h : PeriodPair.Homothetic (UpperHalfPlane.periodPair z)
      (UpperHalfPlane.periodPair w)) : ∃ γ : SL(2, ℤ), γ • z = w := by
  obtain ⟨α, hα⟩ := h
  have hz1 : (α : ℂ) * z ∈ (UpperHalfPlane.periodPair w).lattice := by
    rw [← hα]
    exact (UpperHalfPlane.periodPair z).mem_smul_lattice.mpr
      ⟨z, mem_periodPair_lattice_aux.mpr ⟨0, 1, by simp⟩, rfl⟩
  have hz2 : (α : ℂ) ∈ (UpperHalfPlane.periodPair w).lattice := by
    rw [← hα]
    exact (UpperHalfPlane.periodPair z).mem_smul_lattice.mpr
      ⟨1, mem_periodPair_lattice_aux.mpr ⟨1, 0, by simp⟩, by simp⟩
  obtain ⟨b, a, hab⟩ := mem_periodPair_lattice_aux.mp hz1
  obtain ⟨d, c, hcd⟩ := mem_periodPair_lattice_aux.mp hz2
  have hw1 : (1 : ℂ) ∈ ((α : ℂˣ) • UpperHalfPlane.periodPair z).lattice := by
    rw [hα]
    exact mem_periodPair_lattice_aux.mpr ⟨1, 0, by simp⟩
  have hw2 : (w : ℂ) ∈ ((α : ℂˣ) • UpperHalfPlane.periodPair z).lattice := by
    rw [hα]
    exact mem_periodPair_lattice_aux.mpr ⟨0, 1, by simp⟩
  obtain ⟨y1, hy1, hy1e⟩ := (UpperHalfPlane.periodPair z).mem_smul_lattice.mp hw1
  obtain ⟨y2, hy2, hy2e⟩ := (UpperHalfPlane.periodPair z).mem_smul_lattice.mp hw2
  obtain ⟨p, q, hpq⟩ := mem_periodPair_lattice_aux.mp hy1
  obtain ⟨r, s, hrs⟩ := mem_periodPair_lattice_aux.mp hy2
  have he1 : (1 : ℂ) = (q : ℂ) * b + p * d + ((q : ℂ) * a + p * c) * w := by
    linear_combination hy1e - (α : ℂ) * hpq - (p : ℂ) * hcd - (q : ℂ) * hab
  obtain ⟨h2, h1⟩ := int_comb_injective_aux
    (show ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * w =
        ((q * b + p * d : ℤ) : ℂ) + ((q * a + p * c : ℤ) : ℂ) * w by
      push_cast
      linear_combination he1)
  have he2 : (w : ℂ) = (s : ℂ) * b + r * d + ((s : ℂ) * a + r * c) * w := by
    linear_combination hy2e - (α : ℂ) * hrs - (r : ℂ) * hcd - (s : ℂ) * hab
  obtain ⟨-, h3⟩ := int_comb_injective_aux
    (show ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * w =
        ((s * b + r * d : ℤ) : ℂ) + ((s * a + r * c : ℤ) : ℂ) * w by
      push_cast
      linear_combination he2)
  have hdet : (a * d - b * c) * (p * s - q * r) = 1 := by
    linear_combination (-(s * b) - r * d) * h1.symm +
      (s * a + r * c) * h2.symm + h3.symm
  have hαd : (α : ℂ) = (d : ℂ) + c * w := hcd.symm
  have hzval : (z : ℂ) = ((b : ℂ) + a * w) / ((d : ℂ) + c * w) := by
    rw [← hαd, hab, mul_div_cancel_left₀ _ α.ne_zero]
  exact exists_sl2_smul_eq_of_det_mul_eq_one_aux a b c d (p * s - q * r) hdet hzval

private theorem periodPair_homothetic_of_sl2_smul_aux (γ : SL(2, ℤ)) (z : ℍ) :
    PeriodPair.Homothetic (UpperHalfPlane.periodPair z)
      (UpperHalfPlane.periodPair (γ • z)) := by
  set a : ℤ := γ 0 0 with ha
  set b : ℤ := γ 0 1 with hb
  set c : ℤ := γ 1 0 with hc
  set d : ℤ := γ 1 1 with hd
  have hdet : a * d - b * c = 1 := by
    have h := γ.2
    rwa [Matrix.det_fin_two] at h
  have hdetc : (a : ℂ) * d - b * c = 1 := by
    exact_mod_cast hdet
  have hden : ((c : ℂ) * z + d) ≠ 0 := by
    have h := UpperHalfPlane.denom_ne_zero γ z
    rwa [ModularGroup.denom_apply] at h
  have hwval : ((γ • z : ℍ) : ℂ) = ((a : ℂ) * z + b) / ((c : ℂ) * z + d) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [algebraMap_int_eq, ← ha, ← hb, ← hc, ← hd]
  have hw' : ((c : ℂ) * z + d) * ((γ • z : ℍ) : ℂ) = (a : ℂ) * z + b := by
    rw [hwval, mul_comm, div_mul_cancel₀ _ hden]
  refine ⟨(Units.mk0 _ hden)⁻¹, ?_⟩
  ext x
  rw [PeriodPair.mem_smul_lattice]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨m, n, hmn⟩ := mem_periodPair_lattice_aux.mp hy
    refine mem_periodPair_lattice_aux.mpr ⟨m * a - n * b, n * d - m * c, ?_⟩
    rw [show ((Units.mk0 _ hden)⁻¹ : ℂˣ).val = ((c : ℂ) * z + d)⁻¹ from rfl,
      ← hmn, eq_inv_mul_iff_mul_eq₀ hden]
    push_cast
    linear_combination ((n : ℂ) * d - m * c) * hw' + ((m : ℂ) + n * z) * hdetc
  · intro hx
    obtain ⟨m, n, hmn⟩ := mem_periodPair_lattice_aux.mp hx
    refine ⟨((c : ℂ) * z + d) * x, mem_periodPair_lattice_aux.mpr
      ⟨m * d + n * b, m * c + n * a, ?_⟩, ?_⟩
    · rw [← hmn]
      push_cast
      linear_combination (-(n : ℂ)) * hw'
    · rw [show ((Units.mk0 _ hden)⁻¹ : ℂˣ).val = ((c : ℂ) * z + d)⁻¹ from rfl]
      rw [inv_mul_cancel_left₀ hden]

/-- Cox equation (7.8): homothety of normalized lattices is the `SL₂(ℤ)` orbit relation. -/
theorem periodPair_homothetic_iff_exists_sl2_smul_eq {z w : ℍ} :
    PeriodPair.Homothetic (UpperHalfPlane.periodPair z) (UpperHalfPlane.periodPair w) ↔
      ∃ γ : SL(2, ℤ), γ • z = w := by
  constructor
  · exact exists_sl2_smul_eq_of_periodPair_homothetic_aux
  · rintro ⟨γ, rfl⟩
    exact periodPair_homothetic_of_sl2_smul_aux γ z

/-- Cox Theorem 11.2(ii), proved through the three requested lattice steps. -/
theorem j_eq_iff_exists_sl2_smul_eq (τ τ' : ℍ) :
    j τ = j τ' ↔ ∃ γ : SL(2, ℤ), γ • τ = τ' := by
  rw [j_eq_periodPair_j, j_eq_periodPair_j, PeriodPair.j_eq_iff_homothetic,
    periodPair_homothetic_iff_exists_sl2_smul_eq]

private def levelOneWeightZeroCuspForm_aux {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f)
    (hmdiff : MDiff f) (hzero : IsZeroAtImInfty f) : CuspForm (Gamma 1) 0 where
  toFun := f
  slash_action_eq' := fun γ hγ => by
    obtain ⟨γ', _, rfl⟩ := hγ
    exact hslash γ'
  holo' := hmdiff
  zero_at_cusps' := fun hc =>
    zero_at_cusps_of_zero_at_infty hc fun A hA => by
      obtain ⟨γ, rfl⟩ := hA
      have hγ : f ∣[(0 : ℤ)] (mapGL ℝ γ) = f := hslash γ
      simpa [hγ] using hzero

private theorem weight_zero_cuspForm_eq_zero_aux {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f)
    (hmdiff : MDiff f) (hzero : IsZeroAtImInfty f) : f = 0 := by
  let F : ModularForm (Gamma 1) 0 := levelOneWeightZeroCuspForm_aux hslash hmdiff hzero
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero F
  have hc0 : c = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hc ▸ show IsZeroAtImInfty ⇑F from hzero)
  ext z
  simpa [hc0] using congrFun hc z

private theorem inv_j_sub_slashInvariant_aux (c : ℂ) :
    letI f : ℍ → ℂ := fun τ => (j τ - c)⁻¹
    ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f := by
  intro γ
  ext τ
  have hj := congrFun (j_slashInvariant γ) τ
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one] at hj ⊢
  simpa [hj]

private lemma j_mdifferentiable_aux : MDiff j := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hE4 : DifferentiableAt ℂ (E4 ∘ UpperHalfPlane.ofComplex) z :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo E4 ⟨z, hz⟩)
  have hDelta : DifferentiableAt ℂ (Delta ∘ UpperHalfPlane.ofComplex) z :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo Delta ⟨z, hz⟩)
  have hDelta0 : (Delta ∘ UpperHalfPlane.ofComplex) z ≠ 0 := by
    simpa [Function.comp_def, UpperHalfPlane.ofComplex_apply_of_im_pos hz, Delta_apply] using
      Δ_ne_zero (UpperHalfPlane.ofComplex z)
  have hj : DifferentiableAt ℂ (j ∘ UpperHalfPlane.ofComplex) z := by
    simpa [j, Function.comp_def] using (hE4.pow 3).div hDelta hDelta0
  exact hj.differentiableWithinAt

private theorem inv_j_sub_mdiff_aux (c : ℂ) (hc : ∀ τ : ℍ, j τ ≠ c) :
    MDiff (fun τ : ℍ => (j τ - c)⁻¹) := fun τ =>
  ((j_mdifferentiable_aux τ).sub mdifferentiableAt_const).inv
    (sub_ne_zero.mpr (hc τ))

private lemma E4_tendsto_atImInfty_aux : Tendsto (E4 : ℍ → ℂ) atImInfty (nhds 1) := by
  have hper : Periodic ((E4 : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex E4 (by simp)
  have h0 : cuspFunction 1 (E4 : ℍ → ℂ) 0 = 1 := by
    simpa [qExpansion_coeff, E4] using
      EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) ⟨2, rfl⟩
  simpa only [Function.comp_def, UpperHalfPlane.eq_cuspFunction _ one_ne_zero hper, h0] using
    (ModularFormClass.analyticAt_cuspFunction_zero (h := (1 : ℝ)) E4 (by norm_num)
      (by simp)).continuousAt.tendsto.comp
      (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) (by norm_num))

private lemma qj_tendsto_atImInfty_aux : Tendsto qj atImInfty (nhds 1) := by
  have hE4 : Tendsto (fun τ : ℍ => E4 τ ^ 3) atImInfty (nhds (1 ^ 3)) :=
    E4_tendsto_atImInfty_aux.pow 3
  have hqj : Tendsto ((fun τ : ℍ => E4 τ ^ 3) * qoverDelta) atImInfty
      (nhds (1 ^ 3 * 1)) := hE4.mul qoverDelta_tendsto_atImInfty
  have hEq : ((fun τ : ℍ => E4 τ ^ 3) * qoverDelta) = qj := by
    ext τ
    exact congrFun qjIdentity τ
  simpa [hEq] using hqj

private theorem inv_j_sub_isZeroAtImInfty_aux (c : ℂ) :
    IsZeroAtImInfty (fun τ : ℍ => (j τ - c)⁻¹) := by
  let q : ℍ → ℂ := fun τ => 𝕢 1 τ
  have hq : Tendsto q atImInfty (nhds 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num)
  have hden : Tendsto (fun τ : ℍ => qj τ - c * q τ) atImInfty (nhds 1) := by
    simpa using qj_tendsto_atImInfty_aux.sub (tendsto_const_nhds.mul hq)
  have hratio : Tendsto (fun τ : ℍ => q τ / (qj τ - c * q τ))
      atImInfty (nhds 0) := by
    simpa using hq.mul (hden.inv₀ (by norm_num : (1 : ℂ) ≠ 0))
  have hEq : (fun τ : ℍ => (j τ - c)⁻¹) =ᶠ[atImInfty]
      fun τ : ℍ => q τ / (qj τ - c * q τ) := by
    refine Eventually.of_forall fun τ => ?_
    simp only [show qj τ = q τ * j τ by simp [q, qj, Periodic.qParam]]
    field_simp [show q τ ≠ 0 by simp [q, Periodic.qParam]]
  exact hratio.congr' hEq.symm

/-- Cox Theorem 11.2(iii): the analytic modular `j` is surjective. -/
theorem j_surjective : Function.Surjective j := by
  intro c
  by_contra! hc
  have hf := weight_zero_cuspForm_eq_zero_aux (inv_j_sub_slashInvariant_aux c)
    (inv_j_sub_mdiff_aux c hc) (inv_j_sub_isZeroAtImInfty_aux c)
  let τ : ℍ := ⟨Complex.I, by norm_num⟩
  exact inv_ne_zero (sub_ne_zero.mpr (hc τ)) (congrFun hf τ)
