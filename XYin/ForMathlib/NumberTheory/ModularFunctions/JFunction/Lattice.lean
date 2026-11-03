/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import XYin.ForMathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import XYin.ForMathlib.NumberTheory.ModularFunctions.JFunction.Basic

/-!
# The lattice discriminant and its analytic j-invariant

The dependency subset of `XYin.PhD.Cox.LatticeJ` needed to attach an elliptic curve to a
complex period pair: scaling of Eisenstein invariants, normalization to `[1, τ]`, nonvanishing
of the lattice discriminant, and equality of the lattice and analytic j-invariants.
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
    refine LinearIndependent.pair_iff.mpr fun s t hst ↦
      LinearIndependent.pair_iff.mp L.indep s t ?_
    have h : (a : ℂ) * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [mul_add, mul_smul_comm, mul_smul_comm]
      exact hst
    exact (mul_eq_zero.mp h).resolve_left a.ne_zero

instance instSMulUnitsComplex : SMul ℂˣ PeriodPair := ⟨PeriodPair.smul⟩

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
  change (∃ y ∈ L.lattice, (a : ℂ) * y = x) ↔ ∃ y ∈ L.lattice, x = (a : ℂ) * y
  simp only [eq_comm]

/-- Scaling by a unit, restricted to the corresponding period lattices. -/
def smulLatticeEquiv (a : ℂˣ) (L : PeriodPair) :
    L.lattice ≃ₗ[ℤ] (a • L).lattice :=
  (a.mulLeftLinearEquiv ℤ ℂ).ofSubmodules L.lattice (a • L).lattice
    (map_lattice_mulLeftLinearEquiv a L)

/-- Eisenstein sums have weight `n` under scaling. -/
theorem G_smul (L : PeriodPair) (a : ℂˣ) (n : ℕ) :
    (a • L).G n = ((a : ℂ) ^ n)⁻¹ * L.G n := by
  let e := (smulLatticeEquiv a L).toEquiv
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

/-- `g₂` depends only on the lattice, not on the chosen ordered period basis. -/
theorem g₂_congr {L M : PeriodPair} (h : L.lattice = M.lattice) : L.g₂ = M.g₂ := by
  unfold g₂ G
  rw [h]

/-- `g₃` depends only on the lattice, not on the chosen ordered period basis. -/
theorem g₃_congr {L M : PeriodPair} (h : L.lattice = M.lattice) : L.g₃ = M.g₃ := by
  unfold g₃ G
  rw [h]

end PeriodPair

namespace UpperHalfPlane

/-- The normalized period pair `[1, τ]`. -/
noncomputable def periodPair (τ : ℍ) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := by
    refine LinearIndependent.pair_iff.mpr fun a b hab ↦ ?_
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
theorem periodPair_g₂_eq_E₄ (τ : ℍ) :
    (UpperHalfPlane.periodPair τ).g₂ = 4 * (π : ℂ) ^ 4 / 3 * E₄ τ := by
  rw [PeriodPair.g₂, periodPair_G_eq_aux τ (by norm_num)]
  norm_num [riemannZeta_four]
  rw [show eisensteinSeries (N := 1) 0 4 τ = 2 * E₄ τ by
    rw [show E₄ τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 4 τ from rfl,
      eisensteinSeriesSIF_apply]
    simp]
  ring

/-- The lattice Eisenstein invariant `g₃([1,τ])` in terms of the normalized `E₆`. -/
theorem periodPair_g₃_eq_E₆ (τ : ℍ) :
    (UpperHalfPlane.periodPair τ).g₃ = 8 * (π : ℂ) ^ 6 / 27 * E₆ τ := by
  rw [PeriodPair.g₃, periodPair_G_eq_aux τ (by norm_num)]
  norm_num [riemannZeta_six_aux]
  rw [show eisensteinSeries (N := 1) 0 6 τ = 2 * E₆ τ by
    rw [show E₆ τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 6 τ from rfl,
      eisensteinSeriesSIF_apply]
    simp]
  ring

/-- The analytic modular `j` agrees with the lattice invariant of `[1,τ]`. -/
theorem j_eq_periodPair_j (τ : ℍ) : j τ = (UpperHalfPlane.periodPair τ).j := by
  rw [j, PeriodPair.j, PeriodPair.discriminant, periodPair_g₂_eq_E₄,
    periodPair_g₃_eq_E₆, discriminant_eq_E₄_cube_sub_E₆_sq]
  have hK : (64 * (π : ℂ) ^ 12 / 27) ≠ 0 := by
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  rw [show (4 * (π : ℂ) ^ 4 / 3 * E₄ τ) ^ 3 -
        27 * (8 * (π : ℂ) ^ 6 / 27 * E₆ τ) ^ 2 =
      (64 * (π : ℂ) ^ 12 / 27) * (E₄ τ ^ 3 - E₆ τ ^ 2) by ring,
    show 1728 * (4 * (π : ℂ) ^ 4 / 3 * E₄ τ) ^ 3 =
      (64 * (π : ℂ) ^ 12 / 27) * (1728 * E₄ τ ^ 3) by ring,
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
    · simp [PeriodPair.lattice, UpperHalfPlane.periodPair, inv_mul_cancel₀ hω₂,
        div_eq_mul_inv, mul_comm, Set.pair_comm]
  · refine ⟨⟨L.ω₂ / L.ω₁, hpos⟩, Units.mk0 L.ω₁⁻¹ (inv_ne_zero hω₁), ?_⟩
    simp [PeriodPair.lattice, UpperHalfPlane.periodPair, inv_mul_cancel₀ hω₁,
      div_eq_mul_inv, mul_comm]

private lemma E₄_cube_sub_E₆_sq_ne_zero_aux (τ : ℍ) : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := fun h ↦
  discriminant_ne_zero τ (by rw [discriminant_eq_E₄_cube_sub_E₆_sq, h, zero_div])

private lemma periodPair_discriminant_eq_aux (τ : ℍ) :
    (UpperHalfPlane.periodPair τ).discriminant =
      64 * (π : ℂ) ^ 12 / 27 * (E₄ τ ^ 3 - E₆ τ ^ 2) := by
  rw [PeriodPair.discriminant, periodPair_g₂_eq_E₄, periodPair_g₃_eq_E₆]
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
      (E₄_cube_sub_E₆_sq_ne_zero_aux τ)
  exact hne hcongr.symm

end PeriodPair
