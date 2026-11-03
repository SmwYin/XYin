/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
module

public import XYin.ForMathlib.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Changes of cusp representative

The stabilizer of infinity in `SL(2, ℤ)` consists of the matrices `±T^m`.
Right multiplication by these matrices preserves the strict cusp width.
-/

@[expose] public noncomputable section

open Matrix Matrix.SpecialLinearGroup OnePoint
open scoped MatrixGroups Pointwise

namespace ModularGroup

/-- An integral determinant-one matrix with lower-left entry zero is `±T^m`. -/
lemma exists_eq_T_zpow_or_neg_of_c_eq_zero {γ : SL(2, ℤ)} (hc : γ 1 0 = 0) :
    ∃ m : ℤ, γ = T ^ m ∨ γ = -(T ^ m) := by
  have had : γ 0 0 * γ 1 1 = 1 := by
    have hdet := γ.det_coe
    rwa [det_fin_two, hc, mul_zero, sub_zero] at hdet
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · refine ⟨γ 0 1, Or.inl ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hc, hd, coe_T_zpow]
  · refine ⟨-(γ 0 1), Or.inr ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hc, hd, coe_T_zpow]

/-- The stabilizer of infinity in the modular group consists exactly of the matrices `±T^m`. -/
lemma smul_infty_eq_self_iff_exists_eq_T_zpow (γ : SL(2, ℤ)) :
    (γ : GL (Fin 2) ℝ) • (∞ : OnePoint ℝ) = ∞ ↔
      ∃ m : ℤ, γ = T ^ m ∨ γ = -(T ^ m) := by
  rw [OnePoint.smul_infty_eq_self_iff]
  change (γ 1 0 : ℝ) = 0 ↔ _
  constructor
  · intro hγ
    apply exists_eq_T_zpow_or_neg_of_c_eq_zero
    exact_mod_cast hγ
  · rintro ⟨m, rfl | rfl⟩ <;> simp [coe_T_zpow]

/-- Two matrices representing the same cusp point differ on the right by `±T^m`. -/
lemma exists_eq_mul_T_zpow_of_smul_infty_eq {γ γ' : SL(2, ℤ)}
    (h : (γ' : GL (Fin 2) ℝ) • (∞ : OnePoint ℝ) =
      (γ : GL (Fin 2) ℝ) • ∞) :
    ∃ m : ℤ, γ' = γ * T ^ m ∨ γ' = -(γ * T ^ m) := by
  have hfix : ((γ⁻¹ * γ' : SL(2, ℤ)) : GL (Fin 2) ℝ) • (∞ : OnePoint ℝ) = ∞ := by
    change mapGL ℝ (γ⁻¹ * γ') • (∞ : OnePoint ℝ) = ∞
    rw [map_mul, map_inv, mul_smul]
    change (γ : GL (Fin 2) ℝ)⁻¹ • ((γ' : GL (Fin 2) ℝ) • ∞) = ∞
    rw [h, inv_smul_smul]
  obtain ⟨m, hm | hm⟩ := (smul_infty_eq_self_iff_exists_eq_T_zpow _).mp hfix
  · exact ⟨m, Or.inl (by simpa using congrArg (γ * ·) hm)⟩
  · exact ⟨m, Or.inr (by simpa using congrArg (γ * ·) hm)⟩

/-- Matrices representing the same cusp orbit differ by a level-group element on the left
and `±T^m` on the right. -/
lemma exists_eq_mul_T_zpow_of_cuspOrbit_eq (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    {γ γ' : SL(2, ℤ)}
    (h : cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ'⁻¹⟧ =
      cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ⁻¹⟧) :
    ∃ δ ∈ Γ, ∃ m : ℤ, γ' = δ * γ * T ^ m ∨ γ' = -(δ * γ * T ^ m) := by
  simp only [cosetToCuspOrbit_apply_mk, inv_inv] at h
  obtain ⟨δg, hδg⟩ := Quotient.eq.mp h
  obtain ⟨δ, hδ, heq⟩ := δg.property
  refine ⟨δ, hδ, exists_eq_mul_T_zpow_of_smul_infty_eq ?_⟩
  have hpoint := congrArg Subtype.val hδg
  change (δg : GL (Fin 2) ℝ) • (mapGL ℝ γ • (∞ : OnePoint ℝ)) =
    mapGL ℝ γ' • (∞ : OnePoint ℝ) at hpoint
  rw [← heq, ← mul_smul, ← map_mul] at hpoint
  exact hpoint.symm

end ModularGroup

namespace Subgroup

/-- The strict width at infinity depends only on the strict period subgroup. -/
lemma strictWidthInfty_eq_of_strictPeriods_eq {Γ Δ : Subgroup (GL (Fin 2) ℝ)}
    (h : Γ.strictPeriods = Δ.strictPeriods) : Γ.strictWidthInfty = Δ.strictWidthInfty := by
  unfold strictWidthInfty
  congr! 3 <;> simp [h]

/-- Conjugating by a translation preserves strict periods at infinity. -/
lemma strictPeriods_conj_upperRightHom (Γ : Subgroup (GL (Fin 2) ℝ)) (x : ℝ) :
    (ConjAct.toConjAct (GeneralLinearGroup.upperRightHom x) • Γ).strictPeriods =
      Γ.strictPeriods := by
  ext h
  simp only [mem_strictPeriods_iff, mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, ← AddChar.map_neg_eq_inv,
    ← AddChar.map_add_eq_mul]
  simp [add_comm]

/-- Changing a cusp representative on the right by `T^m` preserves its strict width. -/
@[simp]
lemma strictWidthAt_mul_T_zpow (Γ : Subgroup (GL (Fin 2) ℝ)) (γ : SL(2, ℤ)) (m : ℤ) :
    Γ.strictWidthAt (γ * ModularGroup.T ^ m) = Γ.strictWidthAt γ := by
  unfold strictWidthAt
  change (ConjAct.toConjAct (mapGL ℝ (γ * ModularGroup.T ^ m))⁻¹ • Γ).strictWidthInfty = _
  rw [map_mul, _root_.mul_inv_rev, map_mul, mul_smul]
  apply strictWidthInfty_eq_of_strictPeriods_eq
  have hT (n : ℤ) : mapGL ℝ (ModularGroup.T ^ n) =
      GeneralLinearGroup.upperRightHom (n : ℝ) := by
    apply Units.ext
    rw [mapGL_coe_matrix, map_apply_coe, ModularGroup.coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [← map_inv, ← zpow_neg, hT]
  exact strictPeriods_conj_upperRightHom _ _

/-- Negating a cusp representative preserves its strict width. -/
@[simp]
lemma strictWidthAt_neg (Γ : Subgroup (GL (Fin 2) ℝ)) (γ : SL(2, ℤ)) :
    Γ.strictWidthAt (-γ) = Γ.strictWidthAt γ := by
  unfold strictWidthAt
  have hneg : ((-γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = -(γ : GL (Fin 2) ℝ) := by
    apply Units.ext
    ext i j
    simp
  rw [hneg]
  congr 1
  ext x
  simp only [mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul, inv_inv]
  simp

/-- The strict width depends on the cusp point, rather than its matrix representative. -/
lemma strictWidthAt_eq_of_smul_infty_eq (Γ : Subgroup (GL (Fin 2) ℝ))
    {γ γ' : SL(2, ℤ)}
    (h : (γ' : GL (Fin 2) ℝ) • (∞ : OnePoint ℝ) = (γ : GL (Fin 2) ℝ) • ∞) :
    Γ.strictWidthAt γ' = Γ.strictWidthAt γ := by
  obtain ⟨m, rfl | rfl⟩ := ModularGroup.exists_eq_mul_T_zpow_of_smul_infty_eq h <;> simp

/-- The strict width is constant on cusp orbits of an integral finite-index subgroup. -/
lemma strictWidthAt_eq_of_cuspOrbit_eq (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    {γ γ' : SL(2, ℤ)}
    (h : cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ'⁻¹⟧ =
      cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ⁻¹⟧) :
    (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt γ' =
      (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt γ := by
  obtain ⟨δ, hδ, m, rfl | rfl⟩ := ModularGroup.exists_eq_mul_T_zpow_of_cuspOrbit_eq Γ h
  all_goals
    simp only [strictWidthAt_neg, strictWidthAt_mul_T_zpow]
    exact (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt_mul_left γ δ ⟨δ, hδ, rfl⟩

/-- The strict width at an integral cusp representative is an integer. -/
lemma exists_intCast_strictWidthAt (Γ : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) :
    ∃ n : ℤ, (n : ℝ) = (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt γ := by
  have hm := (ConjAct.toConjAct (γ : GL (Fin 2) ℝ)⁻¹ •
    (Γ : Subgroup (GL (Fin 2) ℝ))).strictWidthInfty_mem_strictPeriods
  rw [mem_strictPeriods_iff] at hm
  obtain ⟨x, ⟨δ, hδ, rfl⟩, hx⟩ := hm
  change (mapGL ℝ γ)⁻¹ * mapGL ℝ δ * mapGL ℝ γ = _ at hx
  have heq : mapGL ℝ (γ⁻¹ * δ * γ) =
      GeneralLinearGroup.upperRightHom
        ((Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt γ) := by
    simpa only [strictWidthAt, map_mul, map_inv] using hx
  refine ⟨(γ⁻¹ * δ * γ) 0 1, ?_⟩
  exact congrArg (fun g : GL (Fin 2) ℝ ↦ g 0 1) heq

/-- The strict width at an integral cusp representative is a natural number. -/
lemma exists_natCast_strictWidthAt (Γ : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) :
    ∃ n : ℕ, (n : ℝ) = (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt γ := by
  obtain ⟨n, hn⟩ := Γ.exists_intCast_strictWidthAt γ
  have hn0 : 0 ≤ n := by
    exact_mod_cast hn ▸ (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt_nonneg γ
  lift n to ℕ using hn0
  exact ⟨n, by simpa using hn⟩

/-- For a finite-index subgroup, every strict cusp width is a positive natural number. -/
lemma exists_pos_natCast_strictWidthAt (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (γ : SL(2, ℤ)) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt γ := by
  obtain ⟨n, hn⟩ := Γ.exists_natCast_strictWidthAt γ
  refine ⟨n, ?_, hn⟩
  exact_mod_cast hn ▸ (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt_pos γ

end Subgroup
