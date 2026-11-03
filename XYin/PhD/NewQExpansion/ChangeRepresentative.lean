/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
module

public import XYin.PhD.NewQExpansion.CuspRepresentatives

/-!
# Changing a cusp representative

Changing a representative by a matrix in the level group leaves its q-expansion unchanged.
Right multiplication by a power of `T` rescales the q-coordinate, and negating the matrix
multiplies the expansion by `(-1)^k`. The analytic statements in this file use global
holomorphy and boundedness at infinity.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm Function
open scoped MatrixGroups Manifold Pointwise

namespace Function.Periodic

lemma qParam_add (h : ℝ) (z w : ℂ) :
    qParam h (z + w) = qParam h z * qParam h w := by
  simp [qParam, mul_add, add_div, Complex.exp_add]

/-- An integral translation changes an integral-width q-coordinate by a root of unity. -/
lemma isOfFinOrder_qParam_natCast_int (N : ℕ) (hN : 0 < N) (m : ℤ) :
    IsOfFinOrder (qParam (N : ℝ) (m : ℂ)) := by
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨N, hN, ?_⟩
  rw [qParam, ← Complex.exp_nat_mul]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  push_cast
  rw [mul_div_cancel₀ _ hNc]
  simpa [mul_comm, mul_left_comm, mul_assoc] using Complex.exp_int_mul_two_pi_mul_I m

end Function.Periodic

namespace ModularForm

/-- Slashing by an integral translation translates the argument. -/
lemma SL_slash_T_zpow (f : ℍ → ℂ) (k m : ℤ) :
    f ∣[k] (ModularGroup.T ^ m : SL(2, ℤ)) = fun τ ↦ f ((m : ℝ) +ᵥ τ) := by
  funext τ
  rw [SL_slash_apply, modular_T_zpow_smul, ModularGroup.denom_apply]
  simp [ModularGroup.coe_T_zpow]

/-- Negating the representative matrix multiplies the slash transform by `(-1)^k`. -/
lemma SL_slash_neg_matrix (f : ℍ → ℂ) (k : ℤ) (γ : SL(2, ℤ)) :
    f ∣[k] (-γ) = (-1 : ℂ) ^ k • (f ∣[k] γ) := by
  ext τ
  simp only [SL_slash_apply, ModularGroup.SL_neg_smul, Pi.smul_apply, smul_eq_mul]
  have hd : denom (-γ : SL(2, ℤ)) τ = -denom γ τ := by
    simp [denom, add_comm]
  rw [hd, neg_eq_neg_one_mul, mul_zpow]
  have hk : (-1 : ℂ) ^ (-k) = (-1 : ℂ) ^ k := by
    rw [zpow_neg, ← inv_zpow, inv_neg_one]
  rw [hk]
  ring

end ModularForm

namespace UpperHalfPlane

/-- Integral translation multiplies the `n`th q-expansion coefficient by the `n`th power
of the corresponding q-coordinate. -/
lemma qExpansion_slash_T_zpow_coeff {f : ℍ → ℂ} {h : ℝ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (k m : ℤ) (n : ℕ) :
    (qExpansion h (f ∣[k] (ModularGroup.T ^ m : SL(2, ℤ)))).coeff n =
      (qExpansion h f).coeff n * Periodic.qParam h m ^ n := by
  have hfv (τ : ℍ) : f (h +ᵥ τ) = f τ := by
    simpa only [comp_apply, add_comm (τ : ℂ) (h : ℂ), ← coe_vadd, ofComplex_apply]
      using hfper (τ : ℂ)
  have hper : Periodic ((f ∣[k] (ModularGroup.T ^ m : SL(2, ℤ))) ∘ ofComplex) h := by
    apply UpperHalfPlane.periodic_comp_ofComplex
    intro τ
    simp only [SL_slash_T_zpow]
    rw [vadd_comm, hfv]
  have hhol : MDiff (f ∣[k] (ModularGroup.T ^ m : SL(2, ℤ))) :=
    hfhol.slash k (ModularGroup.T ^ m : SL(2, ℤ))
  have hbdd : IsBoundedAtImInfty (f ∣[k] (ModularGroup.T ^ m : SL(2, ℤ))) := by
    apply hfbdd.slash k
    change Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ m) 1 0 = 0
    simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe]
    simp [ModularGroup.coe_T_zpow]
  let : FunLike (ℍ → ℂ) ℍ ℂ := { coe := id, coe_injective := fun _ _ h ↦ h }
  symm
  apply qExpansion_coeff_unique (f ∣[k] (ModularGroup.T ^ m : SL(2, ℤ))) hh
    (analyticAt_cuspFunction_zero hh hper hhol hbdd)
    (c := fun j ↦ (qExpansion h f).coeff j * Periodic.qParam h m ^ j)
  intro τ
  convert hasSum_qExpansion hh hfper hfhol hfbdd ((m : ℝ) +ᵥ τ) using 1
  · funext j
    simp [coe_vadd, Periodic.qParam_add, mul_pow, smul_eq_mul, mul_assoc]
  · rw [SL_slash_T_zpow]
    rfl

end UpperHalfPlane

namespace SlashInvariantForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
  (f : SlashInvariantForm Γ k) {γ : SL(2, ℤ)}

/-- The coefficient formula for changing the representative from `γ` to `γ * T^m`. -/
lemma qExpansionAt_mul_T_zpow_coeff
    (hh : 0 < Γ.strictWidthAt γ)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k] γ)) (m : ℤ) (n : ℕ) :
    (f.qExpansionAt (γ * ModularGroup.T ^ m)).coeff n =
      Periodic.qParam (Γ.strictWidthAt γ) m ^ n * (f.qExpansionAt γ).coeff n := by
  simpa only [qExpansionAt, Subgroup.strictWidthAt_mul_T_zpow,
    SlashAction.slash_mul, mul_comm] using
    qExpansion_slash_T_zpow_coeff hh (f.periodic_slash_strictWidthAt γ) hfhol hfbdd k m n

/-- Changing the representative by `T^m` rescales the power series variable. -/
lemma qExpansionAt_mul_T_zpow
    (hh : 0 < Γ.strictWidthAt γ)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k] γ)) (m : ℤ) :
    f.qExpansionAt (γ * ModularGroup.T ^ m) =
      PowerSeries.rescale (Periodic.qParam (Γ.strictWidthAt γ) m) (f.qExpansionAt γ) := by
  ext n
  rw [PowerSeries.coeff_rescale, f.qExpansionAt_mul_T_zpow_coeff hh hfhol hfbdd]

/-- Negating the representative matrix multiplies its q-expansion by the weight sign. -/
lemma qExpansionAt_neg_matrix
    (hh : 0 < Γ.strictWidthAt γ)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k] γ)) :
    f.qExpansionAt (-γ) = (-1 : ℂ) ^ k • f.qExpansionAt γ := by
  rw [qExpansionAt, Γ.strictWidthAt_neg, SL_slash_neg_matrix]
  exact qExpansion_smul
    (analyticAt_cuspFunction_zero hh (f.periodic_slash_strictWidthAt γ) hfhol hfbdd) _

/-- The coefficient formula for a signed integral translation of the representative. -/
lemma qExpansionAt_neg_mul_T_zpow_coeff
    (hh : 0 < Γ.strictWidthAt γ)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k] γ)) (m : ℤ) (n : ℕ) :
    (f.qExpansionAt (-(γ * ModularGroup.T ^ m))).coeff n =
      (-1 : ℂ) ^ k * Periodic.qParam (Γ.strictWidthAt γ) m ^ n *
        (f.qExpansionAt γ).coeff n := by
  have hhol : MDiff ((f : ℍ → ℂ) ∣[k] (γ * ModularGroup.T ^ m)) := by
    rw [SlashAction.slash_mul]
    exact hfhol.slash k (ModularGroup.T ^ m : SL(2, ℤ))
  have hbdd : IsBoundedAtImInfty ((f : ℍ → ℂ) ∣[k] (γ * ModularGroup.T ^ m)) := by
    rw [SlashAction.slash_mul]
    apply hfbdd.slash k
    change Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ m) 1 0 = 0
    simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe]
    simp [ModularGroup.coe_T_zpow]
  rw [f.qExpansionAt_neg_matrix (by simpa using hh) hhol hbdd,
    PowerSeries.coeff_smul, smul_eq_mul,
    f.qExpansionAt_mul_T_zpow_coeff hh hfhol hfbdd, mul_assoc]

section IntegralSubgroup

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
  (f : SlashInvariantForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) {γ γ' : SL(2, ℤ)}

/-- Representatives of the same cusp orbit have coefficients related by a weight sign
and powers of a single root of unity. The phase is explicitly `exp (2π i m / h)`.
Only the slash transform at the original representative needs analytic hypotheses. -/
lemma exists_qExpansionAt_coeff_eq_of_cuspOrbit_eq
    (h : cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ'⁻¹⟧ =
      cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ⁻¹⟧)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k] γ)) :
    ∃ (ε : ℂ) (m : ℤ), (ε = 1 ∨ ε = -1) ∧
      IsOfFinOrder (Periodic.qParam ((Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt γ) m) ∧
      ∀ n : ℕ, (f.qExpansionAt γ').coeff n =
        ε ^ k * Periodic.qParam ((Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt γ) m ^ n *
          (f.qExpansionAt γ).coeff n := by
  obtain ⟨δ, hδ, m, hm⟩ := ModularGroup.exists_eq_mul_T_zpow_of_cuspOrbit_eq Γ h
  have hδ' : (δ : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) := ⟨δ, hδ, rfl⟩
  have hh := (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt_pos γ
  obtain ⟨N, hN, hwidth⟩ := Γ.exists_pos_natCast_strictWidthAt γ
  have hphase : IsOfFinOrder
      (Periodic.qParam ((Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthAt γ) m) := by
    rw [← hwidth]
    exact Periodic.isOfFinOrder_qParam_natCast_int N hN m
  rcases hm with rfl | rfl
  · refine ⟨1, m, Or.inl rfl, hphase, ?_⟩
    intro n
    rw [mul_assoc, f.qExpansionAt_mul_left _ δ hδ']
    simpa using f.qExpansionAt_mul_T_zpow_coeff hh hfhol hfbdd m n
  · refine ⟨-1, m, Or.inr rfl, hphase, ?_⟩
    intro n
    rw [mul_assoc, ← mul_neg, f.qExpansionAt_mul_left _ δ hδ']
    exact f.qExpansionAt_neg_mul_T_zpow_coeff hh hfhol hfbdd m n

/-- Changing the representative within a cusp orbit preserves each coefficient's norm. -/
lemma qExpansionAt_coeff_norm_eq_of_cuspOrbit_eq
    (h : cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ'⁻¹⟧ =
      cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ⁻¹⟧)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k] γ)) (n : ℕ) :
    ‖(f.qExpansionAt γ').coeff n‖ = ‖(f.qExpansionAt γ).coeff n‖ := by
  obtain ⟨ε, m, hε, -, hcoeff⟩ :=
    f.exists_qExpansionAt_coeff_eq_of_cuspOrbit_eq h hfhol hfbdd
  rw [hcoeff n, norm_mul, norm_mul, norm_zpow, norm_pow]
  rcases hε with rfl | rfl <;> simp [Periodic.norm_qParam]

/-- The vanishing of a coefficient is independent of the representative of its cusp orbit. -/
lemma qExpansionAt_coeff_eq_zero_iff_of_cuspOrbit_eq
    (h : cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ'⁻¹⟧ =
      cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ⁻¹⟧)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k] γ)) (n : ℕ) :
    (f.qExpansionAt γ').coeff n = 0 ↔ (f.qExpansionAt γ).coeff n = 0 := by
  rw [← norm_eq_zero, f.qExpansionAt_coeff_norm_eq_of_cuspOrbit_eq h hfhol hfbdd,
    norm_eq_zero]

end IntegralSubgroup

end SlashInvariantForm
