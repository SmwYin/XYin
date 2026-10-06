/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldKummer

/-!
# Replacing radical generators by supported representatives

Janusz V.9.3, printed175/PDF186. This algebraic generator replacement does not
assert the later arithmetic unramifiedness step.
-/

noncomputable section
namespace Cox.ClassFieldTheory

/-- Janusz V.9.3: inclusion of radicands gives inclusion of their radical fields. -/
theorem radicalField_mono (K : Type*) [Field K] (n : ℕ)
    {V W : Subgroup Kˣ} (h : V ≤ W) : radicalField K n V ≤ radicalField K n W := by
  rw [radicalField, IntermediateField.adjoin_le_iff]
  rintro x ⟨w, hw, hx⟩
  exact IntermediateField.subset_adjoin K _ ⟨w, h hw, hx⟩

/-- Janusz V.9.3: multiplying radicands by base nth powers does not change the radical field. -/
theorem radicalField_sup_nthPowers (K : Type*) [Field K] (n : ℕ) (V : Subgroup Kˣ) :
    radicalField K n (V ⊔ nthPowers K n) = radicalField K n V := by
  refine le_antisymm ?_ (radicalField_mono K n le_sup_left)
  rw [radicalField, IntermediateField.adjoin_le_iff]
  rintro x ⟨w, hw, hx⟩
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hw
  obtain ⟨v, rfl⟩ := hc
  have hv0 : algebraMap K (AlgebraicClosure K) (v : K) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero v)
  have hy : (x / algebraMap K (AlgebraicClosure K) (v : K)) ^ n =
      algebraMap K (AlgebraicClosure K) (a : K) := by
    rw [div_pow, hx, ← map_pow, ← map_div₀, powMonoidHom_apply, Units.val_mul,
      Units.val_pow_eq_pow_val, mul_div_cancel_right₀ _ (pow_ne_zero _ (Units.ne_zero v))]
  have hymem : x / algebraMap K (AlgebraicClosure K) (v : K) ∈ radicalField K n V :=
    IntermediateField.subset_adjoin K _ ⟨a, ha, hy⟩
  have hxy : x = x / algebraMap K (AlgebraicClosure K) (v : K) *
      algebraMap K (AlgebraicClosure K) (v : K) := (div_mul_cancel₀ _ hv0).symm
  rw [SetLike.mem_coe, hxy]
  exact IntermediateField.mul_mem _ hymem (IntermediateField.algebraMap_mem _ _)

/-- Janusz V.9.3: supported radicands up to base powers generate a supported radical field. -/
theorem radicalField_le_of_le_sup_nthPowers (K : Type*) [Field K] (n : ℕ)
    {V W : Subgroup Kˣ} (h : W ≤ V ⊔ nthPowers K n) :
    radicalField K n W ≤ radicalField K n V := by
  exact (radicalField_mono K n h).trans (radicalField_sup_nthPowers K n V).le

end Cox.ClassFieldTheory
