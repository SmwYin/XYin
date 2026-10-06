/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldRayGeometry

/-! # Ideal counts in congruence classes

Janusz IV.2.8, IV.2.13, and IV.2.15–16: each congruence class is a union of equally many
ray classes, so the uniform ray-class count gives a common leading coefficient. This
module does not assume reciprocity or class-field existence.
-/

open NumberField
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]
variable (m : Ideal (𝓞 K))

/-- Janusz IV.2.15: the leading ideal-counting coefficient is independent of the ray class. -/
theorem exists_congruenceClassIdealCount_error (hm : m ≠ ⊥)
    (H : Subgroup (coprimeIdeals K m)) (hH : raySubgroup K m ≤ H) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (c : coprimeIdeals K m ⧸ H) (x : ℝ), 1 ≤ x →
        |(congruenceClassIdealCount K m H c x : ℝ) - κ * x| ≤
          C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  classical
  haveI : (raySubgroup K m).FiniteIndex := raySubgroup_finiteIndex K m hm
  obtain ⟨C₀, hC₀, hC⟩ := exists_rayClassIdealCount_error K m hm
  obtain ⟨h, hh, hfib⟩ := congruenceProjection_uniform_fibers K m hm H hH
  have hκ := rayClassConstant_pos K m hm
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  refine ⟨h * rayClassConstant K m, mul_pos hh' hκ, h * C₀, mul_pos hh' hC₀,
    fun c x hx => ?_⟩
  have hsum := congruenceClassIdealCount_eq_sum_ray K m hm H hH c x
  letI := Fintype.ofFinite {r : coprimeIdeals K m ⧸ raySubgroup K m //
    congruenceProjection K m H hH r = c}
  have hcardF : Fintype.card {r : coprimeIdeals K m ⧸ raySubgroup K m //
      congruenceProjection K m H hH r = c} = h := by
    rw [Fintype.card_eq_nat_card, hfib c]
  rw [hsum]
  push_cast
  have hlead : (h : ℝ) * rayClassConstant K m * x =
      ∑ _r : {r : coprimeIdeals K m ⧸ raySubgroup K m //
        congruenceProjection K m H hH r = c}, rayClassConstant K m * x := by
    rw [Finset.sum_const, Finset.card_univ, hcardF, nsmul_eq_mul]
    ring
  have hxe : 0 ≤ x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := Real.rpow_nonneg (by linarith) _
  rw [hlead, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ r : {r : coprimeIdeals K m ⧸ raySubgroup K m //
          congruenceProjection K m H hH r = c},
          |(congruenceClassIdealCount K m (raySubgroup K m) r.val x : ℝ) -
            rayClassConstant K m * x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : {r : coprimeIdeals K m ⧸ raySubgroup K m //
          congruenceProjection K m H hH r = c},
          C₀ * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) :=
        Finset.sum_le_sum fun r _ => hC r.val x hx
    _ = h * C₀ * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
      rw [Finset.sum_const, Finset.card_univ, hcardF, nsmul_eq_mul]
      ring

end Cox.ClassFieldTheory
