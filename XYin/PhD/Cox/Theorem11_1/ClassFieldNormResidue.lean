/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormCongruence
import Mathlib.Data.ZMod.Basic

noncomputable section
open NumberField
/-! Interfaces for Janusz III.3.3 and V.5.1.1–5.1.2. The actual readiness proofs are retained
separately.
-/

namespace Cox.ClassFieldTheory

/-- The rational integral norm agrees with the integer determinant norm. -/
theorem rat_intNorm_eq_norm_int (K : Type*) [Field K] [NumberField K]
    (a : 𝓞 K) :
    Rat.ringOfIntegersEquiv (Algebra.intNorm (𝓞 ℚ) (𝓞 K) a) = Algebra.norm ℤ a := by
  apply Int.cast_injective (α := ℚ)
  rw [Rat.ringOfIntegersEquiv_apply_coe, Algebra.coe_norm_int]
  exact Algebra.algebraMap_intNorm (K := ℚ) (L := K) a

/-- A principal finite-ray congruence is preserved by the integer norm. -/
theorem norm_int_zmod_eq_one (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (a : 𝓞 K)
    (ha : a - 1 ∈ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) :
    (Algebra.norm ℤ a : ZMod n) = 1 := by
  have hmap : (Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map (algebraMap (𝓞 ℚ) (𝓞 K)) =
      Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have h := intNorm_sub_one_mem ℚ K (Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))) a
    (by rw [hmap]; exact ha)
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have h2 := congrArg Rat.ringOfIntegersEquiv hc
  rw [map_sub, map_one, rat_intNorm_eq_norm_int, map_mul, map_natCast] at h2
  have h3 : ((Algebra.norm ℤ a - 1 : ℤ) : ZMod n) = 0 := by
    rw [h2]
    push_cast
    simp
  rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at h3
  exact h3

/-- The integer norm of a rational algebraic integer is that same integer. -/
theorem norm_int_rat_eq (a : 𝓞 ℚ) :
    Algebra.norm ℤ a = Rat.ringOfIntegersEquiv a := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int, Rat.ringOfIntegersEquiv_apply_coe]
  convert DFunLike.congr_fun (Algebra.norm_self (R := ℚ)) (a : ℚ)

end Cox.ClassFieldTheory
