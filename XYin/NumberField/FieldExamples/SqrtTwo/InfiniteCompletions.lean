/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.Embeddings
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.Ramification

/-!
# Infinite completions of `ℚ(√2)`

This file records the archimedean completion viewpoint for the `ℚ(√2)` example.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open NumberField

namespace NumberField.SqrtTwo

/-- The completion of `ℚ(√2)` at an infinite place. -/
abbrev InfiniteCompletion (v : NumberField.InfinitePlace K) : Type :=
  v.Completion

/-- Every infinite completion of `ℚ(√2)` is a real completion. -/
theorem infiniteCompletion_equiv_real (v : NumberField.InfinitePlace K) :
    Nonempty (InfiniteCompletion v ≃+* ℝ) := by
  exact ⟨NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (infinitePlace_isReal v)⟩

/-- The real isomorphism sends the image of `√2` to the expected real absolute value. -/
theorem infiniteCompletion_sqrtTwoRoot_norm (v : NumberField.InfinitePlace K) :
    ‖(algebraMap K (InfiniteCompletion v) sqrtTwoRoot)‖ = Real.sqrt 2 := by
  change ‖(((WithAbs.equiv v.1).symm sqrtTwoRoot : WithAbs v.1) : v.Completion)‖ =
    Real.sqrt 2
  rw [NumberField.InfinitePlace.Completion.norm_coe, (WithAbs.equiv v.1).apply_symm_apply]
  exact infinitePlace_apply_sqrtTwoRoot v

open scoped Classical in
/-- The completion-ramification formula at infinity specializes to the degree `2` of
`ℚ(√2)/ℚ`. -/
theorem infinitePlace_sum_inertiaDeg_eq_two (v : NumberField.InfinitePlace ℚ) :
    ∑ w ∈ v.placesOver K, v.inertiaDeg w = 2 := by
  rw [NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank (K := ℚ) (L := K) v]
  exact degree_eq_two

end NumberField.SqrtTwo
