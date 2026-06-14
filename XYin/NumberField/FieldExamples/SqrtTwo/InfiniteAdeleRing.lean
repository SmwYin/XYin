/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.Embeddings
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# Infinite adeles of `ℚ(√2)`

This file specializes mathlib's infinite adele ring API to the standard generator and
fundamental unit of `ℚ(√2)`.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open NumberField

namespace NumberField.SqrtTwo

/-- The infinite adele ring of `ℚ(√2)`. -/
abbrev SqrtTwoInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

/-- The principal infinite adele attached to `√2`. -/
abbrev infinitePrincipalAdele_sqrtTwoRoot : SqrtTwoInfiniteAdeleRing :=
  algebraMap K SqrtTwoInfiniteAdeleRing sqrtTwoRoot

/-- The principal infinite adele attached to the fundamental unit `1 + √2`. -/
abbrev infinitePrincipalAdele_fundamentalUnit : SqrtTwoInfiniteAdeleRing :=
  algebraMap K SqrtTwoInfiniteAdeleRing
    (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K))

theorem infiniteAdele_norm_sqrtTwoRoot :
    ‖infinitePrincipalAdele_sqrtTwoRoot‖ = |Algebra.norm ℚ sqrtTwoRoot| := by
  sorry

theorem infiniteAdele_norm_fundamentalUnit :
    ‖infinitePrincipalAdele_fundamentalUnit‖ =
      |Algebra.norm ℚ (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K))| := by
  sorry

theorem infiniteAdele_denseRange :
    DenseRange (algebraMap K SqrtTwoInfiniteAdeleRing) := by
  sorry

end NumberField.SqrtTwo
