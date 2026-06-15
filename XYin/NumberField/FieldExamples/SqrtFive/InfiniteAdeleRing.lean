/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.Regulator
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# Infinite adeles of `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

abbrev SqrtFiveInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

abbrev infinitePrincipalAdele_goldenRoot : SqrtFiveInfiniteAdeleRing :=
  algebraMap K SqrtFiveInfiniteAdeleRing goldenRoot

abbrev infinitePrincipalAdele_fundamentalUnit : SqrtFiveInfiniteAdeleRing :=
  algebraMap K SqrtFiveInfiniteAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem infiniteAdele_norm_goldenRoot :
    ‖infinitePrincipalAdele_goldenRoot‖ = |Algebra.norm ℚ goldenRoot| := by
  exact NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm goldenRoot

theorem infiniteAdele_denseRange :
    DenseRange (algebraMap K SqrtFiveInfiniteAdeleRing) := by
  exact NumberField.InfiniteAdeleRing.denseRange_algebraMap K

end NumberField.SqrtFive
