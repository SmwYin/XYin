/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.Regulator
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# Infinite adeles of `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

abbrev SqrtNegSixInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

abbrev infinitePrincipalAdele_theta : SqrtNegSixInfiniteAdeleRing :=
  algebraMap K SqrtNegSixInfiniteAdeleRing θ

abbrev infinitePrincipalAdele_torsionGenerator : SqrtNegSixInfiniteAdeleRing :=
  algebraMap K SqrtNegSixInfiniteAdeleRing (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K))

theorem infiniteAdele_norm_theta :
    ‖infinitePrincipalAdele_theta‖ = |Algebra.norm ℚ θ| := by
  sorry

theorem infiniteAdele_denseRange :
    DenseRange (algebraMap K SqrtNegSixInfiniteAdeleRing) := by
  sorry

end NumberField.SqrtNegSix
