/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.Regulator
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# Infinite adeles of `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

abbrev CubeRootThreeInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

abbrev infinitePrincipalAdele_cubeRootThree : CubeRootThreeInfiniteAdeleRing :=
  algebraMap K CubeRootThreeInfiniteAdeleRing cubeRootThree

abbrev infinitePrincipalAdele_fundamentalUnit : CubeRootThreeInfiniteAdeleRing :=
  algebraMap K CubeRootThreeInfiniteAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem infiniteAdele_norm_cubeRootThree :
    ‖infinitePrincipalAdele_cubeRootThree‖ = |Algebra.norm ℚ cubeRootThree| := by
  sorry

theorem infiniteAdele_denseRange :
    DenseRange (algebraMap K CubeRootThreeInfiniteAdeleRing) := by
  sorry

end NumberField.CubeRootThree
