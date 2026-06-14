/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.Regulator
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# Infinite adeles of `ℚ(ζ₅)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

abbrev CyclotomicFiveInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

abbrev infinitePrincipalAdele_zeta : CyclotomicFiveInfiniteAdeleRing :=
  algebraMap K CyclotomicFiveInfiniteAdeleRing ζ

abbrev infinitePrincipalAdele_fundamentalUnit : CyclotomicFiveInfiniteAdeleRing :=
  algebraMap K CyclotomicFiveInfiniteAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem infiniteAdele_norm_zeta :
    ‖infinitePrincipalAdele_zeta‖ = |Algebra.norm ℚ ζ| := by
  sorry

theorem infiniteAdele_denseRange :
    DenseRange (algebraMap K CyclotomicFiveInfiniteAdeleRing) := by
  sorry

end NumberField.CyclotomicFive
