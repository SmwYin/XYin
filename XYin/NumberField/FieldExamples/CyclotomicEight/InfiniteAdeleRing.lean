/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.Regulator
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# Infinite adeles of `ℚ(ζ₈)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

abbrev CyclotomicEightInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

abbrev infinitePrincipalAdele_zeta : CyclotomicEightInfiniteAdeleRing :=
  algebraMap K CyclotomicEightInfiniteAdeleRing ζ

abbrev infinitePrincipalAdele_fundamentalUnit : CyclotomicEightInfiniteAdeleRing :=
  algebraMap K CyclotomicEightInfiniteAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem infiniteAdele_norm_zeta :
    ‖infinitePrincipalAdele_zeta‖ = |Algebra.norm ℚ ζ| := by
  sorry

theorem infiniteAdele_denseRange :
    DenseRange (algebraMap K CyclotomicEightInfiniteAdeleRing) := by
  sorry

end NumberField.CyclotomicEight
