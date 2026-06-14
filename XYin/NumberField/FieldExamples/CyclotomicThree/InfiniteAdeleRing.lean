/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.Regulator
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# Infinite adeles of `ℚ(ζ₃)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicThree

abbrev CyclotomicThreeInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

abbrev infinitePrincipalAdele_zeta : CyclotomicThreeInfiniteAdeleRing :=
  algebraMap K CyclotomicThreeInfiniteAdeleRing ζ

abbrev infinitePrincipalAdele_etaUnit : CyclotomicThreeInfiniteAdeleRing :=
  algebraMap K CyclotomicThreeInfiniteAdeleRing (algebraMap (𝓞 K) K (etaUnit : 𝓞 K))

theorem infiniteAdele_norm_zeta :
    ‖infinitePrincipalAdele_zeta‖ = |Algebra.norm ℚ ζ| := by
  sorry

theorem infiniteAdele_denseRange :
    DenseRange (algebraMap K CyclotomicThreeInfiniteAdeleRing) := by
  sorry

end NumberField.CyclotomicThree
