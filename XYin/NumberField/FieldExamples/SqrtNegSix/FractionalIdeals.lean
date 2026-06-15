/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.PrimeSplitting
import Mathlib.NumberTheory.NumberField.FractionalIdeal

/-!
# Fractional ideals of `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

abbrev thetaFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanSingleton (𝓞 K)⁰ θ

abbrev primeAboveTwoFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  (primeAboveTwo : FractionalIdeal (𝓞 K)⁰ K)

abbrev primeAboveThreeFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  (primeAboveThree : FractionalIdeal (𝓞 K)⁰ K)

theorem theta_mem_fractionalIdeal :
    θ ∈ thetaFractionalIdeal := by
  exact FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ θ

theorem thetaFractionalIdeal_absNorm :
    FractionalIdeal.absNorm thetaFractionalIdeal = |Algebra.norm ℚ θ| := by
  simp [thetaFractionalIdeal]

theorem ramifiedFractionalIdeals_ne_zero :
    primeAboveTwoFractionalIdeal ≠ 0 ∧ primeAboveThreeFractionalIdeal ≠ 0 := by
  constructor
  · exact FractionalIdeal.coeIdeal_ne_zero.mpr (by
      intro hbot
      have hnorm := absNorm_primeAboveTwo
      rw [hbot] at hnorm
      norm_num at hnorm)
  · exact FractionalIdeal.coeIdeal_ne_zero.mpr (by
      intro hbot
      have hnorm := absNorm_primeAboveThree
      rw [hbot] at hnorm
      norm_num at hnorm)

end NumberField.SqrtNegSix
