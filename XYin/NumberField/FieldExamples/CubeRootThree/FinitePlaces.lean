/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.PrimeSplitting
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Finite places of `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial
open IsDedekindDomain
open NumberField.FieldExamples

namespace NumberField.CubeRootThree

/-- The finite place over `3`, represented by the totally ramified prime `(θ)`. -/
def heightOneThree : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {thetaInt}
  isPrime := by
    sorry
  ne_bot := by
    sorry

/-- The degree-one prime above `2`, represented by `(θ - 1)`. -/
def heightOneTwoLinear : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {thetaInt - 1}
  isPrime := by
    sorry
  ne_bot := by
    sorry

/-- The degree-two prime above `2`, represented by `(θ² + θ + 1)`. -/
def heightOneTwoQuadratic : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {thetaInt ^ 2 + thetaInt + 1}
  isPrime := by
    sorry
  ne_bot := by
    sorry

/-- The inert finite place above `7`. -/
def heightOneSeven : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {(7 : 𝓞 K)}
  isPrime := by
    sorry
  ne_bot := by
    sorry

/-- One degree-one finite place above `61`. -/
def heightOneSixtyOneFour : HeightOneSpectrum (𝓞 K) where
  asIdeal := primeAbove61 4
  isPrime := by
    sorry
  ne_bot := by
    sorry

/-- One degree-one finite place above `61`. -/
def heightOneSixtyOneFive : HeightOneSpectrum (𝓞 K) where
  asIdeal := primeAbove61 5
  isPrime := by
    sorry
  ne_bot := by
    sorry

/-- One degree-one finite place above `61`. -/
def heightOneSixtyOneFiftyTwo : HeightOneSpectrum (𝓞 K) where
  asIdeal := primeAbove61 52
  isPrime := by
    sorry
  ne_bot := by
    sorry

abbrev vThree : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneThree

theorem vThree_ramificationIdx :
    (Ideal.span {(3 : ℤ)}).ramificationIdx heightOneThree.asIdeal = 3 := by
  sorry

theorem vThree_inertiaDeg :
    (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThree.asIdeal = 1 := by
  sorry

theorem vTwoLinear_inertiaDeg :
    (Ideal.span {(2 : ℤ)}).inertiaDeg heightOneTwoLinear.asIdeal = 1 := by
  sorry

theorem vTwoQuadratic_inertiaDeg :
    (Ideal.span {(2 : ℤ)}).inertiaDeg heightOneTwoQuadratic.asIdeal = 2 := by
  sorry

theorem vSeven_inertiaDeg :
    (Ideal.span {(7 : ℤ)}).inertiaDeg heightOneSeven.asIdeal = 3 := by
  sorry

theorem vSixtyOne_inertiaDegs :
    (Ideal.span {(61 : ℤ)}).inertiaDeg heightOneSixtyOneFour.asIdeal = 1 ∧
      (Ideal.span {(61 : ℤ)}).inertiaDeg heightOneSixtyOneFive.asIdeal = 1 ∧
        (Ideal.span {(61 : ℤ)}).inertiaDeg heightOneSixtyOneFiftyTwo.asIdeal = 1 := by
  sorry

end NumberField.CubeRootThree
