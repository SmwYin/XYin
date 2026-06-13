/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.Units

/-!
# `ℚ(√2)` Class group

This file develops the class group part of the `ℚ(√2)` number field example.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

/-- The ring of integers `ℤ[√2]` is a principal ideal domain — the ring-theoretic content of
class number one. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing O2 := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [sqrtTwo_numberField_discr]
  have hfin : Module.finrank ℚ QSqrtTwo = 2 := by
    rw [PowerBasis.finrank sqrtTwoPowerBasis]
    exact sqrtTwoPowerBasis_dim
  rw [hfin]
  have hsig := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := QSqrtTwo)
  rw [hfin] at hsig
  have hnle : NumberField.InfinitePlace.nrComplexPlaces QSqrtTwo ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hnle with hn | hn
  · rw [hn]
    norm_num
  · rw [hn]
    ring_nf
    nlinarith [Real.pi_gt_three]

/-- The class number of `ℚ(√2)` is `1`. The Minkowski bound is `(1/2)·√8 ≈ 1.41`, so every
ideal class contains an ideal of norm `1` and the class group is trivial outright. -/
theorem classNumber_eq_one : NumberField.classNumber QSqrtTwo = 1 := by
  exact NumberField.classNumber_eq_one_iff.mpr isPrincipalIdealRing

/-- The class group of `𝓞 ℚ(√2)` is trivial. -/
theorem classGroupStructure : Nonempty (ClassGroup O2 ≃* Multiplicative (ZMod 1)) := by
  classical
  have hcard : Fintype.card (ClassGroup O2) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup O2) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  exact ⟨MulEquiv.ofBijective (1 : ClassGroup O2 →* Multiplicative (ZMod 1)) (by
    constructor
    · intro a b h
      exact Subsingleton.elim _ _
    · intro y
      exact ⟨1, Subsingleton.elim _ _⟩)⟩

/-- The unit ideal as the concrete representative of the unique ideal class. -/
abbrev unitIdealRepresentative : (Ideal O2)⁰ := ⟨(⊤ : Ideal O2), by simp⟩

/-- Every ideal class is represented by the unit ideal. -/
theorem classGroupRepresentative (C : ClassGroup O2) :
    C = ClassGroup.mk0 unitIdealRepresentative := by
  classical
  have hcard : Fintype.card (ClassGroup O2) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup O2) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  exact Subsingleton.elim _ _


end NumberField.SqrtTwo
