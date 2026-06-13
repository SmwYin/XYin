/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.Units

/-!
# `ℚ(ζ₃)` Class group

This file develops the class group part of the `ℚ(ζ₃)` number field example.
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace NumberField.CyclotomicThree

/-- The ring of integers `ℤ[ζ]` is a principal ideal domain — the ring-theoretic content of
class number one. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing OK :=
  IsCyclotomicExtension.Rat.three_pid K

/-- The class number of `ℚ(ζ₃)` is `1`. -/
theorem classNumber_eq_one : NumberField.classNumber K = 1 :=
  NumberField.classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.three_pid K)

/-- The class group of `𝓞 K` is trivial. -/
theorem classGroupStructure : Nonempty (ClassGroup OK ≃* Multiplicative (ZMod 1)) := by
  have h1 : Nat.card (ClassGroup OK) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup OK) := (Nat.card_eq_one_iff_unique.mp h1).1
  haveI : Unique (ClassGroup OK) := uniqueOfSubsingleton 1
  exact ⟨MulEquiv.ofUnique⟩

/-- The unit ideal as the concrete representative of the unique ideal class. -/
abbrev unitIdealRepresentative : (Ideal OK)⁰ := ⟨(⊤ : Ideal OK), by simp⟩

/-- Every ideal class is represented by the unit ideal. -/
theorem classGroupRepresentative (C : ClassGroup OK) :
    C = ClassGroup.mk0 unitIdealRepresentative := by
  have h1 : Nat.card (ClassGroup OK) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup OK) := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim _ _


end NumberField.CyclotomicThree
