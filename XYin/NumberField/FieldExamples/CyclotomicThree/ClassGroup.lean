import XYin.NumberField.FieldExamples.CyclotomicThree.Units

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace XYin.NumberField.CyclotomicThree

/-! ## 7. Class group -/

/--
The convex-body version of the Minkowski bound in mathlib is attached to a fractional
ideal. For the trivial fractional ideal it is finite and positive.
-/
abbrev trivialFractionalIdeal : (FractionalIdeal OK⁰ K)ˣ :=
  1

example : 0 < mixedEmbedding.minkowskiBound K trivialFractionalIdeal :=
  mixedEmbedding.minkowskiBound_pos K trivialFractionalIdeal

example : mixedEmbedding.minkowskiBound K trivialFractionalIdeal < ⊤ :=
  mixedEmbedding.minkowskiBound_lt_top K trivialFractionalIdeal

/--
The class-number API presents the class group as a finite type and provides the map
from nonzero integral ideals to ideal classes.
-/
example : Fintype (ClassGroup OK) := by infer_instance

example (C : ClassGroup OK) : ∃ I : (Ideal OK)⁰, ClassGroup.mk0 I = C :=
  ClassGroup.mk0_surjective C

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


end XYin.NumberField.CyclotomicThree
