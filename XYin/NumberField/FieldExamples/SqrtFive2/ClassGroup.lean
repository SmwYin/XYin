import XYin.NumberField.FieldExamples.SqrtFive2.Units

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace XYin.NumberField.SqrtFiveGoldenAdjoinRoot

/-! ## 7. Class group -/

/-- The class number of `ℚ(√5)` is `1`. The Minkowski bound is `(1/2)·√5 ≈ 1.12 < 2`, so
every ideal class contains an ideal of norm `1` and the class group is trivial outright. -/
theorem classNumber_eq_one : NumberField.classNumber QSqrtFive = 1 := by
  sorry

/-- The ring of integers `ℤ[φ]` is a principal ideal domain — the ring-theoretic content of
class number one. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 QSqrtFive) := by
  sorry

/-- The class group of `𝓞 K` is trivial. -/
theorem classGroupStructure :
    Nonempty (ClassGroup (𝓞 QSqrtFive) ≃* Multiplicative (ZMod 1)) := by
  sorry

/-- The unit ideal as the concrete representative of the unique ideal class. -/
abbrev unitIdealRepresentative : (Ideal (𝓞 QSqrtFive))⁰ :=
  ⟨(⊤ : Ideal (𝓞 QSqrtFive)), by simp⟩

/-- Every ideal class is represented by the unit ideal. -/
theorem classGroupRepresentative (C : ClassGroup (𝓞 QSqrtFive)) :
    C = ClassGroup.mk0 unitIdealRepresentative := by
  sorry


end XYin.NumberField.SqrtFiveGoldenAdjoinRoot
