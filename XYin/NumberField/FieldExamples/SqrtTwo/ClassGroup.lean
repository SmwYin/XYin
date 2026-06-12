import XYin.NumberField.FieldExamples.SqrtTwo.Units

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace XYin.NumberField.SqrtTwo

/-! ## 7. Class group -/

example : Fintype (ClassGroup O2) := by infer_instance

example (C : ClassGroup O2) : ∃ I : (Ideal O2)⁰, ClassGroup.mk0 I = C :=
  ClassGroup.mk0_surjective C

abbrev trivialFractionalIdealSqrtTwo : (FractionalIdeal O2⁰ QSqrtTwo)ˣ :=
  1

example : 0 < mixedEmbedding.minkowskiBound QSqrtTwo trivialFractionalIdealSqrtTwo :=
  mixedEmbedding.minkowskiBound_pos QSqrtTwo trivialFractionalIdealSqrtTwo

example : mixedEmbedding.minkowskiBound QSqrtTwo trivialFractionalIdealSqrtTwo < ⊤ :=
  mixedEmbedding.minkowskiBound_lt_top QSqrtTwo trivialFractionalIdealSqrtTwo

theorem sqrtTwo_ringOfIntegers_isPrincipalIdealRing :
    IsPrincipalIdealRing O2 := by
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

theorem sqrtTwo_numberField_classNumber :
    NumberField.classNumber QSqrtTwo = 1 :=
  NumberField.classNumber_eq_one_iff.mpr sqrtTwo_ringOfIntegers_isPrincipalIdealRing

/-- The class group of `𝓞 ℚ(√2)` is trivial. -/
theorem classGroupStructure : Nonempty (ClassGroup O2 ≃* Multiplicative (ZMod 1)) := by
  classical
  have hcard : Fintype.card (ClassGroup O2) = 1 := by
    simpa [NumberField.classNumber] using sqrtTwo_numberField_classNumber
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
    simpa [NumberField.classNumber] using sqrtTwo_numberField_classNumber
  haveI : Subsingleton (ClassGroup O2) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  exact Subsingleton.elim _ _


end XYin.NumberField.SqrtTwo
