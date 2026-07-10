/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NFIL.NumberField.FieldExamples.CyclotomicThree.PrimeSplitting

/-!
# `ℚ(ζ₃)` ClassGroup

Fractional ideals, ideal representatives, class number, PID/UFD consequences, and class group
structure.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Fractional Ideals
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicThree

abbrev zetaFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanSingleton (𝓞 K)⁰ ζ

abbrev ramifiedPrimeFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  (Ideal.span {zetaInt - 1} : FractionalIdeal (𝓞 K)⁰ K)

theorem zeta_mem_fractionalIdeal :
    ζ ∈ zetaFractionalIdeal := by
  exact FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ ζ

theorem zetaFractionalIdeal_absNorm :
    FractionalIdeal.absNorm zetaFractionalIdeal = |Algebra.norm ℚ ζ| := by
  rw [zetaFractionalIdeal, FractionalIdeal.absNorm_span_singleton]

theorem ramifiedPrimeFractionalIdeal_ne_zero :
    ramifiedPrimeFractionalIdeal ≠ 0 := by
  haveI : IsCyclotomicExtension {3 ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {3} ℚ K)
  have hζ : IsPrimitiveRoot ζ (3 ^ (0 + 1)) := by
    change IsPrimitiveRoot ζ 3
    exact zeta_isPrimitiveRoot
  exact FractionalIdeal.coeIdeal_ne_zero.mpr
    (IsCyclotomicExtension.Rat.span_zeta_sub_one_ne_bot (p := 3) (k := 0) hζ)

end NumberField.CyclotomicThree


/-!
## Class Group
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace NumberField.CyclotomicThree

/-- The ring of integers `ℤ[ζ]` is a principal ideal domain — the ring-theoretic content of
class number one. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 K) :=
  IsCyclotomicExtension.Rat.three_pid K

/-- The ring of integers `ℤ[ζ]` is a unique factorization monoid. -/
theorem uniqueFactorizationMonoid : UniqueFactorizationMonoid (𝓞 K) := by
  haveI : IsPrincipalIdealRing (𝓞 K) := isPrincipalIdealRing
  infer_instance

/-- The class number of `ℚ(ζ₃)` is `1`. -/
theorem classNumber_eq_one : NumberField.classNumber K = 1 :=
  NumberField.classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.three_pid K)

/-- The class group of `𝓞 K` is trivial. -/
theorem classGroupStructure : Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1)) := by
  have h1 : Nat.card (ClassGroup (𝓞 K)) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup (𝓞 K)) := (Nat.card_eq_one_iff_unique.mp h1).1
  haveI : Unique (ClassGroup (𝓞 K)) := uniqueOfSubsingleton 1
  exact ⟨MulEquiv.ofUnique⟩

/-- The unit ideal as the concrete representative of the unique ideal class. -/
abbrev unitIdealRepresentative : (Ideal (𝓞 K))⁰ := ⟨(⊤ : Ideal (𝓞 K)), by simp⟩

/-- Every ideal class is represented by the unit ideal. -/
theorem classGroupRepresentative (C : ClassGroup (𝓞 K)) :
    C = ClassGroup.mk0 unitIdealRepresentative := by
  have h1 : Nat.card (ClassGroup (𝓞 K)) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup (𝓞 K)) := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim _ _


end NumberField.CyclotomicThree
