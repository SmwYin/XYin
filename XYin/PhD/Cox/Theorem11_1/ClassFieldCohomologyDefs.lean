/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # Janusz's cyclic Tate groups and Herbrand quotient

The quotient convention is H¹/H⁰_Tate. Coefficient-general quotient definitions
permit the local normal-basis lattice to use its actual valuation-ring coefficients.
-/

noncomputable section

namespace Cox.CyclicCohomology

variable {G A : Type*} [Group G] [Fintype G] [AddCommGroup A]
section Coefficients
variable {R : Type*} [CommRing R] [Module R A]

/-- Janusz V.1: invariants modulo norms, using the generator-difference kernel. -/
abbrev tateZero (ρ : Representation R G A) (g : G) :=
  (LinearMap.ker (ρ g - LinearMap.id)) ⧸
    (LinearMap.range ρ.norm).comap (LinearMap.ker (ρ g - LinearMap.id)).subtype

/-- Janusz V.1: norm-one cycles modulo generator differences. -/
abbrev tateOne (ρ : Representation R G A) (g : G) :=
  (LinearMap.ker ρ.norm) ⧸
    (LinearMap.range (ρ g - LinearMap.id)).comap (LinearMap.ker ρ.norm).subtype

/-- The source's ratio, with finiteness supplied separately when it is used. -/
def herbrandQuotient (ρ : Representation R G A) (g : G) : ℚ :=
  (Nat.card (tateOne ρ g) : ℚ) / Nat.card (tateZero ρ g)

/-- Both cyclic cohomology quotients must be finite before cardinal cancellation. -/
def FiniteHerbrand (ρ : Representation R G A) (g : G) : Prop :=
  Finite (tateZero ρ g) ∧ Finite (tateOne ρ g)

end Coefficients

variable (ρ : Representation ℤ G A) (g : G)

/-- Norms are invariant under the generator. -/
theorem range_norm_le_ker_difference :
    LinearMap.range ρ.norm ≤ LinearMap.ker (ρ g - LinearMap.id) := by
  rintro _ ⟨x, rfl⟩
  simp [LinearMap.mem_ker, Representation.self_norm_apply]

/-- Generator differences have norm zero. -/
theorem range_difference_le_ker_norm :
    LinearMap.range (ρ g - LinearMap.id) ≤ LinearMap.ker ρ.norm := by
  rintro _ ⟨x, rfl⟩
  simp [LinearMap.mem_ker, Representation.norm_self_apply]

end Cox.CyclicCohomology
