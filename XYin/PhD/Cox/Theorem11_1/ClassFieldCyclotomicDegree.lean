/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.GroupTheory.Coset.Card
import Mathlib.FieldTheory.Finite.Basic

/-!
# The cyclotomic degree divides the exponent group order

This is the faithful exponent action used in Janusz V.11.2, printed186/PDF197. The theorem is stated
over arbitrary fields.
-/

noncomputable section
namespace Cox.ClassFieldTheory

/-- Lagrange applied to the faithful cyclotomic exponent action bounds the degree by
divisibility. -/
theorem cyclotomic_finrank_dvd_card_units
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} K E] :
    Module.finrank K E ∣ Nat.card (ZMod n)ˣ := by
  haveI := IsCyclotomicExtension.finiteDimensional {n} K E
  haveI := IsCyclotomicExtension.isGalois {n} K E
  have hζ := IsCyclotomicExtension.zeta_spec n K E
  rw [← IsGalois.card_aut_eq_finrank K E]
  exact Subgroup.card_dvd_of_injective (hζ.autToPow K) (hζ.autToPow_injective K)

end Cox.ClassFieldTheory
