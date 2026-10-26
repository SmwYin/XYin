/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldExistence

/-! # Conductor avoidance and equivalent moduli

The supremum definition of the finite conductor directly gives this instance of
Janusz V.6's defining-modulus characterization: the conductor fails to lie below an ideal
exactly when some defining modulus does. The test ideal is arbitrary.
-/

open NumberField
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- A supremum fails to lie below an ideal exactly when one defining modulus does. -/
theorem conductor_not_le_iff_exists_equivalent_modulus (H : CongruenceSubgroup K)
    (q : Ideal (𝓞 K)) :
    ¬idealGroupConductor K H ≤ q ↔
      ∃ J : CongruenceSubgroup K, CongruenceEquivalent K H J ∧ ¬J.modulus ≤ q := by
  rw [idealGroupConductor, sSup_le_iff]
  constructor
  · intro h
    by_contra hcon
    apply h
    rintro m ⟨J, hHJ, rfl⟩
    by_contra hn
    exact hcon ⟨J, hHJ, hn⟩
  · rintro ⟨J, hHJ, hJ⟩ h
    exact hJ (h _ ⟨J, hHJ, rfl⟩)

end Cox.ClassFieldTheory
