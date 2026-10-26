/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldTheory

/-! # Ideal counts in congruence classes
Janusz IV.2.8, IV.2.13, and IV.2.15–16. The uniform ray-class counting theorem
uses a source-local geometric decomposition. This module does not
assume reciprocity or class-field existence.
-/

open NumberField
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]
variable (m : Ideal (𝓞 K))

/-- Integral ideals in a class of the prime-to-modulus ideal group. -/
def integralIdealsInCongruenceClass (H : Subgroup (coprimeIdeals K m))
    (c : coprimeIdeals K m ⧸ H) : Set (Ideal (𝓞 K)) :=
  {A | A ≠ ⊥ ∧ A ⊔ m = ⊤ ∧ ∃ u : coprimeIdeals K m,
    ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = A ∧
      QuotientGroup.mk u = c}

/-- The source's summatory ideal-counting function in a congruence class. -/
def congruenceClassIdealCount (H : Subgroup (coprimeIdeals K m))
    (c : coprimeIdeals K m ⧸ H) (x : ℝ) : ℕ :=
  Nat.card {A : Ideal (𝓞 K) // A ∈ integralIdealsInCongruenceClass K m H c ∧
    (A.absNorm : ℝ) ≤ x}

/-- A group containing the ray subgroup has finite index. -/
theorem finiteIndex_of_raySubgroup_le (hm : m ≠ ⊥)
    (H : Subgroup (coprimeIdeals K m)) (hH : raySubgroup K m ≤ H) : H.FiniteIndex := by
  haveI := raySubgroup_finiteIndex K m hm
  exact Subgroup.finiteIndex_of_le hH

end Cox.ClassFieldTheory
