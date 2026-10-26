/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryCore
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicBaseChange
import XYin.PhD.Cox.Theorem11_1.ClassFieldResidueIndependence

/-!
# Compatible cyclotomic modulus and residue data

Janusz V.5.3–4, printed160–161/PDF171–172, chooses a single modulus after the finite cyclotomic
capture bound. The root, two residue units and all required coprimalities refer to this same
modulus. Root existence is explicit.
-/

open IntermediateField
noncomputable section
namespace Cox.ClassFieldTheory.ArtinAuxiliary

/-- Janusz V.5.3–4: choose the same modulus, root and independent residue units. -/
theorem exists_cyclotomic_residue_data
    {Ω : Type*} [Field Ω] [CharZero Ω]
    (hroots : ∀ m : ℕ, 0 < m → ∃ ξ : Ω, IsPrimitiveRoot ξ m)
    (L : IntermediateField ℚ Ω) [Finite (IntermediateField ℚ L)]
    (a n s : ℕ) (ha : 2 ≤ a) (hn : 0 < n) (hs : 0 < s) :
    ∃ (m : ℕ) (ξ : Ω), 0 < m ∧ m.Coprime s ∧ m.Coprime a ∧
      IsPrimitiveRoot ξ m ∧ L ⊓ adjoin ℚ {ξ} = ⊥ ∧
      ∃ u v : (ZMod m)ˣ, (u : ZMod m) = a ∧ n ∣ orderOf u ∧ n ∣ orderOf v ∧
        Disjoint (Subgroup.zpowers u) (Subgroup.zpowers v) := by
  obtain ⟨M, hM, hbound⟩ := CyclotomicBaseChange.exists_rational_intersection_bound L
  obtain ⟨m, hm1, -, hlarge, u, v, hu, hnu, hnv, hind⟩ :=
    exists_independent_residue_units a n (max M (max s a)) ha hn
  have hm : 0 < m := by omega
  have hcopM : m.Coprime M := coprime_of_prime_divisors_gt m M _ hM (le_max_left _ _) hlarge
  have hcops : m.Coprime s := coprime_of_prime_divisors_gt m s _ hs
    ((le_max_left _ _).trans (le_max_right _ _)) hlarge
  have hcopa : m.Coprime a := coprime_of_prime_divisors_gt m a _ (by omega)
    ((le_max_right _ _).trans (le_max_right _ _)) hlarge
  obtain ⟨ξ, hξ⟩ := hroots m hm
  exact ⟨m, ξ, hm, hcops, hcopa, hξ, hbound m hm hcopM.symm ξ hξ, u, v, hu, hnu, hnv, hind⟩

end Cox.ClassFieldTheory.ArtinAuxiliary
