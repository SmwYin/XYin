/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalApproximation
import Mathlib.Order.ModularLattice

/-! # The approximation and group steps of Janusz V.3.3–3.4

These steps do not depend on the completion norm formula or a Galois action.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory

/-- The relative-index comparison underlying the second quotient in Janusz V.3.3. -/
theorem sup_relIndex_eq_inf_sup_of_le {G : Type*} [CommGroup G]
    (N H P : Subgroup G) (hP : P ≤ H) :
    (N ⊔ P).relIndex (N ⊔ H) = ((N ⊓ H) ⊔ P).relIndex H := by
  have h1 : N ⊔ H = (N ⊔ P) ⊔ H := by rw [sup_assoc, sup_eq_right.mpr hP]
  have h2 : (N ⊔ P) ⊓ H = (N ⊓ H) ⊔ P := by
    apply le_antisymm
    · rintro x ⟨hx, hxH⟩
      obtain ⟨n, hn, p, hp, rfl⟩ := Subgroup.mem_sup.mp hx
      have hnH : n ∈ H := by
        have h := H.mul_mem hxH (H.inv_mem (hP hp))
        rwa [mul_inv_cancel_right] at h
      exact Subgroup.mul_mem_sup ⟨hn, hnH⟩ hp
    · exact sup_le (inf_le_inf_right H le_sup_left) (le_inf le_sup_right hP)
  rw [h1, Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, h2]

/-- Janusz V.3.3(b): split off the index contributed by the valuation factor. -/
theorem index_sup_factorization {G : Type*} [CommGroup G]
    (N H P : Subgroup G) (hP : P ≤ H) :
    (N ⊔ P).index = (N ⊔ H).index * ((N ⊓ H) ⊔ P).relIndex H := by
  have hle : N ⊔ P ≤ N ⊔ H := sup_le_sup_left hP N
  rw [← Subgroup.relIndex_mul_index hle, sup_relIndex_eq_inf_sup_of_le N H P hP, mul_comm]

variable (L : Type*) [Field L] [hNL : NumberField L]
include hNL

/-- Finite approximation can prescribe multiplicative local ray errors independently. -/
theorem exists_global_localRay_approx (S : Finset (HeightOneSpectrum (𝓞 L)))
    (β : (w : S) → (w.1.adicCompletion L)ˣ) (t : S → ℕ) :
    ∃ γ : Lˣ, ∀ w : S,
      completionUnitMap L w.1 γ * (β w)⁻¹ ∈ localFieldUnitFiltration L w.1 (t w) := by
  choose N hN using fun w : S => exists_precision_for_localRay L w.1 (t w) (β w)
  obtain ⟨γ, hγ⟩ := exists_global_unit_approx L S β N
  exact ⟨γ, fun w => hN w (completionUnitMap L w.1 γ) (hγ w)⟩

/-- Janusz V.3.4: approximate β at the selected prime and 1 at all the others. -/
theorem exists_selected_localRay_approx (S : Finset (HeightOneSpectrum (𝓞 L)))
    (w : HeightOneSpectrum (𝓞 L)) (hw : w ∈ S) (β : (w.adicCompletion L)ˣ) (t : ℕ) :
    ∃ γ : Lˣ, completionUnitMap L w γ * β⁻¹ ∈ localFieldUnitFiltration L w t ∧
      ∀ w' ∈ S, w' ≠ w → completionUnitMap L w' γ ∈ localFieldUnitFiltration L w' t := by
  classical
  let β' : (w' : S) → (w'.1.adicCompletion L)ˣ := fun w' =>
    if h : w'.1 = w then h ▸ β else 1
  obtain ⟨γ, hγ⟩ := exists_global_localRay_approx L S β' (fun _ => t)
  refine ⟨γ, ?_, fun w' hw' hne => ?_⟩
  · have h := hγ ⟨w, hw⟩
    simpa [β'] using h
  · have h := hγ ⟨w', hw'⟩
    simpa [β', hne] using h

end Cox.ClassFieldTheory
