/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Faithful simultaneous restriction

Janusz V.5.6, printed162/PDF173, identifies the common ambient Galois group through its restrictions
to the fields generating the compositum. This is the injectivity half; full-prefix disjointness is
needed separately for surjectivity.
-/

open IntermediateField
noncomputable section
namespace Cox.ClassFieldTheory.AuxiliaryFields

/-- Janusz V.5.6, p162: the actual generating fields determine an automorphism. -/
theorem simultaneous_restriction_injective_of_sup_eq_top
    {K M ι : Type*} [Field K] [Field M] [Algebra K M]
    (L : IntermediateField K M) [Normal K L]
    (E : ι → IntermediateField K M) [∀ i, Normal K (E i)]
    (hSup : L ⊔ ⨆ i, E i = ⊤) :
    Function.Injective (fun χ : M ≃ₐ[K] M =>
      (χ.restrictNormal L, fun i => χ.restrictNormal (E i))) := by
  intro χ ψ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hL, hE⟩ := h
  have key : ∀ (F : IntermediateField K M) [Normal K F], χ.restrictNormal F = ψ.restrictNormal F →
      ∀ x ∈ F, χ x = ψ x := by
    intro F _ hF x hx
    have h1 := χ.restrictNormal_commutes F ⟨x, hx⟩
    have h2 := ψ.restrictNormal_commutes F ⟨x, hx⟩
    rw [hF] at h1
    exact h1.symm.trans h2
  let S : IntermediateField K M :=
    (RingHom.eqLocusField (χ : M →+* M) (ψ : M →+* M)).toIntermediateField fun r => by
      change χ (algebraMap K M r) = ψ (algebraMap K M r)
      rw [χ.commutes, ψ.commutes]
  have hLS : L ≤ S := fun x hx => key L hL x hx
  have hES : ∀ i, E i ≤ S := fun i x hx => key (E i) (congrFun hE i) x hx
  have htop : (⊤ : IntermediateField K M) ≤ S := hSup ▸ sup_le hLS (iSup_le hES)
  exact AlgEquiv.ext fun x => htop IntermediateField.mem_top

end Cox.ClassFieldTheory.AuxiliaryFields
