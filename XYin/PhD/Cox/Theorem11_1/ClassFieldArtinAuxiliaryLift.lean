/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryCore

/-!
# Include the auxiliary fixed field in the ambient field

Janusz V.5.5, printed161–162/PDF172–173, constructs the same auxiliary field inside the compositum
LE. This representation adapter includes that witness in the ambient field and transports its
intersection, generation and splitting properties through the actual inclusion.
-/

open NumberField IntermediateField Cox.Chebotarev
noncomputable section
namespace Cox.ClassFieldTheory.ArtinAuxiliary

/-- The auxiliary field inside the actual compositum gives the same ambient witness. -/
theorem exists_lifted_auxiliary_field
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L E M : IntermediateField K Ω) (hL : L ≤ M) (hE : E ≤ M)
    (hgen : L ⊔ E = M) (q : Ideal (𝓞 K))
    (hinner : ∃ F : IntermediateField K M,
      L.restrict hL ⊓ F = ⊥ ∧ F ⊔ E.restrict hE = ⊤ ∧
        q ∈ splittingIdeals K F) :
    ∃ F : IntermediateField K Ω, L ⊓ F = ⊥ ∧
      L ⊔ E = F ⊔ E ∧ q ∈ splittingIdeals K F := by
  obtain ⟨F, h1, h2, h3⟩ := hinner
  refine ⟨IntermediateField.lift F, ?_, ?_, ?_⟩
  · have h := congrArg (fun X : IntermediateField K M => IntermediateField.lift X) h1
    simp only at h
    rwa [IntermediateField.lift_inf, IntermediateField.lift_restrict,
      IntermediateField.lift_bot] at h
  · have h := congrArg (fun X : IntermediateField K M => IntermediateField.lift X) h2
    simp only at h
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_top] at h
    rw [hgen, h]
  · rw [← splittingIdeals_algEquiv (IntermediateField.liftAlgEquiv F)]
    exact h3

end Cox.ClassFieldTheory.ArtinAuxiliary
