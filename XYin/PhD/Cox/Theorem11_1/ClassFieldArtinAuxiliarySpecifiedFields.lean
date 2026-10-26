/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryCore

/-!
# Specified auxiliary fixed fields in a larger ambient field

Janusz V.5.5–5.6, printed162/PDF173, uses the same two-generator subgroup and the actual Frobenius
coordinates in each factor. These contracts retain its pulled-back restriction kernel when the
common ambient is larger than one pairwise compositum. Finite ambient construction and all-prime
unramification are separate obligations.
-/

open NumberField IntermediateField Cox.Chebotarev
noncomputable section
namespace Cox.ClassFieldTheory.ArtinAuxiliary
open AuxiliaryFields

/-- Janusz V.5.5–5.6, p162: native Galois-correspondence containment adapter. -/
theorem auxiliaryFixedField_le_sup
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (L E : IntermediateField K M) [Normal K L] [Normal K E]
    (σ ρ : L ≃ₐ[K] L) (τ η : E ≃ₐ[K] E) :
    auxiliaryFixedField L E σ ρ τ η ≤ L ⊔ E := by
  unfold auxiliaryFixedField
  have hker : (L ⊔ E).fixingSubgroup = (restrictionProd L E).ker := by
    rw [IntermediateField.fixingSubgroup_sup, ← IntermediateField.restrictNormalHom_ker,
      ← IntermediateField.restrictNormalHom_ker, restrictionProd, MonoidHom.ker_prod]
  calc IntermediateField.fixedField ((twoGeneratorGroup σ ρ τ η).comap (restrictionProd L E))
      ≤ IntermediateField.fixedField (L ⊔ E).fixingSubgroup := by
        apply IntermediateField.fixedField_le
        rw [hker]
        exact Subgroup.ker_le_comap _ _
    _ = L ⊔ E := IsGalois.fixedField_fixingSubgroup _

/-- Janusz V.5.5–5.6, p162: native Galois-correspondence compositum adapter. -/
theorem auxiliaryFixedField_sup_eq_sup
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (L E : IntermediateField K M) [Normal K L] [Normal K E]
    [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (E ≃ₐ[K] E)]
    (σ ρ : L ≃ₐ[K] L) (τ η : E ≃ₐ[K] E)
    (hστ : orderOf σ ∣ orderOf τ) (hρη : orderOf ρ ∣ orderOf η)
    (hind : Disjoint (Subgroup.zpowers τ) (Subgroup.zpowers η)) :
    auxiliaryFixedField L E σ ρ τ η ⊔ E = L ⊔ E := by
  apply le_antisymm
  · exact sup_le (auxiliaryFixedField_le_sup L E σ ρ τ η) le_sup_right
  · have hbot : twoGeneratorGroup σ ρ τ η ⊓
        (MonoidHom.snd (L ≃ₐ[K] L) (E ≃ₐ[K] E)).ker = ⊥ := by
      open scoped IsMulCommutative in
      exact twoGeneratorGroup_inf_ker_snd σ ρ τ η hστ hρη hind
    have hsub : (auxiliaryFixedField L E σ ρ τ η ⊔ E).fixingSubgroup ≤
        (L ⊔ E).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_sup]
      unfold auxiliaryFixedField
      rw [IntermediateField.fixingSubgroup_fixedField]
      intro χ hχ
      obtain ⟨hH, hE'⟩ := Subgroup.mem_inf.mp hχ
      rw [← IntermediateField.restrictNormalHom_ker] at hE'
      have h1 : restrictionProd L E χ ∈
          twoGeneratorGroup σ ρ τ η ⊓ (MonoidHom.snd (L ≃ₐ[K] L) (E ≃ₐ[K] E)).ker :=
        Subgroup.mem_inf.mpr ⟨hH, hE'⟩
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : χ ∈ (restrictionProd L E).ker := h1
      rw [restrictionProd, MonoidHom.ker_prod, IntermediateField.restrictNormalHom_ker,
        IntermediateField.restrictNormalHom_ker] at h2
      exact h2
    calc L ⊔ E = IntermediateField.fixedField (L ⊔ E).fixingSubgroup :=
          (IsGalois.fixedField_fixingSubgroup _).symm
      _ ≤ IntermediateField.fixedField (auxiliaryFixedField L E σ ρ τ η ⊔ E).fixingSubgroup :=
          IntermediateField.fixedField_le hsub
      _ = auxiliaryFixedField L E σ ρ τ η ⊔ E := IsGalois.fixedField_fixingSubgroup _

/-- Janusz V.5.5–5.6, p162: the actual Frobenius pair splits the specified fixed field. -/
theorem splits_auxiliaryFixedField
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [IsAbelianGalois K M]
    (L E : IntermediateField K M) (σ : L ≃ₐ[K] L) (τ : E ≃ₐ[K] E)
    (q : Ideal (𝓞 K)) [q.IsPrime] (hU : UnramifiedIn K M q) :
    q ∈ splittingIdeals K (auxiliaryFixedField L E
      σ (frobeniusClass K L q).out τ (frobeniusClass K E q).out) := by
  haveI : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M
  haveI : NumberField L := NumberField.of_module_finite K L
  haveI : NumberField E := NumberField.of_module_finite K E
  have hUL := Chebotarev.unramifiedIn_intermediateField K M L q hU
  have hUE := Chebotarev.unramifiedIn_intermediateField K M E q hU
  have h1 := frobeniusClass_out_restrict K L M q hU hUL
  have h2 := frobeniusClass_out_restrict K E M q hU hUE
  unfold auxiliaryFixedField
  apply splits_fixedField_of_frobenius_mem K M _ q hU
  rw [Subgroup.mem_comap]
  have h3 : restrictionProd L E (frobeniusClass K M q).out =
      ((frobeniusClass K L q).out, (frobeniusClass K E q).out) := Prod.ext h1 h2
  rw [h3]
  exact second_mem_twoGeneratorGroup _ _ _ _

end Cox.ClassFieldTheory.ArtinAuxiliary
