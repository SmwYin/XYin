/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldAuxiliaryFields

/-!
# One common automorphism for the Artin auxiliary fields

Janusz V.5.6, printed162–163/PDF173–174, uses a simultaneous product of Galois groups and the same
generator in every auxiliary fixed field. Successive disjointness supplies the actual simultaneous
restriction map. One lift fixes the entire auxiliary compositum. Finite cyclotomic-family selection
is separate.
-/

open IntermediateField
noncomputable section
namespace Cox.ClassFieldTheory.AuxiliaryFields

/-- Successive disjointness permits simultaneous restriction to the normal fields. -/
theorem simultaneous_restriction_surjective_of_prefix_inf
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (r : ℕ) (L : IntermediateField K M) [Normal K L]
    (E : Fin r → IntermediateField K M) [∀ i, Normal K (E i)]
    (hInf : ∀ i,
      (L ⊔ ⨆ j : {j : Fin r // j < i}, E j.1) ⊓ E i = ⊥) :
    Function.Surjective (fun χ : M ≃ₐ[K] M =>
      (χ.restrictNormal L, fun i => χ.restrictNormal (E i))) := by
  rintro ⟨σ, τ⟩
  have descend : ∀ (A B : IntermediateField K M) [Normal K A] [Normal K B], A ≤ B →
      ∀ χ χ' : M ≃ₐ[K] M, χ.restrictNormal B = χ'.restrictNormal B →
        χ.restrictNormal A = χ'.restrictNormal A := by
    intro A B _ _ hAB χ χ' h
    ext x
    have hx : (x : M) ∈ B := hAB x.2
    change algebraMap A M (χ.restrictNormal A x) = algebraMap A M (χ'.restrictNormal A x)
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormal_commutes]
    have h4 := AlgEquiv.restrictNormal_commutes χ B ⟨x, hx⟩
    have h5 := AlgEquiv.restrictNormal_commutes χ' B ⟨x, hx⟩
    rw [h] at h4
    exact h4.symm.trans h5
  have key : ∀ k ≤ r, ∃ χ : M ≃ₐ[K] M, χ.restrictNormal L = σ ∧
      ∀ i : Fin r, i.val < k → χ.restrictNormal (E i) = τ i := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨χ, hχ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) M σ
      exact ⟨χ, hχ, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨χ, hχL, hχE⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨P, hPdef⟩ : ∃ P : IntermediateField K M,
          P = L ⊔ ⨆ j : {j : Fin r // j < ⟨k, hk⟩}, E j.1 := ⟨_, rfl⟩
      haveI : Normal K P := by rw [hPdef]; infer_instance
      have hPinf : P ⊓ E ⟨k, hk⟩ = ⊥ := by rw [hPdef]; exact hInf ⟨k, hk⟩
      obtain ⟨χ', hχ'⟩ := restrictionProd_surjective P (E ⟨k, hk⟩) hPinf
        (χ.restrictNormal P, τ ⟨k, hk⟩)
      have hP : χ'.restrictNormal P = χ.restrictNormal P := congrArg Prod.fst hχ'
      have hEi : χ'.restrictNormal (E ⟨k, hk⟩) = τ ⟨k, hk⟩ := congrArg Prod.snd hχ'
      refine ⟨χ', ?_, fun j hj => ?_⟩
      · have hLP : L ≤ P := by rw [hPdef]; exact le_sup_left
        rw [descend L P hLP χ' χ hP, hχL]
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
        · have hjP : E j ≤ P := by
            rw [hPdef]
            exact le_sup_of_le_right
              (le_iSup_of_le (⟨j, hjk⟩ : {j' : Fin r // j' < ⟨k, hk⟩}) le_rfl)
          rw [descend (E j) P hjP χ' χ hP, hχE j hjk]
        · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hjk
          exact hEi
  obtain ⟨χ, hχL, hχE⟩ := key r le_rfl
  exact ⟨χ, Prod.ext hχL (funext fun i => hχE i i.2)⟩

/-- A common lift of the same generator fixes the whole auxiliary compositum. -/
theorem auxiliary_iSup_inf_eq_bot_of_simultaneous_restriction
    {K M ι : Type*} [Field K] [Field M] [Algebra K M]
    (L : IntermediateField K M) [FiniteDimensional K L] [IsGalois K L]
    (E : ι → IntermediateField K M) [∀ i, Normal K (E i)]
    (σ : L ≃ₐ[K] L) (hσ : Subgroup.zpowers σ = ⊤)
    (ρ : ι → L ≃ₐ[K] L) (τ η : ∀ i, E i ≃ₐ[K] E i)
    (hR : Function.Surjective (fun χ : M ≃ₐ[K] M =>
      (χ.restrictNormal L, fun i => χ.restrictNormal (E i)))) :
    (⨆ i, auxiliaryFixedField L (E i) σ (ρ i) (τ i) (η i)) ⊓ L = ⊥ := by
  obtain ⟨χ, hχ⟩ := hR (σ, τ)
  have hχL : χ.restrictNormal L = σ := congrArg Prod.fst hχ
  have hχE : ∀ i, χ.restrictNormal (E i) = τ i := fun i => congrFun (congrArg Prod.snd hχ) i
  have hle : (⨆ i, auxiliaryFixedField L (E i) σ (ρ i) (τ i) (η i)) ≤
      IntermediateField.fixedField (Subgroup.zpowers χ) := by
    refine iSup_le fun i => IntermediateField.fixedField_le ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_comap]
    have h : restrictionProd L (E i) χ = (σ, τ i) := Prod.ext hχL (hχE i)
    rw [h]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hmap : (Subgroup.zpowers χ).map (AlgEquiv.restrictNormalHom L) = ⊤ := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (χ.restrictNormal L) = ⊤
    rw [hχL, hσ]
  rw [eq_bot_iff]
  calc (⨆ i, auxiliaryFixedField L (E i) σ (ρ i) (τ i) (η i)) ⊓ L ≤
        IntermediateField.fixedField (Subgroup.zpowers χ) ⊓ L := inf_le_inf_right L hle
    _ = ⊥ := fixedField_inf_eq_bot_of_map_eq_top L _ hmap

end Cox.ClassFieldTheory.AuxiliaryFields
