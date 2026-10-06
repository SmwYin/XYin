/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import XYin.PhD.Cox.Theorem11_1.ClassFieldSplittingDensity

/-! # Janusz III.2.7 and IV.5.5: composita and splitting densities
The actual compositum is formed inside an arbitrary ambient field. Only the finite subfields are
number fields.
-/
open NumberField
noncomputable section
namespace Cox.ClassFieldTheory
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
/-- An automorphism trivial on both subfields is trivial on their actual compositum. -/
theorem compositum_automorphism_eq_one (L E : IntermediateField K Ω) [Normal K L] [Normal K E]
    (σ : (L ⊔ E : IntermediateField K Ω) ≃ₐ[K] (L ⊔ E : IntermediateField K Ω)) :
    letI : Algebra L (L ⊔ E : IntermediateField K Ω) :=
      (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
    letI : Algebra E (L ⊔ E : IntermediateField K Ω) :=
      (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
    letI : IsScalarTower K L (L ⊔ E : IntermediateField K Ω) :=
      IsScalarTower.of_algebraMap_eq' (by rfl)
    letI : IsScalarTower K E (L ⊔ E : IntermediateField K Ω) :=
      IsScalarTower.of_algebraMap_eq' (by rfl)
    σ.restrictNormal L = 1 → σ.restrictNormal E = 1 → σ = 1 := by
  letI : Algebra L (L ⊔ E : IntermediateField K Ω) :=
    (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  letI : Algebra E (L ⊔ E : IntermediateField K Ω) :=
    (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
  letI : IsScalarTower K L (L ⊔ E : IntermediateField K Ω) :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  letI : IsScalarTower K E (L ⊔ E : IntermediateField K Ω) :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  intro hL hE
  have hfixL : ∀ y : L, σ (IntermediateField.inclusion le_sup_left y) =
      IntermediateField.inclusion le_sup_left y := by
    intro y
    have h := σ.restrictNormal_commutes L y
    rw [hL] at h
    exact h.symm
  have hfixE : ∀ y : E, σ (IntermediateField.inclusion le_sup_right y) =
      IntermediateField.inclusion le_sup_right y := by
    intro y
    have h := σ.restrictNormal_commutes E y
    rw [hE] at h
    exact h.symm
  let S : IntermediateField K (L ⊔ E : IntermediateField K Ω) :=
    (RingHom.eqLocusField (σ : (L ⊔ E : IntermediateField K Ω) →+* _)
      (RingHom.id _)).toIntermediateField fun r => by
        change σ (algebraMap K _ r) = algebraMap K _ r
        exact σ.commutes r
  have hLle : L ≤ S.map (L ⊔ E).val := by
    intro y hy
    exact (IntermediateField.mem_map _).mpr ⟨IntermediateField.inclusion le_sup_left ⟨y, hy⟩,
      hfixL ⟨y, hy⟩, rfl⟩
  have hEle : E ≤ S.map (L ⊔ E).val := by
    intro y hy
    exact (IntermediateField.mem_map _).mpr ⟨IntermediateField.inclusion le_sup_right ⟨y, hy⟩,
      hfixE ⟨y, hy⟩, rfl⟩
  have htop : L ⊔ E ≤ S.map (L ⊔ E).val := sup_le hLle hEle
  ext x
  obtain ⟨x', hx', hxx'⟩ := (IntermediateField.mem_map _).mp (htop x.2)
  have hx'x : x' = x := Subtype.ext hxx'
  rw [← hx'x]
  exact congrArg Subtype.val (show σ x' = x' from hx')

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

/-- At a completely split prime every arithmetic Frobenius element is trivial. -/
theorem isArithFrobAt_eq_one_of_splits {q : Ideal (𝓞 K)} (hs : q ∈ splittingIdeals K M)
    (P : Ideal (𝓞 M)) (hP : P ∈ q.primesOver (𝓞 M))
    (σ : M ≃ₐ[K] M) (hσ : IsArithFrobAt (𝓞 K) σ P) : σ = 1 := by
  rw [splittingIdeals_eq_frobeniusClass_one] at hs
  obtain ⟨hqp, hunr, hcl⟩ := hs
  haveI := hqp
  haveI := hP.1
  have hcl' := Chebotarev.frobeniusClass_eq_mk_of_isArithFrobAt K M q hunr σ P hσ hP.2
  rw [hcl] at hcl'
  exact isConj_one_right.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hcl')

/-- Identity arithmetic Frobenius at one upper prime gives complete splitting. -/
theorem splits_of_isArithFrobAt_eq_one {q : Ideal (𝓞 K)} (hq : q.IsPrime)
    (hu : Chebotarev.UnramifiedIn K M q)
    (P : Ideal (𝓞 M)) (hP : P ∈ q.primesOver (𝓞 M))
    (σ : M ≃ₐ[K] M) (hσ : IsArithFrobAt (𝓞 K) σ P) (h1 : σ = 1) :
    q ∈ splittingIdeals K M := by
  rw [splittingIdeals_eq_frobeniusClass_one]
  haveI := hq
  haveI := hP.1
  refine ⟨hq, hu, ?_⟩
  rw [Chebotarev.frobeniusClass_eq_mk_of_isArithFrobAt K M q hu σ P hσ hP.2, h1]

/-- Outside ramification, splitting in both normal fields gives splitting in their compositum. -/
theorem splits_compositum_of_unramified {Ω : Type*} [Field Ω] [Algebra K Ω]
    (L E : IntermediateField K Ω) [NumberField L] [NumberField E]
    [IsGalois K L] [IsGalois K E]
    {q : Ideal (𝓞 K)} (hL : q ∈ splittingIdeals K L) (hE : q ∈ splittingIdeals K E)
    (hu : Chebotarev.UnramifiedIn K (L ⊔ E : IntermediateField K Ω) q) :
    q ∈ splittingIdeals K (L ⊔ E : IntermediateField K Ω) := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite ℚ K E
  haveI : NumberField (L ⊔ E : IntermediateField K Ω) := NumberField.of_module_finite K _
  haveI : Normal K (L ⊔ E : IntermediateField K Ω) := IntermediateField.normal_sup K Ω L E
  haveI : IsGalois K (L ⊔ E : IntermediateField K Ω) := IsGalois.mk
  have hq0 : q ≠ ⊥ := hu.1
  haveI hqp : q.IsPrime := hL.1
  obtain ⟨Q, hQp, hQlo, -⟩ :=
    Chebotarev.exists_prime_liesOver K (L ⊔ E : IntermediateField K Ω) q hq0
  haveI := hQp
  haveI : Finite (𝓞 (L ⊔ E : IntermediateField K Ω) ⧸ Q) :=
    Chebotarev.UnramifiedIn.finite_quotient K _ hu Q hQlo
  set σ := arithFrobAt (𝓞 K) Gal((L ⊔ E : IntermediateField K Ω)/K) Q with hσdef
  have hσ : IsArithFrobAt (𝓞 K) σ Q :=
    IsArithFrobAt.arithFrobAt (𝓞 K) Gal((L ⊔ E : IntermediateField K Ω)/K) Q
  letI : Algebra L (L ⊔ E : IntermediateField K Ω) :=
    (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  letI : Algebra E (L ⊔ E : IntermediateField K Ω) :=
    (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
  letI : IsScalarTower K L (L ⊔ E : IntermediateField K Ω) :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  letI : IsScalarTower K E (L ⊔ E : IntermediateField K Ω) :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  have hσL := Chebotarev.isArithFrobAt_restrictNormal_repl K L _ σ Q hσ
  have hσE := Chebotarev.isArithFrobAt_restrictNormal_repl K E _ σ Q hσ
  have hQL : Q.under (𝓞 L) ∈ q.primesOver (𝓞 L) :=
    ⟨inferInstance, ⟨by rw [Ideal.under_under]; exact hQlo.over⟩⟩
  have hQE : Q.under (𝓞 E) ∈ q.primesOver (𝓞 E) :=
    ⟨inferInstance, ⟨by rw [Ideal.under_under]; exact hQlo.over⟩⟩
  have h1L := isArithFrobAt_eq_one_of_splits K L hL _ hQL _ hσL
  have h1E := isArithFrobAt_eq_one_of_splits K E hE _ hQE _ hσE
  have hσ1 : σ = 1 := compositum_automorphism_eq_one L E σ h1L h1E
  exact splits_of_isArithFrobAt_eq_one K _ hqp hu Q ⟨hQp, hQlo⟩ σ hσ hσ1

/-- Finite-exception inclusion preserves the order of Dirichlet densities. -/
theorem density_le_of_finite_diff {S T : Set (Ideal (𝓞 K))} {δ ε : ℝ}
    (hS : Chebotarev.HasDirichletDensity S δ) (hT : Chebotarev.HasDirichletDensity T ε)
    (h : (S \ T).Finite) : δ ≤ ε := by
  have h1 := density_diff_finite K hS h
  have hsub : S \ (S \ T) ⊆ T := fun x hx => by
    by_contra hxT
    exact hx.2 ⟨hx.1, hxT⟩
  exact Chebotarev.HasLowerDirichletDensity.mono K hsub h1.hasLower hT.hasLower

/-- Janusz IV.5.5: the compositum adds at most finitely many exceptions. -/
theorem splitting_compositum_finite_diff {Ω : Type*} [Field Ω] [Algebra K Ω]
    (L E : IntermediateField K Ω) [NumberField L] [NumberField E]
    [IsGalois K L] [IsGalois K E]
    (h : (splittingIdeals K E \ splittingIdeals K L).Finite) :
    (splittingIdeals K E \ splittingIdeals K (L ⊔ E : IntermediateField K Ω)).Finite := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite ℚ K E
  haveI : NumberField (L ⊔ E : IntermediateField K Ω) := NumberField.of_module_finite K _
  haveI : Normal K (L ⊔ E : IntermediateField K Ω) := IntermediateField.normal_sup K Ω L E
  haveI : IsGalois K (L ⊔ E : IntermediateField K Ω) := IsGalois.mk
  refine (h.union (Chebotarev.finite_ramifiedIn K (L ⊔ E : IntermediateField K Ω))).subset ?_
  rintro q ⟨hqE, hqM⟩
  by_cases hqL : q ∈ splittingIdeals K L
  · right
    refine ⟨hqE.1, hqE.2.1, fun hu => hqM ?_⟩
    exact splits_compositum_of_unramified K L E hqL hqE hu
  · exact Or.inl ⟨hqE, hqL⟩

end Cox.ClassFieldTheory
