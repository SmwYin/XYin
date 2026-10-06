/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryFixedField
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryIrreducible
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryLift

/-!
# Realize the auxiliary field in the actual compositum

Janusz V.5.5, printed161–162/PDF172–173, constructs the auxiliary fixed field inside LE=L(ξ). The
finite cyclotomic extension of L supplies the actual number-field compositum; the ambient field need
not be a number field. The same root and field inclusions preserve every property of the witness.
-/

open NumberField IntermediateField Polynomial Cox.Chebotarev
noncomputable section
namespace Cox.ClassFieldTheory.ArtinAuxiliary

/-- Janusz V.5.5: the compatible cyclotomic data gives one ambient auxiliary field. -/
theorem exists_auxiliary_field_of_cyclotomic_data
    {K Ω : Type*} [Field K] [NumberField K]
    [Field Ω] [CharZero Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [NumberField L]
    [IsGalois K L] [IsCyclic Gal(L/K)]
    (m : ℕ) (hm : 0 < m) (ξ : Ω) (hξ : IsPrimitiveRoot ξ m)
    (hinter : L.restrictScalars ℚ ⊓ adjoin ℚ {ξ} = ⊥)
    (q : Ideal (𝓞 K)) [q.IsPrime] (hU : UnramifiedIn K L q)
    (hcop : q.absNorm.Coprime m) (u v : (ZMod m)ˣ)
    (hu : (u : ZMod m) = q.absNorm)
    (hnu : Nat.card Gal(L/K) ∣ orderOf u)
    (hnv : Nat.card Gal(L/K) ∣ orderOf v)
    (hind : Disjoint (Subgroup.zpowers u) (Subgroup.zpowers v)) :
    ∃ F : IntermediateField K Ω, L ⊓ F = ⊥ ∧
      L ⊔ adjoin K {ξ} = F ⊔ adjoin K {ξ} ∧ q ∈ splittingIdeals K F := by
  classical
  letI : NeZero m := ⟨hm.ne'⟩
  have hL : L ≤ L ⊔ adjoin K {ξ} := le_sup_left
  have hE : adjoin K {ξ} ≤ L ⊔ adjoin K {ξ} := le_sup_right
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : FiniteDimensional K (adjoin K {ξ}) :=
    CyclotomicIntersection.finiteDimensional_adjoin_root (F := K) m hm ξ hξ
  haveI : NumberField ↥(L ⊔ adjoin K {ξ}) := NumberField.of_module_finite K _
  haveI : IsGalois K (adjoin K {ξ}) := CyclotomicBaseChange.rootField_isGalois (F := K) m hm ξ hξ
  haveI : Algebra.IsSeparable K ↥(L ⊔ adjoin K {ξ}) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois K ↥(L ⊔ adjoin K {ξ}) := ⟨⟩
  -- unramified in the whole compositum, through `L(ξ)/L`
  have hUM : UnramifiedIn K ↥(L ⊔ adjoin K {ξ}) q := by
    haveI := CyclotomicBaseChange.rootField_isCyclotomic (F := L) m hm ξ hξ
    haveI : FiniteDimensional L (adjoin L {ξ}) :=
      CyclotomicIntersection.finiteDimensional_adjoin_root (F := L) m hm ξ hξ
    haveI : NumberField (adjoin L {ξ}) := NumberField.of_module_finite L (adjoin L {ξ})
    have h0 : UnramifiedIn K (adjoin L {ξ}) q :=
      unramifiedIn_cyclotomic_tower K L (adjoin L {ξ}) m q hU hcop
    have h1 : UnramifiedIn K ((adjoin L {ξ}).restrictScalars K) q := h0
    have transport : ∀ X Y : IntermediateField K Ω, X = Y →
        UnramifiedIn K X q → UnramifiedIn K Y q := by
      rintro X Y rfl h
      exact h
    exact transport _ _ (IntermediateField.restrictScalars_adjoin_eq_sup K L {ξ}) h1
  -- the two fields inside the compositum
  let eL : L ≃ₐ[K] L.restrict hL := IntermediateField.restrict_algEquiv hL
  let eE : adjoin K {ξ} ≃ₐ[K] (adjoin K {ξ}).restrict hE := IntermediateField.restrict_algEquiv hE
  haveI : IsGalois K (L.restrict hL) := IsGalois.of_algEquiv eL
  haveI : IsCyclic Gal((L.restrict hL)/K) :=
    isCyclic_of_surjective (AlgEquiv.autCongr eL) (AlgEquiv.autCongr eL).surjective
  haveI : IsCyclotomicExtension {m} K (adjoin K {ξ}) :=
    CyclotomicBaseChange.rootField_isCyclotomic (F := K) m hm ξ hξ
  haveI : IsCyclotomicExtension {m} K ((adjoin K {ξ}).restrict hE) :=
    IsCyclotomicExtension.equiv (S := {m}) (A := K) (f := eE)
  have hcard : Nat.card Gal((L.restrict hL)/K) = Nat.card Gal(L/K) :=
    Nat.card_congr (AlgEquiv.autCongr eL).toEquiv.symm
  have hirr := irreducible_cyclotomic_of_rational_intersection L m hm ξ hξ hinter
  have hSup : L.restrict hL ⊔ (adjoin K {ξ}).restrict hE = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top]
  have hInf : L.restrict hL ⊓ (adjoin K {ξ}).restrict hE = ⊥ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_inf, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_bot]
    exact CyclotomicBaseChange.relative_intersection_of_rational_intersection L m hm ξ hξ hinter
  obtain ⟨F₀, h1, h2, h3⟩ := exists_auxiliary_fixedField K ↥(L ⊔ adjoin K {ξ})
    (L.restrict hL) ((adjoin K {ξ}).restrict hE) m hirr hSup hInf q hUM hcop u v hu
    (by rw [hcard]; exact hnu) (by rw [hcard]; exact hnv) hind
  exact exists_lifted_auxiliary_field L (adjoin K {ξ}) (L ⊔ adjoin K {ξ}) hL hE rfl q
    ⟨F₀, h1, h2, h3⟩

end Cox.ClassFieldTheory.ArtinAuxiliary
