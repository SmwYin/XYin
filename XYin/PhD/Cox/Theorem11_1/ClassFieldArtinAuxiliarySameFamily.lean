/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryResidueFamily
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliarySpecifiedFields
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryAmbientTransport
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryUnramification
import XYin.PhD.Cox.Theorem11_1.ClassFieldAuxiliaryFamily
import XYin.PhD.Cox.Theorem11_1.ClassFieldAuxiliaryFaithful
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryPartner
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryIrreducible
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicFrobenius

/-! # One coherent auxiliary family for cyclic reciprocity
-/

open NumberField IntermediateField Cox.Chebotarev
open scoped nonZeroDivisors

noncomputable section

namespace Cox.ClassFieldTheory.ArtinAuxiliary

/-- Source: Janusz, Algebraic Number Fields (1973), V.5.6, printed162–163/PDF173–174. -/
theorem exists_same_auxiliary_family
    (K : Type*) [Field K] [NumberField K]
    (L : IntermediateField K (AlgebraicClosure K)) [NumberField L]
    [IsGalois K L]
    (r : ℕ) (σ : Gal(L/K)) (hσ : Subgroup.zpowers σ = ⊤)
    (q : Fin r → Ideal (𝓞 K)) [∀ i, (q i).IsPrime]
    (hq0 : ∀ i, q i ≠ ⊥) (hU : ∀ i, UnramifiedIn K L (q i)) :
    ∃ (m : Fin r → ℕ) (ξ : Fin r → AlgebraicClosure K)
      (F : Fin r → IntermediateField K (AlgebraicClosure K)),
      (∀ i, 0 < m i) ∧ (∀ i, IsPrimitiveRoot (ξ i) (m i)) ∧
      (∀ i j, (q i).absNorm.Coprime (m j)) ∧
      (∀ i, F i ≤ L ⊔ ⨆ j, adjoin K {ξ j}) ∧
      (∀ i, q i ∈ splittingIdeals K (F i)) ∧
      (∀ i, F i ⊔ adjoin K {ξ i} = L ⊔ adjoin K {ξ i}) ∧
      (⨆ i, F i) ⊓ L = ⊥ := by
  classical
  haveI : IsCyclic Gal(L/K) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, hσ⟩
  have hn : 0 < Nat.card Gal(L/K) := Nat.card_pos
  have ha : ∀ i, 2 ≤ (q i).absNorm := fun i => by
    have h0 : (q i).absNorm ≠ 0 := fun h => hq0 i (Ideal.absNorm_eq_zero_iff.mp h)
    have h1 : (q i).absNorm ≠ 1 := fun h =>
      Ideal.IsPrime.ne_top (inferInstance : (q i).IsPrime) (Ideal.absNorm_eq_one_iff.mp h)
    omega
  have hs : 0 < ∏ i, (q i).absNorm := Finset.prod_pos fun i _ => by have := ha i; omega
  have hroots : ∀ k : ℕ, 0 < k → ∃ ξ : AlgebraicClosure K, IsPrimitiveRoot ξ k := by
    intro k hk
    haveI : NeZero (k : AlgebraicClosure K) := ⟨Nat.cast_ne_zero.mpr hk.ne'⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot _ k
  haveI : FiniteDimensional ℚ (L.restrictScalars ℚ) := inferInstanceAs (FiniteDimensional ℚ L)
  obtain ⟨m, ξ, u, v, hdata⟩ := exists_sequential_cyclotomic_residue_family hroots
    (L.restrictScalars ℚ) r (fun i => (q i).absNorm) ha (Nat.card Gal(L/K))
    (∏ i, (q i).absNorm) hn hs
  have hm : ∀ i, 0 < m i := fun i => (hdata i).1
  have hξ : ∀ i, IsPrimitiveRoot (ξ i) (m i) := fun i => (hdata i).2.2.2.1
  have hcop : ∀ i j, (q i).absNorm.Coprime (m j) := fun i j => by
    have h1 : (m j).Coprime ((∏ l, (q l).absNorm) * ∏ l : {l : Fin r // l < j}, m l.1) :=
      (hdata j).2.1
    have h2 : (m j).Coprime (∏ l, (q l).absNorm) :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) h1
    exact (Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) h2).symm
  -- the common compositum
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI hEfin : ∀ j, FiniteDimensional K (adjoin K {ξ j}) := fun j =>
    CyclotomicIntersection.finiteDimensional_adjoin_root (F := K) (m j) (hm j) (ξ j) (hξ j)
  haveI hEgal : ∀ j, IsGalois K (adjoin K {ξ j}) := fun j =>
    CyclotomicBaseChange.rootField_isGalois (F := K) (m j) (hm j) (ξ j) (hξ j)
  haveI hNZ : ∀ j, NeZero (m j) := fun j => ⟨(hm j).ne'⟩
  haveI hEcyc : ∀ j, IsCyclotomicExtension {m j} K (adjoin K {ξ j}) := fun j =>
    CyclotomicBaseChange.rootField_isCyclotomic (F := K) (m j) (hm j) (ξ j) (hξ j)
  haveI : NumberField ↥(L ⊔ ⨆ j, adjoin K {ξ j}) := NumberField.of_module_finite K _
  haveI : Algebra.IsSeparable K ↥(L ⊔ ⨆ j, adjoin K {ξ j}) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois K ↥(L ⊔ ⨆ j, adjoin K {ξ j}) := ⟨⟩
  have hUM : ∀ i, UnramifiedIn K ↥(L ⊔ ⨆ j, adjoin K {ξ j}) (q i) := fun i =>
    unramifiedIn_sup_iSup_rootField L m ξ hm hξ (q i) (hU i) (fun j => hcop i j)
  have hLM : L ≤ L ⊔ ⨆ j, adjoin K {ξ j} := le_sup_left
  have hEM : ∀ j, adjoin K {ξ j} ≤ L ⊔ ⨆ j, adjoin K {ξ j} := fun j =>
    le_sup_of_le_right (le_iSup (fun j => adjoin K {ξ j}) j)
  set Mf : IntermediateField K (AlgebraicClosure K) := L ⊔ ⨆ j, adjoin K {ξ j} with hMf
  -- the restricted fields
  let eL : L ≃ₐ[K] L.restrict hLM := IntermediateField.restrict_algEquiv hLM
  let eE : ∀ j, adjoin K {ξ j} ≃ₐ[K] (adjoin K {ξ j}).restrict (hEM j) := fun j =>
    IntermediateField.restrict_algEquiv (hEM j)
  haveI : IsGalois K (L.restrict hLM) := IsGalois.of_algEquiv eL
  haveI hE'gal : ∀ j, IsGalois K ((adjoin K {ξ j}).restrict (hEM j)) := fun j =>
    IsGalois.of_algEquiv (eE j)
  haveI : IsAbelianGalois K L := IsAbelianGalois.of_isCyclic K L
  haveI : IsAbelianGalois K (L.restrict hLM) := IsAbelianGalois.of_algHom eL.symm.toAlgHom
  haveI hEab : ∀ j, IsAbelianGalois K (adjoin K {ξ j}) := fun j =>
    IsCyclotomicExtension.isAbelianGalois {m j} K _
  haveI hE'ab : ∀ j, IsAbelianGalois K ((adjoin K {ξ j}).restrict (hEM j)) := fun j =>
    IsAbelianGalois.of_algHom (eE j).symm.toAlgHom
  haveI hE'cyc : ∀ j, IsCyclotomicExtension {m j} K ((adjoin K {ξ j}).restrict (hEM j)) :=
    fun j => IsCyclotomicExtension.equiv (S := {m j}) (A := K) (f := eE j)
  haveI hE'nf : ∀ j, NumberField ((adjoin K {ξ j}).restrict (hEM j)) := fun j =>
    NumberField.of_module_finite K _
  haveI : NumberField (L.restrict hLM) := NumberField.of_module_finite K _
  -- generation, hence abelian compositum
  have hlift_iSup : ∀ (G : Fin r → IntermediateField K Mf),
      IntermediateField.lift (⨆ j, G j) = ⨆ j, IntermediateField.lift (G j) := fun G => by
    rw [IntermediateField.lift, IntermediateField.map_iSup]
    rfl
  have hSup' : L.restrict hLM ⊔ ⨆ j, (adjoin K {ξ j}).restrict (hEM j) = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict, hlift_iSup,
      IntermediateField.lift_top]
    exact congrArg (L ⊔ ·) (iSup_congr fun j => IntermediateField.lift_restrict (hEM j))
  have hinj := AuxiliaryFields.simultaneous_restriction_injective_of_sup_eq_top
    (L.restrict hLM) (fun j => (adjoin K {ξ j}).restrict (hEM j)) hSup'
  haveI : IsAbelianGalois K Mf :=
    { is_comm.comm x y := hinj (by
        have h1 : ∀ (A : IntermediateField K Mf) [Normal K A] [IsMulCommutative Gal(A/K)],
            (x * y).restrictNormal A = (y * x).restrictNormal A := fun A _ _ => by
          change AlgEquiv.restrictNormalHom A (x * y) = AlgEquiv.restrictNormalHom A (y * x)
          rw [map_mul, map_mul]
          open scoped IsMulCommutative in
          exact mul_comm _ _
        exact Prod.ext (h1 _) (funext fun j => h1 _)) }
  -- prefix disjointness and simultaneous restriction
  have hprefix := restricted_prefix_inf_eq_bot_of_rational Mf L r m ξ hm hξ hLM hEM
    (fun i => (hdata i).2.2.2.2.1)
  have hR := AuxiliaryFields.simultaneous_restriction_surjective_of_prefix_inf r
    (L.restrict hLM) (fun j => (adjoin K {ξ j}).restrict (hEM j)) hprefix
  -- the generator, Frobenius coordinates and partners
  set σ' : Gal((L.restrict hLM)/K) := AlgEquiv.autCongr eL σ with hσ'def
  have hσ' : Subgroup.zpowers σ' = ⊤ := by
    rw [show σ' = (AlgEquiv.autCongr eL).toMonoidHom σ from rfl, ← MonoidHom.map_zpowers, hσ,
      Subgroup.map_top_of_surjective _ (AlgEquiv.autCongr eL).surjective]
  have hcardL : Nat.card Gal((L.restrict hLM)/K) = Nat.card Gal(L/K) :=
    Nat.card_congr (AlgEquiv.autCongr eL).toEquiv.symm
  have hirr : ∀ i, Irreducible (Polynomial.cyclotomic (m i) K) := fun i =>
    irreducible_cyclotomic_of_rational_intersection L (m i) (hm i) (ξ i) (hξ i)
      (eq_bot_iff.mpr ((inf_le_inf_right _ le_sup_left).trans (hdata i).2.2.2.2.1.le))
  have hUE : ∀ i, UnramifiedIn K ((adjoin K {ξ i}).restrict (hEM i)) (q i) := fun i =>
    Chebotarev.unramifiedIn_intermediateField K Mf _ (q i) (hUM i)
  choose τ hτn hτind using fun i => independent_frobenius_partner K
    ((adjoin K {ξ i}).restrict (hEM i)) (m i) (hirr i) (q i) (hUE i) (hcop i i)
    (Nat.card Gal(L/K)) (u i) (v i) (hdata i).2.2.2.2.2.1 (hdata i).2.2.2.2.2.2.2.1
    (hdata i).2.2.2.2.2.2.2.2
  have hηn : ∀ i, Nat.card Gal(L/K) ∣
      orderOf (frobeniusClass K ((adjoin K {ξ i}).restrict (hEM i)) (q i)).out := fun i => by
    have hηu : IsCyclotomicExtension.autEquivPow _ (hirr i)
        (frobeniusClass K ((adjoin K {ξ i}).restrict (hEM i)) (q i)).out = u i := by
      rw [CyclotomicFrobenius.autEquivPow_frobeniusClass_out K _ (m i) (hirr i) (q i) (hUE i)
        (hcop i i)]
      exact Units.ext (by rw [ZMod.coe_unitOfCoprime, (hdata i).2.2.2.2.2.1])
    rw [← MulEquiv.orderOf_eq (IsCyclotomicExtension.autEquivPow _ (hirr i)), hηu]
    exact (hdata i).2.2.2.2.2.2.1
  -- the fixed fields inside the compositum
  have hsplit : ∀ i, q i ∈ splittingIdeals K (AuxiliaryFields.auxiliaryFixedField
      (L.restrict hLM) ((adjoin K {ξ i}).restrict (hEM i)) σ'
      (frobeniusClass K (L.restrict hLM) (q i)).out (τ i)
      (frobeniusClass K ((adjoin K {ξ i}).restrict (hEM i)) (q i)).out) := fun i =>
    splits_auxiliaryFixedField K Mf _ _ σ' (τ i) (q i) (hUM i)
  have hsup : ∀ i, AuxiliaryFields.auxiliaryFixedField
      (L.restrict hLM) ((adjoin K {ξ i}).restrict (hEM i)) σ'
      (frobeniusClass K (L.restrict hLM) (q i)).out (τ i)
      (frobeniusClass K ((adjoin K {ξ i}).restrict (hEM i)) (q i)).out ⊔
        (adjoin K {ξ i}).restrict (hEM i) =
      L.restrict hLM ⊔ (adjoin K {ξ i}).restrict (hEM i) := fun i =>
    auxiliaryFixedField_sup_eq_sup _ _ σ' _ (τ i) _
      ((orderOf_dvd_natCard σ').trans (by rw [hcardL]; exact hτn i))
      ((orderOf_dvd_natCard _).trans (by rw [hcardL]; exact hηn i)) (hτind i)
  have hinf := AuxiliaryFields.auxiliary_iSup_inf_eq_bot_of_simultaneous_restriction
    (L.restrict hLM) (fun j => (adjoin K {ξ j}).restrict (hEM j)) σ' hσ'
    (fun i => (frobeniusClass K (L.restrict hLM) (q i)).out) τ
    (fun i => (frobeniusClass K ((adjoin K {ξ i}).restrict (hEM i)) (q i)).out) hR
  -- lift everything back to the algebraic closure
  refine ⟨m, ξ, fun i => IntermediateField.lift (AuxiliaryFields.auxiliaryFixedField
      (L.restrict hLM) ((adjoin K {ξ i}).restrict (hEM i)) σ'
      (frobeniusClass K (L.restrict hLM) (q i)).out (τ i)
      (frobeniusClass K ((adjoin K {ξ i}).restrict (hEM i)) (q i)).out),
    hm, hξ, hcop, fun i => IntermediateField.lift_le _, fun i => ?_, fun i => ?_, ?_⟩
  · rw [← splittingIdeals_algEquiv (IntermediateField.liftAlgEquiv _)]
    exact hsplit i
  · have h := congrArg (fun X : IntermediateField K Mf => IntermediateField.lift X) (hsup i)
    simp only at h
    rwa [IntermediateField.lift_sup, IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict] at h
  · have h := congrArg (fun X : IntermediateField K Mf => IntermediateField.lift X) hinf
    simp only at h
    rwa [IntermediateField.lift_inf, hlift_iSup, IntermediateField.lift_restrict,
      IntermediateField.lift_bot] at h

end Cox.ClassFieldTheory.ArtinAuxiliary
