/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryAmbient
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryResidueData
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinFrobeniusMap
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinIntegral
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinSurjectivity
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclic
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicQuotients
import XYin.PhD.Cox.Theorem11_1.ClassFieldExtensionEquiv
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnramifiedModulus
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormModulus
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalPower
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnits
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnitIndices
import XYin.PhD.Cox.Theorem11_1.ClassFieldKummer
import XYin.PhD.Cox.Theorem11_1.ClassFieldResidueUnits
import XYin.PhD.Cox.Theorem11_1.ClassFieldResidueIndependence
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicBaseChange
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliarySameFamily
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicReciprocity
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormRayTransport
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormDegreePower
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliarySpecifiedFields
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryPartner
import XYin.PhD.Cox.Theorem11_1.ClassFieldAuxiliaryFamily
import XYin.PhD.Cox.Theorem11_1.ClassFieldAuxiliaryFaithful
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryAmbientTransport
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryIrreducible
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryUnramification
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryResidueFamily
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealTate
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryCore
import XYin.PhD.Cox.Theorem11_1.ClassFieldTheory
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealGroups
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Constructive inputs to Janusz V.9

These are source-backed internal proof obligations, not assumptions of Cox Theorem 11.1.
The finite-modulus reciprocity and existence developments are restricted to totally
complex number fields. The auxiliary-field, Kummer, S-unit, and local inputs are general.
-/

open NumberField IsDedekindDomain
open NumberField.InfinitePlace
open scoped nonZeroDivisors BigOperators

noncomputable section

namespace Cox.ClassFieldTheory

variable (K : Type*) [Field K] [NumberField K]

/-- Janusz V.9 setup: finitely many class representatives and exponent divisors suffice. -/
theorem exists_suitable_support (n : ℕ) (hn : 0 < n) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      SupportsClassRepresentatives K S ∧ CoversNthPrimes K n S := by
  classical
  have hrep : ∀ c : ClassGroup (𝓞 K), ∃ u : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      ClassGroup.mk K u = c := fun c => ClassGroup.induction K (fun I => ⟨I, rfl⟩) c
  choose u hu using hrep
  have hfin : ∀ c, {v : HeightOneSpectrum (𝓞 K) |
      FractionalIdeal.count K v (u c : FractionalIdeal (𝓞 K)⁰ K) ≠ 0}.Finite := fun c =>
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (u c : FractionalIdeal (𝓞 K)⁰ K))
  have hn0 : Ideal.span {(n : 𝓞 K)} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  have hfinn := Ideal.finite_factors hn0
  refine ⟨(Finset.univ.biUnion fun c => (hfin c).toFinset) ∪ hfinn.toFinset,
    fun c => ⟨u c, ?_, hu c⟩, fun v hv => ?_⟩
  · rw [mem_supportedIdeals_iff_count_eq_zero]
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, (hfin c).mem_toFinset.mpr h⟩))
  · refine Finset.mem_union_right _ (hfinn.mem_toFinset.mpr ?_)
    rw [Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv

section AuxiliaryFields

/-- Janusz V.5.5: the cyclotomic auxiliary field makes a selected prime split while
retaining the cyclic extension after adjoining the same roots of unity. -/
theorem exists_artin_auxiliary_field
    (L : IntermediateField K (AlgebraicClosure K)) [NumberField L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] (s : ℕ) (hs : 0 < s)
    (q : Ideal (𝓞 K)) (hq : q.IsPrime) (hq0 : q ≠ ⊥)
    (hU : ∀ P ∈ q.primesOver (𝓞 L), Ideal.ramificationIdx q P = 1) :
    ∃ (m : ℕ) (ζ : AlgebraicClosure K) (F : IntermediateField K (AlgebraicClosure K)),
      0 < m ∧ m.Coprime s ∧ m.Coprime q.absNorm ∧ IsPrimitiveRoot ζ m ∧
      L ⊓ F = ⊥ ∧ L ⊓ IntermediateField.adjoin K {ζ} = ⊥ ∧
      L ⊔ IntermediateField.adjoin K {ζ} = F ⊔ IntermediateField.adjoin K {ζ} ∧
      q ∈ splittingIdeals K F := by
  haveI := hq
  have hroots : ∀ m : ℕ, 0 < m → ∃ ξ : AlgebraicClosure K, IsPrimitiveRoot ξ m := by
    intro m hm
    haveI : NeZero (m : AlgebraicClosure K) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) m
  haveI : FiniteDimensional ℚ (L.restrictScalars ℚ) := inferInstanceAs (FiniteDimensional ℚ L)
  haveI : Finite (IntermediateField ℚ (L.restrictScalars ℚ)) :=
    CyclotomicCapture.finite_intermediateFields_of_finite_separable ℚ _
  have ha : 2 ≤ q.absNorm := HeightOneSpectrum.one_lt_absNorm ⟨q, hq, hq0⟩
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hn : 0 < Nat.card (L ≃ₐ[K] L) := Nat.card_pos
  obtain ⟨m, ξ, hm, hms, hmq, hξ, hinter, u, v, hu, hnu, hnv, hind⟩ :=
    ArtinAuxiliary.exists_cyclotomic_residue_data hroots (L.restrictScalars ℚ) q.absNorm
      (Nat.card (L ≃ₐ[K] L)) s ha hn hs
  have hUq := ArtinAuxiliary.unramifiedIn_of_ramificationIdx_eq_one K L q hq0 hU
  obtain ⟨F, hLF, hjoin, hsplit⟩ := ArtinAuxiliary.exists_auxiliary_field_of_cyclotomic_data L m hm
    ξ hξ hinter q hUq hmq.symm u v hu hnu hnv hind
  exact ⟨m, ξ, F, hm, hms, hmq, hξ, hLF,
    CyclotomicBaseChange.relative_intersection_of_rational_intersection L m hm ξ hξ hinter,
    hjoin, hsplit⟩

end AuxiliaryFields

section Reciprocity

variable (m : Ideal (𝓞 K)) (L : Type*) [Field L] [NumberField L] [Algebra K L]
variable [Module.Finite (𝓞 K) (𝓞 L)]

/-- Reciprocity at a fixed modulus: ray principals act trivially under arithmetic Artin. -/
def IsReciprocityLaw : Prop :=
  ∃ φ : coprimeIdeals K m →* (L ≃ₐ[K] L), IsArtinMap K m L φ ∧
    Function.Surjective φ ∧ raySubgroup K m ≤ φ.ker

-- `[Module.Finite (𝓞 K) (𝓞 L)]` is a section variable; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Prime ideal Frobenius extends to a surjective Artin map in an abelian extension. -/
theorem exists_artinMap [IsAbelianGalois K L] (hm : m ≠ ⊥)
    (hU : IsUnramifiedAway K m L) :
    ∃ φ : coprimeIdeals K m →* (L ≃ₐ[K] L),
      IsArtinMap K m L φ ∧ Function.Surjective φ := by
  exact ⟨arithmeticArtin K m L, arithmeticArtin_isArtinMap K m L hU,
    surjective_of_frobenius_prime_values K m hm L _
      fun q hq hq0 u hu => arithmeticArtin_prime K m L q hq hq0 u hu⟩

/-- Janusz III.3.2 / V.5.1: relative ideal norms act trivially under Artin. -/
theorem normImage_le_artin_ker [IsGalois K L]
    (hU : IsUnramifiedAway K m L)
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K m L φ) :
    normImage K m L ≤ φ.ker := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro u ⟨A, hA0, hAm, hAu⟩
  exact artin_integral_norm_eq_one K m L hU φ hφ A hA0 hAm u hAu

/-- Janusz V.5.1: reciprocity and the first inequality identify the Artin kernel. -/
theorem artin_ker_eq_normRaySubgroup [IsAbelianGalois K L] (hm : m ≠ ⊥)
    (hU : IsUnramifiedAway K m L)
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K m L φ) (hsurj : Function.Surjective φ)
    (hray : raySubgroup K m ≤ φ.ker) : φ.ker = normRaySubgroup K m L := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hle : normRaySubgroup K m L ≤ φ.ker := sup_le (normImage_le_artin_ker K m L hU φ hφ) hray
  have hker : φ.ker.index = Module.finrank K L := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective φ hsurj, Subgroup.card_top,
      IsGalois.card_aut_eq_finrank]
  have hidx := normRaySubgroup_index_le K m L hm
  haveI : (normRaySubgroup K m L).FiniteIndex :=
    finiteIndex_of_raySubgroup_le K m hm _ le_sup_right
  have hrel := Subgroup.relIndex_mul_index hle
  rw [hker] at hrel
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  have hne : (normRaySubgroup K m L).relIndex φ.ker ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrel
    exact Subgroup.FiniteIndex.index_ne_zero hrel.symm
  have hle1 : (normRaySubgroup K m L).relIndex φ.ker ≤ 1 := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [hrel, one_mul]
    exact hidx
  have hrel1 : (normRaySubgroup K m L).relIndex φ.ker = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel1) hle

end Reciprocity

/-- An Artin map at a modulus restricts along the inclusion from a more divisible modulus.
The proof rewrites with `Subgroup.coe_inclusion`: a definitional check would make the kernel
compare the two coprime-ideal groups, which times out. -/
theorem isArtinMap_comp_inclusion (K L : Type*) [Field K] [NumberField K] [Field L]
    [Algebra K L] {m r : Ideal (𝓞 K)} (hrm : r ≤ m)
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K m L φ) :
    IsArtinMap K r L (φ.comp (Subgroup.inclusion (coprimeIdeals_mono K hrm))) := by
  intro q hq hq0 hqr u hu P hP x
  have hu' : (((Subgroup.inclusion (coprimeIdeals_mono K hrm) u : coprimeIdeals K m) :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q := by
    rw [Subgroup.coe_inclusion]
    exact hu
  rw [MonoidHom.comp_apply]
  exact hφ q hq hq0 (eq_top_mono (sup_le_sup_left hrm q) hqr) _ hu' P hP x

/-- The away-from-the-modulus ideal norm has the underlying fractional-ideal norm. -/
theorem coe_awayIdealNorm (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (m : Ideal (𝓞 K)) (x : coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))) :
    ((awayIdealNorm K L m x : coprimeIdeals K m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      idealUnitNorm K L (x : (FractionalIdeal (𝓞 L)⁰ L)ˣ) := rfl

/-- Source: Janusz, Algebraic Number Fields (1973), V.5.6, printed163/PDF174. -/
theorem exists_common_artin_norm_preimage
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (L F : IntermediateField K M)
    [IsGalois K L] [IsAbelianGalois F M]
    (hLF : L ⊓ F = ⊥)
    (m t : Ideal (𝓞 K)) (ht : t ≠ ⊥) (htm : t ≤ m)
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K m L φ) (hU : IsUnramifiedAway K m L)
    (σ : L ≃ₐ[K] L) :
    ∃ B_F : coprimeIdeals F (t.map (algebraMap (𝓞 K) (𝓞 F))),
      φ (Subgroup.inclusion (coprimeIdeals_mono K htm)
        (awayIdealNorm K F t B_F)) = σ := by
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite ℚ F M
  haveI : Module.Finite (𝓞 K) (𝓞 F) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 F)
  haveI : Module.Finite (𝓞 F) (𝓞 M) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 M)
  obtain ⟨τ, hτ⟩ := IntermediateField.restrictRestrictAlgEquivMapHom_surjective L F hLF σ
  obtain ⟨d, hd0, hdU⟩ := exists_unramifiedAway_modulus F M
  set r := t * Ideal.under (𝓞 K) d with hr
  have hr0 : r ≠ ⊥ := by
    rw [hr, Ne, ← Ideal.zero_eq_bot, mul_eq_zero, Ideal.zero_eq_bot]
    exact not_or.mpr ⟨ht, Ideal.under_ne_bot (𝓞 K) hd0⟩
  have hrt : r ≤ t := Ideal.mul_le_right
  have hrm : r ≤ m := hrt.trans htm
  have hrd : r.map (algebraMap (𝓞 K) (𝓞 F)) ≤ d := by
    rw [hr, Ideal.map_mul]
    exact Ideal.mul_le_left.trans Ideal.map_comap_le
  have hUF : IsUnramifiedAway F (r.map (algebraMap (𝓞 K) (𝓞 F))) M := fun Q hQ hQ0 hQr =>
    hdU Q hQ hQ0 (eq_top_mono (sup_le_sup_left hrd Q) hQr)
  obtain ⟨ψ, hψ, hψs⟩ := exists_artinMap F (r.map (algebraMap (𝓞 K) (𝓞 F))) M
    (Ideal.map_ne_bot_of_ne_bot hr0) hUF
  obtain ⟨β, hβ⟩ := hψs τ
  obtain ⟨A, B, hA, hB, hAm, hBm, hAB⟩ := exists_coprime_ideal_quotient F _ β
  have hφr := isArtinMap_comp_inclusion K L hrm φ hφ
  have hUr : IsUnramifiedAway K r L := fun q hq hq0 hqr =>
    hU q hq hq0 (eq_top_mono (sup_le_sup_left hrm q) hqr)
  have hAne : (A : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hA
  have hBne : (B : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hB
  have hunit : (β : (FractionalIdeal (𝓞 F)⁰ F)ˣ) * Units.mk0 _ hBne = Units.mk0 _ hAne :=
    Units.ext hAB
  have hN : ((awayIdealNorm K F r β : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
      (Ideal.relNorm (𝓞 K) B : FractionalIdeal (𝓞 K)⁰ K) = Ideal.relNorm (𝓞 K) A := by
    have h1 := congrArg (fun u => ((idealUnitNorm K F u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K)) hunit
    simp only [map_mul, Units.val_mul] at h1
    rw [idealUnitNorm_integral K F (Units.mk0 _ hBne) B rfl,
      idealUnitNorm_integral K F (Units.mk0 _ hAne) A rfl] at h1
    rw [coe_awayIdealNorm]
    exact h1
  have key := artin_baseChange_quotient_norm K L F M r _ hφr hUr ψ hψ β A B hA hB hAm hBm hAB _
    hN
  have hres : AlgEquiv.restrictNormalHom L ((ψ β).restrictScalars K) = σ := by
    rw [hβ, ← hτ]
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [IntermediateField.restrictRestrictAlgEquivMapHom_apply]
    exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) L x
  have hBF : (Subgroup.inclusion (coprimeIdeals_mono K htm) (awayIdealNorm K F t
      (Subgroup.inclusion (coprimeIdeals_mono F (Ideal.map_mono hrt)) β)) : coprimeIdeals K m) =
        Subgroup.inclusion (coprimeIdeals_mono K hrm) (awayIdealNorm K F r β) := by
    apply Subtype.ext
    rw [Subgroup.coe_inclusion, Subgroup.coe_inclusion, coe_awayIdealNorm, coe_awayIdealNorm,
      Subgroup.coe_inclusion]
  refine ⟨Subgroup.inclusion (coprimeIdeals_mono F (Ideal.map_mono hrt)) β, ?_⟩
  rw [hBF, ← hres, key, MonoidHom.comp_apply]

namespace CyclicReciprocity

/-- Janusz V.5.6, p. 163: the norm relation of `C` forces its upper Artin value to be one. -/
theorem artin_eq_one_of_same_norm_relation
    (K L E M : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field E] [NumberField E] [Field M]
    [Algebra K L] [Algebra K E] [Algebra K M] [Algebra L M] [Algebra E M]
    [IsScalarTower K L M] [IsScalarTower K E M] [IsGalois K L]
    (hgen : Algebra.adjoin E (Set.range (algebraMap L M)) = ⊤)
    (m : Ideal (𝓞 K))
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K m L φ) (hU : IsUnramifiedAway K m L)
    (ψ : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))) →* (M ≃ₐ[E] M))
    (hψ : IsArtinMap E (m.map (algebraMap (𝓞 K) (𝓞 E))) M ψ)
    (C : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))))
    (B u : coprimeIdeals K m) (σ : L ≃ₐ[K] L) (d : ℕ)
    (hNorm : awayIdealNorm K E m C = u * B ^ (-(d : ℤ)))
    (hu : φ u = σ ^ d) (hB : φ B = σ) : ψ C = 1 := by
  have hBase : φ (awayIdealNorm K E m C) = 1 := by
    rw [hNorm, map_mul, map_zpow, hu, hB, zpow_neg, zpow_natCast, mul_inv_cancel]
  obtain ⟨A, D, hA, hD, hAm, hDm, hC⟩ :=
    exists_coprime_ideal_quotient E (m.map (algebraMap (𝓞 K) (𝓞 E))) C
  obtain ⟨a, ha⟩ := exists_coprimeIdealUnit E _ A hA hAm
  obtain ⟨b, hb⟩ := exists_coprimeIdealUnit E _ D hD hDm
  have hCb : (C : (FractionalIdeal (𝓞 E)⁰ E)ˣ) *
      (b : (FractionalIdeal (𝓞 E)⁰ E)ˣ) = a := by
    apply Units.ext
    simpa only [Units.val_mul, hb, ha] using hC
  have hNa := idealUnitNorm_integral K E (a : (FractionalIdeal (𝓞 E)⁰ E)ˣ) A ha
  have hNb := idealUnitNorm_integral K E (b : (FractionalIdeal (𝓞 E)⁰ E)ˣ) D hb
  have hN : (((awayIdealNorm K E m C) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) * (Ideal.relNorm (𝓞 K) D : FractionalIdeal (𝓞 K)⁰ K) =
        Ideal.relNorm (𝓞 K) A := by
    have hNormUnits := congrArg (idealUnitNorm K E) hCb
    rw [map_mul] at hNormUnits
    have hNormValues := congrArg
      (fun I : (FractionalIdeal (𝓞 K)⁰ K)ˣ ↦ (I : FractionalIdeal (𝓞 K)⁰ K)) hNormUnits
    change (idealUnitNorm K E (C : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) * (Ideal.relNorm (𝓞 K) D : FractionalIdeal (𝓞 K)⁰ K) =
        Ideal.relNorm (𝓞 K) A
    simpa only [Units.val_mul, hNa, hNb] using hNormValues
  have hCompatibility := artin_baseChange_quotient_norm K L E M m φ hφ hU ψ hψ
    C A D hA hD hAm hDm hC (awayIdealNorm K E m C) hN
  apply compositum_restriction_injective K L E M hgen
  have hOne : (1 : M ≃ₐ[E] M).restrictScalars K = (1 : M ≃ₐ[K] M) := by
    ext x
    rfl
  change AlgEquiv.restrictNormalHom L ((ψ C).restrictScalars K) =
    AlgEquiv.restrictNormalHom L ((1 : M ≃ₐ[E] M).restrictScalars K)
  rw [hOne, map_one]
  exact hCompatibility.trans hBase

/-- Janusz V.5.6, p. 163: a kernel element of the upper Artin map is a norm-ray element. -/
theorem mem_normRay_of_artin_eq_one
    (K Ω : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    [Field Ω] [Algebra K Ω]
    (L F : IntermediateField K Ω) [NumberField L] [NumberField F]
    (n : ℕ) [NeZero n] (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (hjoin : F ⊔ IntermediateField.adjoin K {ξ} = L ⊔ IntermediateField.adjoin K {ξ})
    (t : Ideal (𝓞 K)) (ht0 : t ≠ ⊥)
    (htn : t ≤ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) :
    let M : IntermediateField K Ω := L ⊔ F
    letI : NumberField M := NumberField.of_module_finite K M
    letI : Algebra F M := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
    letI : IsScalarTower K F M := IsScalarTower.of_algebraMap_eq' (by rfl)
    ∀ (ψ : coprimeIdeals F (t.map (algebraMap (𝓞 K) (𝓞 F))) →* (M ≃ₐ[F] M)),
      IsArtinMap F (t.map (algebraMap (𝓞 K) (𝓞 F))) M ψ →
      ∀ C : coprimeIdeals F (t.map (algebraMap (𝓞 K) (𝓞 F))),
      ψ C = 1 → C ∈ normRaySubgroup F (t.map (algebraMap (𝓞 K) (𝓞 F))) M := by
  let M : IntermediateField K Ω := L ⊔ F
  letI : NumberField M := NumberField.of_module_finite K M
  letI : Algebra F M := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
  letI : IsScalarTower K F M := IsScalarTower.of_algebraMap_eq' (by rfl)
  dsimp only
  intro ψ hψ C hc
  letI : IsTotallyComplex F := NumberField.isTotallyComplex_of_algebra K F
  let Q : IntermediateField F Ω := IntermediateField.adjoin F {ξ}
  have hQeq : Q.restrictScalars K = F ⊔ IntermediateField.adjoin K {ξ} :=
    IntermediateField.restrictScalars_adjoin_eq_sup K F {ξ}
  have hLQ : L ≤ Q.restrictScalars K := by
    rw [hQeq, hjoin]
    exact le_sup_left
  have hFQ : F ≤ Q.restrictScalars K := by
    rw [hQeq]
    exact le_sup_left
  have hMQ : M ≤ Q.restrictScalars K := sup_le hLQ hFQ
  -- This is an actual inclusion of the original M, not an equivalence to a new carrier.
  let ι : M →ₐ[F] Q :=
    { (IntermediateField.inclusion hMQ).toRingHom with
      commutes' := by intro x; rfl }
  letI : Algebra M Q := ι.toRingHom.toAlgebra
  letI : IsScalarTower F M Q := IsScalarTower.of_algebraMap_eq' ι.comp_algebraMap.symm
  letI : IsCyclotomicExtension {n} F Q :=
    CyclotomicBaseChange.rootField_isCyclotomic n (NeZero.pos n) ξ hξ
  letI : NumberField Q := IsCyclotomicExtension.numberField {n} F Q
  letI : IsAbelianGalois F Q := IsCyclotomicExtension.isAbelianGalois {n} F Q
  letI : IsAbelianGalois F M := IsAbelianGalois.tower_bot F M Q
  let ζ : Q := ⟨ξ, IntermediateField.mem_adjoin_simple_self F ξ⟩
  have hζ : IsPrimitiveRoot ζ n := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact hξ
  let N : Ideal (𝓞 F) := Ideal.span ({(n : 𝓞 F)} : Set (𝓞 F))
  let tF : Ideal (𝓞 F) := t.map (algebraMap (𝓞 K) (𝓞 F))
  have hN0 : N ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have htF0 : tF ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot ht0
  have htFN : tF ≤ N := by
    have h := Ideal.map_mono (f := algebraMap (𝓞 K) (𝓞 F)) htn
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using h
  have hUQN : IsUnramifiedAway F N Q := cyclotomic_isUnramifiedAway F Q n
  have hUQt : IsUnramifiedAway F tF Q := by
    intro q hq hq0 hqt
    exact hUQN q hq hq0 (top_unique (hqt ▸ sup_le_sup_left htFN q))
  have hUMt : IsUnramifiedAway F tF M := by
    -- Native tower proof on the ORIGINAL M; no ClassFieldEmbedding/Existence dependency.
    intro q hq hq0 hqt P hP
    letI := hq
    rcases hP with ⟨hPprime, hPover⟩
    letI := hPprime
    letI := hPover
    obtain ⟨R, hRprime, hRover⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := 𝓞 Q) P (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 M) (𝓞 Q))]
        exact bot_le)
    letI := hRprime
    letI : R.LiesOver P := ⟨hRover.symm⟩
    letI : R.LiesOver q := Ideal.LiesOver.trans R P q
    have hR : Ideal.ramificationIdx q R = 1 :=
      hUQt q hq hq0 hqt R ⟨hRprime, inferInstance⟩
    rw [Ideal.ramificationIdx_algebra_tower' q P R] at hR
    exact Nat.eq_one_of_mul_eq_one_right hR
  obtain ⟨φN, hφN, _⟩ := exists_artinMap F N Q hN0 hUQN
  obtain ⟨φt, hφt, _⟩ := exists_artinMap F tF Q htF0 hUQt
  have hRayN := cyclotomic_ray_le_artin_ker F Q n ζ hζ φN hφN
  have hRayt := ray_le_artin_ker_of_modulus_le F Q tF N htFN hUQt
    φN hφN φt hφt hRayN
  have hRayM := ray_le_artin_ker_subfield F Q M tF hUMt φt hφt ψ hψ hRayt
  obtain ⟨ρ, hρ, hsurj⟩ := exists_artinMap F tF M htF0 hUMt
  have heq : ψ = ρ := isArtinMap_unique F tF M hUMt hψ hρ
  have hψsurj : Function.Surjective ψ := heq.symm ▸ hsurj
  rw [← artin_ker_eq_normRaySubgroup F tF M htF0 hUMt ψ hψ hψsurj hRayM]
  exact hc

end CyclicReciprocity

/-- Source: Janusz, Algebraic Number Fields (1973), V.5.6, printed163/PDF174;
III.3.1, printed103–104/PDF114–115. -/
theorem same_ideal_mem_normRay
    (K Ω : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    [Field Ω] [Algebra K Ω]
    (L F : IntermediateField K Ω) [NumberField L] [NumberField F] [IsGalois K L]
    (n : ℕ) [NeZero n] (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (hjoin : F ⊔ IntermediateField.adjoin K {ξ} = L ⊔ IntermediateField.adjoin K {ξ})
    (t : Ideal (𝓞 K)) (ht0 : t ≠ ⊥)
    (htn : t ≤ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)))
    (φ : coprimeIdeals K t →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K t L φ) (hU : IsUnramifiedAway K t L)
    (C : coprimeIdeals F (t.map (algebraMap (𝓞 K) (𝓞 F))))
    (B u : coprimeIdeals K t) (σ : L ≃ₐ[K] L) (d : ℕ)
    (hNorm : awayIdealNorm K F t C = u * B ^ (-(d : ℤ)))
    (hu : φ u = σ ^ d) (hB : φ B = σ) :
    let M : IntermediateField K Ω := L ⊔ F
    letI : NumberField M := NumberField.of_module_finite K M
    letI : Algebra F M := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
    letI : IsScalarTower K F M := IsScalarTower.of_algebraMap_eq' (by rfl)
    C ∈ normRaySubgroup F (t.map (algebraMap (𝓞 K) (𝓞 F))) M := by
  let M : IntermediateField K Ω := L ⊔ F
  letI : NumberField M := NumberField.of_module_finite K M
  letI : Algebra F M := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
  letI : IsScalarTower K F M := IsScalarTower.of_algebraMap_eq' (by rfl)
  letI : Algebra L M := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' (by rfl)
  dsimp only
  letI : IsTotallyComplex F := NumberField.isTotallyComplex_of_algebra K F
  let Q : IntermediateField F Ω := IntermediateField.adjoin F {ξ}
  have hQeq : Q.restrictScalars K = F ⊔ IntermediateField.adjoin K {ξ} :=
    IntermediateField.restrictScalars_adjoin_eq_sup K F {ξ}
  have hLQ : L ≤ Q.restrictScalars K := by
    rw [hQeq, hjoin]
    exact le_sup_left
  have hFQ : F ≤ Q.restrictScalars K := by
    rw [hQeq]
    exact le_sup_left
  have hMQ : M ≤ Q.restrictScalars K := sup_le hLQ hFQ
  -- This is an actual inclusion of the original M, not an equivalence to a new carrier.
  let ι : M →ₐ[F] Q :=
    { (IntermediateField.inclusion hMQ).toRingHom with
      commutes' := by intro x; rfl }
  letI : Algebra M Q := ι.toRingHom.toAlgebra
  letI : IsScalarTower F M Q := IsScalarTower.of_algebraMap_eq' ι.comp_algebraMap.symm
  letI : IsCyclotomicExtension {n} F Q :=
    CyclotomicBaseChange.rootField_isCyclotomic n (NeZero.pos n) ξ hξ
  letI : NumberField Q := IsCyclotomicExtension.numberField {n} F Q
  letI : IsAbelianGalois F Q := IsCyclotomicExtension.isAbelianGalois {n} F Q
  letI : IsAbelianGalois F M := IsAbelianGalois.tower_bot F M Q
  let N : Ideal (𝓞 F) := Ideal.span ({(n : 𝓞 F)} : Set (𝓞 F))
  let tF : Ideal (𝓞 F) := t.map (algebraMap (𝓞 K) (𝓞 F))
  have htF0 : tF ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot ht0
  have htFN : tF ≤ N := by
    have h := Ideal.map_mono (f := algebraMap (𝓞 K) (𝓞 F)) htn
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using h
  have hUQN : IsUnramifiedAway F N Q := cyclotomic_isUnramifiedAway F Q n
  have hUQt : IsUnramifiedAway F tF Q := by
    intro q hq hq0 hqt
    exact hUQN q hq hq0 (top_unique (hqt ▸ sup_le_sup_left htFN q))
  have hUMt : IsUnramifiedAway F tF M := by
    -- Native tower proof on the ORIGINAL M; no ClassFieldEmbedding/Existence dependency.
    intro q hq hq0 hqt P hP
    letI := hq
    rcases hP with ⟨hPprime, hPover⟩
    letI := hPprime
    letI := hPover
    obtain ⟨R, hRprime, hRover⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := 𝓞 Q) P (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 M) (𝓞 Q))]
        exact bot_le)
    letI := hRprime
    letI : R.LiesOver P := ⟨hRover.symm⟩
    letI : R.LiesOver q := Ideal.LiesOver.trans R P q
    have hR : Ideal.ramificationIdx q R = 1 :=
      hUQt q hq hq0 hqt R ⟨hRprime, inferInstance⟩
    rw [Ideal.ramificationIdx_algebra_tower' q P R] at hR
    exact Nat.eq_one_of_mul_eq_one_right hR
  -- This choice uses only unramifiedness and abelian Galoisness, not ψ C = 1 or reciprocity.
  obtain ⟨ψ, hψ, _⟩ := exists_artinMap F tF M htF0 hUMt
  have hgen : Algebra.adjoin F (Set.range (algebraMap L M)) = ⊤ := by
    let A : Subalgebra F M := Algebra.adjoin F (Set.range (algebraMap L M))
    have hL : L.toSubalgebra ≤ (A.restrictScalars K).map M.val := by
      intro x hx
      apply Subalgebra.mem_map.mpr
      refine ⟨algebraMap L M ⟨x, hx⟩, ?_, ?_⟩
      · change algebraMap L M ⟨x, hx⟩ ∈
          Algebra.adjoin F (Set.range (algebraMap L M))
        exact (Algebra.subset_adjoin (R := F) (A := M)
          (s := Set.range (algebraMap L M))) ⟨⟨x, hx⟩, rfl⟩
      · rfl
    have hF : F.toSubalgebra ≤ (A.restrictScalars K).map M.val := by
      intro x hx
      apply Subalgebra.mem_map.mpr
      refine ⟨algebraMap F M ⟨x, hx⟩, ?_, ?_⟩
      · change algebraMap F M ⟨x, hx⟩ ∈ A
        exact A.algebraMap_mem ⟨x, hx⟩
      · rfl
    have hM : M.toSubalgebra ≤ (A.restrictScalars K).map M.val := by
      change (L ⊔ F).toSubalgebra ≤ _
      rw [IntermediateField.sup_toSubalgebra_of_isAlgebraic_left]
      exact sup_le hL hF
    change A = ⊤
    apply top_unique
    intro x _
    obtain ⟨y, hy, hyx⟩ := Subalgebra.mem_map.mp (hM x.property)
    have hyx' : y = x := Subtype.ext hyx
    simpa only [hyx'] using hy
  have hc : ψ C = 1 := CyclicReciprocity.artin_eq_one_of_same_norm_relation
    K L F M hgen t φ hφ hU ψ hψ C B u σ d hNorm hu hB
  exact CyclicReciprocity.mem_normRay_of_artin_eq_one K Ω L F n ξ hξ hjoin t ht0 htn
    ψ hψ C hc

namespace CyclicReciprocity

theorem exists_nat_exponents_orderOf_dvd_sum
    {G ι : Type*} [CommGroup G] (σ : G) (hσ : IsOfFinOrder σ)
    (s : Finset ι) (g : ι → G)
    (hg : ∀ i ∈ s, g i ∈ Subgroup.zpowers σ)
    (hprod : ∏ i ∈ s, g i = 1) :
    ∃ d : ι → ℕ, (∀ i ∈ s, g i = σ ^ d i) ∧ orderOf σ ∣ ∑ i ∈ s, d i := by
  classical
  have hex : ∀ i, ∃ n : ℕ, i ∈ s → g i = σ ^ n := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (g i) σ).mp
        (hσ.mem_powers_iff_mem_zpowers.mpr (hg i hi))
      exact ⟨n, fun _ ↦ hn.symm⟩
    · exact ⟨0, fun h ↦ (hi h).elim⟩
  choose d hd using hex
  refine ⟨d, hd, orderOf_dvd_iff_pow_eq_one.mpr ?_⟩
  calc
    σ ^ (∑ i ∈ s, d i) = ∏ i ∈ s, σ ^ d i :=
      (Finset.prod_pow_eq_pow_sum s d σ).symm
    _ = ∏ i ∈ s, g i := Finset.prod_congr rfl fun i hi ↦ (hd i hi).symm
    _ = 1 := hprod


theorem normImage_map_awayIdealNorm_le
    (K E F : Type*) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field F] [NumberField F] [Algebra K E] [Algebra K F] [Algebra E F]
    [IsScalarTower K E F] (m : Ideal (𝓞 K)) :
    (normImage E (m.map (algebraMap (𝓞 K) (𝓞 E))) F).map
      (awayIdealNorm K E m) ≤ normImage K m F := by
  have hmF : (m.map (algebraMap (𝓞 K) (𝓞 E))).map (algebraMap (𝓞 E) (𝓞 F)) =
      m.map (algebraMap (𝓞 K) (𝓞 F)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 E) (𝓞 F)]
  rintro u ⟨v, hv, rfl⟩
  rw [← awayIdealNorm_range E F] at hv
  obtain ⟨w, rfl⟩ := hv
  let wF : coprimeIdeals F (m.map (algebraMap (𝓞 K) (𝓞 F))) :=
    ⟨w, by simpa only [hmF] using w.property⟩
  rw [← awayIdealNorm_range K F]
  refine ⟨wF, ?_⟩
  apply Subtype.ext
  exact (idealUnitNorm_tower K E F w).symm

theorem normImage_tower_le
    (K E F : Type*) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field F] [NumberField F] [Algebra K E] [Algebra K F] [Algebra E F]
    [IsScalarTower K E F] (m : Ideal (𝓞 K)) :
    normImage K m F ≤ normImage K m E := by
  have hmF : (m.map (algebraMap (𝓞 K) (𝓞 E))).map (algebraMap (𝓞 E) (𝓞 F)) =
      m.map (algebraMap (𝓞 K) (𝓞 F)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 E) (𝓞 F)]
  intro u hu
  rw [← awayIdealNorm_range K F] at hu
  obtain ⟨w, rfl⟩ := hu
  let wF : coprimeIdeals F
      ((m.map (algebraMap (𝓞 K) (𝓞 E))).map (algebraMap (𝓞 E) (𝓞 F))) :=
    ⟨w, by simpa only [hmF] using w.property⟩
  rw [← awayIdealNorm_range K E]
  refine ⟨awayIdealNorm E F (m.map (algebraMap (𝓞 K) (𝓞 E))) wF, ?_⟩
  apply Subtype.ext
  exact idealUnitNorm_tower K E F w


theorem normRay_transport
    (K L E F : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field E] [NumberField E] [Field F] [NumberField F]
    [Algebra K L] [Algebra K E] [Algebra K F] [Algebra L F] [Algebra E F]
    [IsScalarTower K L F] [IsScalarTower K E F] (m : Ideal (𝓞 K)) :
    (normRaySubgroup E (m.map (algebraMap (𝓞 K) (𝓞 E))) F).map
      (awayIdealNorm K E m) ≤ normRaySubgroup K m L := by
  unfold normRaySubgroup
  rw [Subgroup.map_sup]
  exact sup_le_sup
    ((normImage_map_awayIdealNorm_le K E F m).trans (normImage_tower_le K L F m))
    (raySubgroup_map_awayIdealNorm_le K E m)


theorem exists_norm_lifts_of_splitting
    {ι : Type*} (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] (E : ι → Type*) [∀ i, Field (E i)] [∀ i, NumberField (E i)]
    [∀ i, Algebra K (E i)] [∀ i, Algebra (E i) F] [∀ i, IsScalarTower K (E i) F]
    (m : Ideal (𝓞 K))
    (B_F : coprimeIdeals F (m.map (algebraMap (𝓞 K) (𝓞 F))))
    (q : ι → Ideal (𝓞 K)) (hq : ∀ i, q i ∈ splittingIdeals K (E i))
    (hqm : ∀ i, q i ⊔ m = ⊤) (u : ι → coprimeIdeals K m)
    (hu : ∀ i, ((u i : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q i)
    (e : ι → ℤ) (d : ι → ℕ) :
    ∀ i, ∃ C : coprimeIdeals (E i) (m.map (algebraMap (𝓞 K) (𝓞 (E i)))),
      awayIdealNorm K (E i) m C = u i ^ e i * (awayIdealNorm K F m B_F ^ d i)⁻¹ := by
  intro i
  have hB : awayIdealNorm K F m B_F ∈ normImage K m F := by
    rw [← awayIdealNorm_range K F]
    exact ⟨B_F, rfl⟩
  have hBi := normImage_tower_le K (E i) F m hB
  have hqi := mem_normImage_of_splits K m (E i) (hq i) (hqm i) (u i) (hu i)
  have hC : u i ^ e i * (awayIdealNorm K F m B_F ^ d i)⁻¹ ∈ normImage K m (E i) :=
    (normImage K m (E i)).mul_mem
      ((normImage K m (E i)).zpow_mem hqi (e i))
      ((normImage K m (E i)).inv_mem ((normImage K m (E i)).pow_mem hBi (d i)))
  rw [← awayIdealNorm_range K (E i)] at hC
  exact hC


theorem mem_normRay_of_factor_products {ι : Type*}
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (m t : Ideal (𝓞 K)) (htm : t ≤ m)
    (s : Finset ι) (u : ι → coprimeIdeals K t) (e : ι → ℤ)
    (B : coprimeIdeals K t) (d : ι → ℕ) (A : coprimeIdeals K m)
    (hfactor : A = Subgroup.inclusion (coprimeIdeals_mono K htm)
      (∏ i ∈ s, u i ^ e i))
    (hCi : ∀ i ∈ s,
      Subgroup.inclusion (coprimeIdeals_mono K htm)
        (u i ^ e i * (B ^ d i)⁻¹) ∈ normRaySubgroup K m L)
    (hdiv : Module.finrank K L ∣ ∑ i ∈ s, d i) :
    A ∈ normRaySubgroup K m L := by
  let j : coprimeIdeals K t →* coprimeIdeals K m :=
    Subgroup.inclusion (coprimeIdeals_mono K htm)
  let H : Subgroup (coprimeIdeals K m) := normRaySubgroup K m L
  have hc : ∀ i ∈ s, j (u i ^ e i) * (j B ^ d i)⁻¹ ∈ H := by
    intro i hi
    have h := hCi i hi
    change j (u i ^ e i * (B ^ d i)⁻¹) ∈ H at h
    simpa only [map_mul, map_inv, map_pow] using h
  have hprod := H.prod_mem hc
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_pow_eq_pow_sum] at hprod
  have hBn : j B ^ Module.finrank K L ∈ H :=
    (show normImage K m L ≤ H from le_sup_left)
      (pow_finrank_mem_normImage K L m (j B))
  have hpow : j B ^ (∑ i ∈ s, d i) ∈ H := by
    obtain ⟨c, hc⟩ := hdiv
    rw [hc, pow_mul]
    exact H.pow_mem hBn c
  have hmem : (∏ i ∈ s, j (u i ^ e i)) ∈ H := by
    have h := H.mul_mem hprod hpow
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  have hA : A = ∏ i ∈ s, j (u i ^ e i) := by
    change A = j (∏ i ∈ s, u i ^ e i) at hfactor
    simpa only [map_prod] using hfactor
  rw [hA]
  exact hmem

end CyclicReciprocity

open scoped IsMulCommutative in
/-- Source: Janusz, Algebraic Number Fields (1973), V.5.6, printed163–164/PDF174–175. -/
theorem cyclic_kernel_element_mem_normRay
    {ι : Type*} [Fintype ι]
    (K M : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]
    (L F : IntermediateField K M) (Fi : ι → IntermediateField K M)
    (hF : F = ⨆ i, Fi i) (hFL : F ⊓ L = ⊥)
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (ξ : ι → M)
    (hξ : ∀ i, IsPrimitiveRoot (ξ i) (n i))
    (hjoin : ∀ i, Fi i ⊔ IntermediateField.adjoin K {ξ i} =
      L ⊔ IntermediateField.adjoin K {ξ i})
    (q : ι → Ideal (𝓞 K)) (hq : ∀ i, q i ∈ splittingIdeals K (Fi i))
    (m t : Ideal (𝓞 K)) (ht0 : t ≠ ⊥) (htm : t ≤ m)
    (htn : ∀ i, t ≤ Ideal.span ({(n i : 𝓞 K)} : Set (𝓞 K)))
    (hqt : ∀ i, q i ⊔ t = ⊤)
    (u : ι → coprimeIdeals K t)
    (hu : ∀ i, ((u i : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = q i)
    (e : ι → ℤ) (A : coprimeIdeals K m)
    (hfactor : A = Subgroup.inclusion (coprimeIdeals_mono K htm) (∏ i, u i ^ e i))
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K m L φ) (hU : IsUnramifiedAway K m L)
    (hA : A ∈ φ.ker) (σ : L ≃ₐ[K] L) (hgen : Subgroup.zpowers σ = ⊤) :
    A ∈ normRaySubgroup K m L := by
  classical
  let j : coprimeIdeals K t →* coprimeIdeals K m :=
    Subgroup.inclusion (coprimeIdeals_mono K htm)
  let φt : coprimeIdeals K t →* (L ≃ₐ[K] L) := φ.comp j
  have hUt : IsUnramifiedAway K t L := by
    intro p hp hp0 hpt P hP
    have hpm : p ⊔ m = ⊤ := by
      apply top_unique
      rw [← hpt]
      exact sup_le_sup_left htm p
    exact hU p hp hp0 hpm P hP
  have hφt : IsArtinMap K t L φt := by
    intro p hp hp0 hpt v hv P hP x
    have hpm : p ⊔ m = ⊤ := by
      apply top_unique
      rw [← hpt]
      exact sup_le_sup_left htm p
    exact hφ p hp hp0 hpm (j v)
      (by simpa only [j, Subgroup.coe_inclusion] using hv) P hP x
  have hprod : ∏ i, φt (u i ^ e i) = 1 := by
    rw [← map_prod]
    change φ (Subgroup.inclusion (coprimeIdeals_mono K htm) (∏ i, u i ^ e i)) = 1
    rw [← hfactor]
    exact hA
  obtain ⟨d, hd, hdiv⟩ := CyclicReciprocity.exists_nat_exponents_orderOf_dvd_sum σ
    (isOfFinOrder_of_finite σ) Finset.univ (fun i ↦ φt (u i ^ e i))
    (fun i _ ↦ hgen.ge (Subgroup.mem_top _)) hprod
  have horder : orderOf σ = Module.finrank K L := by
    calc
      orderOf σ = Nat.card (L ≃ₐ[K] L) := orderOf_eq_card_of_zpowers_eq_top hgen
      _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  rw [horder] at hdiv
  obtain ⟨B_F, hBφ⟩ := exists_common_artin_norm_preimage K M L F
    (by simpa only [inf_comm] using hFL) m t ht0 htm φ hφ hU σ
  let B : coprimeIdeals K t := awayIdealNorm K F t B_F
  have hBt : φt B = σ := hBφ
  have hiF : ∀ i, Fi i ≤ F := by
    intro i
    rw [hF]
    exact le_iSup Fi i
  letI algebraFiF : ∀ i, Algebra (Fi i) F :=
    fun i ↦ (IntermediateField.inclusion (hiF i)).toRingHom.toAlgebra
  letI towerFiF : ∀ i, IsScalarTower K (Fi i) F :=
    fun _ ↦ IsScalarTower.of_algebraMap_eq' (by rfl)
  obtain ⟨C, hC⟩ := Classical.axiomOfChoice
    (CyclicReciprocity.exists_norm_lifts_of_splitting K F (fun i ↦ ↥(Fi i)) t B_F q hq hqt u hu e d)
  have hCi : ∀ i ∈ (Finset.univ : Finset ι),
      Subgroup.inclusion (coprimeIdeals_mono K htm)
        (u i ^ e i * (B ^ d i)⁻¹) ∈ normRaySubgroup K m L := by
    intro i hi
    letI : NeZero (n i) := ⟨(hn i).ne'⟩
    let J : IntermediateField K M := L ⊔ Fi i
    letI : NumberField J := NumberField.of_module_finite K J
    letI : Algebra (Fi i) J := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
    letI : IsScalarTower K (Fi i) J := IsScalarTower.of_algebraMap_eq' (by rfl)
    letI : Algebra L J := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
    letI : IsScalarTower K L J := IsScalarTower.of_algebraMap_eq' (by rfl)
    have hnorm : awayIdealNorm K (Fi i) t (C i) =
        u i ^ e i * B ^ (-(d i : ℤ)) := by
      simpa only [B, zpow_neg, zpow_natCast] using hC i
    have hlocal : C i ∈ normRaySubgroup (Fi i)
        (t.map (algebraMap (𝓞 K) (𝓞 (Fi i)))) J :=
      same_ideal_mem_normRay K M L (Fi i) (n i) (ξ i) (hξ i) (hjoin i)
        t ht0 (htn i) φt hφt hUt (C i) B (u i ^ e i) σ (d i)
        hnorm (hd i hi) hBt
    have hnormt : awayIdealNorm K (Fi i) t (C i) ∈ normRaySubgroup K t L :=
      CyclicReciprocity.normRay_transport K L (Fi i) J t ⟨C i, hlocal, rfl⟩
    have hvaluet : u i ^ e i * (B ^ d i)⁻¹ ∈ normRaySubgroup K t L := by
      simpa only [hC i] using hnormt
    exact normRaySubgroup_restrictModulus K L t m htm
      ⟨u i ^ e i * (B ^ d i)⁻¹, hvaluet, rfl⟩
  exact CyclicReciprocity.mem_normRay_of_factor_products K L m t htm Finset.univ u e B d A hfactor
    hCi hdiv

namespace CyclicReciprocity

section Families
open NumberField IntermediateField Polynomial Cox.Chebotarev
open AuxiliaryFields ArtinAuxiliary CyclotomicFrobenius
open scoped IsMulCommutative

-- Janusz V.5.6, pp162–163: one selected partner family, actual Frobenius
-- coordinates, and the same fixed fields in a common finite abelian ambient.
-- Scratch composition only; planned children remain conditional evidence.
theorem same_auxiliary_family
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [IsAbelianGalois K M]
    (r : ℕ) (L : IntermediateField K M) (E : Fin r → IntermediateField K M)
    (σ : Gal(L/K)) (hσ : Subgroup.zpowers σ = ⊤)
    (m : Fin r → ℕ) [∀ i, NeZero (m i)]
    [∀ i, IsCyclotomicExtension {m i} K (E i)]
    (hirr : ∀ i, Irreducible (cyclotomic (m i) K))
    (q : Fin r → Ideal (𝓞 K)) [∀ i, (q i).IsPrime]
    (hU : ∀ i, UnramifiedIn K M (q i))
    (hcop : ∀ i, (q i).absNorm.Coprime (m i))
    (u v : ∀ i, (ZMod (m i))ˣ)
    (hu : ∀ i, (u i : ZMod (m i)) = (q i).absNorm)
    (hnu : ∀ i, Nat.card Gal(L/K) ∣ orderOf (u i))
    (hnv : ∀ i, Nat.card Gal(L/K) ∣ orderOf (v i))
    (hind : ∀ i, Disjoint (Subgroup.zpowers (u i)) (Subgroup.zpowers (v i)))
    (hInf : ∀ i,
      (L ⊔ ⨆ j : {j : Fin r // j < i}, E j.1) ⊓ E i = ⊥) :
    ∃ τ : ∀ i, Gal(E i/K),
      (∀ i, q i ∈ splittingIdeals K
        (auxiliaryFixedField L (E i) σ (frobeniusClass K L (q i)).out
          (τ i) (frobeniusClass K (E i) (q i)).out)) ∧
      (∀ i, auxiliaryFixedField L (E i) σ (frobeniusClass K L (q i)).out
          (τ i) (frobeniusClass K (E i) (q i)).out ⊔ E i = L ⊔ E i) ∧
      (⨆ i, auxiliaryFixedField L (E i) σ (frobeniusClass K L (q i)).out
          (τ i) (frobeniusClass K (E i) (q i)).out) ⊓ L = ⊥ := by
  have hUE (i : Fin r) : UnramifiedIn K (E i) (q i) :=
    unramifiedIn_tower_descend K (E i) M (q i) (hU i)
  have hpartners (i : Fin r) : ∃ τ : Gal(E i/K),
      Nat.card Gal(L/K) ∣ orderOf τ ∧
      Disjoint (Subgroup.zpowers τ)
        (Subgroup.zpowers (frobeniusClass K (E i) (q i)).out) :=
    independent_frobenius_partner K (E i) (m i) (hirr i) (q i) (hUE i)
      (hcop i) (Nat.card Gal(L/K)) (u i) (v i) (hu i) (hnv i) (hind i)
  choose τ hτ hindτ using hpartners
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro i
    exact splits_auxiliaryFixedField K M L (E i) σ (τ i) (q i) (hU i)
  · intro i
    have hu' : ZMod.unitOfCoprime (q i).absNorm (hcop i) = u i := by
      apply Units.ext
      exact (hu i).symm
    have horder : orderOf (frobeniusClass K (E i) (q i)).out = orderOf (u i) := by
      rw [← MulEquiv.orderOf_eq (IsCyclotomicExtension.autEquivPow (E i) (hirr i))]
      rw [autEquivPow_frobeniusClass_out K (E i) (m i) (hirr i) (q i) (hUE i)
        (hcop i), hu']
    apply auxiliaryFixedField_sup_eq_sup L (E i) σ _ (τ i) _
    · exact (orderOf_dvd_natCard σ).trans (hτ i)
    · rw [horder]
      exact (orderOf_dvd_natCard (frobeniusClass K L (q i)).out).trans (hnu i)
    · exact hindτ i
  · exact auxiliary_iSup_inf_eq_bot_of_simultaneous_restriction L E σ hσ
      (fun i => (frobeniusClass K L (q i)).out) τ
      (fun i => (frobeniusClass K (E i) (q i)).out)
      (simultaneous_restriction_surjective_of_prefix_inf r L E hInf)



theorem common_ambient (K : Type*) [Field K] [NumberField K]
    (L : IntermediateField K (AlgebraicClosure K)) [NumberField L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (r : ℕ) (m : Fin r → ℕ) (ξ : Fin r → AlgebraicClosure K)
    (hm : ∀ i, 0 < m i) (hξ : ∀ i, IsPrimitiveRoot (ξ i) (m i)) :
    let M := L ⊔ ⨆ i, adjoin K {ξ i}
    NumberField M ∧ IsAbelianGalois K M := by
  let E : Fin r → IntermediateField K (AlgebraicClosure K) := fun i => adjoin K {ξ i}
  let M := L ⊔ ⨆ i, E i
  change NumberField M ∧ IsAbelianGalois K M
  letI : ∀ i : Fin r, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  letI : ∀ i : Fin r, IsCyclotomicExtension {m i} K (E i) := fun i =>
    CyclotomicBaseChange.rootField_isCyclotomic (m i) (hm i) (ξ i) (hξ i)
  letI : ∀ i : Fin r, FiniteDimensional K (E i) := fun i =>
    IsCyclotomicExtension.finite_of_singleton (m i) K (E i)
  letI : FiniteDimensional K M := inferInstance
  letI : NumberField M := NumberField.of_module_finite K M
  letI : IsAbelianGalois K L := IsAbelianGalois.of_isCyclic K L
  letI : ∀ i : Fin r, IsAbelianGalois K (E i) := fun i =>
    IsCyclotomicExtension.isAbelianGalois {m i} K (E i)
  letI : IsGalois K M := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hL : L ≤ M := le_sup_left
  have hE (i : Fin r) : E i ≤ M := le_sup_of_le_right (le_iSup E i)
  let L' := L.restrict hL
  let E' (i : Fin r) := (E i).restrict (hE i)
  letI : IsAbelianGalois K L' :=
    IsAbelianGalois.of_algHom (restrict_algEquiv hL).symm.toAlgHom
  letI : ∀ i : Fin r, IsAbelianGalois K (E' i) := fun i =>
    IsAbelianGalois.of_algHom (restrict_algEquiv (hE i)).symm.toAlgHom
  have hAll : lift (⨆ i, E' i) = ⨆ i, E i := by
    change (⨆ i, E' i).map M.val = _
    rw [IntermediateField.map_iSup]
    change (⨆ i, lift ((E i).restrict (hE i))) = _
    simp only [lift_restrict]
  have hSup : L' ⊔ ⨆ i, E' i = ⊤ := by
    apply lift_injective M
    rw [lift_sup, lift_top]
    change lift (L.restrict hL) ⊔ lift (⨆ i, E' i) = M
    rw [lift_restrict, hAll]
  have hcomm : IsMulCommutative (M ≃ₐ[K] M) := IsMulCommutative.of_comm (by
    intro σ τ
    apply Cox.ClassFieldTheory.AuxiliaryFields.simultaneous_restriction_injective_of_sup_eq_top
      L' E' hSup
    apply Prod.ext
    · change (AlgEquiv.restrictNormalHom L') (σ * τ) =
        (AlgEquiv.restrictNormalHom L') (τ * σ)
      rw [map_mul, map_mul, mul_comm']
    · funext i
      change (AlgEquiv.restrictNormalHom (E' i)) (σ * τ) =
        (AlgEquiv.restrictNormalHom (E' i)) (τ * σ)
      rw [map_mul, map_mul, mul_comm'])
  exact ⟨inferInstance, { toIsGalois := inferInstance, is_comm := hcomm.is_comm }⟩

-- Instantiate the preceding contract with the same selected roots and then
-- lift the actual fixed fields back into the original ambient closure.
theorem same_root_field_family
    (K : Type*) [Field K] [NumberField K]
    (L : IntermediateField K (AlgebraicClosure K)) [NumberField L]
    [IsGalois K L] [IsCyclic Gal(L/K)]
    (r : ℕ) (σ : Gal(L/K)) (hσ : Subgroup.zpowers σ = ⊤)
    (m : Fin r → ℕ) (ξ : Fin r → AlgebraicClosure K)
    (hm : ∀ i, 0 < m i) (hξ : ∀ i, IsPrimitiveRoot (ξ i) (m i))
    (q : Fin r → Ideal (𝓞 K)) [∀ i, (q i).IsPrime]
    (hU : ∀ i, UnramifiedIn K L (q i))
    (hcop : ∀ i j, (q i).absNorm.Coprime (m j))
    (u v : ∀ i, (ZMod (m i))ˣ)
    (hu : ∀ i, (u i : ZMod (m i)) = (q i).absNorm)
    (hnu : ∀ i, Nat.card Gal(L/K) ∣ orderOf (u i))
    (hnv : ∀ i, Nat.card Gal(L/K) ∣ orderOf (v i))
    (hind : ∀ i, Disjoint (Subgroup.zpowers (u i)) (Subgroup.zpowers (v i)))
    (hInf : ∀ i,
      (L.restrictScalars ℚ ⊔ ⨆ j : {j : Fin r // j < i}, adjoin ℚ {ξ j.1}) ⊓
        adjoin ℚ {ξ i} = ⊥) :
    ∃ F : Fin r → IntermediateField K (AlgebraicClosure K),
      (∀ i, F i ≤ L ⊔ ⨆ j, adjoin K {ξ j}) ∧
      (∀ i, q i ∈ splittingIdeals K (F i)) ∧
      (∀ i, F i ⊔ adjoin K {ξ i} = L ⊔ adjoin K {ξ i}) ∧
      (⨆ i, F i) ⊓ L = ⊥ := by
  let E : Fin r → IntermediateField K (AlgebraicClosure K) := fun i => adjoin K {ξ i}
  let M := L ⊔ ⨆ i, E i
  have hambient := common_ambient K L r m ξ hm hξ
  letI : NumberField M := hambient.1
  letI : IsAbelianGalois K M := hambient.2
  have hL : L ≤ M := le_sup_left
  have hE (i : Fin r) : E i ≤ M := le_sup_of_le_right (le_iSup E i)
  let L' := L.restrict hL
  let E' (i : Fin r) := (E i).restrict (hE i)
  let e : L ≃ₐ[K] L' := restrict_algEquiv hL
  let σ' : Gal(L'/K) := e.autCongr σ
  have hσ' : Subgroup.zpowers σ' = ⊤ := by
    change Subgroup.zpowers (e.autCongr.toMonoidHom σ) = ⊤
    rw [← MonoidHom.map_zpowers, hσ,
      Subgroup.map_top_of_surjective _ e.autCongr.surjective]
  have hcard : Nat.card Gal(L'/K) = Nat.card Gal(L/K) :=
    Nat.card_congr e.autCongr.toEquiv.symm
  letI : ∀ i : Fin r, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  letI : ∀ i : Fin r, IsCyclotomicExtension {m i} K (E i) := fun i =>
    CyclotomicBaseChange.rootField_isCyclotomic (m i) (hm i) (ξ i) (hξ i)
  letI : ∀ i : Fin r, IsCyclotomicExtension {m i} K (E' i) := fun i =>
    IsCyclotomicExtension.equiv {m i} K (E i) (restrict_algEquiv (hE i))
  have hirr (i : Fin r) : Irreducible (cyclotomic (m i) K) := by
    apply irreducible_cyclotomic_of_rational_intersection L (m i) (hm i) (ξ i) (hξ i)
    apply le_antisymm _ bot_le
    calc
      L.restrictScalars ℚ ⊓ adjoin ℚ {ξ i} ≤
          (L.restrictScalars ℚ ⊔ ⨆ j : {j : Fin r // j < i}, adjoin ℚ {ξ j.1}) ⊓
            adjoin ℚ {ξ i} := inf_le_inf_right _ le_sup_left
      _ = ⊥ := hInf i
  have hUM (i : Fin r) : UnramifiedIn K M (q i) :=
    unramifiedIn_sup_iSup_rootField L m ξ hm hξ (q i) (hU i) (hcop i)
  have hInf' := restricted_prefix_inf_eq_bot_of_rational M L r m ξ hm hξ hL hE hInf
  obtain ⟨τ, hsplit, hjoin, hinter⟩ := same_auxiliary_family K M r L' E' σ' hσ'
    m hirr q hUM (fun i => hcop i i) u v hu
    (fun i => hcard ▸ hnu i) (fun i => hcard ▸ hnv i) hind hInf'
  let F' (i : Fin r) := auxiliaryFixedField L' (E' i) σ'
    (frobeniusClass K L' (q i)).out (τ i) (frobeniusClass K (E' i) (q i)).out
  refine ⟨fun i => lift (F' i), ?_, ?_, ?_, ?_⟩
  · intro i
    exact lift_le (F' i)
  · intro i
    rw [← splittingIdeals_algEquiv (liftAlgEquiv (F' i))]
    exact hsplit i
  · intro i
    have h := congrArg (fun A : IntermediateField K M => lift A) (hjoin i)
    simpa only [lift_sup, L', E', lift_restrict, F', E] using h
  · have h := congrArg (fun A : IntermediateField K M => lift A) hinter
    change lift ((⨆ i, F' i) ⊓ L.restrict hL) = lift (⊥ : IntermediateField K M) at h
    rw [lift_inf, lift_restrict, lift_bot] at h
    change ((⨆ i, F' i).map M.val) ⊓ L = ⊥ at h
    rw [IntermediateField.map_iSup] at h
    exact h

-- The source's sequential selection avoids every selected prime norm from
-- the outset; diagonal-only coprimality would not unramify the common M.
theorem selected_root_field_family
    (K : Type*) [Field K] [NumberField K]
    (L : IntermediateField K (AlgebraicClosure K)) [NumberField L]
    [IsGalois K L] [IsCyclic Gal(L/K)]
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
  letI : FiniteDimensional ℚ (L.restrictScalars ℚ) := by
    change FiniteDimensional ℚ L
    infer_instance
  have hroots (n : ℕ) (hn : 0 < n) :
      ∃ ξ : AlgebraicClosure K, IsPrimitiveRoot ξ n := by
    letI : NeZero (n : AlgebraicClosure K) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) n
  have hnorm (i : Fin r) : 2 ≤ (q i).absNorm :=
    NumberField.HeightOneSpectrum.one_lt_absNorm ⟨q i, inferInstance, hq0 i⟩
  let s := ∏ i, (q i).absNorm
  have hs : 0 < s := Finset.prod_pos fun i _ => lt_of_lt_of_le (by decide : 0 < 2) (hnorm i)
  obtain ⟨m, ξ, u, v, hdata⟩ := exists_sequential_cyclotomic_residue_family hroots
    (L.restrictScalars ℚ) r (fun i => (q i).absNorm) hnorm
    (Nat.card Gal(L/K)) s Nat.card_pos hs
  have hm (i : Fin r) := (hdata i).1
  have hξ (i : Fin r) := (hdata i).2.2.2.1
  have hcross (i j : Fin r) : (q i).absNorm.Coprime (m j) := by
    have hms : (m j).Coprime s :=
      (hdata j).2.1.of_dvd_right (dvd_mul_right s _)
    exact (hms.of_dvd_right (Finset.dvd_prod_of_mem (fun i : Fin r => (q i).absNorm)
      (Finset.mem_univ i))).symm
  obtain ⟨F, hF, hsplit, hjoin, hinter⟩ := same_root_field_family K L r σ hσ
    m ξ hm hξ q hU hcross u v (fun i => (hdata i).2.2.2.2.2.1)
    (fun i => (hdata i).2.2.2.2.2.2.1) (fun i => (hdata i).2.2.2.2.2.2.2.1)
    (fun i => (hdata i).2.2.2.2.2.2.2.2) (fun i => (hdata i).2.2.2.2.1)
  exact ⟨m, ξ, F, hm, hξ, hcross, hF, hsplit, hjoin, hinter⟩

end Families

section Factors
open NumberField IsDedekindDomain

-- Janusz V.5.6 p162: the actual given fractional ideal, with its finite
-- signed prime-exponent family; no new ideal is chosen in its place.
theorem prime_factor_family
    (K : Type*) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (A : coprimeIdeals K m) :
    ∃ (r : ℕ) (p : Fin r → HeightOneSpectrum (𝓞 K)) (e : Fin r → ℤ),
      (∀ i, (p i).asIdeal ⊔ m = ⊤) ∧
      (A : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ∏ i, primeIdealUnit K (p i) ^ e i := by
  classical
  let a := idealExponentVector K A
  let s := a.support
  let p : Fin s.card → HeightOneSpectrum (𝓞 K) := fun i => (s.equivFin.symm i).val
  let e : Fin s.card → ℤ := fun i => a (p i)
  refine ⟨s.card, p, e, ?_, ?_⟩
  · intro i
    have hne : a (p i) ≠ 0 := Finsupp.mem_support_iff.mp (s.equivFin.symm i).property
    have hnot : ¬ m ≤ (p i).asIdeal := by
      intro hm
      apply hne
      exact (idealExponentVector_apply K A (p i)).trans
        ((mem_coprimeIdeals_iff_count_eq_zero K m A).mp A.property (p i) hm)
    exact codisjoint_iff.mp
      ((Ideal.isMaximal_def.mp (inferInstance : (p i).asIdeal.IsMaximal)).not_le_iff_codisjoint.mp
        hnot)
  · have hprod : (∏ i, primeIdealUnit K (p i) ^ e i) =
        ∏ v : s, primeIdealUnit K v.val ^ a v.val :=
      Fintype.prod_equiv s.equivFin.symm _ _ (fun _ => rfl)
    rw [hprod, Finset.prod_coe_sort s (fun v => primeIdealUnit K v ^ a v)]
    exact (exponentIdealProduct_idealExponentVector K A).symm

-- At any common deeper modulus, the same primes represented by the supplied
-- good ideals reconstruct A through the actual subgroup inclusion.
theorem reconstruct_factor_family (K : Type*) [Field K] [NumberField K]
    (m t : Ideal (𝓞 K)) (htm : t ≤ m) (A : coprimeIdeals K m)
    (r : ℕ) (p : Fin r → HeightOneSpectrum (𝓞 K)) (e : Fin r → ℤ)
    (hA : (A : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ∏ i, primeIdealUnit K (p i) ^ e i)
    (u : Fin r → coprimeIdeals K t)
    (hu : ∀ i, ((u i : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (p i).asIdeal) :
    A = Subgroup.inclusion (coprimeIdeals_mono K htm) (∏ i, u i ^ e i) := by
  have hu' (i : Fin r) : (u i : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = primeIdealUnit K (p i) := by
    apply Units.ext
    exact (hu i).trans (primeIdealUnit_coe K (p i)).symm
  apply Subtype.ext
  change (A : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
    (coprimeIdeals K t).subtype (∏ i, u i ^ e i)
  rw [map_prod]
  simpa only [map_zpow, Subgroup.coe_subtype, hu'] using hA

end Factors

section Restriction
open NumberField IntermediateField Cox.Chebotarev

-- Fix these equivalent presentations before any B or C ideal is selected.
theorem restrict_selected_family
    (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]
    (M L : IntermediateField K Ω) (hL : L ≤ M)
    (r : ℕ) (F : Fin r → IntermediateField K Ω) (hF : ∀ i, F i ≤ M)
    (n : Fin r → ℕ) (ξ : Fin r → Ω) (hξM : ∀ i, ξ i ∈ M)
    (hξ : ∀ i, IsPrimitiveRoot (ξ i) (n i))
    (q : Fin r → Ideal (𝓞 K))
    (hsplit : ∀ i, q i ∈ splittingIdeals K (F i))
    (hjoin : ∀ i, F i ⊔ adjoin K {ξ i} = L ⊔ adjoin K {ξ i})
    (hinter : (⨆ i, F i) ⊓ L = ⊥) :
    let ξ' : Fin r → M := fun i => ⟨ξ i, hξM i⟩
    let F' : Fin r → IntermediateField K M := fun i => (F i).restrict (hF i)
    (∀ i, IsPrimitiveRoot (ξ' i) (n i)) ∧
      (∀ i, q i ∈ splittingIdeals K (F' i)) ∧
      (∀ i, F' i ⊔ adjoin K {ξ' i} = L.restrict hL ⊔ adjoin K {ξ' i}) ∧
      (⨆ i, F' i) ⊓ L.restrict hL = ⊥ := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact (hξ i).of_map_of_injective (f := M.val) M.val.injective
  · intro i
    rw [← ArtinAuxiliary.splittingIdeals_algEquiv (restrict_algEquiv (hF i))]
    exact hsplit i
  · intro i
    apply lift_injective M
    simpa only [lift_sup, lift_restrict, lift_adjoin_simple] using hjoin i
  · apply lift_injective M
    rw [lift_inf, lift_restrict, lift_bot]
    change ((⨆ i, (F i).restrict (hF i)).map M.val) ⊓ L = ⊥
    rw [IntermediateField.map_iSup]
    change (⨆ i, lift ((F i).restrict (hF i))) ⊓ L = ⊥
    simpa only [lift_restrict] using hinter

end Restriction

section Transport

variable (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K))
variable (L M : Type*) [Field L] [NumberField L] [Field M] [NumberField M]
variable [Algebra K L] [Algebra K M]

omit [NumberField K] [NumberField L] [NumberField M] in
theorem unramified_transport (e : L ≃ₐ[K] M)
    (hL : IsUnramifiedAway K m L) : IsUnramifiedAway K m M := by
  intro q hq hq0 hqm P hP
  letI := hq
  letI := hP.1
  letI := hP.2
  let eO := RingOfIntegers.mapAlgEquiv e
  have hP' : P.comap eO ∈ q.primesOver (𝓞 L) := ⟨inferInstance, inferInstance⟩
  exact (Ideal.ramificationIdx_comap_eq q eO P).symm.trans (hL q hq hq0 hqm _ hP')

omit [NumberField L] [NumberField M] in
theorem artin_transport (e : L ≃ₐ[K] M)
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K m L φ) :
    IsArtinMap K m M ((e.autCongr.toMonoidHom).comp φ) := by
  intro q hq hq0 hqm u hu P hP x
  letI := hq
  letI := hP.1
  letI := hP.2
  let eO := RingOfIntegers.mapAlgEquiv e
  have hP' : P.comap eO ∈ q.primesOver (𝓞 L) := ⟨inferInstance, inferInstance⟩
  have h := hφ q hq hq0 hqm u hu _ hP' (eO.symm x)
  change eO (RingOfIntegers.mapRingHom (φ u).toRingHom (eO.symm x) -
    eO.symm x ^ q.absNorm) ∈ P at h
  simpa only [map_sub, map_pow, AlgEquiv.apply_symm_apply] using h

theorem normImage_transport (e : L ≃ₐ[K] M) :
    normImage K m L = normImage K m M := by
  let eO : (𝓞 L) ≃ₐ[𝓞 K] (𝓞 M) := RingOfIntegers.mapAlgEquiv e
  unfold normImage
  apply congrArg Subgroup.closure
  ext u
  constructor
  · rintro ⟨A, hA, hAm, hu⟩
    refine ⟨A.map eO, (Ideal.map_eq_bot_iff_of_injective eO.injective).not.mpr hA,
      ?_, ?_⟩
    · have hmmap : (m.map (algebraMap (𝓞 K) (𝓞 L))).map eO =
          m.map (algebraMap (𝓞 K) (𝓞 M)) := by
        change (m.map (algebraMap (𝓞 K) (𝓞 L))).map eO.toRingHom =
          m.map (algebraMap (𝓞 K) (𝓞 M))
        rw [Ideal.map_map]
        exact congrArg (fun f : (𝓞 K) →+* (𝓞 M) => m.map f)
          eO.toAlgHom.comp_algebraMap
      rw [← hmmap, ← Ideal.map_sup, hAm, Ideal.map_top]
    · simpa only [Ideal.relNorm_map_algEquiv] using hu
  · rintro ⟨A, hA, hAm, hu⟩
    refine ⟨A.map eO.symm,
      (Ideal.map_eq_bot_iff_of_injective eO.symm.injective).not.mpr hA, ?_, ?_⟩
    · have hmmap : (m.map (algebraMap (𝓞 K) (𝓞 M))).map eO.symm =
          m.map (algebraMap (𝓞 K) (𝓞 L)) := by
        change (m.map (algebraMap (𝓞 K) (𝓞 M))).map eO.symm.toRingHom =
          m.map (algebraMap (𝓞 K) (𝓞 L))
        rw [Ideal.map_map]
        exact congrArg (fun f : (𝓞 K) →+* (𝓞 L) => m.map f)
          eO.symm.toAlgHom.comp_algebraMap
      rw [← hmmap, ← Ideal.map_sup, hAm, Ideal.map_top]
    · simpa only [Ideal.relNorm_map_algEquiv] using hu

end Transport

-- The absolute norm supplies an actual element of the ideal, so Bezout lifts coprimality.
theorem sup_span_natCast_eq_top
    {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R]
    (q : Ideal R) (n : ℕ) (hcop : q.absNorm.Coprime n) :
    q ⊔ Ideal.span ({(n : R)} : Set R) = ⊤ := by
  obtain ⟨a, b, hab⟩ := hcop.cast (R := R)
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← hab]
  apply Ideal.add_mem
  · exact Ideal.mul_mem_left _ _ ((show q ≤ q ⊔ Ideal.span ({(n : R)} : Set R) from le_sup_left)
        (Ideal.absNorm_mem q))
  · exact Ideal.mul_mem_left _ _
      ((show Ideal.span ({(n : R)} : Set R) ≤ q ⊔ Ideal.span ({(n : R)} : Set R) from
        le_sup_right) (Ideal.subset_span (Set.mem_singleton (n : R))))

-- Janusz V.5.6 pp163–164: fix a common modulus before choosing B_F and C_i.
-- One explicit witness handles all avoidance and later local product-modulus inclusions.
theorem exists_common_modulus
    {R ι : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R]
    [Finite ι]
    (m : Ideal R) (hm : m ≠ ⊥) (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (q : ι → Ideal R) (hqm : ∀ i, q i ⊔ m = ⊤)
    (hcop : ∀ i j, (q i).absNorm.Coprime (n j)) :
    ∃ t : Ideal R, t ≠ ⊥ ∧ t ≤ m ∧
      (∀ i, t ≤ m * Ideal.span ({(n i : R)} : Set R)) ∧
      ∀ i, q i ⊔ t = ⊤ := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : CharZero R := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective ℤ R)
  let J : ι → Ideal R := fun i => Ideal.span ({(n i : R)} : Set R)
  let t := m * ∏ i, J i
  have hJ (i : ι) : J i ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr (hn i).ne')
  have ht : t ≠ ⊥ := mul_ne_zero hm (Finset.prod_ne_zero_iff.mpr (fun i _ => hJ i))
  refine ⟨t, ht, Ideal.mul_le_right, ?_, ?_⟩
  · intro i
    exact Ideal.mul_mono_right
      (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i)))
  · intro i
    change q i ⊔ m * ∏ j, J j = ⊤
    rw [Ideal.sup_mul_eq_of_coprime_left (hqm i)]
    exact Ideal.sup_prod_eq_top (fun j _ => sup_span_natCast_eq_top (q i) (n j) (hcop i j))

end CyclicReciprocity

open IntermediateField Cox.Chebotarev in
/-- Source: Janusz, Algebraic Number Fields (1973), V.5.6, printed162–164/PDF173–175. -/
theorem cyclic_artin_ker_le_normRay
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (L : IntermediateField K (AlgebraicClosure K)) [NumberField L]
    [IsGalois K L] [IsCyclic Gal(L/K)]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hU : IsUnramifiedAway K m L)
    (φ : coprimeIdeals K m →* Gal(L/K)) (hφ : IsArtinMap K m L φ) :
    φ.ker ≤ normRaySubgroup K m L := by
  classical
  intro A hA
  obtain ⟨r, p, e, hpm, hfactor⟩ := CyclicReciprocity.prime_factor_family K m A
  let q : Fin r → Ideal (𝓞 K) := fun i => (p i).asIdeal
  have hq0 : ∀ i, q i ≠ ⊥ := fun i => (p i).ne_bot
  letI : ∀ i, (q i).IsPrime := fun i => (p i).isPrime
  have hqU (i : Fin r) : UnramifiedIn K L (q i) :=
    ArtinAuxiliary.unramifiedIn_of_ramificationIdx_eq_one K L (q i) (hq0 i)
      (hU (q i) inferInstance (hq0 i) (hpm i))
  obtain ⟨σ, hσ⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic Gal(L/K))
  obtain ⟨n, ξ, Fi, hn, hξ, hcross, hFi, hsplit, hjoin, hinter⟩ :=
    CyclicReciprocity.selected_root_field_family K L r σ hσ q hq0 hqU
  let M := L ⊔ ⨆ i, adjoin K {ξ i}
  have hM := CyclicReciprocity.common_ambient K L r n ξ hn hξ
  letI : NumberField M := hM.1
  letI : IsAbelianGalois K M := hM.2
  have hL : L ≤ M := le_sup_left
  have hξM (i : Fin r) : ξ i ∈ M :=
    (le_sup_of_le_right (le_iSup (fun j => adjoin K {ξ j}) i))
      (subset_adjoin K {ξ i} (Set.mem_singleton _))
  let ξ' : Fin r → M := fun i => ⟨ξ i, hξM i⟩
  let Fi' : Fin r → IntermediateField K M := fun i => (Fi i).restrict (hFi i)
  let L' : IntermediateField K M := L.restrict hL
  let F' : IntermediateField K M := ⨆ i, Fi' i
  obtain ⟨hξ', hsplit', hjoin', hinter'⟩ := CyclicReciprocity.restrict_selected_family
    K (AlgebraicClosure K) M L hL r Fi hFi n ξ hξM hξ q hsplit hjoin hinter
  let eqL : L ≃ₐ[K] L' := restrict_algEquiv hL
  let φ' : coprimeIdeals K m →* Gal(L'/K) := eqL.autCongr.toMonoidHom.comp φ
  have hφ' : IsArtinMap K m L' φ' := CyclicReciprocity.artin_transport K m L L' eqL φ hφ
  have hU' : IsUnramifiedAway K m L' := CyclicReciprocity.unramified_transport K m L L' eqL hU
  have hA' : A ∈ φ'.ker := by
    change eqL.autCongr (φ A) = 1
    change φ A = 1 at hA
    rw [hA, map_one]
  let σ' : Gal(L'/K) := eqL.autCongr σ
  have hσ' : Subgroup.zpowers σ' = ⊤ := by
    change Subgroup.zpowers (eqL.autCongr.toMonoidHom σ) = ⊤
    rw [← MonoidHom.map_zpowers, hσ,
      Subgroup.map_top_of_surjective _ eqL.autCongr.surjective]
  obtain ⟨t, ht0, htm, htn, hqt⟩ :=
    CyclicReciprocity.exists_common_modulus m hm n hn q hpm hcross
  have htn' (i : Fin r) : t ≤ Ideal.span ({(n i : 𝓞 K)} : Set (𝓞 K)) :=
    (htn i).trans Ideal.mul_le_left
  choose u hu using fun i => exists_coprimeIdealUnit K t (q i) (hq0 i) (hqt i)
  have hAt : A = Subgroup.inclusion (coprimeIdeals_mono K htm) (∏ i, u i ^ e i) :=
    CyclicReciprocity.reconstruct_factor_family K m t htm A r p e hfactor u hu
  have hmem : A ∈ normRaySubgroup K m L' :=
    cyclic_kernel_element_mem_normRay K M L' F' Fi' rfl hinter' n hn ξ' hξ' hjoin' q hsplit'
      m t ht0 htm htn' hqt u hu e A hAt φ' hφ' hU' hA' σ' hσ'
  have hnorm : normImage K m L = normImage K m L' :=
    CyclicReciprocity.normImage_transport K m L L' eqL
  have hnormRay : normRaySubgroup K m L = normRaySubgroup K m L' :=
    congrArg (fun N : Subgroup (coprimeIdeals K m) => N ⊔ raySubgroup K m) hnorm
  rw [hnormRay]
  exact hmem

namespace CyclicReciprocity

theorem reciprocity_of_embedded
    (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hU : IsUnramifiedAway K m L)
    (hindex : (normRaySubgroup K m L).index = Module.finrank K L)
    (embedded : ∀ (L0 : IntermediateField K (AlgebraicClosure K))
      [NumberField L0] [IsGalois K L0] [IsCyclic (L0 ≃ₐ[K] L0)],
      m ≠ ⊥ → IsUnramifiedAway K m L0 →
      (normRaySubgroup K m L0).index = Module.finrank K L0 →
      IsReciprocityLaw K m L0) :
    IsReciprocityLaw K m L := by
  let ι : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let L0 : IntermediateField K (AlgebraicClosure K) := ι.fieldRange
  let e : L ≃ₐ[K] L0 := AlgEquiv.ofInjectiveField ι
  letI : NumberField L0 := NumberField.of_ringEquiv L L0 e.toRingEquiv
  letI : IsGalois K L0 := IsGalois.of_algEquiv e
  letI : IsCyclic (L0 ≃ₐ[K] L0) :=
    isCyclic_of_surjective e.autCongr e.autCongr.surjective
  have hU0 : IsUnramifiedAway K m L0 := unramified_transport K m L L0 e hU
  have hnorm : normImage K m L = normImage K m L0 :=
    normImage_transport K m L L0 e
  have hnormRay : normRaySubgroup K m L = normRaySubgroup K m L0 :=
    congrArg (fun N : Subgroup (coprimeIdeals K m) => N ⊔ raySubgroup K m) hnorm
  have hindex0 : (normRaySubgroup K m L0).index = Module.finrank K L0 := by
    rw [← hnormRay, hindex]
    exact e.toLinearEquiv.finrank_eq
  obtain ⟨φ0, hφ0, hs0, hray0⟩ := embedded L0 hm hU0 hindex0
  refine ⟨e.symm.autCongr.toMonoidHom.comp φ0,
    artin_transport K m L0 L e.symm φ0 hφ0,
    e.symm.autCongr.surjective.comp hs0, ?_⟩
  intro u hu
  have h0 : φ0 u = 1 := hray0 hu
  change e.symm.autCongr (φ0 u) = 1
  rw [h0, map_one]

theorem reciprocity_of_kernel_le (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Module.Finite (𝓞 K) (𝓞 L)] [IsGalois K L]
    (m : Ideal (𝓞 K))
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K m L φ) (hsurj : Function.Surjective φ)
    (hker : φ.ker ≤ normRaySubgroup K m L)
    (hindex : (normRaySubgroup K m L).index = Module.finrank K L) :
    IsReciprocityLaw K m L := by
  have hkerIndex : φ.ker.index = Module.finrank K L := by
    rw [Subgroup.index_ker, φ.range_eq_top_of_surjective hsurj,
      Subgroup.card_top, IsGalois.card_aut_eq_finrank K L]
  have hreverse : normRaySubgroup K m L ≤ φ.ker := by
    by_contra hn
    have hlt : φ.ker < normRaySubgroup K m L := lt_of_le_not_ge hker hn
    have hltIndex := Subgroup.index_strictAnti hlt
    rw [hindex, hkerIndex] at hltIndex
    exact (Nat.lt_irrefl _) hltIndex
  exact ⟨φ, hφ, hsurj,
    (show raySubgroup K m ≤ normRaySubgroup K m L from le_sup_right).trans hreverse⟩

end CyclicReciprocity

section Reciprocity

variable (m : Ideal (𝓞 K)) (L : Type*) [Field L] [NumberField L] [Algebra K L]
variable [Module.Finite (𝓞 K) (𝓞 L)]

/-- Janusz V.5.6: the cyclic reciprocity argument under the fundamental equality. -/
theorem cyclic_reciprocity_of_index_eq [IsTotallyComplex K] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] (hm : m ≠ ⊥) (hU : IsUnramifiedAway K m L)
    (hindex : (normRaySubgroup K m L).index = Module.finrank K L) :
    IsReciprocityLaw K m L := by
  apply CyclicReciprocity.reciprocity_of_embedded K L m hm hU hindex
  intro L0 hNF0 hGal0 hCyc0 hm0 hU0 hindex0
  letI : IsAbelianGalois K L0 := IsAbelianGalois.of_isCyclic K L0
  obtain ⟨φ, hφ, hsurj⟩ := exists_artinMap K m L0 hm0 hU0
  have hker : φ.ker ≤ normRaySubgroup K m L0 :=
    cyclic_artin_ker_le_normRay K L0 m hm0 hU0 φ hφ
  exact CyclicReciprocity.reciprocity_of_kernel_le K L0 m φ hφ hsurj hker hindex0

/-- Janusz V.4.3: the cyclic norm index reaches the field degree for sufficiently
divisible finite moduli over a totally complex field. -/
theorem cyclic_norm_index_eventually_eq [IsTotallyComplex K] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    ∃ m₀ : Ideal (𝓞 K), m₀ ≠ ⊥ ∧ IsUnramifiedAway K m₀ L ∧
      ∀ m : Ideal (𝓞 K), m ≠ ⊥ → m ≤ m₀ →
        (normRaySubgroup K m L).index = Module.finrank K L := by
  classical
  obtain ⟨r, hr0, hrU⟩ := exists_unramifiedAway_modulus K L
  have hrfin := Ideal.finite_factors (show r ≠ 0 by rwa [Ideal.zero_eq_bot])
  set S := hrfin.toFinset with hS
  have hU1 : IsUnramifiedAway K (supportModulus K S 1) L := by
    intro q hq hq0 hqm P hP
    refine hrU q hq hq0 ?_ P hP
    by_contra hqr
    have hmax : q.IsMaximal := hq.isMaximal hq0
    have hrq : r ≤ q := le_sup_right.trans (hmax.eq_of_le hqr le_sup_left).symm.le
    let qv : HeightOneSpectrum (𝓞 K) := ⟨q, hq, hq0⟩
    have hqS : qv ∈ S := hrfin.mem_toFinset.mpr (Ideal.dvd_iff_le.mpr hrq)
    have hle : supportModulus K S 1 ≤ q := (supportModulus_le_prime_iff K S 1 one_pos qv).mpr hqS
    rw [sup_eq_left.mpr hle] at hqm
    exact hq.ne_top hqm
  obtain ⟨c, hc⟩ := cyclic_norm_index_supported K L S hU1
  refine ⟨supportModulus K S (max 1 c), supportModulus_ne_bot K S _, ?_, fun m hm hmm₀ => ?_⟩
  · intro q hq hq0 hqm P hP
    exact hU1 q hq hq0
      (eq_top_mono (sup_le_sup_left (supportModulus_antitone K S (le_max_left _ _)) q) hqm) P hP
  · apply le_antisymm (normRaySubgroup_index_le K m L hm)
    rw [← hc (max 1 c) (le_max_right _ _)]
    exact normRaySubgroup_index_mono K L m _ hm (supportModulus_ne_bot K S _) hmm₀

/-- Janusz V.5.7: combine cyclic reciprocal subextensions using finite abelian decomposition. -/
theorem artin_reciprocity [IsTotallyComplex K] [IsAbelianGalois K L] :
    ∃ m₀ : Ideal (𝓞 K), m₀ ≠ ⊥ ∧ IsUnramifiedAway K m₀ L ∧
      ∀ m : Ideal (𝓞 K), m ≠ ⊥ → m ≤ m₀ →
        HasArtinKernel K m L (normRaySubgroup K m L) := by
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  obtain ⟨ι, hι, E, hcyc, hbot⟩ := exists_cyclic_subfields_iInf_fixing_eq_bot K L
  haveI : ∀ i, IsAbelianGalois K (E i) := fun i => IsAbelianGalois.tower_bot K (E i) L
  have hthr : ∀ i, ∃ d : Ideal (𝓞 K), d ≠ ⊥ ∧ IsUnramifiedAway K d (E i) ∧
      ∀ m : Ideal (𝓞 K), m ≠ ⊥ → m ≤ d →
        (normRaySubgroup K m (E i)).index = Module.finrank K (E i) := by
    intro i
    haveI := hcyc i
    exact cyclic_norm_index_eventually_eq K (E i)
  choose d hd0 hdU hdidx using hthr
  obtain ⟨r, hr0, hrU⟩ := exists_unramifiedAway_modulus K L
  refine ⟨r * ∏ i, d i, ?_, ?_, fun m hm hmm₀ => ?_⟩
  · rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or, Finset.prod_eq_zero_iff, not_exists]
    refine ⟨by rwa [Ideal.zero_eq_bot], fun i ⟨_, h⟩ => hd0 i ?_⟩
    rwa [Ideal.zero_eq_bot] at h
  · intro q hq hq0 hqm
    exact hrU q hq hq0 (eq_top_mono (sup_le_sup_left Ideal.mul_le_right q) hqm)
  · have hmr : m ≤ r := hmm₀.trans Ideal.mul_le_right
    have hUm : IsUnramifiedAway K m L := fun q hq hq0 hqm =>
      hrU q hq hq0 (eq_top_mono (sup_le_sup_left hmr q) hqm)
    obtain ⟨φ, hφ, hsurj⟩ := exists_artinMap K m L hm hUm
    have hmd : ∀ i, m ≤ d i := fun i => hmm₀.trans
      (Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))))
    have hray : raySubgroup K m ≤ φ.ker := by
      intro u hu
      rw [MonoidHom.mem_ker]
      have hall : φ u ∈ ⨅ i, (E i).fixingSubgroup := by
        rw [Subgroup.mem_iInf]
        intro i
        haveI := hcyc i
        have hUEi := isUnramifiedAway_subfield K m L (E i) hUm
        obtain ⟨ψ, hψ, -, hψray⟩ :=
          cyclic_reciprocity_of_index_eq K m (E i) hm hUEi (hdidx i m hm (hmd i))
        have hres := isArtinMap_restrict K m L (E i) φ hφ
        have heq := isArtinMap_unique K m (E i) hUEi hψ hres
        have h1 : ψ u = 1 := hψray hu
        rw [heq, MonoidHom.comp_apply] at h1
        rw [← IntermediateField.restrictNormalHom_ker]
        exact h1
      rw [hbot] at hall
      exact Subgroup.mem_bot.mp hall
    exact ⟨inferInstance, inferInstance, inferInstance, hUm,
      ⟨φ, hφ, hsurj, artin_ker_eq_normRaySubgroup K m L hm hUm φ hφ hsurj hray⟩⟩

end Reciprocity



end Cox.ClassFieldTheory
