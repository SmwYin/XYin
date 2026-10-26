/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldAuxiliaryFields
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicUnramified
import XYin.PhD.Cox.Theorem11_1.ClassFieldSplittingDensity
import XYin.PhD.Cox.Theorem11_1.ChebotarevCrossing

/-!
# Unramification and fixed-field adapters for Artin's lemma

Janusz V.5.4–5.5 uses the actual cyclotomic compositum, its Frobenius element, and the fixed field
of a two-generator subgroup. These seven contracts cover only the common core.
-/

open NumberField IntermediateField
noncomputable section
namespace Cox.ClassFieldTheory.ArtinAuxiliary
open Cox.Chebotarev AuxiliaryFields CyclotomicUnramified

/-- Janusz V.5.4: a finite bound on prime divisors enforces the required coprimality. -/
theorem coprime_of_prime_divisors_gt (m N B : ℕ) (hN : 0 < N) (hNB : N ≤ B)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ m → B < p) : m.Coprime N := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpN
  have h1 := Nat.le_of_dvd hN hpN
  have h2 := hlarge p hp hpm
  omega

/-- Convert ramification index one into the project unramification predicate. -/
theorem unramifiedIn_of_ramificationIdx_eq_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (q : Ideal (𝓞 K)) (hq0 : q ≠ ⊥)
    (hU : ∀ P ∈ q.primesOver (𝓞 L), Ideal.ramificationIdx q P = 1) :
    UnramifiedIn K L q := by
  refine ⟨hq0, fun P hPmax hPlo => ?_⟩
  haveI := hPlo
  haveI : P.IsPrime := hPmax.isPrime
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hq0 P
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP0, ← Ideal.over_def P q]
  exact hU P ⟨inferInstance, hPlo⟩

/-- Janusz I.6 Exercise1: a coprime cyclotomic tower preserves unramification. -/
theorem unramifiedIn_cyclotomic_tower
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (q : Ideal (𝓞 K)) [q.IsPrime] (hU : UnramifiedIn K L q)
    (hcop : q.absNorm.Coprime m) : UnramifiedIn K M q := by
  haveI : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) := inferInstance
  refine ⟨hU.1, fun P hPmax hPlo => ?_⟩
  haveI := hPlo
  haveI : P.IsPrime := hPmax.isPrime
  haveI : (P.under (𝓞 L)).IsPrime := Ideal.IsPrime.under (𝓞 L) P
  haveI : P.LiesOver (P.under (𝓞 L)) := ⟨rfl⟩
  haveI : (P.under (𝓞 L)).LiesOver q := ⟨by rw [Ideal.under_under]; exact hPlo.over⟩
  have hp0 : P.under (𝓞 L) ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hU.1 _
  have hpmax : (P.under (𝓞 L)).IsMaximal := ‹(P.under (𝓞 L)).IsPrime›.isMaximal hp0
  have hcopp : (P.under (𝓞 L)).absNorm.Coprime m :=
    absNorm_coprime_of_liesOver q (P.under (𝓞 L)) ‹_› hU.1 m hcop
  have hUp : UnramifiedIn L M (P.under (𝓞 L)) :=
    unramifiedIn_cyclotomic_of_coprime L M m (P.under (𝓞 L)) hp0 hcopp
  haveI : Algebra.IsUnramifiedAt (𝓞 K) (P.under (𝓞 L)) := hU.2 _ hpmax inferInstance
  haveI : Algebra.IsUnramifiedAt (𝓞 L) P := hUp.2 P hPmax inferInstance
  exact Algebra.IsUnramifiedAt.comp (R := 𝓞 K) (P.under (𝓞 L)) P

/-- One inclusion of `splittingIdeals_algEquiv`: pull primes back along the restricted
equivalence of rings of integers, which preserves e and f. -/
theorem splittingIdeals_subset_of_algEquiv
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] (e : L ≃ₐ[K] M) :
    splittingIdeals K L ⊆ splittingIdeals K M := by
  rintro q ⟨hqp, hq0, hsplit⟩
  refine ⟨hqp, hq0, fun P hP => ?_⟩
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver q := hP.2
  let eO : 𝓞 L ≃ₐ[𝓞 K] 𝓞 M := RingOfIntegers.mapAlgEquiv e
  have hP' : P.comap eO ∈ q.primesOver (𝓞 L) := ⟨Ideal.IsPrime.comap _, inferInstance⟩
  obtain ⟨h1, h2⟩ := hsplit _ hP'
  rw [Ideal.ramificationIdx_comap_eq] at h1
  rw [Ideal.inertiaDeg_comap_eq] at h2
  exact ⟨h1, h2⟩

/-- Preserve the source condition e=f=1 under an actual algebra equivalence. -/
theorem splittingIdeals_algEquiv
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] (e : L ≃ₐ[K] M) :
    splittingIdeals K L = splittingIdeals K M := by
  exact Set.Subset.antisymm (splittingIdeals_subset_of_algEquiv e)
    (splittingIdeals_subset_of_algEquiv e.symm)

/-- Janusz III.2.4: actual Frobenius representatives restrict in an abelian lower field. -/
theorem frobeniusClass_out_restrict
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [IsGalois K L] [IsGalois K M]
    [IsMulCommutative Gal(L/K)]
    (q : Ideal (𝓞 K)) (hM : UnramifiedIn K M q) (hL : UnramifiedIn K L q) :
    (frobeniusClass K M q).out.restrictNormal L = (frobeniusClass K L q).out := by
  have h := Chebotarev.frobeniusClass_proj K L M
    ((frobeniusClass K M q).out.restrictNormal L) (frobeniusClass K M q).out rfl q hM hL
    (Quotient.out_eq' (frobeniusClass K M q)).symm
  open scoped IsMulCommutative in
  apply ConjClasses.mk_injective
  rw [← h]
  exact (Quotient.out_eq' _).symm

/-- Janusz V.5.5: Frobenius membership makes its actual fixed field split. -/
theorem splits_fixedField_of_frobenius_mem
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [IsAbelianGalois K M] (H : Subgroup Gal(M/K))
    (q : Ideal (𝓞 K)) [q.IsPrime] (hU : UnramifiedIn K M q)
    (hmem : (frobeniusClass K M q).out ∈ H) :
    q ∈ splittingIdeals K (fixedField H) := by
  haveI : IsGalois K (fixedField H) := IsGalois.of_fixedField_normal_subgroup H
  rw [splittingIdeals_eq_frobeniusClass_one K (fixedField H)]
  exact ⟨‹_›, Chebotarev.unramifiedIn_intermediateField K M (fixedField H) q hU,
    Chebotarev.frobeniusClass_fixedField_eq_one K M H q hU hmem⟩

/-- Janusz III.2.5: restriction to generating abelian subfields detects commutation. -/
theorem isAbelianGalois_of_generating_fields
    {K M : Type*} [Field K] [Field M] [Algebra K M] [IsGalois K M]
    (L E : IntermediateField K M) [IsAbelianGalois K L] [IsAbelianGalois K E]
    (hSup : L ⊔ E = ⊤) : IsAbelianGalois K M := by
  exact { is_comm.comm x y := restrictionProd_injective L E hSup (by
      rw [map_mul, map_mul]
      open scoped IsMulCommutative in
      exact Prod.ext (mul_comm _ _) (mul_comm _ _)) }

end Cox.ClassFieldTheory.ArtinAuxiliary
