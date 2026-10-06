/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Frobenius
import XYin.PhD.Cox.Theorem11_1.Chebotarev
import XYin.PhD.Cox.Theorem11_1.Residue

/-!
# Splitting-prime comparison in Cox Proposition 8.20

The definitions distinguish complete splitting from existence of one degree-one prime. The
comparison theorems use the Chebotarev density theorem and its local bridges. Fields are embedded
in `ℂ` so the conclusions express literal inclusion.
-/

open NumberField

namespace Cox

/-- Inclusion of sets outside finitely many exceptions, as in Cox, p. 171. -/
def AlmostSubset {α : Type*} (s t : Set α) : Prop :=
  (s \ t).Finite

/-- Finite-exception inclusion is reflexive. -/
theorem AlmostSubset.refl {α : Type*} (s : Set α) : AlmostSubset s s := by
  simp [AlmostSubset]

/-- Finite-exception inclusion is transitive. -/
theorem AlmostSubset.trans {α : Type*} {s t u : Set α}
    (hst : AlmostSubset s t) (htu : AlmostSubset t u) : AlmostSubset s u :=
  (hst.union htu).subset fun x ⟨hxs, hxu⟩ => by
    by_cases hxt : x ∈ t
    · exact Or.inr ⟨hxt, hxu⟩
    · exact Or.inl ⟨hxs, hxt⟩

/-- A finite exceptional set witnesses finite-exception inclusion. -/
theorem almostSubset_iff_exists_finite {α : Type*} (s t : Set α) :
    AlmostSubset s t ↔ ∃ e : Set α, e.Finite ∧ s ⊆ t ∪ e :=
  ⟨fun h => ⟨s \ t, h, fun x hx => by
    by_cases hxt : x ∈ t
    · exact Or.inl hxt
    · exact Or.inr ⟨hx, hxt⟩⟩,
   fun ⟨_, he, hse⟩ => he.subset fun _ ⟨hxs, hxt⟩ => (hse hxs).resolve_left hxt⟩

/-- Rational primes unramified in the embedded field, expressed by ramification indices. -/
def unramifiedPrimes (L : IntermediateField ℚ ℂ) : Set ℕ :=
  {p | p.Prime ∧ ∀ P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L),
    Ideal.ramificationIdx (Ideal.span {(p : ℤ)} : Ideal ℤ) P = 1}

/-- Rational primes splitting completely: unramified, with every residue degree equal to one. -/
def splittingPrimes (L : IntermediateField ℚ ℂ) : Set ℕ :=
  {p | p ∈ unramifiedPrimes L ∧
    ∀ P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L),
      Ideal.inertiaDeg (Ideal.span {(p : ℤ)} : Ideal ℤ) P = 1}

/-- Cox's `S̃`: unramified rational primes having at least one degree-one prime above them. -/
def degreeOnePrimes (L : IntermediateField ℚ ℂ) : Set ℕ :=
  {p | p ∈ unramifiedPrimes L ∧
    ∃ P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L),
      Ideal.inertiaDeg (Ideal.span {(p : ℤ)} : Ideal ℤ) P = 1}

/-- Every member of the unramified-prime set is a rational prime. -/
theorem prime_of_mem_unramifiedPrimes {L : IntermediateField ℚ ℂ} {p : ℕ}
    (hp : p ∈ unramifiedPrimes L) : p.Prime :=
  hp.1

/-- Splitting completely implies unramifiedness. -/
theorem splittingPrimes_subset_unramifiedPrimes (L : IntermediateField ℚ ℂ) :
    splittingPrimes L ⊆ unramifiedPrimes L :=
  fun _ hp => hp.1

/-- The degree-one-prime set also excludes every ramified rational prime. -/
theorem degreeOnePrimes_subset_unramifiedPrimes (L : IntermediateField ℚ ℂ) :
    degreeOnePrimes L ⊆ unramifiedPrimes L :=
  fun _ hp => hp.1

/-- Complete splitting supplies a degree-one prime, using lying-over. -/
theorem splittingPrimes_subset_degreeOnePrimes (L : IntermediateField ℚ ℂ) [NumberField L] :
    splittingPrimes L ⊆ degreeOnePrimes L := by
  rintro p ⟨hpu, hsplit⟩
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hpu.1.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hpu.1)
  obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) (Ideal.span {(p : ℤ)})
  exact ⟨hpu, P, hP, hsplit P hP⟩

/-- Cox Exercise 8.12: in a Galois extension one degree-one prime suffices. -/
theorem degreeOnePrimes_eq_splittingPrimes (L : IntermediateField ℚ ℂ)
    [NumberField L] [IsGalois ℚ L] : degreeOnePrimes L = splittingPrimes L := by
  ext p
  refine ⟨fun ⟨hpu, P, hP, hf⟩ => ⟨hpu, fun Q hQ => ?_⟩,
    fun h => splittingPrimes_subset_degreeOnePrimes L h⟩
  haveI := hP.1
  haveI := hP.2
  haveI := hQ.1
  haveI := hQ.2
  exact (Ideal.inertiaDeg_eq_of_isGaloisGroup _ P Q Gal(L/ℚ)).symm.trans hf

/-- Only finitely many rational primes ramify in a number field. -/
theorem finite_ramifiedPrimes (L : IntermediateField ℚ ℂ) [NumberField L] :
    {p : ℕ | p.Prime ∧ p ∉ unramifiedPrimes L}.Finite := by
  refine (Nat.primeFactors (NumberField.discr L).natAbs).finite_toSet.subset ?_
  rintro p ⟨hp, hpu⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd : (p : ℤ) ∣ NumberField.discr L := by
    by_contra hnd
    apply hpu
    refine ⟨hp, fun P hP => ?_⟩
    haveI := hP.1
    haveI := hP.2
    have hspan : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspan P
    have hunr := (NumberField.not_dvd_discr_iff_forall_liesOver L (𝓞 L) hpZ).mp hnd P
      (hP.1.isMaximal hP0) hP.2
    have h1 := (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP0).mp hunr
    rwa [← hP.2.over] at h1
  rw [Finset.mem_coe, Nat.mem_primeFactors]
  exact ⟨hp, Int.natCast_dvd.mp hdvd, Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero L)⟩

/-- Unramifiedness descends along an inclusion of number fields. -/
theorem unramifiedPrimes_mono {L M : IntermediateField ℚ ℂ}
    [NumberField L] [NumberField M] (hLM : L ≤ M) :
    unramifiedPrimes M ⊆ unramifiedPrimes L := by
  rintro p ⟨hp, hM⟩
  refine ⟨hp, fun P hP => ?_⟩
  letI : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  haveI := hP.1
  haveI := hP.2
  obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 M) P
  haveI := hQ.1
  haveI := hQ.2
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  have htower := Ideal.ramificationIdx_algebra_tower' (Ideal.span {(p : ℤ)}) P Q
  rw [hM Q ⟨hQ.1, inferInstance⟩] at htower
  exact Nat.eq_one_of_mul_eq_one_right htower.symm

/-- Complete splitting descends along an inclusion of number fields. -/
theorem splittingPrimes_mono {L M : IntermediateField ℚ ℂ}
    [NumberField L] [NumberField M] (hLM : L ≤ M) :
    splittingPrimes M ⊆ splittingPrimes L := by
  rintro p ⟨hpu, hsplit⟩
  refine ⟨unramifiedPrimes_mono hLM hpu, fun P hP => ?_⟩
  letI : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  haveI := hP.1
  haveI := hP.2
  have hspan : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hpu.1.ne_zero
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hpu.1.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hpu.1)
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hspan
  haveI : P.IsMaximal := hP.1.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hspan P)
  obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 M) P
  haveI := hQ.1
  haveI := hQ.2
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  have htower := Ideal.inertiaDeg_algebra_tower (Ideal.span {(p : ℤ)}) P Q
  rw [hsplit Q ⟨hQ.1, inferInstance⟩] at htower
  exact Nat.eq_one_of_mul_eq_one_right htower.symm

/-- Existence of a degree-one prime descends along an inclusion of number fields. -/
theorem degreeOnePrimes_mono {L M : IntermediateField ℚ ℂ}
    [NumberField L] [NumberField M] (hLM : L ≤ M) :
    degreeOnePrimes M ⊆ degreeOnePrimes L := by
  rintro p ⟨hpu, Q, hQ, hf⟩
  refine ⟨unramifiedPrimes_mono hLM hpu, ?_⟩
  letI : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  haveI := hQ.1
  haveI := hQ.2
  have hspan : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hpu.1.ne_zero
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hpu.1.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hpu.1)
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hspan
  set P : Ideal (𝓞 L) := Q.under (𝓞 L) with hPdef
  haveI hQP : Q.LiesOver P := Ideal.over_under (A := 𝓞 L) (P := Q)
  haveI hPp : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨by rw [hPdef, Ideal.under_under]; exact hQ.2.over⟩
  haveI : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal
    (Ideal.ne_bot_of_liesOver_of_ne_bot hspan P)
  have htower := Ideal.inertiaDeg_algebra_tower (Ideal.span {(p : ℤ)}) P Q
  rw [hf] at htower
  exact ⟨P, ⟨inferInstance, hPp⟩, Nat.eq_one_of_mul_eq_one_right htower.symm⟩

/-- A prime over the rational prime `p` has residue characteristic `p`. -/
theorem residue_charP {L : IntermediateField ℚ ℂ} {p : ℕ} (_hp : p.Prime)
    (P : Ideal (𝓞 L))
    (hP : P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L)) :
    CharP ((𝓞 L) ⧸ P) p := by
  haveI := hP.2
  refine ⟨fun n => ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem,
    show (n : 𝓞 L) = algebraMap ℤ (𝓞 L) (n : ℤ) by simp, ← Ideal.mem_comap, ← Ideal.under_def,
    ← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}), Ideal.mem_span_singleton]
  exact Int.natCast_dvd_natCast

/-- Cox, p. 238: residue degree one is equivalent to a residue field of cardinality `p`. -/
theorem inertiaDeg_eq_one_iff_card {L : IntermediateField ℚ ℂ} [NumberField L]
    {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 L))
    (hP : P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L)) :
    Ideal.inertiaDeg (Ideal.span {(p : ℤ)} : Ideal ℤ) P = 1 ↔
      Nat.card ((𝓞 L) ⧸ P) = p := by
  haveI := hP.2
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_eq_pow_inertiaDeg' P hp]
  constructor
  · intro h
    rw [h, pow_one]
  · intro h
    exact Nat.pow_right_injective hp.two_le (by simpa using h)

/-- Cox, p. 239: a degree-one rational prime gives an ideal of absolute norm `p`. -/
theorem exists_prime_ideal_absNorm_eq_of_mem_degreeOnePrimes
    {L : IntermediateField ℚ ℂ} [NumberField L] {p : ℕ}
    (hp : p ∈ degreeOnePrimes L) :
    ∃ P : Ideal (𝓞 L),
      P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L) ∧ P.absNorm = p := by
  obtain ⟨hpu, P, hP, hf⟩ := hp
  haveI := hP.2
  exact ⟨P, hP, by rw [Ideal.absNorm_eq_pow_inertiaDeg' P hpu.1, hf, pow_one]⟩

/-- Cox, pp. 238–239: residue degree one is equivalent to identity rational Frobenius. -/
theorem inertiaDeg_eq_one_iff_forall_pow_eq {L : IntermediateField ℚ ℂ} [NumberField L]
    {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 L))
    (hP : P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L)) :
    Ideal.inertiaDeg (Ideal.span {(p : ℤ)} : Ideal ℤ) P = 1 ↔
      ∀ x : (𝓞 L) ⧸ P, x ^ p = x := by
  haveI := Fact.mk hp
  haveI := residue_charP hp P hP
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    have h := (hP.2 : (⊥ : Ideal (𝓞 L)).LiesOver (Ideal.span {(p : ℤ)})).over
    rw [Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ _),
      Ideal.span_singleton_eq_bot] at h
    exact hp.ne_zero (by exact_mod_cast h)
  haveI : P.IsMaximal := hP.1.isMaximal hP0
  letI : Field ((𝓞 L) ⧸ P) := Ideal.Quotient.field P
  rw [inertiaDeg_eq_one_iff_card hp P hP]
  constructor
  · intro h x
    haveI : Finite ((𝓞 L) ⧸ P) := Nat.finite_of_card_ne_zero (h ▸ hp.ne_zero)
    haveI : Fintype ((𝓞 L) ⧸ P) := Fintype.ofFinite _
    have hcard : Fintype.card ((𝓞 L) ⧸ P) = p := by rw [← Nat.card_eq_fintype_card, h]
    rw [← hcard]
    exact FiniteField.pow_card x
  · exact card_eq_prime_of_forall_pow_eq _ p

/-- Cox, (11.33): a Frobenius identity passes to any compatible quotient upstairs. -/
theorem quotient_pow_eq_of_le_comap {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (P : Ideal A) (Q : Ideal B) (hPQ : P ≤ Q.comap f)
    (p : ℕ) (x : A) (hx : (Ideal.Quotient.mk P x) ^ p = Ideal.Quotient.mk P x) :
    (Ideal.Quotient.mk Q (f x)) ^ p = Ideal.Quotient.mk Q (f x) := by
  have h := congrArg (Ideal.quotientMap Q f hPQ) hx
  rwa [map_pow, Ideal.quotientMap_mk] at h

/-- The normal closure of an embedded number field remains a number field. -/
theorem numberField_normalClosure (L : IntermediateField ℚ ℂ) [NumberField L] :
    NumberField (IntermediateField.normalClosure ℚ L ℂ) := by
  haveI : FiniteDimensional ℚ (IntermediateField.normalClosure ℚ L ℂ) :=
    normalClosure.is_finiteDimensional ℚ L ℂ
  exact ⟨⟩

/-- Complex splitting supplies the normal-closure predicate without normality of `ℂ/ℚ`. -/
theorem isNormalClosure_normalClosure (L : IntermediateField ℚ ℂ) [NumberField L] :
    IsNormalClosure ℚ L (IntermediateField.normalClosure ℚ L ℂ) := by
  exact Algebra.IsAlgebraic.isNormalClosure_normalClosure fun _ => IsAlgClosed.splits _

/-- Normality of the closure and characteristic-zero separability give Galoisness. -/
theorem isGalois_normalClosure (L : IntermediateField ℚ ℂ) [NumberField L] :
    IsGalois ℚ (IntermediateField.normalClosure ℚ L ℂ) := by
  haveI := isNormalClosure_normalClosure L
  haveI : Normal ℚ (IntermediateField.normalClosure ℚ L ℂ) := IsNormalClosure.normal (K := L)
  exact IsGalois.mk

/-- Two embedded number fields have a common finite Galois overfield (Cox, p. 171). -/
theorem exists_common_galois_overfield (L M : IntermediateField ℚ ℂ)
    [NumberField L] [NumberField M] :
    ∃ N : IntermediateField ℚ ℂ, NumberField N ∧ IsGalois ℚ N ∧ L ≤ N ∧ M ≤ N := by
  haveI : NumberField (L ⊔ M : IntermediateField ℚ ℂ) := ⟨⟩
  refine ⟨IntermediateField.normalClosure ℚ (L ⊔ M : IntermediateField ℚ ℂ) ℂ,
    numberField_normalClosure _, isGalois_normalClosure _, ?_, ?_⟩
  · exact le_sup_left.trans (IntermediateField.le_normalClosure _)
  · exact le_sup_right.trans (IntermediateField.le_normalClosure _)

/-- Rational primes admitting `σ` as an arithmetic Frobenius at some prime above them. -/
def frobeniusPrimes (N : IntermediateField ℚ ℂ) (σ : N ≃ₐ[ℚ] N) : Set ℕ :=
  {p | p ∈ unramifiedPrimes N ∧
    ∃ P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 N), IsArithFrobAt ℤ σ P}

/-- Frobenius-prime sets contain only unramified primes. -/
theorem frobeniusPrimes_subset_unramifiedPrimes (N : IntermediateField ℚ ℂ)
    (σ : N ≃ₐ[ℚ] N) : frobeniusPrimes N σ ⊆ unramifiedPrimes N := by
  exact fun _ hp => hp.1

open scoped Pointwise in
/-- Frobenius at conjugate primes gives the same set for conjugate automorphisms. -/
theorem frobeniusPrimes_eq_of_isConj (N : IntermediateField ℚ ℂ)
    (σ τ : N ≃ₐ[ℚ] N) (hστ : IsConj σ τ) :
    frobeniusPrimes N σ = frobeniusPrimes N τ := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hστ
  ext p
  constructor
  · rintro ⟨hpu, P, hP, hfrob⟩
    haveI := hP.1
    haveI := hP.2
    exact ⟨hpu, c • P, ⟨inferInstance, inferInstance⟩, hfrob.conj c⟩
  · rintro ⟨hpu, P, hP, hfrob⟩
    haveI := hP.1
    haveI := hP.2
    refine ⟨hpu, c⁻¹ • P, ⟨inferInstance, inferInstance⟩, ?_⟩
    have := hfrob.conj c⁻¹
    rwa [show c⁻¹ * (c * σ * c⁻¹) * c⁻¹⁻¹ = σ by group] at this

/-- The quotient of `ℤ` by `(p)` has `p` elements. -/
theorem natCard_int_quotient_span (p : ℕ) :
    Nat.card (ℤ ⧸ (Ideal.span {(p : ℤ)} : Ideal ℤ)) = p := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

/-- Identity Frobenius is equivalent to complete splitting in a finite Galois extension. -/
theorem frobeniusPrimes_one (N : IntermediateField ℚ ℂ) [NumberField N] [IsGalois ℚ N] :
    frobeniusPrimes N 1 = splittingPrimes N := by
  rw [← degreeOnePrimes_eq_splittingPrimes N]
  ext p
  constructor
  · rintro ⟨hpu, P, hP, hfrob⟩
    refine ⟨hpu, P, hP, (inertiaDeg_eq_one_iff_forall_pow_eq hpu.1 P hP).mpr fun x => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h := AlgHom.IsArithFrobAt.mk_apply hfrob x
    rw [← hP.2.over, natCard_int_quotient_span] at h
    simp only [MulSemiringAction.toAlgHom_apply, one_smul] at h
    exact h.symm
  · rintro ⟨hpu, P, hP, hf⟩
    refine ⟨hpu, P, hP, fun x => ?_⟩
    have hpow := (inertiaDeg_eq_one_iff_forall_pow_eq hpu.1 P hP).mp hf (Ideal.Quotient.mk P x)
    rw [← hP.2.over, natCard_int_quotient_span, MulSemiringAction.toAlgHom_apply, one_smul,
      ← Ideal.Quotient.eq, map_pow]
    exact hpow.symm

/-- Planning child: rational prime-ideal transport. -/
theorem absNorm_span_nat (p : ℕ) : Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p := by
  rw [Ideal.absNorm_span_singleton, show (p : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) by simp,
    Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one,
    Int.natAbs_natCast]

/-- Planning child: rational prime-ideal transport. -/
theorem ratSpan_eq_comap_intSpan (p : ℕ) :
    Ideal.span {(p : 𝓞 ℚ)} = Ideal.comap Rat.ringOfIntegersEquiv (Ideal.span {(p : ℤ)}) := by
  rw [← Ideal.map_symm, Ideal.map_span, Set.image_singleton, map_natCast]

/-- Planning child: rational prime-ideal transport. -/
theorem ratPrime_eq_span (𝔭 : Ideal (𝓞 ℚ)) (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ 𝔭 = Ideal.span {(p : 𝓞 ℚ)} := by
  set e := Rat.ringOfIntegersEquiv
  haveI : (𝔭.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  have h𝔭 : 𝔭 = (𝔭.map e).comap e := (Ideal.comap_map_of_bijective e e.bijective).symm
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (𝔭.map e)).principal
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply hne
    rw [h𝔭, hg, Submodule.span_zero_singleton]
    exact Ideal.comap_bot_of_injective _ e.injective
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp
    (by rw [← Ideal.submodule_span_eq, ← hg]; infer_instance)
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, ?_⟩
  rw [ratSpan_eq_comap_intSpan, h𝔭, hg, Ideal.submodule_span_eq,
    Ideal.span_singleton_eq_span_singleton.mpr (Int.associated_natAbs g)]

/-- Planning child: rational prime-ideal transport. -/
theorem span_nat_isPrime {p : ℕ} (hpp : p.Prime) :
    (Ideal.span {(p : 𝓞 ℚ)}).IsPrime := by
  rw [ratSpan_eq_comap_intSpan]
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hpp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hpp)
  exact Ideal.comap_isPrime _ _

/-- Planning child: rational prime-ideal transport. -/
theorem ringOfIntegers_rat_algebraMap_eq (N : IntermediateField ℚ ℂ) (x : 𝓞 ℚ) :
    algebraMap (𝓞 ℚ) (𝓞 N) x = algebraMap ℤ (𝓞 N) (Rat.ringOfIntegersEquiv x) := by
  conv_lhs => rw [← Rat.ringOfIntegersEquiv.symm_apply_apply x]
  rw [eq_intCast Rat.ringOfIntegersEquiv.symm, map_intCast, eq_intCast]

/-- Planning child: rational prime-ideal transport. -/
theorem under_rat_eq_comap_under_int (N : IntermediateField ℚ ℂ) (P : Ideal (𝓞 N)) :
    P.under (𝓞 ℚ) = (P.under ℤ).comap Rat.ringOfIntegersEquiv := by
  ext x
  rw [Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, Ideal.under_def, Ideal.mem_comap,
    ringOfIntegers_rat_algebraMap_eq]

/-- Planning child: rational prime-ideal transport. -/
theorem ratSpan_primesOver_iff (N : IntermediateField ℚ ℂ) (p : ℕ) (P : Ideal (𝓞 N)) :
    P ∈ (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).primesOver (𝓞 N) ↔
      P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 N) := by
  have h : (Ideal.span {(p : 𝓞 ℚ)} = P.under (𝓞 ℚ)) ↔
      (Ideal.span {(p : ℤ)} : Ideal ℤ) = P.under ℤ := by
    rw [ratSpan_eq_comap_intSpan, under_rat_eq_comap_under_int]
    exact (Ideal.comap_injective_of_surjective _ Rat.ringOfIntegersEquiv.surjective).eq_iff
  simp only [Ideal.primesOver, Set.mem_setOf_eq, Ideal.liesOver_iff, h]

/-- Planning child: rational prime-ideal transport. -/
theorem ramificationIdx_ratSpan_eq (N : IntermediateField ℚ ℂ) (p : ℕ) (P : Ideal (𝓞 N)) :
    Ideal.ramificationIdx (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) P =
      Ideal.ramificationIdx (Ideal.span {(p : ℤ)} : Ideal ℤ) P := by
  simp only [Ideal.ramificationIdx, Ideal.map_span, Set.image_singleton, map_natCast]

/-- Planning child: rational prime-ideal transport. -/
theorem card_rat_quotient_under_eq_int (N : IntermediateField ℚ ℂ) (P : Ideal (𝓞 N)) :
    Nat.card ((𝓞 ℚ) ⧸ P.under (𝓞 ℚ)) = Nat.card (ℤ ⧸ P.under ℤ) := by
  exact Nat.card_congr (Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv (by
    rw [under_rat_eq_comap_under_int]
    exact (Ideal.map_comap_of_surjective (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)
      Rat.ringOfIntegersEquiv.surjective _).symm)).toEquiv

/-- Planning child: rational prime-ideal transport. -/
theorem isArithFrobAt_rat_iff (N : IntermediateField ℚ ℂ) [NumberField N] [IsGalois ℚ N]
    (σ : N ≃ₐ[ℚ] N)
    (P : Ideal (𝓞 N)) :
    IsArithFrobAt (𝓞 ℚ) σ P ↔ IsArithFrobAt ℤ σ P := by
  simp only [IsArithFrobAt, AlgHom.IsArithFrobAt, MulSemiringAction.toAlgHom_apply,
    card_rat_quotient_under_eq_int]

/-- Planning child: rational prime-ideal transport. -/
theorem unramifiedIn_ratSpan_iff (N : IntermediateField ℚ ℂ) [NumberField N]
    {p : ℕ} (hp : p.Prime) :
    Chebotarev.UnramifiedIn ℚ N (Ideal.span {(p : 𝓞 ℚ)}) ↔ p ∈ unramifiedPrimes N := by
  have hspanZ : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  have hspanQ : (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hp, fun P hP => ?_⟩
    haveI := hP.1
    haveI := hP.2
    have hPQ := (ratSpan_primesOver_iff N p P).mpr hP
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspanZ P
    have h1 := (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP0).mp
      (h P (hP.1.isMaximal hP0) hPQ.2)
    rw [← hPQ.2.over, ramificationIdx_ratSpan_eq] at h1
    exact h1
  · rintro ⟨-, h⟩
    refine ⟨hspanQ, fun P hPmax hlo => ?_⟩
    haveI := hPmax.isPrime
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspanQ P
    have hPZ := (ratSpan_primesOver_iff N p P).mp ⟨inferInstance, hlo⟩
    refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP0).mpr ?_
    rw [← hlo.over, ramificationIdx_ratSpan_eq]
    exact h P hPZ

open scoped Pointwise in
/-- Planning child: rational prime-ideal transport. -/
theorem exists_isArithFrobAt_of_rat_class_eq (N : IntermediateField ℚ ℂ)
    [NumberField N] [IsGalois ℚ N] (q : Ideal (𝓞 ℚ)) [q.IsPrime]
    (hq : Chebotarev.UnramifiedIn ℚ N q) (σ : N ≃ₐ[ℚ] N)
    (hclass : Chebotarev.frobeniusClass ℚ N q = ConjClasses.mk σ) :
    ∃ P : Ideal (𝓞 N), P.IsPrime ∧ P.LiesOver q ∧ IsArithFrobAt (𝓞 ℚ) σ P := by
  obtain ⟨𝔓, h𝔓p, h𝔓lo, -⟩ :=
    Chebotarev.exists_prime_liesOver ℚ N q (Chebotarev.UnramifiedIn.ne_bot ℚ N hq)
  haveI := h𝔓p
  haveI := h𝔓lo
  haveI : Finite (𝓞 N ⧸ 𝔓) := Chebotarev.UnramifiedIn.finite_quotient ℚ N hq 𝔓 h𝔓lo
  have hφ := IsArithFrobAt.arithFrobAt (𝓞 ℚ) (N ≃ₐ[ℚ] N) 𝔓
  have hcl := Chebotarev.frobeniusClass_eq_mk_of_isArithFrobAt ℚ N q hq _ 𝔓 hφ h𝔓lo
  rw [hclass] at hcl
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hcl.symm)
  refine ⟨c • 𝔓, inferInstance, inferInstance, ?_⟩
  rw [← hc]
  exact hφ.conj c

/-- Translate the source's prime ideals of `𝓞 ℚ` to positive rational prime generators. -/
theorem frobeniusClassPrimes_rat_eq_image (N : IntermediateField ℚ ℂ)
    [NumberField N] [IsGalois ℚ N] (σ : N ≃ₐ[ℚ] N) :
    Chebotarev.frobeniusClassPrimes ℚ N (ConjClasses.mk σ) =
      (fun p : ℕ ↦ (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ))) '' frobeniusPrimes N σ := by
  ext 𝔭
  constructor
  · rintro ⟨h𝔭p, hunr, hcl⟩
    haveI := h𝔭p
    obtain ⟨p, hp, rfl⟩ := ratPrime_eq_span 𝔭 h𝔭p (Chebotarev.UnramifiedIn.ne_bot ℚ N hunr)
    refine ⟨p, ⟨(unramifiedIn_ratSpan_iff N hp).mp hunr, ?_⟩, rfl⟩
    obtain ⟨P, hPp, hPlo, hfrob⟩ := exists_isArithFrobAt_of_rat_class_eq N _ hunr σ hcl
    exact ⟨P, (ratSpan_primesOver_iff N p P).mp ⟨hPp, hPlo⟩,
      (isArithFrobAt_rat_iff N σ P).mp hfrob⟩
  · rintro ⟨p, ⟨hpu, P, hP, hfrob⟩, rfl⟩
    haveI := span_nat_isPrime hpu.1
    have hunr := (unramifiedIn_ratSpan_iff N hpu.1).mpr hpu
    have hPQ := (ratSpan_primesOver_iff N p P).mpr hP
    haveI := hPQ.1
    exact ⟨inferInstance, hunr, Chebotarev.frobeniusClass_eq_mk_of_isArithFrobAt ℚ N _ hunr σ P
      ((isArithFrobAt_rat_iff N σ P).mpr hfrob) hPQ.2⟩

/-- Qualitative Chebotarev, via the prime-ideal theorem and the rational-prime adapter. -/
theorem infinite_frobeniusPrimes (N : IntermediateField ℚ ℂ)
    [NumberField N] [IsGalois ℚ N] (σ : N ≃ₐ[ℚ] N) :
    (frobeniusPrimes N σ).Infinite := by
  have h := Chebotarev.infinite_setOf_frobenius_class ℚ N (ConjClasses.mk σ)
  change (Chebotarev.frobeniusClassPrimes ℚ N (ConjClasses.mk σ)).Infinite at h
  rw [frobeniusClassPrimes_rat_eq_image] at h
  exact Set.Infinite.of_image _ h

/-- A prescribed Frobenius can be chosen outside any finite set (Cox, p. 172). -/
theorem exists_mem_frobeniusPrimes_notMem (N : IntermediateField ℚ ℂ)
    [NumberField N] [IsGalois ℚ N] (σ : N ≃ₐ[ℚ] N)
    {e : Set ℕ} (he : e.Finite) : ∃ p ∈ frobeniusPrimes N σ, p ∉ e := by
  exact (infinite_frobeniusPrimes N σ).exists_notMem_finite he

/-- A Frobenius fixing `M` produces a degree-one prime of `M` (Cox, pp. 171–172). -/
theorem mem_degreeOnePrimes_of_frobenius_fixes {M N : IntermediateField ℚ ℂ}
    [NumberField M] [NumberField N] (hMN : M ≤ N) (σ : N ≃ₐ[ℚ] N) {p : ℕ}
    (hp : p ∈ frobeniusPrimes N σ)
    (hfix : ∀ x : M, σ (IntermediateField.inclusion hMN x) =
      IntermediateField.inclusion hMN x) : p ∈ degreeOnePrimes M := by
  obtain ⟨hpu, P, hP, hfrob⟩ := hp
  letI : Algebra M N := (IntermediateField.inclusion hMN).toAlgebra
  haveI := hP.1
  haveI := hP.2
  set Q : Ideal (𝓞 M) := P.under (𝓞 M) with hQdef
  haveI hQp : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨by rw [hQdef, Ideal.under_under]; exact hP.2.over⟩
  have hQmem : Q ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 M) := ⟨inferInstance, hQp⟩
  refine ⟨unramifiedPrimes_mono hMN hpu, Q, hQmem,
    (inertiaDeg_eq_one_iff_forall_pow_eq hpu.1 Q hQmem).mpr fun y => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 := AlgHom.IsArithFrobAt.mk_apply hfrob (algebraMap (𝓞 M) (𝓞 N) x)
  rw [← hP.2.over, natCard_int_quotient_span] at h1
  have hσx : (MulSemiringAction.toAlgHom ℤ (𝓞 N) σ) (algebraMap (𝓞 M) (𝓞 N) x) =
      algebraMap (𝓞 M) (𝓞 N) x := by
    apply RingOfIntegers.ext
    exact hfix (x : M)
  rw [hσx] at h1
  have hmem : algebraMap (𝓞 M) (𝓞 N) x - (algebraMap (𝓞 M) (𝓞 N) x) ^ p ∈ P :=
    Ideal.Quotient.eq.mp (h1.trans (map_pow _ _ _).symm)
  rw [← map_pow, Ideal.Quotient.eq, hQdef, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow,
    ← neg_sub]
  exact P.neg_mem hmem

/-- An integral basis gives a finite set of rational algebra generators. -/
theorem exists_finite_integral_generators (L : IntermediateField ℚ ℂ) [NumberField L] :
    ∃ s : Set (𝓞 L), s.Finite ∧ Algebra.adjoin ℚ ((algebraMap (𝓞 L) L) '' s) = ⊤ := by
  refine ⟨Set.range (RingOfIntegers.basis L), Set.finite_range _, ?_⟩
  have himg : (algebraMap (𝓞 L) L) '' Set.range (RingOfIntegers.basis L) =
      Set.range (integralBasis L) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp [integralBasis_apply]
  rw [himg, eq_top_iff]
  intro x _
  exact Algebra.span_le_adjoin ℚ _ ((integralBasis L).mem_span x)

/-- Frobenius restricts to the identity on a completely split Galois subfield. -/
theorem frobenius_fixes_of_mem_splittingPrimes {L N : IntermediateField ℚ ℂ}
    [NumberField L] [NumberField N] [IsGalois ℚ L]
    (hLN : L ≤ N) (σ : N ≃ₐ[ℚ] N) {p : ℕ}
    (hp : p ∈ frobeniusPrimes N σ) (hpL : p ∈ splittingPrimes L) :
    ∀ x : L, σ (IntermediateField.inclusion hLN x) =
      IntermediateField.inclusion hLN x := by
  obtain ⟨-, P, hP, hfrob⟩ := hp
  letI : Algebra L N := (IntermediateField.inclusion hLN).toAlgebra
  haveI : IsScalarTower ℚ L N :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion hLN).commutes x).symm
  haveI := hP.1
  haveI := hP.2
  set τ : L ≃ₐ[ℚ] L := σ.restrictNormal L with hτ
  have hcomm : ∀ x : L, algebraMap L N (τ x) = σ (algebraMap L N x) :=
    fun x => σ.restrictNormal_commutes L x
  set Q : Ideal (𝓞 L) := P.under (𝓞 L) with hQdef
  haveI hQp : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨by rw [hQdef, Ideal.under_under]; exact hP.2.over⟩
  have hQmem : Q ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L) := ⟨inferInstance, hQp⟩
  have hspan : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hpL.1.1.ne_zero
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspan Q
  have hτfrob : IsArithFrobAt ℤ τ Q := by
    intro y
    rw [← hQp.over, natCard_int_quotient_span, hQdef, Ideal.under_def, Ideal.mem_comap,
      map_sub, map_pow]
    have h := hfrob (algebraMap (𝓞 L) (𝓞 N) y)
    rw [← hP.2.over, natCard_int_quotient_span] at h
    convert h using 2
    apply RingOfIntegers.ext
    exact hcomm (y : L)
  have h1frob : IsArithFrobAt ℤ (1 : L ≃ₐ[ℚ] L) Q := by
    intro y
    have hpow := (inertiaDeg_eq_one_iff_forall_pow_eq hpL.1.1 Q hQmem).mp (hpL.2 Q hQmem)
      (Ideal.Quotient.mk Q y)
    rw [← hQp.over, natCard_int_quotient_span, MulSemiringAction.toAlgHom_apply, one_smul,
      ← Ideal.Quotient.eq, map_pow]
    exact hpow.symm
  haveI : Algebra.IsUnramifiedAt ℤ Q := by
    refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hQ0).mpr ?_
    rw [← hQp.over]
    exact hpL.1.2 Q hQmem
  have heq := AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hτfrob h1frob
    (Ideal.primeCompl_le_nonZeroDivisors Q)
  have hτ1 : τ = 1 := by
    obtain ⟨s, -, hs⟩ := exists_finite_integral_generators L
    apply AlgEquiv.coe_algHom_injective
    refine AlgHom.ext_of_adjoin_eq_top hs ?_
    rintro _ ⟨y, -, rfl⟩
    have h2 := congrArg (fun f => f y) heq
    simp only [MulSemiringAction.toAlgHom_apply, one_smul] at h2
    exact congrArg (algebraMap (𝓞 L) L) h2
  intro x
  have := hcomm x
  rw [hτ1] at this
  simpa using this.symm

/-- Galois correspondence converts containment of fixing groups to field containment. -/
theorem le_of_forall_fixes {L M N : IntermediateField ℚ ℂ}
    [NumberField N] [IsGalois ℚ N] (hLN : L ≤ N) (hMN : M ≤ N)
    (hfix : ∀ σ : N ≃ₐ[ℚ] N,
      (∀ x : M, σ (IntermediateField.inclusion hMN x) =
        IntermediateField.inclusion hMN x) →
      ∀ x : L, σ (IntermediateField.inclusion hLN x) =
        IntermediateField.inclusion hLN x) : L ≤ M := by
  set L' : IntermediateField ℚ N := (IntermediateField.inclusion hLN).fieldRange with hL'
  set M' : IntermediateField ℚ N := (IntermediateField.inclusion hMN).fieldRange with hM'
  have hsub : M'.fixingSubgroup ≤ L'.fixingSubgroup := by
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    have hM : ∀ x : M, σ (IntermediateField.inclusion hMN x) =
        IntermediateField.inclusion hMN x :=
      fun x => hσ _ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
    intro y hy
    obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    exact hfix σ hM x
  have hle : L' ≤ M' := by
    rw [← IsGalois.fixedField_fixingSubgroup L', ← IsGalois.fixedField_fixingSubgroup M']
    exact IntermediateField.fixedField_le hsub
  intro x hx
  obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp
    (hle (AlgHom.mem_fieldRange.mpr ⟨⟨x, hx⟩, rfl⟩))
  have hxy : (y : ℂ) = x := congrArg (fun z : N => (z : ℂ)) hy
  rw [← hxy]
  exact y.2

/-- Cox Proposition 8.20(ii), p. 171: the smaller comparison field is Galois. -/
theorem le_iff_degreeOnePrimes_almostSubset (L M : IntermediateField ℚ ℂ)
    [NumberField L] [NumberField M] [IsGalois ℚ L] :
    L ≤ M ↔ AlmostSubset (degreeOnePrimes M) (splittingPrimes L) := by
  constructor
  · intro hLM
    have hsub : degreeOnePrimes M ⊆ splittingPrimes L :=
      degreeOnePrimes_eq_splittingPrimes L ▸ degreeOnePrimes_mono hLM
    simp [AlmostSubset, Set.diff_eq_empty.mpr hsub]
  · intro h
    obtain ⟨N, hNnf, hNgal, hLN, hMN⟩ := exists_common_galois_overfield L M
    haveI := hNnf
    haveI := hNgal
    refine le_of_forall_fixes hLN hMN fun σ hfix => ?_
    obtain ⟨p, hp, hpe⟩ := exists_mem_frobeniusPrimes_notMem N σ h
    have hpM : p ∈ degreeOnePrimes M := mem_degreeOnePrimes_of_frobenius_fixes hMN σ hp hfix
    have hpL : p ∈ splittingPrimes L := by
      by_contra hnot
      exact hpe ⟨hpM, hnot⟩
    exact frobenius_fixes_of_mem_splittingPrimes hLN σ hp hpL

/-- All images of a set of algebraic integers under rational embeddings. -/
def integralConjugates (L N : IntermediateField ℚ ℂ) (s : Set (𝓞 L)) : Set (𝓞 N) :=
  {y | ∃ f : L →ₐ[ℚ] N, ∃ x ∈ s,
    y = RingOfIntegers.mapRingHom f.toRingHom x}

/-- A finite extension has finitely many embeddings, so this conjugate set is finite. -/
theorem finite_integralConjugates (L N : IntermediateField ℚ ℂ) [NumberField L]
    (s : Set (𝓞 L)) (hs : s.Finite) : (integralConjugates L N s).Finite := by
  refine (Set.finite_iUnion fun f : L →ₐ[ℚ] N =>
    hs.image (RingOfIntegers.mapRingHom f.toRingHom)).subset ?_
  rintro y ⟨f, x, hx, rfl⟩
  exact Set.mem_iUnion.mpr ⟨f, x, hx, rfl⟩

/-- Composition of embeddings makes the conjugate set stable under automorphisms. -/
theorem integralConjugates_stable (L N : IntermediateField ℚ ℂ) (s : Set (𝓞 L))
    (σ : N ≃ₐ[ℚ] N) {y : 𝓞 N} (hy : y ∈ integralConjugates L N s) :
    RingOfIntegers.mapRingHom σ.toRingHom y ∈ integralConjugates L N s := by
  obtain ⟨f, x, hx, rfl⟩ := hy
  refine ⟨(σ : N →ₐ[ℚ] N).comp f, x, hx, ?_⟩
  ext
  simp

/-- A normal closure is generated by the conjugates of any generating set. -/
theorem adjoin_integralConjugates_eq_top (L N : IntermediateField ℚ ℂ)
    [NumberField L] [NumberField N] [IsNormalClosure ℚ L N]
    (s : Set (𝓞 L)) (hs : Algebra.adjoin ℚ ((algebraMap (𝓞 L) L) '' s) = ⊤) :
    Algebra.adjoin ℚ ((algebraMap (𝓞 N) N) '' integralConjugates L N s) = ⊤ := by
  set T : Set N := algebraMap (𝓞 N) N '' integralConjugates L N s with hT
  have halg : ∀ x ∈ T, IsAlgebraic ℚ x := fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
  have htop : IntermediateField.adjoin ℚ T = ⊤ := by
    have hnc : IntermediateField.normalClosure ℚ L N = ⊤ :=
      (Algebra.IsAlgebraic.isNormalClosure_iff.mp ‹IsNormalClosure ℚ L N›).2
    rw [eq_top_iff, ← hnc, normalClosure_def]
    refine iSup_le fun f => ?_
    intro y hy
    obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    have hx : x ∈ Algebra.adjoin ℚ ((algebraMap (𝓞 L) L) '' s) := hs ▸ Algebra.mem_top
    have hfx : f x ∈ Algebra.adjoin ℚ (f '' ((algebraMap (𝓞 L) L) '' s)) := by
      rw [← AlgHom.map_adjoin]
      exact Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩
    refine (Algebra.adjoin_le ?_ :
      Algebra.adjoin ℚ _ ≤ (IntermediateField.adjoin ℚ T).toSubalgebra) hfx
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    apply IntermediateField.subset_adjoin
    exact ⟨RingOfIntegers.mapRingHom f.toRingHom z, ⟨f, z, hz, rfl⟩, rfl⟩
  rw [htop, IntermediateField.top_toSubalgebra]

/-- A completely split prime fixes every embedded lower integer in the upper residue field. -/
theorem quotient_pow_eq_of_splitting_embedding {L N : IntermediateField ℚ ℂ}
    [NumberField L] (f : L →ₐ[ℚ] N) {p : ℕ} (hp : p ∈ splittingPrimes L)
    (P : Ideal (𝓞 N))
    (hP : P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 N)) (x : 𝓞 L) :
    Ideal.Quotient.mk P (RingOfIntegers.mapRingHom f.toRingHom x) ^ p =
      Ideal.Quotient.mk P (RingOfIntegers.mapRingHom f.toRingHom x) := by
  haveI := hP.1
  haveI := hP.2
  set g : 𝓞 L →+* 𝓞 N := RingOfIntegers.mapRingHom f.toRingHom with hg
  set Q : Ideal (𝓞 L) := P.comap g with hQ
  haveI : Q.IsPrime := Ideal.comap_isPrime g P
  have hQover : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
    constructor
    rw [Ideal.under_def, hQ, Ideal.comap_comap,
      show g.comp (algebraMap ℤ (𝓞 L)) = algebraMap ℤ (𝓞 N) from RingHom.ext_int _ _,
      ← Ideal.under_def]
    exact hP.2.over
  have hQmem : Q ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L) := ⟨inferInstance, hQover⟩
  have hy := (inertiaDeg_eq_one_iff_forall_pow_eq hp.1.1 Q hQmem).mp (hp.2 Q hQmem)
    (Ideal.Quotient.mk Q x)
  exact quotient_pow_eq_of_le_comap g Q P le_rfl p x hy

-- `hp` belongs to the planned signature; the proof does not need it.
set_option linter.unusedVariables false in
/-- Injective reduction on a stable generating set turns Frobenius congruence into equality. -/
theorem frobenius_eq_one_of_injective_reduction {N : IntermediateField ℚ ℂ}
    (s : Set (𝓞 N)) (hs : Algebra.adjoin ℚ ((algebraMap (𝓞 N) N) '' s) = ⊤)
    (σ : N ≃ₐ[ℚ] N) (hstable : ∀ x ∈ s, RingOfIntegers.mapRingHom σ.toRingHom x ∈ s)
    {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 N))
    (hP : P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 N))
    (hσ : IsArithFrobAt ℤ σ P)
    (hpow : ∀ x ∈ s, Ideal.Quotient.mk P x ^ p = Ideal.Quotient.mk P x)
    (hinj : Function.Injective (fun x : s ↦ Ideal.Quotient.mk P x.1)) : σ = 1 := by
  haveI := hP.2
  have hfix : ∀ x ∈ s, RingOfIntegers.mapRingHom σ.toRingHom x = x := by
    intro x hx
    have h1 := AlgHom.IsArithFrobAt.mk_apply hσ x
    rw [← hP.2.over, natCard_int_quotient_span] at h1
    have h2 : Ideal.Quotient.mk P (RingOfIntegers.mapRingHom σ.toRingHom x) =
        Ideal.Quotient.mk P x := by
      rw [← hpow x hx, ← h1]
      rfl
    exact congrArg Subtype.val
      (hinj (a₁ := ⟨_, hstable x hx⟩) (a₂ := ⟨x, hx⟩) h2)
  apply AlgEquiv.coe_algHom_injective
  refine AlgHom.ext_of_adjoin_eq_top hs ?_
  rintro _ ⟨x, hx, rfl⟩
  have := congrArg (algebraMap (𝓞 N) N) (hfix x hx)
  simpa using this

/-- A prime of a finite Galois number field admits an arithmetic Frobenius. -/
theorem exists_frobenius_at_prime (N : IntermediateField ℚ ℂ)
    [NumberField N] [IsGalois ℚ N] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 N))
    (hP : P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 N)) :
    ∃ σ : N ≃ₐ[ℚ] N, IsArithFrobAt ℤ σ P := by
  haveI := hP.1
  haveI := hP.2
  have hspan : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  haveI : Finite (𝓞 N ⧸ P) :=
    Ideal.finiteQuotientOfFreeOfNeBot P (Ideal.ne_bot_of_liesOver_of_ne_bot hspan P)
  exact IsArithFrobAt.exists_of_isInvariant ℤ (N ≃ₐ[ℚ] N) P

/-- Cox's normal-closure step only needs finite-exception inclusion. -/
theorem splittingPrimes_almostSubset_of_isNormalClosure (L N : IntermediateField ℚ ℂ)
    [NumberField L] [NumberField N] [IsGalois ℚ N] [IsNormalClosure ℚ L N] :
    AlmostSubset (splittingPrimes L) (splittingPrimes N) := by
  obtain ⟨s₀, hs₀fin, hs₀⟩ := exists_finite_integral_generators L
  set s : Set (𝓞 N) := integralConjugates L N s₀ with hs
  have hsfin : s.Finite := finite_integralConjugates L N s₀ hs₀fin
  have hstop := adjoin_integralConjugates_eq_top L N s₀ hs₀
  haveI : Finite s := hsfin.to_subtype
  obtain ⟨e₁, he₁, hcoll⟩ :=
    finite_collision_primes N (Subtype.val : s → 𝓞 N) Subtype.val_injective
  rw [almostSubset_iff_exists_finite]
  refine ⟨e₁ ∪ {p : ℕ | p.Prime ∧ p ∉ unramifiedPrimes N}, he₁.union (finite_ramifiedPrimes N),
    fun p hp => ?_⟩
  by_cases hpe : p ∈ e₁ ∪ {p : ℕ | p.Prime ∧ p ∉ unramifiedPrimes N}
  · exact Or.inr hpe
  left
  have hpp : p.Prime := hp.1.1
  have hpN : p ∈ unramifiedPrimes N := by
    by_contra h
    exact hpe (Or.inr ⟨hpp, h⟩)
  have hpe₁ : p ∉ e₁ := fun h => hpe (Or.inl h)
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hpp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hpp)
  obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 N) (Ideal.span {(p : ℤ)})
  obtain ⟨σ, hσ⟩ := exists_frobenius_at_prime N hpp P hP
  have hσ1 : σ = 1 := by
    refine frobenius_eq_one_of_injective_reduction s hstop σ
      (fun x hx => integralConjugates_stable L N s₀ σ hx) hpp P hP hσ ?_
      (hcoll p hpe₁ hpp P hP)
    rintro _ ⟨f, z, hz, rfl⟩
    exact quotient_pow_eq_of_splitting_embedding f hp P hP z
  rw [← frobeniusPrimes_one N]
  exact ⟨hpN, P, hP, hσ1 ▸ hσ⟩

/-- Finite-exception normal-closure comparison sufficient for Cox Proposition 8.20(i). -/
theorem splittingPrimes_almostSubset_normalClosure (L : IntermediateField ℚ ℂ)
    [NumberField L] : AlmostSubset (splittingPrimes L)
      (splittingPrimes (IntermediateField.normalClosure ℚ L ℂ)) := by
  haveI := numberField_normalClosure L
  haveI := isGalois_normalClosure L
  haveI := isNormalClosure_normalClosure L
  exact splittingPrimes_almostSubset_of_isNormalClosure L _

/-- Cox Proposition 8.20(i), p. 171: the larger comparison field is Galois. -/
theorem le_iff_splittingPrimes_almostSubset (L M : IntermediateField ℚ ℂ)
    [NumberField L] [NumberField M] [IsGalois ℚ M] :
    L ≤ M ↔ AlmostSubset (splittingPrimes M) (splittingPrimes L) := by
  constructor
  · intro hLM
    simp [AlmostSubset, Set.diff_eq_empty.mpr (splittingPrimes_mono hLM)]
  · intro h
    haveI := numberField_normalClosure L
    haveI := isGalois_normalClosure L
    have h2 := h.trans (splittingPrimes_almostSubset_normalClosure L)
    rw [← degreeOnePrimes_eq_splittingPrimes M] at h2
    exact (IntermediateField.le_normalClosure L).trans
      ((le_iff_degreeOnePrimes_almostSubset (IntermediateField.normalClosure ℚ L ℂ) M).mpr h2)
end Cox
