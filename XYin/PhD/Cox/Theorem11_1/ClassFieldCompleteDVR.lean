/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! # Finite extensions of complete discrete valuation rings

Janusz, II.3.2–3.3, pp. 80–82: coordinate completeness, lifting idempotents, and the Chinese
remainder decomposition of the integral closure.
-/

noncomputable section
open scoped nonZeroDivisors
open Module IsLocalRing
namespace Cox.ClassFieldTheory

section Coordinates
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type*} (b : Basis ι R M) (I : Ideal R)

/-- Janusz II.3.3: ideal divisibility of a vector is coordinatewise divisibility. -/
theorem mem_ideal_smul_top_iff_basis (x : M) :
    x ∈ (I • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on (p := fun y => b.repr y i ∈ I) hx
      (fun r hr m _ => ?_) (fun y z hy hz => ?_)
    · beta_reduce
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · beta_reduce at hy hz ⊢
      rw [map_add, Finsupp.add_apply]
      exact I.add_mem hy hz
  · intro h
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
    exact Submodule.finsuppSum_mem _ _ _ _ fun i _ =>
      Submodule.smul_mem_smul (h i) Submodule.mem_top

include b in
/-- Janusz II.3.3: separatedness is checked in the basis coordinates. -/
theorem adicHausdorff_of_basis [IsHausdorff I R] : IsHausdorff I M := by
  constructor
  intro x hx
  have hcoord : ∀ i, b.repr x i = 0 := fun i => by
    apply IsHausdorff.haus' (I := I) (b.repr x i)
    intro n
    have h1 := (mem_ideal_smul_top_iff_basis b (I ^ n) x).mp (SModEq.zero.mp (hx n)) i
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact h1
  apply b.repr.injective
  ext i
  rw [hcoord i, map_zero, Finsupp.zero_apply]

include b in
/-- Janusz II.3.3: a compatible sequence has coordinatewise limits. -/
theorem adicPrecomplete_of_basis [Finite ι] [IsPrecomplete I R] : IsPrecomplete I M := by
  haveI := Fintype.ofFinite ι
  constructor
  intro f hf
  have hcoord : ∀ i, ∃ Li : R, ∀ n,
      b.repr (f n) i ≡ Li [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i => by
    apply IsPrecomplete.prec' (I := I) (fun n => b.repr (f n) i)
    intro m n hmn
    have h := hf hmn
    rw [SModEq.sub_mem] at h ⊢
    have h2 := (mem_ideal_smul_top_iff_basis b (I ^ m) _).mp h i
    rw [map_sub, Finsupp.sub_apply] at h2
    rw [smul_eq_mul, Ideal.mul_top]
    exact h2
  choose L hL using hcoord
  refine ⟨∑ i, L i • b i, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_ideal_smul_top_iff_basis b (I ^ n)]
  intro i
  have h := hL i n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  rw [map_sub, Finsupp.sub_apply, b.repr_sum_self]
  exact h

/-- Janusz II.3.3: finite free modules over an adically complete ring are complete. -/
theorem adicComplete_of_finite_free [Module.Finite R M] [Module.Free R M]
    [IsAdicComplete I R] : IsAdicComplete I M := by
  let b := Module.Free.chooseBasis R M
  exact { toIsHausdorff := adicHausdorff_of_basis b I,
          toIsPrecomplete := adicPrecomplete_of_basis b I }
end Coordinates

section Idempotents
variable {R : Type*} [CommRing R]

/-- Janusz II.3.2: lift one idempotent through a Henselian quotient. -/
theorem henselian_idempotent_lift (I : Ideal R) [HenselianRing R I]
    (e : R ⧸ I) (he : IsIdempotentElem e) :
    ∃ a : R, IsIdempotentElem a ∧ Ideal.Quotient.mk I a = e := by
  nontriviality R
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective e
  have hmon : (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic := by
    apply Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow 2)
    rw [Polynomial.degree_X, Polynomial.degree_X_pow]
    norm_num
  have he' : Ideal.Quotient.mk I a₀ * Ideal.Quotient.mk I a₀ = Ideal.Quotient.mk I a₀ := he
  have h1 : (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).eval a₀ ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, map_sub, map_pow, sq, he',
      sub_self]
  have h2 : IsUnit (Ideal.Quotient.mk I
      ((Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X : Polynomial R)).eval a₀)) := by
    have hd : Ideal.Quotient.mk I
        ((Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X : Polynomial R)).eval a₀) =
          2 * Ideal.Quotient.mk I a₀ - 1 := by
      simp
      ring
    rw [hd]
    exact IsUnit.of_mul_eq_one (2 * Ideal.Quotient.mk I a₀ - 1)
      (by linear_combination (4 : R ⧸ I) * he')
  obtain ⟨a, ha, hai⟩ := HenselianRing.is_henselian _ hmon a₀ h1 h2
  refine ⟨a, ?_, ?_⟩
  · have h3 : a ^ 2 - a = 0 := by simpa [Polynomial.IsRoot] using ha
    change a * a = a
    linear_combination h3
  · rw [Ideal.Quotient.eq]
    exact hai

/-- Janusz II.3.3: a complete domain has no nontrivial idempotent in this quotient. -/
theorem adic_quotient_idempotent_trivial [IsDomain R] (I : Ideal R)
    [IsAdicComplete I R] (e : R ⧸ I) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  haveI : HenselianRing R I := IsAdicComplete.henselianRing R I
  obtain ⟨a, ha, rfl⟩ := henselian_idempotent_lift I e he
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp ha with rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (map_one _)

/-- Janusz II.3.3: two different factors yield a nontrivial product idempotent. -/
theorem exists_nontrivial_product_idempotent {ι : Type*} (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Nontrivial (A i)]
    (i j : ι) (hij : i ≠ j) :
    ∃ e : (∀ i, A i), IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  refine ⟨Pi.single i 1, ?_, ?_, ?_⟩
  · change Pi.single i 1 * Pi.single i 1 = Pi.single i (1 : A i)
    rw [← Pi.single_mul, mul_one]
  · intro h
    have h1 := congrFun h i
    simp at h1
  · intro h
    have h1 := congrFun h j
    simp [Pi.single_eq_of_ne hij.symm] at h1
end Idempotents

section FiniteAlgebra
variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable [hfinite : Module.Finite R S] [hfaithful : IsTorsionFree R S]
include hfinite hfaithful

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- Janusz II.3.3: every maximal ideal of the integral extension lies over the base prime. -/
theorem finiteAlgebra_maximal_liesOver (P : Ideal S) [P.IsMaximal] :
    P.LiesOver (maximalIdeal R) := by
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  exact ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under R P)).symm⟩

/-- Janusz II.3.3: the image of the nonzero base prime remains nonzero. -/
theorem finiteAlgebra_map_maximal_ne_bot :
    Ideal.map (algebraMap R S) (maximalIdeal R) ≠ ⊥ := by
  have hinj : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective R S
  rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  exact IsDiscreteValuationRing.not_a_field R

/-- Janusz II.3.3: the CRT factors cannot contain two distinct primes. -/
theorem adicComplete_prime_factors_subsingleton
    [IsAdicComplete (Ideal.map (algebraMap R S) (maximalIdeal R)) S] :
    Set.Subsingleton (Ideal.primesOver (maximalIdeal R) S) := by
  classical
  intro P hP Q hQ
  by_contra hPQ
  have hJ := finiteAlgebra_map_maximal_ne_bot R S
  have hmem : ∀ X ∈ Ideal.primesOver (maximalIdeal R) S,
      X ∈ (UniqueFactorizationMonoid.factors
        (Ideal.map (algebraMap R S) (maximalIdeal R))).toFinset := by
    intro X hX
    haveI : X.IsPrime := hX.1
    haveI : X.LiesOver (maximalIdeal R) := hX.2
    rw [Multiset.mem_toFinset, UniqueFactorizationMonoid.factors_eq_normalizedFactors,
      Ideal.mem_normalizedFactors_iff hJ]
    exact ⟨hX.1, Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.over_def X (maximalIdeal R)))⟩
  let e := IsDedekindDomain.quotientEquivPiFactors hJ
  haveI hnt : ∀ X : (UniqueFactorizationMonoid.factors
      (Ideal.map (algebraMap R S) (maximalIdeal R))).toFinset,
      Nontrivial (S ⧸ (X : Ideal S) ^ (Multiset.count ↑X (UniqueFactorizationMonoid.factors
        (Ideal.map (algebraMap R S) (maximalIdeal R))))) := fun X => by
    rw [Ideal.Quotient.nontrivial_iff]
    have hX := X.2
    rw [Multiset.mem_toFinset] at hX
    have hprime := UniqueFactorizationMonoid.prime_of_factor _ hX
    have hcount : Multiset.count (↑X) (UniqueFactorizationMonoid.factors
        (Ideal.map (algebraMap R S) (maximalIdeal R))) ≠ 0 :=
      (Multiset.count_pos.mpr hX).ne'
    intro htop
    have hle := Ideal.pow_le_self (I := (X : Ideal S)) hcount
    rw [htop, top_le_iff] at hle
    exact (Ideal.isPrime_of_prime hprime).ne_top hle
  obtain ⟨f, hf, hf0, hf1⟩ := exists_nontrivial_product_idempotent
    (fun X : (UniqueFactorizationMonoid.factors
      (Ideal.map (algebraMap R S) (maximalIdeal R))).toFinset =>
        S ⧸ (X : Ideal S) ^ (Multiset.count ↑X (UniqueFactorizationMonoid.factors
          (Ideal.map (algebraMap R S) (maximalIdeal R)))))
    ⟨P, hmem P hP⟩ ⟨Q, hmem Q hQ⟩ (fun h => hPQ (congrArg Subtype.val h))
  have hidem : IsIdempotentElem (e.symm f) := by
    change e.symm f * e.symm f = e.symm f
    rw [← map_mul, hf.eq]
  haveI : IsAdicComplete (Ideal.map (algebraMap R S) (maximalIdeal R)) S := inferInstance
  rcases adic_quotient_idempotent_trivial _ (e.symm f) hidem with h | h
  · exact hf0 (by rw [← e.apply_symm_apply f, h, map_zero])
  · exact hf1 (by rw [← e.apply_symm_apply f, h, map_one])

/-- Janusz II.3.3: the complete integral extension is local. -/
theorem finiteAlgebra_isLocalRing_of_adicComplete
    [IsAdicComplete (Ideal.map (algebraMap R S) (maximalIdeal R)) S] :
    IsLocalRing S := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal S
  refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun N hN => ?_⟩
  haveI := hM
  haveI := hN
  exact adicComplete_prime_factors_subsingleton R S
    ⟨hN.isPrime, finiteAlgebra_maximal_liesOver R S N⟩
    ⟨hM.isPrime, finiteAlgebra_maximal_liesOver R S M⟩

/-- Janusz II.3.3: a finite integral extension of a DVR cannot be a field. -/
theorem finiteAlgebra_not_isField : ¬ IsField S := by
  intro hS
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hinj : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective R S
  exact IsDiscreteValuationRing.not_isField R
    ((Algebra.IsIntegral.isField_iff_isField hinj).mpr hS)
end FiniteAlgebra

section IntegralClosure
variable (R K L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [hfinite : FiniteDimensional K L]
variable [hseparable : Algebra.IsSeparable K L]
variable [Algebra R L] [IsScalarTower R K L]
variable [hcomplete : IsAdicComplete (maximalIdeal R) R]
include hfinite hseparable hcomplete

/-- Janusz II.3.3: coordinate completeness applies to the integral closure. -/
theorem integralClosure_adicComplete :
    IsAdicComplete
      (Ideal.map (algebraMap R (integralClosure R L)) (maximalIdeal R))
      (integralClosure R L) := by
  haveI : IsTorsionFree R L := isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))
  haveI : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R K L (integralClosure R L)
  haveI : Module.Free R (integralClosure R L) :=
    IsIntegralClosure.module_free R K L (integralClosure R L)
  haveI : IsAdicComplete (maximalIdeal R) (integralClosure R L) :=
    adicComplete_of_finite_free (maximalIdeal R)
  exact (IsAdicComplete.map_algebraMap_iff (I := maximalIdeal R)
    (M := integralClosure R L)).mpr inferInstance

/-- Janusz II.3.3: the integral closure has a unique maximal ideal. -/
theorem integralClosure_isLocalRing : IsLocalRing (integralClosure R L) := by
  haveI : IsTorsionFree R L := isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))
  haveI : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  haveI : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R K L (integralClosure R L)
  haveI := integralClosure_adicComplete R K L
  exact finiteAlgebra_isLocalRing_of_adicComplete R (integralClosure R L)

/-- Janusz II.3.3: the integral closure is a discrete valuation ring. -/
theorem integralClosure_isDiscreteValuationRing :
    IsDiscreteValuationRing (integralClosure R L) := by
  haveI := integralClosure_isLocalRing R K L
  haveI : IsTorsionFree R L := isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))
  haveI : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  haveI : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R K L (integralClosure R L)
  have hnf := finiteAlgebra_not_isField R (integralClosure R L)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure R L) hnf).out 0 2).mpr
    (inferInstance : IsDedekindDomain (integralClosure R L))
end IntegralClosure

section ValuationSubring
variable {L : Type*} [Field L]

/-- The rank-one overring criterion identifies a DVR with any proper valuation overring. -/
theorem dvrSubring_eq_valuationSubring_of_le (C : Subring L)
    [IsDiscreteValuationRing C] [IsFractionRing C L]
    (V : ValuationSubring L) (hCV : C ≤ V.toSubring) (hV : V ≠ ⊤) :
    C = V.toSubring := by
  have hor : ∀ x : L, x ∈ C ∨ x⁻¹ ∈ C := fun x => by
    rcases ValuationRing.isInteger_or_isInteger C x with ⟨y, hy⟩ | ⟨y, hy⟩
    · left
      rw [← hy]
      exact y.2
    · right
      rw [← hy]
      exact y.2
  let V₀ : ValuationSubring L := { C with mem_or_inv_mem' := hor }
  haveI : Ring.KrullDimLE 1 V₀ := inferInstanceAs (Ring.KrullDimLE 1 C)
  have h := ValuationSubring.eq_of_le_of_ne_top (A := V₀) (fun x hx => hCV hx) hV
  exact congrArg ValuationSubring.toSubring h

/-- Integral elements lie in a valuation ring containing the coefficient ring. -/
theorem integralClosure_le_valuationSubring (R : Type*) [CommRing R]
    [Algebra R L] (V : ValuationSubring L) [Algebra R V]
    [IsScalarTower R V L] :
    (integralClosure R L).toSubring ≤ V.toSubring := by
  intro x hx
  have h2 : IsIntegral V x := (show IsIntegral R x from hx).tower_top
  have hint : V.valuation.Integers V := ⟨Subtype.val_injective, fun y => V.valuation_le_one y,
    fun r hr => ⟨⟨r, V.mem_of_valuation_le_one r hr⟩, rfl⟩⟩
  exact V.mem_of_valuation_le_one x (hint.mem_of_integral h2)
end ValuationSubring

section CompleteValuationSubring
variable (R K L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [hfinite : FiniteDimensional K L]
variable [hseparable : Algebra.IsSeparable K L]
variable [Algebra R L] [IsScalarTower R K L]
variable [hcomplete : IsAdicComplete (maximalIdeal R) R]
variable (V : ValuationSubring L) [Algebra R V] [IsScalarTower R V L]
include hfinite hseparable hcomplete

/-- Janusz II.3.3–3.4: the actual proper valuation ring is the integral closure. -/
theorem complete_integralClosure_eq_valuationSubring (hV : V ≠ ⊤) :
    (integralClosure R L).toSubring = V.toSubring := by
  haveI := integralClosure_isDiscreteValuationRing R K L
  haveI : IsFractionRing (integralClosure R L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R K L (integralClosure R L)
  haveI : IsDiscreteValuationRing (integralClosure R L).toSubring :=
    inferInstanceAs (IsDiscreteValuationRing (integralClosure R L))
  haveI : IsFractionRing (integralClosure R L).toSubring L :=
    inferInstanceAs (IsFractionRing (integralClosure R L) L)
  exact dvrSubring_eq_valuationSubring_of_le (integralClosure R L).toSubring V
    (integralClosure_le_valuationSubring R V) hV

/-- Janusz II.3.3: the proper valuation overring satisfies the integral-closure property. -/
theorem complete_valuationSubring_isIntegralClosure (hV : V ≠ ⊤) :
    IsIntegralClosure V R L := by
  have heq := complete_integralClosure_eq_valuationSubring R K L V hV
  refine ⟨Subtype.val_injective, fun {x} => ?_⟩
  constructor
  · intro hx
    have h1 : x ∈ (integralClosure R L).toSubring := hx
    rw [heq] at h1
    exact ⟨⟨x, h1⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    have h1 : (y : L) ∈ V.toSubring := y.2
    rw [← heq] at h1
    exact h1

/-- Janusz II.3.3: the completed valuation ring is finite over the base integer ring. -/
theorem complete_valuationSubring_finite (hV : V ≠ ⊤) : Module.Finite R V := by
  haveI := complete_valuationSubring_isIntegralClosure R K L V hV
  exact IsIntegralClosure.finite R K L V
end CompleteValuationSubring
end Cox.ClassFieldTheory
