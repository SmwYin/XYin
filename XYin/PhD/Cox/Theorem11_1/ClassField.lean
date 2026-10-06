/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldEmbedding
import XYin.PhD.Cox.Theorem11_1.OrderClasses
import XYin.PhD.Cox.Theorem11_1.RingClassConjugation
import XYin.PhD.Cox.Theorem11_1.RingClassSplitting

/-! # Cox order classes and ring class fields

For an order `O` of an imaginary quadratic field `K`, the class group `C(O)` is the quotient
`I_K(f) / P_{K,ℤ}(f)` (Cox Proposition 7.22), hence finite. Class-field existence gives an
embedded ring class field, unique by its Artin kernel and Galois over `ℚ` by the conjugation
argument of Cox Lemma 9.3. Up to finitely many exceptions, its completely split primes are
exactly the rational primes represented by the norm form of `O` (Cox (11.28)).
-/

open NumberField
open scoped nonZeroDivisors

noncomputable section
namespace Cox.Order
variable {K : IntermediateField ℚ ℂ} [hNF : NumberField K]

variable (O : Subalgebra ℤ K) [hO : IsOrder O]
include hNF hO

/-- The conductor modulus is a nonzero ideal of `O_K`. -/
theorem conductorIdeal_ne_bot : conductorIdeal O ≠ ⊥ := by
  rw [conductorIdeal, Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast (conductor_pos O).ne'

/-- The ring-class subgroup has finite index, as a congruence subgroup; Cox (8.1). -/
theorem rationalPrincipalIdeals_finiteIndex :
    (rationalPrincipalIdeals O).FiniteIndex := by
  haveI : (rayPrincipalIdeals O).FiniteIndex :=
    ClassFieldTheory.raySubgroup_finiteIndex K _ (conductorIdeal_ne_bot O)
  exact Subgroup.finiteIndex_of_le (rayPrincipalIdeals_le_rationalPrincipalIdeals O)

omit hNF hO in
/-- An embedded number field containing `K` stays a number field over `ℂ/K`. -/
theorem numberField_extendScalars {L : IntermediateField ℚ ℂ} [NumberField L] (hKL : K ≤ L) :
    NumberField (IntermediateField.extendScalars hKL) := by
  let e : L ≃+* IntermediateField.extendScalars hKL :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  exact NumberField.of_ringEquiv _ _ e

/-- An embedded Artin-kernel field over `K`, with the inclusion algebra, keeps its kernel
when viewed as an intermediate field of `ℂ/K`. -/
theorem hasArtinKernel_extendScalars {L : IntermediateField ℚ ℂ} [NumberField L]
    (hKL : K ≤ L) {H : Subgroup (conductorCoprimeIdeals O)}
    (hL : letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
      HasArtinKernel O L H) :
    HasArtinKernel O (IntermediateField.extendScalars hKL) H := by
  letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  let e : L ≃ₐ[K] IntermediateField.extendScalars hKL :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  haveI := numberField_extendScalars hKL
  exact ClassFieldTheory.hasArtinKernel_algEquiv K _ L _ e hL

variable [hK : IsImaginaryQuadraticField K]

include hO hK

/-- Cox Proposition 7.22: the independent ideal-class quotient for a quadratic order. -/
theorem classGroup_equiv_conductorQuotient :
    Nonempty (ClassGroup O ≃* (conductorCoprimeIdeals O ⧸ rationalPrincipalIdeals O)) := by
  obtain ⟨e⟩ := classGroup_equiv_orderCoprimeQuotient O
  exact ⟨e.trans (QuotientGroup.congr _ _ (orderCoprimeEquiv O)
    (orderCoprimeEquiv_map_principal O))⟩

/-- Cox Theorem 7.7(ii): the ideal class group of an imaginary quadratic order is finite. -/
theorem finite_classGroup : Finite (ClassGroup O) := by
  obtain ⟨e⟩ := classGroup_equiv_conductorQuotient O
  haveI := rationalPrincipalIdeals_finiteIndex O
  exact Finite.of_equiv _ e.symm.toEquiv

/-- Cox §9.A: the ring class field exists by the independently specified congruence subgroup. -/
theorem exists_ringClassField :
    ∃ L : IntermediateField ℚ ℂ, IsRingClassField O L := by
  obtain ⟨L, hNL, hKL, hL⟩ := exists_artinKernel O (rationalPrincipalIdeals O)
    (rayPrincipalIdeals_le_rationalPrincipalIdeals O)
  exact ⟨L, hNL, hKL, hL⟩

-- `hK` is part of the fixed signature: uniqueness holds over any number field `K`.
set_option linter.unusedSectionVars false in
/-- Cox Corollary 8.7 / Janusz V.9.16: equal Artin kernels determine the embedded class field. -/
theorem ringClassField_unique {L M : IntermediateField ℚ ℂ}
    (hL : IsRingClassField O L) (hM : IsRingClassField O M) : L = M := by
  haveI := hL.numberField
  haveI := hM.numberField
  haveI := numberField_extendScalars hL.le
  haveI := numberField_extendScalars hM.le
  -- Compare both fields as intermediate fields of `ℂ/K`.
  have h := ClassFieldTheory.eq_of_artinKernel_eq _ _ (conductorIdeal O) (conductorIdeal_ne_bot O)
    (hasArtinKernel_extendScalars O hL.le hL.artinKernel)
    (hasArtinKernel_extendScalars O hM.le hM.artinKernel)
  -- Restricting scalars back to `ℚ` recovers the original fields.
  exact congrArg (fun E : IntermediateField K ℂ => (E.restrictScalars ℚ : IntermediateField ℚ ℂ)) h

/-- Cox Lemma 9.3: the independently constructed ring class field is Galois over `ℚ`. -/
theorem isGalois_ringClassField {L : IntermediateField ℚ ℂ}
    (hL : IsRingClassField O L) : IsGalois ℚ L := by
  haveI := hL.numberField
  have hconj := ringClassField_unique O (isRingClassField_conjugate K O hL) hL
  letI : Algebra K L := (IntermediateField.inclusion hL.le).toRingHom.toAlgebra
  haveI := hL.artinKernel.isGalois
  exact isGalois_of_conjugateField_eq K hL.le inferInstance hconj

/-- Rational primes which are norms of elements of the order; Cox (11.28). -/
def normPrimes : Set ℕ :=
  {p | p.Prime ∧ ∃ α : O, Algebra.norm ℚ (α : K) = (p : ℚ)}

/-- Cox Theorem 9.4 and Exercise 9.3, the forward half of (11.28). -/
theorem splittingPrimes_norm_criterion {L : IntermediateField ℚ ℂ}
    (hL : IsRingClassField O L) :
    AlmostSubset (splittingPrimes L) (normPrimes O) := by
  haveI := hL.numberField
  letI : Algebra K L := (IntermediateField.inclusion hL.le).toRingHom.toAlgebra
  -- The exceptions divide the conductor.
  refine ((conductor O).divisors.finite_toSet).subset fun p ⟨hp, hpn⟩ => ?_
  rw [Finset.mem_coe, Nat.mem_divisors]
  refine ⟨?_, (conductor_pos O).ne'⟩
  by_contra hdvd
  have hcop : p.Coprime (conductor O) := (Nat.Prime.coprime_iff_not_dvd hp.1.1).mpr hdvd
  exact hpn ⟨hp.1.1, exists_order_norm_of_relative_split O L hL.artinKernel hcop
    (exists_relative_split_prime_of_splitting hL.le hp)⟩

/-- Cox Theorem 9.4 and Exercise 9.3, the reverse half of (11.28). -/
theorem normPrimes_splitting_criterion {L : IntermediateField ℚ ℂ}
    (hL : IsRingClassField O L) :
    AlmostSubset (normPrimes O) (splittingPrimes L) := by
  haveI := hL.numberField
  haveI := isGalois_ringClassField O hL
  letI : Algebra K L := (IntermediateField.inclusion hL.le).toRingHom.toAlgebra
  -- The exceptions divide the conductor or ramify in `L`.
  refine (((conductor O).divisors.finite_toSet).union (finite_ramifiedPrimes L)).subset
    fun p ⟨⟨hpp, hα⟩, hps⟩ => ?_
  by_contra hmem
  rw [Set.mem_union, Finset.mem_coe, Nat.mem_divisors, Set.mem_setOf_eq, not_or] at hmem
  have hcop : p.Coprime (conductor O) := (Nat.Prime.coprime_iff_not_dvd hpp).mpr
    fun h => hmem.1 ⟨h, (conductor_pos O).ne'⟩
  have hpu : p ∈ unramifiedPrimes L := Classical.byContradiction fun h => hmem.2 ⟨hpp, h⟩
  exact hps (splitting_of_relative_split_prime hL.le hpu
    (exists_relative_split_of_order_norm O L hL.artinKernel hpp hcop hα))

end Cox.Order
