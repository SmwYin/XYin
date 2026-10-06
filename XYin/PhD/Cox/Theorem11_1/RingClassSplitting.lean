/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.OrderClasses
import XYin.PhD.Cox.Theorem11_1.ClassFieldTheory
import XYin.PhD.Cox.Theorem11_1.Splitting

/-! # The prime norm equivalences of Cox Theorem 9.4

The statements use arbitrary imaginary quadratic orders, covering Exercise 9.3.
The Artin kernel is the independently defined rational-principal subgroup; no
norm/splitting equivalence is assumed. Splitting of a good prime is translated into
triviality of its order ideal class, then into a principal contraction, and finally
into representation of the prime by the order norm.
-/

open NumberField
open scoped nonZeroDivisors
noncomputable section
namespace Cox

/-- A prime ideal of absolute norm p lies above p. -/
theorem liesOver_of_absNorm_eq_prime {K : IntermediateField ℚ ℂ} [NumberField K]
    (q : Ideal (𝓞 K)) [q.IsPrime] {p : ℕ} (hp : p.Prime) (hq : q.absNorm = p) :
    q.LiesOver (Ideal.span {(p : ℤ)} : Ideal ℤ) := by
  have hmax : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hmem : ((q.absNorm : ℕ) : 𝓞 K) ∈ q := Ideal.absNorm_mem q
  rw [hq] at hmem
  refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap]
  simpa using hmem

/-- The residue-cardinality formula in a tower at relative residue degree one. -/
theorem absNorm_eq_of_relative_inertiaDeg_eq_one {K L : Type*}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (q : Ideal (𝓞 K)) [q.IsPrime] (hq : q ≠ ⊥)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver q]
    (hf : Ideal.inertiaDeg q P = 1) : P.absNorm = q.absNorm := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P q inferInstance hq, hf, pow_one]

/-- Cox 9.4: both relative indices divide the corresponding rational indices. -/
theorem relative_split_of_mem_splittingPrimes {K L : IntermediateField ℚ ℂ}
    [NumberField K] [NumberField L] (hKL : K ≤ L) {p : ℕ}
    (hp : p ∈ splittingPrimes L) (q : Ideal (𝓞 K))
    (hq : q ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)) :
    letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
    q ∈ ClassFieldTheory.splittingIdeals K L := by
  letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  obtain ⟨hpu, hsplit⟩ := hp
  have hp0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa using hpu.1.ne_zero
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hpu.1).irreducible
  haveI := hq.1
  haveI := hq.2
  have hq0 : q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 hq
  haveI : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q (Ideal.span {(p : ℤ)})
  refine ⟨hq.1, hq0, fun P hP => ?_⟩
  haveI := hP.1
  haveI := hP.2
  haveI : P.LiesOver (Ideal.span {(p : ℤ)} : Ideal ℤ) := Ideal.LiesOver.trans P q _
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P q
  have hP' : P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L) := ⟨hP.1, inferInstance⟩
  have he := Ideal.ramificationIdx_algebra_tower' (Ideal.span {(p : ℤ)} : Ideal ℤ) q P
  have hf := Ideal.inertiaDeg_algebra_tower (Ideal.span {(p : ℤ)} : Ideal ℤ) q P
  rw [hpu.2 P hP'] at he
  rw [hsplit P hP'] at hf
  exact ⟨(mul_eq_one.mp he.symm).2, (mul_eq_one.mp hf.symm).2⟩

/-- Cox 9.4: lift the split norm-p base prime and multiply relative residue degrees. -/
theorem degreeOne_of_relative_split_prime {K L : IntermediateField ℚ ℂ}
    [NumberField K] [NumberField L] (hKL : K ≤ L) {p : ℕ}
    (hp : p ∈ unramifiedPrimes L)
    (hq : letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
      ∃ q : Ideal (𝓞 K), q.absNorm = p ∧ q ∈ ClassFieldTheory.splittingIdeals K L) :
    p ∈ degreeOnePrimes L := by
  letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  obtain ⟨q, hqn, hqprime, hq0, hsplit⟩ := hq
  haveI := hqprime
  haveI : q.LiesOver (Ideal.span {(p : ℤ)} : Ideal ℤ) := liesOver_of_absNorm_eq_prime q hp.1 hqn
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.1).irreducible
  haveI : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q (Ideal.span {(p : ℤ)})
  obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) q
  haveI := hP.1
  haveI := hP.2
  haveI : P.LiesOver (Ideal.span {(p : ℤ)} : Ideal ℤ) := Ideal.LiesOver.trans P q _
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P q
  refine ⟨hp, P, ⟨hP.1, inferInstance⟩, ?_⟩
  have hfq : (Ideal.span {(p : ℤ)} : Ideal ℤ).inertiaDeg q = 1 := by
    have h := Ideal.absNorm_eq_pow_inertiaDeg' q hp.1
    rw [hqn, eq_comm] at h
    exact (Nat.pow_eq_self_iff hp.1.one_lt).mp h
  rw [Ideal.inertiaDeg_algebra_tower (Ideal.span {(p : ℤ)} : Ideal ℤ) q P, hfq,
    (hsplit P hP).2]

/-- Cox 9.4, last equivalence: complete splitting supplies a norm-p base prime
which splits in the upper extension. This direction needs no Galois hypothesis. -/
theorem exists_relative_split_prime_of_splitting {K L : IntermediateField ℚ ℂ}
    [NumberField K] [NumberField L] (hKL : K ≤ L) {p : ℕ}
    (hp : p ∈ splittingPrimes L) :
    letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
    ∃ q : Ideal (𝓞 K), q.absNorm = p ∧ q ∈ ClassFieldTheory.splittingIdeals K L := by
  letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  have hpp := hp.1.1
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hpp).irreducible
  obtain ⟨⟨q, hq⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 K) (Ideal.span {(p : ℤ)} : Ideal ℤ)
  refine ⟨q, ?_, relative_split_of_mem_splittingPrimes hKL hp q hq⟩
  haveI := hq.1
  haveI := hq.2
  haveI : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q (Ideal.span {(p : ℤ)})
  obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) q
  haveI := hP.1
  haveI := hP.2
  haveI : P.LiesOver (Ideal.span {(p : ℤ)} : Ideal ℤ) := Ideal.LiesOver.trans P q _
  have hf := Ideal.inertiaDeg_algebra_tower (Ideal.span {(p : ℤ)} : Ideal ℤ) q P
  rw [hp.2 P ⟨hP.1, inferInstance⟩] at hf
  rw [Ideal.absNorm_eq_pow_inertiaDeg' q hpp, (mul_eq_one.mp hf.symm).1, pow_one]

/-- Cox 9.4, last equivalence: a split norm-p base prime supplies a degree-one
prime upstairs, hence complete splitting when the upper field is Galois over ℚ. -/
theorem splitting_of_relative_split_prime {K L : IntermediateField ℚ ℂ}
    [NumberField K] [NumberField L] [IsGalois ℚ L] (hKL : K ≤ L) {p : ℕ}
    (hp : p ∈ unramifiedPrimes L)
    (hq : letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
      ∃ q : Ideal (𝓞 K), q.absNorm = p ∧ q ∈ ClassFieldTheory.splittingIdeals K L) :
    p ∈ splittingPrimes L := by
  rw [← degreeOnePrimes_eq_splittingPrimes L]
  exact degreeOne_of_relative_split_prime hKL hp hq

namespace Order
variable {K : IntermediateField ℚ ℂ} [hNF : NumberField K]
variable (O : Subalgebra ℤ K) [hO : IsOrder O] [hIQ : IsImaginaryQuadraticField K]
include hNF hO hIQ

/-- Cox 7.20/7.22: contraction followed by taking the ideal class. -/
def conductorIdealClassMap : conductorCoprimeIdeals O →* ClassGroup O :=
  (orderCoprimeClassMap O).comp (orderCoprimeEquiv O).symm.toMonoidHom

/-- The concrete class map has the prescribed ring-class subgroup as its kernel. -/
theorem conductorIdealClassMap_ker :
    (conductorIdealClassMap O).ker = rationalPrincipalIdeals O := by
  rw [conductorIdealClassMap, ← MonoidHom.comap_ker, orderCoprimeClassMap_ker,
    ← orderCoprimeEquiv_map_principal]
  exact Subgroup.comap_equiv_eq_map_symm (orderCoprimeEquiv O).symm (orderPrincipalIdeals O)

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- A good integral maximal-order ideal has a representative in the Artin domain. -/
theorem exists_conductorCoprime_unit (q : Ideal (𝓞 K)) (hq : q ≠ ⊥)
    (hcop : q.absNorm.Coprime (conductor O)) :
    ∃ u : conductorCoprimeIdeals O,
      ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q := by
  haveI : Finite ((𝓞 K) ⧸ q) := Ideal.finiteQuotientOfFreeOfNeBot q hq
  have hsup : q ⊔ conductorIdeal O = ⊤ :=
    (OrderCoprimality.sup_span_natCast_eq_top_iff_coprime_card q (conductor O)).mpr
      (by rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcop)
  exact ClassFieldTheory.exists_coprimeIdealUnit K (conductorIdeal O) q hq hsup

/-- Cox 7.20: the inverse extension equivalence sends an integral ideal to its contraction. -/
theorem orderCoprimeEquiv_symm_integral (q : Ideal (𝓞 K))
    (hcop : q.absNorm.Coprime (conductor O)) (u : conductorCoprimeIdeals O)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q) :
    ((((orderCoprimeEquiv O).symm u : orderCoprimeIdeals O) :
      (FractionalIdeal O⁰ K)ˣ) : FractionalIdeal O⁰ K) = contractIdeal O q := by
  have hq0 : q ≠ ⊥ := by
    rintro rfl
    exact (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ).ne_zero (by rw [hu, FractionalIdeal.coeIdeal_bot])
  have hcop' : (Nat.card ((𝓞 K) ⧸ q)).Coprime (conductor O) := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcop
  have hp := isPrimeToConductor_contract O q hcop'
  have ha0 : contractIdeal O q ≠ ⊥ := by
    intro h
    apply hq0
    rw [← extend_contract O q hcop', h, extendIdeal, Ideal.map_bot]
  have hunit := isUnit_of_isPrimeToConductor O _ hp ha0
  let w : orderCoprimeIdeals O := ⟨integralIdealUnit O _ hunit,
    Subgroup.subset_closure ⟨_, ha0, hp, coe_integralIdealUnit O _ hunit⟩⟩
  have hw : (orderCoprimeEquiv O).symm u = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    apply Units.ext
    rw [hu]
    change _ = (extendFractional O (integralIdealUnit O _ hunit) : FractionalIdeal (𝓞 K)⁰ K)
    rw [extendFractional_integral O _ _ (coe_integralIdealUnit O _ hunit),
      extend_contract O q hcop']
  rw [hw]
  exact coe_integralIdealUnit O _ hunit

/-- Cox 9.4, second equivalence: a trivial class is a principal contracted ideal. -/
theorem conductorIdealClassMap_eq_one_iff (q : Ideal (𝓞 K))
    (hcop : q.absNorm.Coprime (conductor O)) (u : conductorCoprimeIdeals O)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q) :
    conductorIdealClassMap O u = 1 ↔ ∃ α : O, contractIdeal O q = Ideal.span {α} := by
  change orderCoprimeClassMap O ((orderCoprimeEquiv O).symm u) = 1 ↔ _
  rw [orderCoprimeClassMap_apply, idealClass, ClassGroup.mk_eq_one_iff,
    orderCoprimeEquiv_symm_integral O q hcop u hu, FractionalIdeal.coe_coeIdeal,
    IsFractionRing.coeSubmodule_isPrincipal]
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α, hα.trans (Ideal.submodule_span_eq).symm⟩
  · rintro ⟨α, hα⟩
    exact ⟨α, hα.trans Ideal.submodule_span_eq⟩

/-- Cox 9.4, first equivalence: a principal contracted norm-p ideal gives a norm-p element. -/
theorem exists_order_norm_of_principal_contract (q : Ideal (𝓞 K)) {p : ℕ}
    (hcop : p.Coprime (conductor O)) (hq : q.absNorm = p)
    (hprincipal : ∃ α : O, contractIdeal O q = Ideal.span {α}) :
    ∃ α : O, Algebra.norm ℚ (α : K) = (p : ℚ) := by
  obtain ⟨α, hα⟩ := hprincipal
  have hcard : Nat.card ((𝓞 K) ⧸ q) = p := by
    rw [← hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h := idealNorm_contract O q (hcard ▸ hcop)
  rw [hα, idealNorm_span_singleton, hcard] at h
  exact ⟨α, by rw [← elementNorm_eq_fieldNorm, h]⟩

/-- Cox 9.4, first equivalence in reverse: extending a principal order ideal preserves its norm. -/
theorem absNorm_extend_principal {p : ℕ} (hcop : p.Coprime (conductor O))
    (α : O) (hα : Algebra.norm ℚ (α : K) = (p : ℚ)) :
    (extendIdeal O (Ideal.span {α})).absNorm = p := by
  have hN : elementNorm O α = p := by
    exact_mod_cast (elementNorm_eq_fieldNorm O α).trans hα
  have hgood : IsPrimeToConductor O (Ideal.span {α}) := by
    rw [IsPrimeToConductor, idealNorm_span_singleton, hN]
    exact hcop
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, idealNorm_extend O _ hgood,
    idealNorm_span_singleton, hN]

/-- A prime absolute norm makes the extended ideal prime. -/
theorem isPrime_extend_principal {p : ℕ} (hp : p.Prime)
    (hcop : p.Coprime (conductor O)) (α : O)
    (hα : Algebra.norm ℚ (α : K) = (p : ℚ)) :
    (extendIdeal O (Ideal.span {α})).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_extend_principal O hcop α hα]
  exact hp.prime.irreducible

/-- Cox 9.4, second equivalence: the extension of a good principal O-ideal has trivial class. -/
theorem conductorIdealClassMap_extend_principal {p : ℕ}
    (hcop : p.Coprime (conductor O)) (α : O)
    (hα : Algebra.norm ℚ (α : K) = (p : ℚ)) (u : conductorCoprimeIdeals O)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      extendIdeal O (Ideal.span {α})) : conductorIdealClassMap O u = 1 := by
  have hN : elementNorm O α = p := by
    exact_mod_cast (elementNorm_eq_fieldNorm O α).trans hα
  have hgood : IsPrimeToConductor O (Ideal.span {α}) := by
    rw [IsPrimeToConductor, idealNorm_span_singleton, hN]
    exact hcop
  have hcop' : (extendIdeal O (Ideal.span {α})).absNorm.Coprime (conductor O) := by
    rw [absNorm_extend_principal O hcop α hα]
    exact hcop
  exact (conductorIdealClassMap_eq_one_iff O _ hcop' u hu).mpr ⟨α, contract_extend O _ hgood⟩

section Artin
variable (L : Type*) [Field L] [NumberField L] [Algebra K L]

/-- Cox 9.4, middle equivalences: splitting of a good prime means its order ideal class is
trivial. -/
theorem splits_iff_conductorIdealClassMap_eq_one
    (hL : HasArtinKernel O L (rationalPrincipalIdeals O))
    (q : Ideal (𝓞 K)) (hq : q.IsPrime) (hq0 : q ≠ ⊥)
    (hcop : q.absNorm.Coprime (conductor O)) (u : conductorCoprimeIdeals O)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q) :
    q ∈ ClassFieldTheory.splittingIdeals K L ↔ conductorIdealClassMap O u = 1 := by
  obtain ⟨-, hGal, -, hU, φ, hφ, -, hker⟩ := hL
  haveI := hGal
  haveI : Finite ((𝓞 K) ⧸ q) := Ideal.finiteQuotientOfFreeOfNeBot q hq0
  have hsup : q ⊔ conductorIdeal O = ⊤ :=
    (OrderCoprimality.sup_span_natCast_eq_top_iff_coprime_card q (conductor O)).mpr
      (by rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcop)
  rw [ClassFieldTheory.splits_iff_artin_eq_one K (conductorIdeal O) L hU φ hφ hq hq0 hsup u hu,
    ← MonoidHom.mem_ker, hker, ← conductorIdealClassMap_ker O]
  exact MonoidHom.mem_ker

/-- Cox 9.4: a split norm-p ideal yields representation by the order norm. -/
theorem exists_order_norm_of_relative_split
    (hL : HasArtinKernel O L (rationalPrincipalIdeals O)) {p : ℕ}
    (hcop : p.Coprime (conductor O))
    (hq : ∃ q : Ideal (𝓞 K), q.absNorm = p ∧ q ∈ ClassFieldTheory.splittingIdeals K L) :
    ∃ α : O, Algebra.norm ℚ (α : K) = (p : ℚ) := by
  obtain ⟨q, hqn, hqs⟩ := hq
  have hcop' : q.absNorm.Coprime (conductor O) := hqn ▸ hcop
  obtain ⟨u, hu⟩ := exists_conductorCoprime_unit O q hqs.2.1 hcop'
  have h1 := (splits_iff_conductorIdealClassMap_eq_one O L hL q hqs.1 hqs.2.1 hcop' u hu).mp hqs
  exact exists_order_norm_of_principal_contract O q hcop hqn
    ((conductorIdealClassMap_eq_one_iff O q hcop' u hu).mp h1)

/-- Cox 9.4: a represented good prime produces a norm-p ideal which splits in the class field. -/
theorem exists_relative_split_of_order_norm
    (hL : HasArtinKernel O L (rationalPrincipalIdeals O)) {p : ℕ}
    (hp : p.Prime) (hcop : p.Coprime (conductor O))
    (hα : ∃ α : O, Algebra.norm ℚ (α : K) = (p : ℚ)) :
    ∃ q : Ideal (𝓞 K), q.absNorm = p ∧ q ∈ ClassFieldTheory.splittingIdeals K L := by
  obtain ⟨α, hα⟩ := hα
  have hN := absNorm_extend_principal O hcop α hα
  have hprime := isPrime_extend_principal O hp hcop α hα
  have hq0 : extendIdeal O (Ideal.span {α}) ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hN
    exact hp.ne_zero hN.symm
  have hcop' : (extendIdeal O (Ideal.span {α})).absNorm.Coprime (conductor O) := hN ▸ hcop
  obtain ⟨u, hu⟩ := exists_conductorCoprime_unit O _ hq0 hcop'
  refine ⟨_, hN, (splits_iff_conductorIdealClassMap_eq_one O L hL _ hprime hq0 hcop' u hu).mpr ?_⟩
  exact conductorIdealClassMap_extend_principal O hcop α hα u hu

end Artin
end Order
end Cox
