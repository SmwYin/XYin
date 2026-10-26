/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicBaseChange
import XYin.PhD.Cox.Theorem11_1.ClassFieldResidueIndependence
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# Cyclotomic automorphisms and residue units

Janusz V.5.4, printed161/PDF172, specifies the two automorphisms by their powers on the chosen
primitive root. Rational disjointness supplies the full cyclotomic degree; the actual automorphism
equivalence then transports orders and independence. Frobenius identification remains a separate
input.
-/

namespace Cox.ClassFieldTheory.CyclotomicAutomorphisms

open IntermediateField Polynomial CyclotomicBaseChange CyclotomicIntersection

/-- Rational disjointness preserves the full degree of the root field. -/
theorem degree_of_rational_disjoint {K Ω : Type*} [Field K] [CharZero K]
    [Field Ω] [CharZero Ω] [Algebra K Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (h : (adjoin ℚ {ξ}).LinearDisjoint K) :
    Module.finrank K (adjoin K {ξ}) = n.totient := by
  haveI := CyclotomicIntersection.finiteDimensional_adjoin_root (F := ℚ) n hn ξ hξ
  have h1 := finrank_adjoin_of_linearDisjoint (L := K) (IntermediateField.adjoin ℚ {ξ}) h
  rw [adjoin_adjoin_of_tower] at h1
  rw [h1, CyclotomicIntersection.finrank_adjoin_root_rat n hn ξ hξ]

/-- A primitive root annihilates the cyclotomic polynomial over the base ring. -/
theorem aeval_cyclotomic_eq_zero {K Ω : Type*} [CommRing K] [CommRing Ω] [IsDomain Ω]
    [Algebra K Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n) :
    aeval ξ (cyclotomic n K) = 0 := by
  have h := IsPrimitiveRoot.isRoot_cyclotomic hn hξ
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
  exact h

/-- The minimal polynomial of the root divides its cyclotomic polynomial. -/
theorem minpoly_dvd_cyclotomic {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n) :
    minpoly K ξ ∣ cyclotomic n K := by
  exact minpoly.dvd K ξ (aeval_cyclotomic_eq_zero n hn ξ hξ)

/-- Full cyclotomic degree converts to equality of polynomial degrees. -/
theorem minpoly_natDegree_eq_cyclotomic {K Ω : Type*}
    [Field K] [Field Ω] [Algebra K Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (hdeg : Module.finrank K (adjoin K {ξ}) = n.totient) :
    (minpoly K ξ).natDegree = (cyclotomic n K).natDegree := by
  rw [← IntermediateField.adjoin.finrank (isIntegral_of_primitiveRoot n hn ξ hξ), hdeg,
    natDegree_cyclotomic]

/-- Full cyclotomic degree identifies the monic minimal polynomial. -/
theorem cyclotomic_eq_minpoly_of_degree {K Ω : Type*}
    [Field K] [Field Ω] [Algebra K Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (hdeg : Module.finrank K (adjoin K {ξ}) = n.totient) :
    cyclotomic n K = minpoly K ξ := by
  have hint := isIntegral_of_primitiveRoot (R := K) n hn ξ hξ
  exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic n K)
    (minpoly_dvd_cyclotomic n hn ξ hξ) (minpoly_natDegree_eq_cyclotomic n hn ξ hξ hdeg).ge

/-- Full cyclotomic degree supplies the irreducibility required for residue automorphisms. -/
theorem irreducible_cyclotomic_of_degree {K Ω : Type*}
    [Field K] [Field Ω] [Algebra K Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (hdeg : Module.finrank K (adjoin K {ξ}) = n.totient) :
    Irreducible (cyclotomic n K) := by
  rw [cyclotomic_eq_minpoly_of_degree n hn ξ hξ hdeg]
  exact minpoly.irreducible (isIntegral_of_primitiveRoot n hn ξ hξ)

/-- The actual Galois group of the embedded root field is parametrized by residue units. -/
noncomputable def residueEquiv {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (hirr : Irreducible (cyclotomic n K)) :
    Gal((adjoin K {ξ})/K) ≃* (ZMod n)ˣ := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI := rootField_isCyclotomic n hn ξ hξ (F := K)
  exact IsCyclotomicExtension.autEquivPow (adjoin K {ξ}) hirr

/-- The cyclotomic automorphism equivalence acts by powers on every root of unity. -/
theorem autEquivPow_apply_of_pow_eq {K E : Type*} [Field K] [Field E]
    [Algebra K E] (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} K E]
    (hirr : Irreducible (cyclotomic n K)) (σ : Gal(E/K))
    (x : E) (hx : x ^ n = 1) :
    σ x = x ^ (IsCyclotomicExtension.autEquivPow E hirr σ).val.val := by
  obtain ⟨i, -, rfl⟩ := (IsCyclotomicExtension.zeta_spec n K E).eq_pow_of_pow_eq_one hx
  rw [map_pow, IsCyclotomicExtension.autEquivPow_apply,
    ← (IsCyclotomicExtension.zeta_spec n K E).autToPow_spec K σ, ← pow_mul, ← pow_mul, mul_comm]
  rfl

/-- The equivalence acts by the expected power on the chosen embedded generator. -/
theorem residueEquiv_apply_root {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (hirr : Irreducible (cyclotomic n K)) (σ : Gal((adjoin K {ξ})/K)) :
    (σ ⟨ξ, subset_adjoin K {ξ} (Set.mem_singleton ξ)⟩ : Ω) =
      ξ ^ (residueEquiv n hn ξ hξ hirr σ).val.val := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI := rootField_isCyclotomic n hn ξ hξ (F := K)
  have hpow : (⟨ξ, subset_adjoin K {ξ} (Set.mem_singleton ξ)⟩ : adjoin K {ξ}) ^ n = 1 :=
    Subtype.ext (by simpa using hξ.pow_eq_one)
  have h := congrArg Subtype.val (autEquivPow_apply_of_pow_eq n hirr σ _ hpow)
  rw [h]
  rfl

/-- Every residue unit supplies the automorphism specified on the chosen generator. -/
theorem residueEquiv_symm_apply_root {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (hirr : Irreducible (cyclotomic n K)) (u : (ZMod n)ˣ) :
    ((residueEquiv n hn ξ hξ hirr).symm u
      ⟨ξ, subset_adjoin K {ξ} (Set.mem_singleton ξ)⟩ : Ω) = ξ ^ u.val.val := by
  have h := residueEquiv_apply_root n hn ξ hξ hirr ((residueEquiv n hn ξ hξ hirr).symm u)
  rwa [MulEquiv.apply_symm_apply] at h

/-- The inverse equivalence preserves the exact order of a residue unit. -/
theorem residueEquiv_symm_orderOf {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (hirr : Irreducible (cyclotomic n K)) (u : (ZMod n)ˣ) :
    orderOf ((residueEquiv n hn ξ hξ hirr).symm u) = orderOf u := by
  exact MulEquiv.orderOf_eq (residueEquiv n hn ξ hξ hirr).symm u

/-- Independent residue units give independent automorphisms. -/
theorem residueEquiv_symm_disjoint {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (hirr : Irreducible (cyclotomic n K)) (u v : (ZMod n)ˣ)
    (h : Disjoint (Subgroup.zpowers u) (Subgroup.zpowers v)) :
    Disjoint (Subgroup.zpowers ((residueEquiv n hn ξ hξ hirr).symm u))
      (Subgroup.zpowers ((residueEquiv n hn ξ hξ hirr).symm v)) := by
  exact ResidueIndependence.disjoint_zpowers_pullback (residueEquiv n hn ξ hξ hirr) u v h

/-- An automorphism is identified by its residue power on the chosen generator. -/
theorem residueEquiv_eq_iff {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (hirr : Irreducible (cyclotomic n K)) (σ : Gal((adjoin K {ξ})/K))
    (u : (ZMod n)ˣ) :
    residueEquiv n hn ξ hξ hirr σ = u ↔
      (σ ⟨ξ, subset_adjoin K {ξ} (Set.mem_singleton ξ)⟩ : Ω) = ξ ^ u.val.val := by
  constructor
  · rintro rfl
    exact residueEquiv_apply_root n hn ξ hξ hirr σ
  · intro h
    apply (residueEquiv n hn ξ hξ hirr).symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply AlgEquiv.coe_algHom_injective
    apply IntermediateField.adjoin_algHom_ext
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    apply Subtype.ext
    exact h.trans (residueEquiv_symm_apply_root n hn x hξ hirr u).symm

end Cox.ClassFieldTheory.CyclotomicAutomorphisms
