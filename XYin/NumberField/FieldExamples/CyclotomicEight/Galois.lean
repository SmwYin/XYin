/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.Basic

/-!
# `ℚ(ζ₈)` Galois

Automorphisms, Galois/non-Galois statements, and explicit Galois group structure.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Galois
-/

noncomputable section

open Module
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicEight

/-- The identity automorphism of `ℚ(ζ₈)`. -/
noncomputable def idAut : K ≃ₐ[ℚ] K := AlgEquiv.refl

/-- The automorphism of `ℚ(ζ₈)` sending `ζ` to `ζ³` (fixing `ℚ(√-2)`). -/
noncomputable def sigmaThree : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 3 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

/-- The automorphism of `ℚ(ζ₈)` sending `ζ` to `ζ⁵ = -ζ` (fixing `ℚ(i)`). -/
noncomputable def sigmaFive : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 5 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

/-- The automorphism of `ℚ(ζ₈)` sending `ζ` to `ζ⁷ = ζ⁻¹` (complex conjugation, fixing the
maximal totally real subfield `ℚ(√2)`). -/
noncomputable def sigmaSeven : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 7 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

/-- The automorphism `sigmaThree` sends `ζ` to `ζ³`. -/
theorem sigmaThree_apply_zeta : sigmaThree ζ = ζ ^ 3 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 3 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

/-- The automorphism `sigmaFive` sends `ζ` to `ζ⁵`. -/
theorem sigmaFive_apply_zeta : sigmaFive ζ = ζ ^ 5 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 5 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

/-- The automorphism `sigmaSeven` sends `ζ` to `ζ⁷`. -/
theorem sigmaSeven_apply_zeta : sigmaSeven ζ = ζ ^ 7 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 7 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

/-- Cyclotomic extensions are Galois: `ℚ(ζ₈)/ℚ` is a Galois extension. -/
theorem isGalois : IsGalois ℚ K :=
  IsCyclotomicExtension.isGalois {8} ℚ K

/-- The Galois group of `ℚ(ζ₈)/ℚ` is canonically `(ℤ/8)ˣ` (the cyclotomic character). -/
theorem galoisGroupStructure : Nonempty ((K ≃ₐ[ℚ] K) ≃* (ZMod 8)ˣ) :=
  ⟨IsCyclotomicExtension.autEquivPow K (Polynomial.cyclotomic.irreducible_rat (by norm_num))⟩

/-- The Galois group is the Klein four group `ℤ/2 × ℤ/2`. -/
theorem galoisGroup_klein :
    Nonempty ((K ≃ₐ[ℚ] K) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  haveI := isGalois
  have e := IsCyclotomicExtension.autEquivPow (n := 8) K
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))
  have hsq : ∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1 := fun σ => e.injective (by
    rw [map_mul, map_one]
    exact (by decide : ∀ t : (ZMod 8)ˣ, t * t = 1) _)
  have h4 : Nat.card (K ≃ₐ[ℚ] K) = 4 := by
    rw [IsGalois.card_aut_eq_finrank ℚ K, degree_eq_four]
  have hexp : Monoid.exponent (K ≃ₐ[ℚ] K) = 2 := by
    have hdvd : Monoid.exponent (K ≃ₐ[ℚ] K) ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun σ => by rw [pow_two]; exact hsq σ
    have ho : orderOf (e.symm (⟨7, 7, by decide, by decide⟩ : (ZMod 8)ˣ)) = 2 :=
      (orderOf_injective e.symm.toMonoidHom e.symm.injective _).trans
        (orderOf_eq_prime (by decide) (by decide))
    have h2 := Monoid.order_dvd_exponent (e.symm (⟨7, 7, by decide, by decide⟩ : (ZMod 8)ˣ))
    rw [ho] at h2
    exact Nat.dvd_antisymm hdvd h2
  haveI : IsKleinFour (K ≃ₐ[ℚ] K) := ⟨h4, hexp⟩
  haveI : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
    constructor
    · rw [Nat.card_prod]
      rw [show Nat.card (Multiplicative (ZMod 2)) = 2 from Nat.card_zmod 2]
    · have hdvd : Monoid.exponent (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∣ 2 :=
        Monoid.exponent_dvd_of_forall_pow_eq_one (by decide)
      have h2 :
          (2 : ℕ) ∣ Monoid.exponent (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
        have ho :
            orderOf ((Multiplicative.ofAdd (1 : ZMod 2)), (1 : Multiplicative (ZMod 2))) = 2 :=
          orderOf_eq_prime (by decide) (by decide)
        have hd := Monoid.order_dvd_exponent
          ((Multiplicative.ofAdd (1 : ZMod 2)), (1 : Multiplicative (ZMod 2)))
        rwa [ho] at hd
      exact Nat.dvd_antisymm hdvd h2
  exact IsKleinFour.nonempty_mulEquiv

/-- Every automorphism of `ℚ(ζ₈)` is an involution: `σ² = 1`. In particular the Galois
group is **not cyclic** — in contrast with `ℚ(ζ₅)`. -/
theorem aut_sq_eq_one (σ : K ≃ₐ[ℚ] K) : σ * σ = 1 := by
  have e := IsCyclotomicExtension.autEquivPow (n := 8) K
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))
  apply e.injective
  rw [map_mul, map_one]
  exact (by decide : ∀ t : (ZMod 8)ˣ, t * t = 1) _

/-- The Galois group is not cyclic (the smallest non-cyclic Galois group over `ℚ`). -/
theorem galoisGroup_not_isCyclic : ¬ IsCyclic (K ≃ₐ[ℚ] K) := by
  haveI := isGalois
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have h4 : orderOf g = 4 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, IsGalois.card_aut_eq_finrank, degree_eq_four]
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact aut_sq_eq_one g)
  rw [h4] at h2
  norm_num at h2

/-- The Galois group consists exactly of the four displayed automorphisms. -/
theorem aut_eq (σ : K ≃ₐ[ℚ] K) :
    σ = idAut ∨ σ = sigmaThree ∨ σ = sigmaFive ∨ σ = sigmaSeven := by
  have hval : ∀ t : (ZMod 8)ˣ, (t : ZMod 8).val = 1 ∨ (t : ZMod 8).val = 3 ∨
      (t : ZMod 8).val = 5 ∨ (t : ZMod 8).val = 7 := by decide
  have hspec := IsPrimitiveRoot.autToPow_spec ℚ zeta_isPrimitiveRoot σ
  have hext : ∀ τ : K ≃ₐ[ℚ] K, σ ζ = τ ζ → σ = τ := by
    intro τ h
    have hgen := (zeta_isPrimitiveRoot.powerBasis ℚ).algHom_ext
      (f := (σ : K →ₐ[ℚ] K)) (g := (τ : K →ₐ[ℚ] K))
      (by rwa [IsPrimitiveRoot.powerBasis_gen])
    exact AlgEquiv.ext fun x => AlgHom.congr_fun hgen x
  rcases hval (IsPrimitiveRoot.autToPow ℚ zeta_isPrimitiveRoot σ) with h | h | h | h <;>
    rw [h] at hspec
  · exact Or.inl (hext idAut (by rw [← hspec, pow_one]; rfl))
  · exact Or.inr (Or.inl (hext sigmaThree (by rw [← hspec, sigmaThree_apply_zeta])))
  · exact Or.inr (Or.inr (Or.inl (hext sigmaFive (by rw [← hspec, sigmaFive_apply_zeta]))))
  · exact Or.inr (Or.inr (Or.inr (hext sigmaSeven (by rw [← hspec, sigmaSeven_apply_zeta]))))


end NumberField.CyclotomicEight
