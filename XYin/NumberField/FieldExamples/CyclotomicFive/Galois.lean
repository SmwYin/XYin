/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.Basic

/-!
# `ℚ(ζ₅)` Galois

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

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicFive

/-- The identity automorphism of `ℚ(ζ₅)`. -/
noncomputable def idAut : K ≃ₐ[ℚ] K := AlgEquiv.refl

/-- The automorphism of `ℚ(ζ₅)` sending `ζ` to `ζ²`. -/
noncomputable def sigmaTwo : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 2 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

/-- The automorphism of `ℚ(ζ₅)` sending `ζ` to `ζ³`. -/
noncomputable def sigmaThree : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 3 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

/-- The automorphism of `ℚ(ζ₅)` sending `ζ` to `ζ⁴` (complex conjugation). -/
noncomputable def sigmaFour : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 4 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

/-- The automorphism `sigmaTwo` sends `ζ` to `ζ²`. -/
theorem sigmaTwo_apply_zeta : sigmaTwo ζ = ζ ^ 2 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 2 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

/-- The automorphism `sigmaThree` sends `ζ` to `ζ³`. -/
theorem sigmaThree_apply_zeta : sigmaThree ζ = ζ ^ 3 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 3 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

/-- The automorphism `sigmaFour` sends `ζ` to `ζ⁴ = ζ⁻¹`: it is complex conjugation, whose
fixed field is the maximal totally real subfield `ℚ(ζ + ζ⁻¹) = ℚ(√5)`. -/
theorem sigmaFour_apply_zeta : sigmaFour ζ = ζ ^ 4 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 4 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private theorem autEq' (σ : K ≃ₐ[ℚ] K) :
    σ = idAut ∨ σ = sigmaTwo ∨ σ = sigmaThree ∨ σ = sigmaFour := by
  have hval : ∀ t : (ZMod 5)ˣ, (t : ZMod 5).val = 1 ∨ (t : ZMod 5).val = 2 ∨
      (t : ZMod 5).val = 3 ∨ (t : ZMod 5).val = 4 := by decide
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
  · exact Or.inr (Or.inl (hext sigmaTwo (by rw [← hspec, sigmaTwo_apply_zeta])))
  · exact Or.inr (Or.inr (Or.inl (hext sigmaThree (by rw [← hspec, sigmaThree_apply_zeta]))))
  · exact Or.inr (Or.inr (Or.inr (hext sigmaFour (by rw [← hspec, sigmaFour_apply_zeta]))))

/-- Cyclotomic extensions are Galois: `ℚ(ζ₅)/ℚ` is a Galois extension. -/
theorem isGalois : IsGalois ℚ K :=
  IsCyclotomicExtension.isGalois {5} ℚ K

/-- The Galois group of `ℚ(ζ₅)/ℚ` is canonically `(ℤ/5)ˣ` (the cyclotomic character). -/
theorem galoisGroupStructure : Nonempty ((K ≃ₐ[ℚ] K) ≃* (ZMod 5)ˣ) :=
  ⟨IsCyclotomicExtension.autEquivPow K (Polynomial.cyclotomic.irreducible_rat (by norm_num))⟩

/-- The Galois group is cyclic (of order `4`) — `2` is a primitive root mod `5`. -/
theorem galoisGroup_isCyclic : IsCyclic (K ≃ₐ[ℚ] K) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have e := IsCyclotomicExtension.autEquivPow (n := 5) K
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))
  exact isCyclic_of_surjective e.symm e.symm.surjective

/-- `σ₂ : ζ ↦ ζ²` generates the Galois group: it has order `4`. -/
theorem orderOf_sigmaTwo : orderOf sigmaTwo = 4 := by
  set e : (K ≃ₐ[ℚ] K) ≃* (ZMod 5)ˣ := IsCyclotomicExtension.autEquivPow (n := 5) K
    (Polynomial.cyclotomic.irreducible_rat (by norm_num)) with hedef
  have h1 : orderOf sigmaTwo = orderOf (e sigmaTwo) :=
    (orderOf_injective e.toMonoidHom e.injective sigmaTwo).symm
  have hspec := IsPrimitiveRoot.autToPow_spec ℚ zeta_isPrimitiveRoot sigmaTwo
  rw [sigmaTwo_apply_zeta] at hspec
  have hval : ((IsPrimitiveRoot.autToPow ℚ zeta_isPrimitiveRoot sigmaTwo : (ZMod 5)ˣ) :
      ZMod 5).val = 2 := zeta_isPrimitiveRoot.pow_inj (ZMod.val_lt _) (by norm_num) hspec
  have hu : e sigmaTwo = (⟨2, 3, by decide, by decide⟩ : (ZMod 5)ˣ) := by
    ext
    change ((IsPrimitiveRoot.autToPow ℚ zeta_isPrimitiveRoot sigmaTwo : (ZMod 5)ˣ) :
      ZMod 5) = 2
    have hinv := ZMod.natCast_rightInverse (n := 5)
      ((IsPrimitiveRoot.autToPow ℚ zeta_isPrimitiveRoot sigmaTwo : (ZMod 5)ˣ) : ZMod 5)
    rw [← hinv, hval]
    rfl
  rw [h1, hu]
  have h4 : (⟨2, 3, by decide, by decide⟩ : (ZMod 5)ˣ) ^ 4 = 1 := by decide
  have h2 : (⟨2, 3, by decide, by decide⟩ : (ZMod 5)ˣ) ^ 2 ≠ 1 := by decide
  have hdvd := orderOf_dvd_of_pow_eq_one h4
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf (⟨2, 3, by decide, by decide⟩ : (ZMod 5)ˣ) ∣ 2 ^ 2 from hdvd)
  have hk2 : k = 2 := by
    by_contra hne
    exact h2 (orderOf_dvd_iff_pow_eq_one.mp (hkeq ▸ (pow_dvd_pow 2 (by omega) :
      (2 : ℕ) ^ k ∣ 2 ^ 1)))
  rw [hkeq, hk2]
  norm_num

/-- The Galois group consists exactly of the four displayed automorphisms. -/
theorem aut_eq (σ : K ≃ₐ[ℚ] K) :
    σ = idAut ∨ σ = sigmaTwo ∨ σ = sigmaThree ∨ σ = sigmaFour :=
  autEq' σ


end NumberField.CyclotomicFive
