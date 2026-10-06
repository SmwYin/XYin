/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicModules
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# The actual supported-prime coordinates

Janusz V.2.5 identifies the supported ideal group with the free abelian group on
its actual prime support. The native restricted action and count coordinates below
expose that representation before the separate orbit and local-degree calculation.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The actual primes dividing the extended base modulus, with the native restricted action. -/
def supportedPrimeSubMulAction (m : Ideal (𝓞 K)) :
    SubMulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L)) where
  carrier := {v | m.map (algebraMap (𝓞 K) (𝓞 L)) ≤ v.asIdeal}
  smul_mem' σ v hv := by
    by_contra h
    exact ((awayPrime_conjugation K L m σ v).mp h) hv

/-- Membership exposes exactly the divisibility condition of the actual extended modulus. -/
@[simp] theorem mem_supportedPrimeSubMulAction (m : Ideal (𝓞 K))
    (v : HeightOneSpectrum (𝓞 L)) :
    v ∈ supportedPrimeSubMulAction K L m ↔
      m.map (algebraMap (𝓞 K) (𝓞 L)) ≤ v.asIdeal := by
  exact Iff.rfl

/-- The native restricted action has the same underlying conjugate prime. -/
theorem supportedPrimeSubMulAction_val_smul (m : Ideal (𝓞 K))
    (σ : L ≃ₐ[K] L) (v : supportedPrimeSubMulAction K L m) :
    ((σ • v : supportedPrimeSubMulAction K L m) : HeightOneSpectrum (𝓞 L)) =
      σ • (v : HeightOneSpectrum (𝓞 L)) := by
  rfl

/-- Zero modulus permits every prime in the support carrier. -/
@[simp] theorem supportedPrimeSubMulAction_bot :
    supportedPrimeSubMulAction K L ⊥ = ⊤ := by
  ext v
  exact iff_of_true (by rw [mem_supportedPrimeSubMulAction, Ideal.map_bot]; exact bot_le) trivial

/-- Unit modulus permits no prime in the support carrier. -/
@[simp] theorem supportedPrimeSubMulAction_top :
    supportedPrimeSubMulAction K L ⊤ = ⊥ := by
  ext v
  refine iff_of_false ?_ id
  rw [mem_supportedPrimeSubMulAction, Ideal.map_top, top_le_iff]
  exact v.isPrime.ne_top

/-- One actual exponent equivalence with its prime-count representative formula. -/
theorem exists_supportedExponentEquiv (m : Ideal (𝓞 K)) :
    ∃ E : supportedIdealSubmodule K L m ≃ₗ[ℤ]
        (supportedPrimeSubMulAction K L m →₀ ℤ),
      ∀ (I : supportedIdealSubmodule K L m) (v : supportedPrimeSubMulAction K L m),
        E I v = FractionalIdeal.count L v.val I.val.toMul := by
  have hS : supportedIdealSubmodule K L m =
      (Finsupp.supported ℤ ℤ
        (supportedPrimeSubMulAction K L m : Set (HeightOneSpectrum (𝓞 L)))).comap
        (idealExponentEquiv L).toIntLinearEquiv.toLinearMap := by
    ext x
    rw [Submodule.mem_comap, Finsupp.mem_supported']
    change Additive.toMul x ∈ modulusSupportedIdeals L _ ↔ _
    rw [mem_modulusSupportedIdeals_iff_count_eq_zero]
    rfl
  exact ⟨(LinearEquiv.ofEq _ _ hS).trans
    (((idealExponentEquiv L).toIntLinearEquiv.ofSubmodule' _).trans
      (Finsupp.supportedEquivFinsupp _)), fun I v => rfl⟩

/-- The prime-count formula forces the equivalence to intertwine the actual actions. -/
theorem supportedExponentEquiv_equivariant (m : Ideal (𝓞 K))
    (E : supportedIdealSubmodule K L m ≃ₗ[ℤ]
      (supportedPrimeSubMulAction K L m →₀ ℤ))
    (hE : ∀ (I : supportedIdealSubmodule K L m) (v : supportedPrimeSubMulAction K L m),
      E I v = FractionalIdeal.count L v.val I.val.toMul)
    (σ : L ≃ₐ[K] L) (I : supportedIdealSubmodule K L m) :
    E (supportedIdealRepresentation K L m σ I) =
      Representation.ofMulAction ℤ (L ≃ₐ[K] L)
        (supportedPrimeSubMulAction K L m) σ (E I) := by
  ext v
  rw [hE, Representation.ofMulAction_apply, hE]
  change FractionalIdeal.count L v.val
    ((Additive.toMul (idealRepresentation K L σ (I : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ)) :
      (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 L)⁰ L) = _
  have hrep := idealRepresentation_apply K L σ
    (Additive.toMul (I : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ))
  rw [ofMul_toMul] at hrep
  rw [hrep, count_idealConjugation]
  rfl

end Cox.ClassFieldTheory
