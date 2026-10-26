/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldSupportedCoordinates
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealTate
import XYin.PhD.Cox.Theorem11_1.ClassFieldHerbrandPermutation

/-!
# Supported prime orbits in Janusz V.2.5

The actual prime support contracts onto the base prime divisors. Its stabilizers
have order e*f, and the existing finite-permutation theorem supplies the reciprocal
orbit product in Janusz's H¹/H⁰ convention. Product reindexing is a separate layer.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise
noncomputable section
namespace Cox.ClassFieldTheory
open Cox.CyclicCohomology

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- Actual supported prime orbits are indexed by base prime divisors of the modulus. -/
theorem exists_supportedPrimeOrbitEquiv [IsGalois K L] (m : Ideal (𝓞 K)) :
    ∃ E : MulAction.orbitRel.Quotient (L ≃ₐ[K] L)
        (supportedPrimeSubMulAction K L m) ≃
        {v : HeightOneSpectrum (𝓞 K) // m ≤ v.asIdeal},
      ∀ w : supportedPrimeSubMulAction K L m,
        (E (Quotient.mk'' w)).val = w.val.under (𝓞 K) := by
  let f : supportedPrimeSubMulAction K L m → {v : HeightOneSpectrum (𝓞 K) // m ≤ v.asIdeal} :=
    fun w => ⟨w.val.under (𝓞 K), Ideal.map_le_iff_le_comap.mp w.prop⟩
  have hconst : ∀ a b : supportedPrimeSubMulAction K L m,
      a ∈ MulAction.orbit (L ≃ₐ[K] L) b → f a = f b := by
    rintro a b ⟨σ, rfl⟩
    exact Subtype.ext (primePermutation_under K L σ b.val)
  let F : MulAction.orbitRel.Quotient (L ≃ₐ[K] L) (supportedPrimeSubMulAction K L m) →
      {v : HeightOneSpectrum (𝓞 K) // m ≤ v.asIdeal} := Quotient.lift f hconst
  have hinj : Function.Injective F := by
    intro c d hcd
    induction c using Quotient.inductionOn' with | h a => ?_
    induction d using Quotient.inductionOn' with | h b => ?_
    apply Quotient.sound'
    obtain ⟨τ, hτ⟩ := prime_fiber_transitive K L b.val a.val (congrArg Subtype.val hcd).symm
    exact ⟨τ, Subtype.ext hτ⟩
  have hsurj : Function.Surjective F := by
    rintro ⟨v, hv⟩
    obtain ⟨w, rfl⟩ := primeUnder_surjective K L v
    exact ⟨Quotient.mk'' ⟨w, Ideal.map_le_iff_le_comap.mpr hv⟩, rfl⟩
  exact ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun w => rfl⟩

/-- A restricted supported-prime stabilizer has the actual base local degree. -/
theorem supportedPrime_stabilizer_card [IsGalois K L] (m : Ideal (𝓞 K))
    (w : supportedPrimeSubMulAction K L m) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) =
      (w.val.under (𝓞 K)).asIdeal.ramificationIdxIn (𝓞 L) *
        (w.val.under (𝓞 K)).asIdeal.inertiaDegIn (𝓞 L) := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI := prime_liesOver_under K L w.val
  haveI : w.val.asIdeal.IsMaximal := w.val.isMaximal
  haveI : (w.val.under (𝓞 K)).asIdeal.IsMaximal := (w.val.under (𝓞 K)).isMaximal
  letI := Ideal.Quotient.field (w.val.under (𝓞 K)).asIdeal
  letI := Ideal.Quotient.field w.val.asIdeal
  haveI : Algebra.IsSeparable (𝓞 K ⧸ (w.val.under (𝓞 K)).asIdeal) (𝓞 L ⧸ w.val.asIdeal) :=
    inferInstance
  rw [SubMulAction.stabilizer_of_subMul, primeStabilizer_eq,
    Ideal.card_stabilizer_eq _ (w.val.under (𝓞 K)).ne_bot w.val.asIdeal]

open Classical in
/-- The actual supported ideal module has the native finite-permutation orbit quotient. -/
theorem supportedIdeal_herbrandQuotient_orbits (m : Ideal (𝓞 K))
    [Fintype (supportedPrimeSubMulAction K L m)]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    herbrandQuotient (supportedIdealRepresentation K L m) σ =
      ∏ c : MulAction.orbitRel.Quotient (L ≃ₐ[K] L)
          (supportedPrimeSubMulAction K L m),
        (Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) c.out) : ℚ)⁻¹ := by
  obtain ⟨E, hE⟩ := exists_supportedExponentEquiv K L m
  exact (herbrandQuotient_congr σ _ _ E.toAddEquiv
    (supportedExponentEquiv_equivariant K L m E hE)).trans
    (herbrandQuotient_permutation_orbits (L ≃ₐ[K] L) (supportedPrimeSubMulAction K L m) σ hσ)

end Cox.ClassFieldTheory
