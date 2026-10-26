/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-! # The integral normal-basis lattice in Janusz V.3.9

These generic adapters expose the source's denominator clearing and full-rank finite-quotient steps.
-/

noncomputable section
namespace Cox.ClassFieldTheory

/-- The nonzero ideals in a discrete valuation ring are finite powers of its
maximal ideal. -/
theorem dvr_ideal_eq_maximalIdeal_pow (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = IsLocalRing.maximalIdeal R ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨n, ?_⟩
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow]

/-- A DVR with finite residue field has finite quotients by every nonzero ideal. -/
theorem dvr_hasFiniteQuotients (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)] :
    Ring.HasFiniteQuotients R := by
  refine ⟨fun {I} hI => ?_⟩
  obtain ⟨n, hn⟩ := dvr_ideal_eq_maximalIdeal_pow R I hI
  exact IsLocalRing.finite_quotient_iff.mpr ⟨n, hn.ge⟩

/-- Smith normal form reduces a full-rank lattice quotient to nonzero principal
ideal quotients of the coefficient PID. -/
theorem finite_quotient_of_full_rank (R M : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Ring.HasFiniteQuotients R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (N : Submodule R M) (hN : Module.finrank R N = Module.finrank R M) :
    Finite (M ⧸ N) := by
  let b := Module.Free.chooseBasis R M
  have e := Submodule.quotientEquivPiSpan N b hN
  haveI : ∀ i, Finite (R ⧸ Ideal.span ({Submodule.smithNormalFormCoeffs b hN i} : Set R)) :=
    fun i => Ring.HasFiniteQuotients.finiteQuotient (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Submodule.smithNormalFormCoeffs_ne_zero b hN i)
  exact Finite.of_equiv _ e.toEquiv.symm

section NormalBasis
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- Scaling every conjugate by the same nonzero base scalar preserves independence. -/
theorem linearIndependent_algEquiv_smul (a : L)
    (ha : LinearIndependent K (fun σ : L ≃ₐ[K] L => σ a))
    (c : K) (hc : c ≠ 0) :
    LinearIndependent K (fun σ : L ≃ₐ[K] L => σ (c • a)) := by
  have h := ha.units_smul (fun _ => Units.mk0 c hc)
  convert h using 1
  funext σ
  simp [map_smul, Units.smul_def]

variable (R : Type*) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
variable [Algebra R L] [IsScalarTower R K L]
variable [hFinite : FiniteDimensional K L] [hGalois : IsGalois K L]
include hFinite hGalois

/-- Clear one common base-ring denominator from all conjugates of a normal-basis
element. The integral conjugates and independence belong to the same witness. -/
theorem exists_integral_normal_basis :
    ∃ a : L, (∀ σ : L ≃ₐ[K] L, IsIntegral R (σ a)) ∧
      LinearIndependent K (fun σ : L ≃ₐ[K] L => σ a) := by
  classical
  set a := IsGalois.normalBasis K L 1 with ha
  have hind : LinearIndependent K (fun σ : L ≃ₐ[K] L => σ a) := by
    convert (IsGalois.normalBasis K L).linearIndependent using 1
    funext σ
    rw [IsGalois.normalBasis_apply]
  obtain ⟨y, hy, hint⟩ :=
    exists_integral_multiples R K (Finset.univ.image fun σ : L ≃ₐ[K] L => σ a)
  have hyK : algebraMap R K y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hy
  refine ⟨algebraMap R K y • a, fun σ => ?_, linearIndependent_algEquiv_smul K L a hind _ hyK⟩
  rw [map_smul, algebraMap_smul]
  exact hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ σ))

end NormalBasis
end Cox.ClassFieldTheory

