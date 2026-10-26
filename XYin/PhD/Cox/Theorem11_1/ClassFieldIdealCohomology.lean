/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicModules
import XYin.PhD.Cox.Theorem11_1.ClassFieldFiniteSupportCohomology

/-! # Actual prime exponents in Janusz V.2.1(a)

The count equivalence reuses IdealGroups' actual exponent vector and prime product.
The good-prime carrier is exactly the complement of the primes over the base modulus.
Only the ideal H1 argument is included here; invariant descent and ideal norm comparison
are separate later stages.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
open Cox.CyclicCohomology
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The actual exponent map on good ideals, restricted to exactly their possible prime support. -/
def awayExponentMap (m : Ideal (𝓞 K)) :
    awayIdealSubmodule K L m →ₗ[ℤ] (awayPrimes K L m →₀ ℤ) :=
  ((Finsupp.subtypeDomainAddMonoidHom
      (p := fun v : HeightOneSpectrum (𝓞 L) ↦ ¬m.map (algebraMap (𝓞 K) (𝓞 L)) ≤ v.asIdeal)).comp
    ((idealExponentEquiv L).toAddMonoidHom.comp
      (awayIdealSubmodule K L m).subtype.toAddMonoidHom)).toIntLinearMap

-- `[NumberField K]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Good-prime coordinates determine a good ideal because all excluded coordinates vanish. -/
theorem awayExponentMap_injective (m : Ideal (𝓞 K)) :
    Function.Injective (awayExponentMap K L m) := by
  intro I J h
  have hI : Additive.toMul (I : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ) ∈
      coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L))) := I.2
  have hJ : Additive.toMul (J : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ) ∈
      coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L))) := J.2
  apply Subtype.ext
  apply (idealExponentEquiv L).injective
  ext v
  by_cases hv : m.map (algebraMap (𝓞 K) (𝓞 L)) ≤ v.asIdeal
  · rw [idealExponentEquiv_apply, idealExponentEquiv_apply,
      (mem_coprimeIdeals_iff_count_eq_zero L _ _).mp hI v hv,
      (mem_coprimeIdeals_iff_count_eq_zero L _ _).mp hJ v hv]
  · exact DFunLike.congr_fun h ⟨v, hv⟩

-- `[NumberField K]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Extend good-prime exponents by zero and form their actual finite prime product. -/
theorem awayExponentMap_surjective (m : Ideal (𝓞 K)) :
    Function.Surjective (awayExponentMap K L m) := by
  intro e
  let e' : HeightOneSpectrum (𝓞 L) →₀ ℤ := e.mapDomain Subtype.val
  have hbad : ∀ v : HeightOneSpectrum (𝓞 L), m.map (algebraMap (𝓞 K) (𝓞 L)) ≤ v.asIdeal →
      e' v = 0 := fun v hv =>
    Finsupp.mapDomain_notin_range _ _ (by rintro ⟨w, rfl⟩; exact w.2 hv)
  have hmem : Additive.toMul ((idealExponentEquiv L).symm e') ∈
      coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L))) := by
    rw [mem_coprimeIdeals_iff_count_eq_zero]
    intro p hp
    rw [← idealExponentEquiv_apply, AddEquiv.apply_symm_apply]
    exact hbad p hp
  refine ⟨⟨(idealExponentEquiv L).symm e', hmem⟩, ?_⟩
  ext v
  change idealExponentEquiv L ((idealExponentEquiv L).symm e') v.val = e v
  rw [AddEquiv.apply_symm_apply]
  exact Finsupp.mapDomain_apply Subtype.val_injective e v

/-- The actual good-ideal exponent equivalence, with the specified forward coordinate map. -/
def awayExponentEquiv (m : Ideal (𝓞 K)) :
    awayIdealSubmodule K L m ≃ₗ[ℤ] (awayPrimes K L m →₀ ℤ) :=
  LinearEquiv.ofBijective (awayExponentMap K L m)
    ⟨awayExponentMap_injective K L m, awayExponentMap_surjective K L m⟩

/-- Every good-prime coordinate is the count of that underlying prime in the given ideal. -/
theorem awayExponentEquiv_apply (m : Ideal (𝓞 K)) (I : awayIdealSubmodule K L m)
    (v : awayPrimes K L m) :
    awayExponentEquiv K L m I v =
      FractionalIdeal.count L v.val
        ((I : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ).toMul : FractionalIdeal (𝓞 L)⁰ L) := by
  rfl

/-- The good-ideal equivalence intertwines the actual ideal and prime permutation actions. -/
theorem awayExponentEquiv_equivariant (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L)
    (I : awayIdealSubmodule K L m) :
    awayExponentEquiv K L m (awayIdealRepresentation K L m σ I) =
      Representation.ofMulAction ℤ (L ≃ₐ[K] L) (awayPrimes K L m) σ
        (awayExponentEquiv K L m I) := by
  ext v
  rw [awayExponentEquiv_apply, Representation.ofMulAction_apply, awayExponentEquiv_apply]
  change FractionalIdeal.count L v.val
    ((Additive.toMul (idealRepresentation K L σ (I : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ)) :
      (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 L)⁰ L) = _
  have hrep := idealRepresentation_apply K L σ
    (Additive.toMul (I : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ))
  rw [ofMul_toMul] at hrep
  rw [hrep, count_idealConjugation]
  rfl

variable [hGalois : IsGalois K L]
include hGalois

-- `hGalois` is included for the whole section; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Janusz V.2.1: orbitwise cumulative prime exponents solve the ideal norm-one equation. -/
theorem awayIdeal_tateOne_subsingleton (m : Ideal (𝓞 K))
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Subsingleton (tateOne (awayIdealRepresentation K L m) σ) := by
  obtain ⟨e⟩ := tateOne_equiv σ (awayIdealRepresentation K L m)
    (Representation.ofMulAction ℤ (L ≃ₐ[K] L) (awayPrimes K L m))
    (awayExponentEquiv K L m).toAddEquiv (awayExponentEquiv_equivariant K L m)
  haveI := tateOne_finsupp_subsingleton (X := awayPrimes K L m) σ hσ
  exact e.injective.subsingleton

end Cox.ClassFieldTheory
