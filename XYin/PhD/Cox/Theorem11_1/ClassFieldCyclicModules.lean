/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealAction
import XYin.PhD.Cox.Theorem11_1.ClassFieldCohomology
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnits
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnitLatticeCohomology
import XYin.PhD.Cox.Theorem11_1.ClassFieldGlobalUnitHerbrand
import XYin.PhD.Cox.Theorem11_1.ClassFieldSupportedFinite

/-!
# Janusz's cyclic fundamental equality

The Herbrand quotient uses Janusz's convention H¹/H⁰_Tate. The Tate groups in `ClassFieldCohomology`
are the actual kernel/image quotients of the norm and difference operators. Their
comparison with the existing positive-degree cyclic cohomology API is explicit;
ordinary H⁰ is not substituted for the Tate denominator.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise WithZero

noncomputable section


namespace Cox.ClassFieldTheory

open Cox.CyclicCohomology

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- Actual element norms, as a subgroup of nonzero base-field elements. -/
def elementNormGroup : Subgroup Kˣ :=
  (Units.map (Algebra.norm K : L →* K)).range

/-- S-units for the upstairs primes belonging to an extended base modulus. -/
def sUnitsAtModulus (m : Ideal (𝓞 K)) : Subgroup Lˣ :=
  (modulusSupportedIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))).comap
    (toPrincipalIdeal (𝓞 L) L)

/-- The additive integral submodule of the natural field-unit representation. -/
def sUnitSubmodule (m : Ideal (𝓞 K)) : Submodule ℤ (Additive Lˣ) :=
  (sUnitsAtModulus K L m).toAddSubgroup.toIntSubmodule



/-- The integral ideal submodule supported above the base modulus. -/
def supportedIdealSubmodule (m : Ideal (𝓞 K)) :
    Submodule ℤ (Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ) :=
  (modulusSupportedIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))).toAddSubgroup.toIntSubmodule

/-- Prime counts of a conjugate ideal are the counts at the inverse-conjugate prime. -/
theorem count_idealConjugation (σ : L ≃ₐ[K] L) (I : (FractionalIdeal (𝓞 L)⁰ L)ˣ)
    (p : HeightOneSpectrum (𝓞 L)) :
    FractionalIdeal.count L p (idealConjugation K L σ I : FractionalIdeal (𝓞 L)⁰ L) =
      FractionalIdeal.count L (σ⁻¹ • p) (I : FractionalIdeal (𝓞 L)⁰ L) := by
  have h := idealExponentVector_conjugation K L σ I (σ⁻¹ • p)
  rwa [smul_inv_smul, idealExponentVector_apply, idealExponentVector_apply] at h

/-- Conjugation preserves the ideals supported above a base modulus. -/
theorem idealConjugation_mem_modulusSupportedIdeals (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L)
    (I : (FractionalIdeal (𝓞 L)⁰ L)ˣ)
    (hI : I ∈ modulusSupportedIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))) :
    idealConjugation K L σ I ∈ modulusSupportedIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L))) := by
  rw [mem_modulusSupportedIdeals_iff_count_eq_zero] at hI ⊢
  intro p hp
  rw [count_idealConjugation]
  exact hI _ ((awayPrime_conjugation K L m σ (σ⁻¹ • p)).mp (by rwa [smul_inv_smul]))

/-- Conjugation preserves the ideals prime to an extended base modulus. -/
theorem idealConjugation_mem_coprimeIdeals (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L)
    (I : (FractionalIdeal (𝓞 L)⁰ L)ˣ)
    (hI : I ∈ coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))) :
    idealConjugation K L σ I ∈ coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L))) := by
  rw [mem_coprimeIdeals_iff_count_eq_zero] at hI ⊢
  intro p hp
  rw [count_idealConjugation]
  refine hI _ (not_not.mp fun h => ?_)
  exact (awayPrime_conjugation K L m σ (σ⁻¹ • p)).mpr h (by rwa [smul_inv_smul])

/-- A support consisting of all primes above a base support is stable under conjugation. -/
theorem supportedIdealSubmodule_stable (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    supportedIdealSubmodule K L m ≤
      (supportedIdealSubmodule K L m).comap (idealRepresentation K L σ) := by
  intro x hx
  change Additive.toMul (idealRepresentation K L σ x) ∈
    modulusSupportedIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))
  have hrep := idealRepresentation_apply K L σ (Additive.toMul x)
  rw [ofMul_toMul] at hrep
  rw [hrep]
  exact idealConjugation_mem_modulusSupportedIdeals K L m σ _ hx

/-- The representation on the actual finite-support ideal group. -/
def supportedIdealRepresentation (m : Ideal (𝓞 K)) :
    Representation ℤ (L ≃ₐ[K] L) (supportedIdealSubmodule K L m) :=
  (idealRepresentation K L).subrepresentation (supportedIdealSubmodule K L m)
    (supportedIdealSubmodule_stable K L m)

/-- The integral submodule of fractional ideals avoiding the extended modulus. -/
def awayIdealSubmodule (m : Ideal (𝓞 K)) :
    Submodule ℤ (Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ) :=
  (coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))).toAddSubgroup.toIntSubmodule

/-- Galois conjugation preserves the prime-to-base-modulus condition. -/
theorem awayIdealSubmodule_stable (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    awayIdealSubmodule K L m ≤
      (awayIdealSubmodule K L m).comap (idealRepresentation K L σ) := by
  intro x hx
  change Additive.toMul (idealRepresentation K L σ x) ∈
    coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))
  have hrep := idealRepresentation_apply K L σ (Additive.toMul x)
  rw [ofMul_toMul] at hrep
  rw [hrep]
  exact idealConjugation_mem_coprimeIdeals K L m σ _ hx

/-- The representation on the actual upstairs prime-to-modulus fractional ideals. -/
def awayIdealRepresentation (m : Ideal (𝓞 K)) :
    Representation ℤ (L ≃ₐ[K] L) (awayIdealSubmodule K L m) :=
  (idealRepresentation K L).subrepresentation (awayIdealSubmodule K L m)
    (awayIdealSubmodule_stable K L m)

/-- Conjugation over K preserves the support above a base modulus. -/
theorem sUnitSubmodule_stable (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    sUnitSubmodule K L m ≤ (sUnitSubmodule K L m).comap
      ((Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ) := by
  intro x hx
  change toPrincipalIdeal (𝓞 L) L (σ • Additive.toMul x) ∈
    modulusSupportedIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))
  rw [← idealConjugation_principal]
  exact idealConjugation_mem_modulusSupportedIdeals K L m σ _ hx

/-- The actual S-unit representation used in both exact hexagons in Janusz V.4.2. -/
def sUnitRepresentation (m : Ideal (𝓞 K)) :
    Representation ℤ (L ≃ₐ[K] L) (sUnitSubmodule K L m) :=
  (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ).subrepresentation
    (sUnitSubmodule K L m) (sUnitSubmodule_stable K L m)

/-- Conjugation commutes with the chosen erasure of primes above a base modulus. -/
theorem idealConjugation_eraseModulusFactors (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L)
    (I : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    idealConjugation K L σ
        (eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L))) I :
          (FractionalIdeal (𝓞 L)⁰ L)ˣ) =
      (eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))
        (idealConjugation K L σ I) : (FractionalIdeal (𝓞 L)⁰ L)ˣ) := by
  set j := eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))
  have hjU : j (idealConjugation K L σ (I * (j I : (FractionalIdeal (𝓞 L)⁰ L)ˣ)⁻¹)) = 1 :=
    eraseModulusFactors_supported L _ _ (idealConjugation_mem_modulusSupportedIdeals K L m σ _
      (eraseModulusFactors_spec L _ I))
  have hcop : idealConjugation K L σ (j I : (FractionalIdeal (𝓞 L)⁰ L)ˣ) ∈
      coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L))) :=
    idealConjugation_mem_coprimeIdeals K L m σ _ (j I).2
  have hjc := eraseModulusFactors_coprime L _ ⟨_, hcop⟩
  have h1 : idealConjugation K L σ I = idealConjugation K L σ
      (I * (j I : (FractionalIdeal (𝓞 L)⁰ L)ˣ)⁻¹) * idealConjugation K L σ (j I) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [h1, map_mul, hjU, one_mul, hjc]

/-- The principal-ideal map followed by prime-factor erasure is equivariant. -/
theorem exists_principalAwayIntertwining (m : Ideal (𝓞 K)) :
    ∃ f : (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ).IntertwiningMap
        (awayIdealRepresentation K L m),
      ∀ x : Lˣ, Additive.toMul (f (Additive.ofMul x) :
          Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ) =
        (eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))
          (toPrincipalIdeal (𝓞 L) L x) : (FractionalIdeal (𝓞 L)⁰ L)ˣ) := by
  let ψ : Lˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
    (coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))).subtype.comp
      ((eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))).comp (toPrincipalIdeal (𝓞 L) L))
  let φ : Additive Lˣ →ₗ[ℤ] awayIdealSubmodule K L m :=
    LinearMap.codRestrict (awayIdealSubmodule K L m) ψ.toAdditive.toIntLinearMap
      (fun x => (eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))
        (toPrincipalIdeal (𝓞 L) L (Additive.toMul x))).2)
  refine ⟨LinearMap.intertwiningMap_of_isIntertwiningMap _ _ φ ?_, fun x => rfl⟩
  intro σ x
  apply Subtype.ext
  apply Additive.toMul.injective
  change (eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))
      (toPrincipalIdeal (𝓞 L) L (σ • Additive.toMul x)) : (FractionalIdeal (𝓞 L)⁰ L)ˣ) =
    Additive.toMul (idealRepresentation K L σ (Additive.ofMul
      (eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))
        (toPrincipalIdeal (𝓞 L) L (Additive.toMul x)) : (FractionalIdeal (𝓞 L)⁰ L)ˣ)))
  rw [idealRepresentation_apply, idealConjugation_eraseModulusFactors, idealConjugation_principal]

/-- The source's equivariant map f from field units to ideals prime to the modulus. -/
def principalAwayIntertwining (m : Ideal (𝓞 K)) :
    (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ).IntertwiningMap
      (awayIdealRepresentation K L m) :=
  Classical.choose (exists_principalAwayIntertwining K L m)

/-- The first exact sequence of V.4.2 has the actual S-unit submodule as kernel. -/
theorem principalAway_ker (m : Ideal (𝓞 K)) :
    LinearMap.ker (principalAwayIntertwining K L m).toLinearMap =
      sUnitSubmodule K L m := by
  have hspec : ∀ x : Lˣ, Additive.toMul ((principalAwayIntertwining K L m (Additive.ofMul x) :
      awayIdealSubmodule K L m) : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ) =
      (eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L))) (toPrincipalIdeal (𝓞 L) L x) :
        (FractionalIdeal (𝓞 L)⁰ L)ˣ) :=
    Classical.choose_spec (exists_principalAwayIntertwining K L m)
  ext x
  have hx := hspec (Additive.toMul x)
  rw [ofMul_toMul] at hx
  change principalAwayIntertwining K L m x = 0 ↔ toPrincipalIdeal (𝓞 L) L (Additive.toMul x) ∈
    modulusSupportedIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))
  rw [← eraseModulusFactors_eq_one_iff, ← Submodule.coe_eq_zero, ← toMul_eq_one, hx,
    OneMemClass.coe_eq_one]

variable [hGalois : IsGalois K L]
include hGalois

open scoped Classical in
/-- The finite prime factors appearing in the source's two reciprocal products. -/
noncomputable def localDegreeProduct (m : Ideal (𝓞 K)) : ℕ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    if m ≤ v.asIdeal then v.asIdeal.ramificationIdxIn (𝓞 L) *
      v.asIdeal.inertiaDegIn (𝓞 L) else 1

omit hGalois in
/-- Finite support gives a finitely generated ideal module and finite Tate groups. -/
theorem supportedIdeal_finiteHerbrand (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    FiniteHerbrand (supportedIdealRepresentation K L m) σ := by
  have hM : m.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hm
  haveI : Module.Finite ℤ (supportedIdealSubmodule K L m) := modulusSupported_moduleFinite L _ hM
  exact finiteHerbrand_of_moduleFinite (supportedIdealRepresentation K L m) σ hσ


end Cox.ClassFieldTheory
