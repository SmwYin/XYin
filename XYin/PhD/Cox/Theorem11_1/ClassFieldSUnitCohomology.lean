/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnitPrincipalImage
import XYin.PhD.Cox.Theorem11_1.ClassFieldSupportedHerbrand

/-!
# The S-unit principal sequence in Janusz V.2.2

The principal map is the existing S-unit linear map into supported ideals. Its
actual range representation and the native inclusion/range restriction give the
source exact sequence. The finite supported-ideal quotient transfers the Herbrand
quotient from supported ideals to their principal image. This image differs from
the erased principal image used in V.4.2.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
open Cox.CyclicCohomology
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The existing principal S-unit map intertwines the actual restricted actions. -/
theorem sUnitPrincipalLinearMap_isIntertwining (m : Ideal (𝓞 K))
    (σ : L ≃ₐ[K] L) (u : sUnitSubmodule K L m) :
    sUnitPrincipalLinearMap K L m (sUnitRepresentation K L m σ u) =
      supportedIdealRepresentation K L m σ (sUnitPrincipalLinearMap K L m u) := by
  apply Subtype.ext
  apply Additive.toMul.injective
  change toPrincipalIdeal (𝓞 L) L (σ • Additive.toMul (u : Additive Lˣ)) =
    Additive.toMul (idealRepresentation K L σ (Additive.ofMul
      (toPrincipalIdeal (𝓞 L) L (Additive.toMul (u : Additive Lˣ)))))
  rw [idealRepresentation_apply, idealConjugation_principal]

/-- The actual existing principal linear map, packaged with its equivariance. -/
def sUnitPrincipalIntertwining (m : Ideal (𝓞 K)) :
    (sUnitRepresentation K L m).IntertwiningMap (supportedIdealRepresentation K L m) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (sUnitPrincipalLinearMap K L m) (sUnitPrincipalLinearMap_isIntertwining K L m)

/-- The library's actual representation on the principal supported-ideal range. -/
def sUnitPrincipalImageRepresentation (m : Ideal (𝓞 K)) :
    Representation ℤ (L ≃ₐ[K] L) (LinearMap.range (sUnitPrincipalLinearMap K L m)) :=
  (sUnitPrincipalIntertwining K L m).range.toRepresentation

/-- The canonical inclusion of global units into S-units, with the inherited actions. -/
def globalUnitSUnitInclusion (m : Ideal (𝓞 K)) :
    (globalUnitRepresentation K L).IntertwiningMap (sUnitRepresentation K L m) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (Submodule.inclusion (globalUnitSubmodule_le_sUnitSubmodule K L m))
    (fun _ _ ↦ rfl)

/-- The original principal map restricted to its actual range. -/
def sUnitPrincipalProjection (m : Ideal (𝓞 K)) :
    (sUnitRepresentation K L m).IntertwiningMap (sUnitPrincipalImageRepresentation K L m) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (sUnitPrincipalLinearMap K L m).rangeRestrict
    (fun σ x ↦ Subtype.ext (sUnitPrincipalLinearMap_isIntertwining K L m σ x))

/-- The native global-unit inclusion is injective. -/
theorem globalUnitSUnitInclusion_injective (m : Ideal (𝓞 K)) :
    Function.Injective (globalUnitSUnitInclusion K L m) := by
  exact Submodule.inclusion_injective (globalUnitSubmodule_le_sUnitSubmodule K L m)

/-- Range restriction makes the actual principal projection surjective. -/
theorem sUnitPrincipalProjection_surjective (m : Ideal (𝓞 K)) :
    Function.Surjective (sUnitPrincipalProjection K L m) := by
  exact LinearMap.surjective_rangeRestrict _

/-- The first source sequence has the actual global units as its principal kernel. -/
theorem sUnitPrincipal_sequence_exact (m : Ideal (𝓞 K)) :
    LinearMap.range (globalUnitSUnitInclusion K L m).toLinearMap =
      LinearMap.ker (sUnitPrincipalProjection K L m).toLinearMap := by
  change LinearMap.range (Submodule.inclusion (globalUnitSubmodule_le_sUnitSubmodule K L m)) =
    LinearMap.ker (sUnitPrincipalLinearMap K L m).rangeRestrict
  rw [Submodule.range_inclusion, LinearMap.ker_rangeRestrict, sUnitPrincipalLinearMap_ker]

/-- The last term V of the ideal sequence is finite, by ideal-class finiteness. -/
theorem principalAway_cokernel_finite (m : Ideal (𝓞 K)) :
    Finite ((awayIdealSubmodule K L m) ⧸
      LinearMap.range (principalAwayIntertwining K L m).toLinearMap) := by
  rw [principalAway_range_eq]
  haveI := erasePrincipal_range_finiteIndex L (m.map (algebraMap (𝓞 K) (𝓞 L)))
  exact Finite.of_equiv _ (Additive.ofMul.trans (additiveIntQuotientEquiv
    ((eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))).comp
      (toPrincipalIdeal (𝓞 L) L)).range).symm.toEquiv)

variable [hGalois : IsGalois K L]
include hGalois

omit hGalois in
/-- A finite supported-ideal quotient transfers Tate finiteness to the principal range. -/
theorem sUnitPrincipalImage_finiteHerbrand (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    FiniteHerbrand (sUnitPrincipalImageRepresentation K L m) σ := by
  haveI := sUnitPrincipalLinearMap_cokernel_finite K L m
  exact (finiteHerbrand_iff_subrepresentation (supportedIdealRepresentation K L m) σ
    (LinearMap.range (sUnitPrincipalLinearMap K L m))
    (fun g => (sUnitPrincipalIntertwining K L m).range.apply_mem_toSubmodule g) hσ).mp
    (supportedIdeal_finiteHerbrand K L m hm σ hσ)

omit hGalois in
/-- The principal supported-ideal image has the same Herbrand quotient as supported ideals. -/
theorem sUnitPrincipalImage_herbrandQuotient (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    herbrandQuotient (sUnitPrincipalImageRepresentation K L m) σ =
      herbrandQuotient (supportedIdealRepresentation K L m) σ := by
  haveI := sUnitPrincipalLinearMap_cokernel_finite K L m
  exact herbrandQuotient_subrepresentation (supportedIdealRepresentation K L m) σ
    (LinearMap.range (sUnitPrincipalLinearMap K L m))
    (fun g => (sUnitPrincipalIntertwining K L m).range.apply_mem_toSubmodule g) hσ
    (supportedIdeal_finiteHerbrand K L m hm σ hσ)
    (sUnitPrincipalImage_finiteHerbrand K L m hm σ hσ)

omit hGalois in
/-- The S-unit cohomology quotients in the exact hexagon are genuinely finite. -/
theorem sUnit_finiteHerbrand (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    FiniteHerbrand (sUnitRepresentation K L m) σ := by
  exact finiteHerbrand_of_first_last (globalUnitRepresentation K L) (sUnitRepresentation K L m)
    (sUnitPrincipalImageRepresentation K L m) σ (globalUnitSUnitInclusion K L m)
    (sUnitPrincipalProjection K L m) (globalUnitSUnitInclusion_injective K L m)
    (sUnitPrincipalProjection_surjective K L m) (sUnitPrincipal_sequence_exact K L m)
    (globalUnit_finiteHerbrand K L σ hσ) (sUnitPrincipalImage_finiteHerbrand K L m hm σ hσ)

omit hGalois in
/-- Janusz V.2.2: the principal-ideal image has finite index in the supported ideals,
so the two short exact sequences multiply the global-unit and supported-ideal factors. -/
theorem sUnit_herbrandQuotient_eq_mul (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    herbrandQuotient (sUnitRepresentation K L m) σ =
      herbrandQuotient (globalUnitRepresentation K L) σ *
        herbrandQuotient (supportedIdealRepresentation K L m) σ := by
  calc herbrandQuotient (sUnitRepresentation K L m) σ
      = herbrandQuotient (globalUnitRepresentation K L) σ *
          herbrandQuotient (sUnitPrincipalImageRepresentation K L m) σ :=
        herbrandQuotient_mul (globalUnitRepresentation K L) σ (sUnitRepresentation K L m)
          (sUnitPrincipalImageRepresentation K L m) (globalUnitSUnitInclusion K L m)
          (sUnitPrincipalProjection K L m) (globalUnitSUnitInclusion_injective K L m)
          (sUnitPrincipalProjection_surjective K L m) (sUnitPrincipal_sequence_exact K L m) hσ
          (globalUnit_finiteHerbrand K L σ hσ) (sUnit_finiteHerbrand K L m hm σ hσ)
          (sUnitPrincipalImage_finiteHerbrand K L m hm σ hσ)
    _ = _ := by rw [sUnitPrincipalImage_herbrandQuotient K L m hm σ hσ]

/-- Janusz V.2.5: S-unit Herbrand quotients cancel the product of local degrees. -/
theorem sUnit_herbrandQuotient [IsTotallyComplex K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    herbrandQuotient (sUnitRepresentation K L m) σ * localDegreeProduct K L m =
      (Module.finrank K L : ℚ) := by
  rw [sUnit_herbrandQuotient_eq_mul K L m hm σ hσ, globalUnit_herbrandQuotient K L σ hσ,
    mul_assoc, supportedIdeal_herbrandQuotient K L m hm σ hσ, mul_one]

end Cox.ClassFieldTheory
