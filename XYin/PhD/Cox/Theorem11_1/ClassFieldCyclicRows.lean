/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnitCohomology
import XYin.PhD.Cox.Theorem11_1.ClassFieldCohomology

/-!
# The two actual principal-away exact rows

The Herbrand quotient uses Janusz's convention H¹/H⁰_Tate.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise WithZero

noncomputable section

namespace Cox.ClassFieldTheory

open Cox.CyclicCohomology

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

variable [hGalois : IsGalois K L]
include hGalois

omit hGalois

/-- The actual principal-away image J=f(Lˣ), as a submodule of I_Lᵐ. -/
def principalImageSubmodule (m : Ideal (𝓞 K)) :
    Submodule ℤ (awayIdealSubmodule K L m) :=
  LinearMap.range (principalAwayIntertwining K L m).toLinearMap

/-- The image of an equivariant map is stable under the Galois action. -/
theorem principalImageSubmodule_stable (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    principalImageSubmodule K L m ≤ (principalImageSubmodule K L m).comap
      (awayIdealRepresentation K L m σ) := by
  exact (principalAwayIntertwining K L m).range.apply_mem_toSubmodule σ

/-- The inherited action on the literal principal-away image. -/
def principalImageRepresentation (m : Ideal (𝓞 K)) :
    Representation ℤ (L ≃ₐ[K] L) (principalImageSubmodule K L m) :=
  (awayIdealRepresentation K L m).subrepresentation (principalImageSubmodule K L m)
    (principalImageSubmodule_stable K L m)

/-- Range restriction of f commutes with the action on J=f(Lˣ). -/
theorem principalImageProjection_isIntertwining (m : Ideal (𝓞 K))
    (σ : L ≃ₐ[K] L) (x : Additive Lˣ) :
    (principalAwayIntertwining K L m).toLinearMap.rangeRestrict
      (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ σ x) =
    principalImageRepresentation K L m σ
      ((principalAwayIntertwining K L m).toLinearMap.rangeRestrict x) := by
  apply Subtype.ext
  exact (principalAwayIntertwining K L m).isIntertwining _ _ σ x

/-- The actual surjective first-row map Lˣ→J. -/
def principalImageProjection (m : Ideal (𝓞 K)) :
    (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ).IntertwiningMap
      (principalImageRepresentation K L m) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (principalAwayIntertwining K L m).toLinearMap.rangeRestrict
    (principalImageProjection_isIntertwining K L m)

/-- The actual first-row inclusion L^S→Lˣ. -/
def sUnitInclusion (m : Ideal (𝓞 K)) :
    (sUnitRepresentation K L m).IntertwiningMap
      (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) :=
  submoduleIntertwining _ (sUnitSubmodule K L m) (sUnitSubmodule_stable K L m)

/-- The actual second-row inclusion J→I_Lᵐ. -/
def principalImageInclusion (m : Ideal (𝓞 K)) :
    (principalImageRepresentation K L m).IntertwiningMap (awayIdealRepresentation K L m) :=
  submoduleIntertwining _ (principalImageSubmodule K L m)
    (principalImageSubmodule_stable K L m)

/-- The quotient action on V=I_Lᵐ/f(Lˣ), the finite last term of the source sequence. -/
def principalCokernelRepresentation (m : Ideal (𝓞 K)) :
    Representation ℤ (L ≃ₐ[K] L)
      ((awayIdealSubmodule K L m) ⧸ principalImageSubmodule K L m) :=
  (awayIdealRepresentation K L m).quotient (principalImageSubmodule K L m)
    (principalImageSubmodule_stable K L m)

/-- The actual second-row projection I_Lᵐ→V. -/
def principalCokernelProjection (m : Ideal (𝓞 K)) :
    (awayIdealRepresentation K L m).IntertwiningMap (principalCokernelRepresentation K L m) :=
  quotientIntertwining _ (principalImageSubmodule K L m)
    (principalImageSubmodule_stable K L m)

/-- The first row begins with an injective inclusion. -/
theorem sUnitInclusion_injective (m : Ideal (𝓞 K)) :
    Function.Injective (sUnitInclusion K L m) := by
  exact submoduleIntertwining_injective _ (sUnitSubmodule K L m) (sUnitSubmodule_stable K L m)

/-- The first row ends with the surjection onto the actual image. -/
theorem principalImageProjection_surjective (m : Ideal (𝓞 K)) :
    Function.Surjective (principalImageProjection K L m) := by
  exact LinearMap.surjective_rangeRestrict _

/-- Exactness of 0→L^S→Lˣ→J→0, using the previously identified principal-away kernel. -/
theorem principal_firstRow_exact (m : Ideal (𝓞 K)) :
    LinearMap.range (sUnitInclusion K L m).toLinearMap =
      LinearMap.ker (principalImageProjection K L m).toLinearMap := by
  change LinearMap.range (sUnitSubmodule K L m).subtype =
    LinearMap.ker (principalAwayIntertwining K L m).toLinearMap.rangeRestrict
  rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict, principalAway_ker]

/-- The second row starts with the literal injective image inclusion. -/
theorem principalImageInclusion_injective (m : Ideal (𝓞 K)) :
    Function.Injective (principalImageInclusion K L m) := by
  exact submoduleIntertwining_injective _ (principalImageSubmodule K L m)
    (principalImageSubmodule_stable K L m)

/-- The second row ends with its quotient projection. -/
theorem principalCokernelProjection_surjective (m : Ideal (𝓞 K)) :
    Function.Surjective (principalCokernelProjection K L m) := by
  exact quotientIntertwining_surjective _ (principalImageSubmodule K L m)
    (principalImageSubmodule_stable K L m)

/-- Exactness of 0→J→I_Lᵐ→V→0, with the actual quotient V. -/
theorem principal_secondRow_exact (m : Ideal (𝓞 K)) :
    LinearMap.range (principalImageInclusion K L m).toLinearMap =
      LinearMap.ker (principalCokernelProjection K L m).toLinearMap := by
  exact submodule_sequence_exact _ (principalImageSubmodule K L m)
    (principalImageSubmodule_stable K L m)

end Cox.ClassFieldTheory
