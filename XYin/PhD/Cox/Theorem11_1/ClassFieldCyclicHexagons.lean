/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicRows
import XYin.PhD.Cox.Theorem11_1.ClassFieldHexagon
import XYin.PhD.Cox.Theorem11_1.ClassFieldFieldUnits
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealCohomology

/-!
# Tate connectors and exact hexagons

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

/-- The first map in the middle of the first source hexagon. -/
def principalTateAlpha (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :=
  tateZeroMap (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)
    (principalImageRepresentation K L m) σ (principalImageProjection K L m)

/-- The map from the common middle group to the second source hexagon. -/
def principalTateBeta (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :=
  tateZeroMap (principalImageRepresentation K L m)
    (awayIdealRepresentation K L m) σ (principalImageInclusion K L m)

/-- The left connecting map H¹(J)→H⁰(S) in the first source row. -/
def principalFirstLeft (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :=
  oneConnecting (sUnitRepresentation K L m)
    (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)
    (principalImageRepresentation K L m) σ
    (sUnitInclusion K L m) (principalImageProjection K L m)
    (sUnitInclusion_injective K L m) (principalImageProjection_surjective K L m)
    (principal_firstRow_exact K L m)

/-- The right connecting map H⁰(J)→H¹(S) in the first source row. -/
def principalFirstRight (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :=
  zeroConnecting (sUnitRepresentation K L m)
    (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)
    (principalImageRepresentation K L m) σ
    (sUnitInclusion K L m) (principalImageProjection K L m)
    (sUnitInclusion_injective K L m) (principalImageProjection_surjective K L m)
    (principal_firstRow_exact K L m)

/-- The left connecting map H¹(V)→H⁰(J) in the second source row. -/
def principalSecondLeft (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :=
  oneConnecting (principalImageRepresentation K L m)
    (awayIdealRepresentation K L m) (principalCokernelRepresentation K L m) σ
    (principalImageInclusion K L m) (principalCokernelProjection K L m)
    (principalImageInclusion_injective K L m) (principalCokernelProjection_surjective K L m)
    (principal_secondRow_exact K L m)

/-- The right connecting map H⁰(V)→H¹(J) in the second source row. -/
def principalSecondRight (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :=
  zeroConnecting (principalImageRepresentation K L m)
    (awayIdealRepresentation K L m) (principalCokernelRepresentation K L m) σ
    (principalImageInclusion K L m) (principalCokernelProjection K L m)
    (principalImageInclusion_injective K L m) (principalCokernelProjection_surjective K L m)
    (principal_secondRow_exact K L m)

/-- Exactness at H⁰(S), for the actual first-row connecting map. -/
theorem principal_firstHexagon_A0 (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    (principalFirstLeft K L m σ).range =
      (tateZeroMap (sUnitRepresentation K L m)
        (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ
        (sUnitInclusion K L m)).ker := by
  exact hexagon_exact_A0 (sUnitRepresentation K L m)
    (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) (principalImageRepresentation K L m) σ
    (sUnitInclusion K L m) (principalImageProjection K L m) (sUnitInclusion_injective K L m)
    (principalImageProjection_surjective K L m) (principal_firstRow_exact K L m)

/-- Exactness at H⁰(Lˣ), with no finiteness of this group. -/
theorem principal_firstHexagon_B0 (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    (tateZeroMap (sUnitRepresentation K L m)
      (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ
      (sUnitInclusion K L m)).range = (principalTateAlpha K L m σ).ker := by
  exact hexagon_exact_B0 (sUnitRepresentation K L m)
    (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) (principalImageRepresentation K L m) σ
    (sUnitInclusion K L m) (principalImageProjection K L m) (sUnitInclusion_injective K L m)
    (principalImageProjection_surjective K L m) (principal_firstRow_exact K L m)

/-- Exactness at H⁰(J) in the first row. -/
theorem principal_firstHexagon_C0 (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    (principalTateAlpha K L m σ).range = (principalFirstRight K L m σ).ker := by
  exact hexagon_exact_C0 (sUnitRepresentation K L m)
    (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) (principalImageRepresentation K L m) σ
    (sUnitInclusion K L m) (principalImageProjection K L m) (sUnitInclusion_injective K L m)
    (principalImageProjection_surjective K L m) (principal_firstRow_exact K L m)

/-- Exactness at the common H⁰(J) in the second row. -/
theorem principal_secondHexagon_A0 (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    (principalSecondLeft K L m σ).range = (principalTateBeta K L m σ).ker := by
  exact hexagon_exact_A0 (principalImageRepresentation K L m)
    (awayIdealRepresentation K L m) (principalCokernelRepresentation K L m) σ
    (principalImageInclusion K L m) (principalCokernelProjection K L m)
    (principalImageInclusion_injective K L m) (principalCokernelProjection_surjective K L m)
    (principal_secondRow_exact K L m)

/-- Exactness at H⁰(I_Lᵐ), without assuming this ideal norm quotient finite. -/
theorem principal_secondHexagon_B0 (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    (principalTateBeta K L m σ).range =
      (tateZeroMap (awayIdealRepresentation K L m)
        (principalCokernelRepresentation K L m) σ
        (principalCokernelProjection K L m)).ker := by
  exact hexagon_exact_B0 (principalImageRepresentation K L m)
    (awayIdealRepresentation K L m) (principalCokernelRepresentation K L m) σ
    (principalImageInclusion K L m) (principalCokernelProjection K L m)
    (principalImageInclusion_injective K L m) (principalCokernelProjection_surjective K L m)
    (principal_secondRow_exact K L m)

/-- Exactness at H⁰(V) in the second row. -/
theorem principal_secondHexagon_C0 (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    (tateZeroMap (awayIdealRepresentation K L m)
      (principalCokernelRepresentation K L m) σ
      (principalCokernelProjection K L m)).range = (principalSecondRight K L m σ).ker := by
  exact hexagon_exact_C0 (principalImageRepresentation K L m)
    (awayIdealRepresentation K L m) (principalCokernelRepresentation K L m) σ
    (principalImageInclusion K L m) (principalCokernelProjection K L m)
    (principalImageInclusion_injective K L m) (principalCokernelProjection_surjective K L m)
    (principal_secondRow_exact K L m)

include hGalois

-- `hGalois` is included for the whole section; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Hilbert 90 makes the first shortened row begin with an injection. -/
theorem principalFirstLeft_injective (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Function.Injective (principalFirstLeft K L m σ) := by
  haveI := fieldUnits_tateOne_subsingleton K L σ hσ
  rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  have hrange := hexagon_exact_C1 (sUnitRepresentation K L m)
    (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) (principalImageRepresentation K L m) σ
    (sUnitInclusion K L m) (principalImageProjection K L m) (sUnitInclusion_injective K L m)
    (principalImageProjection_surjective K L m) (principal_firstRow_exact K L m)
  have hc' : c ∈ (tateOneMap (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)
      (principalImageRepresentation K L m) σ (principalImageProjection K L m)).range := by
    rw [hrange]
    exact hc
  obtain ⟨x, rfl⟩ := hc'
  have hx : x = 0 := Subsingleton.elim x 0
  rw [hx]
  exact AddSubgroup.mem_bot.mpr (AddMonoidHom.map_zero _)

-- `hGalois` is included for the whole section; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Hilbert 90 makes the first shortened row end with a surjection. -/
theorem principalFirstRight_surjective (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Function.Surjective (principalFirstRight K L m σ) := by
  haveI := fieldUnits_tateOne_subsingleton K L σ hσ
  rw [← AddMonoidHom.range_eq_top]
  unfold principalFirstRight
  rw [hexagon_exact_A1 (sUnitRepresentation K L m)
    (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) (principalImageRepresentation K L m) σ
    (sUnitInclusion K L m) (principalImageProjection K L m) (sUnitInclusion_injective K L m)
    (principalImageProjection_surjective K L m) (principal_firstRow_exact K L m), eq_top_iff]
  intro x _
  exact AddMonoidHom.mem_ker.mpr (Subsingleton.elim _ _)

/-- Vanishing of ideal H¹ makes the second shortened row begin with an injection. -/
theorem principalSecondLeft_injective (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Function.Injective (principalSecondLeft K L m σ) := by
  haveI := awayIdeal_tateOne_subsingleton K L m σ hσ
  rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  have hrange := hexagon_exact_C1 (principalImageRepresentation K L m)
    (awayIdealRepresentation K L m) (principalCokernelRepresentation K L m) σ
    (principalImageInclusion K L m) (principalCokernelProjection K L m)
    (principalImageInclusion_injective K L m) (principalCokernelProjection_surjective K L m)
    (principal_secondRow_exact K L m)
  have hc' : c ∈ (tateOneMap (awayIdealRepresentation K L m)
      (principalCokernelRepresentation K L m) σ (principalCokernelProjection K L m)).range := by
    rw [hrange]
    exact hc
  obtain ⟨x, rfl⟩ := hc'
  have hx : x = 0 := Subsingleton.elim x 0
  rw [hx]
  exact AddSubgroup.mem_bot.mpr (AddMonoidHom.map_zero _)

/-- Vanishing of ideal H¹ makes the second shortened row end with a surjection. -/
theorem principalSecondRight_surjective (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Function.Surjective (principalSecondRight K L m σ) := by
  haveI := awayIdeal_tateOne_subsingleton K L m σ hσ
  rw [← AddMonoidHom.range_eq_top]
  unfold principalSecondRight
  rw [hexagon_exact_A1 (principalImageRepresentation K L m)
    (awayIdealRepresentation K L m) (principalCokernelRepresentation K L m) σ
    (principalImageInclusion K L m) (principalCokernelProjection K L m)
    (principalImageInclusion_injective K L m) (principalCokernelProjection_surjective K L m)
    (principal_secondRow_exact K L m), eq_top_iff]
  intro x _
  exact AddMonoidHom.mem_ker.mpr (Subsingleton.elim _ _)

end Cox.ClassFieldTheory
