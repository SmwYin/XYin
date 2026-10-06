/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealDescent

/-! # The principal-extension square in Janusz V.4

These four adapters identify the actual principal-away map under the book's
extension of base ideals. No Galois or unramified hypothesis enters this layer.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
/-- Extension of the principal ideal agrees with the specified field embedding. -/
theorem idealUnitExtension_principal (x : Kˣ) :
    idealUnitExtension K L (toPrincipalIdeal (𝓞 K) K x) =
      toPrincipalIdeal (𝓞 L) L (fieldUnitEmbedding K L x) := by
  apply Units.ext
  rw [idealUnitExtension, Units.coe_map, coe_toPrincipalIdeal, coe_toPrincipalIdeal]
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, fieldUnitEmbedding, Units.coe_map]
  rw [FractionalIdeal.coe_extendedHom_eq_span, FractionalIdeal.coe_spanSingleton]
  have himg : (algebraMap K L '' (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) : Set K)) =
      (Submodule.span (𝓞 K) {algebraMap K L (x : K)} : Set L) := by
    ext y
    simp only [Set.mem_image, SetLike.mem_coe, FractionalIdeal.mem_spanSingleton,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      refine ⟨a, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply (𝓞 K) K L a]
    · rintro ⟨a, rfl⟩
      refine ⟨a • (x : K), ⟨a, rfl⟩, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply (𝓞 K) K L a]
  rw [himg, Submodule.span_span_of_tower]
/-- Extending a supported ideal preserves support above the base modulus. -/
theorem idealUnitExtension_supported (m : Ideal (𝓞 K))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hI : I ∈ modulusSupportedIdeals K m) :
    idealUnitExtension K L I ∈
      modulusSupportedIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L))) := by
  rw [mem_modulusSupportedIdeals_iff_count_eq_zero] at hI ⊢
  intro p hp
  rw [idealExtension_count, hI _ ((awayPrime_iff_under K L m p).mp hp), mul_zero]
/-- The actual extension map commutes with deletion of modulus factors. -/
theorem idealUnitExtension_erase (m : Ideal (𝓞 K))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    idealUnitExtension K L (eraseModulusFactors K m I) =
      (eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))
        (idealUnitExtension K L I) : (FractionalIdeal (𝓞 L)⁰ L)ˣ) := by
  have hU := eraseModulusFactors_spec K m I
  have h1 : eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))
      (idealUnitExtension K L (I * (eraseModulusFactors K m I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹)) =
        1 :=
    eraseModulusFactors_supported L _ _ (idealUnitExtension_supported K L m _ hU)
  have hcop := idealUnitExtension_coprime K L m (eraseModulusFactors K m I)
  have h2 : eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))
      (idealUnitExtension K L (eraseModulusFactors K m I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) =
        ⟨_, hcop⟩ :=
    eraseModulusFactors_coprime L _ ⟨_, hcop⟩
  have hI : idealUnitExtension K L I =
      idealUnitExtension K L (I * (eraseModulusFactors K m I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹) *
        idealUnitExtension K L (eraseModulusFactors K m I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [hI, map_mul (eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))), h1, one_mul, h2]
/-- The existing principal-away map on a base unit is the extension of its erased principal
ideal. -/
theorem principalAway_base_unit (m : Ideal (𝓞 K)) (x : Kˣ) :
    principalAwayIntertwining K L m (Additive.ofMul (fieldUnitEmbedding K L x)) =
      awayIdealExtension K L m (Additive.ofMul
        (eraseModulusFactors K m (toPrincipalIdeal (𝓞 K) K x))) := by
  have hspec : ∀ y : Lˣ, Additive.toMul ((principalAwayIntertwining K L m (Additive.ofMul y) :
      awayIdealSubmodule K L m) : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ) =
      (eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L))) (toPrincipalIdeal (𝓞 L) L y) :
        (FractionalIdeal (𝓞 L)⁰ L)ˣ) :=
    Classical.choose_spec (exists_principalAwayIntertwining K L m)
  apply Subtype.ext
  apply Additive.toMul.injective
  rw [hspec, ← idealUnitExtension_principal, ← idealUnitExtension_erase]
  rfl

end Cox.ClassFieldTheory
