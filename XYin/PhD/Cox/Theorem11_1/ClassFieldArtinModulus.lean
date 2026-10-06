/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldTheory

/-! # Artin kernels under modulus and field restriction

Janusz V.5.1.3 and V.5.1.5 preserve reciprocity under a finer finite
modulus and restriction to a normal subfield. The supplied maps are the
actual arithmetic Artin maps.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors IsMulCommutative
noncomputable section
namespace Cox.ClassFieldTheory

/-- Janusz V.5.1.3, p158. -/
theorem ray_le_artin_ker_of_modulus_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (m n : Ideal (𝓞 K)) (hmn : m ≤ n)
    (hUm : IsUnramifiedAway K m L)
    (φ : coprimeIdeals K n →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K n L φ)
    (ψ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hψ : IsArtinMap K m L ψ)
    (hray : raySubgroup K n ≤ φ.ker) : raySubgroup K m ≤ ψ.ker := by
  let ι : coprimeIdeals K m →* coprimeIdeals K n :=
    Subgroup.inclusion (coprimeIdeals_mono K hmn)
  have hι : ∀ u : coprimeIdeals K m,
      ((ι u : coprimeIdeals K n) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := fun u => Subgroup.coe_inclusion _ u
  have hres : IsArtinMap K m L (φ.comp ι) := by
    intro q hq hq0 hqm u hu P hP x
    have hqn : q ⊔ n = ⊤ := top_unique (hqm ▸ sup_le_sup_left hmn q)
    have hu' : (((ι u : coprimeIdeals K n) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = q := by
      rw [hι]
      exact hu
    exact hφ q hq hq0 hqn (ι u) hu' P hP x
  have heq : ψ = φ.comp ι := isArtinMap_unique K m L hUm hψ hres
  intro u hu
  have hv : ι u ∈ raySubgroup K n := by
    change ((ι u : coprimeIdeals K n) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈
      Subgroup.closure (rayGenerators K n)
    rw [hι]
    exact Subgroup.closure_mono (rayGenerators_mono K hmn) hu
  change ψ u = 1
  rw [heq]
  exact hray hv

/-- Janusz V.5.1.5, pp158–159. -/
theorem ray_le_artin_ker_subfield
    (K L E : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field E] [NumberField E] [Algebra K L] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L] [IsGalois K L] [Normal K E]
    (m : Ideal (𝓞 K)) (hUE : IsUnramifiedAway K m E)
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K m L φ)
    (ψ : coprimeIdeals K m →* (E ≃ₐ[K] E)) (hψ : IsArtinMap K m E ψ)
    (hray : raySubgroup K m ≤ φ.ker) : raySubgroup K m ≤ ψ.ker := by
  letI : IsGalois K E := {}
  have hres := isArtinMap_restrict K m L E φ hφ
  have heq : ψ = (AlgEquiv.restrictNormalHom E).comp φ :=
    isArtinMap_unique K m E hUE hψ hres
  intro u hu
  change ψ u = 1
  rw [heq, MonoidHom.comp_apply, show φ u = 1 from hray hu, map_one]

end Cox.ClassFieldTheory
