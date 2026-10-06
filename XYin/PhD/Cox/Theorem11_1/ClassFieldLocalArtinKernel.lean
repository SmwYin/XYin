/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalArtinMap
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalUnitNorm
import XYin.PhD.Cox.Theorem11_1.ClassFieldRayNormApproximation
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalNorm

/-! # Norm kernel of the actual local Artin character

Janusz V.12.2 and V.12.5, printed pp. 187–188. A single global norm satisfying the
complementary ray condition approximates any local norm, so the local Artin character kills
the local norm group; its kernel index is the local degree when its image is the
decomposition group.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise
noncomputable section
namespace Cox.ClassFieldTheory
variable (K L : Type*) [Field K] [Field L] [hNK : NumberField K]
  [hNL : NumberField L] [Algebra K L]
include hNK hNL

-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
/-- The prime-to-modulus part of a principal global norm is an actual good ideal norm. -/
theorem erase_principal_globalNorm_mem_normImage [Module.Finite (𝓞 K) (𝓞 L)]
    (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) (γ : Lˣ) :
    eraseModulusFactors K n
      (toPrincipalIdeal (𝓞 K) K (Units.map (Algebra.norm K : L →* K) γ)) ∈
        normImage K n L := by
  have h := idealUnitNorm_mem_normImage K L n
    (eraseModulusFactors L (n.map (algebraMap (𝓞 K) (𝓞 L))) (toPrincipalIdeal (𝓞 L) L γ))
  have heq : (⟨idealUnitNorm K L (eraseModulusFactors L (n.map (algebraMap (𝓞 K) (𝓞 L)))
      (toPrincipalIdeal (𝓞 L) L γ)), idealUnitNorm_coprime K L n _
        (eraseModulusFactors L _ _).property⟩ : coprimeIdeals K n) =
      eraseModulusFactors K n
        (toPrincipalIdeal (𝓞 K) K (Units.map (Algebra.norm K : L →* K) γ)) := by
    apply Subtype.ext
    change idealUnitNorm K L (eraseModulusFactors L (n.map (algebraMap (𝓞 K) (𝓞 L)))
      (toPrincipalIdeal (𝓞 L) L γ) : (FractionalIdeal (𝓞 L)⁰ L)ˣ) = _
    rw [idealUnitNorm_erase, idealUnitNorm_principal]
  rw [← heq]
  exact h

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
include hvw

/-- V.12.2 uses ray-compatible global norm approximation to kill all local norms. -/
theorem localNormGroup_le_ker_of_ray_agreement [IsAbelianGalois K L]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤) (a : ℕ)
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K (v.asIdeal ^ a * m) L φ)
    (hU : IsUnramifiedAway K (v.asIdeal ^ a * m) L)
    (θ : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L))
    (hθray : θ.comp ((completionUnitMap K v).comp (rayElements K m).subtype) =
      rayArtinMap K L v m a φ)
    (b : ℕ) (hb : localFieldUnitFiltration K v b ≤ θ.ker) :
    localNormGroup K L v w ≤ θ.ker := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ _ _
  intro x hx
  obtain ⟨β, rfl⟩ := hx
  obtain ⟨γ, hγray, hγ⟩ := exists_globalNorm_localRay_approx_preserving_ray K L v w m hm hcop β b
  have hn0 : v.asIdeal ^ a * m ≠ ⊥ := mul_ne_zero (pow_ne_zero _ v.ne_bot) hm
  have h1 : θ (completionUnitMap K v (Units.map (Algebra.norm K : L →* K) γ)) = 1 := by
    have h := DFunLike.congr_fun hθray ⟨_, hγray⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h
    change θ ((completionUnitMap K v) ((rayElements K m).subtype ⟨_, hγray⟩)) = 1
    rw [h, rayArtinMap, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact normImage_le_artin_ker K _ L hU φ hφ
      (erase_principal_globalNorm_mem_normImage K L _ hn0 γ)
  have h2 := hb hγ
  rw [MonoidHom.mem_ker, map_mul, map_inv, h1, one_mul, inv_eq_one] at h2
  rw [MonoidHom.mem_ker]
  exact h2

/-- The actual decomposition-group image gives the kernel index, independently of its norm
kernel. -/
theorem localArtin_ker_index_of_range [IsGalois K L]
    (θ : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L))
    (hθrange : θ.range = MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    letI := completionAlgebra K L v w
    θ.ker.index = Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  letI := completionAlgebra K L v w
  change θ.ker.index = Module.finrank (v.adicCompletion K) (w.adicCompletion L)
  rw [Subgroup.index_ker, hθrange]
  exact (completion_finrank_eq_card_stabilizer K L v w).symm

end Cox.ClassFieldTheory
