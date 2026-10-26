/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalStabilizer
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalApproximation

/-! # Descent to the actual local Artin map

Janusz V.12.1, printed p. 187. The ray character factors through the actual surjective
ray-to-local quotient map, so the descended local character keeps its compatibility with
the global ray character, kills the chosen depth of principal units, and has the same image.
-/

open NumberField IsDedekindDomain
noncomputable section
namespace Cox.ClassFieldTheory

variable (K : Type*) [Field K] [hNF_K : NumberField K]
variable (L : Type*) [Field L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))
variable (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤)
variable (a : ℕ) (ha : 0 < a)
variable (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L))
variable (hray : raySubgroup K (v.asIdeal ^ a * m) ≤ φ.ker)
include hm hcop ha hray

/-- The admissible global ray kernel kills the kernel of the actual local quotient map. -/
theorem rayLocalQuotient_ker_le_rayArtin_ker :
    ((localRayMap K v a).comp (rayElements K m).subtype).ker ≤
      (rayArtinMap K L v m a φ).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
  have h1 : (x : Kˣ) ∈ rayElements K (v.asIdeal ^ a) := by
    rw [← localRayMap_ker K v a ha]
    exact hx
  have hinf : v.asIdeal ^ a * m = v.asIdeal ^ a ⊓ m :=
    Ideal.mul_eq_inf_of_coprime (Ideal.pow_sup_eq_top hcop)
  have h2 : (x : Kˣ) ∈ rayElements K (v.asIdeal ^ a * m) := by
    rw [hinf, rayElements_inf K _ _ (pow_ne_zero _ v.ne_bot) hm]
    exact ⟨h1, x.2⟩
  obtain ⟨y, hy, hyx⟩ := principal_mem_ray_of_mem_rayElements K _ (x : Kˣ) h2
  have he : eraseModulusFactors K (v.asIdeal ^ a * m)
      (toPrincipalIdeal (𝓞 K) K (x : Kˣ)) = y := by
    rw [← hyx]
    exact eraseModulusFactors_coprime K _ y
  rw [MonoidHom.mem_ker, rayArtinMap, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MonoidHom.comp_apply, Subgroup.coe_subtype, he]
  exact hray hy

/-- Descend the ray character through the actual surjective local quotient map. -/
def localArtinMapOfRay : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
  let q := (localRayMap K v a).comp (rayElements K m).subtype
  let ψ := q.liftOfSurjective (localRayMap_ray_restriction_surjective K v m hm hcop a)
    ⟨rayArtinMap K L v m a φ,
      rayLocalQuotient_ker_le_rayArtin_ker K L v m hm hcop a ha φ hray⟩
  ψ.comp (QuotientGroup.mk' (localFieldUnitFiltration K v a))

/-- The descended map agrees with the given ray character on the fixed global embedding. -/
theorem localArtinMapOfRay_comp_ray :
    (localArtinMapOfRay K L v m hm hcop a ha φ hray).comp
      ((completionUnitMap K v).comp (rayElements K m).subtype) =
        rayArtinMap K L v m a φ := by
  refine MonoidHom.ext fun x => ?_
  exact MonoidHom.liftOfRightInverse_comp_apply ((localRayMap K v a).comp (rayElements K m).subtype)
    (Function.surjInv (localRayMap_ray_restriction_surjective K v m hm hcop a))
    (Function.rightInverse_surjInv _)
    ⟨rayArtinMap K L v m a φ, rayLocalQuotient_ker_le_rayArtin_ker K L v m hm hcop a ha φ hray⟩ x

/-- The chosen depth-a subgroup is killed by construction through its quotient. -/
theorem localArtinMapOfRay_deep_units_le_ker :
    localFieldUnitFiltration K v a ≤
      (localArtinMapOfRay K L v m hm hcop a ha φ hray).ker := by
  intro y hy
  rw [MonoidHom.mem_ker, localArtinMapOfRay, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff y).mpr hy, map_one]

/-- Surjectivity onto the local quotient preserves the image of the original ray character. -/
theorem localArtinMapOfRay_range :
    (localArtinMapOfRay K L v m hm hcop a ha φ hray).range =
      (rayArtinMap K L v m a φ).range := by
  ext σ
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := localRayMap_ray_restriction_surjective K v m hm hcop a
      (QuotientGroup.mk' (localFieldUnitFiltration K v a) y)
    refine ⟨x, ?_⟩
    rw [← DFunLike.congr_fun (localArtinMapOfRay_comp_ray K L v m hm hcop a ha φ hray) x,
      MonoidHom.comp_apply, localArtinMapOfRay, MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact congrArg _ hx
  · rintro ⟨x, rfl⟩
    exact ⟨_, DFunLike.congr_fun (localArtinMapOfRay_comp_ray K L v m hm hcop a ha φ hray) x⟩

end Cox.ClassFieldTheory
