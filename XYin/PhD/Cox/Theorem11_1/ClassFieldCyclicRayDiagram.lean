/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicDiagram
import XYin.PhD.Cox.Theorem11_1.ClassFieldQuotientDiagram

/-!
# The norm/ray quotient diagram of Janusz V.4.1

Quotienting the norm/principal map `f₀` by the ray elements gives the bottom map of
Janusz V.4.1. Combined with the Herbrand ratio of the upper row (Janusz V.4.2), this
yields `fundamental_index_factorization`.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise WithZero
noncomputable section
namespace Cox.ClassFieldTheory
open Cox.CyclicCohomology
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable [hGalois : IsGalois K L]
include hGalois

/-- The original f₀ sends a unit class to its erased principal-ideal class. -/
theorem normPrincipalMap_apply (m : Ideal (𝓞 K)) (x : Kˣ) :
    normPrincipalMap K L m (QuotientGroup.mk x) = QuotientGroup.mk
      (eraseModulusFactors K m (toPrincipalIdeal (𝓞 K) K x)) := by
  exact Classical.choose_spec (exists_normPrincipalMap K L m) x
/-- The actual ray-element image in the upper element-norm quotient. -/
def rayImageInNormQuotient (m : Ideal (𝓞 K)) :
    Subgroup (Kˣ ⧸ elementNormGroup K L) :=
  (rayElements K m).map (QuotientGroup.mk' (elementNormGroup K L))

/-- The image of the ray subgroup under f₀ is exactly the projected principal-ray subgroup. -/
theorem rayNormPrincipal_image (m : Ideal (𝓞 K)) :
    (rayImageInNormQuotient K L m).map (normPrincipalMap K L m) =
      (raySubgroup K m).map (QuotientGroup.mk' (normImage K m L)) := by
  ext z
  rw [rayImageInNormQuotient, Subgroup.map_map, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (principal_mem_ray_of_mem_rayElements K m x hx)
    refine ⟨y, hy, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      normPrincipalMap_apply, ← hyx, Subgroup.coe_subtype, eraseModulusFactors_coprime]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨α, hα, hαy⟩ := exists_rayElement_of_mem_closure K m hy
    refine ⟨α, hα, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      normPrincipalMap_apply, hαy, Subgroup.coe_subtype, eraseModulusFactors_coprime]
/-- The lower target quotient is finite by the established finite ray class group. -/
theorem rayNormPrincipal_image_finiteIndex (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    ((rayImageInNormQuotient K L m).map (normPrincipalMap K L m)).FiniteIndex := by
  rw [rayNormPrincipal_image]
  haveI := raySubgroup_finiteIndex K m hm
  rw [Subgroup.finiteIndex_iff]
  intro h
  have hdvd := Subgroup.index_map_dvd (raySubgroup K m)
    (QuotientGroup.mk'_surjective (normImage K m L))
  rw [h, zero_dvd_iff] at hdvd
  exact Subgroup.FiniteIndex.index_ne_zero hdvd
-- The section variables are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- Quotienting first by element norms identifies the source ray-image index. -/
theorem rayImageInNormQuotient_index (m : Ideal (𝓞 K)) :
    (rayImageInNormQuotient K L m).index =
      (elementNormGroup K L ⊔ rayElements K m).index := by
  rw [rayImageInNormQuotient, Subgroup.index_map, QuotientGroup.ker_mk',
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), Subgroup.index_top, mul_one,
    sup_comm]
/-- Quotienting first by ideal norms identifies the target ray-image index. -/
theorem rayNormPrincipal_image_index (m : Ideal (𝓞 K)) :
    ((rayImageInNormQuotient K L m).map (normPrincipalMap K L m)).index =
      (normRaySubgroup K m L).index := by
  rw [rayNormPrincipal_image, Subgroup.index_map, QuotientGroup.ker_mk',
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), Subgroup.index_top, mul_one,
    sup_comm, normRaySubgroup]
/-- Both element norms and ray elements map into the actual norm-and-ray ideal subgroup. -/
theorem rayNormPrincipalMap_lift_condition (m : Ideal (𝓞 K)) :
    elementNormGroup K L ⊔ rayElements K m ≤
      (normRaySubgroup K m L).comap
        ((eraseModulusFactors K m).comp (toPrincipalIdeal (𝓞 K) K)) := by
  refine sup_le ?_ ?_
  · intro x hx
    have h1 : normPrincipalMap K L m (QuotientGroup.mk x) = 1 := by
      rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]
    rw [normPrincipalMap_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_comap.mpr (le_sup_left (a := normImage K m L) h1)
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (principal_mem_ray_of_mem_rayElements K m x hx)
    refine Subgroup.mem_comap.mpr ?_
    rw [MonoidHom.comp_apply, ← hyx, Subgroup.coe_subtype, eraseModulusFactors_coprime]
    exact le_sup_right (b := raySubgroup K m) hy
/-- The actual bottom map g in V.4.1, with the book's source and target quotients. -/
def rayNormPrincipalMap (m : Ideal (𝓞 K)) :
    (Kˣ ⧸ (elementNormGroup K L ⊔ rayElements K m)) →*
      (coprimeIdeals K m ⧸ normRaySubgroup K m L) :=
  QuotientGroup.map _ _
    ((eraseModulusFactors K m).comp (toPrincipalIdeal (𝓞 K) K))
    (rayNormPrincipalMap_lift_condition K L m)

/-- The actual ray adapter is fixed on every unit representative. -/
theorem rayNormPrincipalMap_apply (m : Ideal (𝓞 K)) (x : Kˣ) :
    rayNormPrincipalMap K L m (QuotientGroup.mk x) = QuotientGroup.mk
      (eraseModulusFactors K m (toPrincipalIdeal (𝓞 K) K x)) := by
  rfl
/-- The natural left vertical projection in the book's diagram. -/
def elementNormRayProjection (m : Ideal (𝓞 K)) :
    (Kˣ ⧸ elementNormGroup K L) →*
      (Kˣ ⧸ (elementNormGroup K L ⊔ rayElements K m)) :=
  QuotientGroup.map _ _ (MonoidHom.id _) le_sup_left

/-- The natural right vertical projection in the book's diagram. -/
def idealNormRayProjection (m : Ideal (𝓞 K)) :
    (coprimeIdeals K m ⧸ normImage K m L) →*
      (coprimeIdeals K m ⧸ normRaySubgroup K m L) :=
  QuotientGroup.map _ _ (MonoidHom.id _) le_sup_left

/-- The actual upper map and actual bottom map commute with the natural projections. -/
theorem rayNormPrincipalMap_commutes (m : Ideal (𝓞 K))
    (a : Kˣ ⧸ elementNormGroup K L) :
    rayNormPrincipalMap K L m (elementNormRayProjection K L m a) =
      idealNormRayProjection K L m (normPrincipalMap K L m a) := by
  induction a using QuotientGroup.induction_on with
  | H x =>
  rw [normPrincipalMap_apply]
  rfl
/-- A ray element is in the upper kernel precisely when its un-erased principal ideal is a norm. -/
theorem normPrincipalMap_ray_ker_iff (m : Ideal (𝓞 K)) (x : Kˣ)
    (hx : x ∈ rayElements K m) :
    normPrincipalMap K L m (QuotientGroup.mk x) = 1 ↔
      x ∈ principalIdealNormElements K L m := by
  have hc := principal_mem_coprime_of_mem_rayElements K m x hx
  have he : eraseModulusFactors K m (toPrincipalIdeal (𝓞 K) K x) = ⟨_, hc⟩ :=
    eraseModulusFactors_coprime K m ⟨_, hc⟩
  rw [normPrincipalMap_apply, QuotientGroup.eq_one_iff, he, principalIdealNormElements,
    Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hy' : y = ⟨_, hc⟩ := Subtype.ext hyx
    rw [← hy']
    exact hy
/-- On the ray subgroup, element norms are principal ideal norms.
No inclusion of the two unrestricted ambient norm groups is asserted. -/
theorem rayNormElements_le_principalIdealNormElements (m : Ideal (𝓞 K)) :
    rayElements K m ⊓ elementNormGroup K L ≤
      rayElements K m ⊓ principalIdealNormElements K L m := by
  intro x hx
  refine ⟨hx.1, (normPrincipalMap_ray_ker_iff K L m x hx.1).mp ?_⟩
  rw [(QuotientGroup.eq_one_iff x).mpr hx.2, map_one]
/-- The intersection in V.4.1 is the image of the actual ray/principal-norm intersection. -/
theorem normPrincipalMap_ray_ker_image (m : Ideal (𝓞 K)) :
    (normPrincipalMap K L m).ker ⊓ rayImageInNormQuotient K L m =
      (rayElements K m ⊓ principalIdealNormElements K L m).map
        (QuotientGroup.mk' (elementNormGroup K L)) := by
  ext z
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, rayImageInNormQuotient, Subgroup.mem_map,
    Subgroup.mem_map]
  constructor
  · rintro ⟨hz, x, hx, rfl⟩
    exact ⟨x, ⟨hx, (normPrincipalMap_ray_ker_iff K L m x hx).mp hz⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hxp⟩, rfl⟩
    exact ⟨(normPrincipalMap_ray_ker_iff K L m x hx).mpr hxp, x, hx, rfl⟩
/-- The kernel intersection cardinal is exactly the independently defined n(m). -/
theorem normPrincipalMap_ray_ker_card (m : Ideal (𝓞 K)) :
    Nat.card ↥((normPrincipalMap K L m).ker ⊓ rayImageInNormQuotient K L m) =
      normCorrectionIndex K L m := by
  rw [normPrincipalMap_ray_ker_image, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk',
    normCorrectionIndex, Subgroup.relIndex, Subgroup.relIndex]
  congr 1
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨(Subgroup.mem_inf.mp x.2).1, h⟩, fun h => h.2⟩
/-- Janusz V.4.1: the quotient by ray elements contributes precisely the correction
index, as well as the element-norm congruence index. -/
theorem normRay_index_diagram (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (hU : IsUnramifiedAway K m L) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    ((normRaySubgroup K m L).index : ℚ) =
      (elementNormGroup K L ⊔ rayElements K m).index *
        ((normPrincipalMap K L m).range.index : ℚ) /
          Nat.card (normPrincipalMap K L m).ker * normCorrectionIndex K L m := by
  haveI := normPrincipalMap_ker_finite K L m hm hU σ hσ
  haveI := rayNormPrincipal_image_finiteIndex K L m hm
  have h := Cox.QuotientDiagram.quotientMap_index_ratio (normPrincipalMap K L m)
    (rayImageInNormQuotient K L m)
  rw [rayNormPrincipal_image_index, rayImageInNormQuotient_index,
    normPrincipalMap_ray_ker_card] at h
  exact h
/-- Janusz V.4.1–4.2: the two exact hexagons and the norm/ray quotient diagram give
this precise index factorization. -/
theorem fundamental_index_factorization (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (hU : IsUnramifiedAway K m L) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    ((normRaySubgroup K m L).index : ℚ) =
      herbrandQuotient (sUnitRepresentation K L m) σ *
        (elementNormGroup K L ⊔ rayElements K m).index * normCorrectionIndex K L m := by
  rw [normRay_index_diagram K L m hm hU σ hσ, mul_div_assoc,
    normPrincipalMap_index_ratio K L m hm hU σ hσ]
  ring
/-- The correction index is positive; finite cohomology excludes an infinite quotient. -/
theorem normCorrectionIndex_pos (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (hU : IsUnramifiedAway K m L) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) : 0 < normCorrectionIndex K L m := by
  rw [← normPrincipalMap_ray_ker_card K L m]
  haveI := normPrincipalMap_ker_finite K L m hm hU σ hσ
  haveI : Finite ↥((normPrincipalMap K L m).ker ⊓ rayImageInNormQuotient K L m) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  exact Nat.card_pos
end Cox.ClassFieldTheory
