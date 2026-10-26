/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldGlobalNormIndex

/-! # Janusz V.3.3–3.4: the global prime-power norm index

The valuation quotient contributes the residue degree; the relative unit index
is transported by the equality of actual norm images.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory

/-- A surjective map computes the index after adjoining its kernel, including infinite index. -/
theorem index_sup_ker_eq_index_map_of_surjective {G H : Type*} [Group G] [Group H]
    (N : Subgroup G) (f : G →* H) (hf : Function.Surjective f) :
    (N ⊔ f.ker).index = (N.map f).index := by
  rw [Subgroup.index_map, MonoidHom.range_eq_top_of_surjective f hf, Subgroup.index_top, mul_one]

/-- At depth zero, the full field-ray quotient has the global valuation-unit subgroup as kernel. -/
theorem localRayMap_zero_ker (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    (localRayMap K v 0).ker = globalValuationUnitGroup K v := by
  rw [localRayMap, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rfl

namespace LocalCyclic
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable [hGalois : IsGalois K L]
include hGalois
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]

/-- Global and local field norms have the same image in the full local field-ray quotient. -/
theorem globalNorm_fieldRay_image (t : ℕ) :
    (elementNormGroup K L).map (localRayMap K v t) =
      (localNormGroup K L v w).map (QuotientGroup.mk' (localFieldUnitFiltration K v t)) :=
  by
  apply le_antisymm
  · rintro _ ⟨a, ⟨γ, rfl⟩, rfl⟩
    exact ⟨_, global_norm_mem_localNormGroup K L v w γ, rfl⟩
  · rintro _ ⟨u, ⟨β, rfl⟩, rfl⟩
    obtain ⟨γ, hγ⟩ := exists_globalNorm_localRay_approx K L v w β t
    refine ⟨Units.map (Algebra.norm K : L →* K) γ, ⟨γ, rfl⟩, ?_⟩
    rw [localRayMap_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h := Subgroup.inv_mem _ hγ
    rw [mul_inv_rev, inv_inv, mul_comm] at h
    exact h

/-- Janusz V.3.3(a): the global valuation quotient of the norm group has index f. -/
theorem globalNorm_sup_units_index :
    (elementNormGroup K L ⊔ globalValuationUnitGroup K v).index =
      Ideal.inertiaDeg v.asIdeal w.asIdeal := by
  rw [← localRayMap_zero_ker K v,
    index_sup_ker_eq_index_map_of_surjective _ _ (localRayMap_surjective K v 0),
    globalNorm_fieldRay_image K L v w 0,
    ← index_sup_ker_eq_index_map_of_surjective _ _ (QuotientGroup.mk'_surjective _),
    QuotientGroup.ker_mk', localNormGroup_sup_units_index K L v w]

/-- Janusz V.3.4: identify the two relative indices inside their actual unit subgroups. -/
theorem globalNorm_unitRay_relIndex (t : ℕ) (ht : 0 < t) :
    ((elementNormGroup K L ⊓ globalValuationUnitGroup K v) ⊔
      rayElements K (v.asIdeal ^ t)).relIndex (globalValuationUnitGroup K v) =
        (unitNormGroup K L v w ⊔ localFieldUnitFiltration K v t).relIndex
          (localFieldUnitFiltration K v 0) := by
  have hP := primePowerRay_le_globalValuationUnitGroup K v t ht
  have hU := unitNormGroup_le_units K L v w
  have hT := localFieldUnitFiltration_le_zero K v t
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.subgroupOf_sup inf_le_right hP,
    Subgroup.inf_subgroupOf_right, ← globalUnitRayMap_ker K v t ht,
    index_sup_ker_eq_index_map_of_surjective _ _ (globalUnitRayMap_surjective K v t),
    globalNorm_unitRay_image K L v w t,
    ← index_sup_ker_eq_index_map_of_surjective _ _ (QuotientGroup.mk'_surjective _),
    QuotientGroup.ker_mk', ← Subgroup.subgroupOf_sup hU hT]

/-- Janusz V.3.3–3.4: approximation identifies the global prime-power norm/ray index
with residue degree times the corresponding local integral-unit norm/congruence index. -/
theorem global_primePower_index (t : ℕ) (ht : 0 < t) :
    (elementNormGroup K L ⊔ rayElements K (v.asIdeal ^ t)).index =
      Ideal.inertiaDeg v.asIdeal w.asIdeal *
        ((unitNormGroup K L v w ⊔ localFieldUnitFiltration K v t).relIndex
          (localFieldUnitFiltration K v 0)) := by
  rw [index_sup_factorization (elementNormGroup K L) (globalValuationUnitGroup K v)
      (rayElements K (v.asIdeal ^ t)) (primePowerRay_le_globalValuationUnitGroup K v t ht),
    globalNorm_sup_units_index K L v w, globalNorm_unitRay_relIndex K L v w t ht]

end LocalCyclic
end Cox.ClassFieldTheory
