/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormLocalApproximation

/-! # Global and completed valuation-zero ray quotients

Janusz V.3.3–3.4 uses K_m, the global elements that are units at one finite prime,
and its map onto the completed integer-unit ray quotient. The carriers and maps
below are actual subgroups and homomorphisms.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [hNK : NumberField K]
include hNK

/-- Every completed principal-unit subgroup consists of valuation-zero elements. -/
theorem localFieldUnitFiltration_le_zero (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    localFieldUnitFiltration K v t ≤ localFieldUnitFiltration K v 0 := by
  exact Subgroup.map_mono (by rw [localUnitFiltration_zero]; exact le_top)

/-- Janusz V.3.3: the actual global elements that are units at the selected finite prime. -/
def globalValuationUnitGroup (v : HeightOneSpectrum (𝓞 K)) : Subgroup Kˣ :=
  (localFieldUnitFiltration K v 0).comap (completionUnitMap K v)

/-- Membership in K_m is detected by the normalized completed valuation. -/
theorem mem_globalValuationUnitGroup_iff (v : HeightOneSpectrum (𝓞 K)) (u : Kˣ) :
    u ∈ globalValuationUnitGroup K v ↔
      Valued.v (completionUnitMap K v u : v.adicCompletion K) = 1 := by
  exact mem_localFieldUnitFiltration_zero_iff K v _

/-- Positive-depth global ray elements are units at the prime in their modulus. -/
theorem primePowerRay_le_globalValuationUnitGroup (v : HeightOneSpectrum (𝓞 K))
    (t : ℕ) (ht : 0 < t) :
    rayElements K (v.asIdeal ^ t) ≤ globalValuationUnitGroup K v := by
  intro u hu
  rw [← localRayMap_ker K v t ht, MonoidHom.mem_ker, localRayMap_apply,
    QuotientGroup.eq_one_iff] at hu
  exact localFieldUnitFiltration_le_zero K v t hu

/-- Restrict the completion embedding to the actual global and completed unit subgroups. -/
def globalUnitAtMap (v : HeightOneSpectrum (𝓞 K)) :
    globalValuationUnitGroup K v →* localFieldUnitFiltration K v 0 :=
  ((completionUnitMap K v).comp (globalValuationUnitGroup K v).subtype).codRestrict _
    (fun u ↦ u.property)

/-- The restricted unit map has the fixed ambient completion embedding. -/
theorem globalUnitAtMap_apply (v : HeightOneSpectrum (𝓞 K))
    (u : globalValuationUnitGroup K v) :
    (globalUnitAtMap K v u : (v.adicCompletion K)ˣ) = completionUnitMap K v u := by
  rfl

/-- The source map from K_m to the completed unit quotient by positive-depth units. -/
def globalUnitRayMap (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    globalValuationUnitGroup K v →*
      ((localFieldUnitFiltration K v 0) ⧸
        (localFieldUnitFiltration K v t).subgroupOf (localFieldUnitFiltration K v 0)) :=
  (QuotientGroup.mk' _).comp (globalUnitAtMap K v)

/-- The unit-ray homomorphism sends an element to the class of its completed image. -/
theorem globalUnitRayMap_apply (v : HeightOneSpectrum (𝓞 K)) (t : ℕ)
    (u : globalValuationUnitGroup K v) :
    globalUnitRayMap K v t u = QuotientGroup.mk (globalUnitAtMap K v u) := by
  rfl

/-- Janusz V.3.4: global elements that are units at v cover every completed unit ray class. -/
theorem globalUnitRayMap_surjective (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    Function.Surjective (globalUnitRayMap K v t) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((localFieldUnitFiltration K v t).subgroupOf (localFieldUnitFiltration K v 0)) q
  obtain ⟨u, hu⟩ := localRayMap_surjective K v t
    (QuotientGroup.mk (y : (v.adicCompletion K)ˣ))
  rw [localRayMap_apply, QuotientGroup.eq] at hu
  have hu0 : completionUnitMap K v u ∈ localFieldUnitFiltration K v 0 := by
    have h1 := localFieldUnitFiltration_le_zero K v t hu
    have h2 := (localFieldUnitFiltration K v 0).mul_mem y.2
      ((localFieldUnitFiltration K v 0).inv_mem h1)
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h2
  refine ⟨⟨u, hu0⟩, ?_⟩
  rw [globalUnitRayMap_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    Subgroup.coe_mul, Subgroup.coe_inv, globalUnitAtMap_apply]
  exact hu

/-- For positive depth, the unit-ray map has the source global ray subgroup as kernel. -/
theorem globalUnitRayMap_ker (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) (ht : 0 < t) :
    (globalUnitRayMap K v t).ker =
      (rayElements K (v.asIdeal ^ t)).subgroupOf (globalValuationUnitGroup K v) := by
  ext x
  rw [MonoidHom.mem_ker, globalUnitRayMap_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, globalUnitAtMap_apply,
    ← localRayMap_ker K v t ht, MonoidHom.mem_ker, localRayMap_apply, QuotientGroup.eq_one_iff]

/-- The global and completed valuation-zero ray quotients are the same quotient group. -/
theorem globalUnitRay_quotient_equiv (v : HeightOneSpectrum (𝓞 K))
    (t : ℕ) (ht : 0 < t) :
    Nonempty (((globalValuationUnitGroup K v) ⧸
      (rayElements K (v.asIdeal ^ t)).subgroupOf (globalValuationUnitGroup K v)) ≃*
        ((localFieldUnitFiltration K v 0) ⧸
          (localFieldUnitFiltration K v t).subgroupOf (localFieldUnitFiltration K v 0))) := by
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (globalUnitRayMap_ker K v t ht).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (globalUnitRayMap_surjective K v t))⟩

end Cox.ClassFieldTheory
