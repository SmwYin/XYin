/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalIndex

/-! # Unramified local unit norms

Janusz V.12.7 (printed p. 189, PDF p. 200) extends V.3.11 from cyclic to abelian
extensions by induction. The norm image uses actual depth-zero local integer units.
-/

open NumberField IsDedekindDomain
noncomputable section
namespace Cox.ClassFieldTheory

section Tower
variable (K E L : Type*) [Field K] [Field E] [Field L]
variable [hNF_K : NumberField K] [hNF_E : NumberField E] [hNF_L : NumberField L]
variable [Algebra K E] [Algebra E L] [Algebra K L] [hTower : IsScalarTower K E L]
variable (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
variable (w : HeightOneSpectrum (𝓞 L))
variable [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]
variable [w.asIdeal.LiesOver v.asIdeal]
include hTower hNF_K hNF_E hNF_L

-- The section instances are included for the whole section; the planned signature keeps them.
set_option linter.unusedSectionVars false in
/-- A prime unramified in the composite tower is unramified in the lower step. -/
theorem ramificationIdx_lower_eq_one_of_tower
    (he : Ideal.ramificationIdx v.asIdeal w.asIdeal = 1) :
    Ideal.ramificationIdx v.asIdeal u.asIdeal = 1 := by
  haveI := w.isPrime
  have h := Ideal.ramificationIdx_algebra_tower' v.asIdeal u.asIdeal w.asIdeal
  exact Nat.eq_one_of_mul_eq_one_right (h.symm.trans he)

-- The section instances are included for the whole section; the planned signature keeps them.
set_option linter.unusedSectionVars false in
/-- A prime unramified in the composite tower is unramified in the upper step. -/
theorem ramificationIdx_upper_eq_one_of_tower
    (he : Ideal.ramificationIdx v.asIdeal w.asIdeal = 1) :
    Ideal.ramificationIdx u.asIdeal w.asIdeal = 1 := by
  haveI := w.isPrime
  have h := Ideal.ramificationIdx_algebra_tower' v.asIdeal u.asIdeal w.asIdeal
  exact Nat.eq_one_of_mul_eq_one_left (h.symm.trans he)

/-- The actual norm image of upper local integer units composes along the tower. -/
theorem localUnitNormImage_tower :
    (localFieldUnitFiltration L w 0).map (localNormMap K L v w) =
      ((localFieldUnitFiltration L w 0).map (localNormMap E L u w)).map
        (localNormMap K E v u) := by
  rw [Subgroup.map_map, localNormMap_tower K E L v u w]

/-- Surjectivity on the two integer-unit groups gives surjectivity on their composite. -/
theorem localUnitNormImage_eq_units_tower
    (hLower : (localFieldUnitFiltration E u 0).map (localNormMap K E v u) =
      localFieldUnitFiltration K v 0)
    (hUpper : (localFieldUnitFiltration L w 0).map (localNormMap E L u w) =
      localFieldUnitFiltration E u 0) :
    (localFieldUnitFiltration L w 0).map (localNormMap K L v w) =
      localFieldUnitFiltration K v 0 := by
  rw [localUnitNormImage_tower K E L v u w, hUpper, hLower]

end Tower

section Extension
variable (K L : Type*) [Field K] [Field L]
variable [hNF_K : NumberField K] [hNF_L : NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
include hNF_K hNF_L hvw

/-- V.3.11: cyclic unit norm index e becomes surjectivity when e is one. -/
theorem localUnitNormImage_eq_units_of_isCyclic [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] (he : Ideal.ramificationIdx v.asIdeal w.asIdeal = 1) :
    (localFieldUnitFiltration L w 0).map (localNormMap K L v w) =
      localFieldUnitFiltration K v 0 := by
  haveI := LocalCyclic.completion_isGalois K L v w
  haveI := LocalCyclic.completion_aut_isCyclic K L v w
  have h1 := LocalCyclic.unit_norm_index K L v w
  rw [he, Subgroup.relIndex_eq_one] at h1
  exact le_antisymm (LocalCyclic.unitNormGroup_le_units K L v w) h1

/-- V.12.7: induction on the global degree extends cyclic unit norms to the abelian case. -/
theorem localUnitNormImage_eq_units_of_unramified [IsAbelianGalois K L]
    (he : Ideal.ramificationIdx v.asIdeal w.asIdeal = 1) :
    (localFieldUnitFiltration L w 0).map (localNormMap K L v w) =
      localFieldUnitFiltration K v 0 := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank K L = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing L with
  | _ n ih =>
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  by_cases hdeg : n ≤ 1
  · -- A Galois group of order at most one is cyclic.
    haveI : Subsingleton (L ≃ₐ[K] L) := by
      rw [← Finite.card_le_one_iff_subsingleton, IsGalois.card_aut_eq_finrank, hn]
      exact hdeg
    haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_subsingleton
    exact localUnitNormImage_eq_units_of_isCyclic K L v w he
  · -- A prime upper step: induction below it, the cyclic case above it.
    obtain ⟨E, hEp, hElt⟩ := exists_intermediateField_prime_topDegree K L (by omega)
    haveI : IsAbelianGalois K E := IsAbelianGalois.tower_bot K E L
    haveI : IsAbelianGalois E L := IsAbelianGalois.tower_top K E L
    obtain ⟨u, hu1, hu2⟩ := exists_intermediate_prime K L v w E
    haveI := hu1
    haveI := hu2
    have hlow := ih _ (by rw [← hn]; exact hElt) E u
      (ramificationIdx_lower_eq_one_of_tower K E L v u w he) rfl
    haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
    haveI := Fact.mk hEp
    haveI : IsCyclic (L ≃ₐ[E] L) :=
      isCyclic_of_prime_card (p := Module.finrank E L) (IsGalois.card_aut_eq_finrank E L)
    have hup := localUnitNormImage_eq_units_of_isCyclic E L u w
      (ramificationIdx_upper_eq_one_of_tower K E L v u w he)
    exact localUnitNormImage_eq_units_tower K E L v u w hlow hup

/-- Janusz V.3.11: norms from an unramified local extension cover local integer units. -/
theorem local_units_le_normGroup_of_unramified [IsAbelianGalois K L]
    (he : Ideal.ramificationIdx v.asIdeal w.asIdeal = 1) :
    localFieldUnitFiltration K v 0 ≤ localNormGroup K L v w := by
  rw [← localUnitNormImage_eq_units_of_unramified K L v w he, ← localNormMap_range K L v w]
  exact Subgroup.map_le_range _ _

/-- The local norm index and valuation formula prevent a ramified extension
from having every local integer unit as a norm; Janusz V.12.7. -/
theorem unramified_of_local_units_le_normGroup
    (hUnits : localFieldUnitFiltration K v 0 ≤ localNormGroup K L v w)
    (hIndex : letI := completionAlgebra K L v w
      (localNormGroup K L v w).index =
        Module.finrank (v.adicCompletion K) (w.adicCompletion L)) :
    Ideal.ramificationIdx v.asIdeal w.asIdeal = 1 := by
  have h1 := localNormGroup_sup_units_index K L v w
  rw [sup_eq_left.mpr hUnits, hIndex, completion_finrank_eq_ramification_mul_inertia K L v w]
    at h1
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hf : 0 < Ideal.inertiaDeg v.asIdeal w.asIdeal := Ideal.inertiaDeg_pos v.asIdeal w.asIdeal
  exact Nat.eq_of_mul_eq_mul_right hf (h1.trans (one_mul _).symm)

end Extension
end Cox.ClassFieldTheory
