/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclic
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionTower
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! # The abelian local norm-index bound

Janusz V.12.4 (printed p. 188, PDF p. 199). The induction retains finite index together
with its bound, because a natural index of zero would otherwise hide an infinite quotient.
A prime upper step keeps the base field fixed throughout the induction.
-/

open NumberField IsDedekindDomain
noncomputable section
namespace Cox.ClassFieldTheory

section Groups
variable {G H J : Type*} [Group G] [Group H] [Group J]

/-- Finite-index images remain finite-index under composition. -/
theorem finiteIndex_range_comp (f : H →* G) (g : J →* H)
    [f.range.FiniteIndex] [g.range.FiniteIndex] : (f.comp g).range.FiniteIndex := by
  rw [Subgroup.finiteIndex_iff, MonoidHom.range_comp, Subgroup.index_map]
  haveI : (g.range ⊔ f.ker).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

/-- The index in the lower image cannot exceed the upper norm-image index. -/
theorem index_range_comp_le (f : H →* G) (g : J →* H) [g.range.FiniteIndex] :
    (f.comp g).range.index ≤ f.range.index * g.range.index := by
  rw [MonoidHom.range_comp, Subgroup.index_map, mul_comm]
  exact Nat.mul_le_mul_left _ (Subgroup.index_antitone le_sup_left)

end Groups

section Extension
variable (K : Type*) [Field K] [hNF_K : NumberField K]
variable (L : Type*) [Field L] [hNF_L : NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
include hNF_K hNF_L hvw

/-- The actual determinant norm on units, for the fixed completion embedding. -/
def localNormMap : (w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ :=
  letI := completionAlgebra K L v w
  Units.map (Algebra.norm (v.adicCompletion K) :
    w.adicCompletion L →* v.adicCompletion K)

/-- The range uses precisely the norm subgroup already defined below reciprocity. -/
theorem localNormMap_range : (localNormMap K L v w).range = localNormGroup K L v w := by
  rfl

/-- V.3.12 and the local fundamental identity give equality in the cyclic case. -/
theorem localNormGroup_index_eq_of_isCyclic [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    letI := completionAlgebra K L v w
    (localNormGroup K L v w).index =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  haveI := LocalCyclic.completion_isGalois K L v w
  haveI := LocalCyclic.completion_aut_isCyclic K L v w
  rw [LocalCyclic.norm_index K L v w, completion_finrank_eq_ramification_mul_inertia K L v w]

end Extension

section Tower
variable (K E L : Type*) [Field K] [Field E] [Field L]
variable [hNF_K : NumberField K] [hNF_E : NumberField E] [hNF_L : NumberField L]
variable [Algebra K E] [Algebra E L] [Algebra K L] [hTower : IsScalarTower K E L]
variable (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
variable (w : HeightOneSpectrum (𝓞 L))
variable [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]
variable [w.asIdeal.LiesOver v.asIdeal]
include hTower hNF_K hNF_E hNF_L

/-- The selected local norm homomorphisms satisfy the norm transitivity formula. -/
theorem localNormMap_tower :
    (localNormMap K E v u).comp (localNormMap E L u w) = localNormMap K L v w := by
  letI := completionAlgebra K E v u
  letI := completionAlgebra E L u w
  letI := completionAlgebra K L v w
  haveI := completion_isScalarTower_tower K E L v u w
  haveI := completion_finiteDimensional K E v u
  haveI := completion_finiteDimensional E L u w
  refine MonoidHom.ext fun x => Units.ext ?_
  change Algebra.norm (v.adicCompletion K)
    (Algebra.norm (u.adicCompletion E) (x : w.adicCompletion L)) =
      Algebra.norm (v.adicCompletion K) (x : w.adicCompletion L)
  exact Algebra.norm_norm

/-- Finite lower and upper norm quotients give a finite composite norm quotient. -/
theorem localNormGroup_finiteIndex_tower
    [hLower : (localNormGroup K E v u).FiniteIndex]
    [hUpper : (localNormGroup E L u w).FiniteIndex] :
    (localNormGroup K L v w).FiniteIndex := by
  haveI : (localNormMap K E v u).range.FiniteIndex := by
    rw [localNormMap_range]
    exact hLower
  haveI : (localNormMap E L u w).range.FiniteIndex := by
    rw [localNormMap_range]
    exact hUpper
  rw [← localNormMap_range K L v w, ← localNormMap_tower K E L v u w]
  exact finiteIndex_range_comp _ _

/-- The two numerical local norm-index bounds multiply along the completion tower. -/
theorem localNormGroup_index_le_tower
    [hUpper : (localNormGroup E L u w).FiniteIndex]
    (hLowerBound : letI := completionAlgebra K E v u
      (localNormGroup K E v u).index ≤
        Module.finrank (v.adicCompletion K) (u.adicCompletion E))
    (hUpperBound : letI := completionAlgebra E L u w
      (localNormGroup E L u w).index ≤
        Module.finrank (u.adicCompletion E) (w.adicCompletion L)) :
    letI := completionAlgebra K L v w
    (localNormGroup K L v w).index ≤
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  letI := completionAlgebra K E v u
  letI := completionAlgebra E L u w
  letI := completionAlgebra K L v w
  haveI := completion_isScalarTower_tower K E L v u w
  haveI := completion_finiteDimensional K E v u
  haveI := completion_finiteDimensional E L u w
  haveI : (localNormMap E L u w).range.FiniteIndex := by
    rw [localNormMap_range]
    exact hUpper
  rw [← localNormMap_range K L v w, ← localNormMap_tower K E L v u w,
    ← Module.finrank_mul_finrank (v.adicCompletion K) (u.adicCompletion E) (w.adicCompletion L)]
  refine (index_range_comp_le _ _).trans (Nat.mul_le_mul ?_ ?_)
  · rw [localNormMap_range]
    exact hLowerBound
  · rw [localNormMap_range]
    exact hUpperBound

/-- Package the independently established finite-index and numerical conclusions. -/
theorem localNormGroup_bound_tower
    [hLower : (localNormGroup K E v u).FiniteIndex]
    [hUpper : (localNormGroup E L u w).FiniteIndex]
    (hLowerBound : letI := completionAlgebra K E v u
      (localNormGroup K E v u).index ≤
        Module.finrank (v.adicCompletion K) (u.adicCompletion E))
    (hUpperBound : letI := completionAlgebra E L u w
      (localNormGroup E L u w).index ≤
        Module.finrank (u.adicCompletion E) (w.adicCompletion L)) :
    letI := completionAlgebra K L v w
    (localNormGroup K L v w).FiniteIndex ∧
      (localNormGroup K L v w).index ≤
        Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  exact ⟨localNormGroup_finiteIndex_tower K E L v u w,
    localNormGroup_index_le_tower K E L v u w hLowerBound hUpperBound⟩

end Tower

/-- Cauchy's theorem gives a prime upper step in a finite Galois tower. -/
theorem exists_intermediateField_prime_topDegree (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hdeg : 1 < Module.finrank K L) :
    ∃ E : IntermediateField K L, Nat.Prime (Module.finrank E L) ∧
      Module.finrank K E < Module.finrank K L := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hdeg.ne'
  haveI := Fact.mk hp
  have hcard := IsGalois.card_aut_eq_finrank K L
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := L ≃ₐ[K] L) p (hcard ▸ hpd)
  have hEL : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L = p := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hσ]
  refine ⟨IntermediateField.fixedField (Subgroup.zpowers σ), hEL ▸ hp, ?_⟩
  have hmul := Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  have h2 := Nat.mul_le_mul_left
    (Module.finrank K (IntermediateField.fixedField (Subgroup.zpowers σ))) hp.two_le
  rw [← hEL, hmul] at h2
  omega

section Induction
variable (K : Type*) [Field K] [hNF_K : NumberField K]
variable (L : Type*) [Field L] [hNF_L : NumberField L] [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
include hNF_K hNF_L hvw

-- `hNF_K` and `hNF_L` are included for the whole section; the planned signature keeps them.
set_option linter.unusedSectionVars false in
/-- Contract the chosen upper prime to the intermediate field in the induction. -/
theorem exists_intermediate_prime (E : IntermediateField K L) :
    ∃ u : HeightOneSpectrum (𝓞 E), u.asIdeal.LiesOver v.asIdeal ∧
      w.asIdeal.LiesOver u.asIdeal := by
  refine ⟨w.under (𝓞 E), ?_, ⟨rfl⟩⟩
  haveI : w.asIdeal.LiesOver (w.under (𝓞 E)).asIdeal := ⟨rfl⟩
  exact Ideal.LiesOver.tower_bot w.asIdeal (w.under (𝓞 E)).asIdeal v.asIdeal

/-- V.12.4's induction carries finiteness so that its numerical bound is meaningful.
The two conclusions are exposed separately by the projections below. -/
private theorem localNormGroup_finiteIndex_and_index_le [IsAbelianGalois K L] :
    letI := completionAlgebra K L v w
    (localNormGroup K L v w).FiniteIndex ∧
      (localNormGroup K L v w).index ≤
        Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank K L = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing L with
  | _ n ih =>
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  by_cases hdeg : n ≤ 1
  · -- A Galois group of order at most one is cyclic; the cyclic equality applies.
    haveI : Subsingleton (L ≃ₐ[K] L) := by
      rw [← Finite.card_le_one_iff_subsingleton, IsGalois.card_aut_eq_finrank, hn]
      exact hdeg
    haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_subsingleton
    have heq := localNormGroup_index_eq_of_isCyclic K L v w
    letI := completionAlgebra K L v w
    haveI := completion_finiteDimensional K L v w
    have hpos : 0 < Module.finrank (v.adicCompletion K) (w.adicCompletion L) :=
      Module.finrank_pos
    exact ⟨⟨by rw [heq]; exact hpos.ne'⟩, heq.le⟩
  · -- A prime upper step: induction below it, the cyclic equality above it.
    obtain ⟨E, hEp, hElt⟩ := exists_intermediateField_prime_topDegree K L (by omega)
    haveI : IsAbelianGalois K E := IsAbelianGalois.tower_bot K E L
    haveI : IsAbelianGalois E L := IsAbelianGalois.tower_top K E L
    obtain ⟨u, hu1, hu2⟩ := exists_intermediate_prime K L v w E
    haveI := hu1
    haveI := hu2
    obtain ⟨hLower, hLowerBound⟩ := ih _ (by rw [← hn]; exact hElt) E u rfl
    haveI := hLower
    haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
    haveI := Fact.mk hEp
    haveI : IsCyclic (L ≃ₐ[E] L) :=
      isCyclic_of_prime_card (p := Module.finrank E L) (IsGalois.card_aut_eq_finrank E L)
    have heq := localNormGroup_index_eq_of_isCyclic E L u w
    letI := completionAlgebra E L u w
    haveI := completion_finiteDimensional E L u w
    have hpos : 0 < Module.finrank (u.adicCompletion E) (w.adicCompletion L) :=
      Module.finrank_pos
    haveI : (localNormGroup E L u w).FiniteIndex := ⟨by rw [heq]; exact hpos.ne'⟩
    exact localNormGroup_bound_tower K E L v u w hLowerBound heq.le

/-- Janusz V.3.12 and the tower induction in V.12.4 give an actually finite local
norm quotient; this prevents the natural-number index convention from hiding infinity. -/
theorem localNormGroup_finiteIndex [IsAbelianGalois K L] :
    (localNormGroup K L v w).FiniteIndex := by
  exact (localNormGroup_finiteIndex_and_index_le K L v w).1

/-- Janusz V.12.4: the local norm index is at most the local degree for an abelian extension. -/
theorem localNormGroup_index_le [IsAbelianGalois K L] :
    letI := completionAlgebra K L v w
    (localNormGroup K L v w).index ≤
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  exact (localNormGroup_finiteIndex_and_index_le K L v w).2

end Induction
end Cox.ClassFieldTheory
