/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionGalois
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionNorm
import Mathlib.GroupTheory.Complement

/-! # The coset norm calculation in Janusz V.3.4

Right cosets are used: D × T → G sends (d,t) to d*t. The distinguished
representative is 1.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise WithZero
noncomputable section
namespace Cox.ClassFieldTheory

/-- Choose a right transversal containing the identity in a finite group. -/
theorem exists_finset_rightTransversal_one (G : Type*) [Group G] [Finite G]
    (D : Subgroup G) :
    ∃ T : Finset G, Subgroup.IsComplement (D : Set G) (T : Set G) ∧ 1 ∈ T := by
  obtain ⟨S, hS, h1⟩ := Subgroup.exists_isComplement_right D 1
  refine ⟨(Set.toFinite S).toFinset, ?_, ?_⟩
  · rwa [Set.Finite.coe_toFinset]
  · rwa [Set.Finite.mem_toFinset]

open Classical in
/-- The product over a finite group partitions into products over right cosets. -/
theorem prod_eq_prod_rightTransversal {G A : Type*} [Group G] [Fintype G]
    [CommMonoid A] (D : Subgroup G) (T : Finset G)
    (hT : Subgroup.IsComplement (D : Set G) (T : Set G)) (f : G → A) :
    (∏ g : G, f g) = ∏ t ∈ T, ∏ d : D, f ((d : G) * t) := by
  have hbij : Function.Bijective (fun p : D × T => (p.1 : G) * p.2) := hT
  rw [← Fintype.prod_equiv (Equiv.ofBijective _ hbij) (fun p => f ((p.1 : G) * p.2)) f
    (fun p => rfl), Fintype.prod_prod_type_right, ← Finset.prod_coe_sort T]

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable [hGalois : IsGalois K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
include hGalois hvw
attribute [local instance] completionAlgebra completion_finiteDimensional

open Classical in
/-- The completed norm of a global element is the product over its actual decomposition group. -/
theorem completion_norm_global_eq_stabilizer_prod (x : L) :
    completionEmbedding K L v w
      (Algebra.norm (v.adicCompletion K) (FinitePlace.embedding w x)) =
        ∏ σ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal,
          FinitePlace.embedding w ((σ : L ≃ₐ[K] L) x) := by
  haveI := LocalCyclic.completion_isGalois K L v w
  obtain ⟨ι, hι, hιx⟩ := LocalCyclic.exists_completion_stabilizerMap K L v w
  have hfin : Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :=
    completion_finrank_eq_card_stabilizer K L v w
  have hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) =
      Nat.card (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) := by
    rw [IsGalois.card_aut_eq_finrank, hfin]
  have hbij : Function.Bijective ι := (Nat.bijective_iff_injective_and_card ι).mpr ⟨hι, hcard⟩
  change algebraMap (v.adicCompletion K) (w.adicCompletion L) _ = _
  rw [Algebra.norm_eq_prod_automorphisms (K := v.adicCompletion K),
    ← Fintype.prod_equiv (Equiv.ofBijective ι hbij)
      (fun σ => ι σ (FinitePlace.embedding w x)) (fun τ => τ (FinitePlace.embedding w x))
      (fun σ => rfl)]
  exact Finset.prod_congr rfl fun σ _ => hιx σ x

/-- Janusz V.3.4: the global norm is the local norm of a product of coset conjugates. -/
theorem completion_global_norm_coset_product (T : Finset (L ≃ₐ[K] L))
    (hT : Subgroup.IsComplement
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal : Set (L ≃ₐ[K] L))
      (T : Set (L ≃ₐ[K] L))) (x : L) :
    FinitePlace.embedding v (Algebra.norm K x) =
      Algebra.norm (v.adicCompletion K) (∏ τ ∈ T, FinitePlace.embedding w (τ x)) := by
  classical
  apply (completionEmbedding K L v w).injective
  rw [completionEmbedding_commutes, Algebra.norm_eq_prod_automorphisms (K := K)]
  simp only [map_prod]
  rw [prod_eq_prod_rightTransversal _ T hT]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [completion_norm_global_eq_stabilizer_prod]
  rfl

/-- A global field norm gives an actual local field norm at every chosen prime. -/
theorem global_norm_mem_localNormGroup (x : Lˣ) :
    Units.map (FinitePlace.embedding v).toMonoidHom
      (Units.map (Algebra.norm K : L →* K) x) ∈ localNormGroup K L v w := by
  classical
  obtain ⟨T, hT, -⟩ := exists_finset_rightTransversal_one (L ≃ₐ[K] L)
    (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)
  have hne : (∏ τ ∈ T, FinitePlace.embedding w (τ (x : L))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro τ _
    exact (map_ne_zero _).mpr ((map_ne_zero τ).mpr x.ne_zero)
  rw [mem_localNormGroup_iff]
  refine ⟨Units.mk0 _ hne, Units.ext ?_⟩
  change Algebra.norm (v.adicCompletion K) (∏ τ ∈ T, FinitePlace.embedding w (τ (x : L))) =
    FinitePlace.embedding v (Algebra.norm K (x : L))
  exact (completion_global_norm_coset_product K L v w T hT x).symm

end Cox.ClassFieldTheory
