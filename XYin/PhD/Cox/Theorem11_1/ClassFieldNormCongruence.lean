/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldRayElements
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Relative norms preserve finite congruences

The integer norm computation used in Janusz V.3.1 and V.7.2, below cyclic class-field theory. The
target of an embedding may be an algebraic closure.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [hNF : NumberField K]
variable (E : Type*) [Field E] [NumberField E] [Algebra K E]
variable [Module.Finite (𝓞 K) (𝓞 E)]

include hNF in
/-- Integral extension from a Dedekind ring of integers is faithfully flat, even for
an algebraic-closure target; extension and contraction recover every base ideal. -/
theorem integerIdeal_comap_map (Ω : Type*) [Field Ω] [Algebra K Ω]
    (m : Ideal (𝓞 K)) :
    (m.map (algebraMap (𝓞 K) (𝓞 Ω))).comap (algebraMap (𝓞 K) (𝓞 Ω)) = m := by
  exact Ideal.comap_map_eq_self_of_faithfullyFlat m

/-- A finite product of elements congruent to one is congruent to one. -/
theorem prod_sub_one_mem {R ι : Type*} [CommRing R] (m : Ideal R)
    (s : Finset ι) (f : ι → R) (hf : ∀ i ∈ s, f i - 1 ∈ m) :
    (∏ i ∈ s, f i) - 1 ∈ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h : f a * ∏ i ∈ s, f i - 1 = f a * (∏ i ∈ s, f i - 1) + (f a - 1) := by ring
    rw [h]
    exact m.add_mem (m.mul_mem_left _ h2) h1

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- Every K-embedding takes α≡1 mod mO_E to the same congruence in its target. -/
theorem embedding_sub_one_mem {Ω : Type*} [Field Ω] [Algebra K Ω]
    (σ : E →ₐ[K] Ω) (m : Ideal (𝓞 K)) (α : 𝓞 E)
    (hα : α - 1 ∈ m.map (algebraMap (𝓞 K) (𝓞 E))) :
    RingOfIntegers.mapAlgHom σ α - 1 ∈ m.map (algebraMap (𝓞 K) (𝓞 Ω)) := by
  have h := Ideal.mem_map_of_mem (RingOfIntegers.mapAlgHom σ : 𝓞 E →+* 𝓞 Ω) hα
  rw [map_sub, map_one, Ideal.map_map, AlgHom.comp_algebraMap] at h
  exact h

open scoped Classical in
-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- The integral relative norm is the product of the integral images of all K-embeddings
in an algebraic closure; the target is not assumed to be a number field. -/
theorem intNorm_eq_prod_integer_embeddings (Ω : Type*) [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (α : 𝓞 E) :
    algebraMap (𝓞 K) (𝓞 Ω) (Algebra.intNorm (𝓞 K) (𝓞 E) α) =
      ∏ σ : E →ₐ[K] Ω, RingOfIntegers.mapAlgHom σ α := by
  apply RingOfIntegers.ext
  have h1 : ((algebraMap (𝓞 K) (𝓞 Ω) (Algebra.intNorm (𝓞 K) (𝓞 E) α) : 𝓞 Ω) : Ω) =
      algebraMap K Ω (algebraMap (𝓞 K) K (Algebra.intNorm (𝓞 K) (𝓞 E) α)) := rfl
  rw [h1, Algebra.algebraMap_intNorm (L := E), Algebra.norm_eq_prod_embeddings]
  push_cast
  rfl

/-- The integer norm preserves the source's congruence to one. -/
theorem intNorm_sub_one_mem (m : Ideal (𝓞 K)) (α : 𝓞 E)
    (hα : α - 1 ∈ m.map (algebraMap (𝓞 K) (𝓞 E))) :
    Algebra.intNorm (𝓞 K) (𝓞 E) α - 1 ∈ m := by
  classical
  let Ω := AlgebraicClosure K
  have h2 := prod_sub_one_mem (m.map (algebraMap (𝓞 K) (𝓞 Ω))) Finset.univ
    (fun σ : E →ₐ[K] Ω => RingOfIntegers.mapAlgHom σ α)
    (fun σ _ => embedding_sub_one_mem K E σ m α hα)
  rw [← intNorm_eq_prod_integer_embeddings K E Ω α, ← map_one (algebraMap (𝓞 K) (𝓞 Ω)),
    ← map_sub] at h2
  have h3 := Ideal.mem_comap.mpr h2
  rwa [integerIdeal_comap_map K Ω m] at h3

end Cox.ClassFieldTheory
