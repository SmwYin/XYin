/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionEmbedding
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # Completed generators and unramified radical extensions

Source: Janusz V.9.3 and its Hensel/local-degree prerequisites.
-/

noncomputable section
namespace Cox.ClassFieldTheory
open NumberField IsDedekindDomain Polynomial IsLocalRing
open scoped Valued

/-- A dense image of algebra generators generates a finite-dimensional complete topological
extension. -/
theorem adjoin_image_eq_top_of_denseRange
    (K F L E : Type*) [CommSemiring K] [NontriviallyNormedField F]
    [CompleteSpace F] [Semiring L] [Ring E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    [Algebra K F] [Algebra K L] [Algebra K E] [Algebra F E]
    [IsScalarTower K F E] [ContinuousSMul F E] [FiniteDimensional F E]
    (φ : L →ₐ[K] E) (hdense : DenseRange φ) (s : Set L)
    (hgen : Algebra.adjoin K s = ⊤) :
    Algebra.adjoin F (φ '' s) = ⊤ := by
  set B := Algebra.adjoin F (φ '' s) with hB
  have hrange : ∀ y : L, φ y ∈ B := by
    intro y
    have hy : y ∈ Algebra.adjoin K s := hgen ▸ Algebra.mem_top
    have hφy : φ y ∈ Algebra.adjoin K (φ '' s) := by
      rw [← AlgHom.map_adjoin]
      exact Subalgebra.mem_map.mpr ⟨y, hy, rfl⟩
    have hsub : Algebra.adjoin K (φ '' s) ≤ B.restrictScalars K := by
      rw [Algebra.adjoin_le_iff]
      intro z hz
      rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
      exact Algebra.subset_adjoin hz
    exact hsub hφy
  have hclosed : IsClosed (B.toSubmodule : Set E) := B.toSubmodule.closed_of_finiteDimensional
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ closure (Set.range φ) := by rw [hdense.closure_range]; trivial
  have hsub : Set.range φ ⊆ (B.toSubmodule : Set E) := by
    rintro _ ⟨y, rfl⟩
    exact hrange y
  exact closure_minimal hsub hclosed hz

/-- The same global generators generate the completed extension. -/
theorem completion_adjoin_image_eq_top
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (s : Set L) (hgen : Algebra.adjoin K s = ⊤) :
    letI := completionAlgebra K L v w
    Algebra.adjoin (v.adicCompletion K) (FinitePlace.embedding w '' s) = ⊤ := by
  letI := completionAlgebra K L v w
  haveI := completion_isScalarTower K L v w
  haveI := completion_continuousSMul K L v w
  haveI := completion_finiteDimensional K L v w
  have hdense : DenseRange (IsScalarTower.toAlgHom K L (w.adicCompletion L)) :=
    w.denseRange_algebraMap L
  exact adjoin_image_eq_top_of_denseRange K (v.adicCompletion K) L (w.adicCompletion L)
    (IsScalarTower.toAlgHom K L (w.adicCompletion L)) hdense s hgen

end Cox.ClassFieldTheory
