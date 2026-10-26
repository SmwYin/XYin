/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-! # The compatible map between prime-adic completions

Janusz II.2.2 and II.3.8. These statements precede reciprocity and local norms.
-/

open NumberField IsDedekindDomain
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]
variable (L : Type*) [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]

include hvw in
/-- A lying-over prime gives the continuous extension of the fixed field embedding
between the actual prime-adic completions. -/
theorem exists_completionEmbedding :
    ∃ ι : v.adicCompletion K →+* w.adicCompletion L, Continuous ι ∧
      ∀ x : K, ι (FinitePlace.embedding v x) =
        FinitePlace.embedding w (algebraMap K L x) := by
  have huc := HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) (L := L)
    (v := v) (w := w)
  refine ⟨UniformSpace.Completion.mapRingHom _ huc.continuous,
    UniformSpace.Completion.continuous_map, fun x => ?_⟩
  rw [FinitePlace.embedding_apply, FinitePlace.embedding_apply]
  exact UniformSpace.Completion.mapRingHom_coe huc.continuous _

/-- The continuous completion embedding extending the given global inclusion. -/
def completionEmbedding : v.adicCompletion K →+* w.adicCompletion L :=
  Classical.choose (exists_completionEmbedding K L v w)

/-- Continuity of the chosen completion embedding. -/
theorem completionEmbedding_continuous : Continuous (completionEmbedding K L v w) := by
  exact (Classical.choose_spec (exists_completionEmbedding K L v w)).1

/-- The chosen local embedding agrees with the global embedding on its dense domain. -/
theorem completionEmbedding_commutes (x : K) :
    completionEmbedding K L v w (FinitePlace.embedding v x) =
      FinitePlace.embedding w (algebraMap K L x) := by
  exact (Classical.choose_spec (exists_completionEmbedding K L v w)).2 x

/-- The scalar structure supplied by the actual completion embedding. -/
@[reducible]
def completionAlgebra : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (completionEmbedding K L v w).toAlgebra

/-- Compatibility of local and global scalar structures. -/
theorem completion_isScalarTower :
    letI := completionAlgebra K L v w
    IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) := by
  letI := completionAlgebra K L v w
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  exact (completionEmbedding_commutes K L v w x).symm

/-- Continuity of local scalar multiplication, from the continuous embedding. -/
theorem completion_continuousSMul :
    letI := completionAlgebra K L v w
    ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) := by
  letI := completionAlgebra K L v w
  refine ⟨?_⟩
  simp_rw [Algebra.smul_def]
  exact ((completionEmbedding_continuous K L v w).comp continuous_fst).mul continuous_snd

/-- Finite global degree gives finite degree for the chosen local extension. -/
theorem completion_finiteDimensional :
    letI := completionAlgebra K L v w
    FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) := by
  letI := completionAlgebra K L v w
  haveI := completion_continuousSMul K L v w
  haveI := completion_isScalarTower K L v w
  exact inferInstance

end Cox.ClassFieldTheory
