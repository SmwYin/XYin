/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionEmbedding

/-! # Compatible towers of prime-adic completions

Janusz V.12.4 uses the completion tower attached to a fixed global tower and primes. Its
compatibility follows from uniqueness of continuous extension in II.2.2.
-/

open NumberField IsDedekindDomain
noncomputable section
namespace Cox.ClassFieldTheory

variable (K E L : Type*) [Field K] [Field E] [Field L]
variable [NumberField K] [NumberField E] [NumberField L]
variable [Algebra K E] [Algebra E L] [Algebra K L] [hTower : IsScalarTower K E L]
variable (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
variable (w : HeightOneSpectrum (𝓞 L))
variable [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]
variable [w.asIdeal.LiesOver v.asIdeal]

include hTower

/-- Continuous extension respects the fixed tower of global field embeddings. -/
theorem completionEmbedding_comp :
    (completionEmbedding E L u w).comp (completionEmbedding K E v u) =
      completionEmbedding K L v w := by
  have hcont : Continuous ((completionEmbedding E L u w).comp (completionEmbedding K E v u)) :=
    (completionEmbedding_continuous E L u w).comp (completionEmbedding_continuous K E v u)
  have hfun : ⇑((completionEmbedding E L u w).comp (completionEmbedding K E v u)) =
      ⇑(completionEmbedding K L v w) := by
    refine Continuous.ext_on (v.denseRange_algebraMap K) hcont
      (completionEmbedding_continuous K L v w) ?_
    rintro _ ⟨x, rfl⟩
    change completionEmbedding E L u w (completionEmbedding K E v u (FinitePlace.embedding v x)) =
      completionEmbedding K L v w (FinitePlace.embedding v x)
    rw [completionEmbedding_commutes, completionEmbedding_commutes, completionEmbedding_commutes,
      ← IsScalarTower.algebraMap_apply]
  exact RingHom.ext (congrFun hfun)

/-- The three chosen local scalar structures form the actual completion tower. -/
theorem completion_isScalarTower_tower :
    letI := completionAlgebra K E v u
    letI := completionAlgebra E L u w
    letI := completionAlgebra K L v w
    IsScalarTower (v.adicCompletion K) (u.adicCompletion E) (w.adicCompletion L) := by
  letI := completionAlgebra K E v u
  letI := completionAlgebra E L u w
  letI := completionAlgebra K L v w
  exact IsScalarTower.of_algebraMap_eq' (completionEmbedding_comp K E L v u w).symm

end Cox.ClassFieldTheory
