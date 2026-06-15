/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.RingOfIntegers

/-!
# `ℚ(∛3)` Discriminant

Discriminant computations and immediate discriminant consequences.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Discriminant
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CubeRootThree

/-- The number-field discriminant of `ℚ(∛3)` is `-243 = -3⁵` (for `X³ - a` one has
`disc = -27a²`). In particular `3` is the only ramified prime, cf. `ramified_iff_eq_three`. -/
theorem numberField_discr_eq : NumberField.discr K = (-243 : ℤ) := by
  have hf : cubePolynomial ≠ 0 := by intro h; simpa using congrArg natDegree h
  have hdim : (AdjoinRoot.powerBasis hf).dim = 3 := by
    rw [AdjoinRoot.powerBasis_dim hf]; exact natDegree_X_pow_sub_C
  set qb : Basis (Fin 3) ℚ K := (AdjoinRoot.powerBasis hf).basis.reindex (finCongr hdim)
    with hqb
  have hbpow : ∀ i : Fin 3, qb i = cubeRootThree ^ (i : ℕ) := by
    intro i
    rw [hqb, Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis_gen]
    exact rfl
  have hqfun : ⇑qb = integralBasisVectors := by
    funext i
    rw [hbpow i]
    fin_cases i <;> simp [integralBasisVectors]
  have hspan : Submodule.span ℤ (Set.range ⇑qb) =
      Submodule.span ℤ (Set.range ⇑(NumberField.integralBasis K)) := by
    rw [hqfun]; exact span_integralBasisVectors_eq_integralBasis
  have h1 : ∀ i j, IsIntegral ℤ (qb.toMatrix (NumberField.integralBasis K) i j) := by
    intro i j
    have hmem : (NumberField.integralBasis K) j ∈ Submodule.span ℤ (Set.range ⇑qb) := by
      rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩
    rw [Basis.mem_span_iff_repr_mem] at hmem
    obtain ⟨m, hm⟩ := hmem i
    rw [Basis.toMatrix_apply, ← hm]
    exact isIntegral_algebraMap
  have h2 : ∀ i j, IsIntegral ℤ ((NumberField.integralBasis K).toMatrix qb i j) := by
    intro i j
    have hmem : qb j ∈ Submodule.span ℤ (Set.range ⇑(NumberField.integralBasis K)) := by
      rw [← hspan]; exact Submodule.subset_span ⟨j, rfl⟩
    rw [Basis.mem_span_iff_repr_mem] at hmem
    obtain ⟨m, hm⟩ := hmem i
    rw [Basis.toMatrix_apply, ← hm]
    exact isIntegral_algebraMap
  have hQ : (NumberField.discr K : ℚ) = (-243 : ℚ) := by
    rw [NumberField.coe_discr,
      ← Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral K h1 h2,
      hqb, Basis.coe_reindex, Algebra.discr_reindex]
    exact discr_powerBasis_eq
  exact_mod_cast hQ

/-- The discriminant of mathlib's canonical field integral basis is `-243`. -/
theorem integralBasis_discr :
    Algebra.discr ℚ (NumberField.integralBasis K) = (-243 : ℚ) := by
  have h := NumberField.coe_discr K
  rw [numberField_discr_eq] at h
  simpa using h.symm


end NumberField.CubeRootThree
