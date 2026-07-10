/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import Mathlib

/-!
# `ℚ(√-6)` Basic

Field definition, chosen generator, defining polynomial, degree, and basic algebraic facts.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Basic
-/

noncomputable section

open Module
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace NumberField.SqrtNegSix

/-- The nonsquare condition making `QuadraticAlgebra ℚ (-6) 0` a field: `-6` is not a
rational square. -/
instance : Fact (∀ r : ℚ, r ^ 2 ≠ (-6 : ℚ) + (0 : ℚ) * r) := by
  refine ⟨fun r hr => ?_⟩
  have h : (0 : ℚ) ≤ r ^ 2 := sq_nonneg r
  nlinarith

/-- The number field `ℚ(√-6)` as `QuadraticAlgebra ℚ (-6) 0`. -/
abbrev K : Type := QuadraticAlgebra ℚ (-6 : ℚ) 0

/-- The distinguished square root of `-6`. -/
abbrev θ : K := QuadraticAlgebra.omega

/-- The field structure on `K`. -/
instance : Field K := by
  infer_instance

/-- The finite-dimensional `ℚ`-vector-space structure on `K`. -/
instance : FiniteDimensional ℚ K :=
  (QuadraticAlgebra.basis (-6 : ℚ) (0 : ℚ)).finiteDimensional_of_finite

/-- The number-field structure on `K`. -/
instance : NumberField K :=
  NumberField.of_module_finite ℚ K

/-- The extension degree of `K = ℚ(√-6)` over `ℚ` is `2`. -/
theorem degree_eq_two : Module.finrank ℚ K = 2 := by
  rw [Module.finrank_eq_card_basis (QuadraticAlgebra.basis (-6 : ℚ) (0 : ℚ)), Fintype.card_fin]

instance : Algebra.IsQuadraticExtension ℚ K where
  finrank_eq_two' := degree_eq_two

/-- The generator satisfies `θ² = -6`. -/
theorem theta_sq : θ ^ 2 = -6 := by
  rw [sq, QuadraticAlgebra.omega_mul_omega_eq_add]
  simp

/-- The polynomial `X² + 6`, whose root is `√-6`. -/
abbrev sqrtNegSixPolynomial : Polynomial ℚ :=
  Polynomial.X ^ 2 + Polynomial.C (6 : ℚ)

instance : Fact (Irreducible sqrtNegSixPolynomial) := by
  exact ⟨by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [sqrtNegSixPolynomial, Finset.mem_Icc]
      change 1 ≤ (Polynomial.X ^ 2 + Polynomial.C (6 : ℚ)).natDegree ∧
        (Polynomial.X ^ 2 + Polynomial.C (6 : ℚ)).natDegree ≤ 3
      rw [Polynomial.natDegree_X_pow_add_C]
      norm_num
    · intro x hx
      have hzero : x ^ 2 + 6 = 0 := by
        simpa [sqrtNegSixPolynomial, Polynomial.IsRoot] using hx
      have h : (0 : ℚ) ≤ x ^ 2 := sq_nonneg x
      nlinarith⟩

/-- The same field, now presented by adjoining a root of `X² + 6`. -/
abbrev KAdjoinRoot : Type := AdjoinRoot sqrtNegSixPolynomial

/-- The formal square root of `-6` in the `AdjoinRoot` presentation. -/
abbrev thetaAdjoinRoot : KAdjoinRoot := AdjoinRoot.root sqrtNegSixPolynomial

theorem thetaAdjoinRoot_sq :
    thetaAdjoinRoot ^ 2 = (-6 : KAdjoinRoot) := by
  have hroot : thetaAdjoinRoot ^ 2 + 6 = 0 := by
    simpa [thetaAdjoinRoot, sqrtNegSixPolynomial] using
      (AdjoinRoot.eval₂_root sqrtNegSixPolynomial)
  linear_combination hroot

private theorem sqrtNegSixPolynomial_aeval_theta :
    Polynomial.eval₂ (Algebra.ofId ℚ K) θ sqrtNegSixPolynomial = 0 := by
  calc Polynomial.eval₂ (Algebra.ofId ℚ K) θ sqrtNegSixPolynomial
      = θ ^ 2 + 6 := by simp [sqrtNegSixPolynomial]
    _ = 0 := by rw [theta_sq]; ring

private theorem thetaAdjoinRoot_mul_self :
    thetaAdjoinRoot * thetaAdjoinRoot =
      (-6 : ℚ) • (1 : KAdjoinRoot) + (0 : ℚ) • thetaAdjoinRoot := by
  rw [show thetaAdjoinRoot * thetaAdjoinRoot = thetaAdjoinRoot ^ 2 by ring,
    thetaAdjoinRoot_sq]
  simp

/-- The `AdjoinRoot` presentation is equivalent to the quadratic-algebra model. -/
noncomputable def adjoinRootEquivQuadratic : KAdjoinRoot ≃ₐ[ℚ] K := by
  let f : KAdjoinRoot →ₐ[ℚ] K :=
    AdjoinRoot.liftAlgHom sqrtNegSixPolynomial (Algebra.ofId ℚ K) θ
      sqrtNegSixPolynomial_aeval_theta
  let g : K →ₐ[ℚ] KAdjoinRoot :=
    QuadraticAlgebra.lift ⟨thetaAdjoinRoot, thetaAdjoinRoot_mul_self⟩
  have hfroot : f thetaAdjoinRoot = θ := by
    change (AdjoinRoot.liftAlgHom sqrtNegSixPolynomial (Algebra.ofId ℚ K) θ
        sqrtNegSixPolynomial_aeval_theta) (AdjoinRoot.root sqrtNegSixPolynomial) = θ
    exact AdjoinRoot.liftAlgHom_root sqrtNegSixPolynomial (Algebra.ofId ℚ K) θ
      sqrtNegSixPolynomial_aeval_theta
  have hgroot : g θ = thetaAdjoinRoot := by
    change (QuadraticAlgebra.omega : K).re • (1 : KAdjoinRoot) +
      (QuadraticAlgebra.omega : K).im • thetaAdjoinRoot = thetaAdjoinRoot
    simp
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply QuadraticAlgebra.algHom_ext
    change f (g θ) = θ
    rw [hgroot]
    exact hfroot
  · apply AdjoinRoot.algHom_ext
    change g (f thetaAdjoinRoot) = thetaAdjoinRoot
    rw [hfroot]
    exact hgroot

theorem adjoinRootEquivQuadratic_root :
    adjoinRootEquivQuadratic thetaAdjoinRoot = θ := by
  change (AdjoinRoot.liftAlgHom sqrtNegSixPolynomial (Algebra.ofId ℚ K) θ
      sqrtNegSixPolynomial_aeval_theta) (AdjoinRoot.root sqrtNegSixPolynomial) = θ
  exact AdjoinRoot.liftAlgHom_root sqrtNegSixPolynomial (Algebra.ofId ℚ K) θ
    sqrtNegSixPolynomial_aeval_theta


end NumberField.SqrtNegSix
