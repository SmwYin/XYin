/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.FieldTheory.RatFunc.Basic
import XYin.PhD.Cox.CoxMatrices
import XYin.PhD.Cox.LatticeJ
import XYin.PhD.Cox.ModularPolynomial.AnalyticSupport

/-!
# The function field of the upper half-plane

This file realizes `ℂ(Y)` inside the meromorphic function field on the upper half-plane
by sending `Y` to the modular function `j`. Precomposition by `SL₂(ℤ)` then gives
`ℂ(Y)`-automorphisms which act transitively on the right-coset conjugates `j(mγτ)`.

The distinctness proof is carried out for functions, rather than at a fixed point of the upper
half-plane: specialized roots can collide at CM points.
-/

open Complex Function MatrixGroups ModularForm UpperHalfPlane
open UpperHalfPlane.MeromorphicField
open scoped Manifold

noncomputable section

namespace Cox
namespace UpperHalfPlaneFunctionField

/-- The codiscrete field of meromorphic functions on the upper half-plane. -/
abbrev FunctionField := MeromorphicField

/-- The modular function `j`, bundled as a holomorphic function. -/
def jElement : HolomorphicFunction := ⟨j, j_mdifferentiable⟩

/-- Evaluation of a complex polynomial at the holomorphic function `j`. -/
def evalJ : Polynomial ℂ →+* HolomorphicFunction :=
  Polynomial.eval₂RingHom (algebraMap ℂ HolomorphicFunction) jElement

/-- Evaluation of a holomorphic function at a point of the upper half-plane. -/
def evaluation (tau : ℍ) : HolomorphicFunction →+* ℂ :=
  (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) tau).comp holomorphicFunctions.subtype

@[simp]
theorem evaluation_apply (tau : ℍ) (f : HolomorphicFunction) : evaluation tau f = f.1 tau :=
  rfl

@[simp]
theorem evalJ_apply (P : Polynomial ℂ) (tau : ℍ) :
    (evalJ P).1 tau = P.eval (j tau) := by
  change evaluation tau (Polynomial.eval₂ (algebraMap ℂ HolomorphicFunction) jElement P) = _
  rw [Polynomial.hom_eval₂]
  rfl

@[simp]
theorem evalJ_X : evalJ Polynomial.X = jElement :=
  Polynomial.eval₂_X _ _

/-- Evaluation at `j` sends a constant polynomial to the constant function. -/
@[simp]
theorem evalJ_C (c : ℂ) : evalJ (Polynomial.C c) = algebraMap ℂ HolomorphicFunction c :=
  Polynomial.eval₂_C _ _

/-- Evaluating at a point after evaluating a polynomial at `j` is evaluation at `j(τ)`. -/
theorem evaluation_comp_evalJ (tau : ℍ) :
    (evaluation tau).comp evalJ = Polynomial.evalRingHom (j tau) :=
  RingHom.ext fun P ↦ evalJ_apply P tau

/-- Polynomial evaluation at `j` is injective because the analytic `j`-function is surjective. -/
theorem evalJ_injective : Function.Injective evalJ := fun P Q hPQ ↦
  Polynomial.funext fun z ↦ by
    obtain ⟨tau, rfl⟩ := j_surjective z
    simpa using congrArg (·.1 tau) hPQ

/-- Evaluation at `j`, followed by inclusion into the function field. -/
def evalJFracPoly : Polynomial ℂ →+* FunctionField :=
  (algebraMap HolomorphicFunction FunctionField).comp evalJ

/-- Evaluation at `j` remains injective after passing to the function field. -/
theorem evalJFracPoly_injective : Function.Injective evalJFracPoly :=
  holomorphicToMeromorphic_injective.comp evalJ_injective

/-- The embedding `ℂ(Y) → FunctionField` obtained by sending `Y` to `j`. -/
def ratFuncEvalJ : RatFunc ℂ →+* FunctionField :=
  RatFunc.liftRingHom evalJFracPoly
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ evalJFracPoly_injective)

noncomputable instance : Algebra (RatFunc ℂ) FunctionField := ratFuncEvalJ.toAlgebra

/-- The chosen algebra structure is induced by `ratFuncEvalJ`. -/
@[simp]
theorem algebraMap_ratFunc (r : RatFunc ℂ) :
    algebraMap (RatFunc ℂ) FunctionField r = ratFuncEvalJ r := rfl

/-- On polynomials, the rational-function embedding agrees with evaluation at `j`. -/
@[simp]
theorem ratFuncEvalJ_algebraMap (P : Polynomial ℂ) :
    ratFuncEvalJ (algebraMap (Polynomial ℂ) (RatFunc ℂ) P) =
      evalJFracPoly P := by
  simp [ratFuncEvalJ]

/-- The embedding of `ℂ(Y)` extends the embedding of the constants. -/
instance : IsScalarTower ℂ (RatFunc ℂ) FunctionField :=
  IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ), algebraMap_ratFunc,
      ratFuncEvalJ_algebraMap, evalJFracPoly, RingHom.comp_apply, Polynomial.algebraMap_eq,
      evalJ_C]
    rfl

private theorem precomp_evalJPoly (delta : SL(2, ℤ)) (P : Polynomial ℂ) :
    precomp delta (evalJFracPoly P) = evalJFracPoly P :=
  precomp_algebraMap_eq_of_forall delta _ _ fun tau ↦ by
    simp only [evalJ_apply, j_modularGroup_smul]

/-- Precomposition fixes the embedded copy of `ℂ(Y)`. -/
private theorem precomp_ratFunc (delta : SL(2, ℤ)) (r : RatFunc ℂ) :
    precomp delta (algebraMap (RatFunc ℂ) FunctionField r) =
      algebraMap (RatFunc ℂ) FunctionField r := by
  induction r using RatFunc.induction_on with
  | f p q _ =>
      simp only [map_div₀, algebraMap_ratFunc, ratFuncEvalJ_algebraMap, precomp_evalJPoly]

/-- Precomposition as a `ℂ(Y)`-algebra automorphism of the function field. -/
def precompAlgEquiv (delta : SL(2, ℤ)) : FunctionField ≃ₐ[RatFunc ℂ] FunctionField :=
  AlgEquiv.ofRingEquiv (precomp_ratFunc delta)

private theorem conjugate_injective (m : ℕ+) :
    Function.Injective (fun sigma : CoxMatrix m ↦ fun tau : ℍ ↦ j (sigma.act tau)) := by
  intro sigma tau h
  apply transformedJSeries_injective m
  rw [← laurentqExpansion_coxAction m sigma, ← laurentqExpansion_coxAction m tau]
  exact congrArg (laurentqExpansion ((m : ℕ) : ℝ)) h

/-- The conjugate indexed by a right coset, bundled as a holomorphic function. -/
def rightCosetFunction (m : ℕ+) (c : Gamma0RightCosets m) : HolomorphicFunction :=
  ⟨rightCosetEval m c, rightCosetEval_mdifferentiable m c⟩

@[simp]
theorem rightCosetFunction_apply (m : ℕ+) (c : Gamma0RightCosets m) (τ : ℍ) :
    (rightCosetFunction m c).1 τ = rightCosetEval m c τ :=
  rfl

/-- Distinct right cosets give distinct holomorphic conjugates. -/
theorem rightCosetFunction_injective (m : ℕ+) : Function.Injective (rightCosetFunction m) := by
  intro c d hcd
  obtain ⟨sigma, rfl⟩ := (coxMatrixEquivRightCosets m).surjective c
  obtain ⟨tau, rfl⟩ := (coxMatrixEquivRightCosets m).surjective d
  have hst : sigma = tau := by
    apply conjugate_injective m
    funext z
    simpa [rightCosetFunction, rightCosetEval_equiv] using congrArg (·.1 z) hcd
  exact congrArg (coxMatrixEquivRightCosets m) hst

/-- A right-coset conjugate embedded in the function field. -/
def rightCosetRoot (m : ℕ+) (c : Gamma0RightCosets m) : FunctionField :=
  algebraMap HolomorphicFunction FunctionField (rightCosetFunction m c)

/-- Distinct right cosets remain distinct after embedding into the function field. -/
theorem rightCosetRoot_injective (m : ℕ+) : Function.Injective (rightCosetRoot m) :=
  holomorphicToMeromorphic_injective.comp (rightCosetFunction_injective m)

/-- Precomposition acts on conjugate roots by right multiplication of their cosets. -/
theorem precompAlgEquiv_rightCosetRoot (m : ℕ+) (delta : SL(2, ℤ))
    (c : Gamma0RightCosets m) :
    precompAlgEquiv delta (rightCosetRoot m c) =
      rightCosetRoot m (rightCosetMul m delta c) :=
  precomp_algebraMap_eq_of_forall delta _ _ (rightCosetEval_smul m delta c)

end UpperHalfPlaneFunctionField
end Cox
