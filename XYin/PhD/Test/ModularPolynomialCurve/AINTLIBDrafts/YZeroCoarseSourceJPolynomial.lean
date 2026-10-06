/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSourceJSurjective
public import Mathlib.Algebra.Polynomial.Roots

/-!
# The actual coarse source-j polynomial homomorphism is injective over ℂ

Evaluation uses the actual constant and variable pullback formulas. Surjectivity of
source-j values at actual coarse complex points then rules out any nonzero polynomial
relation in this single coordinate. No domain assumption on the invariant ring is used.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

local instance sourceJEvaluationInvariantAlgebra : Algebra ℂ
    (yZeroInvariantRing (R := .of ℂ) N hN (complexLevelIsUnit N)) :=
  yZeroInvariantAlgebra (R := .of ℂ) N hN (complexLevelIsUnit N)

theorem sourceJ_polynomial_eval (φ : yZeroComplexAlgebraPoint N hN) (f : Polynomial ℂ) :
    φ (yZeroJPolynomialHom (R := .of ℂ) N hN (complexLevelIsUnit N) f) =
      f.eval (φ (fineJInvariant (R := .of ℂ) N hN (complexLevelIsUnit N))) := by
  have h : φ.toRingHom.comp
      (yZeroJPolynomialHom (R := .of ℂ) N hN (complexLevelIsUnit N)) =
        Polynomial.evalRingHom
          (φ (fineJInvariant (R := .of ℂ) N hN (complexLevelIsUnit N))) := by
    apply Polynomial.ringHom_ext
    · intro z
      have hc := congrArg (fun u : CommRingCat.of ℂ ⟶
        yZeroInvariantRing (R := .of ℂ) N hN (complexLevelIsUnit N) ↦ u z)
        (yZeroJPolynomial_C (R := .of ℂ) N hN (complexLevelIsUnit N))
      change yZeroJPolynomialHom (R := .of ℂ) N hN (complexLevelIsUnit N)
        (Polynomial.C z) = algebraMap ℂ _ z at hc
      simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
      change φ (yZeroJPolynomialHom (R := .of ℂ) N hN (complexLevelIsUnit N)
        (Polynomial.C z)) = z
      rw [hc]
      exact φ.commutes z
    · simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X]
      change φ (yZeroJPolynomialHom (R := .of ℂ) N hN (complexLevelIsUnit N)
        Polynomial.X) = φ (fineJInvariant (R := .of ℂ) N hN (complexLevelIsUnit N))
      rw [yZeroJPolynomialHom_X]
  exact DFunLike.congr_fun h f

#print axioms sourceJ_polynomial_eval

/-- A polynomial relation in the actual source-j coordinate is trivial. -/
theorem yZeroJPolynomialHom_complex_injective :
    Function.Injective (yZeroJPolynomialHom (R := .of ℂ) N hN (complexLevelIsUnit N)) := by
  intro f g hfg
  have heval : ∀ z : ℂ, f.eval z = g.eval z := by
    intro z
    obtain ⟨φ, rfl⟩ := yZeroComplexInvariantJValue_surjective N hN z
    rw [← sourceJ_polynomial_eval, ← sourceJ_polynomial_eval]
    exact congrArg φ hfg
  apply Polynomial.eq_of_infinite_eval_eq f g
  simpa only [heval, Set.ofPred_true] using
    (Set.infinite_univ : Set.Infinite (Set.univ : Set ℂ))

/-- The actual source-j polynomial map detects the zero polynomial. -/
theorem yZeroJPolynomialHom_complex_eq_zero_iff (f : Polynomial ℂ) :
    yZeroJPolynomialHom (R := .of ℂ) N hN (complexLevelIsUnit N) f = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply yZeroJPolynomialHom_complex_injective N hN
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

#print axioms yZeroJPolynomialHom_complex_injective
#print axioms yZeroJPolynomialHom_complex_eq_zero_iff

example (f : Polynomial ℂ) :
    yZeroJPolynomialHom (R := .of ℂ) 3 (by decide) (complexLevelIsUnit 3) f = 0 ↔ f = 0 :=
  yZeroJPolynomialHom_complex_eq_zero_iff 3 (by decide) f

end ModularPolynomialCurveTest.AINTLIB
