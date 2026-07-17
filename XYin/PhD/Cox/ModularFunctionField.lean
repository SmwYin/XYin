/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

import XYin.PhD.Cox.ModularPolynomial.Interpolation

/-!
# The bundled modular function field for `Γ₀(N)`

This file upgrades Cox Theorem 11.9(ii) from a guarded pointwise rational expression to an
equality of intermediate fields inside the fraction field of holomorphic functions on the upper
half-plane.
-/

open UpperHalfPlane
open scoped Manifold Polynomial.Bivariate

noncomputable section

namespace Cox
namespace UpperHalfPlaneFunctionField

/-- The function `τ ↦ j(Nτ)` is holomorphic on the upper half-plane. -/
theorem levelJ_mdifferentiable (N : ℕ+) : MDiff (levelJ N) :=
  UpperHalfPlane.mdifferentiable_iff.mpr fun z hz ↦
    (jN_Meromorphic (N : ℕ) (z := ⟨z, hz⟩)).differentiableWithinAt

/-- The function `j(Nτ)`, bundled as a holomorphic function. -/
def levelJElement (N : ℕ+) : HolomorphicFunction :=
  ⟨levelJ N, levelJ_mdifferentiable N⟩

/-- Evaluate a bivariate complex polynomial at the holomorphic functions `j` and `j_N`. -/
def evalJLevelHol (N : ℕ+) : ℂ[X][Y] →+* HolomorphicFunction :=
  Polynomial.eval₂RingHom evalJ (levelJElement N)

/-- Pointwise, bundled bivariate evaluation substitutes analytic `j` and `j(Nτ)`. -/
@[simp]
theorem evalJLevelHol_apply (N : ℕ+) (P : ℂ[X][Y]) (τ : ℍ) :
    (evalJLevelHol N P).1 τ = P.evalEval (j τ) (levelJ N τ) := by
  change evaluation τ (Polynomial.eval₂ evalJ (levelJElement N) P) = _
  rw [Polynomial.hom_eval₂]
  have heval : (evaluation τ).comp evalJ = Polynomial.evalRingHom (j τ) := by
    apply Polynomial.ringHom_ext
    · intro z
      change (evalJ (Polynomial.C z)).1 τ = _
      rw [evalJ_apply]
      simp
    · change (evalJ Polynomial.X).1 τ = _
      rw [evalJ_apply]
      simp
  rw [heval, Polynomial.eval₂_evalRingHom]
  rfl

/-- Bivariate evaluation in the ambient analytic function field. -/
def evalJLevel (N : ℕ+) : ℂ[X][Y] →+* FunctionField :=
  (algebraMap HolomorphicFunction FunctionField).comp (evalJLevelHol N)

/-- The ambient function-field element represented by `j(Nτ)`. -/
def levelJFieldElement (N : ℕ+) : FunctionField :=
  algebraMap HolomorphicFunction FunctionField (levelJElement N)

/-- A raw meromorphic function represents an element of the analytic fraction field. -/
def Represents (f : ℍ → ℂ) (x : FunctionField) : Prop :=
  ∃ a b : HolomorphicFunction, b ≠ 0 ∧
    x = algebraMap HolomorphicFunction FunctionField a /
      algebraMap HolomorphicFunction FunctionField b ∧
    ∀ τ : ℍ, b.1 τ ≠ 0 → f τ = a.1 τ / b.1 τ

/-- A holomorphic function represents its image under the fraction-field map. -/
theorem represents_algebraMap (a : HolomorphicFunction) :
    Represents a.1 (algebraMap HolomorphicFunction FunctionField a) := by
  refine ⟨a, 1, one_ne_zero, by simp, ?_⟩
  simp

/-- A meromorphic function has at most one representative in the analytic fraction field. -/
theorem represents_unique {f : ℍ → ℂ} {x y : FunctionField}
    (hx : Represents f x) (hy : Represents f y) : x = y := by
  rcases hx with ⟨a, b, hb, rfl, hab⟩
  rcases hy with ⟨c, d, hd, rfl, hcd⟩
  have hcross : a * d = c * b := by
    have hzero : (a * d - c * b) * (b * d) = 0 := by
      apply Subtype.ext
      funext τ
      change (a.1 τ * d.1 τ - c.1 τ * b.1 τ) * (b.1 τ * d.1 τ) = 0
      by_cases hbτ : b.1 τ = 0
      · simp [hbτ]
      by_cases hdτ : d.1 τ = 0
      · simp [hdτ]
      have hratio : a.1 τ / b.1 τ = c.1 τ / d.1 τ :=
        (hab τ hbτ).symm.trans (hcd τ hdτ)
      have hcrossτ : a.1 τ * d.1 τ = c.1 τ * b.1 τ :=
        (div_eq_div_iff hbτ hdτ).mp hratio
      rw [hcrossτ, sub_self, zero_mul]
    rcases mul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exact (mul_ne_zero hb hd h).elim
  have hbmap : algebraMap HolomorphicFunction FunctionField b ≠ 0 :=
    fun h ↦ hb (IsFractionRing.to_map_eq_zero_iff.mp h)
  have hdmap : algebraMap HolomorphicFunction FunctionField d ≠ 0 :=
    fun h ↦ hd (IsFractionRing.to_map_eq_zero_iff.mp h)
  apply (div_eq_div_iff hbmap hdmap).mpr
  simpa using congrArg (algebraMap HolomorphicFunction FunctionField) hcross

/-- A guarded pointwise rational expression gives the corresponding fraction-field
representation. -/
theorem represents_evalJLevel_of (N : ℕ+) {f : ℍ → ℂ} (P Q : ℂ[X][Y])
    (hQ : (fun τ : ℍ ↦ Q.evalEval (j τ) (levelJ N τ)) ≠ 0)
    (hf : ∀ τ : ℍ, Q.evalEval (j τ) (levelJ N τ) ≠ 0 →
      f τ = P.evalEval (j τ) (levelJ N τ) /
        Q.evalEval (j τ) (levelJ N τ)) :
    Represents f (evalJLevel N P / evalJLevel N Q) := by
  refine ⟨evalJLevelHol N P, evalJLevelHol N Q, ?_, ?_, ?_⟩
  · intro hzero
    apply hQ
    funext τ
    simpa only [evalJLevelHol_apply, Subring.coe_zero, Pi.zero_apply] using
      congrArg (fun g : HolomorphicFunction ↦ g.1 τ) hzero
  · rfl
  · intro τ hden
    simp only [evalJLevelHol_apply] at hden ⊢
    exact hf τ hden

/-- Ambient representatives of all level-`N` modular functions. -/
def modularRepresentatives (N : ℕ+) : Set FunctionField :=
  {x | ∃ f : ℍ → ℂ, IsGamma0ModularFunction N f ∧ Represents f x}

/-- The bundled field of level-`N` modular functions, over the existing copy of `ℂ(j)`. -/
def gamma0ModularFunctionField (N : ℕ+) :
    IntermediateField (RatFunc ℂ) FunctionField :=
  IntermediateField.adjoin (RatFunc ℂ) (modularRepresentatives N)

/-- The simple extension `ℂ(j)(j(Nτ))` in the same ambient function field. -/
def jLevelFunctionField (N : ℕ+) : IntermediateField (RatFunc ℂ) FunctionField :=
  IntermediateField.adjoin (RatFunc ℂ) {levelJFieldElement N}

/-- Every bivariate polynomial in `j` and `j_N` belongs to `ℂ(j)(j_N)`. -/
theorem evalJLevel_mem_jLevelFunctionField (N : ℕ+) (P : ℂ[X][Y]) :
    evalJLevel N P ∈ jLevelFunctionField N := by
  change algebraMap HolomorphicFunction FunctionField
      (Polynomial.eval₂ evalJ (levelJElement N) P) ∈ jLevelFunctionField N
  rw [Polynomial.hom_eval₂]
  change Polynomial.eval₂ evalJFracPoly (levelJFieldElement N) P ∈
    jLevelFunctionField N
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.eval₂_add]
      exact (jLevelFunctionField N).add_mem hP hQ
  | monomial n p =>
      rw [Polynomial.eval₂_monomial]
      apply (jLevelFunctionField N).mul_mem
      · rw [← ratFuncEvalJ_algebraMap]
        exact (jLevelFunctionField N).algebraMap_mem _
      · exact (jLevelFunctionField N).pow_mem
          (IntermediateField.subset_adjoin (RatFunc ℂ) {levelJFieldElement N}
            (Set.mem_singleton _)) n

end UpperHalfPlaneFunctionField

open UpperHalfPlaneFunctionField

/-- Cox Theorem 11.9(ii), as an equality of bundled analytic function fields. -/
theorem theorem_11_9_ii (N : ℕ+) :
    gamma0ModularFunctionField N = jLevelFunctionField N := by
  apply le_antisymm
  · rw [gamma0ModularFunctionField, IntermediateField.adjoin_le_iff]
    rintro x ⟨f, hf, hx⟩
    obtain ⟨P, Q, hQ, hPQ⟩ := theorem_11_9_ii_pointwise N hf
    rw [represents_unique hx (represents_evalJLevel_of N P Q hQ hPQ)]
    exact (jLevelFunctionField N).div_mem
      (evalJLevel_mem_jLevelFunctionField N P)
      (evalJLevel_mem_jLevelFunctionField N Q)
  · rw [jLevelFunctionField, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin (RatFunc ℂ) (modularRepresentatives N)
      ⟨levelJ N, levelJ_isGamma0ModularFunction N,
        represents_algebraMap (levelJElement N)⟩

end Cox
