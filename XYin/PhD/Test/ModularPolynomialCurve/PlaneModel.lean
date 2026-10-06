/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.Quotient.Operations
import XYin.PhD.Cox.CyclicSublattice.Classification
import XYin.PhD.Cox.ModularPolynomial.Irreducibility
import XYin.PhD.Cox.ModularFunctionField

/-!
# The plane curve defined by the modular polynomial

The coordinate ring is defined independently as `ℂ[X][Y] / (Φ_N)`. Evaluation at
`(j, j_N)` has exactly the defining principal ideal as its kernel, so this ring
embeds in the ambient meromorphic field and its spectrum is integral.

This is the plane model. No identification with AINTLIB's coarse moduli quotient,
or with its normalization, is made here.
-/

open AlgebraicGeometry Polynomial UpperHalfPlane
open scoped Polynomial.Bivariate

noncomputable section

namespace ModularPolynomialCurveTest

open Cox Cox.UpperHalfPlaneFunctionField

/-- All polynomial relations between `j` and `j_N` are multiples of `Φ_N`. -/
theorem evalJLevel_eq_zero_iff (N : ℕ+) (P : ℂ[X][Y]) :
    evalJLevel N P = 0 ↔ modularPolynomialC N ∣ P := by
  rw [evalJLevel_eq_aeval, ← rightCosetRoot_baseRightCoset,
    ← minpoly.dvd_iff, ← modularPolynomialC_map_eq_minpoly]
  exact Polynomial.map_dvd_map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
    (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)) (modularPolynomialC_monic N)

/-- The principal ideal cutting out the modular-polynomial plane curve. -/
def definingIdeal (N : ℕ+) : Ideal ℂ[X][Y] :=
  Ideal.span {modularPolynomialC N}

theorem definingIdeal_eq_ker (N : ℕ+) :
    definingIdeal N = RingHom.ker (evalJLevel N) := by
  ext P
  rw [definingIdeal, Ideal.mem_span_singleton, RingHom.mem_ker, evalJLevel_eq_zero_iff]

instance definingIdeal_isPrime (N : ℕ+) : (definingIdeal N).IsPrime := by
  rw [definingIdeal_eq_ker]
  exact RingHom.ker_isPrime (evalJLevel N)

/-- The actual coordinate ring of the plane model, not a renamed modular-function ring. -/
abbrev planeRing (N : ℕ+) := ℂ[X][Y] ⧸ definingIdeal N

instance planeRing_isDomain (N : ℕ+) : IsDomain (planeRing N) := inferInstance

/-- Evaluation descends from the independently defined coordinate ring. -/
def planeEmbedding (N : ℕ+) : planeRing N →+* MeromorphicField :=
  Ideal.Quotient.lift (definingIdeal N) (evalJLevel N)
    (fun _ hP ↦ RingHom.mem_ker.mp (definingIdeal_eq_ker N ▸ hP))

theorem planeEmbedding_injective (N : ℕ+) : Function.Injective (planeEmbedding N) := by
  apply RingHom.lift_injective_of_ker_le_ideal
  exact le_of_eq (definingIdeal_eq_ker N).symm

@[simp]
theorem planeEmbedding_mk (N : ℕ+) (P : ℂ[X][Y]) :
    planeEmbedding N (Ideal.Quotient.mk (definingIdeal N) P) = evalJLevel N P :=
  Ideal.Quotient.lift_mk ..

/-- The independent affine scheme cut out by the modular polynomial. -/
def planeScheme (N : ℕ+) : Scheme := Spec (.of (planeRing N))

instance planeScheme_isIntegral (N : ℕ+) : IsIntegral (planeScheme N) := by
  change IsIntegral (Spec (.of (planeRing N)))
  infer_instance

/-- Complex points of the plane equation, with base `j` first and isogenous `j` second. -/
def planePoints (N : ℕ+) := {p : ℂ × ℂ // (modularPolynomialC N).evalEval p.1 p.2 = 0}

/-- The existing lattice classification describes exactly the plane equation's zero set. -/
theorem mem_planePoints_iff (N : ℕ+) (v u : ℂ) :
    (modularPolynomialC N).evalEval v u = 0 ↔
      ∃ L : PeriodPair, ∃ S : PeriodPair.CyclicSublattice L N,
        u = S.j ∧ v = L.j := by
  simpa only [modularPolynomial_map_complex] using theorem_11_23 N u v

/-- The analytic parametrization lands in the independently defined plane equation. -/
def jPair (N : ℕ+) (τ : ℍ) : planePoints N :=
  ⟨(j τ, levelJ N τ), modularPolynomialC_evalEval_j_levelJ N τ⟩

example (N : ℕ+) : IsDomain (planeRing N) := inferInstance
example (N : ℕ+) : IsIntegral (planeScheme N) := inferInstance

#print axioms evalJLevel_eq_zero_iff
#print axioms definingIdeal_isPrime
#print axioms planeEmbedding_injective
#print axioms planeScheme_isIntegral
#print axioms mem_planePoints_iff

end ModularPolynomialCurveTest
