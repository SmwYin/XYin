/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.AlgebraicGeometry.FunctionField
import XYin.PhD.Test.ModularPolynomialCurve.FractionField

/-!
# The actual scheme function field of the modular-polynomial plane curve

The scheme is independently `Spec (ℂ[X][Y] / (Φ_N))`. Its function field is mathlib's
stalk at the generic point, rather than a definition in terms of modular functions.
The two geometric coordinates become `j` and `j_N` under the resulting equivalence.
-/

open AlgebraicGeometry Polynomial UpperHalfPlane
open Cox Cox.UpperHalfPlaneFunctionField
open scoped Polynomial.Bivariate

noncomputable section

namespace ModularPolynomialCurveTest

instance planeFunctionFieldAlgebra (N : ℕ+) :
    Algebra (planeRing N) (planeScheme N).functionField :=
  instAlgebraCarrierFunctionFieldSpec (.of (planeRing N))

instance planeFunctionFieldIsFractionRing (N : ℕ+) :
    IsFractionRing (planeRing N) (planeScheme N).functionField :=
  functionField_isFractionRing_of_affine (.of (planeRing N))

instance planeFunctionFieldComplexAlgebra (N : ℕ+) :
    Algebra ℂ (planeScheme N).functionField :=
  ((algebraMap (planeRing N) (planeScheme N).functionField).comp
    (algebraMap ℂ (planeRing N))).toAlgebra

instance planeFunctionFieldComplexScalarTower (N : ℕ+) :
    IsScalarTower ℂ (planeRing N) (planeScheme N).functionField :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The generic-point stalk agrees with the independently constructed fraction ring. -/
def planeSchemeFractionEquiv (N : ℕ+) :
    (planeScheme N).functionField ≃ₐ[ℂ] PlaneFractionField N :=
  IsFractionRing.algEquivOfAlgEquiv (AlgEquiv.refl : planeRing N ≃ₐ[ℂ] planeRing N)

/-- The actual plane scheme's function field is the field of Gamma-zero modular functions. -/
def planeSchemeModularEquiv (N : ℕ+) :
    (planeScheme N).functionField ≃ₐ[ℂ]
      ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ)) :=
  (planeSchemeFractionEquiv N).trans (planeFractionModularEquiv N)

/-- The geometric root coordinate has its intended modular-function interpretation. -/
theorem planeSchemeModularEquiv_X (N : ℕ+) :
    planeSchemeModularEquiv N
      (algebraMap (planeRing N) (planeScheme N).functionField
        (Ideal.Quotient.mk (definingIdeal N) X)) = levelJModularFunction N := by
  rw [planeSchemeModularEquiv, AlgEquiv.trans_apply, planeSchemeFractionEquiv,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  exact planeFractionModularEquiv_X N

/-- The geometric parameter coordinate represents the actual analytic invariant `j`. -/
theorem planeSchemeModularEquiv_C_X (N : ℕ+) :
    (planeSchemeModularEquiv N
      (algebraMap (planeRing N) (planeScheme N).functionField
        (Ideal.Quotient.mk (definingIdeal N) (C X)))).toMeromorphicField =
      algebraMap HolomorphicFunction MeromorphicField jElement := by
  rw [planeSchemeModularEquiv, AlgEquiv.trans_apply, planeSchemeFractionEquiv,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  exact planeFractionModularEquiv_C_X N

/-- The geometric parameter is the restriction of the classical bundled `j` function. -/
theorem planeSchemeModularEquiv_C_X_restrict (N : ℕ+) :
    planeSchemeModularEquiv N
      (algebraMap (planeRing N) (planeScheme N).functionField
        (Ideal.Quotient.mk (definingIdeal N) (C X))) =
      jModularFunction.restrict (Subgroup.map_le_range ..) := by
  apply ModularFunction.toMeromorphicField_injective
  rw [planeSchemeModularEquiv_C_X]
  symm
  exact ModularFunction.toMeromorphicField_eq_iff.2 (by simp [jElement])

example (N : ℕ+) (c : ℂ) :
    planeSchemeModularEquiv N (algebraMap ℂ (planeScheme N).functionField c) =
      algebraMap ℂ (ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ))) c :=
  (planeSchemeModularEquiv N).commutes c

example (N : ℕ+) (f : (planeScheme N).functionField) :
    (planeSchemeModularEquiv N).symm (planeSchemeModularEquiv N f) = f :=
  (planeSchemeModularEquiv N).symm_apply_apply f

#print axioms planeFunctionFieldIsFractionRing
#print axioms planeSchemeModularEquiv
#print axioms planeSchemeModularEquiv_X
#print axioms planeSchemeModularEquiv_C_X
#print axioms planeSchemeModularEquiv_C_X_restrict

end ModularPolynomialCurveTest
