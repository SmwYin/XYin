/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Test.ModularPolynomialCurve.PlaneModel
import XYin.PhD.Test.ModularPolynomialCurve.FieldPresentation

/-!
# The fraction field of the independent modular-polynomial plane curve

This file identifies the fraction field of `ℂ[X][Y] / (Φ_N)` with the independently
defined bundled field of modular functions for `Γ₀(N)`. The maps preserve both coordinates.
The statement is about function fields, and makes no smoothness or moduli identification.
-/

open Polynomial UpperHalfPlane UpperHalfPlane.MeromorphicField
open Cox Cox.UpperHalfPlaneFunctionField
open scoped Polynomial.Bivariate

noncomputable section

namespace ModularPolynomialCurveTest

/-- The fraction field of the independently defined plane coordinate ring. -/
abbrev PlaneFractionField (N : ℕ+) := FractionRing (planeRing N)

theorem evalJLevel_C (N : ℕ+) (P : Polynomial ℂ) :
    evalJLevel N (C P) = evalJFracPoly P := by
  simp [evalJLevel, evalJLevelHol, evalJFracPoly]

theorem evalJLevel_X (N : ℕ+) : evalJLevel N X = levelJFieldElement N := by
  simp [evalJLevel, evalJLevelHol, levelJFieldElement]

/-- Evaluation of the coordinate ring, as a complex algebra homomorphism. -/
def planeEmbeddingAlgHom (N : ℕ+) : planeRing N →ₐ[ℂ] MeromorphicField where
  __ := planeEmbedding N
  commutes' c := by
    change planeEmbedding N (Ideal.Quotient.mk (definingIdeal N) (C (C c))) = _
    rw [planeEmbedding_mk, evalJLevel_C]
    simp only [evalJFracPoly, RingHom.comp_apply, evalJ_C]
    exact (IsScalarTower.algebraMap_apply ℂ HolomorphicFunction MeromorphicField c).symm

/-- The injective coordinate map extends to the fraction field. -/
def planeFractionEmbedding (N : ℕ+) : PlaneFractionField N →ₐ[ℂ] MeromorphicField :=
  IsFractionRing.liftAlgHom (g := planeEmbeddingAlgHom N) (planeEmbedding_injective N)

@[simp]
theorem planeFractionEmbedding_algebraMap (N : ℕ+) (a : planeRing N) :
    planeFractionEmbedding N (algebraMap (planeRing N) (PlaneFractionField N) a) =
      planeEmbedding N a :=
  IsFractionRing.lift_algebraMap (planeEmbedding_injective N) a

/-- Taking fractions of polynomial evaluations generates exactly `ℂ(j)(j_N)`. -/
theorem planeFractionEmbedding_fieldRange (N : ℕ+) :
    (planeFractionEmbedding N).toRingHom.fieldRange = (jLevelFunctionField N).toSubfield := by
  rw [planeFractionEmbedding, IsFractionRing.liftAlgHom_toRingHom,
    IsFractionRing.lift_fieldRange]
  change Subfield.closure (planeEmbedding N).range = (jLevelFunctionField N).toSubfield
  apply le_antisymm
  · refine Subfield.closure_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [planeEmbedding_mk]
    exact evalJLevel_mem_jLevelFunctionField N P
  · rw [jLevelFunctionField, IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.mpr (Set.union_subset ?_ ?_)
    · rintro _ ⟨r, rfl⟩
      have hpoly (P : Polynomial ℂ) :
          evalJFracPoly P ∈ Subfield.closure (planeEmbedding N).range := by
        refine Subfield.subset_closure ⟨Ideal.Quotient.mk (definingIdeal N) (C P), ?_⟩
        rw [planeEmbedding_mk, evalJLevel_C]
      induction r using RatFunc.induction_on with
      | f p q _ =>
        simpa only [map_div₀, algebraMap_ratFunc, ratFuncEvalJ_algebraMap] using
          div_mem (hpoly p) (hpoly q)
    · refine Set.singleton_subset_iff.mpr ?_
      refine Subfield.subset_closure ⟨Ideal.Quotient.mk (definingIdeal N) X, ?_⟩
      rw [planeEmbedding_mk, evalJLevel_X]

/-- The fraction field maps to its actual simple extension inside meromorphic functions. -/
def planeFractionToJLevel (N : ℕ+) : PlaneFractionField N →ₐ[ℂ] jLevelFunctionField N where
  toFun f := ⟨planeFractionEmbedding N f,
    (by
      change planeFractionEmbedding N f ∈ (jLevelFunctionField N).toSubfield
      rw [← planeFractionEmbedding_fieldRange]
      exact ⟨f, rfl⟩)⟩
  map_one' := Subtype.ext ((planeFractionEmbedding N).map_one)
  map_mul' _ _ := Subtype.ext ((planeFractionEmbedding N).map_mul _ _)
  map_zero' := Subtype.ext ((planeFractionEmbedding N).map_zero)
  map_add' _ _ := Subtype.ext ((planeFractionEmbedding N).map_add _ _)
  commutes' c := Subtype.ext (by
    change planeFractionEmbedding N (algebraMap ℂ (PlaneFractionField N) c) =
      (algebraMap ℂ (jLevelFunctionField N) c : MeromorphicField)
    exact ((planeFractionEmbedding N).commutes c).trans
      (Subalgebra.coe_algebraMap (S := (jLevelFunctionField N).toSubalgebra) c).symm)

theorem planeFractionToJLevel_surjective (N : ℕ+) :
    Function.Surjective (planeFractionToJLevel N) := by
  intro f
  have hf : (f : MeromorphicField) ∈ (planeFractionEmbedding N).toRingHom.fieldRange :=
    (planeFractionEmbedding_fieldRange N).symm ▸ f.property
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, Subtype.ext ha⟩

/-- The plane curve's fraction field is `ℂ(j)(j_N)`. -/
def planeFractionJLevelEquiv (N : ℕ+) :
    PlaneFractionField N ≃ₐ[ℂ] jLevelFunctionField N :=
  AlgEquiv.ofBijective (planeFractionToJLevel N)
    ⟨(planeFractionToJLevel N).injective, planeFractionToJLevel_surjective N⟩

/-- The actual plane model has the field of Gamma-zero modular functions as its function field. -/
def planeFractionModularEquiv (N : ℕ+) :
    PlaneFractionField N ≃ₐ[ℂ] ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ)) :=
  (planeFractionJLevelEquiv N).trans (jLevelModularEquiv N)

@[simp]
theorem toMeromorphicField_planeFractionModularEquiv (N : ℕ+) (f : PlaneFractionField N) :
    (planeFractionModularEquiv N f).toMeromorphicField = planeFractionEmbedding N f :=
  toMeromorphicField_jLevelToModular ..

/-- The root coordinate becomes the classical function `j(Nτ)`. -/
theorem planeFractionModularEquiv_X (N : ℕ+) :
    planeFractionModularEquiv N
      (algebraMap (planeRing N) (PlaneFractionField N)
        (Ideal.Quotient.mk (definingIdeal N) X)) = levelJModularFunction N := by
  apply ModularFunction.toMeromorphicField_injective
  rw [toMeromorphicField_planeFractionModularEquiv, planeFractionEmbedding_algebraMap,
    planeEmbedding_mk, evalJLevel_X, toMeromorphicField_levelJModularFunction]

/-- The parameter coordinate becomes the meromorphic field element represented by `j`. -/
theorem planeFractionModularEquiv_C_X (N : ℕ+) :
    (planeFractionModularEquiv N
      (algebraMap (planeRing N) (PlaneFractionField N)
        (Ideal.Quotient.mk (definingIdeal N) (C X)))).toMeromorphicField =
      algebraMap HolomorphicFunction MeromorphicField jElement := by
  rw [toMeromorphicField_planeFractionModularEquiv, planeFractionEmbedding_algebraMap,
    planeEmbedding_mk, evalJLevel_C]
  simp [evalJFracPoly, evalJ_X]

#print axioms planeFractionEmbedding_fieldRange
#print axioms planeFractionModularEquiv
#print axioms planeFractionModularEquiv_X

end ModularPolynomialCurveTest
