/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import XYin.PhD.Cox.ModularPolynomial.Irreducibility
import XYin.PhD.Cox.ModularFunctionField

/-!
# The modular polynomial presents the Gamma-zero modular function field

The presentation below is defined solely by the polynomial `Φ_N`, over the independent
rational function field `RatFunc ℂ`. Its distinguished root is then identified with `j(Nτ)`
using the existing minimal-polynomial theorem. This is a function-field presentation; it does
not identify the possibly singular plane curve with a smooth modular curve.
-/

open UpperHalfPlane UpperHalfPlane.MeromorphicField
open Cox Cox.UpperHalfPlaneFunctionField
open scoped Polynomial.Bivariate

noncomputable section

namespace ModularPolynomialCurveTest

/-- The modular polynomial over the rational function field in its parameter variable. -/
def phiRat (N : ℕ+) : Polynomial (RatFunc ℂ) :=
  (modularPolynomialC N).map (algebraMap (Polynomial ℂ) (RatFunc ℂ))

instance phiRat_irreducible (N : ℕ+) : Fact (Irreducible (phiRat N)) :=
  ⟨irreducible_map_modularPolynomialC N⟩

/-- An independent field defined by adjoining a root of the modular polynomial. -/
abbrev PolynomialFunctionField (N : ℕ+) := AdjoinRoot (phiRat N)

/-- The relation really is the minimal polynomial of the analytic function `j(Nτ)`. -/
theorem phiRat_eq_minpoly (N : ℕ+) :
    phiRat N = minpoly (RatFunc ℂ) (levelJFieldElement N) := by
  rw [phiRat, modularPolynomialC_map_eq_minpoly, rightCosetRoot_baseRightCoset]

theorem levelJFieldElement_isIntegral (N : ℕ+) :
    IsIntegral (RatFunc ℂ) (levelJFieldElement N) :=
  minpoly.ne_zero_iff.mp ((phiRat_eq_minpoly N) ▸ (phiRat_irreducible N).out.ne_zero)

/-- The field presented by `Φ_N` is `ℂ(j)(j(Nτ))`, over `ℂ(j)`. -/
def polynomialJLevelEquiv (N : ℕ+) :
    PolynomialFunctionField N ≃ₐ[RatFunc ℂ] jLevelFunctionField N :=
  (AdjoinRoot.algEquivOfEq (RatFunc ℂ) (phiRat N)
    (minpoly (RatFunc ℂ) (levelJFieldElement N)) (phiRat_eq_minpoly N)).trans
    (IntermediateField.adjoinRootEquivAdjoin (RatFunc ℂ) (levelJFieldElement_isIntegral N))

/-- The distinguished polynomial root maps to the actual analytic `j(Nτ)`. -/
theorem polynomialJLevelEquiv_root (N : ℕ+) :
    (polynomialJLevelEquiv N (AdjoinRoot.root (phiRat N)) : MeromorphicField) =
      levelJFieldElement N := by
  simp only [polynomialJLevelEquiv, AlgEquiv.trans_apply, AdjoinRoot.algEquivOfEq_root]
  exact congrArg Subtype.val
    (IntermediateField.adjoinRootEquivAdjoin_apply_root (RatFunc ℂ)
      (levelJFieldElement_isIntegral N))

/-- The base coordinate maps to the ambient function `j`. -/
theorem polynomialJLevelEquiv_base_X (N : ℕ+) :
    (polynomialJLevelEquiv N
      (algebraMap (RatFunc ℂ) (PolynomialFunctionField N) RatFunc.X) : MeromorphicField) =
      algebraMap HolomorphicFunction MeromorphicField jElement := by
  rw [(polynomialJLevelEquiv N).commutes]
  change algebraMap (RatFunc ℂ) MeromorphicField RatFunc.X = _
  rw [algebraMap_ratFunc, ← RatFunc.algebraMap_X, ratFuncEvalJ_algebraMap, evalJFracPoly,
    RingHom.comp_apply, evalJ_X]

/-- This presentation has exactly the degree of the modular polynomial. -/
theorem polynomialFunctionField_finrank (N : ℕ+) :
    Module.finrank (RatFunc ℂ) (PolynomialFunctionField N) =
      Fintype.card (Gamma0RightCosets N) := by
  rw [show Module.finrank (RatFunc ℂ) (PolynomialFunctionField N) = (phiRat N).natDegree
    from finrank_quotient_span_eq_natDegree]
  rw [phiRat, (modularPolynomialC_monic N).natDegree_map, modularPolynomialC_natDegree]
  exact Fintype.card_congr (coxMatrixEquivRightCosets N)

/-- Every element of the simple extension is the germ of a Gamma-zero modular function. -/
theorem jLevel_isModular (N : ℕ+) (x : jLevelFunctionField N) :
    IsModular (CongruenceSubgroup.Gamma0 (N : ℕ)) (x : MeromorphicField) := by
  change (x : MeromorphicField) ∈ ModularFunction.subfield _
  rw [theorem_11_9_ii_subfield]
  exact x.property

/-- Recover the canonical modular-function representative of an element of `ℂ(j)(j_N)`. -/
def jLevelToModular (N : ℕ+) :
    jLevelFunctionField N →ₐ[ℂ] ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ)) where
  toFun x := ModularFunction.ofMeromorphicField x (jLevel_isModular N x)
  map_one' := ModularFunction.toMeromorphicField_injective (by simp)
  map_mul' _ _ := ModularFunction.toMeromorphicField_injective (by simp)
  map_zero' := ModularFunction.toMeromorphicField_injective (by simp)
  map_add' _ _ := ModularFunction.toMeromorphicField_injective (by simp)
  commutes' c := ModularFunction.toMeromorphicField_injective (by
    simp only [ModularFunction.toMeromorphicField_ofMeromorphicField,
      ModularFunction.toMeromorphicField_algebraMap]
    exact Subalgebra.coe_algebraMap (S := (jLevelFunctionField N).toSubalgebra) c)

@[simp]
theorem toMeromorphicField_jLevelToModular (N : ℕ+) (x : jLevelFunctionField N) :
    (jLevelToModular N x).toMeromorphicField = x :=
  ModularFunction.toMeromorphicField_ofMeromorphicField _ (jLevel_isModular N x)

theorem jLevelToModular_surjective (N : ℕ+) :
    Function.Surjective (jLevelToModular N) := by
  intro f
  refine ⟨⟨f.toMeromorphicField, toMeromorphicField_mem_jLevelFunctionField N f⟩, ?_⟩
  exact ModularFunction.toMeromorphicField_injective (toMeromorphicField_jLevelToModular ..)

/-- The simple extension is the field of the existing independently defined modular functions. -/
def jLevelModularEquiv (N : ℕ+) :
    jLevelFunctionField N ≃ₐ[ℂ] ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ)) :=
  AlgEquiv.ofBijective (jLevelToModular N)
    ⟨(jLevelToModular N).injective, jLevelToModular_surjective N⟩

/-- The polynomial presentation identifies with the bundled Gamma-zero modular function field. -/
def polynomialModularEquiv (N : ℕ+) :
    PolynomialFunctionField N ≃ₐ[ℂ] ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ)) :=
  ((polynomialJLevelEquiv N).restrictScalars ℂ).trans (jLevelModularEquiv N)

/-- The root coordinate maps to the bundled classical function `j(Nτ)`. -/
theorem polynomialModularEquiv_root (N : ℕ+) :
    polynomialModularEquiv N (AdjoinRoot.root (phiRat N)) = levelJModularFunction N := by
  apply ModularFunction.toMeromorphicField_injective
  rw [polynomialModularEquiv, AlgEquiv.trans_apply]
  change (jLevelToModular N _).toMeromorphicField = _
  rw [toMeromorphicField_jLevelToModular, toMeromorphicField_levelJModularFunction]
  exact polynomialJLevelEquiv_root N

/-- Rational coefficients are respected over the actual analytic function field. -/
example (N : ℕ+) (r : RatFunc ℂ) :
    (polynomialModularEquiv N
      (algebraMap (RatFunc ℂ) (PolynomialFunctionField N) r)).toMeromorphicField =
      algebraMap (RatFunc ℂ) MeromorphicField r := by
  change (jLevelToModular N _).toMeromorphicField = _
  rw [toMeromorphicField_jLevelToModular]
  change ((polynomialJLevelEquiv N)
    (algebraMap (RatFunc ℂ) (PolynomialFunctionField N) r) : MeromorphicField) = _
  rw [(polynomialJLevelEquiv N).commutes]
  rfl

/-- Polynomial arithmetic agrees with modular-function arithmetic. -/
example (N : ℕ+) (a b : PolynomialFunctionField N) :
    polynomialModularEquiv N (a / b) =
      polynomialModularEquiv N a / polynomialModularEquiv N b :=
  map_div₀ (polynomialModularEquiv N) a b

#print axioms phiRat_eq_minpoly
#print axioms polynomialJLevelEquiv
#print axioms polynomialJLevelEquiv_root
#print axioms polynomialFunctionField_finrank
#print axioms polynomialModularEquiv
#print axioms polynomialModularEquiv_root

end ModularPolynomialCurveTest
