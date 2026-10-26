/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.FieldTheory.Minpoly.Field
import XYin.PhD.Cox.ModularPolynomial.Construction
import XYin.PhD.Cox.UpperHalfPlaneFunctionField

/-!
# Irreducibility of Cox's modular polynomial

This file proves irreducibility of the complex modular polynomial in its root variable (the
outer variable of `ℂ[X][Y]`) over Cox's `ℂ(Y)`, the rational function field `RatFunc ℂ` of the
parameter: `Φ_m` is the minimal polynomial over `RatFunc ℂ` of the conjugate `j(mτ)`, because it
has as many distinct conjugates `j(mγτ)` as its degree.
-/

open Complex Function MatrixGroups ModularForm UpperHalfPlane
open scoped Manifold Polynomial.Bivariate

noncomputable section

namespace Cox

section Irreducibility

open UpperHalfPlaneFunctionField

private theorem modularPolynomialHolomorphic_eq_product (m : ℕ+) :
    Polynomial.map evalJ (modularPolynomialC m) =
      ∏ c : Gamma0RightCosets m,
        (Polynomial.X - Polynomial.C (rightCosetFunction m c)) := by
  classical
  ext n : 1
  refine HolomorphicFunction.ext fun tau ↦ ?_
  have h := congrArg (fun p : Polynomial ℂ ↦ p.coeff n)
    (modularPolynomialC_rightCosetProduct m tau)
  rw [Polynomial.coeff_map, evalJ_apply, ← evaluation_apply, ← Polynomial.coeff_map]
  simpa [Polynomial.coeff_map, Polynomial.map_prod] using h

private abbrev modularPolynomialRatFunc (m : ℕ+) : Polynomial (RatFunc ℂ) :=
  Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
    (modularPolynomialC m)

private abbrev modularPolynomialFunctionField (m : ℕ+) : Polynomial MeromorphicField :=
  Polynomial.map (algebraMap (RatFunc ℂ) MeromorphicField) (modularPolynomialRatFunc m)

private theorem modularPolynomialFunctionField_eq_map (m : ℕ+) :
    modularPolynomialFunctionField m =
      Polynomial.map (algebraMap HolomorphicFunction MeromorphicField)
        (Polynomial.map evalJ (modularPolynomialC m)) := by
  apply Polynomial.ext
  intro n
  simp only [modularPolynomialFunctionField, modularPolynomialRatFunc, Polynomial.coeff_map]
  exact ratFuncEvalJ_algebraMap _

private theorem modularPolynomialFunctionField_eq_product (m : ℕ+) :
    modularPolynomialFunctionField m =
      ∏ c : Gamma0RightCosets m,
        (Polynomial.X - Polynomial.C (rightCosetRoot m c)) := by
  classical
  rw [modularPolynomialFunctionField_eq_map,
    modularPolynomialHolomorphic_eq_product, Polynomial.map_prod]
  simp [rightCosetRoot]

private theorem modularPolynomialRatFunc_aeval_base (m : ℕ+) :
    Polynomial.aeval (rightCosetRoot m (baseRightCoset m))
      (modularPolynomialRatFunc m) = 0 := by
  rw [Polynomial.aeval_def, ← Polynomial.eval_map,
    show Polynomial.map (algebraMap (RatFunc ℂ) MeromorphicField)
      (modularPolynomialRatFunc m) = modularPolynomialFunctionField m from rfl,
    modularPolynomialFunctionField_eq_product, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (baseRightCoset m))
  simp

private theorem minpoly_aeval_rightCosetRoot (m : ℕ+) (c : Gamma0RightCosets m) :
    Polynomial.aeval (rightCosetRoot m c)
      (minpoly (RatFunc ℂ) (rightCosetRoot m (baseRightCoset m))) = 0 := by
  obtain ⟨delta, hdelta⟩ := exists_rightCosetMul_baseRightCoset_eq m c
  simpa only [AlgEquiv.coe_algHom, precompAlgEquiv_rightCosetRoot, hdelta] using
    minpoly.aeval_algHom (RatFunc ℂ) (precompAlgEquiv delta).toAlgHom
      (rightCosetRoot m (baseRightCoset m))

/-- A nonzero polynomial over a field vanishing at `card ι` distinct points of a domain has
degree at least `card ι`. -/
private lemma card_le_natDegree_of_injective_roots
    {F E ι : Type*} [Field F] [CommRing E] [IsDomain E] [Algebra F E] [Fintype ι]
    {p : Polynomial F} (hp : p ≠ 0) (conjugate : ι → E)
    (hinjective : Function.Injective conjugate)
    (hroots : ∀ i, Polynomial.aeval (conjugate i) p = 0) :
    Fintype.card ι ≤ p.natDegree := by
  rw [← Polynomial.natDegree_map (algebraMap F E)]
  by_contra hdegree
  exact Polynomial.map_ne_zero hp <|
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinjective
      (fun i ↦ by simpa [Polynomial.aeval_def, Polynomial.eval_map] using hroots i)
      (Nat.lt_of_not_ge hdegree)

/-- A monic polynomial vanishing at `α` whose degree is at most the number of distinct roots of
the minimal polynomial of `α` is that minimal polynomial. -/
private lemma eq_minpoly_of_card_conjugates
    {F E ι : Type*} [Field F] [CommRing E] [IsDomain E] [Algebra F E] [Fintype ι]
    {p : Polynomial F} (hp : p.Monic) {α : E} (hα : Polynomial.aeval α p = 0)
    (conjugate : ι → E) (hinjective : Function.Injective conjugate)
    (hroots : ∀ i, Polynomial.aeval (conjugate i) (minpoly F α) = 0)
    (hdegree : p.natDegree ≤ Fintype.card ι) : p = minpoly F α := by
  have hmin := minpoly.ne_zero (show IsIntegral F α from ⟨p, hp, hα⟩)
  refine minpoly.unique_of_degree_le_degree_minpoly F α hp hα ?_
  rw [Polynomial.degree_eq_natDegree hp.ne_zero, Polynomial.degree_eq_natDegree hmin]
  exact_mod_cast hdegree.trans
    (card_le_natDegree_of_injective_roots hmin conjugate hinjective hroots)

/-- Over `RatFunc ℂ` (Cox's `ℂ(Y)`), `Φ_m` is the minimal polynomial of the conjugate `j(mτ)`
attached to the identity coset. -/
theorem modularPolynomialC_map_eq_minpoly (m : ℕ+) :
    Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (modularPolynomialC m) =
      minpoly (RatFunc ℂ) (rightCosetRoot m (baseRightCoset m)) := by
  refine eq_minpoly_of_card_conjugates ((modularPolynomialC_monic m).map _)
    (modularPolynomialRatFunc_aeval_base m) (rightCosetRoot m) (rightCosetRoot_injective m)
    (minpoly_aeval_rightCosetRoot m) (le_of_eq ?_)
  rw [(modularPolynomialC_monic m).natDegree_map, modularPolynomialC_natDegree]
  exact Fintype.card_congr (coxMatrixEquivRightCosets m)

/-- Exercise 11.10 / Theorem 11.18(ii), function-field form: `Φ_m` is irreducible in the
root variable (Cox's `X`, the outer variable) over `RatFunc ℂ` (Cox's `ℂ(Y)`). -/
theorem irreducible_map_modularPolynomialC (m : ℕ+) :
    Irreducible (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      (modularPolynomialC m)) :=
  modularPolynomialC_map_eq_minpoly m ▸ minpoly.irreducible
    ⟨_, (modularPolynomialC_monic m).map _, modularPolynomialRatFunc_aeval_base m⟩

end Irreducibility

end Cox
