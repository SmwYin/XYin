/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.FieldTheory.Minpoly.Field
import XYin.PhD.Cox.ModularPolynomial.Construction
import XYin.PhD.Cox.UpperHalfPlaneFunctionField

/-!
# Irreducibility of Cox's modular polynomial

This file proves irreducibility of the complex modular polynomial in its root variable over
`ℂ(Y)`.
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
  apply Polynomial.ext
  intro n
  apply Subtype.ext
  funext tau
  have h := congrArg (fun p : Polynomial ℂ ↦ p.coeff n)
    (modularPolynomialC_rightCosetProduct m tau)
  rw [Polynomial.coeff_map, evalJ_apply]
  change _ = evaluation tau ((∏ c : Gamma0RightCosets m,
    (Polynomial.X - Polynomial.C (rightCosetFunction m c))).coeff n)
  rw [← Polynomial.coeff_map]
  simpa [BivariatePolynomial.specializeY, Polynomial.coeff_map,
    Polynomial.map_prod, rightCosetFunction] using h

private abbrev modularPolynomialRatFunc (m : ℕ+) : Polynomial (RatFunc ℂ) :=
  Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
    (modularPolynomialC m)

private abbrev modularPolynomialFunctionField (m : ℕ+) : Polynomial FunctionField :=
  Polynomial.map (algebraMap (RatFunc ℂ) FunctionField) (modularPolynomialRatFunc m)

private theorem modularPolynomialFunctionField_eq_map (m : ℕ+) :
    modularPolynomialFunctionField m =
      Polynomial.map (algebraMap HolomorphicFunction FunctionField)
        (Polynomial.map evalJ (modularPolynomialC m)) := by
  calc
    modularPolynomialFunctionField m =
        Polynomial.map evalJFracPoly (modularPolynomialC m) := by
      apply Polynomial.ext
      intro n
      rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map]
      exact ratFuncEvalJ_algebraMap _
    _ = Polynomial.map (algebraMap HolomorphicFunction FunctionField)
        (Polynomial.map evalJ (modularPolynomialC m)) := by
      rw [Polynomial.map_map]
      rfl

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
    show Polynomial.map (algebraMap (RatFunc ℂ) FunctionField)
      (modularPolynomialRatFunc m) = modularPolynomialFunctionField m from rfl,
    modularPolynomialFunctionField_eq_product, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (baseRightCoset m))
  simp

private theorem minpoly_aeval_rightCosetRoot (m : ℕ+) (c : Gamma0RightCosets m) :
    Polynomial.aeval (rightCosetRoot m c)
      (minpoly (RatFunc ℂ) (rightCosetRoot m (baseRightCoset m))) = 0 := by
  obtain ⟨delta, hdelta⟩ := exists_rightCosetMul_baseRightCoset_eq m c
  have h := minpoly.aeval_algHom (RatFunc ℂ) (precompAlgEquiv delta).toAlgHom
    (rightCosetRoot m (baseRightCoset m))
  have he : (precompAlgEquiv delta).toAlgHom (rightCosetRoot m (baseRightCoset m)) =
      rightCosetRoot m c := by
    change precompAlgEquiv delta (rightCosetRoot m (baseRightCoset m)) = _
    rw [precompAlgEquiv_rightCosetRoot, hdelta]
  simpa only [he] using h

private lemma card_le_minpoly_natDegree_of_injective_roots
    {F E iota : Type*} [Field F] [CommRing E] [IsDomain E] [Algebra F E] [Fintype iota]
    {alpha : E} (halphaIntegral : IsIntegral F alpha)
    (conjugate : iota → E) (hinjective : Function.Injective conjugate)
    (hroots : ∀ i, Polynomial.aeval (conjugate i) (minpoly F alpha) = 0) :
    Fintype.card iota ≤ (minpoly F alpha).natDegree := by
  let q := (minpoly F alpha).map (algebraMap F E)
  have hqmonic : q.Monic := (minpoly.monic halphaIntegral).map (algebraMap F E)
  have hqdegree : q.natDegree = (minpoly F alpha).natDegree :=
    (minpoly.monic halphaIntegral).natDegree_map (algebraMap F E)
  rw [← hqdegree]
  by_contra hdegree
  have hzero : q = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q hinjective
      (fun i ↦ by simpa [q, Polynomial.aeval_def] using hroots i)
      (Nat.lt_of_not_ge hdegree)
  exact hqmonic.ne_zero hzero

private lemma irreducible_of_card_conjugates
    {F E iota : Type*} [Field F] [CommRing E] [IsDomain E] [Algebra F E] [Fintype iota]
    {p : Polynomial F} (hp : p.Monic) {alpha : E} (halpha : Polynomial.aeval alpha p = 0)
    (conjugate : iota → E) (hinjective : Function.Injective conjugate)
    (hroots : ∀ i, Polynomial.aeval (conjugate i) (minpoly F alpha) = 0)
    (hdegree : p.natDegree ≤ Fintype.card iota) : Irreducible p := by
  have halphaIntegral : IsIntegral F alpha := ⟨p, hp, halpha⟩
  have hpdegree := hdegree.trans <|
    card_le_minpoly_natDegree_of_injective_roots halphaIntegral conjugate hinjective hroots
  have hpmin : p = minpoly F alpha :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic halphaIntegral) hp
      (minpoly.dvd F alpha halpha) hpdegree
  exact hpmin.symm ▸ minpoly.irreducible halphaIntegral

private theorem modularPolynomialRatFunc_irreducible (m : ℕ+) :
    Irreducible (modularPolynomialRatFunc m) := by
  apply irreducible_of_card_conjugates
    ((modularPolynomialC_monic m).map
      (algebraMap (Polynomial ℂ) (RatFunc ℂ)))
    (modularPolynomialRatFunc_aeval_base m)
    (rightCosetRoot m) (rightCosetRoot_injective m)
    (minpoly_aeval_rightCosetRoot m)
  apply le_of_eq
  calc
    (modularPolynomialRatFunc m).natDegree = (modularPolynomialC m).natDegree :=
      (modularPolynomialC_monic m).natDegree_map _
    _ = Fintype.card (CoxMatrix m) := modularPolynomialC_natDegree m
    _ = Fintype.card (Gamma0RightCosets m) :=
      Fintype.card_congr (coxMatrixEquivRightCosets m)

/-- Exercise 11.10 / Theorem 11.18(ii), function-field form: `Φ_m` is irreducible in the
root variable over `ℂ(Y)`. -/
theorem modularPolynomialC_irreducibleInX (m : ℕ+) :
    Irreducible (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      (modularPolynomialC m)) :=
  modularPolynomialRatFunc_irreducible m

end Irreducibility

end Cox

