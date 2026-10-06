/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.Vendored.RiemannRoch.CoordinateFree.Divisor

/-!
# Principal-divisor coefficients and intrinsic normalized valuations

The normalized valuation of a unit at an intrinsic place is the exponential of
the negative coefficient of its principal divisor. This follows from the actual
chart/place equivalence, the existing chart coefficient formula and normalized
valuation compatibility.

The current principal-divisor API uses explicit polynomial and rational-function
scalars, scalar towers, a function-field structure and separability. These inputs
remain explicit here. No independence under a change of chart, full constant
field, genus, scheme model or cross-field divisor pullback is asserted. The two
examples compare actual chart coefficients and recover the valuation of a
nonzero constant.
-/

@[expose] public section

open scoped Polynomial RatFunc WithZero

namespace FunctionField

variable (k K : Type*) [Field k] [Field K]
  [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

theorem valuation_eq_exp_neg_principalDivisor (u : Kˣ) (v : Place k K) :
    v.valuation (u : K) =
      WithZero.exp (-(principalDivisor k K (Additive.ofMul u) v)) := by
  obtain ⟨w, rfl⟩ := (chartToPlace k K).surjective v
  rw [placeValuation_eq]
  change Chart.placeValuation k K w (u : K) =
    WithZero.exp (-((divisorEquivChart k K)
      (Chart.principalDivisorA k K (Additive.ofMul u)) (chartToPlace k K w)))
  simpa only [divisorEquivChart, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply,
    Equiv.symm_apply_apply, toMul_ofMul] using
    Chart.placeValuation_eq_exp_neg_principalDivisor k K (Additive.ofMul u) w

example (u : Kˣ) (w : Chart.PlaceA k K) :
    (chartToPlace k K w).valuation (u : K) =
      WithZero.exp (-(Chart.principalDivisorA k K (Additive.ofMul u) w)) := by
  have hv := valuation_eq_exp_neg_principalDivisor k K u (chartToPlace k K w)
  change (chartToPlace k K w).valuation (u : K) =
    WithZero.exp (-((divisorEquivChart k K)
      (Chart.principalDivisorA k K (Additive.ofMul u)) (chartToPlace k K w))) at hv
  simpa only [divisorEquivChart, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply,
    Equiv.symm_apply_apply] using hv

example (c : kˣ) (v : Place k K) : v.valuation (algebraMap k K (c : k)) = 1 := by
  have hv := valuation_eq_exp_neg_principalDivisor k K
    (Units.map (algebraMap k K) c) v
  change v.valuation (algebraMap k K (c : k)) = _ at hv
  simpa [principalDivisor, Chart.principalDivisorA_algebraMap] using hv

#print axioms valuation_eq_exp_neg_principalDivisor
#print axioms principalDivisor
#print axioms divisorEquivChart
#print axioms chartToPlace
#print axioms placeValuation_eq
#print axioms Chart.placeValuation_eq_exp_neg_principalDivisor
#print axioms Chart.principalDivisorA_algebraMap
#print axioms Finsupp.domCongr

end FunctionField
