/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.Vendored.RiemannRoch.Place
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Intrinsic places from actual discrete valuation rings

The adic valuation of a DVR in its fraction field gives a nontrivial discrete
rank-one place. Constants factor through the actual DVR scalar tower, and
membership is precisely membership in the image of that DVR. No function-field
presentation, smoothness, finite type or genus premise is needed.
-/

@[expose] public section

open scoped WithZero

namespace FunctionField.Place

variable (k A K : Type*) [Field k] [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Algebra k A] [Algebra A K]
  [Algebra k K] [IsScalarTower k A K] [IsFractionRing A K]

/-- A DVR in its actual fraction field gives an intrinsic place over its constants. -/
noncomputable def ofDiscreteValuationRing : Place k K := by
  let v := (IsDiscreteValuationRing.maximalIdeal A).valuation K
  have hv : v.IsNontrivial := inferInstance
  refine
    { toValuationSubring := v.valuationSubring
      ne_top := fun h => (Valuation.valuationSubring_eq_top_iff v).mp h hv
      triv_on_k := fun c => ?_
      isDiscrete := ?_ }
  · rw [Valuation.mem_valuationSubring_iff]
    rw [IsScalarTower.algebraMap_apply k A K]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
  · let h := Valuation.isEquiv_valuation_valuationSubring v
    exact ⟨h.orderMonoidIso.symm.trans
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v)⟩

theorem ofDiscreteValuationRing_toValuationSubring :
    (ofDiscreteValuationRing k A K).toValuationSubring =
      ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring := rfl

theorem mem_ofDiscreteValuationRing_iff (z : K) :
    z ∈ ofDiscreteValuationRing k A K ↔ ∃ a : A, algebraMap A K a = z := by
  change z ∈ ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring ↔ _
  rw [← ValuationSubring.mem_toSubring,
    ← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]
  simp only [Subring.mem_map, Subring.mem_top, true_and]

example (c : k) : algebraMap k K c ∈ ofDiscreteValuationRing k A K :=
  (ofDiscreteValuationRing k A K).triv_on_k c

example (a : A) : algebraMap A K a ∈ ofDiscreteValuationRing k A K :=
  (mem_ofDiscreteValuationRing_iff k A K _).mpr ⟨a, rfl⟩

#print axioms ofDiscreteValuationRing
#print axioms ofDiscreteValuationRing_toValuationSubring
#print axioms mem_ofDiscreteValuationRing_iff
#print axioms IsDiscreteValuationRing.isRankOneDiscrete
#print axioms IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
#print axioms Valuation.IsEquiv.orderMonoidIso
#print axioms Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt
#print axioms IsScalarTower.algebraMap_apply

end FunctionField.Place
