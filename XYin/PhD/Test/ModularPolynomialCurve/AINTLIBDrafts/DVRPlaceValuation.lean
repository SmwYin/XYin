/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.DVRPlace

/-!
# The intrinsic DVR place has the actual normalized adic valuation

Uniqueness of the ordered integer value-group normalization identifies the
intrinsic Place valuation with the original DVR adic valuation. Actual adic
surjectivity fixes its scale. The examples check literal equality on field
elements and surjectivity of the intrinsic valuation.
-/

@[expose] public section

open scoped WithZero
open MonoidWithZeroHom

namespace FunctionField.Place

variable (k A K : Type*) [Field k] [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Algebra k A] [Algebra A K]
  [Algebra k K] [IsScalarTower k A K] [IsFractionRing A K]

theorem ofDiscreteValuationRing_valuation_eq :
    (ofDiscreteValuationRing k A K).valuation =
      (IsDiscreteValuationRing.maximalIdeal A).valuation K := by
  let v := (IsDiscreteValuationRing.maximalIdeal A).valuation K
  let V := v.valuationSubring
  let h := Valuation.isEquiv_valuation_valuationSubring v
  let e : ValueGroup₀ (.ofClass V.valuation) ≃*o ℤᵐ⁰ :=
    h.orderMonoidIso.symm.trans
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v)
  have hnorm : (ofDiscreteValuationRing k A K).normalization = e :=
    FunctionField.orderMonoidIso_withZeroMulInt_unique _ _
  ext x
  change (ofDiscreteValuationRing k A K).normalization (V.valuation.restrict x) = v x
  rw [hnorm]
  change (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v)
      (h.orderMonoidIso.symm (V.valuation.restrict x)) = v x
  rw [show h.orderMonoidIso.symm (V.valuation.restrict x) = v.restrict x by
    exact h.orderMonoidIso.symm_apply_eq.mpr (h.orderMonoidIso_spec x).symm]
  exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
    ((IsDiscreteValuationRing.maximalIdeal A).valuation_surjective K) x

example (z : K) :
    (ofDiscreteValuationRing k A K).valuation z =
      (IsDiscreteValuationRing.maximalIdeal A).valuation K z :=
  DFunLike.congr_fun (ofDiscreteValuationRing_valuation_eq k A K) z

example : Function.Surjective (ofDiscreteValuationRing k A K).valuation := by
  rw [ofDiscreteValuationRing_valuation_eq]
  exact (IsDiscreteValuationRing.maximalIdeal A).valuation_surjective K

#print axioms ofDiscreteValuationRing_valuation_eq
#print axioms FunctionField.orderMonoidIso_withZeroMulInt_unique
#print axioms Valuation.IsEquiv.orderMonoidIso_spec
#print axioms Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
#print axioms IsDedekindDomain.HeightOneSpectrum.valuation_surjective
#print axioms IsDiscreteValuationRing.isRankOneDiscrete

end FunctionField.Place
