/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.DVRPlace
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Recovering a place from an actual DVR image

A nontrivial intrinsic place containing the literal image of a DVR in its
actual fraction field equals the place defined by that DVR. The DVR place
valuation ring has Krull dimension at most one, so a larger nontrivial
valuation subring is equal to it. No geometric centre or bijection is assumed.
-/

@[expose] public section

namespace FunctionField.Place

variable (k A K : Type*) [Field k] [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Algebra k A] [Algebra A K]
  [Algebra k K] [IsScalarTower k A K] [IsFractionRing A K]

theorem ofDiscreteValuationRing_eq_of_algebraMap_mem (v : Place k K)
    (h : ∀ a : A, algebraMap A K a ∈ v) : ofDiscreteValuationRing k A K = v := by
  have : Ring.KrullDimLE 1 (ofDiscreteValuationRing k A K).toValuationSubring := by
    change Ring.KrullDimLE 1
      ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring
    infer_instance
  apply Place.ext
  apply ValuationSubring.eq_of_le_of_ne_top _ _ v.ne_top
  intro z hz
  obtain ⟨a, rfl⟩ := (mem_ofDiscreteValuationRing_iff k A K z).mp hz
  exact h a

example (a : A) : algebraMap A K a ∈ ofDiscreteValuationRing k A K :=
  (mem_ofDiscreteValuationRing_iff k A K _).mpr ⟨a, rfl⟩

example (v : Place k K) (h : ∀ a : A, algebraMap A K a ∈ v) :
    v = ofDiscreteValuationRing k A K :=
  (ofDiscreteValuationRing_eq_of_algebraMap_mem k A K v h).symm

#print axioms ofDiscreteValuationRing_eq_of_algebraMap_mem
#print axioms ValuationSubring.eq_of_le_of_ne_top
#print axioms Valuation.valuationSubring_isDiscreteValuationRing
#print axioms mem_ofDiscreteValuationRing_iff

end FunctionField.Place
