/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.DVRPlace

/-!
# Canonical DVR-place algebra equivalence

The native DVR-to-valuation-subring ring equivalence preserves the original
constant-field action through the actual scalar tower. Its forward and inverse
formulas use the literal embedding into the given fraction field. No scalar
structures are transported and no geometric centre or place bijection is assumed.
-/

@[expose] public section

namespace FunctionField.Place

variable (k A K : Type*) [Field k] [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Algebra k A] [Algebra A K]
  [Algebra k K] [IsScalarTower k A K] [IsFractionRing A K]

noncomputable def ofDiscreteValuationRingAlgEquiv :
    A ≃ₐ[k] (ofDiscreteValuationRing k A K).toValuationSubring := by
  refine
    { IsDiscreteValuationRing.equivValuationSubring (A := A) (K := K) with
      commutes' := ?_ }
  intro c
  apply Subtype.ext
  change algebraMap A K (algebraMap k A c) = algebraMap k K c
  exact (IsScalarTower.algebraMap_apply k A K c).symm

theorem ofDiscreteValuationRingAlgEquiv_coe (a : A) :
    ((ofDiscreteValuationRingAlgEquiv k A K a :
      (ofDiscreteValuationRing k A K).toValuationSubring) : K) = algebraMap A K a := rfl

theorem ofDiscreteValuationRingAlgEquiv_symm_coe
    (z : (ofDiscreteValuationRing k A K).toValuationSubring) :
    algebraMap A K ((ofDiscreteValuationRingAlgEquiv k A K).symm z) = (z : K) := by
  have h := congrArg
    (fun w : (ofDiscreteValuationRing k A K).toValuationSubring => (w : K))
    ((ofDiscreteValuationRingAlgEquiv k A K).apply_symm_apply z)
  simpa only [ofDiscreteValuationRingAlgEquiv_coe] using h

example (c : k) :
    ((ofDiscreteValuationRingAlgEquiv k A K (algebraMap k A c) :
      (ofDiscreteValuationRing k A K).toValuationSubring) : K) = algebraMap k K c := by
  exact (ofDiscreteValuationRingAlgEquiv_coe k A K _).trans
    (IsScalarTower.algebraMap_apply k A K c).symm

example (a : A) :
    (ofDiscreteValuationRingAlgEquiv k A K).symm
      ⟨algebraMap A K a, (mem_ofDiscreteValuationRing_iff k A K _).mpr ⟨a, rfl⟩⟩ = a := by
  change (ofDiscreteValuationRingAlgEquiv k A K).symm
    (ofDiscreteValuationRingAlgEquiv k A K a) = a
  exact (ofDiscreteValuationRingAlgEquiv k A K).symm_apply_apply a

#print axioms ofDiscreteValuationRingAlgEquiv
#print axioms ofDiscreteValuationRingAlgEquiv_coe
#print axioms ofDiscreteValuationRingAlgEquiv_symm_coe
#print axioms IsDiscreteValuationRing.equivValuationSubring
#print axioms IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
#print axioms algebraValuationSubring
#print axioms IsScalarTower.algebraMap_apply

end FunctionField.Place
