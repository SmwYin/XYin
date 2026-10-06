/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.DVRPlaceValuation
public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Intrinsic DVR valuations along an actual local unramified map

The original constants and scalar towers of both DVR fraction fields remain
independent inputs. The compatible fraction-field square derives injectivity
of the ring map and its required torsion-free coefficient module. Locality
identifies the genuine maximal primes, and formal unramifiedness with essential
finite type makes the actual ramification index one.

The existing adic valuation comparison and both intrinsic normalizations then
give pointwise equality along the actual field algebra map. No flatness or
finite field-extension premise is required. Identity and local étale examples
check the two natural interfaces. Scheme specialization is a separate step.
-/

@[expose] public section

open scoped WithZero

namespace FunctionField.Place

variable (k A B K L : Type*) [Field k]
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Field K] [Field L]
  [Algebra k A] [Algebra A K] [Algebra k K]
  [IsScalarTower k A K] [IsFractionRing A K]
  [Algebra k B] [Algebra B L] [Algebra k L]
  [IsScalarTower k B L] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsLocalHom (algebraMap A B)]

/-- Intrinsic normalized DVR valuations agree along the genuine local unramified map. -/
theorem ofDiscreteValuationRing_valuation_algebraMap_of_formallyUnramified
    [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B] (z : K) :
    (ofDiscreteValuationRing k A K).valuation z =
      (ofDiscreteValuationRing k B L).valuation (algebraMap K L z) := by
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr <| by
      intro a b hab
      apply hAL
      simpa only [IsScalarTower.algebraMap_apply A B L] using
        congrArg (algebraMap B L) hab
  let v := IsDiscreteValuationRing.maximalIdeal A
  let w := IsDiscreteValuationRing.maximalIdeal B
  have : w.asIdeal.LiesOver v.asIdeal :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have he : w.asIdeal.ramificationIdx A = 1 :=
    (IsLocalRing.maximalIdeal B).ramificationIdx_eq_one A
  rw [ofDiscreteValuationRing_valuation_eq k A K, ofDiscreteValuationRing_valuation_eq k B L]
  simpa only [he, pow_one] using
    IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v w z

example (z : K) :
    (ofDiscreteValuationRing k A K).valuation z =
      (ofDiscreteValuationRing k A K).valuation (algebraMap K K z) :=
  ofDiscreteValuationRing_valuation_algebraMap_of_formallyUnramified k A A K K z

example [Algebra.Etale A B] (z : K) :
    (ofDiscreteValuationRing k A K).valuation z =
      (ofDiscreteValuationRing k B L).valuation (algebraMap K L z) :=
  ofDiscreteValuationRing_valuation_algebraMap_of_formallyUnramified k A B K L z

#print axioms ofDiscreteValuationRing_valuation_algebraMap_of_formallyUnramified
#print axioms IsFractionRing.injective
#print axioms IsScalarTower.algebraMap_eq
#print axioms Module.isTorsionFree_iff_algebraMap_injective
#print axioms IsLocalRing.maximalIdeal_comap
#print axioms Ideal.ramificationIdx_eq_one
#print axioms IsDedekindDomain.HeightOneSpectrum.valuation_liesOver
#print axioms ofDiscreteValuationRing_valuation_eq

end FunctionField.Place
