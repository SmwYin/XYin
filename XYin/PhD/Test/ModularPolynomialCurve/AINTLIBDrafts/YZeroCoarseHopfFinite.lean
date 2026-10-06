/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseHopfGaloisLeft
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.TensorProduct.Finite
public import ModularCurves.GroupScheme.StableChartData

/-!
# Module finiteness of a Hopf-Galois extension and actual chart sections

If the coaction's coefficient algebra `A` is finite over `R0`, its base change
`B ⊗[R0] A` is finite over the left factor `B`. The retained left-factor Galois
equivalence transfers this finite-module structure to `B ⊗[coinvariants ρ] B`.
Faithfully flat descent then proves that `B` is finite over its coinvariants.

The faithfully flat instance is the actual field `h.faithfullyFlat` of the existing
`IsHopfGalois ρ` input. No domain or Noetherian hypothesis is needed. The actual
`AffineChartPatch` specialization uses its geometric algebra instances, the finite
group-ring instance, and its proved Hopf-Galois theorem with the same existing local
freeness prerequisite. A finite morphism of quotient schemes or a global étale result
requires subsequent geometric arguments and is not asserted here.
-/

@[expose] public section

open AlgebraicGeometry ModularCurves
open scoped TensorProduct

noncomputable section

universe u

namespace ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

variable {R0 A B : Type*} [CommRing R0] [CommRing A] [CommRing B]
  [Algebra R0 A] [Algebra R0 B] {ρ : B →ₐ[R0] B ⊗[R0] A}

/-- A finite coefficient algebra makes a Hopf-Galois extension finite over its coinvariants. -/
theorem coinvariants_finite [Module.Finite R0 A] (h : IsHopfGalois ρ) :
    Module.Finite (coinvariants ρ) B := by
  let : Module.FaithfullyFlat (coinvariants ρ) B := h.faithfullyFlat
  let : Module.Finite B (B ⊗[R0] A) := inferInstance
  let : Module.Finite B (B ⊗[coinvariants ρ] B) :=
    Module.Finite.equiv (galoisEquivOverLeft h).symm.toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

/-- Actual stable-chart sections are finite over their literal coaction coinvariants. -/
theorem chartCoinvariants_finite {S : Scheme.{u}} {E : EllipticCurve S}
    {G : E.FiniteLocallyFreeSubgroup} (P : G.AffineChartPatch)
    [Module.Free P.baseRing P.groupRing] :
    Module.Finite (coinvariants P.chartCoaction) P.chartRing :=
  coinvariants_finite P.isHopfGalois_chartCoaction

example [Module.Finite R0 A] (h : IsHopfGalois ρ) :
    (algebraMap (coinvariants ρ) B).Finite :=
  (RingHom.finite_algebraMap).mpr (coinvariants_finite h)

example {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
    (P : G.AffineChartPatch) [Module.Free P.baseRing P.groupRing] :
    Module.Finite (coinvariants P.chartCoaction) P.chartRing :=
  chartCoinvariants_finite P

#print axioms coinvariants_finite
#print axioms chartCoinvariants_finite
#print axioms Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
#print axioms Module.Finite.base_change
#print axioms Module.Finite.equiv
#print axioms galoisEquivOverLeft
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch.isHopfGalois_chartCoaction
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch.instModuleFiniteGroupRing

end ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft
