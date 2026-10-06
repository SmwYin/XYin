/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativePatchBaseField
public import AINTLIBDrafts.LocallySmoothIntegrallyClosed
public import ModularCurves.EllipticCurve.IntegralOverField

/-!
# Integral closedness of actual native curve charts over a field

A genuine nonempty affine chart patch of a native elliptic curve has an
integrally closed section ring. The existing base ring receives a local field
structure through its proved ring equivalence; its actual appLE scalar map is
unchanged. Native curve integrality supplies the chart domain, and actual
locally standard-smooth relative dimension one supplies integral closedness.

The genuine chosen gluing patch provides its nonemptiness witness. No subgroup
freeness, étale, Noetherian, chart-domain, model or genus premise is added.
This module asserts no stalk or quotient-ring normality.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

open ModularPolynomialCurveTest.AINTLIB.Normality

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  {G : E.FiniteLocallyFreeSubgroup} (P : G.AffineChartPatch)

/-- A genuine nonempty native affine chart over a field is integrally closed. -/
theorem chartRing_isIntegrallyClosed_of_nonempty (hU : Nonempty P.U) :
    IsIntegrallyClosed P.chartRing := by
  let e := P.baseRingEquivFieldOfNonempty hU
  let : Field P.baseRing := (e.toMulEquiv.isField (Field.toIsField k)).toField
  have : Nonempty P.U := hU
  have : IsDomain P.chartRing := IsIntegral.component_integral P.U
  have hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap P.baseRing P.chartRing) := by
    change RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (E.π.appLE P.V P.U P.hover).hom
    exact HasRingHomProperty.appLE (@SmoothOfRelativeDimension 1) E.π E.smooth
      ⟨P.V, P.hV⟩ ⟨P.U, P.hU⟩ P.hover
  exact isIntegrallyClosed_of_locally_standardSmoothRelDim_one
    P.baseRing P.chartRing hlocal

example (hU : Nonempty P.U) :
    let _ : Field P.baseRing :=
      ((P.baseRingEquivFieldOfNonempty hU).toMulEquiv.isField (Field.toIsField k)).toField
    algebraMap P.baseRing P.chartRing = (E.π.appLE P.V P.U P.hover).hom := rfl

#print axioms chartRing_isIntegrallyClosed_of_nonempty
#print axioms baseRingEquivFieldOfNonempty
#print axioms isIntegrallyClosed_of_locally_standardSmoothRelDim_one
#print axioms IsField.toField
#print axioms MulEquiv.isField
#print axioms ModularCurves.EllipticCurve.isIntegral_of_field
#print axioms IsIntegral.component_integral
#print axioms HasRingHomProperty.appLE
#print axioms ModularCurves.EllipticCurveGeom.smooth

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup)

/-- The actual chosen gluing patch supplies its own source nonemptiness. -/
theorem gluePatch_chartRing_isIntegrallyClosed (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) (x : E.E) :
    IsIntegrallyClosed (G.gluePatch N hkill x).chartRing :=
  (G.gluePatch N hkill x).chartRing_isIntegrallyClosed_of_nonempty
    ⟨⟨x, G.mem_gluePatch N hkill x⟩⟩

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) (x : E.E) :
    IsIntegrallyClosed (G.gluePatch N hkill x).chartRing :=
  G.gluePatch_chartRing_isIntegrallyClosed N hkill x

#print axioms gluePatch_chartRing_isIntegrallyClosed
#print axioms mem_gluePatch

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
