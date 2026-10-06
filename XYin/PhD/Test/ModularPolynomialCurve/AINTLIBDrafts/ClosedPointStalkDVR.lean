/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.ForMathlib.StandardSmoothMaximalDVR
public import ModularCurves.EllipticCurve.GroupLaw
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Closed-point stalks of a smooth curve over a field

The actual standard-smooth affine chart and maximal ideal of a closed point
supply a DVR localization, identified with the literal scheme stalk. The
paired result derives both the domain and DVR structures, without assuming
that the whole scheme is integral. The examples check an integral-scheme
client and an actual native elliptic curve over an arbitrary field.

Only closed points are covered: no all-point DVR, RR place, genus or quotient
model claim is made.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularPolynomialCurveTest.AINTLIB.LocalValuation

theorem closedPoint_stalk_isDiscreteValuationRing
    {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 π] (x : X) (hx : IsClosed {x}) :
    ∃ _hd : IsDomain (X.presheaf.stalk x),
      IsDiscreteValuationRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hxV, e, hss⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := π) x
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    have hxU : π.base x ∈ U := e hxV
    exact (Subsingleton.elim (π.base x) y) ▸ hxU
  subst hUtop
  let : Algebra k Γ(X, V) := ((π.appLE ⊤ V e).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(X, V) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv hss
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : q.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  obtain ⟨hd, hdvr⟩ :=
    ModularCurves.isDiscreteValuationRing_localizationAtPrime_of_isStandardSmooth k Γ(X, V) q
  let : IsDomain (Localization.AtPrime q) := hd
  let : IsDiscreteValuationRing (Localization.AtPrime q) := hdvr
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  let i := (IsLocalization.algEquiv q.primeCompl
    (Localization.AtPrime q) (X.presheaf.stalk x)).toRingEquiv
  let hdom : IsDomain (X.presheaf.stalk x) := i.symm.injective.isDomain i.symm
  exact ⟨hdom, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing i⟩

example {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 π]
    (x : X) (hx : IsClosed {x}) : IsDiscreteValuationRing (X.presheaf.stalk x) := by
  obtain ⟨_, hdvr⟩ := closedPoint_stalk_isDiscreteValuationRing π x hx
  exact hdvr

example {k : Type u} [Field k] (E : ModularCurves.EllipticCurve (Spec (CommRingCat.of k)))
    (x : E.E) (hx : IsClosed {x}) :
    ∃ _hd : IsDomain (E.E.presheaf.stalk x),
      IsDiscreteValuationRing (E.E.presheaf.stalk x) :=
  closedPoint_stalk_isDiscreteValuationRing E.π x hx

#print axioms closedPoint_stalk_isDiscreteValuationRing
#print axioms SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
#print axioms IsAffineOpen.primeIdealOf_isMaximal_of_isClosed
#print axioms IsAffineOpen.isLocalization_stalk
#print axioms ModularCurves.isDiscreteValuationRing_localizationAtPrime_of_isStandardSmooth
#print axioms Scheme.ΓSpecIso
#print axioms RingHom.isStandardSmoothOfRelativeDimension_respectsIso
#print axioms RingHom.isStandardSmoothOfRelativeDimension_algebraMap
#print axioms IsLocalization.algEquiv
#print axioms IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
#print axioms Function.Injective.isDomain

end ModularPolynomialCurveTest.AINTLIB.LocalValuation
