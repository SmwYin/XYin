/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.IntegrallyClosedLocalizationCover
public import ModularCurves.ForMathlib.StandardSmoothIntegrallyClosed
public import ModularCurves.ForMathlib.PolynomialStandardSmooth
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Integral closedness for a locally standard-smooth curve algebra

For a domain over a field, a locally standard-smooth relative-dimension-one
scalar map gives integral closedness. Each nonzero member of the actual
basic-open cover is standard smooth over the same field, so its localization
is normal; the checked unit-span localization criterion joins those rings.

No global standard-smooth, Noetherian or scheme-model premise is assumed.
The examples check a global standard algebra and the actual polynomial line.
-/

@[expose] public section

universe u

namespace ModularPolynomialCurveTest.AINTLIB.Normality

theorem isIntegrallyClosed_of_locally_standardSmoothRelDim_one
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap k A)) : IsIntegrallyClosed A := by
  obtain ⟨s, hs, hlocal⟩ := h
  apply IsIntegrallyClosed.of_localizationAway_span A s hs
  intro a ha hne
  have : IsDomain (Localization.Away a) := IsLocalization.Away.isDomain _ hne
  have hstd : RingHom.IsStandardSmoothOfRelativeDimension 1
      (algebraMap k (Localization.Away a)) := by
    simpa only [← IsScalarTower.algebraMap_eq k A (Localization.Away a)] using hlocal a ha
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Localization.Away a) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mp hstd
  exact ModularCurves.isIntegrallyClosed_of_isStandardSmoothOfRelativeDimension_one
    k (Localization.Away a)

example (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A] : IsIntegrallyClosed A :=
  isIntegrallyClosed_of_locally_standardSmoothRelDim_one k A
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      (algebraMap k A)
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr inferInstance))

example (k : Type u) [Field k] : IsIntegrallyClosed (Polynomial k) := by
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Polynomial k) :=
    Algebra.IsStandardSmoothOfRelativeDimension.polynomial k
  exact isIntegrallyClosed_of_locally_standardSmoothRelDim_one k (Polynomial k)
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      (algebraMap k (Polynomial k))
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr inferInstance))

#print axioms isIntegrallyClosed_of_locally_standardSmoothRelDim_one
#print axioms IsIntegrallyClosed.of_localizationAway_span
#print axioms ModularCurves.isIntegrallyClosed_of_isStandardSmoothOfRelativeDimension_one
#print axioms ModularCurves.isDiscreteValuationRing_localizationAtPrime_of_isStandardSmooth
#print axioms RingHom.isStandardSmoothOfRelativeDimension_algebraMap
#print axioms RingHom.locally_of
#print axioms RingHom.isStandardSmoothOfRelativeDimension_respectsIso
#print axioms IsLocalization.Away.isDomain
#print axioms Algebra.IsStandardSmoothOfRelativeDimension.polynomial

end ModularPolynomialCurveTest.AINTLIB.Normality
