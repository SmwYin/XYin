/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Stalk ranks of relative differentials along formally étale maps

For a scalar tower `R → A → B`, formal étaleness of `A → B` identifies
`Ω[B⁄R]` with base change of `Ω[A⁄R]`. When the original differential module is
finite and flat, the existing module base-change theorem compares their ranks
at a prime of `B` and its inverse image in `A`.

The primary statement uses exactly those finite and flat module hypotheses.
A separate corollary supplies them from smoothness of `A` over `R`. This requires
no Noetherian, domain, nontriviality, finite-extension, or surjectivity hypothesis.
It does not assume that `B` is globally standard smooth. The proof only combines
mathlib's formally étale differential base change and stalk-rank base change.

The sanities exercise the general finite-flat statement, the identity map for a
smooth algebra, and the smooth corollary with the literal prime-comap interface.
No local-standard-smooth rank criterion, relative-dimension descent, or quotient
elliptic curve upgrade is claimed here.
-/

@[expose] public section

namespace ModularPolynomialCurveTest.AINTLIB.RelativeDimension

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Relative differentials have the same stalk rank along a formally étale map
when the original differential module is finite and flat. -/
theorem kaehler_rankAtStalk_eq_of_formallyEtale [Module.Finite A Ω[A⁄R]]
    [Module.Flat A Ω[A⁄R]] [Algebra.FormallyEtale A B] (P : PrimeSpectrum B) :
    Module.rankAtStalk (R := B) Ω[B⁄R] P =
      Module.rankAtStalk (R := A) Ω[A⁄R] (P.comap (algebraMap A B)) :=
  Module.rankAtStalk_isBaseChange
    (KaehlerDifferential.isBaseChange_of_formallyEtale R A B) P

/-- Smoothness supplies the finite and flat differential module hypotheses
for formally étale stalk rank comparison. -/
theorem kaehler_rankAtStalk_eq_of_smooth_formallyEtale [Algebra.Smooth R A]
    [Algebra.FormallyEtale A B] (P : PrimeSpectrum B) :
    Module.rankAtStalk (R := B) Ω[B⁄R] P =
      Module.rankAtStalk (R := A) Ω[A⁄R] (P.comap (algebraMap A B)) :=
  kaehler_rankAtStalk_eq_of_formallyEtale R A B P

example [Module.Finite A Ω[A⁄R]] [Module.Flat A Ω[A⁄R]]
    [Algebra.FormallyEtale A B] (P : PrimeSpectrum B) :
    Module.rankAtStalk (R := B) Ω[B⁄R] P =
      Module.rankAtStalk (R := A) Ω[A⁄R] (PrimeSpectrum.comap (algebraMap A B) P) :=
  kaehler_rankAtStalk_eq_of_formallyEtale R A B P

example [Algebra.Smooth R A] (P : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) Ω[A⁄R] P =
      Module.rankAtStalk (R := A) Ω[A⁄R] (P.comap (algebraMap A A)) :=
  kaehler_rankAtStalk_eq_of_smooth_formallyEtale R A A P

example [Algebra.Smooth R A] [Algebra.FormallyEtale A B] (P : PrimeSpectrum B) :
    Module.rankAtStalk (R := B) Ω[B⁄R] P =
      Module.rankAtStalk (R := A) Ω[A⁄R] (PrimeSpectrum.comap (algebraMap A B) P) :=
  kaehler_rankAtStalk_eq_of_smooth_formallyEtale R A B P

#print axioms kaehler_rankAtStalk_eq_of_formallyEtale
#print axioms kaehler_rankAtStalk_eq_of_smooth_formallyEtale
#print axioms KaehlerDifferential.isBaseChange_of_formallyEtale
#print axioms Module.rankAtStalk_isBaseChange
#print axioms KaehlerDifferential.finite
#print axioms Algebra.FormallySmooth.projective_kaehlerDifferential
#print axioms Module.Flat.of_projective

end ModularPolynomialCurveTest.AINTLIB.RelativeDimension
