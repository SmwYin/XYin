/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Stalk rank of differentials for a standard smooth algebra

For an algebra that is standard smooth of relative dimension `n`, the module
of relative differentials has stalk rank `n` at each prime of the algebra.
The given prime supplies nontriviality, so this result has no separate
nontriviality assumption. The proof uses the existing free differential
module and global rank theorem, followed by mathlib's free-module stalk rank
formula.

The two sanity examples use actual standard-smooth instances: the identity
algebra has rank zero, and a polynomial algebra in one variable has rank one.
This module assumes standard smoothness on the entire algebra. It does not
provide a criterion from locally standard smoothness, relative-dimension
descent, or a quotient elliptic curve model.
-/

@[expose] public section

namespace ModularPolynomialCurveTest.AINTLIB.RelativeDimension

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- Standard smooth relative dimension determines the differential rank at each prime.
The prime itself supplies nontriviality of the algebra. -/
theorem kaehler_rankAtStalk_eq_of_standardSmooth (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] (P : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) Ω[A⁄R] P = n := by
  have : Nontrivial A := P.nontrivial
  have : Algebra.IsStandardSmooth R A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := n)
  rw [Module.rankAtStalk_eq_finrank_of_free]
  exact Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)

example (P : PrimeSpectrum R) : Module.rankAtStalk (R := R) Ω[R⁄R] P = 0 :=
  kaehler_rankAtStalk_eq_of_standardSmooth R R 0 P

example (P : PrimeSpectrum (MvPolynomial (Fin 1) R)) :
    Module.rankAtStalk (R := MvPolynomial (Fin 1) R) Ω[MvPolynomial (Fin 1) R⁄R] P = 1 :=
  kaehler_rankAtStalk_eq_of_standardSmooth R (MvPolynomial (Fin 1) R) 1 P

#print axioms kaehler_rankAtStalk_eq_of_standardSmooth
#print axioms Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
#print axioms Algebra.IsStandardSmooth.free_kaehlerDifferential
#print axioms Module.rankAtStalk_eq_finrank_of_free
#print axioms Module.finrank_eq_of_rank_eq
#print axioms PrimeSpectrum.nontrivial

end ModularPolynomialCurveTest.AINTLIB.RelativeDimension
