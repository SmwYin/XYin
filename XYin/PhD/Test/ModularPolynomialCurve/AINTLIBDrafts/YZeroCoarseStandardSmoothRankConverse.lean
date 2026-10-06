/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Standard smooth relative dimension from one differential stalk rank

For a standard smooth algebra, the module of relative differentials is finite
and free. Its rank at one prime therefore determines its global finite rank.
The existing rank characterization of standard smooth relative dimension
then gives that dimension. The given prime supplies nontriviality, with no
separate nontriviality hypothesis.

The two sanity examples use the identity algebra and a polynomial algebra in
one variable. This module concerns an algebra already known to be globally
standard smooth. It does not construct local standard smooth charts, prove a
full local-condition converse, or descend scheme relative dimension.
-/

@[expose] public section

namespace ModularPolynomialCurveTest.AINTLIB.RelativeDimension

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- For a standard smooth algebra, the differential stalk rank at one prime
determines its standard smooth relative dimension. -/
theorem isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk (n : ℕ)
    [Algebra.IsStandardSmooth R A] (P : PrimeSpectrum A)
    (hrank : Module.rankAtStalk (R := A) Ω[A⁄R] P = n) :
    Algebra.IsStandardSmoothOfRelativeDimension n R A := by
  have : Nontrivial A := P.nontrivial
  apply (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n).mpr
  have hn : Module.finrank A Ω[A⁄R] = n := by
    rw [Module.rankAtStalk_eq_finrank_of_free] at hrank
    exact hrank
  rw [← Module.finrank_eq_rank, hn]

example (P : PrimeSpectrum R) : Algebra.IsStandardSmoothOfRelativeDimension 0 R R := by
  have : Algebra.IsStandardSmooth R R :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 0)
  apply isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk R R 0 P
  exact congrFun (Module.rankAtStalk_eq_zero_of_subsingleton (R := R) (M := Ω[R⁄R])) P

example (P : PrimeSpectrum (MvPolynomial (Fin 1) R)) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial (Fin 1) R) := by
  have : Nontrivial (MvPolynomial (Fin 1) R) := P.nontrivial
  apply isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk
    R (MvPolynomial (Fin 1) R) 1 P
  rw [Module.rankAtStalk_eq_finrank_of_free]
  exact Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1)

#print axioms isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk
#print axioms Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth
#print axioms Module.finrank_eq_rank
#print axioms Module.rankAtStalk_eq_finrank_of_free
#print axioms KaehlerDifferential.finite
#print axioms Algebra.IsStandardSmooth.free_kaehlerDifferential
#print axioms Algebra.IsStandardSmooth.finitePresentation
#print axioms PrimeSpectrum.nontrivial

end ModularPolynomialCurveTest.AINTLIB.RelativeDimension
