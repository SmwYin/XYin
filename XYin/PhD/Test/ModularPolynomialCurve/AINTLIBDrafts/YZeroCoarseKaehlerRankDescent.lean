/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseKaehlerRank
public import AINTLIBDrafts.YZeroCoarseStandardSmoothRank
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Constant differential rank descends along a faithfully flat formally etale map

For a scalar tower `R → A → B`, each prime of `A` lifts to a prime of `B`
under faithful flatness. The formally etale differential base-change theorem
compares the stalk ranks at those two primes. Constant rank on `B` therefore
descends to `A`.

The original differential module needs only be finite and flat. Smoothness,
Noetherian rings, domains, globally standard smooth charts, and finite
extensions are not assumed. The two API examples use actual identity and
one-variable polynomial algebras with ranks zero and one.

This module supplies a rank-descent step. A relative-dimension criterion or
an actual quotient curve still requires the local-standard-smooth adapters.
-/

@[expose] public section

namespace ModularPolynomialCurveTest.AINTLIB.RelativeDimension

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Constant differential stalk rank descends through a faithfully flat formally
etale extension. Only finite flatness of the original differentials is needed. -/
theorem kaehler_rankAtStalk_eq_of_formallyEtale_faithfullyFlat
    [Module.Finite A Ω[A⁄R]] [Module.Flat A Ω[A⁄R]]
    [Algebra.FormallyEtale A B] [Module.FaithfullyFlat A B] (n : ℕ)
    (hB : ∀ Q : PrimeSpectrum B, Module.rankAtStalk (R := B) Ω[B⁄R] Q = n)
    (P : PrimeSpectrum A) : Module.rankAtStalk (R := A) Ω[A⁄R] P = n := by
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) P
  have hrank := kaehler_rankAtStalk_eq_of_formallyEtale R A B Q
  rw [hQ] at hrank
  exact hrank.symm.trans (hB Q)

example (P : PrimeSpectrum R) : Module.rankAtStalk (R := R) Ω[R⁄R] P = 0 :=
  kaehler_rankAtStalk_eq_of_formallyEtale_faithfullyFlat R R R 0
    (fun Q ↦ kaehler_rankAtStalk_eq_of_standardSmooth R R 0 Q) P

example (P : PrimeSpectrum (MvPolynomial (Fin 1) R)) :
    Module.rankAtStalk (R := MvPolynomial (Fin 1) R) Ω[MvPolynomial (Fin 1) R⁄R] P = 1 := by
  have : Algebra.IsStandardSmooth R (MvPolynomial (Fin 1) R) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 1)
  exact kaehler_rankAtStalk_eq_of_formallyEtale_faithfullyFlat
    R (MvPolynomial (Fin 1) R) (MvPolynomial (Fin 1) R) 1
    (fun Q ↦ kaehler_rankAtStalk_eq_of_standardSmooth R (MvPolynomial (Fin 1) R) 1 Q) P

#print axioms kaehler_rankAtStalk_eq_of_formallyEtale_faithfullyFlat
#print axioms kaehler_rankAtStalk_eq_of_formallyEtale
#print axioms PrimeSpectrum.comap_surjective_of_faithfullyFlat
#print axioms kaehler_rankAtStalk_eq_of_standardSmooth

end ModularPolynomialCurveTest.AINTLIB.RelativeDimension
