/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseKaehlerRank
public import AINTLIBDrafts.YZeroCoarseStandardSmoothRank
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Differential stalk ranks from locally standard smooth relative dimension

For a smooth algebra `S` over `R`, a literal ring-hom local standard smooth
relative dimension `n` condition determines the rank of `Ω[S⁄R]` at every prime.
The local condition is unpacked as its unit-span localization cover. At a given
prime, an element of this cover outside the prime gives a localization with a
prime lying above the original one.

The local chart has the stated standard smooth relative dimension and hence
stalk rank `n`. The canonical scalar tower identifies its local ring-hom scalars
with the existing localization algebra. Formally étale differential base change
then transports the rank back to the original prime.

Smoothness of `S` over `R` remains an explicit hypothesis for the finite and flat
differential module used in rank transport. No global standard smooth chart of
`S` is assumed. Identity-dimension-zero and polynomial-dimension-one sanities
construct genuine local conditions through the ring-hom API.

This is the local-condition-to-rank direction. The converse criterion and scheme
relative-dimension descent are separate proof steps.
-/

@[expose] public section

namespace ModularPolynomialCurveTest.AINTLIB.RelativeDimension

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- A locally standard smooth relative dimension determines the differential rank
at every prime. Smoothness supplies finite and flat differentials for localization. -/
theorem kaehler_rankAtStalk_eq_of_locally_standardSmooth [Algebra.Smooth R S] (n : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R S))
    (P : PrimeSpectrum S) : Module.rankAtStalk (R := S) Ω[S⁄R] P = n := by
  obtain ⟨s, hs, hstd⟩ := h
  obtain ⟨t, hts, htP⟩ : ∃ t ∈ s, t ∉ P.asIdeal := by
    by_contra h
    have hle : Ideal.span s ≤ P.asIdeal := Ideal.span_le.mpr fun t ht ↦ by
      by_contra hp
      exact h ⟨t, ht, hp⟩
    rw [hs] at hle
    exact P.2.ne_top (top_le_iff.mp hle)
  let Sₜ := Localization.Away t
  obtain ⟨Q, hQ⟩ : ∃ Q : PrimeSpectrum Sₜ,
      PrimeSpectrum.comap (algebraMap S Sₜ) Q = P := by
    have hmem : P ∈ Set.range (PrimeSpectrum.comap (algebraMap S Sₜ)) := by
      rw [PrimeSpectrum.localization_away_comap_range Sₜ t]
      exact (PrimeSpectrum.mem_basicOpen t P).mpr htP
    exact hmem
  have hstd' : RingHom.IsStandardSmoothOfRelativeDimension n (algebraMap R Sₜ) := by
    rw [IsScalarTower.algebraMap_eq R S Sₜ]
    exact hstd t hts
  have : Algebra.IsStandardSmoothOfRelativeDimension n R Sₜ :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).mp hstd'
  have : Algebra.FormallyEtale S Sₜ :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := Sₜ) (Submonoid.powers t)
  have hrank := kaehler_rankAtStalk_eq_of_smooth_formallyEtale R S Sₜ Q
  change Module.rankAtStalk (R := Sₜ) Ω[Sₜ⁄R] Q =
    Module.rankAtStalk (R := S) Ω[S⁄R] (PrimeSpectrum.comap (algebraMap S Sₜ) Q) at hrank
  calc
    Module.rankAtStalk (R := S) Ω[S⁄R] P =
        Module.rankAtStalk (R := Sₜ) Ω[Sₜ⁄R] Q := by
      simpa only [hQ] using hrank.symm
    _ = n := kaehler_rankAtStalk_eq_of_standardSmooth R Sₜ n Q

example (P : PrimeSpectrum R) : Module.rankAtStalk (R := R) Ω[R⁄R] P = 0 := by
  have h : RingHom.IsStandardSmoothOfRelativeDimension 0 (algebraMap R R) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 0)).mpr inferInstance
  exact kaehler_rankAtStalk_eq_of_locally_standardSmooth R R 0
    (RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso) _ h) P

example (P : PrimeSpectrum (MvPolynomial (Fin 1) R)) :
    Module.rankAtStalk (R := MvPolynomial (Fin 1) R) Ω[MvPolynomial (Fin 1) R⁄R] P = 1 := by
  have h : RingHom.IsStandardSmoothOfRelativeDimension 1
      (algebraMap R (MvPolynomial (Fin 1) R)) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr inferInstance
  exact kaehler_rankAtStalk_eq_of_locally_standardSmooth R (MvPolynomial (Fin 1) R) 1
    (RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso) _ h) P

#print axioms kaehler_rankAtStalk_eq_of_locally_standardSmooth
#print axioms kaehler_rankAtStalk_eq_of_smooth_formallyEtale
#print axioms kaehler_rankAtStalk_eq_of_standardSmooth
#print axioms PrimeSpectrum.localization_away_comap_range
#print axioms Algebra.FormallyEtale.of_isLocalization
#print axioms RingHom.isStandardSmoothOfRelativeDimension_algebraMap
#print axioms IsScalarTower.algebraMap_eq
#print axioms Ideal.span_le
#print axioms RingHom.locally_of
#print axioms RingHom.isStandardSmoothOfRelativeDimension_respectsIso

end ModularPolynomialCurveTest.AINTLIB.RelativeDimension
