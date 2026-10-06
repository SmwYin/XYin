/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseKaehlerRank
public import AINTLIBDrafts.YZeroCoarseStandardSmoothRank
public import AINTLIBDrafts.YZeroCoarseStandardSmoothRankConverse
public import AINTLIBDrafts.YZeroCoarseLocallyStandardSmoothRank
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Differential rank characterizes locally standard smooth relative dimension

For a smooth algebra, constant differential stalk rank first gives a standard
smooth localization of the same relative dimension near each prime. Choosing
these localizations by prime gives a genuine unit-span cover, and hence the
corresponding `RingHom.Locally` condition. Together with the checked forward
rank theorem this yields an equivalence.

The three APIs assume smoothness and the stated rank condition only. They
require no nontriviality, domain, or Noetherian hypothesis. A lifted prime
supplies nontriviality whenever the standard smooth rank calculation needs it.
The five examples test the per-prime and full-cover identity and one-variable
polynomial cases, and the vacuous prime-spectrum case for a zero ring at any
relative dimension. Scheme-level gluing and quotient applications are separate.
-/

@[expose] public section

namespace ModularPolynomialCurveTest.AINTLIB.RelativeDimension

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Constant differential stalk rank gives a standard smooth neighborhood of
that relative dimension around each prime of a smooth algebra. -/
theorem exists_notMem_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk
    [Algebra.Smooth R S] (n : ℕ)
    (h : ∀ P : PrimeSpectrum S, Module.rankAtStalk (R := S) Ω[S⁄R] P = n)
    (P : PrimeSpectrum S) :
    ∃ t : S, t ∉ P.asIdeal ∧
      Algebra.IsStandardSmoothOfRelativeDimension n R (Localization.Away t) := by
  obtain ⟨t, ht, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R P.asIdeal
  let T := Localization.Away t
  obtain ⟨Q, hQ⟩ : ∃ Q : PrimeSpectrum T,
      PrimeSpectrum.comap (algebraMap S T) Q = P := by
    have hmem : P ∈ Set.range (PrimeSpectrum.comap (algebraMap S T)) := by
      rw [PrimeSpectrum.localization_away_comap_range T t]
      exact (PrimeSpectrum.mem_basicOpen t P).mpr ht
    exact hmem
  have : Algebra.IsStandardSmooth R T := hstd
  have : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := T) (Submonoid.powers t)
  have hrank := kaehler_rankAtStalk_eq_of_smooth_formallyEtale R S T Q
  change Module.rankAtStalk (R := T) Ω[T⁄R] Q =
    Module.rankAtStalk (R := S) Ω[S⁄R] (PrimeSpectrum.comap (algebraMap S T) Q) at hrank
  rw [hQ] at hrank
  exact ⟨t, ht, isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk
    R T n Q (hrank.trans (h P))⟩

example (P : PrimeSpectrum R) :
    ∃ t : R, t ∉ P.asIdeal ∧
      Algebra.IsStandardSmoothOfRelativeDimension 0 R (Localization.Away t) :=
  exists_notMem_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk R R 0
    (fun Q ↦ kaehler_rankAtStalk_eq_of_standardSmooth R R 0 Q) P

example (P : PrimeSpectrum (MvPolynomial (Fin 1) R)) :
    ∃ t : MvPolynomial (Fin 1) R, t ∉ P.asIdeal ∧
      Algebra.IsStandardSmoothOfRelativeDimension 1 R (Localization.Away t) := by
  have : Algebra.IsStandardSmooth R (MvPolynomial (Fin 1) R) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 1)
  exact exists_notMem_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk
    R (MvPolynomial (Fin 1) R) 1
    (fun Q ↦ kaehler_rankAtStalk_eq_of_standardSmooth R (MvPolynomial (Fin 1) R) 1 Q) P

#print axioms exists_notMem_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk
#print axioms Algebra.IsSmoothAt.exists_notMem_isStandardSmooth
#print axioms kaehler_rankAtStalk_eq_of_smooth_formallyEtale
#print axioms isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk
#print axioms PrimeSpectrum.localization_away_comap_range
#print axioms Algebra.FormallyEtale.of_isLocalization


/-- Constant differential stalk rank on a smooth algebra gives a cover by
standard smooth algebras of that relative dimension. -/
theorem locally_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk
    [Algebra.Smooth R S] (n : ℕ)
    (h : ∀ P : PrimeSpectrum S, Module.rankAtStalk (R := S) Ω[S⁄R] P = n) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R S) := by
  classical
  choose t ht hstd using fun P : PrimeSpectrum S ↦
    exists_notMem_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk R S n h P
  have hs : Ideal.span (Set.range t) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp <| top_unique fun P _ ↦
      TopologicalSpace.Opens.mem_iSup.mpr ⟨P, (PrimeSpectrum.mem_basicOpen (t P) P).mpr (ht P)⟩
  refine ⟨Set.range t, hs, ?_⟩
  rintro _ ⟨P, rfl⟩
  rw [← IsScalarTower.algebraMap_eq R S (Localization.Away (t P))]
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).mpr (hstd P)

/-- On a smooth algebra, local standard relative dimension is equivalent to
constant differential stalk rank. -/
theorem locally_isStandardSmoothOfRelativeDimension_iff_kaehler_rankAtStalk
    [Algebra.Smooth R S] (n : ℕ) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R S) ↔
      ∀ P : PrimeSpectrum S, Module.rankAtStalk (R := S) Ω[S⁄R] P = n :=
  ⟨fun h P ↦ kaehler_rankAtStalk_eq_of_locally_standardSmooth R S n h P,
    locally_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk R S n⟩

example :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 0) (algebraMap R R) :=
  locally_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk R R 0
    (fun P ↦ kaehler_rankAtStalk_eq_of_standardSmooth R R 0 P)

example : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
    (algebraMap R (MvPolynomial (Fin 1) R)) := by
  have : Algebra.IsStandardSmooth R (MvPolynomial (Fin 1) R) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 1)
  exact locally_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk
    R (MvPolynomial (Fin 1) R) 1
    (fun P ↦ kaehler_rankAtStalk_eq_of_standardSmooth R (MvPolynomial (Fin 1) R) 1 P)

example [Subsingleton S] (n : ℕ) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R S) :=
  locally_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk R S n
    (fun P ↦ isEmptyElim P)

#print axioms locally_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk
#print axioms locally_isStandardSmoothOfRelativeDimension_iff_kaehler_rankAtStalk
#print axioms kaehler_rankAtStalk_eq_of_locally_standardSmooth
#print axioms PrimeSpectrum.iSup_basicOpen_eq_top_iff
#print axioms RingHom.isStandardSmoothOfRelativeDimension_algebraMap

end ModularPolynomialCurveTest.AINTLIB.RelativeDimension
