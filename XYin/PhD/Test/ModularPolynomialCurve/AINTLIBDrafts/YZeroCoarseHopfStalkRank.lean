/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseHopfFinite
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Stalk rank comparison for an actual Hopf--Galois extension

The existing left-factor Galois equivalence compares `B ⊗[C] B` and
`B ⊗[R] A`, where `C` is the literal coaction coinvariant subalgebra.
At the same prime of `B`, two base-change rank formulas identify their
ranks with the rank of `B` over `C` and the coefficient rank of `A` over `R`.

Only finiteness and flatness of the coefficient algebra and the existing
`IsHopfGalois` datum are required. Finiteness of the extension follows from
its retained theorem, and its flatness comes from the actual faithful-flat
field. There are no domain, Noetherian, étale, smooth, or freeness hypotheses.

The examples exercise the generic formula and the coefficient identity
algebra, with the genuine Hopf input explicit. This comparison is a
prerequisite for quotient degrees. Constant-rank descent, actual subgroup
rank, global scheme rank, and native function-field degree are separate steps.
-/

@[expose] public section

open ModularCurves
open scoped TensorProduct

namespace ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {ρ : B →ₐ[R] B ⊗[R] A}

/-- Hopf--Galois chart rank equals coefficient-algebra rank after lifting to the same prime. -/
theorem coinvariants_rankAtStalk_eq [Module.Finite R A] [Module.Flat R A]
    (h : IsHopfGalois ρ) (q : PrimeSpectrum B) :
    Module.rankAtStalk (R := coinvariants ρ) B
        (q.comap (algebraMap (coinvariants ρ) B)) =
      Module.rankAtStalk (R := R) A (q.comap (algebraMap R B)) := by
  let : Module.FaithfullyFlat (coinvariants ρ) B := h.faithfullyFlat
  let : Module.Finite (coinvariants ρ) B := coinvariants_finite h
  have heq := congrFun
    (Module.rankAtStalk_eq_of_equiv (galoisEquivOverLeft h).toLinearEquiv) q
  rw [Module.rankAtStalk_baseChange, Module.rankAtStalk_baseChange] at heq
  exact heq

example [Module.Finite R A] [Module.Flat R A] (h : IsHopfGalois ρ)
    (q : PrimeSpectrum B) :
    Module.rankAtStalk (R := coinvariants ρ) B
        (q.comap (algebraMap (coinvariants ρ) B)) =
      Module.rankAtStalk (R := R) A (q.comap (algebraMap R B)) :=
  coinvariants_rankAtStalk_eq h q

-- The coefficient identity algebra has rank one; its genuine Hopf input remains explicit.
example (ρ₀ : B →ₐ[R] B ⊗[R] R) (h : IsHopfGalois ρ₀) (q : PrimeSpectrum B) :
    Module.rankAtStalk (R := coinvariants ρ₀) B
      (q.comap (algebraMap (coinvariants ρ₀) B)) = 1 := by
  have : Nontrivial R := (q.comap (algebraMap R B)).nontrivial
  simpa using coinvariants_rankAtStalk_eq h q

#print axioms coinvariants_rankAtStalk_eq
#print axioms galoisEquivOverLeft
#print axioms coinvariants_finite
#print axioms Module.rankAtStalk_eq_of_equiv
#print axioms Module.rankAtStalk_baseChange
#print axioms ModularCurves.IsHopfGalois.faithfullyFlat
#print axioms Module.FaithfullyFlat.iff_flat_and_proper_ideal
#print axioms Module.rankAtStalk_eq_finrank_of_free

end ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft
