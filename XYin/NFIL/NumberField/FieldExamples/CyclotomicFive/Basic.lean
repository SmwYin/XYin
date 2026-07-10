/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import Mathlib

/-!
# `ℚ(ζ₅)` Basic

Field definition, chosen generator, defining polynomial, degree, and basic algebraic facts.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Basic
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicFive

/-- The fifth cyclotomic field over `ℚ`. -/
abbrev K : Type := CyclotomicField 5 ℚ

/-- The cyclotomic-extension structure on `K = ℚ(ζ₅)`. -/
instance : IsCyclotomicExtension {5} ℚ K :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

/-- A chosen primitive fifth root of unity. -/
abbrev ζ : K := IsCyclotomicExtension.zeta 5 ℚ K

/-- `ζ` is a primitive fifth root of unity. -/
theorem zeta_isPrimitiveRoot : IsPrimitiveRoot ζ 5 :=
  IsCyclotomicExtension.zeta_spec 5 ℚ K

/-- `ζ⁵ = 1`. -/
theorem zeta_pow_five : ζ ^ 5 = 1 :=
  zeta_isPrimitiveRoot.pow_eq_one

/-- The vanishing of the fifth cyclotomic polynomial at `ζ`:
`1 + ζ + ζ² + ζ³ + ζ⁴ = 0`. -/
theorem zeta_sum_eq_zero : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
  have h := zeta_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  simp [Finset.sum_range_succ] at h
  linear_combination h

/-- The extension degree of `K = ℚ(ζ₅)` over `ℚ` is `φ(5) = 4`. -/
theorem degree_eq_four : Module.finrank ℚ K = 4 :=
  (IsCyclotomicExtension.finrank (n := 5) K
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))).trans rfl

/--
The same quartic field built directly by adjoining a root of
`X^4 + X^3 + X^2 + X + 1`, the fifth cyclotomic polynomial.
-/
abbrev zetaFivePolynomial : ℚ[X] :=
  Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + Polynomial.C 1

instance : Fact (Irreducible zetaFivePolynomial) where
  out := by
    rw [zetaFivePolynomial]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hΦ :
        Polynomial.cyclotomic 5 ℚ =
          Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X +
            Polynomial.C 1 := by
      rw [Polynomial.cyclotomic_prime]
      simp [Finset.sum_range_succ]
      ring
    rw [← hΦ]
    exact Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 5)

/-- The `AdjoinRoot` presentation of `ℚ(ζ₅)`. -/
abbrev KAdjoinRoot : Type := AdjoinRoot zetaFivePolynomial

/-- The formal primitive fifth root in the `AdjoinRoot Φ₅` model. -/
abbrev zetaFiveRoot : KAdjoinRoot := AdjoinRoot.root zetaFivePolynomial

/-- The formal root satisfies `Φ₅(ζ) = 0` in the `AdjoinRoot` model. -/
theorem zetaFiveRoot_relation :
    1 + zetaFiveRoot + zetaFiveRoot ^ 2 + zetaFiveRoot ^ 3 + zetaFiveRoot ^ 4 = 0 := by
  have hroot :
      zetaFiveRoot ^ 4 + zetaFiveRoot ^ 3 + zetaFiveRoot ^ 2 + zetaFiveRoot + 1 = 0 := by
    simpa [zetaFiveRoot, zetaFivePolynomial] using
      (AdjoinRoot.eval₂_root zetaFivePolynomial)
  calc
    1 + zetaFiveRoot + zetaFiveRoot ^ 2 + zetaFiveRoot ^ 3 + zetaFiveRoot ^ 4 =
        zetaFiveRoot ^ 4 + zetaFiveRoot ^ 3 + zetaFiveRoot ^ 2 + zetaFiveRoot + 1 := by
      ring
    _ = 0 := hroot

/-- The explicit polynomial `X^4 + X^3 + X^2 + X + 1` is the minimal polynomial of `ζ`. -/
theorem zetaFivePolynomial_eq_minpoly : zetaFivePolynomial = minpoly ℚ ζ := by
  rw [zetaFivePolynomial]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hΦ :
      Polynomial.cyclotomic 5 ℚ =
        Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X +
          Polynomial.C 1 := by
    rw [Polynomial.cyclotomic_prime]
    simp [Finset.sum_range_succ]
    ring
  rw [← hΦ]
  exact zeta_isPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 5))

/-- The cyclotomic model is obtained by adjoining a root of the minimal polynomial of `ζ`. -/
def zetaMinpolyAdjoinRootPresentation : IsAdjoinRoot K (minpoly ℚ ζ) := by
  exact IsAdjoinRoot.mkOfAdjoinEqTop
    ((IsCyclotomicExtension.integral {5} ℚ K).isIntegral ζ)
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top zeta_isPrimitiveRoot)

/--
The `AdjoinRoot Φ₅` construction and the cyclotomic-field construction are equivalent as
`ℚ`-algebras.
-/
noncomputable def adjoinRootEquivCyclotomic : KAdjoinRoot ≃ₐ[ℚ] K := by
  refine (AdjoinRoot.algEquivOfEq ℚ zetaFivePolynomial (minpoly ℚ ζ) ?_).trans ?_
  · exact zetaFivePolynomial_eq_minpoly
  · exact zetaMinpolyAdjoinRootPresentation.adjoinRootAlgEquiv

/-- Under the equivalence, the formal adjoining root is the cyclotomic root `ζ`. -/
theorem adjoinRootEquivCyclotomic_root :
    adjoinRootEquivCyclotomic zetaFiveRoot = ζ := by
  change zetaMinpolyAdjoinRootPresentation.adjoinRootAlgEquiv
    ((AdjoinRoot.algEquivOfEq ℚ zetaFivePolynomial (minpoly ℚ ζ)
      zetaFivePolynomial_eq_minpoly) (AdjoinRoot.root zetaFivePolynomial)) = ζ
  rw [AdjoinRoot.algEquivOfEq_root]
  simp [zetaMinpolyAdjoinRootPresentation]


end NumberField.CyclotomicFive
