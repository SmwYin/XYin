/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import Mathlib

/-!
# `ℚ(ζ₈)` Basic

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

open Module
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicEight

/-- The eighth cyclotomic field over `ℚ`. -/
abbrev K : Type := CyclotomicField 8 ℚ

/-- The cyclotomic-extension structure on `K = ℚ(ζ₈)`. -/
instance : IsCyclotomicExtension {8} ℚ K :=
  CyclotomicField.isCyclotomicExtension 8 ℚ

/-- A chosen primitive eighth root of unity. -/
abbrev ζ : K := IsCyclotomicExtension.zeta 8 ℚ K

/-- `ζ` is a primitive eighth root of unity. -/
theorem zeta_isPrimitiveRoot : IsPrimitiveRoot ζ 8 :=
  IsCyclotomicExtension.zeta_spec 8 ℚ K

/-- `ζ⁸ = 1`. -/
theorem zeta_pow_eight : ζ ^ 8 = 1 :=
  zeta_isPrimitiveRoot.pow_eq_one

/-- The vanishing of the eighth cyclotomic polynomial at `ζ`: `ζ⁴ = -1`. -/
theorem zeta_pow_four : ζ ^ 4 = -1 :=
  (zeta_isPrimitiveRoot.pow (by norm_num) (rfl : 8 = 4 * 2)).eq_neg_one_of_two_right

/-- The extension degree of `K = ℚ(ζ₈)` over `ℚ` is `φ(8) = 4`. -/
theorem degree_eq_four : Module.finrank ℚ K = 4 :=
  (IsCyclotomicExtension.finrank (n := 8) K
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))).trans rfl

/-- The polynomial `X⁴ + 1`, defining the eighth cyclotomic field. -/
abbrev zetaEightPolynomial : Polynomial ℚ := Polynomial.X ^ 4 + Polynomial.C (1 : ℚ)

private theorem cyclotomic_eight_rat : Polynomial.cyclotomic 8 ℚ = zetaEightPolynomial := by
  rw [zetaEightPolynomial]
  have h4 : Polynomial.cyclotomic 4 ℚ = Polynomial.X ^ 2 + 1 := by
    have h := Polynomial.cyclotomic_expand_eq_cyclotomic (R := ℚ) Nat.prime_two (dvd_refl 2)
    rw [Polynomial.cyclotomic_two, show (2 * 2 : ℕ) = 4 from rfl] at h
    rw [← h, map_add, map_one, Polynomial.expand_X]
  have h8 := Polynomial.cyclotomic_expand_eq_cyclotomic (R := ℚ) Nat.prime_two
    (by norm_num : (2 : ℕ) ∣ 4)
  rw [h4, show (4 * 2 : ℕ) = 8 from rfl] at h8
  rw [← h8, map_add, map_one, map_pow, Polynomial.expand_X]
  rw [show (1 : Polynomial ℚ) = Polynomial.C 1 from Polynomial.C_1.symm]
  ring

instance : Fact (Irreducible zetaEightPolynomial) where
  out := by
    rw [← cyclotomic_eight_rat]
    exact Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 8)

/-- The same field, presented by adjoining a root of `X⁴ + 1`. -/
abbrev KAdjoinRoot : Type := AdjoinRoot zetaEightPolynomial

/-- The formal eighth-root generator in the `AdjoinRoot` presentation. -/
abbrev zetaEightRoot : KAdjoinRoot := AdjoinRoot.root zetaEightPolynomial

theorem zetaEightRoot_pow_four : zetaEightRoot ^ 4 = (-1 : KAdjoinRoot) := by
  have hroot : zetaEightRoot ^ 4 + 1 = 0 := by
    simpa [zetaEightRoot, zetaEightPolynomial] using
      (AdjoinRoot.eval₂_root zetaEightPolynomial)
  calc
    zetaEightRoot ^ 4 = zetaEightRoot ^ 4 + 1 - 1 := by ring
    _ = -1 := by rw [hroot]; ring

/-- The polynomial `X⁴ + 1` is the minimal polynomial of `ζ₈`. -/
theorem zetaEightPolynomial_eq_minpoly : zetaEightPolynomial = minpoly ℚ ζ := by
  rw [← cyclotomic_eight_rat]
  exact zeta_isPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 8))

/-- The cyclotomic model is obtained by adjoining a root of the minimal polynomial of `ζ`. -/
def zetaMinpolyAdjoinRootPresentation : IsAdjoinRoot K (minpoly ℚ ζ) := by
  exact IsAdjoinRoot.mkOfAdjoinEqTop
    ((IsCyclotomicExtension.integral {8} ℚ K).isIntegral ζ)
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top zeta_isPrimitiveRoot)

/-- The `AdjoinRoot` presentation is equivalent to the cyclotomic model. -/
noncomputable def adjoinRootEquivCyclotomic : KAdjoinRoot ≃ₐ[ℚ] K := by
  refine (AdjoinRoot.algEquivOfEq ℚ zetaEightPolynomial (minpoly ℚ ζ) ?_).trans ?_
  · exact zetaEightPolynomial_eq_minpoly
  · exact zetaMinpolyAdjoinRootPresentation.adjoinRootAlgEquiv

theorem adjoinRootEquivCyclotomic_root :
    adjoinRootEquivCyclotomic zetaEightRoot = ζ := by
  change zetaMinpolyAdjoinRootPresentation.adjoinRootAlgEquiv
    ((AdjoinRoot.algEquivOfEq ℚ zetaEightPolynomial (minpoly ℚ ζ)
      zetaEightPolynomial_eq_minpoly) (AdjoinRoot.root zetaEightPolynomial)) = ζ
  rw [AdjoinRoot.algEquivOfEq_root]
  simp [zetaMinpolyAdjoinRootPresentation]


end NumberField.CyclotomicEight
