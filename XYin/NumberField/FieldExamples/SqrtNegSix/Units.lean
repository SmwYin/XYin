/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.ClassGroup

/-!
# `ℚ(√-6)` Units

Unit group, torsion, fundamental units, Dirichlet rank, regulator, and abstract unit-group
structure.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Units
-/

noncomputable section

open Module Polynomial
open NumberField.FieldExamples
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace NumberField.SqrtNegSix

/-- A torsion generator of `𝓞 Kˣ`, mathematically `-1`. -/
abbrev torsionGenerator : (𝓞 K)ˣ := -1

/-- The concrete torsion units `{1, -1}`. -/
def torsionUnits : Set ((𝓞 K)ˣ) := {u | ∃ k : Fin 2, u = torsionGenerator ^ k.val}

/-- The torsion subgroup of `𝓞 Kˣ` is exactly `{1, -1}` (the discriminant is not `-3` or
`-4`, so there are no extra roots of unity). -/
theorem torsionUnits_eq : {u : (𝓞 K)ˣ | IsOfFinOrder u} = torsionUnits := by
  ext u
  constructor
  · intro hu
    obtain ⟨x, y, hxy⟩ := exists_eq_smul_one_add_smul_theta ((u : (𝓞 K)ˣ) : 𝓞 K)
    have hunit : IsUnit (x • (1 : 𝓞 K) + y • thetaInt) := by
      rw [← hxy]
      exact u.isUnit
    have hform := (isUnit_iff_normForm x y).mp hunit
    have hy0 : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := sq_eq_zero_iff.mp hy0
    have hx2 : x ^ 2 = 1 := by nlinarith
    have hx_le : x ≤ 1 := by nlinarith [sq_nonneg (x - 1)]
    have hx_ge : -1 ≤ x := by nlinarith [sq_nonneg (x + 1)]
    interval_cases x
    · refine ⟨1, ?_⟩
      rw [show ((1 : Fin 2).val) = 1 from rfl, pow_one]
      apply Units.ext
      simpa [torsionGenerator, hy] using hxy
    · norm_num at hx2
    · refine ⟨0, ?_⟩
      rw [show ((0 : Fin 2).val) = 0 from rfl, pow_zero]
      apply Units.ext
      simpa [hy] using hxy
  · rintro ⟨k, rfl⟩
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, ?_⟩
    rw [← pow_mul, mul_comm, pow_mul]
    simp [torsionGenerator]

/-- The torsion subgroup of `𝓞 Kˣ` has order `2`. -/
theorem torsionOrder_eq_two : NumberField.Units.torsionOrder K = 2 := by
  have hcard : Nat.card (NumberField.Units.torsion K) = 2 := by
    rw [Nat.card_eq_two_iff]
    have hmem1 : (1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩
    have hmemn : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K := by
      change IsOfFinOrder _
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩
    refine ⟨⟨1, hmem1⟩, ⟨-1, hmemn⟩, ?_, ?_⟩
    · intro h
      have hval := congrArg (fun z => ((z : (𝓞 K)ˣ) : 𝓞 K)) (Subtype.ext_iff.mp h)
      simp only [Units.val_one, Units.val_neg] at hval
      have h2 := congrArg (algebraMap (𝓞 K) K) hval
      simp only [map_one, map_neg] at h2
      exact two_ne_zero (by linear_combination h2 : (2 : K) = 0)
    · ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      have hz : (z : (𝓞 K)ˣ) ∈ {u : (𝓞 K)ˣ | IsOfFinOrder u} := z.2
      rw [torsionUnits_eq] at hz
      obtain ⟨k, hk⟩ := hz
      fin_cases k
      · left
        exact Subtype.ext (by simpa using hk)
      · right
        exact Subtype.ext (by simpa using hk)
  simpa [NumberField.Units.torsionOrder] using hcard

/-- The Dirichlet unit rank of the imaginary quadratic field `ℚ(√-6)` is `0`: the signature
is `(0, 1)`, so the rank is `r₁ + r₂ - 1 = 0` and the unit group is finite. -/
theorem unitRank_eq_zero : NumberField.Units.rank K = 0 := by
  rw [NumberField.Units.rank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_eq_zero, nrComplexPlaces_eq_one]

/-- Every unit of `ℤ[√-6]` is `1` or `-1`: the unit group is exactly the torsion `{±1}`. -/
theorem unit_eq_one_or_neg_one (u : (𝓞 K)ˣ) : u = 1 ∨ u = -1 := by
  obtain ⟨⟨ζ, f⟩, hζu, -⟩ := NumberField.Units.exist_unique_eq_mul_prod (K := K) u
  have hu_tors : u ∈ {u : (𝓞 K)ˣ | IsOfFinOrder u} := by
    have huζ : u = ζ := by
      rw [← mul_one ζ.1, hζu]
      apply congr_arg
      rw [← Finset.prod_empty]
      congr
      rw [Finset.univ_eq_empty_iff, unitRank_eq_zero]
      infer_instance
    rw [huζ]
    exact ζ.2
  rw [torsionUnits_eq] at hu_tors
  obtain ⟨k, hk⟩ := hu_tors
  fin_cases k
  · left
    simpa [torsionGenerator] using hk
  · right
    simpa [torsionGenerator] using hk

/-- The unit group is `μ₂` as an abstract group. -/
theorem unitGroupStructure : Nonempty ((𝓞 K)ˣ ≃* Multiplicative (ZMod 2)) := by
  have hcard : Nat.card ((𝓞 K)ˣ) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, -1, ?_, ?_⟩
    · intro h
      have hval := congrArg (fun z => ((z : (𝓞 K)ˣ) : 𝓞 K)) h
      simp only [Units.val_one, Units.val_neg] at hval
      have h2 := congrArg (algebraMap (𝓞 K) K) hval
      simp only [map_one, map_neg] at h2
      exact two_ne_zero (by linear_combination h2 : (2 : K) = 0)
    · ext u
      simp [unit_eq_one_or_neg_one u]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨mulEquivOfPrimeCardEq hcard (by
    rw [show Nat.card (Multiplicative (ZMod 2)) = Nat.card (ZMod 2) from rfl, Nat.card_zmod])⟩

/-- The regulator of a field with finite unit group is `1` (empty determinant). -/
theorem regulator_eq_one : NumberField.Units.regulator K = 1 := by
  classical
  rw [NumberField.Units.regulator_eq_det']
  have hcard :
      Fintype.card
        {w : NumberField.InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} = 0 := by
    rw [Fintype.card_congr (NumberField.Units.equivFinRank K).symm]
    simp [unitRank_eq_zero]
  have hdet : (Matrix.of fun i ↦
      (NumberField.Units.logEmbedding K)
        (Additive.ofMul
          (NumberField.Units.fundSystem K ((NumberField.Units.equivFinRank K).symm i)))).det =
      (1 : ℝ) := by
    exact Matrix.det_eq_one_of_card_eq_zero hcard
  rw [hdet]
  simp

end NumberField.SqrtNegSix

/-!
## Regulator
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

end NumberField.SqrtNegSix
