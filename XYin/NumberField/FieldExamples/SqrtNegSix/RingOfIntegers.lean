/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.Embeddings

/-!
# `ℚ(√-6)` RingOfIntegers

Integral basis, ring-of-integers description, and integral-coordinate norm forms.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Ring Of Integers
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace NumberField.SqrtNegSix

/-- The generator `θ = √-6` is integral over `ℤ` (a root of the monic `X² + 6`), hence lies
in `𝓞 K`. -/
theorem theta_integral : θ ∈ integralClosure ℤ K := by
  refine ⟨Polynomial.X ^ 2 + 6, ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_ofNat]
    linear_combination theta_sq

/-- `θ = √-6` as an element of the ring of integers `𝓞 K`. -/
noncomputable def thetaInt : 𝓞 K := ⟨θ, theta_integral⟩

/-- The integral generator also satisfies `θ² = -6` in `𝓞 K`. -/
theorem thetaInt_sq : thetaInt ^ 2 = -6 := by
  apply Subtype.ext
  change (θ : K) ^ 2 = (-6 : K)
  exact theta_sq

/-- The displayed integral-basis vectors `1, θ` (as elements of `K`). -/
def integralBasisVectors : Fin 2 → K := ![1, θ]

local notation "𝓟₂" => Submodule.span ℤ ({(2 : ℤ)} : Set ℤ)
local notation "𝓟₃" => Submodule.span ℤ ({(3 : ℤ)} : Set ℤ)

private theorem quadraticBasis_zero : (QuadraticAlgebra.basis (-6 : ℚ) (0 : ℚ)) 0 = (1 : K) := by
  change (QuadraticAlgebra.basis (-6 : ℚ) (0 : ℚ)) 0 = (⟨1, 0⟩ : K)
  simp [QuadraticAlgebra.basis, Module.Basis.ofEquivFun, QuadraticAlgebra.linearEquivTuple]

private theorem quadraticBasis_one : (QuadraticAlgebra.basis (-6 : ℚ) (0 : ℚ)) 1 = θ := by
  change (QuadraticAlgebra.basis (-6 : ℚ) (0 : ℚ)) 1 = (⟨0, 1⟩ : K)
  simp [QuadraticAlgebra.basis, Module.Basis.ofEquivFun, QuadraticAlgebra.linearEquivTuple]

/-- The usual power basis `1, θ`, where `θ = √-6`. -/
noncomputable def sqrtNegSixPowerBasis : PowerBasis ℚ K where
  gen := θ
  dim := 2
  basis := QuadraticAlgebra.basis (-6 : ℚ) (0 : ℚ)
  basis_eq_pow := by
    intro i
    fin_cases i
    · exact quadraticBasis_zero
    · simpa [pow_one] using quadraticBasis_one

@[simp]
theorem sqrtNegSixPowerBasis_gen : sqrtNegSixPowerBasis.gen = θ := rfl

theorem sqrtNegSixPowerBasis_dim : sqrtNegSixPowerBasis.dim = 2 := rfl

/-- The integral polynomial `X² + 6` satisfied by `θ = √-6`. -/
abbrev sqrtNegSixIntegerPolynomial : ℤ[X] := Polynomial.X ^ 2 + Polynomial.C (6 : ℤ)

/-- The rational minimal polynomial of `θ = √-6`. -/
theorem sqrtNegSix_minpoly_rat : minpoly ℚ θ = sqrtNegSixPolynomial := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · exact (Fact.out : Irreducible sqrtNegSixPolynomial)
  · rw [sqrtNegSixPolynomial]
    simp only [map_add, map_pow, Polynomial.aeval_X, map_ofNat]
    linear_combination theta_sq
  · monicity!

/-- The integral minimal polynomial of `θ = √-6`, viewed as an element of the field. -/
theorem sqrtNegSix_minpoly_int : minpoly ℤ θ = sqrtNegSixIntegerPolynomial := by
  apply (Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) theta_integral,
    sqrtNegSix_minpoly_rat]
  change Polynomial.X ^ 2 + Polynomial.C (6 : ℚ) =
    Polynomial.map (algebraMap ℤ ℚ) (Polynomial.X ^ 2 + Polynomial.C (6 : ℤ))
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rw [show (algebraMap ℤ ℚ) (6 : ℤ) = (6 : ℚ) by norm_num]

/-- The polynomial `X² + 6` is Eisenstein at `2`. -/
theorem sqrtNegSix_minpoly_int_isEisensteinAt_two :
    (minpoly ℤ θ).IsEisensteinAt 𝓟₂ := by
  rw [sqrtNegSix_minpoly_int]
  refine
    (Polynomial.monic_X_pow_add_C (6 : ℤ)
      (by norm_num : (2 : ℕ) ≠ 0)).isEisensteinAt_of_mem_of_notMem
      ?_ ?_ ?_
  · rw [ne_eq, Ideal.eq_top_iff_one]
    simp [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
  · intro n hn
    rw [Polynomial.natDegree_X_pow_add_C] at hn
    interval_cases n
    · simpa using (show (6 : ℤ) ∈ 𝓟₂ by
        exact Ideal.mem_span_singleton.mpr ⟨3, by norm_num⟩)
    · simp [Ideal.submodule_span_eq]
  · simp [Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- The polynomial `X² + 6` is Eisenstein at `3`. -/
theorem sqrtNegSix_minpoly_int_isEisensteinAt_three :
    (minpoly ℤ θ).IsEisensteinAt 𝓟₃ := by
  rw [sqrtNegSix_minpoly_int]
  refine
    (Polynomial.monic_X_pow_add_C (6 : ℤ)
      (by norm_num : (2 : ℕ) ≠ 0)).isEisensteinAt_of_mem_of_notMem
      ?_ ?_ ?_
  · rw [ne_eq, Ideal.eq_top_iff_one]
    simp [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
  · intro n hn
    rw [Polynomial.natDegree_X_pow_add_C] at hn
    interval_cases n
    · simpa using (show (6 : ℤ) ∈ 𝓟₃ by
        exact Ideal.mem_span_singleton.mpr ⟨2, by norm_num⟩)
    · simp [Ideal.submodule_span_eq]
  · simp [Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private theorem algebraNorm_eq_quadraticNorm (z : K) :
    Algebra.norm ℚ z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply, ← QuadraticAlgebra.det_toLinearMap_eq_norm]
  congr 1

/-- The discriminant of the power basis `1, θ` is `-24`. -/
theorem sqrtNegSixPowerBasis_discr :
    Algebra.discr ℚ sqrtNegSixPowerBasis.basis = (-24 : ℚ) := by
  rw [Algebra.discr_powerBasis_eq_norm]
  have hgen : sqrtNegSixPowerBasis.gen = θ := rfl
  rw [hgen, degree_eq_two, sqrtNegSix_minpoly_rat]
  have hder : Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.C (6 : ℚ)) =
      2 * Polynomial.X := by
    simp
    ring
  rw [hder]
  have haev : Polynomial.aeval θ (2 * Polynomial.X : ℚ[X]) = 2 * θ := by
    rw [map_mul, Polynomial.aeval_X, map_ofNat]
  rw [haev]
  have hnorm : Algebra.norm ℚ (2 * θ) = (24 : ℚ) := by
    rw [algebraNorm_eq_quadraticNorm]
    simp [QuadraticAlgebra.norm_def, θ]
    ring
  rw [hnorm]
  norm_num

private theorem integralClosure_eq_adjoin :
    integralClosure ℤ K = Algebra.adjoin ℤ ({θ} : Set K) := by
  apply le_antisymm
  · intro z hz
    have hzI : IsIntegral ℤ z := hz
    have hBint : IsIntegral ℤ sqrtNegSixPowerBasis.gen := by
      simpa [sqrtNegSixPowerBasis] using theta_integral
    have hdiscr :=
      Algebra.discr_mul_isIntegral_mem_adjoin (K := ℚ) (L := K)
        (R := ℤ) (B := sqrtNegSixPowerBasis) hBint hzI
    rw [sqrtNegSixPowerBasis_discr] at hdiscr
    have h24z : (24 : ℤ) • z ∈ Algebra.adjoin ℤ ({sqrtNegSixPowerBasis.gen} : Set K) := by
      have hneg : (24 : ℤ) • z = -((-24 : ℚ) • z) := by
        simp [Algebra.smul_def]
      rw [hneg]
      exact neg_mem hdiscr
    have h8z_int : IsIntegral ℤ ((2 : ℤ) ^ 3 • z) := hzI.smul ((2 : ℤ) ^ 3)
    have h3pow : (3 : ℤ) ^ 1 • ((2 : ℤ) ^ 3 • z) ∈
        Algebra.adjoin ℤ ({sqrtNegSixPowerBasis.gen} : Set K) := by
      convert h24z using 1
      norm_num [Algebra.smul_def]
      ring
    have h8z : (2 : ℤ) ^ 3 • z ∈
        Algebra.adjoin ℤ ({sqrtNegSixPowerBasis.gen} : Set K) :=
      mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
        (R := ℤ) (K := ℚ) (L := K) (B := sqrtNegSixPowerBasis)
        (p := (3 : ℤ)) (n := 1) (by norm_num : Prime (3 : ℤ)) hBint h8z_int h3pow
        (by simpa [sqrtNegSixPowerBasis] using sqrtNegSix_minpoly_int_isEisensteinAt_three)
    have hzmem : z ∈ Algebra.adjoin ℤ ({sqrtNegSixPowerBasis.gen} : Set K) :=
      mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
        (R := ℤ) (K := ℚ) (L := K) (B := sqrtNegSixPowerBasis)
        (p := (2 : ℤ)) (n := 3) Int.prime_two hBint hzI h8z
        (by simpa [sqrtNegSixPowerBasis] using sqrtNegSix_minpoly_int_isEisensteinAt_two)
    simpa [sqrtNegSixPowerBasis] using hzmem
  · rw [Algebra.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact theta_integral

private theorem thetaInt_adjoin_eq_top : Algebra.adjoin ℤ ({thetaInt} : Set (𝓞 K)) = ⊤ := by
  apply le_antisymm le_top
  intro x hx
  have hfield : (x : K) ∈ Algebra.adjoin ℤ ({θ} : Set K) := by
    rw [← integralClosure_eq_adjoin]
    exact x.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hfield
  rcases hfield with ⟨P, hP⟩
  have hx_eq : x = Polynomial.aeval thetaInt P := by
    apply Subtype.ext
    change (x : K) = ((Polynomial.aeval thetaInt P : 𝓞 K) : K)
    rw [← hP]
    simpa [thetaInt] using
      (Polynomial.aeval_algHom_apply (algebraMap (𝓞 K) K).toIntAlgHom thetaInt P)
  rw [hx_eq]
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨P, rfl⟩

private theorem thetaInt_minpoly : minpoly ℤ thetaInt = sqrtNegSixIntegerPolynomial := by
  letI : IsScalarTower ℤ (𝓞 K) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hint : IsIntegral ℤ thetaInt := Algebra.IsIntegral.isIntegral thetaInt
  have hfrac :
      minpoly ℚ ((algebraMap (𝓞 K) K) thetaInt) =
        Polynomial.map (algebraMap ℤ ℚ) (minpoly ℤ thetaInt) :=
    @minpoly.isIntegrallyClosed_eq_field_fractions ℤ (𝓞 K)
      inferInstance inferInstance inferInstance inferInstance
      ℚ K inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance this inferInstance inferInstance
      thetaInt hint
  apply (Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective)
  rw [← hfrac]
  change minpoly ℚ θ = Polynomial.map (algebraMap ℤ ℚ) sqrtNegSixIntegerPolynomial
  rw [sqrtNegSix_minpoly_rat]
  change Polynomial.X ^ 2 + Polynomial.C (6 : ℚ) =
    Polynomial.map (algebraMap ℤ ℚ) (Polynomial.X ^ 2 + Polynomial.C (6 : ℤ))
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rw [show (algebraMap ℤ ℚ) (6 : ℤ) = (6 : ℚ) by norm_num]

private noncomputable def sqrtNegSixExplicitIntegralPowerBasis : PowerBasis ℤ (𝓞 K) :=
  PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral thetaInt) thetaInt_adjoin_eq_top

private theorem sqrtNegSixExplicitIntegralPowerBasis_dim :
    sqrtNegSixExplicitIntegralPowerBasis.dim = 2 := by
  rw [sqrtNegSixExplicitIntegralPowerBasis, PowerBasis.ofAdjoinEqTop'_dim, thetaInt_minpoly]
  change sqrtNegSixIntegerPolynomial.natDegree = 2
  rw [sqrtNegSixIntegerPolynomial, Polynomial.natDegree_X_pow_add_C]

private noncomputable def sqrtNegSixExplicitIntegralBasis : Basis (Fin 2) ℤ (𝓞 K) :=
  sqrtNegSixExplicitIntegralPowerBasis.basis.reindex
    (finCongr sqrtNegSixExplicitIntegralPowerBasis_dim)

private theorem sqrtNegSixExplicitIntegralBasis_zero :
    sqrtNegSixExplicitIntegralBasis 0 = 1 := by
  rw [sqrtNegSixExplicitIntegralBasis, Basis.reindex_apply]
  rw [sqrtNegSixExplicitIntegralPowerBasis.basis_eq_pow]
  have hcoe :
      (((finCongr sqrtNegSixExplicitIntegralPowerBasis_dim).symm (0 : Fin 2) :
        Fin sqrtNegSixExplicitIntegralPowerBasis.dim) : ℕ) = 0 := rfl
  rw [hcoe]
  simp

private theorem sqrtNegSixExplicitIntegralBasis_one :
    sqrtNegSixExplicitIntegralBasis 1 = thetaInt := by
  rw [sqrtNegSixExplicitIntegralBasis, Basis.reindex_apply]
  rw [sqrtNegSixExplicitIntegralPowerBasis.basis_eq_pow]
  have hcoe :
      (((finCongr sqrtNegSixExplicitIntegralPowerBasis_dim).symm (1 : Fin 2) :
        Fin sqrtNegSixExplicitIntegralPowerBasis.dim) : ℕ) = 1 := rfl
  rw [hcoe, pow_one]
  exact PowerBasis.ofAdjoinEqTop'_gen _ _

private noncomputable def integralBasisVectorsInt : Fin 2 → 𝓞 K := ![1, thetaInt]

private theorem algebraMap_integralBasisVectorsInt :
    (fun i => (algebraMap (𝓞 K) K) (integralBasisVectorsInt i)) = integralBasisVectors := by
  funext i
  fin_cases i <;> simp [integralBasisVectorsInt, integralBasisVectors, thetaInt]

private noncomputable def ringOfIntegersLinearMap : 𝓞 K →ₗ[ℤ] K :=
  (Algebra.linearMap (𝓞 K) K).restrictScalars ℤ

private theorem ringOfIntegersLinearMap_apply (u : 𝓞 K) :
    ringOfIntegersLinearMap u = (algebraMap (𝓞 K) K) u := rfl

private theorem span_integralBasisVectorsInt_eq_top :
    Submodule.span ℤ (Set.range integralBasisVectorsInt) = ⊤ := by
  have hbasis : ⇑sqrtNegSixExplicitIntegralBasis = integralBasisVectorsInt := by
    funext i
    fin_cases i
    · simp [sqrtNegSixExplicitIntegralBasis_zero, integralBasisVectorsInt]
    · simp [sqrtNegSixExplicitIntegralBasis_one, integralBasisVectorsInt]
  rw [← hbasis]
  exact sqrtNegSixExplicitIntegralBasis.span_eq

private theorem sqrtNegSixExplicitIntegralBasis_discr :
    Algebra.discr ℤ sqrtNegSixExplicitIntegralBasis = (-24 : ℤ) := by
  let bInt : Basis (Fin 2) ℤ (𝓞 K) := sqrtNegSixExplicitIntegralBasis
  haveI : IsScalarTower ℤ (𝓞 K) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hdiscLoc :=
    @Algebra.discr_localizationLocalization
      ℤ (𝓞 K) _ _ _ ℚ _ _ ℤ⁰ _ K _ _ _ _
      (by infer_instance : IsScalarTower ℤ ℚ K)
      (by infer_instance : IsScalarTower ℤ (𝓞 K) K)
      (by infer_instance : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) K)
      (Fin 2) (by infer_instance) (by infer_instance) bInt
  let bLoc : Basis (Fin 2) ℚ K :=
    @Module.Basis.localizationLocalization
      ℤ ℚ _ ℤ⁰ _ _ _ (𝓞 K) _ _ K _ _ _ _
      (by infer_instance : IsScalarTower ℤ ℚ K)
      (by infer_instance : IsScalarTower ℤ (𝓞 K) K)
      (by infer_instance : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) K)
      (Fin 2) bInt
  apply (algebraMap ℤ ℚ).injective_int
  change (algebraMap ℤ ℚ) (Algebra.discr ℤ bInt) = (algebraMap ℤ ℚ) (-24)
  rw [← hdiscLoc]
  change Algebra.discr ℚ bLoc = (-24 : ℚ)
  have hBasis : bLoc = sqrtNegSixPowerBasis.basis.reindex (finCongr sqrtNegSixPowerBasis_dim) := by
    apply DFunLike.ext
    intro i
    fin_cases i
    · simp [bLoc, bInt, Basis.localizationLocalization_apply,
        sqrtNegSixExplicitIntegralBasis_zero]
    · simpa [bLoc, bInt, Basis.localizationLocalization_apply,
        sqrtNegSixExplicitIntegralBasis_one, thetaInt, sqrtNegSixPowerBasis]
        using quadraticBasis_one.symm
  rw [hBasis]
  simpa [Basis.coe_reindex] using
    (Algebra.discr_reindex ℚ sqrtNegSixPowerBasis.basis
      (finCongr sqrtNegSixPowerBasis_dim)).trans sqrtNegSixPowerBasis_discr

/-- `1, θ` is an integral basis of `ℚ(√-6)`: their `ℤ`-span in `K` is exactly the ring of
integers `𝓞 K`. Since `-6 ≡ 2 (mod 4)`, the naive order `ℤ[√-6]` is already maximal — in
contrast with `ℚ(√5)`. -/
theorem span_integralBasisVectors_eq :
    Submodule.span ℤ (Set.range integralBasisVectors) =
      Subalgebra.toSubmodule (integralClosure ℤ K) := by
  have hmap :=
    congrArg (Submodule.map ringOfIntegersLinearMap) span_integralBasisVectorsInt_eq_top
  rw [Submodule.map_span, ← Set.range_comp] at hmap
  have hcomp : ringOfIntegersLinearMap ∘ integralBasisVectorsInt = integralBasisVectors := by
    funext i
    rw [Function.comp_apply, ringOfIntegersLinearMap_apply, ← algebraMap_integralBasisVectorsInt]
  rw [hcomp, Submodule.map_top] at hmap
  rw [hmap]
  ext x
  rw [Subalgebra.mem_toSubmodule]
  constructor
  · rintro ⟨u, rfl⟩
    exact u.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The integral basis `1, θ` packaged as a genuine `ℤ`-basis of the ring of integers `𝓞 K`. -/
noncomputable def concreteIntegralBasis : Basis (Fin 2) ℤ (𝓞 K) := by
  exact sqrtNegSixExplicitIntegralBasis

/-- The packaged integral basis is, vector by vector, the displayed family `1, θ`. -/
theorem concreteIntegralBasis_apply (i : Fin 2) :
    (algebraMap (𝓞 K) K) (concreteIntegralBasis i) = integralBasisVectors i := by
  fin_cases i <;>
    simp [concreteIntegralBasis, sqrtNegSixExplicitIntegralBasis_zero,
      sqrtNegSixExplicitIntegralBasis_one, integralBasisVectors, thetaInt]

theorem exists_eq_smul_one_add_smul_theta (z : 𝓞 K) :
    ∃ x y : ℤ, z = x • (1 : 𝓞 K) + y • thetaInt := by
  refine ⟨concreteIntegralBasis.repr z 0, concreteIntegralBasis.repr z 1, ?_⟩
  apply IsFractionRing.injective (𝓞 K) K
  have hsum := concreteIntegralBasis.sum_repr z
  conv_lhs => rw [← hsum]
  rw [map_sum]
  rw [Fin.sum_univ_two]
  simp [concreteIntegralBasis_apply, integralBasisVectors, thetaInt]

theorem linearIndependent_one_theta : LinearIndependent ℤ ![(1 : 𝓞 K), thetaInt] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_two] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  have h0 : concreteIntegralBasis 0 = (1 : 𝓞 K) := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [concreteIntegralBasis_apply]
    simp [integralBasisVectors]
  have h1 : concreteIntegralBasis 1 = thetaInt := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [concreteIntegralBasis_apply]
    simp [integralBasisVectors, thetaInt]
  have hsum : ∑ i : Fin 2, g i • concreteIntegralBasis i = 0 := by
    rw [Fin.sum_univ_two, h0, h1]
    exact hg
  exact Fintype.linearIndependent_iff.mp concreteIntegralBasis.linearIndependent g hsum

/-- The displayed integral basis `1, θ` spans the same `ℤ`-lattice in `K` as mathlib's
`NumberField.integralBasis K` (the correct form of "the two integral bases agree": equality
of lattices, not a mere reindexing). -/
theorem span_integralBasisVectors_eq_integralBasis :
    Submodule.span ℤ (Set.range integralBasisVectors) =
      Submodule.span ℤ (Set.range (NumberField.integralBasis K)) := by
  rw [span_integralBasisVectors_eq]
  ext x
  rw [Subalgebra.mem_toSubmodule]
  constructor
  · intro hx
    exact (NumberField.mem_span_integralBasis K).mpr (RingHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)
  · intro hx
    obtain ⟨y, hy⟩ := RingHom.mem_range.mp ((NumberField.mem_span_integralBasis K).mp hx)
    exact hy ▸ y.2

/-- The concrete order `ℤ[θ]` inside `K`. -/
abbrev concreteRingOfIntegers : Subalgebra ℤ K := Algebra.adjoin ℤ ({θ} : Set K)

/-- The full ring of integers of `ℚ(√-6)` is `ℤ[θ]` (maximality of the naive order, since
`-6 ≡ 2 (mod 4)`). -/
theorem ringOfIntegers_eq : integralClosure ℤ K = concreteRingOfIntegers := by
  exact integralClosure_eq_adjoin

/-- The number-field discriminant of `ℚ(√-6)` is `-24` (for `d ≡ 2, 3 (mod 4)` squarefree
the discriminant of `ℚ(√d)` is `4d`). In particular the ramified primes are exactly `2`
and `3`, cf. `ramified_iff`. -/
theorem numberField_discr_eq : NumberField.discr K = (-24 : ℤ) := by
  rw [← NumberField.discr_eq_discr K concreteIntegralBasis]
  exact sqrtNegSixExplicitIntegralBasis_discr

/-- The discriminant of the explicit integral basis `1, θ` is `-24`. -/
theorem concreteIntegralBasis_discr :
    Algebra.discr ℤ concreteIntegralBasis = (-24 : ℤ) := by
  exact sqrtNegSixExplicitIntegralBasis_discr

/-- The discriminant of mathlib's canonical field integral basis is `-24`. -/
theorem integralBasis_discr :
    Algebra.discr ℚ (NumberField.integralBasis K) = (-24 : ℚ) := by
  have h := NumberField.coe_discr K
  rw [numberField_discr_eq] at h
  simpa using h.symm


end NumberField.SqrtNegSix


/-!
## Norm Form
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace NumberField.SqrtNegSix

/-- The norm form of `ℚ(√-6)` in the basis `1, θ`: the field norm of `x + yθ` is the
positive-definite binary quadratic form `x² + 6y²`. -/
theorem norm_eq_normForm (x y : ℚ) :
    Algebra.norm ℚ (x • (1 : K) + y • θ) = x ^ 2 + 6 * y ^ 2 := by
  have h : Algebra.norm ℚ (x • (1 : K) + y • θ) =
      QuadraticAlgebra.norm (x • (1 : K) + y • θ) := by
    rw [Algebra.norm_apply, ← QuadraticAlgebra.det_toLinearMap_eq_norm]
    congr 1
  rw [h]
  simp [QuadraticAlgebra.norm_def, θ]
  ring

/-- The integral norm form: on `𝓞 K = ℤ[θ]` the norm of `x + yθ` (with `x, y ∈ ℤ`) is
`x² + 6y²`. -/
theorem intNorm_eq_normForm (x y : ℤ) :
    Algebra.norm ℤ (x • (1 : 𝓞 K) + y • thetaInt) = x ^ 2 + 6 * y ^ 2 := by
  have h1 : ((Algebra.norm ℤ (x • (1 : 𝓞 K) + y • thetaInt) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap (𝓞 K) K (x • (1 : 𝓞 K) + y • thetaInt)) :=
    Algebra.coe_norm_int _
  have h2 : algebraMap (𝓞 K) K (x • (1 : 𝓞 K) + y • thetaInt) =
      (x : ℚ) • (1 : K) + (y : ℚ) • θ := by
    rw [map_add, map_zsmul, map_zsmul, map_one]
    rw [Int.cast_smul_eq_zsmul ℚ x (1 : K), Int.cast_smul_eq_zsmul ℚ y θ]
    rfl
  rw [h2, norm_eq_normForm] at h1
  exact_mod_cast h1

theorem normForm_ne_two (x y : ℤ) : x ^ 2 + 6 * y ^ 2 ≠ 2 := by
  intro h
  have hy_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hx_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hy0 : y ^ 2 = 0 := by nlinarith
  have hx2 : x ^ 2 = 2 := by nlinarith
  have hx_le : x ≤ 1 := by nlinarith [sq_nonneg (x - 1)]
  have hx_ge : -1 ≤ x := by nlinarith [sq_nonneg (x + 1)]
  interval_cases x <;> norm_num at hx2

private theorem normForm_ne_three (x y : ℤ) : x ^ 2 + 6 * y ^ 2 ≠ 3 := by
  intro h
  have hy_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hx_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hy0 : y ^ 2 = 0 := by nlinarith
  have hx3 : x ^ 2 = 3 := by nlinarith
  have hx_le' : 4 * x ≤ 7 := by nlinarith [sq_nonneg (x - 2)]
  have hx_ge' : -7 ≤ 4 * x := by nlinarith [sq_nonneg (x + 2)]
  have hx_le : x ≤ 1 := by omega
  have hx_ge : -1 ≤ x := by omega
  interval_cases x <;> norm_num at hx3

private theorem normForm_ne_five (x y : ℤ) : x ^ 2 + 6 * y ^ 2 ≠ 5 := by
  intro h
  have hy_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hx_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hy0 : y ^ 2 = 0 := by nlinarith
  have hx5 : x ^ 2 = 5 := by nlinarith
  have hx_le' : 6 * x ≤ 14 := by nlinarith [sq_nonneg (x - 3)]
  have hx_ge' : -14 ≤ 6 * x := by nlinarith [sq_nonneg (x + 3)]
  have hx_le : x ≤ 2 := by omega
  have hx_ge : -2 ≤ x := by omega
  interval_cases x <;> norm_num at hx5

/-- The unit equation for `ℚ(√-6)`: `x + yθ` is a unit iff `x² + 6y² = 1`, i.e. iff
`(x, y) = (±1, 0)`. The form is positive definite, so there is no Pell phenomenon. -/
theorem isUnit_iff_normForm (x y : ℤ) :
    IsUnit (x • (1 : 𝓞 K) + y • thetaInt) ↔ x ^ 2 + 6 * y ^ 2 = 1 := by
  rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm, ← Algebra.coe_norm_int,
    intNorm_eq_normForm, abs_eq (by norm_num : (0 : ℚ) ≤ 1)]
  constructor
  · rintro (h | h)
    · exact_mod_cast h
    · have hq : x ^ 2 + 6 * y ^ 2 = (-1 : ℤ) := by exact_mod_cast h
      have hnonneg : (0 : ℤ) ≤ x ^ 2 + 6 * y ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg y]
      omega
  · intro h
    left
    exact_mod_cast h

theorem intNorm_nonneg (z : 𝓞 K) : 0 ≤ Algebra.norm ℤ z := by
  obtain ⟨x, y, hz⟩ := exists_eq_smul_one_add_smul_theta z
  rw [hz, intNorm_eq_normForm]
  nlinarith [sq_nonneg x, sq_nonneg y]

theorem isUnit_iff_intNorm_eq_one (z : 𝓞 K) :
    IsUnit z ↔ Algebra.norm ℤ z = 1 := by
  obtain ⟨x, y, hz⟩ := exists_eq_smul_one_add_smul_theta z
  rw [hz, isUnit_iff_normForm, intNorm_eq_normForm]

theorem intNorm_ne_two (z : 𝓞 K) : Algebra.norm ℤ z ≠ 2 := by
  intro hz2
  obtain ⟨x, y, hz⟩ := exists_eq_smul_one_add_smul_theta z
  rw [hz, intNorm_eq_normForm] at hz2
  exact normForm_ne_two x y hz2

theorem intNorm_ne_three (z : 𝓞 K) : Algebra.norm ℤ z ≠ 3 := by
  intro hz3
  obtain ⟨x, y, hz⟩ := exists_eq_smul_one_add_smul_theta z
  rw [hz, intNorm_eq_normForm] at hz3
  exact normForm_ne_three x y hz3

theorem intNorm_ne_five (z : 𝓞 K) : Algebra.norm ℤ z ≠ 5 := by
  intro hz5
  obtain ⟨x, y, hz⟩ := exists_eq_smul_one_add_smul_theta z
  rw [hz, intNorm_eq_normForm] at hz5
  exact normForm_ne_five x y hz5


end NumberField.SqrtNegSix
