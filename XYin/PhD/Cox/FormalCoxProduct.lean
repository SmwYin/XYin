/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.NumberTheory.Cyclotomic.Gal

import XYin.PhD.Cox.CoxMatrices

/-!
# The formal Cox product

This file packages the Laurent-series product from Cox equation (11.13) and proves that all
its coefficients are ordinary integers. The proof works in the concrete cyclotomic subfield
`ℚ(ζₘ) ⊆ ℂ`: Galois automorphisms reindex the Cox representatives, while coefficientwise
integrality descends a fixed coefficient first to `ℚ` and then to `ℤ`.
-/

noncomputable section

namespace Cox

/-- The formal Cox product obtained from the Laurent series in equation (11.13). -/
def formalCoxPolynomial {K : Type*} [Field K] (m : ℕ+) (ζ : K) :
    Polynomial (LaurentSeries K) :=
  ∏ σ : CoxMatrix m,
    (Polynomial.X - Polynomial.C (transformedJSeries ζ σ))

/-- Every transformed series is a root of the formal Cox product. -/
theorem formalCoxPolynomial_eval_transformedJSeries {K : Type*} [Field K] {m : ℕ+} (ζ : K)
    (σ : CoxMatrix m) : (formalCoxPolynomial m ζ).eval (transformedJSeries ζ σ) = 0 := by
  classical
  rw [formalCoxPolynomial, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ σ) (by simp)

/-- Coefficientwise base change of a transformed series changes its phase. -/
theorem transformedJSeries_map {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) {m : ℕ+} (ζ : K) (σ : CoxMatrix m) :
    (transformedJSeries ζ σ).map φ = transformedJSeries (φ ζ) σ := by
  ext k
  rw [HahnSeries.map_coeff, transformedJSeries_coeff, transformedJSeries_coeff]
  split_ifs with h
  · rw [map_mul, map_zpow₀, map_intCast]
  · exact map_zero φ

/-- Coefficientwise base change of the formal Cox product changes its phase. -/
theorem formalCoxPolynomial_map {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (m : ℕ+) (ζ : K) :
    (formalCoxPolynomial m ζ).map (HahnSeries.mapRingHom φ) = formalCoxPolynomial m (φ ζ) := by
  classical
  simp [formalCoxPolynomial, Polynomial.map_prod, transformedJSeries_map]

/-- Coefficientwise form of `formalCoxPolynomial_map`. -/
private lemma formalCoxPolynomial_map_coeff_coeff {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (m : ℕ+) (ζ : K) (n : ℕ) (k : ℤ) :
    φ (((formalCoxPolynomial m ζ).coeff n).coeff k) =
      ((formalCoxPolynomial m (φ ζ)).coeff n).coeff k := by
  rw [← formalCoxPolynomial_map φ, Polynomial.coeff_map]
  rfl

private lemma transformedJSeries_mem_integralLaurentSeries
    {K : Type*} [Field K] {m : ℕ+} {ζ : K}
    (hζ : IsPrimitiveRoot ζ (m : ℕ)) (σ : CoxMatrix m) :
    transformedJSeries ζ σ ∈ HahnSeries.coeffSubring (integralClosure ℤ K).toSubring := by
  intro k
  rw [transformedJSeries_coeff]
  split_ifs
  · refine Subring.mul_mem _ (intCast_mem _ _) (IsIntegral.of_pow (PNat.pos m) ?_)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hζ.zpow_eq_one, one_zpow]
    exact isIntegral_one
  · exact zero_mem _

private lemma formalCoxPolynomial_coeff_integral
    {K : Type*} [Field K] (m : ℕ+) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (m : ℕ)) (n : ℕ) (k : ℤ) :
    IsIntegral ℤ (((formalCoxPolynomial m ζ).coeff n).coeff k) := by
  classical
  let S := HahnSeries.coeffSubring (Γ := ℤ) (integralClosure ℤ K).toSubring
  let P : Polynomial S := ∏ σ : CoxMatrix m, (Polynomial.X - Polynomial.C
    ⟨transformedJSeries ζ σ, transformedJSeries_mem_integralLaurentSeries hζ σ⟩)
  have hmap : P.map S.subtype = formalCoxPolynomial m ζ := by
    simp [P, formalCoxPolynomial, Polynomial.map_prod]
  rw [← hmap, Polynomial.coeff_map]
  exact (P.coeff n).property k

private lemma transformedJSeries_pow_eq_reindex
    {K : Type*} [Field K] {m : ℕ+} {ζ : K}
    (hζ : IsPrimitiveRoot ζ (m : ℕ)) (r : ℕ)
    (hr : Nat.Coprime r (m : ℕ)) (σ : CoxMatrix m) :
    transformedJSeries (ζ ^ r) σ = transformedJSeries ζ (reindex r hr σ) := by
  ext k
  rw [transformedJSeries_coeff, transformedJSeries_coeff, reindex_a, reindex_b]
  split_ifs with hk
  · congr 1
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (PNat.ne_zero m)
    rw [← zpow_natCast, ← zpow_mul]
    apply (div_eq_one_iff_eq (zpow_ne_zero _ hζ0)).mp
    rw [← zpow_sub₀ hζ0]
    apply (hζ.zpow_eq_one_iff_dvd _).2
    let q := (σ.b * r) / σ.d
    refine ⟨(q : ℤ) * (k / (σ.a : ℤ) ^ 2), ?_⟩
    have hdiv : (σ.b * r) % σ.d + σ.d * q = σ.b * r := by
      simpa [q] using Nat.mod_add_div (σ.b * r) σ.d
    have hdet : (m : ℤ) = (σ.a : ℤ) * σ.d := by
      exact_mod_cast σ.determinant.symm
    have hdivZ := congrArg (fun x : ℕ ↦ (x : ℤ)) hdiv
    simp only [Nat.cast_add, Nat.cast_mul] at hdivZ
    rw [hdet]
    linear_combination -(σ.a : ℤ) * (k / (σ.a : ℤ) ^ 2) * hdivZ
  · rfl

private lemma formalCoxPolynomial_pow_eq
    {K : Type*} [Field K] {m : ℕ+} {ζ : K}
    (hζ : IsPrimitiveRoot ζ (m : ℕ)) (r : ℕ)
    (hr : Nat.Coprime r (m : ℕ)) :
    formalCoxPolynomial m (ζ ^ r) = formalCoxPolynomial m ζ := by
  classical
  simp_rw [formalCoxPolynomial, transformedJSeries_pow_eq_reindex hζ r hr]
  exact (reindex_bijective r hr).prod_comp
    (fun σ : CoxMatrix m ↦ Polynomial.X - Polynomial.C (transformedJSeries ζ σ))

private lemma formalCoxPolynomial_coeff_fixed
    {K : Type*} [Field K] [Algebra ℚ K] {m : ℕ+} {ζ : K}
    (hζ : IsPrimitiveRoot ζ (m : ℕ))
    [IsCyclotomicExtension {(m : ℕ)} ℚ K]
    (n : ℕ) (k : ℤ) (φ : K ≃ₐ[ℚ] K) :
    φ (((formalCoxPolynomial m ζ).coeff n).coeff k) =
      ((formalCoxPolynomial m ζ).coeff n).coeff k := by
  let u : (ZMod (m : ℕ))ˣ := hζ.autToPow ℚ φ
  let r : ℕ := u.val.val
  have hr : Nat.Coprime r (m : ℕ) := by
    simpa [r, u] using ZMod.val_coe_unit_coprime u
  have hζmap : φ.toRingHom ζ = ζ ^ r := by
    simp [r, u, hζ.autToPow_spec ℚ φ]
  have h := formalCoxPolynomial_map_coeff_coeff φ.toRingHom m ζ n k
  rwa [hζmap, formalCoxPolynomial_pow_eq hζ r hr] at h

private lemma formalCoxPolynomial_coeff_eq_int
    {K : Type*} [Field K] [Algebra ℚ K] {m : ℕ+} {ζ : K}
    (hζ : IsPrimitiveRoot ζ (m : ℕ))
    [IsCyclotomicExtension {(m : ℕ)} ℚ K]
    (n : ℕ) (k : ℤ) :
    ∃ z : ℤ, ((formalCoxPolynomial m ζ).coeff n).coeff k = (z : K) := by
  letI : CharZero K :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℚ K)
  letI : FiniteDimensional ℚ K :=
    IsCyclotomicExtension.finiteDimensional {(m : ℕ)} ℚ K
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {(m : ℕ)} ℚ K
  let x : K := ((formalCoxPolynomial m ζ).coeff n).coeff k
  have hxint : IsIntegral ℤ x := formalCoxPolynomial_coeff_integral m hζ n k
  have hfixed : ∀ φ : K ≃ₐ[ℚ] K, φ x = x :=
    formalCoxPolynomial_coeff_fixed hζ n k
  have hxrange : x ∈ Set.range (algebraMap ℚ K) :=
    (IsGalois.mem_range_algebraMap_iff_fixed x).2 hfixed
  obtain ⟨q, hq⟩ := hxrange
  have hqint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (B := K)).mp <| by
      simpa [x, hq] using hxint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  refine ⟨z, ?_⟩
  calc
    ((formalCoxPolynomial m ζ).coeff n).coeff k = algebraMap ℚ K q := hq.symm
    _ = algebraMap ℚ K (algebraMap ℤ ℚ z) := by rw [hz]
    _ = (z : K) := by simp

private abbrev zetaField (m : ℕ+) :=
  IntermediateField.adjoin ℚ ({zeta m} : Set ℂ)

private def zetaFieldRoot (m : ℕ+) : zetaField m :=
  ⟨zeta m, IntermediateField.subset_adjoin ℚ ({zeta m} : Set ℂ) (by simp)⟩

private lemma zetaFieldRoot_isPrimitiveRoot (m : ℕ+) :
    IsPrimitiveRoot (zetaFieldRoot m) (m : ℕ) := by
  rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
  exact zeta_isPrimitiveRoot m

private noncomputable instance zetaField_isCyclotomicExtension (m : ℕ+) :
    IsCyclotomicExtension {(m : ℕ)} ℚ (zetaField m) := by
  change IsCyclotomicExtension {(m : ℕ)} ℚ
    (IntermediateField.adjoin ℚ ({zeta m} : Set ℂ)).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (((zeta_isPrimitiveRoot m).isIntegral (PNat.pos m)).tower_top).isAlgebraic]
  exact (zeta_isPrimitiveRoot m).adjoin_isCyclotomicExtension ℚ

/-- Every coefficient of the formal Cox product is an ordinary integer. -/
theorem formalCoxPolynomial_coeff_isInteger
    (m : ℕ+) (n : ℕ) (k : ℤ) :
    ∃ z : ℤ, ((formalCoxPolynomial m (zeta m)).coeff n).coeff k = (z : ℂ) := by
  obtain ⟨z, hz⟩ := formalCoxPolynomial_coeff_eq_int
    (zetaFieldRoot_isPrimitiveRoot m) n k
  refine ⟨z, ?_⟩
  have h := formalCoxPolynomial_map_coeff_coeff (zetaField m).val.toRingHom m
    (zetaFieldRoot m) n k
  rw [hz, map_intCast] at h
  simpa [zetaFieldRoot] using h.symm

end Cox
