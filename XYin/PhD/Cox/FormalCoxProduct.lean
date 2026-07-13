/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
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

private lemma transformedJSeries_map {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) {m : ℕ+} (ζ : K) (σ : CoxMatrix m) :
    (transformedJSeries ζ σ).map φ = transformedJSeries (φ ζ) σ := by
  ext k
  rw [HahnSeries.map_coeff, transformedJSeries_coeff, transformedJSeries_coeff]
  split_ifs with h
  · rw [map_mul, map_zpow₀]
    simp only [map_intCast]
  · exact map_zero φ

private lemma formalCoxPolynomial_map {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (m : ℕ+) (ζ : K) :
    (formalCoxPolynomial m ζ).map
        { toFun := fun F ↦ F.map φ
          map_zero' := HahnSeries.map_zero φ.toZeroHom
          map_one' := HahnSeries.map_one φ.toMonoidWithZeroHom
          map_add' := fun _ _ ↦ HahnSeries.map_add φ.toAddMonoidHom
          map_mul' := fun _ _ ↦ HahnSeries.map_mul φ.toNonUnitalRingHom } =
      formalCoxPolynomial m (φ ζ) := by
  classical
  simp [formalCoxPolynomial, Polynomial.map_prod, transformedJSeries_map]

private def integralLaurentSeries (K : Type*) [Field K] [CharZero K] :
    Subring (LaurentSeries K) where
  carrier := {F | ∀ k, IsIntegral ℤ (F.coeff k)}
  zero_mem' := by
    intro k
    simpa using (isIntegral_zero : IsIntegral ℤ (0 : K))
  one_mem' := by
    intro k
    by_cases hk : k = 0
    · subst k
      simpa using (isIntegral_one : IsIntegral ℤ (1 : K))
    · simpa [HahnSeries.coeff_one, hk] using (isIntegral_zero : IsIntegral ℤ (0 : K))
  add_mem' := by
    intro F G hF hG k
    simpa using (hF k).add (hG k)
  neg_mem' := by
    intro F hF k
    simpa using (hF k).neg
  mul_mem' := by
    intro F G hF hG k
    rw [HahnSeries.coeff_mul]
    exact IsIntegral.sum _ fun ij _ ↦ (hF ij.1).mul (hG ij.2)

private lemma transformedJSeries_mem_integralLaurentSeries
    {K : Type*} [Field K] [CharZero K] {m : ℕ+} {ζ : K}
    (hζ : IsPrimitiveRoot ζ (m : ℕ)) (σ : CoxMatrix m) :
    transformedJSeries ζ σ ∈ integralLaurentSeries K := by
  intro k
  rw [transformedJSeries_coeff]
  split_ifs
  · apply IsIntegral.mul
    · simpa using (isIntegral_algebraMap :
        IsIntegral ℤ (algebraMap ℤ K (jIntCoeff (k / (σ.a : ℤ) ^ 2))))
    · apply IsIntegral.of_pow (PNat.pos m)
      have hpow : (ζ ^ (((σ.a : ℤ) * (σ.b : ℤ)) *
          (k / (σ.a : ℤ) ^ 2))) ^ (m : ℕ) = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hζ.zpow_eq_one, one_zpow]
      simpa [hpow] using (isIntegral_one : IsIntegral ℤ (1 : K))
  · exact isIntegral_zero

private lemma formalCoxPolynomial_coeff_integral
    {K : Type*} [Field K] [CharZero K] (m : ℕ+) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (m : ℕ)) (n : ℕ) (k : ℤ) :
    IsIntegral ℤ (((formalCoxPolynomial m ζ).coeff n).coeff k) := by
  classical
  let S := integralLaurentSeries K
  let F : CoxMatrix m → S := fun σ ↦
    ⟨transformedJSeries ζ σ, transformedJSeries_mem_integralLaurentSeries hζ σ⟩
  let P : Polynomial S :=
    ∏ σ : CoxMatrix m, (Polynomial.X - Polynomial.C (F σ))
  have hmap : P.map S.subtype = formalCoxPolynomial m ζ := by
    simp [P, F, S, formalCoxPolynomial, Polynomial.map_prod]
  have hcoeff : ((formalCoxPolynomial m ζ).coeff n).coeff k =
      ((P.coeff n : S) : LaurentSeries K).coeff k := by
    have hc := congrArg
      (fun Q : Polynomial (LaurentSeries K) ↦ (Q.coeff n).coeff k) hmap
    simpa [Polynomial.coeff_map] using hc.symm
  rw [hcoeff]
  exact (P.coeff n).property k

private lemma transformedJSeries_pow_eq_reindex
    {K : Type*} [Field K] {m : ℕ+} {ζ : K}
    (hζ : IsPrimitiveRoot ζ (m : ℕ)) (r : ℕ)
    (hr : Nat.Coprime r (m : ℕ)) (σ : CoxMatrix m) :
    transformedJSeries (ζ ^ r) σ = transformedJSeries ζ (reindex r hr σ) := by
  ext k
  rw [transformedJSeries_coeff, transformedJSeries_coeff]
  simp only [reindex]
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
    have hmod : (σ.b : ℤ) * r % σ.d = (((σ.b * r) % σ.d : ℕ) : ℤ) :=
      (Int.natCast_mod (σ.b * r) σ.d).symm
    have hdiff : (σ.b : ℤ) * r - (((σ.b * r) % σ.d : ℕ) : ℤ) =
        (σ.d : ℤ) * q := by
      linarith [hdivZ]
    rw [hdet]
    calc
      (r : ℤ) * ((σ.a : ℤ) * σ.b * (k / (σ.a : ℤ) ^ 2)) -
          (σ.a : ℤ) * ((σ.b * r) % σ.d) * (k / (σ.a : ℤ) ^ 2) =
          (σ.a : ℤ) * (k / (σ.a : ℤ) ^ 2) *
            ((σ.b : ℤ) * r - (((σ.b * r) % σ.d : ℕ) : ℤ)) := by
        rw [hmod]
        ring
      _ = (σ.a : ℤ) * (k / (σ.a : ℤ) ^ 2) * ((σ.d : ℤ) * q) := by
        rw [hdiff]
      _ = (σ.a : ℤ) * σ.d * ((q : ℤ) * (k / (σ.a : ℤ) ^ 2)) := by
        ring
  · rfl

private lemma formalCoxPolynomial_pow_eq
    {K : Type*} [Field K] {m : ℕ+} {ζ : K}
    (hζ : IsPrimitiveRoot ζ (m : ℕ)) (r : ℕ)
    (hr : Nat.Coprime r (m : ℕ)) :
    formalCoxPolynomial m (ζ ^ r) = formalCoxPolynomial m ζ := by
  classical
  rw [formalCoxPolynomial, formalCoxPolynomial]
  calc
    ∏ σ : CoxMatrix m,
        (Polynomial.X - Polynomial.C (transformedJSeries (ζ ^ r) σ)) =
        ∏ σ : CoxMatrix m,
          (Polynomial.X - Polynomial.C (transformedJSeries ζ (reindex r hr σ))) := by
      apply Finset.prod_congr rfl
      intro σ _
      rw [transformedJSeries_pow_eq_reindex hζ r hr σ]
    _ = _ := by
      simpa using (reindex_bijective r hr).prod_comp
        (fun σ : CoxMatrix m ↦
          Polynomial.X - Polynomial.C (transformedJSeries ζ σ))

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
  have hζmap : ζ ^ r = φ ζ := by
    simp [r, u, hζ.autToPow_spec ℚ φ]
  have hpow := formalCoxPolynomial_pow_eq hζ r hr
  have hmap := formalCoxPolynomial_map φ.toRingHom m ζ
  have hpoly :
      (formalCoxPolynomial m ζ).map
          { toFun := fun F ↦ F.map φ.toRingHom
            map_zero' := HahnSeries.map_zero φ.toRingHom.toZeroHom
            map_one' := HahnSeries.map_one φ.toRingHom.toMonoidWithZeroHom
            map_add' := fun _ _ ↦ HahnSeries.map_add φ.toRingHom.toAddMonoidHom
            map_mul' := fun _ _ ↦ HahnSeries.map_mul φ.toRingHom.toNonUnitalRingHom } =
        formalCoxPolynomial m ζ := by
    rw [hmap]
    rw [show φ.toRingEquiv.toRingHom ζ = ζ ^ r by exact hζmap.symm]
    exact hpow
  have hc := congrArg
    (fun P : Polynomial (LaurentSeries K) ↦ (P.coeff n).coeff k) hpoly
  simpa [Polynomial.coeff_map, HahnSeries.map_coeff] using hc

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
    (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp <| by
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
  let ι : zetaField m →+* ℂ :=
    (IntermediateField.adjoin ℚ ({zeta m} : Set ℂ)).val.toRingHom
  have hmap := formalCoxPolynomial_map ι m (zetaFieldRoot m)
  have hcoeff := congrArg
    (fun P : Polynomial (LaurentSeries ℂ) ↦ (P.coeff n).coeff k) hmap
  have hbridge :
      ι (((formalCoxPolynomial m (zetaFieldRoot m)).coeff n).coeff k) =
        ((formalCoxPolynomial m (zeta m)).coeff n).coeff k := by
    simpa [ι, zetaFieldRoot, Polynomial.coeff_map, HahnSeries.map_coeff] using hcoeff
  refine ⟨z, ?_⟩
  calc
    ((formalCoxPolynomial m (zeta m)).coeff n).coeff k =
        ι (((formalCoxPolynomial m (zetaFieldRoot m)).coeff n).coeff k) := hbridge.symm
    _ = ι (z : zetaField m) := congrArg ι hz
    _ = (z : ℂ) := by simp [ι]

end Cox
