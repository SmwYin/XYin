/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.CyclicSublattice.Classification
import XYin.PhD.Cox.LevelThree
import XYin.PhD.Cox.ModularFunctionField

/-!
# Arithmetic of the modular polynomial: Cox Theorem 11.18

The integral modular polynomial `Φ_m ∈ ℤ[X][Y]` maps to the complex one (Theorem 11.18(i)), is
irreducible in its root variable over the rational function field of its parameter (ii), is
symmetric for `m > 1` (iii), and for nonsquare `m` its diagonal `Φ_m(X, X)` (in Lean
`Φ_m.eval X`) has leading coefficient `±1` and degree `> 1` (iv). The explicit level-three
polynomial (11.22) follows from the symmetry. The variable convention (outer variable `Y` =
Cox's root variable `X`, inner variable `C X` = Cox's parameter `Y`) is explained in
`XYin.PhD.Cox.ModularPolynomial.Construction`.
-/

open Polynomial UpperHalfPlane
open scoped Polynomial.Bivariate

noncomputable section

/-- In a domain whose only units are `±1`, the only units of the polynomial ring are `±1`. -/
theorem Polynomial.eq_one_or_eq_neg_one_of_isUnit {R : Type*} [CommRing R] [IsDomain R]
    (hR : ∀ r : R, IsUnit r → r = 1 ∨ r = -1) {p : Polynomial R} (hp : IsUnit p) :
    p = 1 ∨ p = -1 := by
  obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.1 hp
  rcases hR r hr with rfl | rfl <;> simp

/-- Over a domain whose only units are `±1`, associated polynomials agree up to sign. -/
theorem Polynomial.eq_or_eq_neg_of_associated {R : Type*} [CommRing R] [IsDomain R]
    (hR : ∀ r : R, IsUnit r → r = 1 ∨ r = -1) {P Q : Polynomial R} (h : Associated P Q) :
    Q = P ∨ Q = -P := by
  obtain ⟨u, rfl⟩ := h
  rcases Polynomial.eq_one_or_eq_neg_one_of_isUnit hR u.isUnit with hu | hu <;> simp [hu]

namespace Cox

open UpperHalfPlaneFunctionField

/-- Theorem 11.18(i): the integral modular polynomial maps to the complex one. -/
theorem theorem_11_18_i (m : ℕ+) :
    (modularPolynomial m).map (mapRingHom (Int.castRingHom ℂ)) = modularPolynomialC m :=
  modularPolynomial_map_complex m

/-- Theorem 11.18(ii): Cox's `Φ_m(X, Y)` is irreducible as a polynomial in the root variable `X`
over `ℂ(Y)`. In Lean the root variable is the outer variable and `ℂ(Y)` is `RatFunc ℂ`, the
fraction field of the coefficient ring `ℂ[X]` (the parameter being the inner variable). -/
theorem theorem_11_18_ii (m : ℕ+) :
    Irreducible (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      (modularPolynomialC m)) := irreducible_map_modularPolynomialC m

/-- Dual cyclic inclusions make the complex modular curve invariant under exchanging its two
coordinates: Cox's `Φ_m(u, v) = 0 ↔ Φ_m(v, u) = 0`. -/
theorem modularPolynomial_map_complex_zero_swap (m : ℕ+) (u v : ℂ) :
    ((modularPolynomial m).map (mapRingHom (Int.castRingHom ℂ))).evalEval v u = 0 ↔
      ((modularPolynomial m).map (mapRingHom (Int.castRingHom ℂ))).evalEval u v = 0 := by
  suffices hswap : ∀ u v : ℂ,
      ((modularPolynomial m).map (mapRingHom (Int.castRingHom ℂ))).evalEval v u = 0 →
      ((modularPolynomial m).map (mapRingHom (Int.castRingHom ℂ))).evalEval u v = 0 from
    ⟨hswap u v, hswap v u⟩
  intro u v h
  obtain ⟨L, S, hu, hv⟩ := (theorem_11_23 m u v).mp h
  exact (theorem_11_23 m v u).mpr
    ⟨S.toPeriodPair, S.dual, hv.trans S.dual_sub_j.symm, hu.trans S.dual_base_j.symm⟩

private theorem modularPolynomialC_evalEval_levelJ_j (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).evalEval (levelJ m τ) (j τ) = 0 := by
  rw [← modularPolynomial_map_complex]
  exact (modularPolynomial_map_complex_zero_swap m (levelJ m τ) (j τ)).mp <| by
    rw [modularPolynomial_map_complex]
    exact modularPolynomialC_evalEval_j_levelJ m τ

private theorem aeval_base_eq_zero_of_forall_evalEval_eq_zero
    (m : ℕ+) (F : ℂ[X][Y])
    (hF : ∀ τ : ℍ, F.evalEval (j τ) (levelJ m τ) = 0) :
    aeval (rightCosetRoot m (baseRightCoset m))
      (F.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) = 0 := by
  rw [rightCosetRoot_baseRightCoset, ← evalJLevel_eq_aeval, evalJLevel, RingHom.comp_apply,
    show evalJLevelHol m F = 0 from HolomorphicFunction.ext fun τ ↦ by
      simpa using hF τ, map_zero]

/-- The modular polynomial divides its image under swapping the two variables. -/
theorem modularPolynomial_dvd_swap (m : ℕ+) :
    modularPolynomial m ∣ Bivariate.swap (modularPolynomial m) := by
  have hQzero := aeval_base_eq_zero_of_forall_evalEval_eq_zero m
    (Bivariate.swap (modularPolynomialC m)) fun τ ↦ by
      rw [← coe_aevalAeval_eq_evalEval, Bivariate.aevalAeval_swap, coe_aevalAeval_eq_evalEval]
      exact modularPolynomialC_evalEval_levelJ_j m τ
  have hC : modularPolynomialC m ∣ Bivariate.swap (modularPolynomialC m) :=
    (map_dvd_map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)) (modularPolynomialC_monic m)).mp
      (modularPolynomialC_map_eq_minpoly m ▸ minpoly.dvd _ _ hQzero)
  refine (map_dvd_map (mapRingHom (Int.castRingHom ℂ))
    (map_injective _ Int.cast_injective) (modularPolynomial_monic m)).mp ?_
  rwa [modularPolynomial_map_complex_swap, modularPolynomial_map_complex]

private theorem modularPolynomialC_not_anti (m : ℕ+) (hm : 1 < (m : ℕ)) :
    Bivariate.swap (modularPolynomialC m) ≠ -(modularPolynomialC m) := by
  intro hanti
  have hdiag : (modularPolynomialC m).eval X = 0 := by
    have h := congrArg (eval X) hanti
    rw [Bivariate.eval_X_swap, eval_neg] at h
    exact CharZero.eq_neg_self_iff.mp h
  have hdiv : Y - C X ∣ modularPolynomialC m := dvd_iff_isRoot.mpr hdiag
  let f : Polynomial ℂ →+* RatFunc ℂ := algebraMap _ _
  let P : Polynomial (RatFunc ℂ) := Polynomial.map f (modularPolynomialC m)
  have hdivP : Polynomial.X - Polynomial.C (f Polynomial.X) ∣ P := by
    simpa only [P, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] using Polynomial.map_dvd f hdiv
  have hI : Irreducible P := by
    simpa only [P, f] using irreducible_map_modularPolynomialC m
  obtain hunit | hassoc := hI.dvd_iff.mp hdivP
  · exact Polynomial.not_isUnit_X_sub_C (f Polynomial.X) hunit
  · have hdegree_le : P.natDegree ≤ 1 := by
      rw [← Polynomial.natDegree_X_sub_C (f Polynomial.X)]
      exact Polynomial.natDegree_le_of_dvd hassoc.dvd
        (Polynomial.monic_X_sub_C (f Polynomial.X)).ne_zero
    have hdegree : P.natDegree = Fintype.card (CoxMatrix m) := by
      exact ((modularPolynomialC_monic m).natDegree_map f).trans
        (modularPolynomialC_natDegree m)
    rw [hdegree] at hdegree_le
    exact (not_le_of_gt (one_lt_card_coxMatrix m hm)) hdegree_le

/-- Theorem 11.18(iii): the modular polynomial is symmetric at every level above one. -/
theorem theorem_11_18_iii (m : ℕ+) (hm : 1 < (m : ℕ)) :
    Polynomial.Bivariate.swap (modularPolynomial m) = modularPolynomial m := by
  have hdiv := modularPolynomial_dvd_swap m
  have hdiv' : Polynomial.Bivariate.swap (modularPolynomial m) ∣
      modularPolynomial m := by
    simpa only [Polynomial.Bivariate.swap_swap_apply] using
      (show Polynomial.Bivariate.swap (modularPolynomial m) ∣
        Polynomial.Bivariate.swap (Polynomial.Bivariate.swap (modularPolynomial m)) from
        Polynomial.Bivariate.swap.map_dvd hdiv)
  obtain heq | hanti := Polynomial.eq_or_eq_neg_of_associated
    (fun _ ↦ Polynomial.eq_one_or_eq_neg_one_of_isUnit fun _ ↦ Int.isUnit_iff.1)
    (associated_of_dvd_dvd hdiv hdiv')
  · exact heq
  · refine absurd ?_ (modularPolynomialC_not_anti m hm)
    have hmap := congrArg (Polynomial.map (mapRingHom (Int.castRingHom ℂ))) hanti
    rwa [modularPolynomial_map_complex_swap, Polynomial.map_neg,
      modularPolynomial_map_complex] at hmap

/-- The diagonal polynomial, Cox's `Φ_m(X, X)`: both variables of `ℤ[X][Y]` are set to `X`. -/
def modularPolynomialDiagonal (m : ℕ+) : Polynomial ℤ :=
  (modularPolynomial m).eval X

/-- The integral form of Cox equation (11.19), with the explicit exponent `2m`. -/
theorem modularPolynomialDiagonal_leadingCoeff_pow_two_mul
    (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    (modularPolynomialDiagonal m).leadingCoeff ^ (2 * (m : ℕ)) = 1 := by
  let D := modularPolynomialDiagonal m
  let DC := (modularPolynomialC m).eval X
  have hmap : D.map (Int.castRingHom ℂ) = DC := by
    dsimp only [D, DC, modularPolynomialDiagonal]
    rw [← map_mapRingHom_eval_map, map_X, modularPolynomial_map_complex]
  have hlc : (D.leadingCoeff : ℂ) = DC.leadingCoeff := by
    rw [← hmap, Polynomial.leadingCoeff_map_of_injective Int.cast_injective]
    rfl
  have h := modularPolynomialC_eval_X_leadingCoeff_pow m hm
  rw [← hlc] at h
  exact_mod_cast h

/-- Cox equation (11.19): before integrality is used, the leading diagonal coefficient is a
root of unity. -/
theorem modularPolynomialDiagonal_leadingCoeff_isRootOfUnity
    (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    ∃ k : ℕ, 0 < k ∧ (modularPolynomialDiagonal m).leadingCoeff ^ k = 1 := by
  exact ⟨2 * (m : ℕ), Nat.mul_pos (by decide) (PNat.pos m),
    modularPolynomialDiagonal_leadingCoeff_pow_two_mul m hm⟩

/-- Theorem 11.18(iv), leading coefficient assertion. -/
theorem theorem_11_18_iv_leadingCoeff (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    (modularPolynomialDiagonal m).leadingCoeff = 1 ∨
      (modularPolynomialDiagonal m).leadingCoeff = -1 := by
  obtain ⟨k, hk, hpow⟩ :=
    modularPolynomialDiagonal_leadingCoeff_isRootOfUnity m hm
  rcases (pow_eq_one_iff_of_ne_zero hk.ne').mp hpow with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

private noncomputable def diagonalFixedPoint (m : ℕ+) : ℍ :=
  ⟨Complex.I * (Real.sqrt (m : ℝ) : ℂ)⁻¹, by
    rw [Complex.mul_im]
    norm_num⟩

private theorem diagonalFixedPoint_scale_eq (m : ℕ+) :
    natScale m (diagonalFixedPoint m) = ModularGroup.S • diagonalFixedPoint m := by
  rw [UpperHalfPlane.modular_S_smul]
  apply UpperHalfPlane.ext
  simp only [coe_natScale, diagonalFixedPoint, UpperHalfPlane.coe_mk]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast PNat.pos m
  have hsqrt : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hmpos.le
  have hsqrt0 : (Real.sqrt (m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hmpos).ne'
  have hsqrtC : (Real.sqrt (m : ℝ) : ℂ) ^ 2 = (m : ℂ) := by
    exact_mod_cast hsqrt
  field_simp
  rw [hsqrtC]
  norm_num

private theorem levelJ_diagonalFixedPoint (m : ℕ+) :
    levelJ m (diagonalFixedPoint m) = j (diagonalFixedPoint m) := by
  rw [levelJ_apply, diagonalFixedPoint_scale_eq, j_modularGroup_smul]

private theorem modularPolynomialDiagonal_map_eval_fixedPoint (m : ℕ+) :
    ((modularPolynomialDiagonal m).map (Int.castRingHom ℂ)).eval
      (j (diagonalFixedPoint m)) = 0 := by
  rw [modularPolynomialDiagonal, ← map_mapRingHom_eval_map, map_X, Bivariate.eval_eval_X,
    modularPolynomial_map_complex]
  have h := modularPolynomialC_evalEval_j_levelJ m (diagonalFixedPoint m)
  rwa [levelJ_diagonalFixedPoint] at h

/-- Theorem 11.18(iv), degree assertion. -/
theorem theorem_11_18_iv_degree (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    1 < (modularPolynomialDiagonal m).natDegree := by
  set P := modularPolynomialDiagonal m
  have hlc : P.leadingCoeff = 1 ∨ P.leadingCoeff = -1 := theorem_11_18_iv_leadingCoeff m hm
  have hP : P ≠ 0 := Polynomial.leadingCoeff_ne_zero.1 (by rcases hlc with h | h <;> simp [h])
  have hpos : 0 < P.natDegree :=
    Polynomial.natDegree_pos_of_eval₂_root hP (Int.castRingHom ℂ)
      (by simpa only [Polynomial.eval₂_eq_eval_map] using
        modularPolynomialDiagonal_map_eval_fixedPoint m)
      fun _ h ↦ Int.cast_eq_zero.mp h
  have hmgt : 1 < (m : ℕ) := lt_of_le_of_ne m.pos fun h ↦ hm ⟨1, by simp [← h]⟩
  -- By symmetry, the linear coefficient of the diagonal is even.
  have hcoeff : P.coeff 1 = 2 * ((modularPolynomial m).coeff 1).coeff 0 := by
    change ((modularPolynomial m).eval X).coeff 1 = _
    rw [Bivariate.coeff_eval_X_one, ← Bivariate.coeff_coeff_swap _ 1 0, theorem_11_18_iii m hmgt,
      two_mul]
  have hne : P.natDegree ≠ 1 := fun hd ↦ by
    rw [← hd, Polynomial.coeff_natDegree] at hcoeff
    rcases hlc with hlc | hlc <;> lia
  lia

/-- Cox equation (11.22), the explicit level-three modular polynomial. -/
theorem modularPolynomial_three :
    modularPolynomial (3 : ℕ+) = modularPolynomialThreeExplicit := by
  apply modularPolynomial_three_of_complex_swap
  rw [← modularPolynomial_map_complex_swap, theorem_11_18_iii 3 (by norm_num),
    modularPolynomial_map_complex]

end Cox
