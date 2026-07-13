/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.CyclicSublattice.Classification
import XYin.PhD.Cox.LevelThree

/-!
# Arithmetic of the modular polynomial: Cox Theorem 11.18
-/

open UpperHalfPlane

noncomputable section

namespace Cox

open UpperHalfPlaneFunctionField

/-- Theorem 11.18(i): the integral modular polynomial maps to the complex one. -/
theorem theorem_11_18_i (m : ℕ+) :
    BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m) =
      modularPolynomialC m := modularPolynomial_map_complex m

/-- Theorem 11.18(ii): irreducibility as a polynomial in the root variable `X`, over the
coefficient field `ℂ(Y)`. -/
theorem theorem_11_18_ii (m : ℕ+) :
    Irreducible (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      (modularPolynomialC m)) := modularPolynomialC_irreducibleInX m

/-- Dual cyclic inclusions make the complex modular curve invariant under exchanging its two
coordinates. -/
theorem modularPolynomial_map_complex_zero_swap (m : ℕ+) (u v : ℂ) :
    (BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m)).eval u v = 0 ↔
      (BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m)).eval v u = 0 := by
  constructor
  · intro h
    obtain ⟨L, S, hu, hv⟩ := (theorem_11_23 m u v).mp h
    exact (theorem_11_23 m v u).mpr
      ⟨S.toPeriodPair, S.dual, hv.trans S.dual_sub_j.symm,
        hu.trans S.dual_base_j.symm⟩
  · intro h
    obtain ⟨L, S, hv, hu⟩ := (theorem_11_23 m v u).mp h
    exact (theorem_11_23 m u v).mpr
      ⟨S.toPeriodPair, S.dual, hu.trans S.dual_sub_j.symm,
        hv.trans S.dual_base_j.symm⟩

private theorem modularPolynomialC_eval_j_levelJ (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).eval (j τ) (levelJ m τ) = 0 := by
  rw [← modularPolynomial_map_complex]
  exact (modularPolynomial_map_complex_zero_swap m (levelJ m τ) (j τ)).mp <| by
    rw [modularPolynomial_map_complex]
    exact modularPolynomialC_eval_levelJ_j m τ

private theorem aeval_base_eq_zero_of_forall_eval_eq_zero
    (m : ℕ+) (F : BivariatePolynomial ℂ)
    (hF : ∀ τ : ℍ, F.eval (levelJ m τ) (j τ) = 0) :
    Polynomial.aeval (rightCosetRoot m (baseRightCoset m))
      (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) F) = 0 := by
  let f : HolomorphicFunction := rightCosetFunction m (baseRightCoset m)
  have hf : f.1 = levelJ m := by
    funext τ
    change rightCosetEval m (baseRightCoset m) τ = levelJ m τ
    rw [baseRightCoset, rightCosetEval_mk]
    simp
  have heval : Polynomial.eval f (Polynomial.map evalJ F) = 0 := by
    apply Subtype.ext
    funext τ
    change evaluation τ (Polynomial.eval f (Polynomial.map evalJ F)) = 0
    rw [← Polynomial.eval₂_hom (evaluation τ) f, Polynomial.eval₂_map]
    have hevalJ : (evaluation τ).comp evalJ = Polynomial.evalRingHom (j τ) := by
      apply DFunLike.ext _ _
      intro P
      exact evalJ_apply P τ
    rw [hevalJ, show evaluation τ f = levelJ m τ from congrFun hf τ]
    change Polynomial.eval₂ (Polynomial.evalRingHom (j τ))
      (levelJ m τ) F = 0
    rw [congrFun (congrFun (Polynomial.eval₂_evalRingHom (j τ))
      (levelJ m τ)) F]
    exact hF τ
  rw [Polynomial.aeval_def, ← Polynomial.eval_map]
  have hcoeff :
      (algebraMap (RatFunc ℂ) FunctionField).comp
        (algebraMap (Polynomial ℂ) (RatFunc ℂ)) = evalJFracPoly := by
    apply DFunLike.ext _ _
    intro P
    exact ratFuncEvalJ_algebraMap P
  have hpoly :
      Polynomial.map (algebraMap (RatFunc ℂ) FunctionField)
          (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) F) =
        Polynomial.map (algebraMap HolomorphicFunction FunctionField)
          (Polynomial.map evalJ F) := by
    rw [Polynomial.map_map, Polynomial.map_map, hcoeff]
    rfl
  rw [hpoly]
  change Polynomial.eval ((algebraMap HolomorphicFunction FunctionField) f)
    (Polynomial.map (algebraMap HolomorphicFunction FunctionField)
      (Polynomial.map evalJ F)) = 0
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, heval, map_zero]

/-- The modular polynomial divides its image under swapping the two variables. -/
theorem modularPolynomial_dvd_swap (m : ℕ+) :
    modularPolynomial m ∣ Polynomial.Bivariate.swap (modularPolynomial m) := by
  let α : FunctionField := rightCosetRoot m (baseRightCoset m)
  let P : Polynomial (RatFunc ℂ) :=
    Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (modularPolynomialC m)
  let Q : Polynomial (RatFunc ℂ) :=
    Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      (Polynomial.Bivariate.swap (modularPolynomialC m))
  have hPzero : Polynomial.aeval α P = 0 :=
    aeval_base_eq_zero_of_forall_eval_eq_zero m (modularPolynomialC m)
      (modularPolynomialC_eval_levelJ_j m)
  have hQzero : Polynomial.aeval α Q = 0 := by
    apply aeval_base_eq_zero_of_forall_eval_eq_zero m
    intro τ
    rw [BivariatePolynomial.eval_swap]
    exact modularPolynomialC_eval_j_levelJ m τ
  have hPmin : P = minpoly (RatFunc ℂ) α :=
    minpoly.eq_of_irreducible_of_monic
      (modularPolynomialC_irreducibleInX m) hPzero
      ((modularPolynomialC_monic m).map _)
  have hRat : P ∣ Q := by
    rw [hPmin]
    exact minpoly.dvd (RatFunc ℂ) α hQzero
  have hC : modularPolynomialC m ∣
      Polynomial.Bivariate.swap (modularPolynomialC m) :=
    (Polynomial.map_dvd_map
      (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))
      (modularPolynomialC_monic m)).mp hRat
  let f := Polynomial.mapRingHom (Int.castRingHom ℂ)
  have hf : Function.Injective f :=
    Polynomial.map_injective _ Int.cast_injective
  apply (Polynomial.map_dvd_map f hf (modularPolynomial_monic m)).mp
  change BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m) ∣
    BivariatePolynomial.map (Int.castRingHom ℂ)
      (Polynomial.Bivariate.swap (modularPolynomial m))
  rw [BivariatePolynomial.map_swap, modularPolynomial_map_complex]
  exact hC

private theorem modularPolynomialC_not_anti (m : ℕ+) (hm : 1 < (m : ℕ)) :
    Polynomial.Bivariate.swap (modularPolynomialC m) ≠ -(modularPolynomialC m) := by
  intro hanti
  have hdiag : BivariatePolynomial.diagonal (modularPolynomialC m) = 0 := by
    have h := congrArg BivariatePolynomial.diagonal hanti
    rw [BivariatePolynomial.diagonal_swap] at h
    simp only [BivariatePolynomial.diagonal, Polynomial.eval_neg] at h
    exact CharZero.eq_neg_self_iff.mp h
  have hdiv : Polynomial.X - Polynomial.C Polynomial.X ∣ modularPolynomialC m := by
    rw [Polynomial.dvd_iff_isRoot]
    simpa only [BivariatePolynomial.diagonal] using hdiag
  let f : Polynomial ℂ →+* RatFunc ℂ := algebraMap _ _
  let P : Polynomial (RatFunc ℂ) := Polynomial.map f (modularPolynomialC m)
  have hdivP : Polynomial.X - Polynomial.C (f Polynomial.X) ∣ P := by
    simpa only [P, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] using Polynomial.map_dvd f hdiv
  have hI : Irreducible P := by
    simpa only [P, f] using modularPolynomialC_irreducibleInX m
  obtain hunit | hassoc := hI.dvd_iff.mp hdivP
  · exact Polynomial.not_isUnit_X_sub_C (f Polynomial.X) hunit
  · have hdegree_le : P.natDegree ≤ 1 := by
      rw [← Polynomial.natDegree_X_sub_C (f Polynomial.X)]
      exact Polynomial.natDegree_le_of_dvd hassoc.dvd
        (Polynomial.monic_X_sub_C (f Polynomial.X)).ne_zero
    have hdegree : P.natDegree = Fintype.card (CoxMatrix m) := by
      calc
        P.natDegree = (modularPolynomialC m).natDegree := by
          simpa only [P] using (modularPolynomialC_monic m).natDegree_map f
        _ = Fintype.card (CoxMatrix m) := modularPolynomialC_natDegree m
    rw [hdegree] at hdegree_le
    exact (not_le_of_gt (one_lt_card_coxMatrix m hm)) hdegree_le

private theorem eq_or_eq_neg_of_associated_int_bivariate
    {P Q : BivariatePolynomial ℤ} (h : Associated P Q) : Q = P ∨ Q = -P := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.mp u.isUnit
  obtain ⟨z, hz, hzr⟩ := Polynomial.isUnit_iff.mp hr
  obtain rfl | rfl := Int.isUnit_iff.mp hz
  · left
    rw [← hu, ← hru, ← hzr]
    simp
  · right
    rw [← hu, ← hru, ← hzr]
    simpa only [map_neg, map_one] using mul_neg_one P

/-- Theorem 11.18(iii): the modular polynomial is symmetric at every level above one. -/
theorem theorem_11_18_iii (m : ℕ+) (hm : 1 < (m : ℕ)) :
    Polynomial.Bivariate.swap (modularPolynomial m) = modularPolynomial m := by
  have hdiv := modularPolynomial_dvd_swap m
  have hdiv' : Polynomial.Bivariate.swap (modularPolynomial m) ∣
      modularPolynomial m := by
    have h := Polynomial.Bivariate.swap.map_dvd hdiv
    change Polynomial.Bivariate.swap (modularPolynomial m) ∣
      Polynomial.Bivariate.swap
        (Polynomial.Bivariate.swap (modularPolynomial m)) at h
    simpa only [Polynomial.Bivariate.swap_swap_apply] using h
  obtain heq | hanti := eq_or_eq_neg_of_associated_int_bivariate
    (associated_of_dvd_dvd hdiv hdiv')
  · exact heq
  · exfalso
    apply modularPolynomialC_not_anti m hm
    have hmap := congrArg
      (BivariatePolynomial.map (Int.castRingHom ℂ)) hanti
    rw [BivariatePolynomial.map_swap, modularPolynomial_map_complex] at hmap
    simp only [BivariatePolynomial.map, Polynomial.map_neg] at hmap
    change Polynomial.Bivariate.swap (modularPolynomialC m) =
      -BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m) at hmap
    rw [modularPolynomial_map_complex] at hmap
    exact hmap

/-- The diagonal polynomial `Φ_m(X,X)`. -/
def modularPolynomialDiagonal (m : ℕ+) : Polynomial ℤ :=
  BivariatePolynomial.diagonal (modularPolynomial m)

/-- The integral form of Cox equation (11.19), with the explicit exponent `2m`. -/
theorem modularPolynomialDiagonal_leadingCoeff_pow_two_mul
    (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    (modularPolynomialDiagonal m).leadingCoeff ^ (2 * (m : ℕ)) = 1 := by
  let D := modularPolynomialDiagonal m
  let DC := BivariatePolynomial.diagonal (modularPolynomialC m)
  have hmap : D.map (Int.castRingHom ℂ) = DC := by
    dsimp only [D, DC, modularPolynomialDiagonal]
    rw [← BivariatePolynomial.diagonal_map, modularPolynomial_map_complex]
  have hlc : (D.leadingCoeff : ℂ) = DC.leadingCoeff := by
    have h := Polynomial.leadingCoeff_map_of_injective
      (f := Int.castRingHom ℂ) Int.cast_injective D
    rw [hmap] at h
    exact h.symm
  have h := modularPolynomialC_diagonal_leadingCoeff_pow m hm
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

private theorem diagonal_coeff_one {R : Type*} [CommRing R]
    (Φ : BivariatePolynomial R) :
    (BivariatePolynomial.diagonal Φ).coeff 1 =
      (Φ.coeff 0).coeff 1 + (Φ.coeff 1).coeff 0 := by
  induction Φ using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [BivariatePolynomial.diagonal, Polynomial.eval_add,
        Polynomial.coeff_add] at hP hQ ⊢
      rw [hP, hQ]
      ring
  | monomial n P =>
      rcases n with _ | n
      · simp [BivariatePolynomial.diagonal]
      · rcases n with _ | n
        · simp [BivariatePolynomial.diagonal]
        · simp only [BivariatePolynomial.diagonal, Polynomial.eval_monomial]
          rw [Polynomial.coeff_mul_X_pow']
          simp [Polynomial.coeff_monomial]

private noncomputable def diagonalFixedPoint (m : ℕ+) : ℍ :=
  ⟨Complex.I * (Real.sqrt (m : ℝ) : ℂ)⁻¹, by
    rw [Complex.mul_im]
    norm_num⟩

private theorem diagonalFixedPoint_scale_eq (m : ℕ+) :
    (⟨(m : ℂ) * (diagonalFixedPoint m : ℂ), by
      rw [Complex.mul_im]
      norm_num
      exact (diagonalFixedPoint m).im_pos⟩ : ℍ) =
      ModularGroup.S • diagonalFixedPoint m := by
  rw [UpperHalfPlane.modular_S_smul]
  apply UpperHalfPlane.ext
  simp only [diagonalFixedPoint, UpperHalfPlane.coe_mk]
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
  unfold levelJ jN
  rw [diagonalFixedPoint_scale_eq]
  exact j_invariant ModularGroup.S (diagonalFixedPoint m)

private theorem modularPolynomialDiagonal_map_eval_fixedPoint (m : ℕ+) :
    ((modularPolynomialDiagonal m).map (Int.castRingHom ℂ)).eval
      (j (diagonalFixedPoint m)) = 0 := by
  rw [modularPolynomialDiagonal, ← BivariatePolynomial.diagonal_map,
    BivariatePolynomial.diagonal_eval, modularPolynomial_map_complex]
  have h := modularPolynomialC_eval_levelJ_j m (diagonalFixedPoint m)
  rwa [levelJ_diagonalFixedPoint] at h

/-- Theorem 11.18(iv), degree assertion. -/
theorem theorem_11_18_iv_degree (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    1 < (modularPolynomialDiagonal m).natDegree := by
  let P := modularPolynomialDiagonal m
  change 1 < P.natDegree
  have hlc : P.leadingCoeff = 1 ∨ P.leadingCoeff = -1 :=
    theorem_11_18_iv_leadingCoeff m hm
  have hP : P ≠ 0 := by
    intro hP
    rcases hlc with hlc | hlc <;> simp [hP] at hlc
  have hroot : Polynomial.eval₂ (Int.castRingHom ℂ)
      (j (diagonalFixedPoint m)) P = 0 := by
    simpa only [Polynomial.eval₂_eq_eval_map] using
      modularPolynomialDiagonal_map_eval_fixedPoint m
  have hpos : 0 < P.natDegree :=
    Polynomial.natDegree_pos_of_eval₂_root hP (Int.castRingHom ℂ) hroot
      fun x h ↦ by
        change (x : ℂ) = 0 at h
        exact Int.cast_eq_zero.mp h
  have hm_ne_one : (m : ℕ) ≠ 1 := by
    intro hm1
    apply hm
    refine ⟨1, ?_⟩
    simp [hm1]
  have hmgt : 1 < (m : ℕ) := by
    have := PNat.pos m
    lia
  have hsymm := theorem_11_18_iii m hmgt
  have hswap := BivariatePolynomial.coeff_coeff_swap (modularPolynomial m) 0 1
  rw [hsymm] at hswap
  have hcoeff := diagonal_coeff_one (modularPolynomial m)
  rw [hswap] at hcoeff
  have hne : P.natDegree ≠ 1 := by
    intro hd
    have hleading : P.coeff 1 = P.leadingCoeff := by
      simpa only [hd] using P.coeff_natDegree
    change P.coeff 1 = _ at hcoeff
    rw [hleading] at hcoeff
    rcases hlc with hlc | hlc <;> lia
  lia

/-- Cox equation (11.22), the explicit level-three modular polynomial. -/
theorem modularPolynomial_three :
    modularPolynomial (3 : ℕ+) = modularPolynomialThreeExplicit := by
  apply modularPolynomial_three_of_complex_swap
  have h := congrArg (BivariatePolynomial.map (Int.castRingHom ℂ))
    (theorem_11_18_iii (3 : ℕ+) (by norm_num))
  rw [BivariatePolynomial.map_swap, modularPolynomial_map_complex] at h
  exact h

end Cox
