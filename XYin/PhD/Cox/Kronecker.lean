/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

import XYin.PhD.Cox.DiagonalLaurent

/-!
# Kronecker's congruence for the modular polynomial

This file develops the cyclotomic descent and Laurent-series infrastructure used in the proof
of Cox Theorem 11.18(v), Kronecker's congruence `Φ_p(X, Y) ≡ (X ^ p - Y) (X - Y ^ p) mod p` in
Cox's notation; in the letters of `(ZMod p)[X][Y]` (see `Cox.modularPolynomialC`) the right-hand
side is `(Y ^ p - C X) * (Y - C X ^ p)`. At a prime level, the Cox representatives consist of the
`p` matrices `(1,i;0,p)` and `(p,0;0,1)`. The final Frobenius factorization is proved in
`KroneckerFrobenius.lean`.

The final descent from a specialized identity uses the lowest Laurent coefficient of `P(j)`;
this is Cox Exercise 11.15, formalized in `LaurentPolynomialEvaluation.lean`.
-/

open scoped Polynomial.Bivariate

noncomputable section

namespace Cox

open UpperHalfPlane

/-- The prime-level representative `(1,i;0,p)`. -/
def primeLowerCoxMatrix (p : ℕ+) (i : Fin (p : ℕ)) : CoxMatrix p where
  a := 1
  b := i
  d := p
  a_pos := Nat.zero_lt_one
  determinant := Nat.one_mul p
  b_lt := i.isLt
  primitive := by simp

private def primeFinToCoxMatrix (p : ℕ+) : Fin ((p : ℕ) + 1) → CoxMatrix p :=
  Fin.lastCases (sigmaZero p) (primeLowerCoxMatrix p)

@[simp]
private theorem primeFinToCoxMatrix_castSucc (p : ℕ+) (i : Fin (p : ℕ)) :
    primeFinToCoxMatrix p i.castSucc = primeLowerCoxMatrix p i := by
  simp [primeFinToCoxMatrix]

@[simp]
private theorem primeFinToCoxMatrix_last (p : ℕ+) :
    primeFinToCoxMatrix p (Fin.last (p : ℕ)) = sigmaZero p := by
  simp [primeFinToCoxMatrix]

private theorem primeFinToCoxMatrix_surjective
    (p : ℕ+) [hp : Fact (Nat.Prime (p : ℕ))] :
    Function.Surjective (primeFinToCoxMatrix p) := by
  intro σ
  rcases hp.out.eq_one_or_self_of_dvd σ.a σ.a_dvd with ha | ha
  · have hd : σ.d = (p : ℕ) := by simpa [ha] using σ.determinant
    refine ⟨Fin.castSucc ⟨σ.b, hd ▸ σ.b_lt⟩, ?_⟩
    rw [primeFinToCoxMatrix_castSucc]
    exact CoxMatrix.ext ha.symm rfl hd.symm
  · have hd : σ.d = 1 := by
      have hdet := σ.determinant
      rw [ha] at hdet
      nlinarith [PNat.pos p]
    refine ⟨Fin.last (p : ℕ), ?_⟩
    rw [primeFinToCoxMatrix_last]
    exact CoxMatrix.ext ha.symm (by simp only [sigmaZero]; have := σ.b_lt; lia) hd.symm

private theorem primeFinToCoxMatrix_injective
    (p : ℕ+) [hp : Fact (Nat.Prime (p : ℕ))] :
    Function.Injective (primeFinToCoxMatrix p) := by
  intro i j h
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · apply Fin.ext
      have hb := congrArg CoxMatrix.b h
      simpa [primeLowerCoxMatrix] using hb
    · exfalso
      have ha := congrArg CoxMatrix.a h
      have ha' : 1 = (p : ℕ) := by
        simpa only [primeFinToCoxMatrix_castSucc, primeFinToCoxMatrix_last,
          primeLowerCoxMatrix, sigmaZero] using ha
      exact hp.out.ne_one ha'.symm
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · exfalso
      have ha := congrArg CoxMatrix.a h
      have ha' : (p : ℕ) = 1 := by
        simpa only [primeFinToCoxMatrix_castSucc, primeFinToCoxMatrix_last,
          primeLowerCoxMatrix, sigmaZero] using ha
      exact hp.out.ne_one ha'
    · rfl

private noncomputable def primeFinEquivCoxMatrix
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    Fin ((p : ℕ) + 1) ≃ CoxMatrix p :=
  Equiv.ofBijective (primeFinToCoxMatrix p) <|
    ⟨primeFinToCoxMatrix_injective p, primeFinToCoxMatrix_surjective p⟩

@[simp]
private theorem primeFinEquivCoxMatrix_apply_of_lt
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (i : Fin ((p : ℕ) + 1)) (hi : (i : ℕ) < (p : ℕ)) :
    primeFinEquivCoxMatrix p i = primeLowerCoxMatrix p ⟨i, hi⟩ := by
  let j : Fin (p : ℕ) := ⟨i, hi⟩
  have hij : i = j.castSucc := Fin.ext rfl
  change primeFinToCoxMatrix p i = primeLowerCoxMatrix p j
  rw [hij, primeFinToCoxMatrix_castSucc]

@[simp]
private theorem primeFinEquivCoxMatrix_apply_last
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    primeFinEquivCoxMatrix p (Fin.last (p : ℕ)) = sigmaZero p :=
  primeFinToCoxMatrix_last p

/-- For a prime `p`, Cox's representatives are the `p` matrices `(1,i;0,p)` together with
`(p,0;0,1)`. -/
noncomputable def primeCoxMatrixEquiv
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    CoxMatrix p ≃ Fin ((p : ℕ) + 1) :=
  (primeFinEquivCoxMatrix p).symm

@[simp]
theorem primeCoxMatrixEquiv_symm_apply_of_lt
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (i : Fin ((p : ℕ) + 1)) (hi : (i : ℕ) < (p : ℕ)) :
    (primeCoxMatrixEquiv p).symm i = primeLowerCoxMatrix p ⟨i, hi⟩ :=
  primeFinEquivCoxMatrix_apply_of_lt p i hi

@[simp]
theorem primeCoxMatrixEquiv_symm_apply_last
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    (primeCoxMatrixEquiv p).symm (Fin.last (p : ℕ)) = sigmaZero p :=
  primeFinEquivCoxMatrix_apply_last p

/-- The Frobenius identity for the width-`m` Laurent series of `j` modulo a prime `p`: raising
it to the power `pⁿ` multiplies the width by `pⁿ`. -/
theorem jLaurentSeriesWidth_pow_prime_pow (p : ℕ+) [Fact (p : ℕ).Prime] (m : ℕ+) (n : ℕ) :
    jLaurentSeriesWidth (ZMod p) m ^ (p : ℕ) ^ n =
      jLaurentSeriesWidth (ZMod p) (m * p ^ n) := by
  rw [jLaurentSeriesWidth_eq_single_mul_expand, jLaurentSeriesWidth_eq_single_mul_expand, mul_pow,
    HahnSeries.single_pow, one_pow, ← PowerSeries.coe_pow, PowerSeries.pow_prime_pow_eq_expand,
    ← PowerSeries.expand_mul]
  congr 3
  · rw [nsmul_eq_mul]
    push_cast
    ring
  · simp only [PNat.mul_coe, PNat.pow_coe, mul_comm]

/-- The case `n = 1` of `jLaurentSeriesWidth_pow_prime_pow`. -/
theorem jLaurentSeriesWidth_pow_prime (p : ℕ+) [Fact (p : ℕ).Prime] (m : ℕ+) :
    jLaurentSeriesWidth (ZMod p) m ^ (p : ℕ) = jLaurentSeriesWidth (ZMod p) (m * p) := by
  simpa using jLaurentSeriesWidth_pow_prime_pow p m 1

/-- Substitute the width-`p` Laurent series of `j` for the parameter, i.e. for the inner
variable `C X`. -/
noncomputable def specializeJMod (p : ℕ+) :
    (ZMod (p : ℕ))[X][Y] →+* Polynomial (LaurentSeries (ZMod (p : ℕ))) :=
  bivariateSpecializeLaurent (jLaurentSeriesWidth (ZMod p) p)

/-- `specializeJMod` sends the outer (root) variable `Y` to the variable of the target. -/
@[simp]
theorem specializeJMod_Y (p : ℕ+) :
    specializeJMod p (Y : (ZMod (p : ℕ))[X][Y]) = Polynomial.X := by
  simp [specializeJMod, bivariateSpecializeLaurent]

/-- `specializeJMod` sends the inner variable `C X` to the width-`p` `j`-series. -/
@[simp]
theorem specializeJMod_C_X (p : ℕ+) :
    specializeJMod p (Polynomial.C Polynomial.X : (ZMod (p : ℕ))[X][Y]) =
      Polynomial.C (jLaurentSeriesWidth (ZMod p) p) := by
  simp [specializeJMod, bivariateSpecializeLaurent]

/-- Substitute the integral width-`m` expansion of `j` for the parameter, i.e. for the inner
variable `C X`. -/
def specializeJIntegral (m : ℕ+) : ℤ[X][Y] →+* Polynomial (LaurentSeries ℤ) :=
  bivariateSpecializeLaurent (jLaurentSeriesWidth ℤ m)

/-- Reduction modulo `p` commutes with integral specialization at the width-`p` `j`-series. -/
theorem specializeJIntegral_map_zmod (p : ℕ+) (F : ℤ[X][Y]) :
    (specializeJIntegral p F).map
        (HahnSeries.mapRingHom (Int.castRingHom (ZMod (p : ℕ)))) =
      specializeJMod p (F.map (Polynomial.mapRingHom (Int.castRingHom (ZMod (p : ℕ))))) :=
  bivariateSpecializeLaurent_map_apply _ _ _ (jLaurentSeriesWidth_map _ p) F

/-- Mapping the integral specialization to `ℂ` gives specialization at the analytic
width-`m` Laurent expansion of `j`. -/
theorem specializeJIntegral_map_complex (m : ℕ+) (F : ℤ[X][Y]) :
    (specializeJIntegral m F).map
        (HahnSeries.mapRingHom (Int.castRingHom ℂ)) =
      Polynomial.map
        (Polynomial.eval₂RingHom (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
          (laurentqExpansion ((m : ℕ) : ℝ) j))
        (F.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) :=
  bivariateSpecializeLaurent_map_apply _ _ _ (jLaurentSeriesWidth_map_complex m) F

/-- The integral specialization of the modular polynomial becomes its formal Cox product
after extending coefficients to `ℂ`. -/
theorem specializeJIntegral_modularPolynomial_map_complex (m : ℕ+) :
    (specializeJIntegral m (modularPolynomial m)).map
        (HahnSeries.mapRingHom (Int.castRingHom ℂ)) =
      formalCoxPolynomial m (zeta m) := by
  rw [specializeJIntegral_map_complex, modularPolynomial_map_complex,
    ← formalCoxPolynomial_eq_modularPolynomialC_map_j]

/-- Exercise 11.15, the coefficientwise Hasse q-expansion principle modulo `p`. -/
theorem specializeJMod_injective
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    Function.Injective (specializeJMod p) :=
  Polynomial.map_injective _ <| polynomial_eval₂_laurentSeries_injective
    (jLaurentSeriesWidth (ZMod p) p) p p.pos (jLaurentSeriesWidth_order _ p)
      (jLaurentSeriesWidth_leadingCoeff _ p)

/-- An integral polynomial lift of a power of the `p`-th-root phase. -/
def phasePolynomial (p : ℕ+) (e : ℤ) : Polynomial ℤ :=
  Polynomial.X ^ Int.toNat (e % (p : ℤ))

private theorem phasePolynomial_eval_zeta (p : ℕ+) (e : ℤ) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (zeta p) (phasePolynomial p e) =
      zeta p ^ e := by
  rw [phasePolynomial, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    ← zpow_natCast, Int.toNat_of_nonneg]
  · let u : ℂˣ := Units.mk0 (zeta p) (zeta_ne_zero p)
    have hu : u ^ (p : ℕ) = 1 := by
      apply Units.ext
      simpa [u] using (zeta_isPrimitiveRoot p).pow_eq_one
    have hemod := zpow_eq_zpow_emod' (x := u) e hu
    have hval := congrArg (fun v : ℂˣ ↦ (v : ℂ)) hemod
    simpa only [Units.val_zpow_eq_zpow_val] using hval.symm
  · exact Int.emod_nonneg e (by exact_mod_cast PNat.ne_zero p)

/-- The integral cyclotomic lift of a transformed `j`-series. -/
noncomputable def cyclotomicTransformedJSeries
    (p : ℕ+) (σ : CoxMatrix p) : LaurentSeries (Polynomial ℤ) :=
  HahnSeries.ofSuppBddBelow
    (fun k ↦ if (σ.a : ℤ) ^ 2 ∣ k ∧ -((σ.a : ℤ) ^ 2) ≤ k
      then Polynomial.C (jIntCoeff (k / (σ.a : ℤ) ^ 2)) *
        phasePolynomial p (((σ.a : ℤ) * (σ.b : ℤ)) * (k / (σ.a : ℤ) ^ 2))
      else 0)
    ⟨-((σ.a : ℤ) ^ 2), fun _ hk ↦ by_contra fun h ↦ hk (if_neg fun h' ↦ h h'.2)⟩

theorem cyclotomicTransformedJSeries_coeff
    (p : ℕ+) (σ : CoxMatrix p) (k : ℤ) :
    (cyclotomicTransformedJSeries p σ).coeff k =
      if (σ.a : ℤ) ^ 2 ∣ k ∧ -((σ.a : ℤ) ^ 2) ≤ k
      then Polynomial.C (jIntCoeff (k / (σ.a : ℤ) ^ 2)) *
        phasePolynomial p (((σ.a : ℤ) * (σ.b : ℤ)) *
          (k / (σ.a : ℤ) ^ 2))
      else 0 :=
  rfl

/-- Evaluate the integral phase variable at the analytic primitive root. -/
def phaseEvalComplex (p : ℕ+) : Polynomial ℤ →+* ℂ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℂ) (zeta p)

/-- Reduce the integral phase coefficients modulo `p` and set the phase variable to one. -/
def phaseEvalMod (p : ℕ+) : Polynomial ℤ →+* ZMod (p : ℕ) :=
  Polynomial.eval₂RingHom (Int.castRingHom (ZMod (p : ℕ))) 1

/-- Specializing the phase variable to a value `ζ` whose powers the phase polynomials
represent turns the cyclotomic lift into the transformed series at `ζ`. -/
theorem cyclotomicTransformedJSeries_map {K : Type*} [Field K] (p : ℕ+) (σ : CoxMatrix p)
    (φ : Polynomial ℤ →+* K) (ζ : K) (hφ : ∀ e : ℤ, φ (phasePolynomial p e) = ζ ^ e) :
    (cyclotomicTransformedJSeries p σ).map φ = transformedJSeries ζ σ := by
  ext k
  rw [HahnSeries.map_coeff, cyclotomicTransformedJSeries_coeff, transformedJSeries_coeff]
  split_ifs
  · rw [map_mul, hφ, eq_intCast Polynomial.C, map_intCast]
  · exact map_zero φ

/-- The finite Cox product over the integral cyclotomic lift. -/
noncomputable def cyclotomicCoxPolynomial
    (p : ℕ+) : Polynomial (LaurentSeries (Polynomial ℤ)) :=
  ∏ σ : CoxMatrix p,
    (Polynomial.X - Polynomial.C (cyclotomicTransformedJSeries p σ))

/-- Specializing the phase variable turns the cyclotomic Cox product into the formal Cox
product. -/
theorem cyclotomicCoxPolynomial_map {K : Type*} [Field K] (p : ℕ+) (φ : Polynomial ℤ →+* K)
    (ζ : K) (hφ : ∀ e : ℤ, φ (phasePolynomial p e) = ζ ^ e) :
    (cyclotomicCoxPolynomial p).map (HahnSeries.mapRingHom φ) = formalCoxPolynomial p ζ := by
  classical
  simp [cyclotomicCoxPolynomial, formalCoxPolynomial, Polynomial.map_prod,
    cyclotomicTransformedJSeries_map p _ φ ζ hφ]

/-- At `ζ = ζ_p`, the cyclotomic Cox product specializes to the complex formal Cox product. -/
theorem cyclotomicCoxPolynomial_map_complex (p : ℕ+) :
    (cyclotomicCoxPolynomial p).map
        (HahnSeries.mapRingHom (phaseEvalComplex p)) =
      formalCoxPolynomial p (zeta p) :=
  cyclotomicCoxPolynomial_map p _ _ (phasePolynomial_eval_zeta p)

/-- Modulo `p` and at phase one, the cyclotomic Cox product specializes to the formal Cox
product over `ZMod p`. -/
theorem cyclotomicCoxPolynomial_map_mod (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    (cyclotomicCoxPolynomial p).map
        (HahnSeries.mapRingHom (phaseEvalMod p)) =
      formalCoxPolynomial p (1 : ZMod (p : ℕ)) :=
  cyclotomicCoxPolynomial_map p _ _ fun e ↦ by simp [phaseEvalMod, phasePolynomial]

/-- Exercise 11.13: an integral value at `ζ_p` is congruent modulo `p` to the value at one. -/
theorem cyclotomicDescent_dvd
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (F : Polynomial ℤ) (z : ℤ)
    (hF : Polynomial.eval₂ (Int.castRingHom ℂ) (zeta p) F = (z : ℂ)) :
    (p : ℤ) ∣ F.eval 1 - z := by
  have hroot : Polynomial.aeval (zeta p) (F - Polynomial.C z) = 0 := by
    rw [map_sub, Polynomial.aeval_C, Polynomial.aeval_def, algebraMap_int_eq, hF, eq_intCast,
      sub_self]
  have hdiv : Polynomial.cyclotomic (p : ℕ) ℤ ∣ F - Polynomial.C z := by
    rw [Polynomial.cyclotomic_eq_minpoly (zeta_isPrimitiveRoot p) p.pos]
    exact minpoly.isIntegrallyClosed_dvd ((zeta_isPrimitiveRoot p).isIntegral p.pos) hroot
  simpa only [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_sub,
    Polynomial.eval_C] using Polynomial.eval_dvd (x := (1 : ℤ)) hdiv

/-- Exercise 11.13 in its coefficientwise reduction-modulo-`p` form. -/
theorem cyclotomicDescent_zmod
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (F : Polynomial ℤ) (z : ℤ)
    (hF : Polynomial.eval₂ (Int.castRingHom ℂ) (zeta p) F = (z : ℂ)) :
    ((F.eval 1 : ℤ) : ZMod (p : ℕ)) = (z : ZMod (p : ℕ)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  simpa only [neg_sub] using dvd_neg.mpr (cyclotomicDescent_dvd p F z hF)

/-- Coefficientwise Exercise 11.13 for polynomials whose coefficients are Laurent series. -/
theorem cyclotomicDescent_polynomialLaurentSeries
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (A : Polynomial (LaurentSeries (Polynomial ℤ)))
    (B : Polynomial (LaurentSeries ℤ))
    (h : A.map (HahnSeries.mapRingHom (phaseEvalComplex p)) =
      B.map (HahnSeries.mapRingHom (Int.castRingHom ℂ))) :
    A.map (HahnSeries.mapRingHom (phaseEvalMod p)) =
      B.map (HahnSeries.mapRingHom (Int.castRingHom (ZMod (p : ℕ)))) := by
  ext n k
  have hcoeff := congrArg
    (fun P : Polynomial (LaurentSeries ℂ) ↦ (P.coeff n).coeff k) h
  simp only [Polynomial.coeff_map, HahnSeries.mapRingHom_coeff] at hcoeff ⊢
  rw [phaseEvalMod, Polynomial.coe_eval₂RingHom,
    show (1 : ZMod (p : ℕ)) = (Int.castRingHom (ZMod (p : ℕ))) (1 : ℤ) by simp,
    Polynomial.eval₂_at_apply]
  exact cyclotomicDescent_zmod p ((A.coeff n).coeff k) ((B.coeff n).coeff k) hcoeff

/-- After reduction modulo `p`, the integral modular polynomial specializes to the phase-one
formal Cox product. -/
theorem specializeJMod_modularPolynomial_eq_formal
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    specializeJMod p
        ((modularPolynomial p).map (Polynomial.mapRingHom (Int.castRingHom (ZMod (p : ℕ))))) =
      formalCoxPolynomial p (1 : ZMod (p : ℕ)) := by
  rw [← specializeJIntegral_map_zmod, ← cyclotomicDescent_polynomialLaurentSeries p _ _
      ((cyclotomicCoxPolynomial_map_complex p).trans
        (specializeJIntegral_modularPolynomial_map_complex p).symm),
    cyclotomicCoxPolynomial_map_mod]

end Cox
