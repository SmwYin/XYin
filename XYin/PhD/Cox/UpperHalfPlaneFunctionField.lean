/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.FieldTheory.RatFunc.Basic

import XYin.PhD.Cox.CoxMatrices

/-!
# The function field of the upper half-plane

This file realizes `ℂ(Y)` inside the fraction field of holomorphic functions on the upper
half-plane by sending `Y` to the modular function `j`. Precomposition by `SL₂(ℤ)` then gives
`ℂ(Y)`-automorphisms which act transitively on the right-coset conjugates `j(mγτ)`.

The distinctness proof is carried out for functions, rather than at a fixed point of the upper
half-plane: specialized roots can collide at CM points.
-/

open Complex Function MatrixGroups ModularForm UpperHalfPlane
open scoped Manifold

noncomputable section

namespace Cox
namespace UpperHalfPlaneFunctionField

/-- The subring of holomorphic functions on the upper half-plane. -/
def holomorphicFunctions : Subring (ℍ → ℂ) where
  carrier := {f | MDiff f}
  zero_mem' := mdifferentiable_const
  one_mem' := mdifferentiable_const
  add_mem' := fun hf hg ↦ hf.add hg
  neg_mem' := fun hf ↦ hf.neg
  mul_mem' := fun hf hg ↦ hf.mul hg

/-- A holomorphic function on the upper half-plane. -/
abbrev HolomorphicFunction := holomorphicFunctions

instance : NoZeroDivisors HolomorphicFunction where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} hfg := by
    have hfun := congrArg (fun h : HolomorphicFunction ↦ (h : ℍ → ℂ)) hfg
    change (f.1 * g.1 : ℍ → ℂ) = 0 at hfun
    rcases (UpperHalfPlane.mul_eq_zero_iff f.property g.property).mp hfun with hf | hg
    · left
      exact Subtype.ext hf
    · right
      exact Subtype.ext hg

/-- The fraction field of holomorphic functions on the upper half-plane. -/
abbrev FunctionField := FractionRing HolomorphicFunction

private def constant : ℂ →+* HolomorphicFunction where
  toFun z := ⟨fun _ ↦ z, mdifferentiable_const⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The modular function `j`, bundled as a holomorphic function. -/
def jElement : HolomorphicFunction := ⟨j, j_mdifferentiable⟩

/-- Evaluation of a complex polynomial at the holomorphic function `j`. -/
def evalJ : Polynomial ℂ →+* HolomorphicFunction :=
  Polynomial.eval₂RingHom constant jElement

/-- Evaluation of a holomorphic function at a point of the upper half-plane. -/
def evaluation (tau : ℍ) : HolomorphicFunction →+* ℂ :=
  (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) tau).comp holomorphicFunctions.subtype

@[simp]
theorem evalJ_apply (P : Polynomial ℂ) (tau : ℍ) :
    (evalJ P).1 tau = P.eval (j tau) := by
  change (Polynomial.eval₂ constant jElement P : HolomorphicFunction).1 tau = _
  change evaluation tau (Polynomial.eval₂ constant jElement P) = _
  rw [Polynomial.hom_eval₂]
  have hconstant : (evaluation tau).comp constant = RingHom.id ℂ := by
    ext z
    rfl
  rw [hconstant]
  change Polynomial.eval₂ (RingHom.id ℂ) (j tau) P = _
  exact Polynomial.eval₂_at_apply (RingHom.id ℂ) (j tau)

/-- Polynomial evaluation at `j` is injective because the analytic `j`-function is surjective. -/
theorem evalJ_injective : Function.Injective evalJ := by
  intro P Q hPQ
  apply Polynomial.funext
  intro z
  obtain ⟨tau, htau⟩ := j_surjective z
  have h := congrArg (fun f : HolomorphicFunction ↦ f.1 tau) hPQ
  change (evalJ P).1 tau = (evalJ Q).1 tau at h
  rw [evalJ_apply, evalJ_apply, htau] at h
  exact h

/-- Evaluation at `j`, followed by inclusion into the function field. -/
def evalJFracPoly : Polynomial ℂ →+* FunctionField :=
  (algebraMap HolomorphicFunction FunctionField).comp evalJ

/-- Evaluation at `j` remains injective after passing to the function field. -/
theorem evalJFracPoly_injective : Function.Injective evalJFracPoly :=
  (IsFractionRing.injective HolomorphicFunction FunctionField).comp evalJ_injective

/-- The embedding `ℂ(Y) → FunctionField` obtained by sending `Y` to `j`. -/
def ratFuncEvalJ : RatFunc ℂ →+* FunctionField :=
  RatFunc.liftRingHom evalJFracPoly
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ evalJFracPoly_injective)

/-- The resulting homomorphism from `ℂ(Y)` is an embedding. -/
theorem ratFuncEvalJ_injective : Function.Injective ratFuncEvalJ := by
  exact RatFunc.liftRingHom_injective evalJFracPoly evalJFracPoly_injective
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ evalJFracPoly_injective)

noncomputable instance : Algebra (RatFunc ℂ) FunctionField := ratFuncEvalJ.toAlgebra

/-- The chosen algebra structure is induced by `ratFuncEvalJ`. -/
@[simp]
theorem algebraMap_ratFunc (r : RatFunc ℂ) :
    algebraMap (RatFunc ℂ) FunctionField r = ratFuncEvalJ r := rfl

/-- On polynomials, the rational-function embedding agrees with evaluation at `j`. -/
@[simp]
theorem ratFuncEvalJ_algebraMap (P : Polynomial ℂ) :
    ratFuncEvalJ (algebraMap (Polynomial ℂ) (RatFunc ℂ) P) =
      evalJFracPoly P := by
  simp [ratFuncEvalJ]

private lemma sl2_mdifferentiable (delta : SL(2, ℤ)) :
    MDiff (fun tau : ℍ ↦ delta • tau) := by
  simpa only using
    UpperHalfPlane.mdifferentiable_smul (g := (delta : GL (Fin 2) ℝ)) (by simp)

/-- Precomposition of holomorphic functions by an element of `SL₂(ℤ)`. -/
private def precompHolomorphic (delta : SL(2, ℤ)) :
    HolomorphicFunction ≃+* HolomorphicFunction where
  toFun f := ⟨fun tau ↦ f.1 (delta • tau), f.property.comp <| sl2_mdifferentiable delta⟩
  invFun f := ⟨fun tau ↦ f.1 (delta⁻¹ • tau), f.property.comp <|
    sl2_mdifferentiable delta⁻¹⟩
  left_inv f := by
    apply Subtype.ext
    funext tau
    simp
  right_inv f := by
    apply Subtype.ext
    funext tau
    simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Precomposition extended to the fraction field. -/
private def precomp (delta : SL(2, ℤ)) : FunctionField ≃+* FunctionField :=
  IsFractionRing.ringEquivOfRingEquiv (K := FunctionField) (L := FunctionField)
    (precompHolomorphic delta)

private theorem precomp_evalJPoly (delta : SL(2, ℤ)) (P : Polynomial ℂ) :
    precomp delta (evalJFracPoly P) = evalJFracPoly P := by
  rw [evalJFracPoly, RingHom.comp_apply, precomp,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  apply congrArg (algebraMap HolomorphicFunction FunctionField)
  apply Subtype.ext
  funext tau
  simp only [precompHolomorphic, RingEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [evalJ_apply, evalJ_apply, j_invariant]

/-- Precomposition fixes the embedded copy of `ℂ(Y)`. -/
private theorem precomp_ratFunc (delta : SL(2, ℤ)) (r : RatFunc ℂ) :
    precomp delta (algebraMap (RatFunc ℂ) FunctionField r) =
      algebraMap (RatFunc ℂ) FunctionField r := by
  induction r using RatFunc.induction_on with
  | f p q _ =>
      simp only [map_div₀]
      change precomp delta (ratFuncEvalJ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)) /
          precomp delta (ratFuncEvalJ (algebraMap (Polynomial ℂ) (RatFunc ℂ) q)) =
        ratFuncEvalJ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) /
          ratFuncEvalJ (algebraMap (Polynomial ℂ) (RatFunc ℂ) q)
      simp only [ratFuncEvalJ_algebraMap, precomp_evalJPoly]

/-- Precomposition as a `ℂ(Y)`-algebra automorphism of the function field. -/
def precompAlgEquiv (delta : SL(2, ℤ)) : FunctionField ≃ₐ[RatFunc ℂ] FunctionField where
  __ := precomp delta
  commutes' := precomp_ratFunc delta

private lemma transformed_leading (m : ℕ+) (sigma : CoxMatrix m) :
    (transformedJSeries (zeta m) sigma).coeff (-((sigma.a : ℤ) ^ 2)) =
      zeta m ^ (-((sigma.a : ℤ) * (sigma.b : ℤ))) := by
  rw [transformedJSeries_coeff, if_pos]
  · have ha0 : (sigma.a : ℤ) ^ 2 ≠ 0 := by
      exact_mod_cast (pow_ne_zero 2 sigma.a_pos.ne')
    simp [ha0, jIntCoeff_neg_one]
  · exact ⟨dvd_neg.mpr (dvd_refl _), le_rfl⟩

private lemma transformed_leading_ne (m : ℕ+) (sigma : CoxMatrix m) :
    (transformedJSeries (zeta m) sigma).coeff (-((sigma.a : ℤ) ^ 2)) ≠ 0 := by
  rw [transformed_leading]
  exact zpow_ne_zero _ ((zeta_isPrimitiveRoot m).ne_zero (PNat.ne_zero m))

private lemma cox_a_le {m : ℕ+} {sigma tau : CoxMatrix m}
    (h : transformedJSeries (zeta m) sigma = transformedJSeries (zeta m) tau) :
    sigma.a ≤ tau.a := by
  have hne : (transformedJSeries (zeta m) tau).coeff (-((sigma.a : ℤ) ^ 2)) ≠ 0 := by
    rw [← h]
    exact transformed_leading_ne m sigma
  have hc : (tau.a : ℤ) ^ 2 ∣ -((sigma.a : ℤ) ^ 2) ∧
      -((tau.a : ℤ) ^ 2) ≤ -((sigma.a : ℤ) ^ 2) := by
    by_contra hc
    rw [transformedJSeries_coeff, if_neg hc] at hne
    exact hne rfl
  have hsigma : (0 : ℤ) < sigma.a := by exact_mod_cast sigma.a_pos
  have htau : (0 : ℤ) < tau.a := by exact_mod_cast tau.a_pos
  exact_mod_cast (by nlinarith [hc.2] : (sigma.a : ℤ) ≤ tau.a)

private lemma transformed_phase {m : ℕ+} {sigma tau : CoxMatrix m}
    (h : transformedJSeries (zeta m) sigma = transformedJSeries (zeta m) tau)
    (ha : sigma.a = tau.a) :
    zeta m ^ (-((sigma.a : ℤ) * (sigma.b : ℤ))) =
      zeta m ^ (-((sigma.a : ℤ) * (tau.b : ℤ))) := by
  calc
    zeta m ^ (-((sigma.a : ℤ) * (sigma.b : ℤ))) =
        (transformedJSeries (zeta m) sigma).coeff (-((sigma.a : ℤ) ^ 2)) :=
      (transformed_leading m sigma).symm
    _ = (transformedJSeries (zeta m) tau).coeff (-((sigma.a : ℤ) ^ 2)) := by rw [h]
    _ = (transformedJSeries (zeta m) tau).coeff (-((tau.a : ℤ) ^ 2)) := by rw [ha]
    _ = zeta m ^ (-((tau.a : ℤ) * (tau.b : ℤ))) := transformed_leading m tau
    _ = zeta m ^ (-((sigma.a : ℤ) * (tau.b : ℤ))) := by rw [ha]

private lemma cox_b_eq {m : ℕ+} {sigma tau : CoxMatrix m}
    (hd : sigma.d = tau.d)
    (hphase : zeta m ^ (-((sigma.a : ℤ) * (sigma.b : ℤ))) =
      zeta m ^ (-((sigma.a : ℤ) * (tau.b : ℤ)))) :
    sigma.b = tau.b := by
  let x : ℤ := -((sigma.a : ℤ) * (sigma.b : ℤ))
  let y : ℤ := -((sigma.a : ℤ) * (tau.b : ℤ))
  have hzeta0 : zeta m ≠ 0 := (zeta_isPrimitiveRoot m).ne_zero (PNat.ne_zero m)
  have hpow : zeta m ^ (x - y) = 1 := by
    rw [zpow_sub₀ hzeta0, show zeta m ^ x = zeta m ^ y by simpa [x, y] using hphase]
    exact div_self (zpow_ne_zero _ hzeta0)
  have hmdiv : (m : ℤ) ∣ x - y :=
    ((zeta_isPrimitiveRoot m).zpow_eq_one_iff_dvd (x - y)).mp hpow
  have ham : (m : ℤ) = (sigma.a : ℤ) * (sigma.d : ℤ) := by
    exact_mod_cast sigma.determinant.symm
  have ha0 : (sigma.a : ℤ) ≠ 0 := by exact_mod_cast sigma.a_pos.ne'
  have hdvd : (sigma.d : ℤ) ∣ (tau.b : ℤ) - (sigma.b : ℤ) := by
    rw [ham] at hmdiv
    apply (mul_dvd_mul_iff_left ha0).mp
    convert hmdiv using 1
    all_goals simp only [x, y]
    all_goals ring
  obtain ⟨q, hq⟩ := hdvd
  have hsigma0 : (0 : ℤ) ≤ sigma.b := by exact_mod_cast Nat.zero_le sigma.b
  have htau0 : (0 : ℤ) ≤ tau.b := by exact_mod_cast Nat.zero_le tau.b
  have hsigmaLt : (sigma.b : ℤ) < sigma.d := by exact_mod_cast sigma.b_lt
  have htauLt : (tau.b : ℤ) < tau.d := by exact_mod_cast tau.b_lt
  have hdInt : (sigma.d : ℤ) = tau.d := by exact_mod_cast hd
  have hdpos : (0 : ℤ) < sigma.d := by exact_mod_cast sigma.d_pos
  have hdiff : (tau.b : ℤ) - (sigma.b : ℤ) = (sigma.d : ℤ) * q := by
    simpa [mul_comm] using hq
  have hq0 : q = 0 := by
    by_cases hqneg : q < 0
    · have hmul : (sigma.d : ℤ) * q ≤ -(sigma.d : ℤ) := by
        simpa using mul_le_mul_of_nonneg_left (show q ≤ -1 by omega) hdpos.le
      omega
    · by_cases hqpos : 0 < q
      · have hmul : (sigma.d : ℤ) ≤ (sigma.d : ℤ) * q := by
          simpa using mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ q by omega) hdpos.le
        omega
      · omega
  rw [hq0, mul_zero] at hdiff
  exact_mod_cast (by omega : (sigma.b : ℤ) = tau.b)

private theorem transformed_injective (m : ℕ+) :
    Function.Injective (transformedJSeries (zeta m) : CoxMatrix m → LaurentSeries ℂ) := by
  intro sigma tau h
  have ha : sigma.a = tau.a := le_antisymm (cox_a_le h) (cox_a_le h.symm)
  have hd : sigma.d = tau.d := by
    apply Nat.eq_of_mul_eq_mul_left sigma.a_pos
    rw [sigma.determinant, ha, tau.determinant]
  have hb := cox_b_eq hd (transformed_phase h ha)
  apply CoxMatrix.toFin_injective
  simp [CoxMatrix.toFin, ha, hb, hd]

private theorem conjugate_injective (m : ℕ+) :
    Function.Injective (fun sigma : CoxMatrix m ↦ fun tau : ℍ ↦ j (sigma.act tau)) := by
  intro sigma tau h
  apply transformed_injective m
  rw [← laurentqExpansion_coxAction m sigma, ← laurentqExpansion_coxAction m tau]
  exact congrArg (laurentqExpansion ((m : ℕ) : ℝ)) h

private lemma rightCosetEval_mdifferentiable (m : ℕ+) (c : Gamma0RightCosets m) :
    MDiff (rightCosetEval m c) := by
  letI : NeZero (m : ℕ) := ⟨PNat.ne_zero m⟩
  have hlevel : MDiff (levelJ m) := UpperHalfPlane.mdifferentiable_iff.mpr fun z hz ↦
    (jN_Meromorphic (m : ℕ) (z := ⟨z, hz⟩)).differentiableWithinAt
  refine Quotient.inductionOn c ?_
  intro gamma
  simpa only [rightCosetEval_mk] using hlevel.comp (sl2_mdifferentiable gamma)

/-- The conjugate indexed by a right coset, bundled as a holomorphic function. -/
def rightCosetFunction (m : ℕ+) (c : Gamma0RightCosets m) : HolomorphicFunction :=
  ⟨rightCosetEval m c, rightCosetEval_mdifferentiable m c⟩

/-- Distinct right cosets give distinct holomorphic conjugates. -/
theorem rightCosetFunction_injective (m : ℕ+) : Function.Injective (rightCosetFunction m) := by
  intro c d hcd
  obtain ⟨sigma, rfl⟩ := (coxMatrixEquivRightCosets m).surjective c
  obtain ⟨tau, rfl⟩ := (coxMatrixEquivRightCosets m).surjective d
  have hst : sigma = tau := by
    apply conjugate_injective m
    funext z
    have h := congrArg (fun f : HolomorphicFunction ↦ f.1 z) hcd
    simpa [rightCosetFunction, rightCosetEval_equiv] using h
  exact congrArg (coxMatrixEquivRightCosets m) hst

/-- A right-coset conjugate embedded in the function field. -/
def rightCosetRoot (m : ℕ+) (c : Gamma0RightCosets m) : FunctionField :=
  algebraMap HolomorphicFunction FunctionField (rightCosetFunction m c)

/-- Distinct right cosets remain distinct after embedding into the function field. -/
theorem rightCosetRoot_injective (m : ℕ+) : Function.Injective (rightCosetRoot m) :=
  (IsFractionRing.injective HolomorphicFunction FunctionField).comp
    (rightCosetFunction_injective m)

/-- Precomposition acts on conjugate roots by right multiplication of their cosets. -/
theorem precompAlgEquiv_rightCosetRoot (m : ℕ+) (delta : SL(2, ℤ))
    (c : Gamma0RightCosets m) :
    precompAlgEquiv delta (rightCosetRoot m c) =
      rightCosetRoot m (rightCosetMul m delta c) := by
  change precomp delta (rightCosetRoot m c) = _
  rw [rightCosetRoot, rightCosetRoot, precomp,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  apply congrArg (algebraMap HolomorphicFunction FunctionField)
  apply Subtype.ext
  funext tau
  exact rightCosetEval_smul m delta c tau

end UpperHalfPlaneFunctionField
end Cox
