/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.Algebra.Polynomial.Lifts
import XYin.PhD.Cox.CoxMatrices.Basic
import XYin.PhD.ModularFunctions.FieldAction

/-!
# Analytic support for Cox modular polynomials

This file provides the holomorphy and cusp-meromorphy lemmas shared by the construction,
interpolation, and integral-descent arguments for Cox's modular polynomial.

The coefficients of a product `∏ (X - C rᵢ)` lie in every subring containing the roots `rᵢ`
(`Polynomial.coeff_prod_X_sub_C_mem`). Applied to the subring `holomorphicFunctions` and to the
subring `cuspMeromorphicSubring h` of functions with a meromorphic width-`h` cusp expansion,
this gives holomorphy and cusp meromorphy of the coefficients of the Cox products
(`coxNodal_coeff_mdifferentiable`, `coxNodal_coeff_cuspMeromorphicAt`).
-/

open Complex Function MatrixGroups ModularForm UpperHalfPlane
open scoped Manifold Polynomial.Bivariate

noncomputable section

namespace Polynomial

variable {R ι : Type*}

/-- The coefficients of a finite product of polynomials lie in a subsemiring containing the
coefficients of the factors. -/
theorem coeff_finset_prod_mem [CommSemiring R] (S : Subsemiring R) {s : Finset ι}
    {P : ι → R[X]} (hP : ∀ i ∈ s, ∀ n, (P i).coeff n ∈ S) (n : ℕ) :
    (∏ i ∈ s, P i).coeff n ∈ S := by
  have h : ∏ i ∈ s, P i ∈ lifts S.subtype :=
    Subsemiring.prod_mem _ fun i hi ↦
      (lifts_iff_coeff_lifts _).2 fun k ↦ by simpa using hP i hi k
  simpa using (lifts_iff_coeff_lifts _).1 h n

/-- The coefficients of `X - C a` lie in every subring containing `a`. -/
theorem coeff_X_sub_C_mem [Ring R] (S : Subring R) {a : R} (ha : a ∈ S) (n : ℕ) :
    (X - C a).coeff n ∈ S := by
  rcases n with _ | _ | n <;> simp [coeff_X, coeff_C, S.neg_mem ha, S.one_mem, S.zero_mem]

/-- The coefficients of `∏ (X - C rᵢ)` lie in every subring containing the roots `rᵢ`. -/
theorem coeff_prod_X_sub_C_mem [CommRing R] (S : Subring R) {s : Finset ι} {r : ι → R}
    (hr : ∀ i ∈ s, r i ∈ S) (n : ℕ) : (∏ i ∈ s, (X - C (r i))).coeff n ∈ S :=
  coeff_finset_prod_mem S.toSubsemiring (fun i hi ↦ coeff_X_sub_C_mem S (hr i hi)) n

end Polynomial

namespace Cox

/-- The subring of functions on the upper half-plane whose width-`h` cusp function is
meromorphic at `0`. -/
def cuspMeromorphicSubring (h : ℝ) : Subring (ℍ → ℂ) where
  carrier := {f | MeromorphicAt (cuspFunction h f) 0}
  mul_mem' := meromorphicAt_cuspFunction_mul
  one_mem' := meromorphicAt_cuspFunction_const h 1
  add_mem' := meromorphicAt_cuspFunction_add
  zero_mem' := meromorphicAt_cuspFunction_const h 0
  neg_mem' := meromorphicAt_cuspFunction_neg

@[simp]
theorem mem_cuspMeromorphicSubring {h : ℝ} {f : ℍ → ℂ} :
    f ∈ cuspMeromorphicSubring h ↔ MeromorphicAt (cuspFunction h f) 0 :=
  Iff.rfl

/-- A holomorphic function on `ℍ` is meromorphic at every point of the upper half-plane. -/
theorem meromorphicAt_comp_ofComplex_of_mdifferentiable {f : ℍ → ℂ} (hf : MDiff f) {z : ℂ}
    (hz : 0 < z.im) : MeromorphicAt (f ∘ UpperHalfPlane.ofComplex) z :=
  ((UpperHalfPlane.mdifferentiable_iff.1 hf).analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz)).meromorphicAt

/-- A right-coset translate of raw cusp data has a meromorphic width-`m` cusp expansion. -/
theorem rightCosetTranslate_cuspMeromorphicAt (m : ℕ+) {f : ℍ → ℂ} (hf : CuspData m f)
    (c : Gamma0RightCosets m) :
    MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (rightCosetTranslate m hf c)) 0 :=
  Quotient.inductionOn c hf.meromorphicAt_cuspFunction

/-- A right-coset root has a meromorphic width-`m` cusp expansion. -/
theorem rightCosetEval_cuspMeromorphicAt (m : ℕ+) (c : Gamma0RightCosets m) :
    MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (rightCosetEval m c)) 0 :=
  rightCosetTranslate_cuspMeromorphicAt m (levelJ_cuspData m) c

/-- The conjugate attached to the identity coset is the level transform `j(mτ)`. -/
theorem rightCosetEval_baseRightCoset (m : ℕ+) : rightCosetEval m (baseRightCoset m) = levelJ m :=
  funext fun τ ↦ congrArg (levelJ m) (one_smul _ τ)

/-- A right-coset root is holomorphic on the upper half-plane. -/
theorem rightCosetEval_mdifferentiable (m : ℕ+) (c : Gamma0RightCosets m) :
    MDiff (rightCosetEval m c) :=
  Quotient.inductionOn c fun γ ↦ (levelJ_mdifferentiable m).comp (sl2_mdifferentiable γ)

/-- A Cox root has a meromorphic width-`m` cusp expansion. -/
theorem coxRoot_cuspMeromorphicAt (m : ℕ+) (σ : CoxMatrix m) :
    MeromorphicAt
      (cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ))) 0 := by
  rw [← funext (rightCosetEval_equiv m σ)]
  exact rightCosetEval_cuspMeromorphicAt m (coxMatrixEquivRightCosets m σ)

/-- A Cox root is holomorphic on the upper half-plane. -/
theorem coxRoot_mdifferentiable (m : ℕ+) (σ : CoxMatrix m) :
    MDiff (fun τ : ℍ ↦ j (σ.act τ)) := by
  rw [← funext (rightCosetEval_equiv m σ)]
  exact rightCosetEval_mdifferentiable m (coxMatrixEquivRightCosets m σ)

/-- The coefficients of a product of Cox linear factors have meromorphic width-`m` cusp
expansions. -/
theorem coxNodal_coeff_cuspMeromorphicAt (m : ℕ+) (s : Finset (CoxMatrix m)) (n : ℕ) :
    MeromorphicAt (cuspFunction ((m : ℕ) : ℝ)
      ((∏ σ ∈ s, (Polynomial.X - Polynomial.C (fun τ : ℍ ↦ j (σ.act τ)))).coeff n)) 0 :=
  Polynomial.coeff_prod_X_sub_C_mem (cuspMeromorphicSubring _)
    (fun σ _ ↦ coxRoot_cuspMeromorphicAt m σ) n

/-- The coefficients of a product of Cox linear factors are holomorphic. -/
theorem coxNodal_coeff_mdifferentiable (m : ℕ+) (s : Finset (CoxMatrix m)) (n : ℕ) :
    MDiff ((∏ σ ∈ s, (Polynomial.X - Polynomial.C (fun τ : ℍ ↦ j (σ.act τ))) :
      Polynomial (ℍ → ℂ)).coeff n) :=
  Polynomial.coeff_prod_X_sub_C_mem holomorphicFunctions
    (fun σ _ ↦ coxRoot_mdifferentiable m σ) n

end Cox
