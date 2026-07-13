/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.CoxMatrices.Basic

/-!
# Analytic support for Cox modular polynomials

This file provides the meromorphic and periodicity lemmas shared by the construction,
interpolation, and integral-descent arguments for Cox's modular polynomial.
-/

open Complex Function MatrixGroups ModularForm UpperHalfPlane
open scoped Manifold Polynomial.Bivariate

noncomputable section

namespace Cox

/-- A right-coset root has a meromorphic width-`m` cusp expansion. -/
theorem rightCosetEval_cuspMeromorphicAt
    (m : ℕ+) (c : Gamma0RightCosets m) :
    MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (rightCosetEval m c)) 0 := by
  refine Quotient.inductionOn c ?_
  intro γ
  change MeromorphicAt
    (cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ levelJ m (γ • τ))) 0
  exact (levelJ_isGamma0ModularFunction m).2.2 γ

/-- A Cox root has a meromorphic width-`m` cusp expansion. -/
theorem coxRoot_cuspMeromorphicAt (m : ℕ+) (σ : CoxMatrix m) :
    MeromorphicAt
      (cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ))) 0 := by
  rw [← funext (rightCosetEval_equiv m σ)]
  exact rightCosetEval_cuspMeromorphicAt m (coxMatrixEquivRightCosets m σ)

/-- Every coefficient of a Cox linear factor has a meromorphic cusp expansion. -/
theorem coxLinearFactor_coeff_cuspMeromorphicAt
    (m : ℕ+) (σ : CoxMatrix m) (n : ℕ) :
    MeromorphicAt
      (cuspFunction ((m : ℕ) : ℝ)
        ((Polynomial.X - Polynomial.C (fun τ : ℍ ↦ j (σ.act τ)) :
          Polynomial (ℍ → ℂ)).coeff n)) 0 := by
  cases n with
  | zero =>
      have hroot := coxRoot_cuspMeromorphicAt m σ
      have hneg := (MeromorphicAt.const (-1 : ℂ) 0).mul hroot
      apply hneg.congr
      filter_upwards [self_mem_nhdsWithin] with q hq
      have hq0 := Set.mem_compl_singleton_iff.mp hq
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero,
        Polynomial.coeff_C_zero, zero_sub, Pi.mul_apply]
      simp only [UpperHalfPlane.cuspFunction]
      rw [Periodic.cuspFunction_eq_of_nonzero _ _ hq0,
        Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
      simp
  | succ n =>
      cases n with
      | zero => simpa using meromorphicAt_cuspFunction_const ((m : ℕ) : ℝ) 1
      | succ n =>
          simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Nat.right_eq_add,
            Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
            Polynomial.coeff_C_succ, sub_zero]
          exact meromorphicAt_cuspFunction_const ((m : ℕ) : ℝ) 0

/-- Coefficients of a finite product inherit meromorphic cusp expansions. -/
theorem polynomial_prod_coeff_cuspMeromorphicAt {ι : Type*}
    (h : ℝ) (P : ι → Polynomial (ℍ → ℂ)) :
    ∀ s : Finset ι,
      (∀ i ∈ s, ∀ n, MeromorphicAt (cuspFunction h ((P i).coeff n)) 0) →
      ∀ n, MeromorphicAt (cuspFunction h ((s.prod P).coeff n)) 0 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ n
      by_cases hn : n = 0
      · subst n
        simpa [Polynomial.coeff_one] using meromorphicAt_cuspFunction_const h 1
      · simpa [Polynomial.coeff_one, hn] using meromorphicAt_cuspFunction_const h 0
  | insert a s ha ih =>
      intro hP n
      rw [Finset.prod_insert ha, Polynomial.coeff_mul]
      apply meromorphicAt_cuspFunction_finset_sum
      intro x hx
      exact meromorphicAt_cuspFunction_mul
        (hP a (Finset.mem_insert_self a s) x.1)
        (ih (fun i hi k ↦ hP i (Finset.mem_insert_of_mem hi) k) x.2)

/-- Weight-zero slash invariance gives period one after extending from the upper half-plane. -/
theorem periodic_comp_of_slashInvariant_one {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) :
    Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
  let F : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 0 :=
    { toFun := f
      slash_action_eq' := fun γ hγ ↦ by
        rw [Subgroup.mem_map] at hγ
        obtain ⟨γ', _, rfl⟩ := hγ
        exact hslash γ' }
  have hper : Periodic (F ∘ UpperHalfPlane.ofComplex) (1 : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex F (by simp)
  simpa [F] using hper

end Cox
