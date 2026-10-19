/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.HermiteNormalForm.RankTwo
import XYin.PhD.Cox.ModularFunction.CuspData
import XYin.PhD.jFunction.jLevelN

/-!
# The level transform of the modular invariant

This file constructs `levelJModularFunction N`, the bundled modular function `τ ↦ j(Nτ)` on
`Γ₀(N)`. Integral triangularization identifies each cusp transform with an affine transform of
`j`, whose q-coordinate expression proves meromorphy at the cusp.
-/

open Complex Filter Function MatrixGroups ModularForm UpperHalfPlane
open scoped Manifold Polynomial.Bivariate

noncomputable section

namespace Cox

/-- The affine transform `τ ↦ (r + gτ) / s` of the upper half-plane. -/
def affineUpperHalfPlane (g s : ℕ) (hg : 0 < g) (hs : 0 < s)
    (r : ℤ) (τ : ℍ) : ℍ :=
  ((r : ℝ) / s) +ᵥ
    ((⟨(g : ℝ) / s, div_pos (Nat.cast_pos.mpr hg) (Nat.cast_pos.mpr hs)⟩ :
      {x : ℝ // 0 < x}) • τ)

@[simp]
lemma coe_affineUpperHalfPlane (g s : ℕ) (hg : 0 < g) (hs : 0 < s)
    (r : ℤ) (τ : ℍ) :
    ((affineUpperHalfPlane g s hg hs r τ : ℍ) : ℂ) =
      ((r : ℝ) / s : ℂ) + ((g : ℝ) / s : ℂ) * (τ : ℂ) := by
  simp [affineUpperHalfPlane]

private lemma qParam_affineUpperHalfPlane (g s : ℕ) (hg : 0 < g) (hs : 0 < s)
    (r : ℤ) (τ : ℍ) :
    Periodic.qParam 1 (affineUpperHalfPlane g s hg hs r τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((r : ℝ) / s)) *
        Periodic.qParam ((g * s : ℕ) : ℝ) τ ^ (g * g) := by
  rw [Periodic.qParam, Periodic.qParam, coe_affineUpperHalfPlane]
  simp only [Complex.ofReal_one, div_one]
  rw [show 2 * (Real.pi : ℂ) * Complex.I *
      (((r : ℝ) / s : ℂ) + ((g : ℝ) / s : ℂ) * (τ : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * ((r : ℝ) / s) +
        2 * (Real.pi : ℂ) * Complex.I * (((g : ℝ) / s : ℂ) * (τ : ℂ)) by ring,
    Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  congr 1
  field_simp [show (g : ℂ) ≠ 0 by exact_mod_cast hg.ne',
    show (s : ℂ) ≠ 0 by exact_mod_cast hs.ne']
  push_cast
  ring

private lemma complex_mobius_scale_eq_affine
    {n p q u v a b c d g r s z : ℂ}
    (hD : c * z + d ≠ 0) (hs : s ≠ 0)
    (h00 : p * (n * a) + q * c = g) (h01 : p * (n * b) + q * d = r)
    (h10 : u * (n * a) + v * c = 0) (h11 : u * (n * b) + v * d = s) :
    (p * (n * ((a * z + b) / (c * z + d))) + q) /
        (u * (n * ((a * z + b) / (c * z + d))) + v) =
      r / s + g / s * z := by
  let D := c * z + d
  have hD' : D ≠ 0 := by simpa [D] using hD
  have hnum : p * (n * ((a * z + b) / D)) + q = (g * z + r) / D := by
    field_simp [hD']
    linear_combination z * h00 + h01
  have hden : u * (n * ((a * z + b) / D)) + v = s / D := by
    field_simp [hD']
    linear_combination z * h10 + h11
  rw [show c * z + d = D from rfl, hnum, hden]
  field_simp [hD', hs]
  ring

/-- If `δ · diag(N, 1) · γ = !![g, r; 0, s]` with `δ, γ ∈ SL₂(ℤ)`, then `δ` carries `N (γ τ)` to
the affine point `(r + gτ) / s`. -/
theorem smul_natScale_smul_eq_affine
    (N : ℕ+) (γ δ : SL(2, ℤ)) (g s : ℕ) (hg : 0 < g) (hs : 0 < s)
    (r : ℤ)
    (hmat : δ.1 * !![(N : ℤ) * γ 0 0, (N : ℤ) * γ 0 1; γ 1 0, γ 1 1] =
      !![(g : ℤ), r; 0, (s : ℤ)]) (τ : ℍ) :
    δ • natScale N (γ • τ) = affineUpperHalfPlane g s hg hs r τ := by
  have h00 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hmat 0) 0)
  have h01 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hmat 0) 1)
  have h10 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hmat 1) 0)
  have h11 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hmat 1) 1)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h00 h01 h10 h11
  push_cast at h00 h01 h10 h11
  have hD : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (γ 1 1 : ℤ)) ≠ 0 := by
    simpa [ModularGroup.denom_apply, algebraMap_int_eq] using
      UpperHalfPlane.denom_ne_zero γ τ
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, coe_natScale,
    UpperHalfPlane.coe_specialLinearGroup_apply, coe_affineUpperHalfPlane]
  exact complex_mobius_scale_eq_affine hD (by exact_mod_cast hs.ne') h00 h01 h10 h11

/-- Under the normalization `δ · diag(N, 1) · γ = !![g, r; 0, s]`, the transform `j(N γτ)` is
`j` of the affine point `(r + gτ) / s`. -/
theorem levelJ_smul_eq_j_affine
    (N : ℕ+) (γ δ : SL(2, ℤ)) (g s : ℕ) (hg : 0 < g) (hs : 0 < s) (r : ℤ)
    (hmat : δ.1 * !![(N : ℤ) * γ 0 0, (N : ℤ) * γ 0 1; γ 1 0, γ 1 1] =
      !![(g : ℤ), r; 0, (s : ℤ)]) (τ : ℍ) :
    levelJ N (γ • τ) = j (affineUpperHalfPlane g s hg hs r τ) := by
  rw [levelJ_apply, ← j_modularGroup_smul δ, smul_natScale_smul_eq_affine N γ δ g s hg hs r hmat]

private lemma cuspFunction_affine_j_eq (g s : ℕ) (hg : 0 < g) (hs : 0 < s)
    (r : ℤ) {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) :
    cuspFunction (((g * s : ℕ) : ℝ))
        (fun τ : ℍ ↦ j (affineUpperHalfPlane g s hg hs r τ)) q =
      cuspFunction 1 j
        (Complex.exp (2 * Real.pi * Complex.I * ((r : ℝ) / s)) * q ^ (g * g)) := by
  have hgs : (0 : ℝ) < (g * s : ℕ) := by positivity
  have him := Periodic.im_invQParam_pos_of_norm_lt_one hgs hqnorm hq0
  let τ : ℍ := ⟨Periodic.invQParam ((g * s : ℕ) : ℝ) q, him⟩
  let w : ℍ := affineUpperHalfPlane g s hg hs r τ
  have hleft :
      cuspFunction (((g * s : ℕ) : ℝ))
          (fun z : ℍ ↦ j (affineUpperHalfPlane g s hg hs r z)) q = j w := by
    rw [cuspFunction_apply_of_ne_zero _ _ hq0, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hqparam :
      Periodic.qParam 1 w =
        Complex.exp (2 * Real.pi * Complex.I * ((r : ℝ) / s)) * q ^ (g * g) := by
    rw [show w = affineUpperHalfPlane g s hg hs r τ from rfl,
      qParam_affineUpperHalfPlane]
    rw [show Periodic.qParam ((g * s : ℕ) : ℝ) τ = q by
      simpa [τ] using Periodic.qParam_right_inv
        (show (((g * s : ℕ) : ℝ)) ≠ 0 by positivity) hq0]
  rw [hleft, ← hqparam]
  exact (UpperHalfPlane.eq_cuspFunction w one_ne_zero ModularFunction.j_periodic).symm

/-- Left `SL₂(ℤ)`-triangularization of `diag(N, 1) · γ`, used to describe `j(Nτ)` at each
cusp. -/
private lemma exists_levelJ_cusp_normalization (N : ℕ+) (γ : SL(2, ℤ)) :
    ∃ (δ : SL(2, ℤ)) (g s : ℕ), 0 < g ∧ 0 < s ∧ g * s = (N : ℕ) ∧ ∃ r : ℤ,
      δ.1 * !![(N : ℤ) * γ 0 0, (N : ℤ) * γ 0 1; γ 1 0, γ 1 1] = !![(g : ℤ), r; 0, (s : ℤ)] := by
  set M : Matrix (Fin 2) (Fin 2) ℤ := !![(N : ℤ) * γ 0 0, (N : ℤ) * γ 0 1; γ 1 0, γ 1 1]
  have hdet : M.det = N := by
    have hγ := γ.prop
    rw [Matrix.det_fin_two] at hγ
    rw [Matrix.det_fin_two_of]
    linear_combination (N : ℤ) * hγ
  obtain ⟨δ, hH⟩ := M.exists_SL2_mul_isHermiteNormalForm (by rw [hdet]; positivity)
  have hHdet : (δ.1 * M).det = N := by simp [Matrix.det_mul, hdet]
  obtain ⟨h10, hg, hs, -⟩ :=
    (Matrix.isHermiteNormalForm_fin_two_iff (by rw [hHdet]; positivity)).mp hH
  have hgs : (δ.1 * M) 0 0 * (δ.1 * M) 1 1 = (N : ℤ) := by
    calc
      _ = (δ.1 * M).det := by rw [Matrix.det_fin_two, h10, mul_zero, sub_zero]
      _ = N := hHdet
  refine ⟨δ, ((δ.1 * M) 0 0).natAbs, ((δ.1 * M) 1 1).natAbs,
    Int.natAbs_pos.mpr hg.ne', Int.natAbs_pos.mpr hs.ne', ?_, (δ.1 * M) 0 1, ?_⟩
  · rw [← Int.natAbs_mul, hgs, Int.natAbs_natCast]
  · conv_lhs => rw [Matrix.eta_fin_two (δ.1 * M), h10]
    simp only [Int.natCast_natAbs, abs_of_pos hg, abs_of_pos hs]

private lemma affine_j_cuspFunction_meromorphicAt
    (g s : ℕ) (hg : 0 < g) (hs : 0 < s) (r : ℤ) :
    MeromorphicAt
      (cuspFunction (((g * s : ℕ) : ℝ))
        (fun τ : ℍ ↦ j (affineUpperHalfPlane g s hg hs r τ))) 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((r : ℝ) / s))
  let φ : ℂ → ℂ := fun q ↦ ζ * q ^ (g * g)
  have hgg : g * g ≠ 0 := mul_ne_zero hg.ne' hg.ne'
  have hφ0 : φ 0 = 0 := by simp [φ, hgg]
  have hφan : AnalyticAt ℂ φ 0 := by
    exact analyticAt_const.mul (analyticAt_id.pow (g * g))
  have hbase : MeromorphicAt (cuspFunction 1 j) (φ 0) := by
    simpa [hφ0] using j_cuspFunction_meromorphicAt
  have hcomp : MeromorphicAt ((cuspFunction 1 j) ∘ φ) 0 :=
    hbase.comp_analyticAt hφan
  refine hcomp.congr ?_
  filter_upwards [eventually_ne_zero_and_norm_lt_one] with q ⟨hq0, hqnorm⟩
  simpa [Function.comp_apply, φ, ζ] using
    (cuspFunction_affine_j_eq g s hg hs r hq0 hqnorm).symm

private lemma levelJ_meromorphicAt_cusp (N : ℕ+) (γ : SL(2, ℤ)) :
    MeromorphicAt
      (cuspFunction ((N : ℕ) : ℝ) (fun τ : ℍ ↦ levelJ N (γ • τ))) 0 := by
  obtain ⟨δ, g, s, hg, hs, hgs, r, hmat⟩ := exists_levelJ_cusp_normalization N γ
  rw [funext (levelJ_smul_eq_j_affine N γ δ g s hg hs r hmat), ← hgs]
  exact affine_j_cuspFunction_meromorphicAt g s hg hs r

/-- The level transform `j(Nτ)` is holomorphic on the upper half-plane. -/
theorem levelJ_mdifferentiable (N : ℕ+) : MDiff (levelJ N) :=
  UpperHalfPlane.mdifferentiable_iff.mpr fun z hz ↦
    (levelJ_differentiableAt (N : ℕ) (z := ⟨z, hz⟩)).differentiableWithinAt

/-- The second generator of the modular function field, using the shared bundled definition. -/
def levelJModularFunction (N : ℕ+) :
    ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ)) :=
  ModularFunction.ofGamma0Holomorphic N (levelJ N) (levelJ_mdifferentiable N)
    (fun γ ↦ levelJ_slash_invariant (N : ℕ) γ) (levelJ_meromorphicAt_cusp N)

/-- Analytic data for the bundled level transform. -/
theorem levelJ_cuspData (N : ℕ+) : CuspData N (levelJ N) :=
  CuspData.of_modularFunction N (levelJModularFunction N)

end Cox
