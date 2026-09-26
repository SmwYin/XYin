/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.Polynomial.Bivariate
import XYin.PhD.ModularFunctions.Congruence

/-!
# Analytic cusp data for Cox's modular-function arguments

`CuspData` records the meromorphy, weight-zero invariance, and cusp expansions of raw
intermediate expressions. It is supplied by the bundled `ModularFunction` definition and is
preserved by the pointwise operations used in pole-clearing and interpolation. The three
components are accessed through `CuspData.meromorphicAt`, `CuspData.slash_eq` and
`CuspData.meromorphicAt_cuspFunction`; `LevelOneCuspData.of_widthM` builds level-one data from
invariance and a single cusp expansion.

This module also defines `RationalIn` and `RationalInTwo`, the pointwise rationality statements
used to present the corresponding meromorphic function fields.
-/

open Complex Filter Function MatrixGroups ModularForm UpperHalfPlane
open scoped Manifold Polynomial.Bivariate

noncomputable section

namespace Cox

/-- Auxiliary analytic data for raw expressions: meromorphy on `ℍ`, weight-zero
invariance under `Γ₀(N)`, and period-`N` cusp meromorphy. Point values at removable
singularities are not normalized; use `ModularFunction` for the public function-field API. -/
def CuspData (N : ℕ+) (f : ℍ → ℂ) : Prop :=
  (∀ z : ℂ, 0 < z.im → MeromorphicAt (f ∘ UpperHalfPlane.ofComplex) z) ∧
  (∀ γ : CongruenceSubgroup.Gamma0 (N : ℕ), f ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = f) ∧
  (∀ γ : SL(2, ℤ),
    MeromorphicAt (cuspFunction ((N : ℕ) : ℝ) (fun τ : ℍ ↦ f (γ • τ))) 0)

namespace CuspData

variable {N : ℕ+} {f : ℍ → ℂ}

/-- Raw cusp data is meromorphic at every point of the upper half-plane. -/
theorem meromorphicAt (hf : CuspData N f) (z : ℂ) (hz : 0 < z.im) :
    MeromorphicAt (f ∘ UpperHalfPlane.ofComplex) z :=
  hf.1 z hz

/-- Raw cusp data is meromorphic on the upper half-plane. -/
theorem meromorphicOn (hf : CuspData N f) :
    MeromorphicOn (f ∘ UpperHalfPlane.ofComplex) upperHalfPlaneSet :=
  hf.1

/-- Raw cusp data is weight-zero invariant under `Γ₀(N)`. -/
theorem slash_eq (hf : CuspData N f) (γ : CongruenceSubgroup.Gamma0 (N : ℕ)) :
    f ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = f :=
  hf.2.1 γ

/-- Raw cusp data is invariant under precomposition by `Γ₀(N)`. -/
theorem apply_smul (hf : CuspData N f) (γ : CongruenceSubgroup.Gamma0 (N : ℕ)) (τ : ℍ) :
    f ((γ : SL(2, ℤ)) • τ) = f τ :=
  SL_slash_zero_eq_iff.1 (hf.slash_eq γ) τ

/-- Every integral transform of raw cusp data has a meromorphic width-`N` cusp expansion. -/
theorem meromorphicAt_cuspFunction (hf : CuspData N f) (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction ((N : ℕ) : ℝ) (fun τ : ℍ ↦ f (γ • τ))) 0 :=
  hf.2.2 γ

end CuspData

/-- Level-one specialization of the raw analytic proof data. -/
abbrev LevelOneCuspData (f : ℍ → ℂ) : Prop :=
  CuspData (1 : ℕ+) f

namespace LevelOneCuspData

variable {f : ℍ → ℂ}

/-- Level-one raw cusp data is weight-zero invariant under all of `SL₂(ℤ)`. -/
theorem slash_sl2 (hf : LevelOneCuspData f) (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] γ = f :=
  hf.slash_eq (⟨γ, CongruenceSubgroup.Gamma0_mem.mpr (Subsingleton.elim _ _)⟩ :
    CongruenceSubgroup.Gamma0 1)

/-- Level-one raw cusp data is invariant under precomposition by `SL₂(ℤ)`. -/
theorem apply_sl2_smul (hf : LevelOneCuspData f) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = f τ :=
  SL_slash_zero_eq_iff.1 (hf.slash_sl2 γ) τ

/-- Level-one raw cusp data has period one. -/
theorem periodic (hf : LevelOneCuspData f) :
    Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ) :=
  periodic_comp_ofComplex_of_slashInvariant hf.slash_sl2

/-- Level-one raw cusp data has a meromorphic width-one cusp expansion. -/
theorem meromorphicAt_cuspFunction_one (hf : LevelOneCuspData f) :
    MeromorphicAt (cuspFunction 1 f) 0 := by
  simpa using hf.meromorphicAt_cuspFunction 1

/-- Level-one cusp data from meromorphy on `ℍ`, `SL₂(ℤ)`-invariance, and meromorphy of the
cusp expansion of some width `m`: invariance handles the other cusps and periodicity descends
the expansion to width one. -/
theorem of_widthM {m : ℕ+}
    (hH : ∀ z : ℂ, 0 < z.im → MeromorphicAt (f ∘ UpperHalfPlane.ofComplex) z)
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f)
    (hcusp : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) f) 0) : LevelOneCuspData f := by
  have hone : MeromorphicAt (cuspFunction 1 f) 0 :=
    meromorphicAt_cuspFunction_of_nat_mul (h := 1) (PNat.ne_zero m) (by simpa using hcusp)
      (periodic_comp_ofComplex_of_slashInvariant hslash)
  refine ⟨hH, fun γ ↦ hslash γ, fun γ ↦ ?_⟩
  rw [← SL_slash_zero_eq, hslash γ]
  simpa using hone

end LevelOneCuspData

/-- Pointwise evaluation of a polynomial in a function. -/
def polynomialIn (P : Polynomial ℂ) (g : ℍ → ℂ) : ℍ → ℂ :=
  fun τ ↦ P.eval (g τ)

@[simp]
theorem polynomialIn_apply (P : Polynomial ℂ) (g : ℍ → ℂ) (τ : ℍ) :
    polynomialIn P g τ = P.eval (g τ) :=
  rfl

/-- A function belongs to the rational function field generated by one function.  Equality is
required away from the zero set of the chosen denominator, which is the appropriate pointwise
form of equality of meromorphic functions.
-/
def RationalIn (f g : ℍ → ℂ) : Prop :=
  ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
    ∀ τ : ℍ, Q.eval (g τ) ≠ 0 → f τ = P.eval (g τ) / Q.eval (g τ)

/-- A function belongs to the rational function field generated by two functions. The
denominator must be nonzero after restriction to the parametrized curve; merely requiring the
formal bivariate polynomial to be nonzero would allow a defining equation of the curve and make
the predicate vacuous. -/
def RationalInTwo (f g h : ℍ → ℂ) : Prop :=
  ∃ P Q : ℂ[X][Y], (fun τ : ℍ ↦ Q.evalEval (g τ) (h τ)) ≠ 0 ∧
    ∀ τ : ℍ, Q.evalEval (g τ) (h τ) ≠ 0 →
      f τ = P.evalEval (g τ) (h τ) / Q.evalEval (g τ) (h τ)

/-- A bundled modular function supplies the analytic data used by Cox's proofs. -/
theorem CuspData.of_modularFunction (N : ℕ+)
    (f : ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ))) : CuspData N f :=
  ⟨f.meromorphicOn, fun γ ↦ f.slash_action_eq' _ ⟨γ, γ.property, rfl⟩,
    ModularFunction.cuspFunction_gamma0 N f⟩

/-- A level-one modular function supplies period-one analytic data. -/
theorem CuspData.of_levelOneModularFunction (f : ModularFunction 𝒮ℒ) :
    LevelOneCuspData f :=
  CuspData.of_modularFunction 1 (f.restrict (Subgroup.map_le_range ..))

/-- The bundled `j` supplies period-`N` analytic data after restriction to `Γ₀(N)`. -/
theorem j_cuspData (N : ℕ+) : CuspData N j :=
  CuspData.of_modularFunction N (jModularFunction.restrict (Subgroup.map_le_range ..))

/-- Period-one analytic data of `j`. -/
theorem j_levelOneCuspData : LevelOneCuspData j :=
  j_cuspData 1

/-- Raw analytic cusp data is preserved by pointwise multiplication. -/
theorem CuspData.mul {N : ℕ+} {f g : ℍ → ℂ}
    (hf : CuspData N f) (hg : CuspData N g) :
    CuspData N (fun τ ↦ f τ * g τ) :=
  ⟨fun z hz ↦ (hf.meromorphicAt z hz).mul (hg.meromorphicAt z hz),
    fun γ ↦ SL_slash_zero_eq_iff.2 fun τ ↦ by simp only [hf.apply_smul, hg.apply_smul],
    fun γ ↦ meromorphicAt_cuspFunction_mul (hf.meromorphicAt_cuspFunction γ)
      (hg.meromorphicAt_cuspFunction γ)⟩

/-- Polynomial evaluation preserves raw analytic cusp data. -/
theorem CuspData.polynomialIn {N : ℕ+} {f : ℍ → ℂ}
    (hf : CuspData N f) (P : Polynomial ℂ) :
    CuspData N (Cox.polynomialIn P f) :=
  ⟨fun z hz ↦ (hf.meromorphicAt z hz).polynomial_eval P,
    fun γ ↦ SL_slash_zero_eq_iff.2 fun τ ↦ by simp only [polynomialIn_apply, hf.apply_smul],
    fun γ ↦ meromorphicAt_cuspFunction_polynomial_eval (hf.meromorphicAt_cuspFunction γ) P⟩

end Cox
