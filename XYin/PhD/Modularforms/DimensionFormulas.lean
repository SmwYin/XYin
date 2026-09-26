/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import XYin.PhD.Modularforms.SturmBound

/-!
# Finite-dimensionality of spaces of modular forms

Mathlib's `Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean` computes the
dimension of `ModularForm 𝒮ℒ k` and provides a `FiniteDimensional ℂ (ModularForm 𝒮ℒ k)` instance.
Here we record the corresponding statement for arbitrary finite-index subgroups of `SL(2, ℤ)`. It
is an instance of `ModularForm.instFiniteDimensional` (for arithmetic subgroups of `GL(2, ℝ)`),
which is proved in `XYin.PhD.Modularforms.SturmBound` via the Sturm bound, by taking the norm
(`ModularForm.norm`) down to level one.
-/

@[expose] public section

open scoped MatrixGroups

/-- Spaces of modular forms for a finite-index subgroup of `SL(2, ℤ)` are finite-dimensional. -/
lemma dim_gen_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    FiniteDimensional ℂ (ModularForm Γ k) :=
  have : Γ.FiniteIndex := ⟨hΓ⟩
  inferInstance
