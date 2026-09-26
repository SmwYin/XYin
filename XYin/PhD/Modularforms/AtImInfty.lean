/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-!
# Eventually at `i∞`

The `∀ᶠ` spelling of `UpperHalfPlane.atImInfty_mem`.
-/

@[expose] public section

open UpperHalfPlane

/-- A property holds eventually at `i∞` iff it holds on some half-plane `{A ≤ im z}`. -/
lemma Filter.eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
  atImInfty_mem (setOf p)
