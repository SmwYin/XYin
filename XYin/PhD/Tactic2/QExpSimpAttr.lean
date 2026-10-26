/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.Tactic.Attr.Register

/-!
# The `qexp_simps` simp set

This file registers the simp attribute `qexp_simps` used by the experimental `qexp_simp`
tactic of `XYin.PhD.Tactic2.qexp_simp`. (A simp attribute must be registered in a module other
than the one tagging lemmas with it.)
-/

/-- The simp set of the `qexp_simp` tactic: closure lemmas for the side conditions of mathlib's
`q`-expansion API (periodicity, holomorphy, boundedness at `i∞`, analyticity of the cusp
function at `0`). -/
register_simp_attr qexp_simps
