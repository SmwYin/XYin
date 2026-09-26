/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.ModularFunctions.Basic
import XYin.PhD.jFunction.jfunction

/-!
# The modular invariant as a modular function

The classical modular invariant `j` defines a modular function for `SL₂(ℤ)`. Its existing
meromorphic cusp expansion supplies the exponential growth condition at every cusp.
-/

open Function UpperHalfPlane
open scoped Manifold MatrixGroups

noncomputable section

namespace ModularFunction

/-- The modular invariant has period one. -/
theorem j_periodic : Periodic (j ∘ UpperHalfPlane.ofComplex) 1 :=
  periodic_comp_ofComplex_of_slashInvariant j_slash_invariant

/-- The modular invariant has at most exponential growth at infinity. -/
theorem j_isOfExponentialGrowth : IsOfExponentialGrowth j :=
  isOfExponentialGrowth_of_meromorphicAt_cuspFunction one_pos j_periodic
    j_cuspFunction_meromorphicAt

end ModularFunction

/-- The classical modular invariant, bundled as a level-one modular function. -/
def jModularFunction : ModularFunction 𝒮ℒ :=
  ModularFunction.ofLevelOneHolomorphic j j_mdifferentiable j_slash_invariant
    j_cuspFunction_meromorphicAt

@[simp]
theorem coe_jModularFunction : (jModularFunction : ℍ → ℂ) = j := rfl
