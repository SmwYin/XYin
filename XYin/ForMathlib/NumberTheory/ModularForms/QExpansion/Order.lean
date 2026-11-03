/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
module

public import XYin.ForMathlib.NumberTheory.ModularForms.QExpansion.ChangeRepresentative
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Vanishing orders of q-expansions at cusp representatives

We use `PowerSeries.order`, valued in `ℕ∞`, so that the zero series has order infinity.
The vanishing order is independent of the representative of a cusp orbit under the
global holomorphy and boundedness hypotheses for the power series expansion.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm
open scoped MatrixGroups Manifold

namespace SlashInvariantForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
  (f : SlashInvariantForm Γ k) {γ : SL(2, ℤ)}

/-- Positive vanishing order is equivalent to vanishing of the constant coefficient. -/
lemma qExpansionAt_order_pos_iff :
    0 < (f.qExpansionAt γ).order ↔ (f.qExpansionAt γ).coeff 0 = 0 := by
  rw [pos_iff_ne_zero, PowerSeries.order_ne_zero_iff_constCoeff_eq_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Under the global analytic hypotheses, infinite vanishing order detects the zero form. -/
lemma qExpansionAt_order_eq_top_iff
    (hh : 0 < Γ.strictWidthAt γ)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k] γ)) :
    (f.qExpansionAt γ).order = ⊤ ↔ f = 0 := by
  rw [PowerSeries.order_eq_top, f.qExpansionAt_eq_zero_iff hh hfhol hfbdd]

section IntegralSubgroup

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
  (f : SlashInvariantForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) {γ γ' : SL(2, ℤ)}

/-- The vanishing order of a q-expansion depends only on its cusp orbit. -/
lemma qExpansionAt_order_eq_of_cuspOrbit_eq
    (h : cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ'⁻¹⟧ =
      cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ⁻¹⟧)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k] γ)) :
    (f.qExpansionAt γ').order = (f.qExpansionAt γ).order := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  simp only [PowerSeries.nat_le_order_iff,
    f.qExpansionAt_coeff_eq_zero_iff_of_cuspOrbit_eq h hfhol hfbdd]

end IntegralSubgroup

end SlashInvariantForm
