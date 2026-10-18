/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# Positive periods at cusps

A slash-invariant form for a discrete group with determinants in `{±1}` has a positive real
period in every cusp chart. Conjugation transports the group, its topology, and its determinant
condition, so the strict width at infinity supplies the period.
-/

open UpperHalfPlane MatrixGroups ModularForm
open scoped Pointwise

namespace Subgroup

/-- Conjugation preserves the determinant condition used for modular forms. -/
instance hasDetPlusMinusOne_conj (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetPlusMinusOne]
    (g : GL (Fin 2) ℝ) : (ConjAct.toConjAct g • Γ).HasDetPlusMinusOne where
  det_eq {j} hj := by
    obtain ⟨x, hx, rfl⟩ := hj
    simpa [ConjAct.toConjAct_smul, map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]
      using HasDetPlusMinusOne.det_eq hx

/-- Conjugation preserves discreteness of a subgroup. -/
theorem discreteTopology_conj {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (Γ : Subgroup G) [DiscreteTopology Γ] (g : G) :
    DiscreteTopology ↥(ConjAct.toConjAct g • Γ) := by
  let e : ↥(ConjAct.toConjAct g • Γ) → Γ := fun x ↦
    ⟨g⁻¹ * x * g, by
      simpa only [← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, inv_inv]
        using Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := e)
  · fun_prop
  · intro x y h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    simpa [e] using h'

end Subgroup

namespace SlashInvariantForm

/-- A slash-invariant form has a positive real period in a chart at any cusp. -/
theorem exists_pos_period_at_cusp {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] (f : SlashInvariantForm Γ k)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) (g : GL (Fin 2) ℝ)
    (hg : g • OnePoint.infty = c) :
    ∃ h : ℝ, 0 < h ∧ Function.Periodic (((f : ℍ → ℂ) ∣[k] g) ∘ ofComplex) h := by
  let Γ' := ConjAct.toConjAct g⁻¹ • Γ
  have : DiscreteTopology Γ' := Γ.discreteTopology_conj g⁻¹
  have hc' : IsCusp OnePoint.infty Γ' := by
    simpa [Γ', ← hg] using hc.smul g⁻¹
  exact ⟨Γ'.strictWidthInfty, Γ'.strictWidthInfty_pos_iff.mpr hc',
    SlashInvariantFormClass.periodic_comp_ofComplex (translate f g)
      Γ'.strictWidthInfty_mem_strictPeriods⟩

end SlashInvariantForm
