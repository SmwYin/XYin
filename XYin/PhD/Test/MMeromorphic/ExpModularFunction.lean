import XYin.PhD.ModularFunctions.Algebra
import XYin.PhD.ModularFunctions.Congruence
import XYin.PhD.ModularFunctions.JInvariant
import XYin.PhD.Test.MMeromorphic.CuspQEquivalence

/-!
# Checks for the requested modular-function definition

These checks use the production bundle, its independent manifold normal-form predicate,
the requested exponential cusp field, and the subsequently constructed field element.
-/

open UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

noncomputable section

namespace MMeromorphicTest.Exponential

variable {Γ : Subgroup (GL (Fin 2) ℝ)}

example (f : ModularFunction Γ) : MMeromorphicNF (f : ℍ → ℂ) := f.meromorphic'

example (f : ModularFunction Γ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsExpBoundedAt f 0 := f.bdd_at_cusps' hc

-- Membership follows from the analytic predicate; it is not the analytic structure field.
example (f : ModularFunction Γ) :
    ∃ a : MeromorphicField, MeromorphicField.toFun a = f :=
  ⟨f.toMeromorphicField, f.toFun_toMeromorphicField⟩

example [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] (f : SlashInvariantForm Γ 0)
    (hf : MMeromorphicNF (f : ℍ → ℂ)) :
    (∀ c, IsCusp c Γ → c.IsExpBoundedAt f 0) ↔
      ∀ c, IsCusp c Γ → c.IsMeromorphicAt f :=
  f.exp_bounded_at_cusps_zero_iff (mmeromorphicNF_iff.1 hf)

example [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] : Field (ModularFunction Γ) :=
  inferInstance

example : Field (ModularFunction 𝒮ℒ) := inferInstance

example : Algebra ℂ (ModularFunction 𝒮ℒ) := inferInstance

/-- The bundled inverse law survives the revised independent analytic definition. -/
theorem levelOne_mul_inv_cancel (f : ModularFunction 𝒮ℒ) (hf : f ≠ 0) :
    f * f⁻¹ = 1 := mul_inv_cancel₀ hf

example (f : ModularFunction 𝒮ℒ) :
    MeromorphicField.toFun f.toMeromorphicField = f := f.toFun_toMeromorphicField

#print axioms OnePoint.isExpBoundedAt_zero_iff_isMeromorphicAt
#print axioms ModularFunction.toFun_toMeromorphicField
#print axioms ModularFunction.toMeromorphicField_injective
#print axioms levelOne_mul_inv_cancel

end MMeromorphicTest.Exponential
