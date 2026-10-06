/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealGroups
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-! # The stabilizer average in Janusz V.2.3

This is the first unit-lattice step on printed pp.145–146. The product is the actual
product of conjugate integer units. The later equivariant family, logarithmic rank,
relation normalization and finite-index conclusions remain separate obligations.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise

noncomputable section
namespace Cox.ClassFieldTheory

/-- The Dirichlet-unit construction makes a unit small at every other infinite place. -/
theorem exists_unit_below_one_except (L : Type*) [Field L] [NumberField L]
    (v : InfinitePlace L) :
    ∃ u : (𝓞 L)ˣ, ∀ v' : InfinitePlace L, v' ≠ v → v' (u : L) < 1 := by
  obtain ⟨u, hu⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit (K := L) v
  exact ⟨u, fun v' hv' =>
    (Real.log_neg_iff (NumberField.Units.pos_at_place u v')).mp (hu v' hv')⟩

section Averaging
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

open scoped Classical in
/-- The product of the actual conjugate integer units over the place stabilizer. -/
def stabilizerUnitProduct (v : InfinitePlace L) (u : (𝓞 L)ˣ) : (𝓞 L)ˣ :=
  ∏ τ : MulAction.stabilizer (L ≃ₐ[K] L) v,
    Units.map (RingOfIntegers.mapRingEquiv (τ : L ≃ₐ[K] L).toRingEquiv).toMonoidHom u

open scoped Classical in
/-- Evaluating the stabilizer product uses the inverse action on infinite places. -/
theorem stabilizerUnitProduct_apply (v v' : InfinitePlace L) (u : (𝓞 L)ˣ) :
    v' ((stabilizerUnitProduct K L v u : (𝓞 L)ˣ) : L) =
      ∏ τ : MulAction.stabilizer (L ≃ₐ[K] L) v,
        (((τ : L ≃ₐ[K] L)⁻¹) • v') (u : L) := by
  rw [stabilizerUnitProduct, Units.coe_prod, map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [InfinitePlace.smul_apply]
  rfl

/-- Left multiplication permutes the stabilizer factors, so the product is fixed. -/
theorem stabilizerUnitProduct_fixed (v : InfinitePlace L) (u : (𝓞 L)ˣ) :
    ∀ σ : L ≃ₐ[K] L, σ • v = v →
      σ ((stabilizerUnitProduct K L v u : (𝓞 L)ˣ) : L) =
        ((stabilizerUnitProduct K L v u : (𝓞 L)ˣ) : L) := by
  intro σ hσ
  classical
  let σ' : MulAction.stabilizer (L ≃ₐ[K] L) v := ⟨σ, hσ⟩
  rw [stabilizerUnitProduct, Units.coe_prod, map_prod, map_prod]
  exact Fintype.prod_equiv (Equiv.mulLeft σ') _ _ fun τ => rfl

/-- Positivity and strict smallness of every factor give strict smallness of the product. -/
theorem stabilizerUnitProduct_below_one (v : InfinitePlace L) (u : (𝓞 L)ˣ)
    (hu : ∀ v' : InfinitePlace L, v' ≠ v → v' (u : L) < 1) :
    ∀ v' : InfinitePlace L, v' ≠ v →
      v' ((stabilizerUnitProduct K L v u : (𝓞 L)ˣ) : L) < 1 := by
  classical
  intro v' hv'
  rw [stabilizerUnitProduct_apply]
  calc ∏ τ : MulAction.stabilizer (L ≃ₐ[K] L) v, (((τ : L ≃ₐ[K] L)⁻¹) • v') (u : L)
      < ∏ _τ : MulAction.stabilizer (L ≃ₐ[K] L) v, (1 : ℝ) := by
        refine Finset.prod_lt_prod_of_nonempty (fun τ _ => NumberField.Units.pos_at_place u _)
          (fun τ _ => hu _ ?_) Finset.univ_nonempty
        intro h
        exact hv' ((inv_smul_eq_iff.mp h).trans τ.2)
    _ = 1 := Finset.prod_const_one

end Averaging

/-- The stabilizer product gives a principal-ideal-kernel unit fixed by the stabilizer.
Neither Galoisness nor a condition on real places is used in this averaging step. -/
theorem exists_unit_fixed_by_stabilizer (K L : Type*)
    [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : InfinitePlace L) :
    ∃ u : (toPrincipalIdeal (𝓞 L) L).ker,
      (∀ v' : InfinitePlace L, v' ≠ v → v' ((u : Lˣ) : L) < 1) ∧
      ∀ σ : L ≃ₐ[K] L, σ • v = v → σ • (u : Lˣ) = (u : Lˣ) := by
  classical
  obtain ⟨u, hu⟩ := exists_unit_below_one_except L v
  set w := stabilizerUnitProduct K L v u
  have hker : Units.map (algebraMap (𝓞 L) L).toMonoidHom w ∈ (toPrincipalIdeal (𝓞 L) L).ker := by
    rw [MonoidHom.mem_ker, toPrincipalIdeal_eq_iff, Units.val_one]
    change FractionalIdeal.spanSingleton _ (algebraMap (𝓞 L) L (w : 𝓞 L)) = 1
    rw [← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr w.isUnit,
      FractionalIdeal.coeIdeal_top]
  refine ⟨⟨_, hker⟩, fun v' hv' => stabilizerUnitProduct_below_one K L v u hu v' hv',
    fun σ hσ => Units.ext ?_⟩
  exact stabilizerUnitProduct_fixed K L v u σ hσ

end Cox.ClassFieldTheory
