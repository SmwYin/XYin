/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealAction
import XYin.PhD.Cox.Theorem11_1.ClassFieldCohomology
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnitFiniteIndex

/-! # Global units and their finite-index lattice

The actual unit module includes torsion. Its finite generation comes from
Dirichlet's theorem. The selected equivariant family's finite-index subgroup has
the same Herbrand quotient, using Janusz's convention H¹/H⁰_Tate.
The diagonal-quotient computation remains a separate step.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise
noncomputable section
namespace Cox.ClassFieldTheory
open Cox.CyclicCohomology

/-- The actual global units inside field units, as the principal-ideal kernel. -/
def globalUnitSubmodule (L : Type*) [Field L] [NumberField L] :
    Submodule ℤ (Additive Lˣ) :=
  (toPrincipalIdeal (𝓞 L) L).ker.toAddSubgroup.toIntSubmodule

/-- An arbitrary base-field automorphism preserves actual global units. -/
theorem globalUnitSubmodule_stable (K L : Type*) [Field K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) :
    globalUnitSubmodule L ≤ (globalUnitSubmodule L).comap
      ((Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ) := by
  intro x hx
  change toPrincipalIdeal (𝓞 L) L (Additive.toMul x) = 1 at hx
  change toPrincipalIdeal (𝓞 L) L (σ • Additive.toMul x) = 1
  obtain ⟨y, hy⟩ := (principalIdeal_eq_one_iff L _).mp hx
  refine (principalIdeal_eq_one_iff L _).mpr
    ⟨Units.map (NumberField.RingOfIntegers.mapRingEquiv (σ : L ≃+* L)).toMonoidHom y, ?_⟩
  rw [← hy]
  ext
  simp [NumberField.RingOfIntegers.mapRingEquiv_apply]

/-- Restrict the actual field-unit action to global units. -/
def globalUnitRepresentation (K L : Type*) [Field K] [Field L]
    [NumberField L] [Algebra K L] :
    Representation ℤ (L ≃ₐ[K] L) (globalUnitSubmodule L) :=
  (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ).subrepresentation
    (globalUnitSubmodule L) (globalUnitSubmodule_stable K L)

/-- The actual global-unit module and the additive principal kernel have the same elements. -/
def globalUnitEquivPrincipal (L : Type*) [Field L] [NumberField L] :
    globalUnitSubmodule L ≃ₗ[ℤ] Additive (toPrincipalIdeal (𝓞 L) L).ker :=
  AddEquiv.toIntLinearEquiv {
    toFun := fun x => Additive.ofMul ⟨Additive.toMul x.val, x.property⟩
    invFun := fun x => ⟨Additive.ofMul (Additive.toMul x).val, (Additive.toMul x).property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }

/-- Dirichlet finite generation includes the torsion subgroup of the actual units. -/
theorem globalUnit_moduleFinite (L : Type*) [Field L] [NumberField L] :
    Module.Finite ℤ (globalUnitSubmodule L) := by
  obtain ⟨e, -⟩ := exists_principalUnitEquiv L
  exact Module.Finite.equiv
    ((globalUnitEquivPrincipal L).trans (MulEquiv.toAdditive e).toIntLinearEquiv).symm

/-- The cyclic Tate groups of the finitely generated global-unit module are finite. -/
theorem globalUnit_finiteHerbrand (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    FiniteHerbrand (globalUnitRepresentation K L) σ := by
  haveI := globalUnit_moduleFinite L
  exact finiteHerbrand_of_moduleFinite (globalUnitRepresentation K L) σ hσ

/-- The exponent-map range, pulled back to the module of actual global units. -/
def unitLatticeSubmodule (L : Type*) [Field L] [NumberField L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker) :
    Submodule ℤ (globalUnitSubmodule L) :=
  (LinearMap.range (unitExponentMap L u)).comap (globalUnitSubmodule L).subtype

/-- The pulled-back range is exactly the closure of the family in the principal kernel. -/
theorem unitLatticeSubmodule_eq_kernelClosure (L : Type*) [Field L] [NumberField L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker) :
    unitLatticeSubmodule L u =
      ((Subgroup.closure (Set.range u)).toAddSubgroup.toIntSubmodule).comap
        (globalUnitEquivPrincipal L).toLinearMap := by
  have h1 (y : Additive Lˣ) : y ∈ LinearMap.range (unitExponentMap L u) ↔
      Additive.toMul y ∈ Subgroup.closure (Set.range (fun w => (u w : Lˣ))) := by
    change y ∈ (LinearMap.range (unitExponentMap L u)).toAddSubgroup ↔ _
    rw [unitExponentMap_range_eq_generated]
    rfl
  have hmap : (Subgroup.closure (Set.range u)).map (toPrincipalIdeal (𝓞 L) L).ker.subtype =
      Subgroup.closure (Set.range (fun w => (u w : Lˣ))) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  ext x
  rw [unitLatticeSubmodule, Submodule.mem_comap, Submodule.mem_comap, h1, ← hmap]
  exact Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)

/-- Equivariance of the supplied family makes its actual generated submodule stable. -/
theorem unitLatticeSubmodule_stable (K L : Type*) [Field K] [Field L]
    [NumberField L] [Algebra K L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (hu : ∀ (σ : L ≃ₐ[K] L) w, σ • (u w : Lˣ) = (u (σ • w) : Lˣ))
    (σ : L ≃ₐ[K] L) :
    unitLatticeSubmodule L u ≤
      (unitLatticeSubmodule L u).comap (globalUnitRepresentation K L σ) := by
  intro x hx
  obtain ⟨f, hf⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hx)
  refine Submodule.mem_comap.mpr (LinearMap.mem_range.mpr
    ⟨(Representation.ofMulAction ℤ (L ≃ₐ[K] L) (InfinitePlace L)) σ f, ?_⟩)
  rw [unitExponentMap_equivariant K L u hu σ f, hf]
  rfl

/-- Finite index in the principal kernel gives a finite quotient of actual global units. -/
theorem unitLatticeSubmodule_finite_quotient (L : Type*) [Field L] [NumberField L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (hidx : (Subgroup.closure (Set.range u)).FiniteIndex) :
    Finite ((globalUnitSubmodule L) ⧸ unitLatticeSubmodule L u) := by
  rw [unitLatticeSubmodule_eq_kernelClosure]
  have hidx' : (Subgroup.closure (Set.range u)).toAddSubgroup.index ≠ 0 := by
    rw [Subgroup.index_toAddSubgroup]
    exact Subgroup.FiniteIndex.index_ne_zero
  haveI : ((((Subgroup.closure (Set.range u)).toAddSubgroup.toIntSubmodule).comap
      (globalUnitEquivPrincipal L).toLinearMap).toAddSubgroup).FiniteIndex := by
    rw [AddSubgroup.finiteIndex_iff]
    change ((Subgroup.closure (Set.range u)).toAddSubgroup.comap
      (globalUnitEquivPrincipal L).toLinearMap.toAddMonoidHom).index ≠ 0
    rw [AddSubgroup.index_comap_of_surjective _ (globalUnitEquivPrincipal L).surjective]
    exact hidx'
  exact AddSubgroup.finite_quotient_of_finiteIndex

/-- The stable finite-index lattice has the same Herbrand quotient as all global units. -/
theorem unitLattice_herbrandQuotient_eq (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (hu : ∀ (σ : L ≃ₐ[K] L) w, σ • (u w : Lˣ) = (u (σ • w) : Lˣ))
    (hidx : (Subgroup.closure (Set.range u)).FiniteIndex)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (hU : FiniteHerbrand (globalUnitRepresentation K L) σ) :
    herbrandQuotient ((globalUnitRepresentation K L).subrepresentation
      (unitLatticeSubmodule L u) (unitLatticeSubmodule_stable K L u hu)) σ =
        herbrandQuotient (globalUnitRepresentation K L) σ := by
  haveI := unitLatticeSubmodule_finite_quotient L u hidx
  exact herbrandQuotient_subrepresentation (globalUnitRepresentation K L) σ
    (unitLatticeSubmodule L u) (unitLatticeSubmodule_stable K L u hu) hσ hU
    ((finiteHerbrand_iff_subrepresentation (globalUnitRepresentation K L) σ _ _ hσ).mp hU)

end Cox.ClassFieldTheory
