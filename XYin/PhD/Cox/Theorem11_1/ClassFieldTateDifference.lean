/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCohomology

/-! # The difference quotient in Janusz V.3.8

The source map x ↦ σ(x)/x is written additively as σ−1. Its range lies in the
chosen submodule, and its kernel modulo that submodule is computed explicitly.
-/
noncomputable section
namespace Cox.CyclicCohomology
variable {G A : Type*} [Group G] [Fintype G] [AddCommGroup A]
variable (ρ : Representation ℤ G A) (g : G)

/-- Vanishing first Tate cohomology says every norm-zero vector is a difference. -/
theorem range_difference_eq_ker_norm_of_subsingleton [Subsingleton (tateOne ρ g)] :
    LinearMap.range (ρ g - LinearMap.id) = LinearMap.ker ρ.norm := by
  have h : (LinearMap.range (ρ g - LinearMap.id)).comap (LinearMap.ker ρ.norm).subtype = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp ‹_›
  exact le_antisymm (range_difference_le_ker_norm ρ g) (Submodule.comap_subtype_eq_top.mp h)

variable (W : Submodule ℤ A) (hW : ∀ γ, W ≤ W.comap (ρ γ))
variable (hD : LinearMap.range (ρ g - LinearMap.id) ≤ W)

/-- The restricted norm is the ambient norm on the underlying vector. -/
theorem subrepresentation_norm_coe (w : W) :
    (((ρ.subrepresentation W hW).norm w : W) : A) = ρ.norm (w : A) :=
  intertwining_norm (ρ.subrepresentation W hW) ρ (submoduleIntertwining ρ W hW) w

/-- The ambient difference is a norm-zero vector in the actual restricted representation. -/
theorem difference_mem_subrepresentation_norm_kernel (a : A) :
    (ρ.subrepresentation W hW).norm
      ⟨(ρ g - LinearMap.id : Module.End ℤ A) a, hD ⟨a, rfl⟩⟩ = 0 := by
  apply Subtype.ext
  rw [subrepresentation_norm_coe, ZeroMemClass.coe_zero]
  exact LinearMap.mem_ker.mp (range_difference_le_ker_norm ρ g ⟨a, rfl⟩)

/-- The actual source difference map, followed by its first Tate class. -/
def tateDifferenceMap : A →ₗ[ℤ] tateOne (ρ.subrepresentation W hW) g :=
  ((LinearMap.range ((ρ.subrepresentation W hW) g - LinearMap.id)).comap
      (LinearMap.ker (ρ.subrepresentation W hW).norm).subtype).mkQ ∘ₗ
    (((ρ g - LinearMap.id : Module.End ℤ A).codRestrict W (fun a ↦ hD ⟨a, rfl⟩)).codRestrict
      (LinearMap.ker (ρ.subrepresentation W hW).norm)
      (difference_mem_subrepresentation_norm_kernel ρ g W hW hD))

/-- The quotient map has the literal difference representative from the source. -/
theorem tateDifferenceMap_apply (a : A) :
    tateDifferenceMap ρ g W hW hD a = oneClass (ρ.subrepresentation W hW) g
      ⟨⟨(ρ g - LinearMap.id : Module.End ℤ A) a, hD ⟨a, rfl⟩⟩,
        difference_mem_subrepresentation_norm_kernel ρ g W hW hD a⟩ := by
  rfl

/-- Ambient Hilbert90 makes the restricted difference-class map surjective. -/
theorem tateDifferenceMap_surjective
    (hFull : LinearMap.range (ρ g - LinearMap.id) = LinearMap.ker ρ.norm) :
    Function.Surjective (tateDifferenceMap ρ g W hW hD) := by
  intro c
  obtain ⟨⟨u, hu⟩, rfl⟩ := oneClass_surjective (ρ.subrepresentation W hW) g c
  have hu' : (u : A) ∈ LinearMap.ker ρ.norm := by
    rw [LinearMap.mem_ker, ← subrepresentation_norm_coe ρ W hW u, LinearMap.mem_ker.mp hu,
      ZeroMemClass.coe_zero]
  rw [← hFull] at hu'
  obtain ⟨a, ha⟩ := hu'
  refine ⟨a, ?_⟩
  rw [tateDifferenceMap_apply]
  congr 1
  exact Subtype.ext (Subtype.ext ha)

/-- The difference class vanishes precisely modulo the submodule and ambient invariants. -/
theorem tateDifferenceMap_ker :
    LinearMap.ker (tateDifferenceMap ρ g W hW hD) =
      W ⊔ LinearMap.ker (ρ g - LinearMap.id) := by
  ext a
  rw [LinearMap.mem_ker, tateDifferenceMap_apply, oneClass_eq_zero_iff, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (ρ g - LinearMap.id : Module.End ℤ A) y = (ρ g - LinearMap.id : Module.End ℤ A) a :=
      congrArg Subtype.val hy
    refine ⟨y, y.2, a - y, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, hy', sub_self]
  · rintro ⟨w, hw, k, hk, rfl⟩
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    rw [LinearMap.mem_ker] at hk
    change (ρ g - LinearMap.id : Module.End ℤ A) w = (ρ g - LinearMap.id : Module.End ℤ A) (w + k)
    rw [map_add, hk, add_zero]

include hD in
/-- The first isomorphism theorem gives the quotient used for local-unit H¹. -/
theorem tateOne_subrepresentation_equiv_quotient
    (hFull : LinearMap.range (ρ g - LinearMap.id) = LinearMap.ker ρ.norm) :
    Nonempty (tateOne (ρ.subrepresentation W hW) g ≃+
      (A ⧸ (W ⊔ LinearMap.ker (ρ g - LinearMap.id)))) := by
  exact ⟨((LinearMap.quotKerEquivOfSurjective _
    (tateDifferenceMap_surjective ρ g W hW hD hFull)).symm.trans
    (Submodule.quotEquivOfEq _ _ (tateDifferenceMap_ker ρ g W hW hD))).toAddEquiv⟩

end Cox.CyclicCohomology
