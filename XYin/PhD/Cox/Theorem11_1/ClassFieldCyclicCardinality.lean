/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldHexagon

/-! # The punctured cardinal calculation of Janusz V.4.2

Only kernels, cokernels, and the four end groups are finite. The three middle groups
in the two rows may be infinite.
-/

noncomputable section
namespace Cox.CyclicCohomology

section Composition
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- Janusz V.4.2's image/kernel index identity for a finite-index subgroup. -/
theorem index_eq_map_mul_ker (f : A →+ B) (H : AddSubgroup A) [H.FiniteIndex] :
    H.index = (H.map f).relIndex f.range * (H ⊓ f.ker).relIndex f.ker := by
  have hsup : H.relIndex (H ⊔ f.ker) = H.relIndex f.ker := AddSubgroup.relIndex_sup_left _ _
  rw [AddSubgroup.inf_relIndex_right, ← hsup, mul_comm,
    ← AddSubgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ f.ker)]
  congr 1
  have h1 : ((H.map f).addSubgroupOf f.range).comap f.rangeRestrict = H ⊔ f.ker := by
    rw [← AddSubgroup.comap_map_eq]
    ext a
    simp [AddSubgroup.mem_addSubgroupOf]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ f.rangeRestrict_surjective,
    h1]

/-- Finite kernels stay finite under composition, without finite ambient groups. -/
theorem ker_comp_finite (f : A →+ B) (g : B →+ C) [Finite f.ker] [Finite g.ker] :
    Finite (g.comp f).ker := by
  let i : f.ker →+ (g.comp f).ker := AddSubgroup.inclusion fun a ha => by
    rw [AddMonoidHom.mem_ker] at ha ⊢
    rw [AddMonoidHom.comp_apply, ha, map_zero]
  let r : (g.comp f).ker →+ g.ker :=
    (f.comp (g.comp f).ker.subtype).codRestrict g.ker fun a => a.2
  refine finite_of_exact i r ?_
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    rw [AddMonoidHom.mem_ker]
    apply Subtype.ext
    exact b.2
  · intro ha
    rw [AddMonoidHom.mem_ker] at ha
    exact ⟨⟨a.1, congrArg Subtype.val ha⟩, rfl⟩

/-- Two maps with finite-index images have a composite with finite-index image. -/
theorem range_comp_finiteIndex (f : A →+ B) (g : B →+ C)
    [f.range.FiniteIndex] [g.range.FiniteIndex] : (g.comp f).range.FiniteIndex := by
  refine ⟨?_⟩
  rw [AddMonoidHom.range_comp,
    ← AddSubgroup.relIndex_mul_index (AddSubgroup.map_le_range g f.range)]
  refine mul_ne_zero ?_ AddSubgroup.FiniteIndex.index_ne_zero
  have hdvd := AddSubgroup.index_map_dvd (H := f.range) g.rangeRestrict_surjective
  have hmap : f.range.map g.rangeRestrict = (f.range.map g).addSubgroupOf g.range := by
    ext b
    simp [AddSubgroup.mem_addSubgroupOf, Subtype.ext_iff]
  rw [hmap] at hdvd
  intro h
  change ((f.range.map g).addSubgroupOf g.range).index = 0 at h
  rw [h] at hdvd
  exact AddSubgroup.FiniteIndex.index_ne_zero (Nat.eq_zero_of_zero_dvd hdvd)

/-- Restricting f to the composite kernel gives kernel ker f and image ker g∩im f. -/
theorem card_ker_comp (f : A →+ B) (g : B →+ C) [Finite f.ker] [Finite g.ker] :
    Nat.card (g.comp f).ker = Nat.card f.ker * Nat.card ↥(g.ker ⊓ f.range) := by
  haveI := ker_comp_finite f g
  let r : (g.comp f).ker →+ B := f.comp (g.comp f).ker.subtype
  have hrange : r.range = g.ker ⊓ f.range := by
    ext b
    constructor
    · rintro ⟨⟨a, ha⟩, rfl⟩
      exact ⟨ha, a, rfl⟩
    · rintro ⟨hb, a, rfl⟩
      exact ⟨⟨a, hb⟩, rfl⟩
  have hker : Nat.card r.ker = Nat.card f.ker := Nat.card_congr
    { toFun := fun a => ⟨a.1.1, a.2⟩
      invFun := fun b => ⟨⟨b.1, by
        rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddMonoidHom.mem_ker.mp b.2,
          map_zero]⟩, b.2⟩
      left_inv := fun a => rfl
      right_inv := fun b => rfl }
  rw [card_eq_ker_mul_range r, hker, hrange]

/-- The image of the composite has its relative index inside im g. -/
theorem index_range_comp (f : A →+ B) (g : B →+ C) :
    (g.comp f).range.index = (f.range.map g).relIndex g.range * g.range.index := by
  rw [AddMonoidHom.range_comp, AddSubgroup.relIndex_mul_index (AddSubgroup.map_le_range g f.range)]

/-- Cleared-denominator multiplicativity of cokernel-cardinality/kernel-cardinality. -/
theorem composition_index_card (f : A →+ B) (g : B →+ C)
    [Finite f.ker] [Finite g.ker] [f.range.FiniteIndex] [g.range.FiniteIndex] :
    (g.comp f).range.index * Nat.card f.ker * Nat.card g.ker =
      f.range.index * g.range.index * Nat.card (g.comp f).ker := by
  have h1 := index_eq_map_mul_ker g f.range
  have h2 := index_range_comp f g
  have h3 := card_ker_comp f g
  have h4 : Nat.card g.ker = (f.range ⊓ g.ker).relIndex g.ker * Nat.card ↥(g.ker ⊓ f.range) := by
    rw [← AddSubgroup.card_mul_index ((f.range ⊓ g.ker).addSubgroupOf g.ker), mul_comm,
      Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe
        (inf_le_right : f.range ⊓ g.ker ≤ g.ker)).toEquiv, inf_comm]
    rfl
  rw [h2, h1, h3, h4]
  ring
end Composition

section Punctured
variable {J₁ A₀ B₀ J₀ A₁ V₁ I₀ V₀ : Type*}
variable [AddCommGroup J₁] [AddCommGroup A₀] [AddCommGroup B₀]
variable [AddCommGroup J₀] [AddCommGroup A₁] [AddCommGroup V₁]
variable [AddCommGroup I₀] [AddCommGroup V₀]
variable (u : J₁ →+ A₀) (i : A₀ →+ B₀) (α : B₀ →+ J₀) (δ : J₀ →+ A₁)
variable (x : V₁ →+ J₀) (β : J₀ →+ I₀) (y : I₀ →+ V₀) (z : V₀ →+ J₁)
variable (hu : Function.Injective u) (hδ : Function.Surjective δ)
variable (hx : Function.Injective x) (hz : Function.Surjective z)
variable (hui : u.range = i.ker) (hiα : i.range = α.ker) (hαδ : α.range = δ.ker)
variable (hxβ : x.range = β.ker) (hβy : β.range = y.ker) (hyz : y.range = z.ker)

include hu in
/-- The first connecting group is finite because it injects into A₀. -/
theorem punctured_common_finite [Finite A₀] : Finite J₁ := by
  exact Finite.of_injective u hu

include hiα in
/-- First-row exactness expresses the finite kernel of α as an image of A₀. -/
theorem punctured_alpha_kernel_finite [Finite A₀] : Finite α.ker := by
  haveI : Finite i.range := (Set.finite_range i).to_subtype
  exact hiα ▸ this

include hδ hαδ in
/-- First-row exactness and the onto map δ identify coker α with A₁. -/
theorem punctured_alpha_cokernel_card [Finite A₁] : α.range.index = Nat.card A₁ := by
  rw [hαδ, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hδ, AddSubgroup.card_top]

include hu hui hiα in
/-- The kernel/image count at A₀ supplies the first-row cardinal product. -/
theorem punctured_alpha_kernel_card [Finite A₀] :
    Nat.card α.ker * Nat.card J₁ = Nat.card A₀ := by
  rw [card_eq_ker_mul_range i, ← hui, ← hiα, mul_comm,
    Nat.card_congr (AddMonoidHom.ofInjective hu).toEquiv]

include hxβ in
/-- Second-row exactness identifies ker β with V₁, hence it is finite. -/
theorem punctured_beta_kernel_finite [Finite V₁] : Finite β.ker := by
  haveI : Finite x.range := (Set.finite_range x).to_subtype
  exact hxβ ▸ this

include hx hxβ in
/-- Injectivity of x gives the second-row kernel cardinal. -/
theorem punctured_beta_kernel_card [Finite V₁] : Nat.card β.ker = Nat.card V₁ := by
  rw [← hxβ]
  exact (Nat.card_congr (AddMonoidHom.ofInjective hx).toEquiv).symm

include hβy in
/-- The finite last term V₀ gives a finite cokernel for β. -/
theorem punctured_beta_cokernel_finite [Finite V₀] : β.range.FiniteIndex := by
  rw [hβy]
  exact ⟨by rw [AddSubgroup.index_ker]; exact Nat.card_pos.ne'⟩

include hz hβy hyz in
/-- Counting the last two maps in the second row supplies its cardinal product. -/
theorem punctured_beta_cokernel_card [Finite V₀] :
    β.range.index * Nat.card J₁ = Nat.card V₀ := by
  rw [hβy, AddSubgroup.index_ker, hyz, card_eq_ker_mul_range z, AddMonoidHom.range_eq_top.mpr hz,
    AddSubgroup.card_top]

include hiα hxβ in
/-- Both finite row kernels make the kernel of β∘α finite. -/
theorem punctured_composite_kernel_finite [Finite A₀] [Finite V₁] :
    Finite (β.comp α).ker := by
  haveI := punctured_alpha_kernel_finite i α hiα
  haveI := punctured_beta_kernel_finite x β hxβ
  exact ker_comp_finite α β

include hδ hαδ hβy in
/-- Both finite row cokernels make the composite cokernel finite. -/
theorem punctured_composite_cokernel_finite [Finite A₁] [Finite V₀] :
    (β.comp α).range.FiniteIndex := by
  haveI : α.range.FiniteIndex :=
    ⟨by rw [punctured_alpha_cokernel_card α δ hδ hαδ]; exact Nat.card_pos.ne'⟩
  haveI := punctured_beta_cokernel_finite β y hβy
  exact range_comp_finiteIndex α β

include hu hδ hx hz hui hiα hαδ hxβ hβy hyz in
/-- Janusz V.4.2's cancellation across the shared J₀, with no finiteness of B₀,J₀,I₀. -/
theorem punctured_index_card [Finite A₀] [Finite A₁] [Finite V₁] [Finite V₀] :
    (β.comp α).range.index * Nat.card A₀ * Nat.card V₁ =
      Nat.card (β.comp α).ker * Nat.card A₁ * Nat.card V₀ := by
  haveI := punctured_common_finite u hu
  haveI := punctured_alpha_kernel_finite i α hiα
  haveI := punctured_beta_kernel_finite x β hxβ
  haveI : α.range.FiniteIndex :=
    ⟨by rw [punctured_alpha_cokernel_card α δ hδ hαδ]; exact Nat.card_pos.ne'⟩
  haveI := punctured_beta_cokernel_finite β y hβy
  have hc := composition_index_card α β
  rw [← punctured_alpha_kernel_card u i α hu hui hiα, ← punctured_beta_kernel_card x β hx hxβ,
    ← punctured_alpha_cokernel_card α δ hδ hαδ, ← punctured_beta_cokernel_card β y z hz hβy hyz]
  calc (β.comp α).range.index * (Nat.card α.ker * Nat.card J₁) * Nat.card β.ker
      = (β.comp α).range.index * Nat.card α.ker * Nat.card β.ker * Nat.card J₁ := by ring
    _ = α.range.index * β.range.index * Nat.card (β.comp α).ker * Nat.card J₁ := by rw [hc]
    _ = Nat.card (β.comp α).ker * α.range.index * (β.range.index * Nat.card J₁) := by ring
end Punctured
end Cox.CyclicCohomology
