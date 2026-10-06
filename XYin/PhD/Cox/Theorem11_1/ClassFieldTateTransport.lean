/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCohomologyDefs
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The transport in Janusz V.1.1

An equivariant additive equivalence commutes with the norm and the generator
difference, and consequently induces equivalences of the two Tate quotients.
The coefficient rings may differ: only the underlying additive groups matter.
-/

noncomputable section
namespace Cox.CyclicCohomology
variable {A B R S : Type*} [AddCommGroup A] [AddCommGroup B]
variable [CommRing R] [CommRing S] [Module R A] [Module S B]

/-- Commuting additive equivalences identify the indicated kernel/range quotients. -/
theorem kernelRangeQuotient_equiv (f p : A →ₗ[R] A) (g q : B →ₗ[S] B) (e : A ≃+ B)
    (hf : ∀ x, e (f x) = g (e x)) (hp : ∀ x, e (p x) = q (e x)) :
    Nonempty ((f.ker ⧸ p.range.comap f.ker.subtype) ≃+
      (g.ker ⧸ q.range.comap g.ker.subtype)) := by
  have hker : ∀ x, x ∈ LinearMap.ker f ↔ e x ∈ LinearMap.ker g := fun x => by
    simp only [LinearMap.mem_ker]
    rw [← hf, map_eq_zero_iff e e.injective]
  let ek : LinearMap.ker f ≃+ LinearMap.ker g :=
    { toFun := fun x => ⟨e x, (hker x).mp x.2⟩
      invFun := fun y => ⟨e.symm y, (hker _).mpr (by simp)⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp
      map_add' := fun x y => by ext; simp }
  refine ⟨QuotientAddGroup.congr _ _ ek ?_⟩
  ext y
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_comap,
    LinearMap.mem_range, Submodule.coe_subtype]
  constructor
  · rintro ⟨x, ⟨a, ha⟩, rfl⟩
    exact ⟨e a, by rw [← hp, ha]; rfl⟩
  · rintro ⟨b, hb⟩
    refine ⟨ek.symm y, ⟨e.symm b, ?_⟩, by simp⟩
    apply e.injective
    rw [hp, e.apply_symm_apply, hb]
    change (y : B) = e (e.symm y)
    rw [e.apply_symm_apply]

variable {G : Type*} [Group G] [Fintype G]

/-- An additive equivariant equivalence commutes with the actual finite norm sum. -/
theorem addEquiv_norm (ρ : Representation R G A) (τ : Representation S G B) (e : A ≃+ B)
    (h : ∀ γ x, e (ρ γ x) = τ γ (e x)) (x : A) :
    e (ρ.norm x) = τ.norm (e x) := by
  rw [Representation.norm, Representation.norm, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun γ _ => h γ x

omit [Fintype G] in
/-- Equivariance also preserves the actual generator difference. -/
theorem addEquiv_difference (ρ : Representation R G A) (τ : Representation S G B) (e : A ≃+ B)
    (h : ∀ γ x, e (ρ γ x) = τ γ (e x)) (γ : G) (x : A) :
    e ((ρ γ - (LinearMap.id : A →ₗ[R] A)) x) =
      (τ γ - (LinearMap.id : B →ₗ[S] B)) (e x) := by
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, h]

end Cox.CyclicCohomology
