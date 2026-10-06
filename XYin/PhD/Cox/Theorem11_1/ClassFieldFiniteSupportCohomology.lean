/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCohomology

/-! # The finite orbit calculation in Janusz V.2.1

An arbitrary finitely supported permutation vector meets only finitely many orbits.
Each orbit is finite when the acting group is finite. We use the existing transitive
finite-orbit calculation separately on those orbits, then add their actual extensions.
No finiteness of the whole prime set or transitivity of its full action is assumed.
-/

noncomputable section
namespace Cox.CyclicCohomology
variable {G X : Type*} [Group G] [MulAction G X]

/-- Restrict a finite exponent vector to one actual orbit. -/
def orbitRestriction (c : MulAction.orbitRel.Quotient G X) :
    (X →₀ ℤ) →ₗ[ℤ] (c.orbit →₀ ℤ) :=
  (Finsupp.subtypeDomainAddMonoidHom (p := fun x ↦ x ∈ c.orbit)).toIntLinearMap

/-- Extend a vector on one actual orbit by zero outside that orbit. -/
def orbitInclusion (c : MulAction.orbitRel.Quotient G X) :
    (c.orbit →₀ ℤ) →ₗ[ℤ] (X →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ Subtype.val

/-- Restriction to an orbit commutes with every permutation in the action. -/
theorem orbitRestriction_equivariant (c : MulAction.orbitRel.Quotient G X)
    (γ : G) (f : X →₀ ℤ) :
    orbitRestriction c (Representation.ofMulAction ℤ G X γ f) =
      Representation.ofMulAction ℤ G c.orbit γ (orbitRestriction c f) := by
  ext x
  change (Representation.ofMulAction ℤ G X γ f) x =
    (Representation.ofMulAction ℤ G c.orbit γ (f.subtypeDomain (· ∈ c.orbit))) x
  rw [Representation.ofMulAction_apply, Representation.ofMulAction_apply]
  rfl

/-- Extension by zero along an invariant orbit is equivariant. -/
theorem orbitInclusion_equivariant (c : MulAction.orbitRel.Quotient G X)
    (γ : G) (f : c.orbit →₀ ℤ) :
    orbitInclusion c (Representation.ofMulAction ℤ G c.orbit γ f) =
      Representation.ofMulAction ℤ G X γ (orbitInclusion c f) := by
  simp only [orbitInclusion, Representation.ofMulAction_def, Finsupp.lmapDomain_apply,
    ← Finsupp.mapDomain_comp]
  rfl

open scoped Classical in
/-- The finite set of orbits actually met by a finite exponent vector. -/
def orbitSupport (f : X →₀ ℤ) : Finset (MulAction.orbitRel.Quotient G X) :=
  f.support.image Quotient.mk''

/-- Restricting to an orbit and extending by zero keeps exactly the coordinates in that orbit. -/
theorem orbitInclusion_restriction_apply (c : MulAction.orbitRel.Quotient G X) (f : X →₀ ℤ)
    (x : X) [Decidable (x ∈ c.orbit)] :
    orbitInclusion c (orbitRestriction c f) x = if x ∈ c.orbit then f x else 0 := by
  split_ifs with hx
  · change Finsupp.mapDomain Subtype.val (f.subtypeDomain (· ∈ c.orbit))
      ((⟨x, hx⟩ : c.orbit) : X) = f x
    rw [Finsupp.mapDomain_apply Subtype.val_injective, Finsupp.subtypeDomain_apply]
  · apply Finsupp.mapDomain_notin_range
    rintro ⟨y, rfl⟩
    exact hx y.2

/-- A finite exponent vector is the sum of its actual orbit restrictions extended by zero. -/
theorem orbit_reconstruction (f : X →₀ ℤ) :
    ∑ c ∈ orbitSupport (G := G) f, orbitInclusion c (orbitRestriction c f) = f := by
  classical
  ext x
  rw [Finsupp.finsetSum_apply]
  simp_rw [orbitInclusion_restriction_apply, MulAction.orbitRel.Quotient.mem_orbit]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · symm
    by_contra hfx
    exact h (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hfx))

/-- Every orbit is finite; the full set X is permitted to be infinite. -/
theorem finite_orbit [Finite G] (c : MulAction.orbitRel.Quotient G X) : c.orbit.Finite := by
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out c Quotient.out_eq']
  exact Finite.finite_mulAction_orbit _

variable [hFinG : Fintype G]

/-- The representation norm commutes with actual orbit restriction. -/
theorem orbitRestriction_norm (c : MulAction.orbitRel.Quotient G X) (f : X →₀ ℤ) :
    orbitRestriction c ((Representation.ofMulAction ℤ G X).norm f) =
      (Representation.ofMulAction ℤ G c.orbit).norm (orbitRestriction c f) := by
  rw [Representation.norm, Representation.norm, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun γ _ => orbitRestriction_equivariant c γ f

/-- A norm-zero vector restricts to a norm-zero vector on every orbit. -/
theorem orbitRestriction_norm_zero (c : MulAction.orbitRel.Quotient G X)
    (f : X →₀ ℤ) (hf : (Representation.ofMulAction ℤ G X).norm f = 0) :
    (Representation.ofMulAction ℤ G c.orbit).norm (orbitRestriction c f) = 0 := by
  rw [← orbitRestriction_norm, hf, map_zero]

/-- On one finite transitive orbit the existing Tate H1 calculation gives an actual difference. -/
theorem orbit_difference_of_norm_zero (c : MulAction.orbitRel.Quotient G X)
    (g : G) (hg : ∀ γ : G, γ ∈ Subgroup.zpowers g) (f : c.orbit →₀ ℤ)
    (hf : (Representation.ofMulAction ℤ G c.orbit).norm f = 0) :
    ∃ y : c.orbit →₀ ℤ, Representation.ofMulAction ℤ G c.orbit g y - y = f := by
  obtain ⟨x, hx⟩ := c.nonempty_orbit
  haveI := tateOne_permutation_subsingleton g c.orbit ⟨x, hx⟩ hg
  have h0 : (Submodule.Quotient.mk ⟨f, hf⟩ :
      tateOne (Representation.ofMulAction ℤ G c.orbit) g) = 0 := Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp h0
  exact ⟨y, hy⟩

/-- Sum the orbitwise differences over the finite set of orbits met by f. -/
theorem finsupp_difference_of_norm_zero (g : G) (hg : ∀ γ : G, γ ∈ Subgroup.zpowers g)
    (f : X →₀ ℤ) (hf : (Representation.ofMulAction ℤ G X).norm f = 0) :
    ∃ y : X →₀ ℤ, Representation.ofMulAction ℤ G X g y - y = f := by
  classical
  have hc (c : MulAction.orbitRel.Quotient G X) : ∃ y : c.orbit →₀ ℤ,
      Representation.ofMulAction ℤ G c.orbit g y - y = orbitRestriction c f :=
    orbit_difference_of_norm_zero c g hg _ (orbitRestriction_norm_zero c f hf)
  choose y hy using hc
  refine ⟨∑ c ∈ orbitSupport (G := G) f, orbitInclusion c (y c), ?_⟩
  rw [map_sum, ← Finset.sum_sub_distrib]
  conv_rhs => rw [← orbit_reconstruction (G := G) f]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← orbitInclusion_equivariant, ← map_sub, hy]

/-- The first Tate group of an arbitrary finitely supported integral permutation module vanishes. -/
theorem tateOne_finsupp_subsingleton (g : G) (hg : ∀ γ : G, γ ∈ Subgroup.zpowers g) :
    Subsingleton (tateOne (Representation.ofMulAction ℤ G X) g) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  rintro ⟨f, hf⟩ -
  obtain ⟨y, hy⟩ := finsupp_difference_of_norm_zero g hg f (LinearMap.mem_ker.mp hf)
  exact Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨y, hy⟩)

end Cox.CyclicCohomology
