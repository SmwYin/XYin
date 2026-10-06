/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite field-valued points have closed image

A point defined over a finite field extension of the base has closed image
on any scheme separated over that base field. The actual over-base triangle
gives a finite composite; separatedness cancels to a finite point map.
No finite type or properness of the whole scheme is required.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
  {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π]

theorem isClosed_image_of_finite_field (e : Spec (.of L) ⟶ X)
    (he : e ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k L))) (x : Spec (.of L)) :
    IsClosed {e x} := by
  have : IsFinite (e ≫ π) := by
    rw [he, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap).mpr inferInstance
  have : IsFinite e := IsFinite.of_comp e π
  have hrange : Set.range e = {e x} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg e (Subsingleton.elim z x))
    · rintro rfl
      exact ⟨x, rfl⟩
  rw [← hrange]
  exact e.isClosedMap.isClosed_range

example (e : Spec (.of k) ⟶ X) (he : e ≫ π = 𝟙 (Spec (.of k))) (x : Spec (.of k)) :
    IsClosed {e x} := by
  apply isClosed_image_of_finite_field π e _ x
  simpa using he

example (x : Spec (.of L)) : IsClosed {x} := by
  exact isClosed_image_of_finite_field
    (Spec.map (CommRingCat.ofHom (algebraMap k L))) (𝟙 _) (by simp) x

#print axioms isClosed_image_of_finite_field
#print axioms IsFinite.of_comp
#print axioms IsFinite.SpecMap_iff
#print axioms RingHom.finite_algebraMap
#print axioms Scheme.Hom.isClosedMap

end AlgebraicGeometry
