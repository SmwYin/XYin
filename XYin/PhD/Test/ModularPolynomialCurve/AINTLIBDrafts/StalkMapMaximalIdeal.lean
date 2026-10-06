/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Maximal ideals under formally unramified stalk maps

For an arbitrary formally unramified, locally finite-type morphism of schemes,
the literal stalk map takes the maximal ideal of the local ring at the image
point to the maximal ideal at the original point. The proof installs the
algebra of that actual ring homomorphism and reuses its genuine local-map,
essentially finite-type, and formally unramified properties.

The theorem has no domain, DVR, finiteness, flatness, Noetherian, or étale
premise. Identity and étale-map examples check its direct API. This module
does not supply quotient wrappers, compute ramification indices, or prove a
genus result.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A formally unramified locally finite-type map preserves maximal ideals on stalks. -/
theorem FormallyUnramified.map_maximalIdeal_stalkMap
    (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f] (x : X) :
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  let : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom
      (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified
      (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  change (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))).map
      (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) = _
  exact Algebra.FormallyUnramified.map_maximalIdeal

example (X : Scheme.{u}) (x : X) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk ((𝟙 X : X ⟶ X).base x))).map
        ((𝟙 X : X ⟶ X).stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
  FormallyUnramified.map_maximalIdeal_stalkMap (𝟙 X) x

example (f : X ⟶ Y) [Etale f] (x : X) :
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
  FormallyUnramified.map_maximalIdeal_stalkMap f x

#print axioms FormallyUnramified.map_maximalIdeal_stalkMap
#print axioms Algebra.FormallyUnramified.map_maximalIdeal
#print axioms Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal
#print axioms FormallyUnramified.stalkMap
#print axioms LocallyOfFiniteType.stalkMap
#print axioms RingHom.formallyUnramified_algebraMap
#print axioms RingHom.essFiniteType_algebraMap
#print axioms RingHom.algebraMap_toAlgebra

end AlgebraicGeometry
