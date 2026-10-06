/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.FaithfullyFlatIntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Integral closedness descends along a flat surjective scheme morphism

A flat local stalk map is faithfully flat. The checked algebraic descent
criterion therefore transfers source stalk normality to its image point;
surjectivity supplies all target points. The examples exercise identity and
the general surjective client. No finite, etale or Noetherian premise occurs.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

theorem Flat.isIntegrallyClosed_stalkMap_target (f : X ⟶ Y) [Flat f] (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)] :
    IsIntegrallyClosed (Y.presheaf.stalk (f.base x)) := by
  let _ : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    Flat.stalkMap f x
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
    f.toLRSHom.prop x
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ModularPolynomialCurveTest.AINTLIB.Normality.isIntegrallyClosed_of_faithfullyFlat
    (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)

theorem Flat.isIntegrallyClosed_stalks_of_surjective (f : X ⟶ Y) [Flat f] [Surjective f]
    (hD : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (hN : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (y : Y) :
    IsIntegrallyClosed (Y.presheaf.stalk y) := by
  obtain ⟨x, rfl⟩ := f.surjective y
  have : IsDomain (X.presheaf.stalk x) := hD x
  have : IsIntegrallyClosed (X.presheaf.stalk x) := hN x
  exact Flat.isIntegrallyClosed_stalkMap_target f x

example (X : Scheme.{u}) (x : X) [IsDomain (X.presheaf.stalk x)]
    [IsIntegrallyClosed (X.presheaf.stalk x)] : IsIntegrallyClosed (X.presheaf.stalk x) :=
  Flat.isIntegrallyClosed_stalkMap_target (𝟙 X) x

example (f : X ⟶ Y) [Flat f] [Surjective f]
    (hD : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (hN : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (y : Y) :
    IsIntegrallyClosed (Y.presheaf.stalk y) :=
  Flat.isIntegrallyClosed_stalks_of_surjective f hD hN y

#print axioms Flat.isIntegrallyClosed_stalkMap_target
#print axioms Flat.isIntegrallyClosed_stalks_of_surjective
#print axioms Flat.stalkMap
#print axioms Module.FaithfullyFlat.of_flat_of_isLocalHom
#print axioms ModularPolynomialCurveTest.AINTLIB.Normality.isIntegrallyClosed_of_faithfullyFlat
#print axioms Scheme.Hom.toLRSHom
#print axioms Scheme.Hom.surjective

end AlgebraicGeometry
