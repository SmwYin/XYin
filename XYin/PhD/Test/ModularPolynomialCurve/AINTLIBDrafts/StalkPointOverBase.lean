/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.StalkBaseAlgebra
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Actual stalk-spectrum points over geometric base constants

Every point of an arbitrary scheme over a field gives a stalk-spectrum
morphism over the independently defined stalk base algebra. Its appTop
formula and affine extensionality prove the literal triangle. Neither
integrality nor irreducibility is needed. Two clients check the canonical
point and arbitrary spectrum precomposition.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

theorem fromSpecStalk_comp_structureMap (π : X ⟶ Spec (.of k)) (x : X) :
    let _ := π.stalkBaseAlgebra x
    X.fromSpecStalk x ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap k (X.presheaf.stalk x))) := by
  let _ := π.stalkBaseAlgebra x
  have hgerm : (X.fromSpecStalk x).appTop ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom = X.presheaf.germ ⊤ x trivial := by
    rw [Scheme.fromSpecStalk_appTop]
    simp only [homOfLE_refl, op_id, Category.assoc]
    rw [(Spec (X.presheaf.stalk x)).presheaf.map_id, Category.id_comp]
    rw [Iso.inv_hom_id, Category.comp_id]
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom]
  rw [Scheme.Hom.comp_appTop, Category.assoc, hgerm, Scheme.ΓSpecIso_naturality]
  change π.appTop ≫ X.presheaf.germ ⊤ x trivial =
    (Scheme.ΓSpecIso (.of k)).hom ≫ (Scheme.ΓSpecIso (.of k)).inv ≫
      π.appTop ≫ X.presheaf.germ ⊤ x trivial
  rw [Iso.hom_inv_id_assoc]

example (π : X ⟶ Spec (.of k)) (x : X) :
    let _ := π.stalkBaseAlgebra x
    X.fromSpecStalk x ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap k (X.presheaf.stalk x))) :=
  fromSpecStalk_comp_structureMap π x

example (π : X ⟶ Spec (.of k)) (x : X) (R : CommRingCat.{u})
    (f : X.presheaf.stalk x ⟶ R) :
    let _ := π.stalkBaseAlgebra x
    (Spec.map f ≫ X.fromSpecStalk x) ≫ π =
      Spec.map (CommRingCat.ofHom
        (f.hom.comp (algebraMap k (X.presheaf.stalk x)))) := by
  let _ := π.stalkBaseAlgebra x
  rw [Category.assoc, fromSpecStalk_comp_structureMap]
  exact (Spec.map_comp _ _).symm

#print axioms fromSpecStalk_comp_structureMap
#print axioms Scheme.Hom.stalkBaseAlgebra
#print axioms Scheme.fromSpecStalk_appTop
#print axioms Scheme.ΓSpecIso_naturality
#print axioms ext_of_isAffine
#print axioms Spec.map_comp

end AlgebraicGeometry
