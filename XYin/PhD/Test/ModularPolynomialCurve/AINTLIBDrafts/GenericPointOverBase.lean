/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.FunctionFieldBaseAlgebra
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ModularCurves.EllipticCurve.IntegralOverField

/-!
# The actual generic point is over the independent geometric base constants

The canonical generic-stalk point of an integral scheme commutes with its
structure map to the spectrum of any field. The base scalar map is defined
independently by the actual generic germ, structure-map appTop, and ΓSpecIso.
The proof uses the literal fromSpecStalk appTop formula and affine extensionality.

The two examples check the same triangle using the actual geometric base-field
algebra, first for an arbitrary structure map and then for a native elliptic curve.
No properness, smoothness, place-centre existence or place bijection is claimed.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

theorem fromSpecFunctionField_comp_structureMap (π : X ⟶ Spec (.of k)) :
    X.fromSpecStalk (genericPoint X) ≫ π =
      Spec.map (CommRingCat.ofHom π.functionFieldConstants) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have hgeneric : (X.fromSpecStalk (genericPoint X)).appTop ≫
      (Scheme.ΓSpecIso X.functionField).hom = X.germToFunctionField ⊤ := by
    rw [Scheme.fromSpecStalk_appTop]
    simp only [homOfLE_refl, op_id, Category.assoc]
    rw [(Spec (X.presheaf.stalk (genericPoint X))).presheaf.map_id, Category.id_comp]
    change X.germToFunctionField ⊤ ≫ (Scheme.ΓSpecIso X.functionField).inv ≫
      (Scheme.ΓSpecIso X.functionField).hom = X.germToFunctionField ⊤
    rw [Iso.inv_hom_id, Category.comp_id]
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso X.functionField).hom]
  rw [Scheme.Hom.comp_appTop, Category.assoc, hgeneric, Scheme.ΓSpecIso_naturality]
  change π.appTop ≫ X.germToFunctionField ⊤ =
    (Scheme.ΓSpecIso (.of k)).hom ≫ (Scheme.ΓSpecIso (.of k)).inv ≫
      π.appTop ≫ X.germToFunctionField ⊤
  rw [Iso.hom_inv_id_assoc]

example (π : X ⟶ Spec (.of k)) :
    let _ := π.functionFieldBaseAlgebra
    X.fromSpecStalk (genericPoint X) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap k X.functionField)) := by
  let _ := π.functionFieldBaseAlgebra
  exact fromSpecFunctionField_comp_structureMap π

example (E : ModularCurves.EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    E.E.fromSpecStalk (genericPoint E.E) ≫ E.π =
      Spec.map (CommRingCat.ofHom (algebraMap k E.E.functionField)) := by
  let _ := E.π.functionFieldBaseAlgebra
  exact fromSpecFunctionField_comp_structureMap E.π

#print axioms fromSpecFunctionField_comp_structureMap
#print axioms Scheme.Hom.functionFieldConstants
#print axioms Scheme.Hom.functionFieldBaseAlgebra
#print axioms Scheme.fromSpecStalk_appTop
#print axioms Scheme.ΓSpecIso_naturality
#print axioms ext_of_isAffine

end AlgebraicGeometry
