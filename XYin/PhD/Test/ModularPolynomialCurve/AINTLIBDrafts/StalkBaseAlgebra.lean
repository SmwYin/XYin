/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.FunctionFieldBaseAlgebra
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Geometric constants in an integral scheme's actual stalk

The stalk algebra is specified independently by the structure morphism and
the actual top germ. Compatibility with the existing native stalk-to-function-
field algebra follows from germ naturality, giving its scalar tower. The
examples verify the literal constant maps in both the stalk and function field.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- Base constants in an actual stalk, independently of any fraction-field presentation. -/
@[instance_reducible]
noncomputable def Scheme.Hom.stalkBaseAlgebra (π : X ⟶ Spec (.of k)) (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp
    (π.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)).toAlgebra

theorem isScalarTower_stalkBaseAlgebra (π : X ⟶ Spec (.of k)) (x : X) :
    let _ := π.stalkBaseAlgebra x
    let _ := π.functionFieldBaseAlgebra
    IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  let _ := π.stalkBaseAlgebra x
  let _ := π.functionFieldBaseAlgebra
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change X.germToFunctionField ⊤
      (π.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)) =
    algebraMap (X.presheaf.stalk x) X.functionField
      ((X.presheaf.germ ⊤ x trivial).hom
        (π.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)))
  exact (X.algebraMap_germ_eq_germToFunctionField (U := ⊤) (x := x) trivial _).symm

example (π : X ⟶ Spec (.of k)) (x : X) (c : k) :
    let _ := π.stalkBaseAlgebra x
    algebraMap k (X.presheaf.stalk x) c =
      (X.presheaf.germ ⊤ x trivial).hom
        (π.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)) := rfl

example (π : X ⟶ Spec (.of k)) (x : X) (c : k) :
    let _ := π.stalkBaseAlgebra x
    let _ := π.functionFieldBaseAlgebra
    algebraMap (X.presheaf.stalk x) X.functionField
        (algebraMap k (X.presheaf.stalk x) c) = π.functionFieldConstants c := by
  let _ := π.stalkBaseAlgebra x
  let _ := π.functionFieldBaseAlgebra
  let _ := isScalarTower_stalkBaseAlgebra π x
  exact (IsScalarTower.algebraMap_apply k (X.presheaf.stalk x) X.functionField c).symm

#print axioms Scheme.Hom.stalkBaseAlgebra
#print axioms isScalarTower_stalkBaseAlgebra
#print axioms Scheme.Hom.functionFieldBaseAlgebra
#print axioms Scheme.algebraMap_germ_eq_germToFunctionField
#print axioms stalkFunctionFieldAlgebra
#print axioms IsScalarTower.algebraMap_apply

end AlgebraicGeometry
