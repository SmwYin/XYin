/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.FunctionFieldConstantsNaturality

/-!
# Geometric base-field algebras and dominant pullback

The base-field algebra on an integral scheme's function field comes from
its actual structure map and generic germ. A dominant map gives a compatible
scalar tower and a base-field algebra homomorphism whose underlying ring
map is exactly the native function-field map. The source structure map is
the actual composite with the given target structure map.

No finite, flat, Noetherian, model or genus assumption is needed. The examples
check the literal scalar map and underlying homomorphism by `rfl`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The base-field algebra is specified by the structure map and the actual generic germ. -/
@[instance_reducible]
noncomputable def Scheme.Hom.functionFieldBaseAlgebra (π : X ⟶ Spec (.of k)) :
    Algebra k X.functionField := π.functionFieldConstants.toAlgebra

/-- The actual dominant function-field map respects the structure-map scalar tower. -/
theorem isScalarTower_functionFieldBaseAlgebra (f : X ⟶ Y) [IsDominant f]
    (π : Y ⟶ Spec (.of k)) :
    let _ := π.functionFieldBaseAlgebra
    let _ := (f ≫ π).functionFieldBaseAlgebra
    let _ := functionFieldAlgebra f
    IsScalarTower k Y.functionField X.functionField := by
  let _ := π.functionFieldBaseAlgebra
  let _ := (f ≫ π).functionFieldBaseAlgebra
  let _ := functionFieldAlgebra f
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (congrArg (fun g : k →+* X.functionField ↦ g r)
    (functionFieldMap_comp_functionFieldConstants f π)).symm

/-- Dominant pullback as a base-field algebra hom, using independently specified scalars. -/
noncomputable def Scheme.Hom.functionFieldBaseAlgHom (f : X ⟶ Y) [IsDominant f]
    (π : Y ⟶ Spec (.of k)) :
    let _ := π.functionFieldBaseAlgebra
    let _ := (f ≫ π).functionFieldBaseAlgebra
    Y.functionField →ₐ[k] X.functionField :=
  let _ := π.functionFieldBaseAlgebra
  let _ := (f ≫ π).functionFieldBaseAlgebra
  { f.functionFieldMap.hom with
    commutes' := fun r ↦ congrArg (fun g : k →+* X.functionField ↦ g r)
      (functionFieldMap_comp_functionFieldConstants f π) }

example (f : X ⟶ Y) [IsDominant f] (π : Y ⟶ Spec (.of k)) :
    let _ := π.functionFieldBaseAlgebra
    let _ := (f ≫ π).functionFieldBaseAlgebra
    (f.functionFieldBaseAlgHom π).toRingHom = f.functionFieldMap.hom := rfl

example (π : X ⟶ Spec (.of k)) (r : k) :
    let _ := π.functionFieldBaseAlgebra
    algebraMap k X.functionField r = π.functionFieldConstants r := rfl

#print axioms Scheme.Hom.functionFieldBaseAlgebra
#print axioms isScalarTower_functionFieldBaseAlgebra
#print axioms Scheme.Hom.functionFieldBaseAlgHom
#print axioms Scheme.Hom.functionFieldConstants
#print axioms functionFieldMap_comp_functionFieldConstants
#print axioms functionFieldAlgebra
#print axioms IsScalarTower.of_algebraMap_eq

end AlgebraicGeometry
