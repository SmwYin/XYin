/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.ForMathlib.DominantFunctionField

/-!
# Naturality of geometric function-field constants

For an integral scheme over `Spec k`, the structural map defines a constant
ring homomorphism by `ΓSpecIso.inv → appTop → generic top germ`, independently
of any ring equivalence. A dominant morphism between integral schemes pulls
back these constants to those of the composite structure map.

The proof uses the actual native function-field germ formula and `appTop`
composition. A uniquely named local instance witnesses the nonempty top open
by the genuine generic point, without adding a premise or a global instance.
The result assumes only an arbitrary field, integral schemes, and dominance;
no finiteness, model, genus, or scalar-equivalence hypothesis is introduced.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

local instance constantsNaturalityTopNonempty (T : Scheme.{u}) [IsIntegral T] :
    Nonempty (⊤ : T.Opens) := ⟨⟨genericPoint T, trivial⟩⟩

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The structural map defines constants before any function-field equivalence. -/
noncomputable def Scheme.Hom.functionFieldConstants (π : X ⟶ Spec (.of k)) :
    k →+* X.functionField :=
  (X.germToFunctionField ⊤).hom.comp
    (π.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)

/-- The actual dominant pullback preserves the independently defined constants. -/
theorem functionFieldMap_comp_functionFieldConstants
    (f : X ⟶ Y) [IsDominant f] (π : Y ⟶ Spec (.of k)) :
    f.functionFieldMap.hom.comp π.functionFieldConstants =
      (f ≫ π).functionFieldConstants := by
  ext r
  change f.functionFieldMap
      (Y.germToFunctionField ⊤ (π.appTop ((Scheme.ΓSpecIso (.of k)).inv r))) =
    X.germToFunctionField ⊤ ((f ≫ π).appTop ((Scheme.ΓSpecIso (.of k)).inv r))
  rw [functionFieldMap_germToFunctionField f ⊤, Scheme.Hom.comp_appTop]
  rfl

example (π : X ⟶ Spec (.of k)) (r : k) :
    π.functionFieldConstants r =
      X.germToFunctionField ⊤ (π.appTop ((Scheme.ΓSpecIso (.of k)).inv r)) := rfl

example (π : X ⟶ Spec (.of k)) (r : k) :
    (𝟙 X : X ⟶ X).functionFieldMap
        (X.germToFunctionField ⊤ (π.appTop ((Scheme.ΓSpecIso (.of k)).inv r))) =
      X.germToFunctionField ⊤ (π.appTop ((Scheme.ΓSpecIso (.of k)).inv r)) := by
  rw [functionFieldMap_id]
  rfl

#print axioms constantsNaturalityTopNonempty
#print axioms Scheme.Hom.functionFieldConstants
#print axioms functionFieldMap_comp_functionFieldConstants
#print axioms Scheme.Hom.functionFieldMap
#print axioms functionFieldMap_germToFunctionField
#print axioms functionFieldMap_comp_germToFunctionField
#print axioms functionFieldMap_id
#print axioms Scheme.Hom.comp_appTop
#print axioms Scheme.ΓSpecIso

end AlgebraicGeometry
