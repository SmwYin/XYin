/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.ForMathlib.DominantFunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Formal unramifiedness of the native generic-stalk pullback

For a dominant map between irreducible schemes, the native
`functionFieldMap` is the generic-point stalk map after the canonical
`eqToHom` identifying the target generic stalk. Its formal unramifiedness
therefore follows directly from the existing stalk theorem and invariance
under composition with an isomorphism.

Only irreducibility is needed here. The native `functionField` denotes the
generic stalk, which acquires a field structure for an integral scheme.
This result makes no reducedness, integrality, finiteness, or scalar-tower
assumption and proves no separability or etaleness conclusion by itself.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A formally unramified dominant map induces a formally unramified native generic-stalk map. -/
theorem functionFieldMap_formallyUnramified (f : X ⟶ Y) [FormallyUnramified f]
    [IsDominant f] [IrreducibleSpace X] [IrreducibleSpace Y] :
    f.functionFieldMap.hom.FormallyUnramified := by
  unfold Scheme.Hom.functionFieldMap
  rw [CommRingCat.hom_comp]
  exact (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso _ _).mpr
    (FormallyUnramified.stalkMap f (genericPoint X))

example (X : Scheme.{u}) [IrreducibleSpace X] :
    (𝟙 X : X ⟶ X).functionFieldMap.hom.FormallyUnramified :=
  functionFieldMap_formallyUnramified (𝟙 X)

#print axioms functionFieldMap_formallyUnramified
#print axioms Scheme.Hom.functionFieldMap
#print axioms genericPoint_eq_of_isDominant
#print axioms FormallyUnramified.stalkMap
#print axioms RingHom.FormallyUnramified.respectsIso
#print axioms RingHom.RespectsIso.cancel_left_isIso
#print axioms HasRingHomProperty.stalkMap

end AlgebraicGeometry
