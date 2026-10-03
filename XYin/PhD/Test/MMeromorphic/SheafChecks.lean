import XYin.PhD.Test.MMeromorphic.Reference.ComplexPlane

/-!
# Checks on the cited sheaf construction

The reference development uses stalkwise regular denominators, as in Stacks 01X1.
This file checks its general field criterion, its concrete complex-plane instance, and
the holomorphic-to-meromorphic map. A comparison isomorphism with codiscrete classes
is a separate theorem, not a definitional identification.
-/

open CategoryTheory Opposite AlgebraicGeometry
open TopologicalSpace

namespace MMeromorphicTest.Sheaf

example (X : LocallyRingedSpace) [ConnectedSpace X] [LocallyConnectedSpace X]
    [LocallyRingedSpace.HasDomainStalks X] [LocallyRingedSpace.UniqueContinuation X] :
    IsField X.meromorphicGlobalSections :=
  LocallyRingedSpace.isField_meromorphicGlobalSections_of_uniqueContinuation X

/-- The cited theorem really yields a field structure, not just an informal assertion. -/
noncomputable abbrev complexPlaneField :
    Field MeromorphicFunction.holomorphicLocallyRingedSpace.meromorphicGlobalSections :=
  MeromorphicFunction.isField_meromorphicGlobalSections_holomorphicLocallyRingedSpace.toField

/-- The natural map from holomorphic global sections to meromorphic global sections. -/
noncomputable def holomorphicToMeromorphic :
    MeromorphicFunction.holomorphicLocallyRingedSpace.presheaf.obj (op ⊤) →+*
      MeromorphicFunction.holomorphicLocallyRingedSpace.meromorphicGlobalSections := by
  let X := MeromorphicFunction.holomorphicLocallyRingedSpace
  exact ((X.toRingedSpace.toMeromorphicPresheaf ≫
    toSheafify (Opens.grothendieckTopology X.toTopCat) X.meromorphicPresheaf).app
      (op ⊤)).hom

example : holomorphicToMeromorphic 1 = 1 := map_one _

example (a b : MeromorphicFunction.holomorphicLocallyRingedSpace.presheaf.obj (op ⊤)) :
    holomorphicToMeromorphic (a + b) =
      holomorphicToMeromorphic a + holomorphicToMeromorphic b := map_add _ _ _

example (a b : MeromorphicFunction.holomorphicLocallyRingedSpace.presheaf.obj (op ⊤)) :
    holomorphicToMeromorphic (a * b) =
      holomorphicToMeromorphic a * holomorphicToMeromorphic b := map_mul _ _ _

#print axioms LocallyRingedSpace.isField_meromorphicGlobalSections_of_uniqueContinuation
#print axioms complexPlaneField
#print axioms holomorphicToMeromorphic

end MMeromorphicTest.Sheaf
