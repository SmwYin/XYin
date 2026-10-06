/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.FiniteFunctionField
public import AINTLIBDrafts.FunctionFieldFormallyUnramified
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Etaleness of the literal native function-field pullback

A finite dominant formally unramified morphism of integral schemes induces
an etale ring homomorphism on their native function fields. The proof uses
the literal pullback's `toAlgebra`, the checked finite-module and generic
stalk APIs, and the existing arbitrary-characteristic field results.
Finite type over the field supplies finite presentation.

The statement needs neither characteristic zero nor an extra scalar tower.
It proves etaleness of the generic field extension; ramification of
valuation rings or places is a separate question. No quotient-specific
specialization, genus, or elliptic-curve-model conclusion is made here.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A finite dominant formally unramified map of integral schemes gives an etale field map. -/
theorem functionFieldMap_etale (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [FormallyUnramified f] : f.functionFieldMap.hom.Etale := by
  let : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
  have : Module.Finite Y.functionField X.functionField := functionFieldMap_finite f
  have : Algebra.FormallyUnramified Y.functionField X.functionField :=
    functionFieldMap_formallyUnramified f
  have : Algebra.IsSeparable Y.functionField X.functionField :=
    Algebra.FormallyUnramified.isSeparable Y.functionField X.functionField
  have : Algebra.FormallyEtale Y.functionField X.functionField :=
    Algebra.FormallyEtale.of_isSeparable Y.functionField X.functionField
  have : Algebra.FinitePresentation Y.functionField X.functionField :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact (show Algebra.Etale Y.functionField X.functionField from ⟨inferInstance, inferInstance⟩)

example (X : Scheme.{u}) [IsIntegral X] : (𝟙 X : X ⟶ X).functionFieldMap.hom.Etale :=
  functionFieldMap_etale (𝟙 X)

#print axioms functionFieldMap_etale
#print axioms functionFieldMap_finite
#print axioms functionFieldMap_formallyUnramified
#print axioms Algebra.FormallyUnramified.isSeparable
#print axioms Algebra.FormallyEtale.of_isSeparable
#print axioms Algebra.FinitePresentation.of_finiteType
#print axioms Module.Finite.finiteType
#print axioms Algebra.EssFiniteType.of_finiteType
#print axioms RingHom.Etale

end AlgebraicGeometry
