/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.ForMathlib.DominantFunctionField
public import Mathlib.AlgebraicGeometry.FunctionField
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientIntegral

/-!
# Literal stalk and function-field pullback square

For a dominant map of irreducible schemes, the canonical stalk-to-generic-
stalk algebra maps commute with the literal native function-field pullback
and actual stalk map at every source point. The proof uses only actual germs
and their pullback and specialization formulas.

No field, integrality, finite type, closed-point, normality or DVR hypothesis
is required by the generic statement. The identity and actual raw quotient
examples check the same four maps; the quotient client supplies its proved
integrality and surjectivity. Generic stalks are fields only after integrality.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

theorem functionFieldMap_comp_stalkFunctionFieldAlgebra
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) :
    f.functionFieldMap.hom.comp (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) =
      (algebraMap (X.presheaf.stalk x) X.functionField).comp (f.stalkMap x).hom := by
  have hcat : CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) ≫
      f.functionFieldMap = f.stalkMap x ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ ?_
    have : Nonempty U := ⟨⟨f x, hxU⟩⟩
    have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, hxU⟩⟩
    ext s
    change f.functionFieldMap.hom
        (algebraMap (Y.presheaf.stalk (f x)) Y.functionField
          (Y.presheaf.germ U (f x) hxU s)) =
      algebraMap (X.presheaf.stalk x) X.functionField
        ((f.stalkMap x).hom (Y.presheaf.germ U (f x) hxU s))
    have hxpre : x ∈ f ⁻¹ᵁ U := hxU
    have hpull : (f.stalkMap x).hom (Y.presheaf.germ U (f x) hxU s) =
        X.presheaf.germ (f ⁻¹ᵁ U) x hxpre (f.app U s) :=
      Scheme.Hom.germ_stalkMap_apply f U x hxU s
    rw [Y.algebraMap_germ_eq_germToFunctionField,
      functionFieldMap_germToFunctionField, hpull]
    change X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) = _
    exact (X.algebraMap_germ_eq_germToFunctionField hxpre (f.app U s)).symm
  exact CommRingCat.hom_ext_iff.mp hcat

example {X : Scheme.{u}} [IrreducibleSpace X] (x : X) :
    (𝟙 X : X ⟶ X).functionFieldMap.hom.comp
      (algebraMap (X.presheaf.stalk x) X.functionField) =
    (algebraMap (X.presheaf.stalk x) X.functionField).comp
      ((𝟙 X : X ⟶ X).stalkMap x).hom :=
  functionFieldMap_comp_stalkFunctionFieldAlgebra (𝟙 X) x

example {k : Type u} [Field k] {E : ModularCurves.EllipticCurve (Spec (.of k))}
    (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) (x : E.E) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    (G.gluedQuotientπ N hkill).functionFieldMap.hom.comp
      (algebraMap ((G.gluedQuotient N hkill).presheaf.stalk
        ((G.gluedQuotientπ N hkill) x)) (G.gluedQuotient N hkill).functionField) =
    (algebraMap (E.E.presheaf.stalk x) E.E.functionField).comp
      ((G.gluedQuotientπ N hkill).stalkMap x).hom := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  exact functionFieldMap_comp_stalkFunctionFieldAlgebra (G.gluedQuotientπ N hkill) x

#print axioms functionFieldMap_comp_stalkFunctionFieldAlgebra
#print axioms TopCat.Presheaf.stalk_hom_ext
#print axioms Scheme.algebraMap_germ_eq_germToFunctionField
#print axioms functionFieldMap_germToFunctionField
#print axioms Scheme.Hom.germ_stalkMap_apply
#print axioms stalkFunctionFieldAlgebra
#print axioms Scheme.Hom.stalkSpecializes_stalkMap
#print axioms genericPoint_eq_of_isDominant
#print axioms Scheme.Hom.functionFieldMap

end AlgebraicGeometry

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

#print axioms gluedQuotient_isIntegral
#print axioms gluedQuotientπ_surjective

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
