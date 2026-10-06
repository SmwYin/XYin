/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativeRatFuncScalars
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientBaseAlgHom
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientFunctionField
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# A transcendental element in the actual subgroup quotient field

The original native elliptic function field is transcendental over its independent
geometric base constants. The actual quotient pullback is a finite algebra map
between the independently specified base-field algebras. Algebraicity of the
quotient would therefore contradict transcendence of the source field.

The raw and public APIs give existence of a quotient transcendental element over
any field, using their actual killing witnesses. They do not select a quotient
coordinate, a separating chart, or a Weierstrass model. The two examples exercise
the raw and public interfaces without extra hypotheses.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open scoped RatFunc

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

theorem nativeField_isTranscendental (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    Algebra.Transcendental k E.E.functionField := by
  let _ := E.π.functionFieldBaseAlgebra
  let _ := nativeFieldRatFuncAlgebra E
  let _ := nativeFieldRatFunc_baseTower E
  refine ⟨algebraMap k⟮X⟯ E.E.functionField (RatFunc.X : k⟮X⟯), ?_⟩
  exact (transcendental_algebraMap_iff
    (algebraMap k⟮X⟯ E.E.functionField).injective).mpr RatFunc.transcendental_X

end ModularCurves.YZeroCoarseJ

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

open ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

theorem gluedQuotient_exists_transcendental :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∃ t : (G.gluedQuotient N hkill).functionField, Transcendental k t := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  let φ : (G.gluedQuotient N hkill).functionField →ₐ[k] E.E.functionField :=
    G.gluedQuotientπ_functionFieldBaseAlgHom N hkill
  let _ := φ.toRingHom.toAlgebra
  have : IsScalarTower k (G.gluedQuotient N hkill).functionField E.E.functionField :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  have : Module.Finite (G.gluedQuotient N hkill).functionField E.E.functionField :=
    (G.gluedQuotientπ_functionFieldMap_finite_injective N hkill).1
  have : Algebra.IsAlgebraic (G.gluedQuotient N hkill).functionField E.E.functionField :=
    Algebra.IsAlgebraic.of_finite _ _
  have hsource := nativeField_isTranscendental E
  have htarget : Algebra.Transcendental k (G.gluedQuotient N hkill).functionField := by
    apply Algebra.transcendental_iff_not_isAlgebraic.mpr
    intro h
    let _ := h
    exact (Algebra.transcendental_iff_not_isAlgebraic.mp hsource)
      (Algebra.IsAlgebraic.trans k (G.gluedQuotient N hkill).functionField E.E.functionField)
  exact htarget.transcendental

theorem quotient_exists_transcendental [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∃ t : G.quotient.functionField, Transcendental k t :=
  G.gluedQuotient_exists_transcendental G.killN G.killN_spec

example :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∃ t : (G.gluedQuotient N hkill).functionField, Transcendental k t :=
  G.gluedQuotient_exists_transcendental N hkill

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∃ t : G.quotient.functionField, Transcendental k t :=
  G.quotient_exists_transcendental

#print axioms ModularCurves.YZeroCoarseJ.nativeField_isTranscendental
#print axioms gluedQuotient_exists_transcendental
#print axioms quotient_exists_transcendental
#print axioms RatFunc.transcendental_X
#print axioms transcendental_algebraMap_iff
#print axioms ModularCurves.YZeroCoarseJ.nativeFieldRatFunc_baseTower
#print axioms gluedQuotientπ_functionFieldBaseAlgHom
#print axioms gluedQuotientπ_functionFieldMap_finite_injective
#print axioms Algebra.IsAlgebraic.of_finite
#print axioms Algebra.IsAlgebraic.trans
#print axioms Algebra.transcendental_iff_not_isAlgebraic
#print axioms IsScalarTower.of_algebraMap_eq

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
