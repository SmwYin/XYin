/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativeFunctionFieldStructure
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientFunctionFieldDegree
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# NativeCoordinateTowerObstruction

The chosen source coordinate cannot generally descend through the quotient.
The genuine quotient extension degree must divide two if its field admits
a compatible algebra under the source Weierstrass RatFunc embedding.
The rank-three API check refutes such a tower. No quotient coordinate
is assumed to exist.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open scoped Polynomial RatFunc

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

theorem nativeFieldRatFunc_finrank (E : EllipticCurve (Spec (.of k))) :
    let _ := nativeFieldRatFuncAlgebra E
    Module.finrank k⟮X⟯ E.E.functionField = 2 := by
  let _ := nativeFieldCoordinateAlgebra E
  let _ := nativeFieldCoordinate_isFractionRing E
  let _ := nativeFieldPolynomialAlgebra E
  let _ := nativeFieldPolynomial_coordinateTower E
  let _ := nativeFieldRatFuncAlgebra E
  let _ := nativeFieldRatFunc_polynomialTower E
  exact (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.finrank_ratFunc_eq_two
    E.E.functionField

end ModularCurves.YZeroCoarseJ

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

open ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

theorem gluedQuotient_coordinateTower_rank_dvd_two (r : ℕ) (hG : G.HasRank r) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := functionFieldAlgebra (G.gluedQuotientπ N hkill)
    let _ := nativeFieldRatFuncAlgebra E
    ∀ (a : Algebra k⟮X⟯ (G.gluedQuotient N hkill).functionField),
      let _ := a
      IsScalarTower k⟮X⟯ (G.gluedQuotient N hkill).functionField E.E.functionField → r ∣ 2 := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := functionFieldAlgebra (G.gluedQuotientπ N hkill)
  let _ := nativeFieldRatFuncAlgebra E
  dsimp only
  intro a
  let _ := a
  intro htower
  let _ := htower
  have h := Module.finrank_dvd_finrank_left k⟮X⟯
    (G.gluedQuotient N hkill).functionField E.E.functionField
  rw [G.gluedQuotientπ_functionField_finrank N hkill r hG, nativeFieldRatFunc_finrank E] at h
  exact h

example (hG : G.HasRank 3) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := functionFieldAlgebra (G.gluedQuotientπ N hkill)
    let _ := nativeFieldRatFuncAlgebra E
    ∀ (a : Algebra k⟮X⟯ (G.gluedQuotient N hkill).functionField),
      let _ := a
      ¬ IsScalarTower k⟮X⟯ (G.gluedQuotient N hkill).functionField E.E.functionField := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := functionFieldAlgebra (G.gluedQuotientπ N hkill)
  let _ := nativeFieldRatFuncAlgebra E
  dsimp only
  intro a
  let _ := a
  intro htower
  have h := G.gluedQuotient_coordinateTower_rank_dvd_two N hkill 3 hG a htower
  norm_num at h

example (r : ℕ) (hG : G.HasRank r) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := functionFieldAlgebra (G.gluedQuotientπ N hkill)
    let _ := nativeFieldRatFuncAlgebra E
    ∀ (a : Algebra k⟮X⟯ (G.gluedQuotient N hkill).functionField),
      let _ := a
      IsScalarTower k⟮X⟯ (G.gluedQuotient N hkill).functionField E.E.functionField → r ∣ 2 :=
  G.gluedQuotient_coordinateTower_rank_dvd_two N hkill r hG

#print axioms ModularCurves.YZeroCoarseJ.nativeFieldRatFunc_finrank
#print axioms gluedQuotient_coordinateTower_rank_dvd_two
#print axioms WeierstrassCurve.Affine.finrank_ratFunc_eq_two
#print axioms Module.finrank_dvd_finrank_left
#print axioms gluedQuotientπ_functionField_finrank

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
