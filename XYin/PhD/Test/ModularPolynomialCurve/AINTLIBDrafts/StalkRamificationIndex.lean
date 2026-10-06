/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientStalkMap
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Actual stalk ramification indices for unramified morphisms

The length-defined ideal ramification index is one under the genuine
formally-unramified and locally finite-type stalk-map properties. Applied to
the native subgroup quotient, this gives actual raw/public indices when the
subgroup projection is etale. No domain, DVR, Noetherian or genus premise is
needed. Comparison with normalized intrinsic Place valuations is separate.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The length-defined index at the actual stalk prime is one for an unramified map. -/
theorem FormallyUnramified.ramificationIdx_stalkMap
    (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f] (x : X) :
    let _ : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx
      (Y.presheaf.stalk (f.base x)) = 1 := by
  let : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified
      (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  exact (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx_eq_one
    (Y.presheaf.stalk (f.base x))

#print axioms FormallyUnramified.ramificationIdx_stalkMap
#print axioms Ideal.ramificationIdx_eq_one
#print axioms FormallyUnramified.stalkMap
#print axioms LocallyOfFiniteType.stalkMap
#print axioms RingHom.formallyUnramified_algebraMap
#print axioms RingHom.essFiniteType_algebraMap

end AlgebraicGeometry

open AlgebraicGeometry ModularCurves

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : E.FiniteLocallyFreeSubgroup)
  [Etale G.π]

theorem gluedQuotientπ_stalk_ramificationIdx_eq_one (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) (x : E.E) :
    let Q := G.gluedQuotient N hkill
    let q := G.gluedQuotientπ N hkill
    let _ : Algebra (Q.presheaf.stalk (q.base x)) (E.E.presheaf.stalk x) :=
      (q.stalkMap x).hom.toAlgebra
    (IsLocalRing.maximalIdeal (E.E.presheaf.stalk x)).ramificationIdx
      (Q.presheaf.stalk (q.base x)) = 1 := by
  have : Etale (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_etale N hkill
  exact FormallyUnramified.ramificationIdx_stalkMap (G.gluedQuotientπ N hkill) x

theorem quotientπ_stalk_ramificationIdx_eq_one [G.HasKillingInt] (x : E.E) :
    let _ : Algebra (G.quotient.presheaf.stalk (G.quotientπ.base x))
        (E.E.presheaf.stalk x) := (G.quotientπ.stalkMap x).hom.toAlgebra
    (IsLocalRing.maximalIdeal (E.E.presheaf.stalk x)).ramificationIdx
      (G.quotient.presheaf.stalk (G.quotientπ.base x)) = 1 :=
  G.gluedQuotientπ_stalk_ramificationIdx_eq_one G.killN G.killN_spec x

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) (x : E.E) :
    let Q := G.gluedQuotient N hkill
    let q := G.gluedQuotientπ N hkill
    let _ : Algebra (Q.presheaf.stalk (q.base x)) (E.E.presheaf.stalk x) :=
      (q.stalkMap x).hom.toAlgebra
    (IsLocalRing.maximalIdeal (E.E.presheaf.stalk x)).ramificationIdx
      (Q.presheaf.stalk (q.base x)) = 1 :=
  G.gluedQuotientπ_stalk_ramificationIdx_eq_one N hkill x

example [G.HasKillingInt] (x : E.E) :
    let _ : Algebra (G.quotient.presheaf.stalk (G.quotientπ.base x))
        (E.E.presheaf.stalk x) := (G.quotientπ.stalkMap x).hom.toAlgebra
    (IsLocalRing.maximalIdeal (E.E.presheaf.stalk x)).ramificationIdx
      (G.quotient.presheaf.stalk (G.quotientπ.base x)) = 1 :=
  G.quotientπ_stalk_ramificationIdx_eq_one x

#print axioms gluedQuotientπ_stalk_ramificationIdx_eq_one
#print axioms quotientπ_stalk_ramificationIdx_eq_one
#print axioms gluedQuotientπ_etale

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
