/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativeChartIntegrallyClosed
public import AINTLIBDrafts.FlatStalkIntegrallyClosed
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientGeometry
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Integral closedness of native curve and actual subgroup quotient stalks

The actual gluing chart at a curve point gives an integrally closed section
ring. Its genuine germ localization gives integral closedness of the curve
stalk. Flatness and surjectivity of the actual subgroup quotient projection
then descend integral closedness to every quotient stalk.

The base is an arbitrary field and the subgroup carries its actual nonzero
killing integer. The public quotient uses the existing chosen killing datum.
The assertions use no additional freeness, étale, Noetherian or genus premise.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup)

/-- The genuine gluing chart proves integral closedness of the actual curve stalk. -/
theorem curveStalk_isIntegrallyClosed (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) (x : E.E) :
    IsIntegrallyClosed (E.E.presheaf.stalk x) := by
  let P := G.gluePatch N hkill x
  have hx : x ∈ P.U := G.mem_gluePatch N hkill x
  have : Nonempty P.U := ⟨⟨x, hx⟩⟩
  have : IsDomain P.chartRing := IsIntegral.component_integral P.U
  have : IsIntegrallyClosed P.chartRing := G.gluePatch_chartRing_isIntegrallyClosed N hkill x
  let : Algebra P.chartRing (E.E.presheaf.stalk x) :=
    E.E.presheaf.algebra_section_stalk ⟨x, hx⟩
  let p := P.hU.primeIdealOf ⟨x, hx⟩
  have : IsLocalization.AtPrime (E.E.presheaf.stalk x) p.asIdeal :=
    P.hU.isLocalization_stalk ⟨x, hx⟩
  exact isIntegrallyClosed_of_isLocalization (E.E.presheaf.stalk x) p.asIdeal.primeCompl
    p.asIdeal.primeCompl_le_nonZeroDivisors

/-- Actual projection flatness and surjectivity descend the source stalk normality. -/
theorem gluedQuotient_stalk_isIntegrallyClosed (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) (y : G.gluedQuotient N hkill) :
    IsIntegrallyClosed ((G.gluedQuotient N hkill).presheaf.stalk y) := by
  have : Flat (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_flat N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  exact Flat.isIntegrallyClosed_stalks_of_surjective (G.gluedQuotientπ N hkill)
    (fun _ ↦ inferInstance) (G.curveStalk_isIntegrallyClosed N hkill) y

/-- The public interface is the same construction at its actual chosen killing integer. -/
theorem quotient_stalk_isIntegrallyClosed [G.HasKillingInt] (y : G.quotient) :
    IsIntegrallyClosed (G.quotient.presheaf.stalk y) :=
  G.gluedQuotient_stalk_isIntegrallyClosed G.killN G.killN_spec y

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
    (y : G.gluedQuotient N hkill) :
    IsIntegrallyClosed ((G.gluedQuotient N hkill).presheaf.stalk y) :=
  G.gluedQuotient_stalk_isIntegrallyClosed N hkill y

example [G.HasKillingInt] (y : G.quotient) :
    IsIntegrallyClosed (G.quotient.presheaf.stalk y) :=
  G.quotient_stalk_isIntegrallyClosed y

#print axioms curveStalk_isIntegrallyClosed
#print axioms gluedQuotient_stalk_isIntegrallyClosed
#print axioms quotient_stalk_isIntegrallyClosed
#print axioms gluePatch_chartRing_isIntegrallyClosed
#print axioms IsAffineOpen.isLocalization_stalk
#print axioms TopCat.Presheaf.algebra_section_stalk
#print axioms Ideal.primeCompl_le_nonZeroDivisors
#print axioms isIntegrallyClosed_of_isLocalization
#print axioms Flat.isIntegrallyClosed_stalks_of_surjective
#print axioms Flat.isIntegrallyClosed_stalkMap_target
#print axioms gluedQuotientπ_flat
#print axioms gluedQuotientπ_surjective
#print axioms ModularCurves.EllipticCurve.isIntegral_of_field
#print axioms killN_spec

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
