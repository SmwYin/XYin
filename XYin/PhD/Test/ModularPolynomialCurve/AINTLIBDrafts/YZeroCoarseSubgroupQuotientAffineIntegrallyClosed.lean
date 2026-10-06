/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientStalkIntegrallyClosed
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientIntegral
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Integral closedness of actual subgroup quotient affine sections

For any affine open whose section ring is an integral domain, integral
closedness of its actual stalks implies integral closedness of its sections.
The proof identifies the true stalk at each maximal prime with the canonical
localization and uses the existing maximal-localization criterion. It does
not require the ambient scheme to be integral.

For a native elliptic curve subgroup quotient over a field, the proved
integrality and stalk integral closedness supply the inputs on every nonempty
affine open. Raw and public quotient interfaces use their actual constructions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace AlgebraicGeometry.IsAffineOpen

variable {X : Scheme.{u}} {U : X.Opens}

/-- Integral closedness of actual stalks gives integral closedness of affine sections. -/
theorem isIntegrallyClosed_of_stalks (hU : IsAffineOpen U) [IsDomain Γ(X, U)]
    (hN : ∀ (x : X), x ∈ U → IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P _ hP
  let p : PrimeSpectrum Γ(X, U) := ⟨P, hP.isPrime⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) :=
    X.presheaf.algebra_section_stalk ⟨hU.fromSpec p, (hU.isoSpec.inv p).2⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec p)) P :=
    hU.isLocalization_stalk' p (hU.isoSpec.inv p).2
  have : IsIntegrallyClosed (X.presheaf.stalk (hU.fromSpec p)) :=
    hN (hU.fromSpec p) (hU.isoSpec.inv p).2
  exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv P.primeCompl
    (X.presheaf.stalk (hU.fromSpec p)) (Localization.AtPrime P)).toRingEquiv

end AlgebraicGeometry.IsAffineOpen

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup)

/-- Every genuine nonempty affine open in the actual raw quotient has normal sections. -/
theorem gluedQuotient_section_isIntegrallyClosed (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
    (U : (G.gluedQuotient N hkill).Opens) [Nonempty U] (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(G.gluedQuotient N hkill, U) := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  exact hU.isIntegrallyClosed_of_stalks
    (fun x _ ↦ G.gluedQuotient_stalk_isIntegrallyClosed N hkill x)

/-- The public quotient uses its actual chosen killing datum. -/
theorem quotient_section_isIntegrallyClosed [G.HasKillingInt]
    (U : G.quotient.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(G.quotient, U) := by
  have : IsIntegral G.quotient := G.quotient_isIntegral
  exact hU.isIntegrallyClosed_of_stalks (fun x _ ↦ G.quotient_stalk_isIntegrallyClosed x)

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
    (U : (G.gluedQuotient N hkill).Opens) [Nonempty U] (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(G.gluedQuotient N hkill, U) :=
  G.gluedQuotient_section_isIntegrallyClosed N hkill U hU

example [G.HasKillingInt] (U : G.quotient.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(G.quotient, U) := G.quotient_section_isIntegrallyClosed U hU

#print axioms AlgebraicGeometry.IsAffineOpen.isIntegrallyClosed_of_stalks
#print axioms gluedQuotient_section_isIntegrallyClosed
#print axioms quotient_section_isIntegrallyClosed
#print axioms IsLocalization.algEquiv
#print axioms IsIntegrallyClosed.of_localization_maximal
#print axioms IsAffineOpen.isLocalization_stalk'
#print axioms TopCat.Presheaf.algebra_section_stalk
#print axioms IsIntegral.component_integral
#print axioms gluedQuotient_stalk_isIntegrallyClosed
#print axioms quotient_stalk_isIntegrallyClosed
#print axioms gluedQuotient_isIntegral
#print axioms quotient_isIntegral

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
