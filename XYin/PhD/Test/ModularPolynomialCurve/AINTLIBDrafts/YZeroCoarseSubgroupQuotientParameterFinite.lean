/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.RatFuncSubfieldParameter
public import AINTLIBDrafts.NativeFunctionFieldStructure
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientBaseAlgHom

/-!
# Finite transcendental parameters in the actual subgroup quotient

The raw and public finite subgroup quotients have finite rational-function
parameter embeddings for each transcendental element of their own native
function fields. Their base constants are supplied independently by the actual
quotient structure maps and generic germs.

The proof embeds the quotient field into the native elliptic function field via
the genuine quotient pullback over those constants. The existing native source
function-field structure and base scalar tower supply the generic subfield
parameter finiteness theorem. No finite-pullback premise, old coordinate
descent, etaleness, Noetherian hypothesis, genus, or quotient model is required.

The public interface uses exactly the chosen killing integer and its witness.
The two examples check the raw and public APIs. This module does not install
a quotient polynomial or rational-function algebra or a separability result.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open scoped RatFunc

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

open ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

theorem gluedQuotient_parameter_finite :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∀ t : (G.gluedQuotient N hkill).functionField, ∀ ht : Transcendental k t,
      (RatFunc.algHomOfTranscendental t ht).toRingHom.Finite := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  let _ := nativeFieldRatFuncAlgebra E
  have : FunctionField k E.E.functionField := nativeField_functionField E
  let _ := nativeFieldRatFunc_baseTower E
  change ∀ (t : (G.gluedQuotient N hkill).functionField) (ht : Transcendental k t),
    (RatFunc.algHomOfTranscendental t ht).toRingHom.Finite
  intro t ht
  exact RatFunc.algHomOfTranscendental_finite_of_algHom
    (G.gluedQuotientπ_functionFieldBaseAlgHom N hkill) t ht

theorem quotient_parameter_finite [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∀ t : G.quotient.functionField, ∀ ht : Transcendental k t,
      (RatFunc.algHomOfTranscendental t ht).toRingHom.Finite :=
  G.gluedQuotient_parameter_finite G.killN G.killN_spec

example :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∀ t : (G.gluedQuotient N hkill).functionField, ∀ ht : Transcendental k t,
      (RatFunc.algHomOfTranscendental t ht).toRingHom.Finite :=
  G.gluedQuotient_parameter_finite N hkill

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∀ t : G.quotient.functionField, ∀ ht : Transcendental k t,
      (RatFunc.algHomOfTranscendental t ht).toRingHom.Finite :=
  G.quotient_parameter_finite

#print axioms gluedQuotient_parameter_finite
#print axioms quotient_parameter_finite
#print axioms RatFunc.algHomOfTranscendental_finite_of_algHom
#print axioms nativeFieldRatFuncAlgebra
#print axioms nativeField_functionField
#print axioms nativeFieldRatFunc_baseTower
#print axioms gluedQuotientπ_functionFieldBaseAlgHom
#print axioms gluedQuotient_isIntegral
#print axioms gluedQuotientπ_surjective
#print axioms Scheme.Hom.functionFieldBaseAlgebra

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
