/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.RatFuncTranscendentalParameter
public import Mathlib.NumberTheory.FunctionField

/-!
# Finite transcendental parameters and algebra-map naturality

A supplied function-field structure and genuine base-field scalar tower imply
that the rational-function embedding attached to any transcendental target
element is finite. This uses finiteness over its actual adjoin field, followed
by the canonical rational-function equivalence.

Under an independently specified base-field algebra map, the parameter embedding
is natural. Injectivity transports transcendence, and the actual polynomial
restrictions agree by aeval naturality and localization extensionality.

The two examples check the rational indeterminate and the identity field map.
No descent of the old source coordinate into a subfield is assumed; no quotient
finite pack or separability result is supplied by this module.
-/

@[expose] public section

open scoped Polynomial RatFunc nonZeroDivisors

universe u v w

namespace RatFunc

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

section Finite

variable [Algebra k⟮X⟯ K] [FunctionField k K] [IsScalarTower k k⟮X⟯ K]

theorem algHomOfTranscendental_finite (t : K) (ht : Transcendental k t) :
    (algHomOfTranscendental t ht).toRingHom.Finite := by
  have hfinite : Module.Finite (IntermediateField.adjoin k {t}) K :=
    FunctionField.finiteDimensional_of_adjoin_transcendental ht
  have hval : (IntermediateField.adjoin k {t}).val.toRingHom.Finite := by
    change (algebraMap (IntermediateField.adjoin k {t}) K).Finite
    exact RingHom.finite_algebraMap.mpr hfinite
  exact hval.comp (algEquivOfTranscendental t ht).toRingEquiv.finite

end Finite

variable {L : Type w} [Field L] [Algebra k L]

theorem comp_algHomOfTranscendental (φ : L →ₐ[k] K) (t : L)
    (ht : Transcendental k t) :
    φ.comp (algHomOfTranscendental t ht) =
      algHomOfTranscendental (φ t) ((isAlgebraic_algHom_iff φ φ.injective).not.mpr ht) := by
  apply IsLocalization.algHom_ext (nonZeroDivisors k[X])
  calc
    (φ.comp (algHomOfTranscendental t ht)).comp (Algebra.algHom k k[X] k⟮X⟯) =
        φ.comp ((algHomOfTranscendental t ht).comp (Algebra.algHom k k[X] k⟮X⟯)) := rfl
    _ = φ.comp (Polynomial.aeval t) :=
      congrArg φ.comp (algHomOfTranscendental_comp_algebraMap t ht)
    _ = Polynomial.aeval (φ t) := (Polynomial.aeval_algHom φ t).symm
    _ = (algHomOfTranscendental (φ t)
          ((isAlgebraic_algHom_iff φ φ.injective).not.mpr ht)).comp
        (Algebra.algHom k k[X] k⟮X⟯) :=
      (algHomOfTranscendental_comp_algebraMap _ _).symm

example {k : Type u} [Field k] :
    (algHomOfTranscendental (X : k⟮X⟯) transcendental_X).toRingHom.Finite :=
  algHomOfTranscendental_finite _ _

example (t : L) (ht : Transcendental k t) :
    (AlgHom.id k L).comp (algHomOfTranscendental t ht) =
      algHomOfTranscendental ((AlgHom.id k L) t)
        ((isAlgebraic_algHom_iff (AlgHom.id k L) (AlgHom.id k L).injective).not.mpr ht) :=
  comp_algHomOfTranscendental _ _ _

#print axioms algHomOfTranscendental_finite
#print axioms comp_algHomOfTranscendental
#print axioms FunctionField.finiteDimensional_of_adjoin_transcendental
#print axioms RingEquiv.finite
#print axioms RingHom.Finite.comp
#print axioms RingHom.finite_algebraMap
#print axioms IsLocalization.algHom_ext
#print axioms Polynomial.aeval_algHom
#print axioms isAlgebraic_algHom_iff
#print axioms RingHom.injective
#print axioms algHomOfTranscendental_comp_algebraMap

end RatFunc
