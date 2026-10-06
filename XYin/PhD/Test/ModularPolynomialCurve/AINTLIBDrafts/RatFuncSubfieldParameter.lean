/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.RatFuncTranscendentalParameterFinite

/-!
# Finite rational parameters in an embedded field

Any base-field algebra embedding into a supplied function field makes the
rational-function embedding attached to a transcendental element of the source
field finite. No finiteness assumption on the field embedding is needed.

The proof first obtains finiteness of the composite using the existing target
function-field scalars and the parameter-map naturality theorem. It then installs
the new parameter scalars on both fields, repackages the actual embedding with
literal scalar compatibility, and transfers finite dimension along its injective
linear map. The independently supplied base-field algebras are unchanged.

The two examples check the identity field map and the actual rational-function
inclusion into the supplied function field. No old target coordinate is assumed
to descend to the embedded field. There is no quotient or separability assertion.
-/

@[expose] public section

open scoped Polynomial RatFunc

universe u v w

namespace RatFunc

variable {k : Type u} {K : Type v} {L : Type w}
  [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
  [Algebra k⟮X⟯ K] [FunctionField k K] [IsScalarTower k k⟮X⟯ K]

theorem algHomOfTranscendental_finite_of_algHom (φ : L →ₐ[k] K) (t : L)
    (ht : Transcendental k t) :
    (algHomOfTranscendental t ht).toRingHom.Finite := by
  let ζ := algHomOfTranscendental t ht
  have hcomp : (φ.comp ζ).toRingHom.Finite := by
    have hK := algHomOfTranscendental_finite (φ t)
      ((isAlgebraic_algHom_iff φ φ.injective).not.mpr ht)
    have heq := congrArg AlgHom.toRingHom (comp_algHomOfTranscendental φ t ht)
    exact (congrArg RingHom.Finite heq).mpr hK
  let _ : Algebra k⟮X⟯ L := ζ.toRingHom.toAlgebra
  let _ : Algebra k⟮X⟯ K := (φ.comp ζ).toRingHom.toAlgebra
  have : Module.Finite k⟮X⟯ K := hcomp
  let ψ : L →ₐ[k⟮X⟯] K :=
    { φ.toRingHom with commutes' := fun _ ↦ rfl }
  change Module.Finite k⟮X⟯ L
  exact FiniteDimensional.of_injective ψ.toLinearMap φ.injective

example {k : Type u} [Field k] :
    (algHomOfTranscendental (X : k⟮X⟯) transcendental_X).toRingHom.Finite :=
  algHomOfTranscendental_finite_of_algHom (AlgHom.id k k⟮X⟯) _ _

example {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra k⟮X⟯ K] [FunctionField k K] [IsScalarTower k k⟮X⟯ K] :
    (algHomOfTranscendental (X : k⟮X⟯) transcendental_X).toRingHom.Finite :=
  algHomOfTranscendental_finite_of_algHom (IsScalarTower.toAlgHom k k⟮X⟯ K) _ _

#print axioms algHomOfTranscendental_finite_of_algHom
#print axioms algHomOfTranscendental_finite
#print axioms comp_algHomOfTranscendental
#print axioms FiniteDimensional.of_injective
#print axioms RingHom.Finite
#print axioms RingHom.toAlgebra
#print axioms RingHom.injective
#print axioms IsScalarTower.toAlgHom

end RatFunc
