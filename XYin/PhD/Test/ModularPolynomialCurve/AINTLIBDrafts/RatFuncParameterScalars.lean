/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.RatFuncTranscendentalParameter

/-!
# Scalars for a transcendental rational parameter

The rational parameter embedding uses the existing base-field algebra.
Its polynomial restriction is evaluation at the parameter, which gives the
actual polynomial/rational-function/function-field scalar tower. The two
API checks verify the literal polynomial and constant formulas.
-/

@[expose] public section

open scoped Polynomial RatFunc

universe u v

namespace RatFunc

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

theorem algHomOfTranscendental_polynomialTower (t : K) (ht : Transcendental k t) :
    let _ : Algebra k[X] K := (Polynomial.aeval t : k[X] →ₐ[k] K).toRingHom.toAlgebra
    let _ := (algHomOfTranscendental t ht).toRingHom.toAlgebra
    IsScalarTower k[X] k⟮X⟯ K := by
  let _ : Algebra k[X] K := (Polynomial.aeval t : k[X] →ₐ[k] K).toRingHom.toAlgebra
  let _ := (algHomOfTranscendental t ht).toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro p
  exact (algHomOfTranscendental_algebraMap t ht p).symm

example (t : K) (ht : Transcendental k t) (p : k[X]) :
    let _ : Algebra k[X] K := (Polynomial.aeval t : k[X] →ₐ[k] K).toRingHom.toAlgebra
    let _ := (algHomOfTranscendental t ht).toRingHom.toAlgebra
    algebraMap k[X] K p = algebraMap k⟮X⟯ K (algebraMap k[X] k⟮X⟯ p) := by
  let _ : Algebra k[X] K := (Polynomial.aeval t : k[X] →ₐ[k] K).toRingHom.toAlgebra
  let _ := (algHomOfTranscendental t ht).toRingHom.toAlgebra
  let _ := algHomOfTranscendental_polynomialTower t ht
  exact IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K p

example (t : K) (ht : Transcendental k t) (r : k) :
    let _ := (algHomOfTranscendental t ht).toRingHom.toAlgebra
    algebraMap k K r = algebraMap k⟮X⟯ K (C r) := by
  let _ := (algHomOfTranscendental t ht).toRingHom.toAlgebra
  exact (algHomOfTranscendental t ht).commutes r |>.symm

#print axioms algHomOfTranscendental_polynomialTower
#print axioms IsScalarTower.of_algHom
#print axioms algHomOfTranscendental_algebraMap
#print axioms IsScalarTower.of_algebraMap_eq
#print axioms IsScalarTower.algebraMap_apply

end RatFunc
