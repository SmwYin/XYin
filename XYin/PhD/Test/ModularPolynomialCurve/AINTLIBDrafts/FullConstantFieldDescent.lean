/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.Vendored.RiemannRoch.Basic
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Full constant fields descend along actual field embeddings

A base-field algebra homomorphism into a field with no new algebraic
constants proves the same property for its source. Algebraicity maps
forward; constant compatibility and field-hom injectivity reflect the
resulting constant equality. No finite-extension, function-field, genus,
separability or algebraic-closure assumption is added.

The examples check identity embeddings and algebra equivalences. The
vendored full-constant-field predicate is used unchanged.
-/

@[expose] public section

namespace FunctionField

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]

/-- A base-field embedding into a field with no new algebraic constants inherits that property. -/
theorem IsFullConstantField.of_algHom [IsFullConstantField k L] (e : K →ₐ[k] L) :
    IsFullConstantField k K := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨c, hc⟩ := IsFullConstantField.algebraic_mem (k := k) (K := L) (e x)
    (IsAlgebraic.algHom e hx)
  exact ⟨c, e.injective (hc.trans (e.commutes c).symm)⟩

example [IsFullConstantField k K] : IsFullConstantField k K :=
  IsFullConstantField.of_algHom (AlgHom.id k K)

example [IsFullConstantField k L] (e : K ≃ₐ[k] L) : IsFullConstantField k K :=
  IsFullConstantField.of_algHom e.toAlgHom

#print axioms IsFullConstantField.of_algHom
#print axioms IsFullConstantField.algebraic_mem
#print axioms IsAlgebraic.algHom
#print axioms RingHom.injective

end FunctionField
