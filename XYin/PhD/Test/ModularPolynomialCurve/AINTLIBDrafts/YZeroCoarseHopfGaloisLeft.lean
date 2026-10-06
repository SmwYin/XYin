/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.ForMathlib.HopfGalois

/-!
# The canonical Hopf-Galois equivalence over its left factor

Pinned AINTLIB packages the canonical Galois map as an equivalence over the
coinvariants. Its actual left-inclusion formula shows that the same ring equivalence
is an equivalence over `B`, using the standard tensor-product algebra structure from
the first `B` factor on both sides. This module changes only the recorded scalar ring:
the underlying ring equivalence and the positive elementary-tensor formula are retained.

The input is precisely the existing `IsHopfGalois ρ` record. No new coaction, Hopf-algebra,
finite-module, or geometric quotient hypothesis is added. The field `h.galois` supplies
bijectivity through upstream `galoisEquiv`; left scalar compatibility comes from
`canonicalGaloisMap_comp_includeLeft`. Subsequent finite or geometric conclusions
require separate theorems and are not asserted here.
-/

@[expose] public section

open scoped TensorProduct
open ModularCurves

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

variable {R0 A B : Type*} [CommRing R0] [CommRing A] [CommRing B]
  [Algebra R0 A] [Algebra R0 B] {ρ : B →ₐ[R0] B ⊗[R0] A}

/-- The existing canonical Galois ring equivalence is also a left-factor algebra equivalence. -/
def galoisEquivOverLeft (h : IsHopfGalois ρ) :
    (B ⊗[coinvariants ρ] B) ≃ₐ[B] (B ⊗[R0] A) :=
  AlgEquiv.ofRingEquiv (f := h.galoisEquiv.toRingEquiv) fun b ↦ by
    change canonicalGaloisMap ρ (b ⊗ₜ[coinvariants ρ] 1) = b ⊗ₜ[R0] 1
    exact AlgHom.congr_fun (canonicalGaloisMap_comp_includeLeft ρ) b

/-- Changing the scalar ring preserves the literal underlying ring equivalence. -/
theorem galoisEquivOverLeft_toRingEquiv (h : IsHopfGalois ρ) :
    (galoisEquivOverLeft h).toRingEquiv = h.galoisEquiv.toRingEquiv := rfl

/-- The left-factor algebra equivalence has the same positive elementary-tensor formula. -/
theorem galoisEquivOverLeft_tmul (h : IsHopfGalois ρ) (b b' : B) :
    galoisEquivOverLeft h (b ⊗ₜ[coinvariants ρ] b') =
      (b ⊗ₜ[R0] 1) * ρ b' := rfl

example (h : IsHopfGalois ρ) (b : B) :
    galoisEquivOverLeft h (algebraMap B (B ⊗[coinvariants ρ] B) b) =
      algebraMap B (B ⊗[R0] A) b :=
  (galoisEquivOverLeft h).commutes b

example (h : IsHopfGalois ρ) (b b' : B) :
    galoisEquivOverLeft h (b ⊗ₜ[coinvariants ρ] b') =
      (b ⊗ₜ[R0] 1) * ρ b' :=
  galoisEquivOverLeft_tmul h b b'

#print axioms galoisEquivOverLeft
#print axioms galoisEquivOverLeft_toRingEquiv
#print axioms galoisEquivOverLeft_tmul
#print axioms ModularCurves.IsHopfGalois.galoisEquiv
#print axioms ModularCurves.canonicalGaloisMap_comp_includeLeft
#print axioms AlgEquiv.ofRingEquiv

end ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft
