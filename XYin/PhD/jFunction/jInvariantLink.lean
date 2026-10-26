/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

import XYin.PhD.Cox.LatticeJ

/-!
# The analytic, lattice, and elliptic-curve `j`-invariants

This file attaches a short Weierstrass model to a complex period lattice and proves that its
Mathlib `j`-invariant is the project's lattice invariant. For the normalized lattice `[1, τ]`,
this also identifies Mathlib's invariant with the analytic modular function `j(τ)`.

## Main definitions

* `PeriodPair.weierstrassCurve`: the short Weierstrass model of a period lattice.
* `UpperHalfPlane.ellipticCurve`: the model attached to the normalized lattice `[1, τ]`.

## Main results

* `PeriodPair.weierstrassCurve_j`: the model's invariant is the lattice invariant.
* `UpperHalfPlane.ellipticCurve_j`: the normalized model's invariant is the analytic `j`.
-/

noncomputable section

namespace PeriodPair

/-- The short Weierstrass model attached to a complex period lattice. -/
def weierstrassCurve (L : PeriodPair) : WeierstrassCurve ℂ :=
  ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩

instance (L : PeriodPair) : L.weierstrassCurve.IsShortNF := ⟨rfl, rfl, rfl⟩

/-- The fourth Weierstrass invariant of the lattice model is `12 g₂`. -/
theorem weierstrassCurve_c₄ (L : PeriodPair) : L.weierstrassCurve.c₄ = 12 * L.g₂ := by
  rw [WeierstrassCurve.c₄_of_isShortNF]
  change -48 * (-L.g₂ / 4) = 12 * L.g₂
  ring

/-- The sixth Weierstrass invariant of the lattice model is `216 g₃`. -/
theorem weierstrassCurve_c₆ (L : PeriodPair) : L.weierstrassCurve.c₆ = 216 * L.g₃ := by
  rw [WeierstrassCurve.c₆_of_isShortNF]
  change -864 * (-L.g₃ / 4) = 216 * L.g₃
  ring

/-- The Weierstrass and period-lattice discriminants have the same normalization. -/
theorem weierstrassCurve_Δ (L : PeriodPair) : L.weierstrassCurve.Δ = L.discriminant := by
  rw [WeierstrassCurve.Δ_of_isShortNF, PeriodPair.discriminant]
  change -16 * (4 * (-L.g₂ / 4) ^ 3 + 27 * (-L.g₃ / 4) ^ 2) = L.g₂ ^ 3 - 27 * L.g₃ ^ 2
  ring

instance (L : PeriodPair) : L.weierstrassCurve.IsElliptic :=
  ⟨L.weierstrassCurve_Δ ▸ L.discriminant_ne_zero.isUnit⟩

/-- The Mathlib elliptic-curve invariant of the lattice model is Cox's lattice invariant. -/
@[simp]
theorem weierstrassCurve_j (L : PeriodPair) : L.weierstrassCurve.j = L.j := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul,
    WeierstrassCurve.coe_Δ', weierstrassCurve_c₄, weierstrassCurve_Δ, PeriodPair.j]
  ring

end PeriodPair

namespace UpperHalfPlane

/-- The short Weierstrass model attached to the normalized lattice `[1, τ]`. -/
def ellipticCurve (τ : ℍ) : WeierstrassCurve ℂ := (periodPair τ).weierstrassCurve

instance (τ : ℍ) : (ellipticCurve τ).IsElliptic :=
  inferInstanceAs (periodPair τ).weierstrassCurve.IsElliptic

/-- The Mathlib `j`-invariant of the normalized elliptic curve is the analytic modular `j`. -/
@[simp]
theorem ellipticCurve_j (τ : ℍ) : (ellipticCurve τ).j = _root_.j τ :=
  (periodPair τ).weierstrassCurve_j.trans (j_eq_periodPair_j τ).symm

end UpperHalfPlane
