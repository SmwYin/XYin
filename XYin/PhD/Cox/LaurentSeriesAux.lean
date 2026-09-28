/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Auxiliary API for Hahn and Laurent series

General facts about Hahn series, Laurent series and power series that are missing from
mathlib and are used by the Laurent-series side of Cox's Chapter 11.

## Main definitions and results

* `HahnSeries.mapRingHom`: coefficientwise application of a ring homomorphism, bundled.
* `HahnSeries.coeffSubring`: the Hahn series with all coefficients in a given subring.
* `HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt`, `HahnSeries.leadingCoeff_pow`.
* `HahnSeries.charP`: Hahn series over a ring of characteristic `p` have characteristic `p`.
* `LaurentSeries.coeff_single_neg_mul_coe_expand`: the coefficients of `X⁻ᴺ · F(Xᴺ)`.
* `PowerSeries.pow_prime_pow_eq_expand`: the Frobenius identity `F ^ pⁿ = F(X^pⁿ)` over `ZMod p`.
-/

noncomputable section

namespace HahnSeries

variable {Γ R S : Type*}

section mapRingHom

variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R]
  [Semiring S]

/-- Coefficientwise application of a ring homomorphism, as a ring homomorphism of Hahn
series. -/
def mapRingHom (f : R →+* S) : HahnSeries Γ R →+* HahnSeries Γ S where
  toFun x := x.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom

@[simp]
theorem mapRingHom_apply (f : R →+* S) (x : HahnSeries Γ R) : mapRingHom f x = x.map f :=
  rfl

theorem mapRingHom_coeff (f : R →+* S) (x : HahnSeries Γ R) (g : Γ) :
    (mapRingHom f x).coeff g = f (x.coeff g) :=
  rfl

end mapRingHom

section coeffSubring

variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Ring R]

/-- The subring of Hahn series all of whose coefficients lie in the subring `S`. -/
def coeffSubring (S : Subring R) : Subring (HahnSeries Γ R) where
  carrier := {x | ∀ g, x.coeff g ∈ S}
  zero_mem' _ := by simp
  one_mem' g := by rw [coeff_one]; split_ifs <;> simp
  add_mem' hx hy g := by rw [coeff_add]; exact S.add_mem (hx g) (hy g)
  neg_mem' hx g := by rw [coeff_neg]; exact S.neg_mem (hx g)
  mul_mem' hx hy g := by
    rw [coeff_mul]
    exact S.sum_mem fun ij _ ↦ S.mul_mem (hx ij.1) (hy ij.2)

@[simp]
theorem mem_coeffSubring {S : Subring R} {x : HahnSeries Γ R} :
    x ∈ coeffSubring S ↔ ∀ g, x.coeff g ∈ S :=
  Iff.rfl

end coeffSubring

/-- A nonzero coefficient below which all coefficients vanish sits at the order. -/
theorem order_eq_of_coeff_ne_zero_of_forall_lt [Zero Γ] [LinearOrder Γ] [Zero R]
    {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) (h' : ∀ i < g, x.coeff i = 0) :
    x.order = g :=
  le_antisymm (order_le_of_coeff_ne_zero h)
    ((le_order_iff_forall (ne_zero_of_coeff_ne_zero h)).2 h')

@[simp]
theorem leadingCoeff_pow [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [Semiring R] [NoZeroDivisors R] (x : HahnSeries Γ R) (n : ℕ) :
    (x ^ n).leadingCoeff = x.leadingCoeff ^ n := by
  induction n with
  | zero => simp [leadingCoeff_one]
  | succ n ih => rw [pow_succ, leadingCoeff_mul, ih, pow_succ]

/-- Hahn series over a ring of characteristic `p` have characteristic `p`. -/
instance charP [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R]
    (p : ℕ) [CharP R p] : CharP (HahnSeries Γ R) p :=
  charP_of_injective_ringHom (f := C) C_injective p

end HahnSeries

namespace LaurentSeries

open HahnSeries

/-- The coefficients of `X⁻ᴺ · F(Xᴺ)`: the coefficient of `Xᵏ` is the coefficient of
`X^(k/N + 1)` in `F` when `N ∣ k` and `-N ≤ k`, and zero otherwise. -/
theorem coeff_single_neg_mul_coe_expand {R : Type*} [CommRing R] (N : ℕ) (hN : N ≠ 0)
    (F : PowerSeries R) (k : ℤ) :
    (single (-(N : ℤ)) (1 : R) * ((F.expand N hN : PowerSeries R) : LaurentSeries R)).coeff k =
      if (N : ℤ) ∣ k ∧ -(N : ℤ) ≤ k then PowerSeries.coeff (k / N + 1).toNat F else 0 := by
  rw [← sub_add_cancel k (-(N : ℤ)), coeff_single_mul_add, one_mul, sub_add_cancel,
    PowerSeries.coeff_coe]
  split_ifs with h1 h2 h2
  · omega
  · rfl
  · obtain ⟨⟨t, rfl⟩, ht⟩ := h2
    have hN0 : (0 : ℤ) < N := by omega
    have ht1 : 0 ≤ t + 1 := by nlinarith
    rw [show (N : ℤ) * t - -N = ((N * (t + 1).toNat : ℕ) : ℤ) by
        push_cast; rw [Int.toNat_of_nonneg ht1]; ring,
      Int.natAbs_natCast, PowerSeries.coeff_expand_mul, Int.mul_ediv_cancel_left _ hN0.ne']
  · rw [PowerSeries.coeff_expand, if_neg]
    rw [← Int.natCast_dvd, sub_neg_eq_add, dvd_add_self_right]
    omega

end LaurentSeries

namespace PowerSeries

/-- The iterated Frobenius identity for power series over `ZMod p`:
`F ^ pⁿ = F(X^pⁿ)`. -/
theorem pow_prime_pow_eq_expand (p : ℕ) [hp : Fact p.Prime] (F : PowerSeries (ZMod p))
    (n : ℕ) : F ^ p ^ n = F.expand (p ^ n) (pow_ne_zero n hp.out.ne_zero) := by
  have hiter : iterateFrobenius (ZMod p) p n = RingHom.id _ := by
    ext x
    exact ZMod.pow_card_pow x
  have h := MvPowerSeries.map_iterateFrobenius_expand (R := ZMod p) p hp.out.ne_zero F n
  rw [hiter, MvPowerSeries.map_id] at h
  exact h.symm

end PowerSeries
