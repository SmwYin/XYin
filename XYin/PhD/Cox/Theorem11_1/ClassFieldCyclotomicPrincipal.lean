/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevIdealCounting

open NumberField
open scoped IsMulCommutative
noncomputable section
/-! Interfaces for Janusz III.3.3 and V.5.1.1–5.1.2. The actual readiness proofs are retained
separately.
-/

namespace Cox.ClassFieldTheory

/-- A principal ideal with nonnegative norm congruent to one acts trivially on a cyclotomic
field. -/
theorem frobenius_principal_eq_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ n) (a : 𝓞 K) (ha : a ≠ 0)
    (hN : 0 ≤ Algebra.norm ℤ a) (hcong : (Algebra.norm ℤ a : ZMod n) = 1) :
    letI := IsCyclotomicExtension.isAbelianGalois {n} K L
    Cox.Chebotarev.frobeniusIdeal K L (Ideal.span ({a} : Set (𝓞 K))) = 1 := by
  letI := IsCyclotomicExtension.isAbelianGalois {n} K L
  set 𝔠 : Ideal (𝓞 K) := Ideal.span ({a} : Set (𝓞 K)) with h𝔠def
  have h𝔠 : 𝔠 ≠ ⊥ := by rw [h𝔠def, Ne, Ideal.span_singleton_eq_bot]; exact ha
  have hnormZ : ((Ideal.absNorm 𝔠 : ℕ) : ℤ) = Algebra.norm ℤ a := by
    rw [h𝔠def, Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg hN]
  have hcong' : ((Ideal.absNorm 𝔠 : ℕ) : ZMod n) = 1 := by
    rw [← hcong, ← hnormZ, Int.cast_natCast]
  have hcop : (Ideal.absNorm 𝔠).Coprime n := by
    rw [← ZMod.isUnit_iff_coprime, hcong']
    exact isUnit_one
  have key := Cox.Chebotarev.autToPow_frobeniusIdeal K L n hζ 𝔠 h𝔠 hcop
  apply hζ.autToPow_injective K
  rw [key, map_one]
  ext
  rw [ZMod.coe_unitOfCoprime, hcong', Units.val_one]

end Cox.ClassFieldTheory
