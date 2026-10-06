/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevFrobenius

/-! Frobenius on ideals, before the ideal-count and Artin analysis layers.
-/
noncomputable section
open NumberField
namespace Cox.Chebotarev

/-- Planning source: ZetaProduct.lean:449; source-local planning contract. -/
def frobeniusIdeal (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]
    (𝔞 : Ideal (𝓞 K)) : Gal(L/K) :=
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
    (fun 𝔭 ↦ (frobeniusClass K L 𝔭).out)).prod

/-- Planning source: ZetaProduct.lean:458; source-local planning contract. -/
theorem frobeniusIdeal_apply_prime
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    frobeniusIdeal K L 𝔭 = (frobeniusClass K L 𝔭).out := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  rw [frobeniusIdeal, UniqueFactorizationMonoid.normalizedFactors_irreducible
    (Ideal.prime_of_isPrime h𝔭 ‹_›).irreducible, normalize_eq, Multiset.map_singleton,
    Multiset.prod_singleton]

/-- Planning source: ZetaProduct.lean:468; source-local planning contract. -/
theorem frobeniusIdeal_mul
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) :
    frobeniusIdeal K L (𝔞 * 𝔟) = frobeniusIdeal K L 𝔞 * frobeniusIdeal K L 𝔟 := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  rw [frobeniusIdeal, frobeniusIdeal, frobeniusIdeal,
    UniqueFactorizationMonoid.normalizedFactors_mul h𝔞 h𝔟, Multiset.map_add, Multiset.prod_add]

/-- Planning source: ZetaProduct.lean:477; source-local planning contract. -/
theorem frobeniusIdeal_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] :
    frobeniusIdeal K L ⊤ = 1 := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  rw [frobeniusIdeal, ← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one,
    Multiset.map_zero, Multiset.prod_zero]

end Cox.Chebotarev
