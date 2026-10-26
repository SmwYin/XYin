/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormIdeals
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinPrimes

/-! # A prime norm acts trivially under Artin

This is the prime calculation of Janusz III.3.1 specialized to E=L, as in
III.3.2. The supplied representatives are kept explicit.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory

/-- The Artin value of a prime norm is one because the Frobenius order is its residue degree. -/
theorem artin_prime_norm_eq_one
    (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [Module.Finite (𝓞 K) (𝓞 L)] [IsGalois K L]
    (hU : IsUnramifiedAway K m L)
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K m L φ)
    {q : Ideal (𝓞 K)} (hq : q.IsPrime) (hq0 : q ≠ ⊥) (hqm : q ⊔ m = ⊤)
    (u : coprimeIdeals K m)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q)
    (P : Ideal (𝓞 L)) (hP : P ∈ q.primesOver (𝓞 L))
    (uN : coprimeIdeals K m)
    (huN : ((uN : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (Ideal.relNorm (𝓞 K) P : FractionalIdeal (𝓞 K)⁰ K)) : φ uN = 1 := by
  haveI : q.IsPrime := hq
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver q := hP.2
  haveI : q.IsMaximal := hq.isMaximal hq0
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hq0 P
  haveI : P.IsMaximal := hP.1.isMaximal hP0
  have hN : Ideal.relNorm (𝓞 K) P = q ^ Ideal.inertiaDeg q P :=
    Ideal.relNorm_eq_pow_of_isMaximal P q
  have huN' : uN = u ^ Ideal.inertiaDeg q P := by
    apply Subtype.ext
    apply Units.ext
    rw [huN, hN, FractionalIdeal.coeIdeal_pow]
    simp [hu]
  rw [huN', map_pow, ← orderOf_artin_eq_inertiaDeg K m L hU φ hφ hq hq0 hqm u hu P hP,
    pow_orderOf_eq_one]

end Cox.ClassFieldTheory
