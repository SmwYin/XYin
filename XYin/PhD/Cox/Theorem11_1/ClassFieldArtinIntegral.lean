/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinNormPrimes
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinFrobeniusMap
import XYin.PhD.Cox.Theorem11_1.ClassFieldTheory
import XYin.PhD.Cox.Theorem11_1.ChebotarevIdealFrobenius

/-! # Integral ideal products under Artin

These contracts implement the multiplicative extension in Janusz III.3.1–3.2.
The generic induction is shared by the Frobenius-ideal comparison and the integral-norm
calculation.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors IsMulCommutative
noncomputable section
namespace Cox.ClassFieldTheory

/-- Induction on nonzero integral ideals prime to a modulus, retaining that condition on factors. -/
theorem ideal_coprime_induction
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (m : Ideal R) (Q : Ideal R → Prop) (h1 : Q ⊤)
    (hprime : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ → P ⊔ m = ⊤ → Q P)
    (hmul : ∀ A B : Ideal R, A ≠ ⊥ → B ≠ ⊥ → A ⊔ m = ⊤ → B ⊔ m = ⊤ →
      Q A → Q B → Q (A * B))
    (A : Ideal R) (hA : A ≠ ⊥) (hAm : A ⊔ m = ⊤) : Q A := by
  refine UniqueFactorizationMonoid.induction_on_prime (P := fun A => A ≠ ⊥ → A ⊔ m = ⊤ → Q A)
    A ?_ ?_ ?_ hA hAm
  · exact fun h _ => (h Ideal.zero_eq_bot).elim
  · intro x hx _ _
    rw [Ideal.isUnit_iff.mp hx]
    exact h1
  · intro a p ha hp ih hpa hpam
    have hp0 : p ≠ ⊥ := hp.ne_zero
    have hpm : p ⊔ m = ⊤ := top_unique (hpam ▸ sup_le_sup_right Ideal.mul_le_right m)
    have ham : a ⊔ m = ⊤ := top_unique (hpam ▸ sup_le_sup_right Ideal.mul_le_left m)
    exact hmul p a hp0 ha hpm ham (hprime p (Ideal.isPrime_of_prime hp) hp0 hpm) (ih ha ham)

/-- A supplied Artin map agrees with the existing product of Frobenius values on integral ideals. -/
theorem artin_eq_frobeniusIdeal
    (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (hU : IsUnramifiedAway K m L)
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K m L φ)
    (A : Ideal (𝓞 K)) (hA : A ≠ ⊥) (hAm : A ⊔ m = ⊤)
    (u : coprimeIdeals K m)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = A) :
    φ u = Chebotarev.frobeniusIdeal K L A := by
  have heq : φ = arithmeticArtin K m L :=
    isArtinMap_unique K m L hU hφ (arithmeticArtin_isArtinMap K m L hU)
  subst heq
  revert u
  refine ideal_coprime_induction m (fun A => ∀ u : coprimeIdeals K m,
      ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = A →
        arithmeticArtin K m L u = Chebotarev.frobeniusIdeal K L A) ?_ ?_ ?_ A hA hAm
  · intro u hu
    have h1 : u = 1 := Subtype.ext (Units.ext (by rw [hu, FractionalIdeal.coeIdeal_top]; rfl))
    rw [h1, map_one, Chebotarev.frobeniusIdeal_one]
  · intro P hP hP0 _ u hu
    haveI := hP
    rw [arithmeticArtin_prime K m L P hP hP0 u hu, Chebotarev.frobeniusIdeal_apply_prime K L P hP0]
  · intro B C hB hC hBm hCm ihB ihC u hu
    obtain ⟨uB, huB⟩ := exists_coprimeIdealUnit K m B hB hBm
    obtain ⟨uC, huC⟩ := exists_coprimeIdealUnit K m C hC hCm
    have h1 : u = uB * uC := Subtype.ext (Units.ext (by
      rw [hu, Subgroup.coe_mul, Units.val_mul, huB, huC, FractionalIdeal.coeIdeal_mul]))
    rw [h1, map_mul, ihB uB huB, ihC uC huC, Chebotarev.frobeniusIdeal_mul K L hB hC]

/-- The Artin value of a nonzero integral norm prime to the modulus is one. -/
theorem artin_integral_norm_eq_one
    (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [Module.Finite (𝓞 K) (𝓞 L)] [IsGalois K L]
    (hU : IsUnramifiedAway K m L)
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K m L φ)
    (A : Ideal (𝓞 L)) (hA : A ≠ ⊥)
    (hAm : A ⊔ m.map (algebraMap (𝓞 K) (𝓞 L)) = ⊤)
    (uN : coprimeIdeals K m)
    (huN : ((uN : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (Ideal.relNorm (𝓞 K) A : FractionalIdeal (𝓞 K)⁰ K)) : φ uN = 1 := by
  revert uN
  refine ideal_coprime_induction (m.map (algebraMap (𝓞 K) (𝓞 L))) (fun A =>
      ∀ uN : coprimeIdeals K m,
        ((uN : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
          (Ideal.relNorm (𝓞 K) A : FractionalIdeal (𝓞 K)⁰ K) → φ uN = 1) ?_ ?_ ?_ A hA hAm
  · intro uN huN
    have h1 : uN = 1 := Subtype.ext (Units.ext (by
      rw [huN, Ideal.relNorm_top, FractionalIdeal.coeIdeal_top]
      rfl))
    rw [h1, map_one]
  · intro P hP hP0 hPm uN huN
    haveI := hP
    have hq : (P.under (𝓞 K)).IsPrime := Ideal.IsPrime.under (𝓞 K) P
    have hq0 : P.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot (A := 𝓞 K) hP0
    have hqm := under_coprime K L m P hPm
    obtain ⟨u, hu⟩ := exists_coprimeIdealUnit K m _ hq0 hqm
    exact artin_prime_norm_eq_one K m L hU φ hφ hq hq0 hqm u hu P ⟨hP, ⟨rfl⟩⟩ uN huN
  · intro B C hB hC hBm hCm ihB ihC uN huN
    obtain ⟨uB, huB⟩ := exists_coprime_relNorm_unit K L m B hB hBm
    obtain ⟨uC, huC⟩ := exists_coprime_relNorm_unit K L m C hC hCm
    have h1 : uN = uB * uC := Subtype.ext (Units.ext (by
      rw [huN, Subgroup.coe_mul, Units.val_mul, huB, huC, map_mul,
        FractionalIdeal.coeIdeal_mul]))
    rw [h1, map_mul, ihB uB huB, ihC uC huC, mul_one]

end Cox.ClassFieldTheory
