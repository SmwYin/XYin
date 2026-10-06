/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormApproximation

/-! # Finite support in Janusz V.3.10

The product of distinct prime powers has precisely the prescribed support at
positive depth.
-/
open NumberField IsDedekindDomain
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

-- `[NumberField K]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- A product of nonzero prime powers is nonzero, including empty support. -/
theorem supportModulus_ne_bot (S : Finset (HeightOneSpectrum (𝓞 K))) (t : ℕ) :
    supportModulus K S t ≠ ⊥ := by
  rw [supportModulus, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  intro v _
  exact pow_ne_zero _ (by rw [Ne, Ideal.zero_eq_bot]; exact v.ne_bot)

/-- Positive depth preserves exactly the prescribed prime support. -/
theorem supportModulus_le_prime_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t : ℕ) (ht : 0 < t) (v : HeightOneSpectrum (𝓞 K)) :
    supportModulus K S t ≤ v.asIdeal ↔ v ∈ S := by
  rw [supportModulus, Ideal.IsPrime.prod_le v.isPrime]
  constructor
  · rintro ⟨w, hw, hle⟩
    rw [Ideal.IsPrime.pow_le_iff (hP := v.isPrime) ht.ne'] at hle
    have hwv : w = v := HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hle)
    exact hwv ▸ hw
  · intro hv
    exact ⟨v, hv, Ideal.pow_le_self ht.ne'⟩

-- `[NumberField K]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Increasing the common exponent gives a more divisible ideal modulus. -/
theorem supportModulus_antitone (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Antitone (supportModulus K S) := by
  intro s t hst
  unfold supportModulus
  exact Finset.prod_le_prod' fun v _ => Ideal.pow_le_pow_right hst

/-- A new prime power is coprime to a supported modulus on the other primes. -/
theorem prime_power_coprime_supportModulus (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (s t : ℕ) :
    v.asIdeal ^ s ⊔ supportModulus K S t = ⊤ := by
  rw [← Ideal.isCoprime_iff_sup_eq, supportModulus]
  exact IsCoprime.prod_right fun w hw =>
    HeightOneSpectrum.isCoprime_pow_of_ne v w (fun h => hv (h ▸ hw)) s t

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]
variable [hGalois : IsGalois K L]
include hGalois

omit hGalois in
/-- Iterating the coprime-modulus formula gives the element-norm product. -/
theorem elementNormRay_index_support_product
    (S : Finset (HeightOneSpectrum (𝓞 K))) (t : ℕ) :
    (elementNormGroup K L ⊔ rayElements K (supportModulus K S t)).index =
      ∏ v ∈ S, (elementNormGroup K L ⊔ rayElements K (v.asIdeal ^ t)).index := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [supportModulus, Finset.prod_empty, Ideal.one_eq_top, rayElements_top, sup_top_eq,
      Subgroup.index_top]
  | insert v S hv ih =>
    rw [Finset.prod_insert hv, ← ih]
    have h1 : supportModulus K (insert v S) t = v.asIdeal ^ t * supportModulus K S t := by
      rw [supportModulus, Finset.prod_insert hv]
      rfl
    have hv0 : v.asIdeal ^ t ≠ ⊥ := by
      simpa only [Ideal.zero_eq_bot] using pow_ne_zero t
        (show v.asIdeal ≠ 0 by simpa only [Ideal.zero_eq_bot] using v.ne_bot)
    rw [h1]
    exact elementNormRay_index_mul K L _ _ hv0 (supportModulus_ne_bot K S t)
      (prime_power_coprime_supportModulus K S v hv t t)

omit hGalois [NumberField L] in
/-- The source's finite product is the actual finitely supported degree product. -/
theorem localDegreeProduct_supportModulus (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t : ℕ) (ht : 0 < t) :
    localDegreeProduct K L (supportModulus K S t) =
      ∏ v ∈ S, v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) := by
  rw [localDegreeProduct, finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
  · refine Finset.prod_congr rfl fun v hv => ?_
    rw [if_pos ((supportModulus_le_prime_iff K S t ht v).mpr hv)]
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    by_contra hvS
    exact hv (if_neg (mt (supportModulus_le_prime_iff K S t ht v).mp hvS))

end Cox.ClassFieldTheory
