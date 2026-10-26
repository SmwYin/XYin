/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArithmetic

/-! # The explicit fractional norm used in Janusz V.11.2
The norm is the finite product of prime powers with residue-degree weights.
This module is below class-field existence; no reciprocity theorem is assumed.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K E : Type*) [Field K] [hNF_K : NumberField K] [Field E] [hNF_E : NumberField E]
  [Algebra K E]

/-- The relative ideal norm on units, calculated from their finite prime-exponent vectors. -/
def idealUnitNormFun (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (idealExponentVector E I).prod fun v n ↦
    primeIdealUnit K (v.under (𝓞 K)) ^
      ((Ideal.inertiaDeg (v.under (𝓞 K)).asIdeal v.asIdeal : ℤ) * n)

include hNF_K hNF_E in
/-- The zero exponent vector gives norm one. -/
theorem idealUnitNormFun_one : idealUnitNormFun K E 1 = 1 := by
  have h0 : idealExponentVector E 1 = 0 := by
    ext v
    rw [idealExponentVector_apply, Units.val_one, FractionalIdeal.count_one]
    rfl
  rw [idealUnitNormFun, h0, Finsupp.prod_zero_index]

include hNF_K hNF_E in
/-- Additivity of prime exponents gives multiplicativity of the relative norm. -/
theorem idealUnitNormFun_mul (I J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    idealUnitNormFun K E (I * J) = idealUnitNormFun K E I * idealUnitNormFun K E J := by
  rw [idealUnitNormFun, idealUnitNormFun, idealUnitNormFun, idealExponentVector_mul,
    Finsupp.prod_add_index']
  · intro v
    simp
  · intro v a b
    rw [mul_add, zpow_add]

/-- The actual relative fractional-ideal norm homomorphism. -/
def idealUnitNorm : (FractionalIdeal (𝓞 E)⁰ E)ˣ →* (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  toFun := idealUnitNormFun K E
  map_one' := idealUnitNormFun_one K E
  map_mul' := idealUnitNormFun_mul K E

include hNF_K hNF_E in
/-- On a prime ideal the relative norm is the lower prime to the residue degree. -/
theorem idealUnitNorm_prime (v : HeightOneSpectrum (𝓞 E)) :
    idealUnitNorm K E (primeIdealUnit E v) =
      primeIdealUnit K (v.under (𝓞 K)) ^
        Ideal.inertiaDeg (v.under (𝓞 K)).asIdeal v.asIdeal := by
  classical
  have hvec : idealExponentVector E (primeIdealUnit E v) = Finsupp.single v 1 := by
    ext w
    rw [idealExponentVector_apply, primeIdealUnit_coe]
    by_cases h : v = w
    · subst h
      rw [FractionalIdeal.count_self, Finsupp.single_eq_same]
    · rw [FractionalIdeal.count_maximal_coprime E w h, Finsupp.single_eq_of_ne (Ne.symm h)]
  change idealUnitNormFun K E _ = _
  rw [idealUnitNormFun, hvec, Finsupp.prod_single_index (by simp), mul_one, zpow_natCast]

include hNF_K hNF_E in
/-- The prime factor step for the integral comparison of ideal norms. -/
theorem idealUnitNorm_integral_prime_step [Module.Finite (𝓞 K) (𝓞 E)]
    (p a : Ideal (𝓞 E)) (hpp : p.IsPrime) (hp0 : p ≠ ⊥)
    (ih : ∀ J : (FractionalIdeal (𝓞 E)⁰ E)ˣ, (J : FractionalIdeal (𝓞 E)⁰ E) = a →
      (idealUnitNorm K E J : FractionalIdeal (𝓞 K)⁰ K) = Ideal.relNorm (𝓞 K) a)
    (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (hI : (I : FractionalIdeal (𝓞 E)⁰ E) = (p * a : Ideal _)) :
    (idealUnitNorm K E I : FractionalIdeal (𝓞 K)⁰ K) = Ideal.relNorm (𝓞 K) (p * a) := by
  haveI : CharZero (FractionRing (𝓞 K)) := charZero_of_injective_algebraMap
    (IsFractionRing.injective (𝓞 K) (FractionRing (𝓞 K)))
  let w : HeightOneSpectrum (𝓞 E) := ⟨p, hpp, hp0⟩
  have hJ : ((I * (primeIdealUnit E w)⁻¹ : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
      FractionalIdeal (𝓞 E)⁰ E) = a := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, primeIdealUnit_coe, hI,
      FractionalIdeal.coeIdeal_mul, mul_comm (p : FractionalIdeal (𝓞 E)⁰ E),
      mul_inv_cancel_right₀ (FractionalIdeal.coeIdeal_ne_zero.mpr hp0)]
  have hIJ : I = primeIdealUnit E w * (I * (primeIdealUnit E w)⁻¹) := by
    rw [mul_comm I, mul_inv_cancel_left]
  haveI : p.IsMaximal := hpp.isMaximal hp0
  haveI : (p.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) p
  rw [hIJ, map_mul, Units.val_mul, ih _ hJ, idealUnitNorm_prime, Units.val_pow_eq_pow_val,
    primeIdealUnit_coe, map_mul, FractionalIdeal.coeIdeal_mul,
    Ideal.relNorm_eq_pow_of_isMaximal p (p.under (𝓞 K)), FractionalIdeal.coeIdeal_pow]
  rfl

include hNF_K hNF_E in
/-- On integral ideals the prime-product norm agrees with the pinned relative ideal norm. -/
theorem idealUnitNorm_integral [Module.Finite (𝓞 K) (𝓞 E)]
    (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (A : Ideal (𝓞 E))
    (hI : (I : FractionalIdeal (𝓞 E)⁰ E) = A) :
    (idealUnitNorm K E I : FractionalIdeal (𝓞 K)⁰ K) = Ideal.relNorm (𝓞 K) A := by
  haveI : CharZero (FractionRing (𝓞 K)) := charZero_of_injective_algebraMap
    (IsFractionRing.injective (𝓞 K) (FractionRing (𝓞 K)))
  induction A using UniqueFactorizationMonoid.induction_on_prime generalizing I with
  | h₁ =>
    exact absurd (hI.trans (by rw [Ideal.zero_eq_bot, FractionalIdeal.coeIdeal_bot])) I.ne_zero
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.mp hx] at hI ⊢
    have h1 : I = 1 := Units.ext (by rw [hI, FractionalIdeal.coeIdeal_top, Units.val_one])
    rw [h1, map_one, Units.val_one, Ideal.relNorm_top, FractionalIdeal.coeIdeal_top]
  | h₃ a p _ hp ih =>
    exact idealUnitNorm_integral_prime_step K E p a (Ideal.isPrime_of_prime hp) hp.ne_zero ih I hI

include hNF_K hNF_E in
/-- On principal fractional ideals the ideal norm is generated by the field norm. -/
theorem idealUnitNorm_principal [Module.Finite (𝓞 K) (𝓞 E)] (u : Eˣ) :
    idealUnitNorm K E (toPrincipalIdeal (𝓞 E) E u) =
      toPrincipalIdeal (𝓞 K) K (Units.map (Algebra.norm K) u) := by
  have hint : ∀ (a : 𝓞 E) (ha : (a : E) ≠ 0),
      idealUnitNorm K E (toPrincipalIdeal (𝓞 E) E (Units.mk0 (a : E) ha)) =
        toPrincipalIdeal (𝓞 K) K (Units.map (Algebra.norm K) (Units.mk0 (a : E) ha)) := by
    intro a ha
    apply Units.ext
    rw [idealUnitNorm_integral K E _ (Ideal.span {a}) (by
        rw [coe_toPrincipalIdeal, Units.val_mk0, FractionalIdeal.coeIdeal_span_singleton]),
      Ideal.relNorm_singleton, FractionalIdeal.coeIdeal_span_singleton, coe_toPrincipalIdeal,
      Units.coe_map, Units.val_mk0,
      Algebra.algebraMap_intNorm (A := 𝓞 K) (B := 𝓞 E) (K := K) (L := E)]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (u : E)
  have hb0 : (b : E) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr
    (nonZeroDivisors.ne_zero hb)
  have ha0 : (a : E) ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [← hab]
    change (a : E) / b = 0
    rw [h, zero_div]
  have hu : u = Units.mk0 (a : E) ha0 * (Units.mk0 (b : E) hb0)⁻¹ := Units.ext (by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, ← div_eq_mul_inv]
    exact hab.symm)
  rw [hu]
  simp only [map_mul, map_inv, hint]

include hNF_K hNF_E in
/-- Relative norm takes ideals avoiding the extended modulus to ideals avoiding the base modulus. -/
theorem idealUnitNorm_coprime (m : Ideal (𝓞 K)) (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hI : I ∈ coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E)))) :
    idealUnitNorm K E I ∈ coprimeIdeals K m := by
  rw [coprimeIdeals_eq_primeGeneratedGroup] at hI ⊢
  have hle : primeGeneratedGroup E {w | ¬m.map (algebraMap (𝓞 K) (𝓞 E)) ≤ w.asIdeal} ≤
      (primeGeneratedGroup K {v | ¬m ≤ v.asIdeal}).comap (idealUnitNorm K E) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, idealUnitNorm_prime]
    have hmem : primeIdealUnit K (w.under (𝓞 K)) ∈ primeGeneratedGroup K {v | ¬m ≤ v.asIdeal} :=
      Subgroup.subset_closure ⟨w.under (𝓞 K), fun hm => hw (Ideal.map_le_iff_le_comap.mpr hm),
        rfl⟩
    exact Subgroup.pow_mem _ hmem _
  exact hle hI

include hNF_K hNF_E in
/-- Relative norm takes ideals supported over a modulus to ideals supported on that modulus. -/
theorem idealUnitNorm_supported (m : Ideal (𝓞 K)) (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hI : I ∈ modulusSupportedIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E)))) :
    idealUnitNorm K E I ∈ modulusSupportedIdeals K m := by
  rw [modulusSupportedIdeals_eq_primeGeneratedGroup] at hI ⊢
  have hle : primeGeneratedGroup E {w | m.map (algebraMap (𝓞 K) (𝓞 E)) ≤ w.asIdeal} ≤
      (primeGeneratedGroup K {v | m ≤ v.asIdeal}).comap (idealUnitNorm K E) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, idealUnitNorm_prime]
    have hmem : primeIdealUnit K (w.under (𝓞 K)) ∈ primeGeneratedGroup K {v | m ≤ v.asIdeal} :=
      Subgroup.subset_closure ⟨w.under (𝓞 K), Ideal.map_le_iff_le_comap.mp hw, rfl⟩
    exact Subgroup.pow_mem _ hmem _
  exact hle hI

include hNF_K hNF_E in
/-- Deleting modulus-prime factors commutes with the norm. -/
theorem idealUnitNorm_erase (m : Ideal (𝓞 K)) (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    idealUnitNorm K E
      (eraseModulusFactors E (m.map (algebraMap (𝓞 K) (𝓞 E))) I) =
        (eraseModulusFactors K m (idealUnitNorm K E I) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
  have hs := eraseModulusFactors_spec E (m.map (algebraMap (𝓞 K) (𝓞 E))) I
  set j := eraseModulusFactors E (m.map (algebraMap (𝓞 K) (𝓞 E))) I with hj
  have hNj : idealUnitNorm K E (j : (FractionalIdeal (𝓞 E)⁰ E)ˣ) ∈ coprimeIdeals K m :=
    idealUnitNorm_coprime K E m _ j.2
  have hNs := idealUnitNorm_supported K E m _ hs
  have hI : I = (I * (j : (FractionalIdeal (𝓞 E)⁰ E)ˣ)⁻¹) * j := (inv_mul_cancel_right I _).symm
  conv_rhs => rw [hI, map_mul, map_mul, eraseModulusFactors_supported K m _ hNs, one_mul]
  rw [show idealUnitNorm K E (j : (FractionalIdeal (𝓞 E)⁰ E)ˣ) =
      ((⟨_, hNj⟩ : coprimeIdeals K m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) from rfl,
    eraseModulusFactors_coprime]

include hNF_K hNF_E in
/-- This norm of a good fractional ideal belongs to the earlier represented norm-image group. -/
theorem idealUnitNorm_mem_normImage [Module.Finite (𝓞 K) (𝓞 E)]
    (m : Ideal (𝓞 K)) (I : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E)))) :
    (⟨idealUnitNorm K E I, idealUnitNorm_coprime K E m I I.property⟩ : coprimeIdeals K m) ∈
      normImage K m E := by
  obtain ⟨A, B, hA, hB, hAm, hBm, hAB⟩ :=
    exists_coprime_integral_fraction E (m.map (algebraMap (𝓞 K) (𝓞 E))) I
  obtain ⟨uA, huA⟩ := exists_coprimeIdealUnit E _ A hA hAm
  obtain ⟨uB, huB⟩ := exists_coprimeIdealUnit E _ B hB hBm
  have hIu : (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) * uB = uA := Units.ext (by
    rw [Units.val_mul, huB, huA, hAB,
      div_mul_cancel₀ _ (FractionalIdeal.coeIdeal_ne_zero.mpr hB)])
  have hgA : (⟨idealUnitNorm K E uA, idealUnitNorm_coprime K E m uA uA.2⟩ :
      coprimeIdeals K m) ∈ normImage K m E :=
    Subgroup.subset_closure ⟨A, hA, hAm, idealUnitNorm_integral K E _ A huA⟩
  have hgB : (⟨idealUnitNorm K E uB, idealUnitNorm_coprime K E m uB uB.2⟩ :
      coprimeIdeals K m) ∈ normImage K m E :=
    Subgroup.subset_closure ⟨B, hB, hBm, idealUnitNorm_integral K E _ B huB⟩
  have heq : (⟨idealUnitNorm K E I, idealUnitNorm_coprime K E m I I.property⟩ :
      coprimeIdeals K m) =
        ⟨idealUnitNorm K E uA, idealUnitNorm_coprime K E m uA uA.2⟩ *
          (⟨idealUnitNorm K E uB, idealUnitNorm_coprime K E m uB uB.2⟩ : coprimeIdeals K m)⁻¹ := by
    apply Subtype.ext
    change idealUnitNorm K E I = idealUnitNorm K E uA * (idealUnitNorm K E uB)⁻¹
    rw [← hIu, map_mul, mul_inv_cancel_right]
  rw [heq]
  exact (normImage K m E).mul_mem hgA ((normImage K m E).inv_mem hgB)

include hNF_K hNF_E in
/-- The prime residue-degree tower formula makes fractional ideal norms transitive. -/
theorem idealUnitNorm_tower (F : Type*) [Field F] [hNF_F : NumberField F]
    [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    idealUnitNorm K E (idealUnitNorm E F I) = idealUnitNorm K F I := by
  have key : ∀ w : HeightOneSpectrum (𝓞 F),
      idealUnitNorm K E (idealUnitNorm E F (primeIdealUnit F w)) =
        idealUnitNorm K F (primeIdealUnit F w) := by
    intro w
    rw [idealUnitNorm_prime E F w, map_pow, idealUnitNorm_prime K E, idealUnitNorm_prime K F,
      ← pow_mul]
    have hunder : (w.under (𝓞 E)).under (𝓞 K) = w.under (𝓞 K) :=
      HeightOneSpectrum.ext (Ideal.under_under w.asIdeal)
    haveI : (w.under (𝓞 K)).asIdeal.IsMaximal := (w.under (𝓞 K)).isMaximal
    haveI : (w.under (𝓞 E)).asIdeal.IsMaximal := (w.under (𝓞 E)).isMaximal
    haveI : w.asIdeal.LiesOver (w.under (𝓞 E)).asIdeal := ⟨rfl⟩
    haveI : (w.under (𝓞 E)).asIdeal.LiesOver (w.under (𝓞 K)).asIdeal :=
      ⟨(Ideal.under_under w.asIdeal).symm⟩
    rw [hunder, Ideal.inertiaDeg_algebra_tower (w.under (𝓞 K)).asIdeal
      (w.under (𝓞 E)).asIdeal w.asIdeal]
  rw [← exponentIdealProduct_idealExponentVector F I]
  simp only [exponentIdealProduct, map_finsuppProd, map_zpow]
  exact Finsupp.prod_congr fun w _ => by rw [key]

include hNF_K hNF_E in
/-- Erasure removes the supported term from the source factorization X=B^q(α)C. -/
theorem erase_norm_paired_product (m : Ideal (𝓞 K)) (q : ℕ)
    (B C : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (u : Eˣ)
    (hC : C ∈ modulusSupportedIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))))
    [Module.Finite (𝓞 K) (𝓞 E)] :
    eraseModulusFactors K m
      (idealUnitNorm K E (B ^ q * toPrincipalIdeal (𝓞 E) E u * C)) =
        eraseModulusFactors K m (idealUnitNorm K E B) ^ q *
          eraseModulusFactors K m
            (toPrincipalIdeal (𝓞 K) K (Units.map (Algebra.norm K) u)) := by
  simp only [map_mul, map_pow, idealUnitNorm_principal,
    eraseModulusFactors_supported K m _ (idealUnitNorm_supported K E m C hC), mul_one]

end Cox.ClassFieldTheory
