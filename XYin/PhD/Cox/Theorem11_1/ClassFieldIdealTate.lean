/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealDescent
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalNorm
import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-! # Actual ideal norms and Janusz V.2.1(c)

The relative ideal norm is the existing prime-product norm. The group norm and
norm-image comparison are explicit, and the final equivalence has the specified
extended-ideal representative formula.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise
noncomputable section

namespace Cox.CyclicCohomology

/-- Translation by one transporter identifies all transporters with a stabilizer. -/
theorem card_transporter_eq_card_stabilizer {G X : Type*} [Group G]
    [MulAction G X] (x y : X) (h : ∃ g : G, g • x = y) :
    Nat.card {g : G // g • x = y} = Nat.card (MulAction.stabilizer G x) := by
  obtain ⟨t, ht⟩ := h
  exact Nat.card_congr
    { toFun := fun g => ⟨t⁻¹ * g, by
        change (t⁻¹ * (g : G)) • x = x
        rw [mul_smul, g.2, ← ht, inv_smul_smul]⟩
      invFun := fun s => ⟨t * s, by
        rw [mul_smul, show (s : G) • x = x from s.2]
        exact ht⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp) }

end Cox.CyclicCohomology

namespace Cox.ClassFieldTheory
open Cox.CyclicCohomology
variable (K L : Type*) [Field K] [Field L] [hNK : NumberField K] [hNL : NumberField L]
  [Algebra K L]

/-- The actual relative ideal norm restricted to precisely the good fractional ideals. -/
def awayIdealNorm (m : Ideal (𝓞 K)) :
    coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L))) →* coprimeIdeals K m :=
  ((idealUnitNorm K L).comp
    (coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))).subtype).codRestrict
      (coprimeIdeals K m) (fun I ↦ idealUnitNorm_coprime K L m I I.property)

include hNK hNL in
/-- Every integral norm generator is in the range of the specified fractional-ideal norm. -/
theorem normImage_generator_mem_range (m : Ideal (𝓞 K)) (u : coprimeIdeals K m)
    (A : Ideal (𝓞 L)) (hA : A ≠ ⊥)
    (hAm : A ⊔ m.map (algebraMap (𝓞 K) (𝓞 L)) = ⊤)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (Ideal.relNorm (𝓞 K) A : FractionalIdeal (𝓞 K)⁰ K)) :
    u ∈ (awayIdealNorm K L m).range := by
  obtain ⟨J, hJ⟩ := exists_coprimeIdealUnit L (m.map (algebraMap (𝓞 K) (𝓞 L))) A hA hAm
  refine ⟨J, Subtype.ext (Units.ext ?_)⟩
  change (idealUnitNorm K L (J : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [idealUnitNorm_integral K L _ A hJ, hu]

include hNK hNL in
/-- The original integral-generator norm subgroup is exactly the range of this actual norm. -/
theorem awayIdealNorm_range (m : Ideal (𝓞 K)) :
    (awayIdealNorm K L m).range = normImage K m L := by
  apply le_antisymm
  · have key : ∀ (J : (FractionalIdeal (𝓞 L)⁰ L)ˣ)
        (hJ : J ∈ Subgroup.closure (coprimeGenerators L (m.map (algebraMap (𝓞 K) (𝓞 L))))),
        awayIdealNorm K L m ⟨J, hJ⟩ ∈ normImage K m L := by
      intro J hJ
      induction hJ using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨A, hA, hAm, hxA⟩ := hx
        exact Subgroup.subset_closure ⟨A, hA, hAm, idealUnitNorm_integral K L x A hxA⟩
      | one =>
        change awayIdealNorm K L m 1 ∈ normImage K m L
        rw [map_one]
        exact (normImage K m L).one_mem
      | mul x y hx hy ihx ihy =>
        have h := (normImage K m L).mul_mem ihx ihy
        rw [← map_mul] at h
        exact h
      | inv x hx ih =>
        have h := (normImage K m L).inv_mem ih
        rw [← map_inv] at h
        exact h
    rintro _ ⟨⟨J, hJ⟩, rfl⟩
    exact key J hJ
  · refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨A, hA, hAm, hu⟩
    exact normImage_generator_mem_range K L m u A hA hAm hu

include hNK hNL in
/-- The specified spectrum action agrees with the existing action on the underlying ideal. -/
theorem primePermutation_asIdeal_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).asIdeal = σ • w.asIdeal := by
  have hsmul : (σ • w).asIdeal =
      w.asIdeal.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom :=
    primePermutation_asIdeal K L σ w
  rw [hsmul]
  rfl

include hNK hNL in
/-- The two representations of a prime have literally the same stabilizer subgroup. -/
theorem primeStabilizer_eq (w : HeightOneSpectrum (𝓞 L)) :
    MulAction.stabilizer (L ≃ₐ[K] L) w =
      MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    ← primePermutation_asIdeal_smul]
  exact HeightOneSpectrum.ext_iff

variable [hGalois : IsGalois K L]
include hNK hNL hGalois

/-- The prime stabilizer has order e f, with the specified prime rather than
an unspecified choice. -/
theorem primeStabilizer_card (w : HeightOneSpectrum (𝓞 L)) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) =
      Ideal.ramificationIdx (w.under (𝓞 K)).asIdeal w.asIdeal *
        Ideal.inertiaDeg (w.under (𝓞 K)).asIdeal w.asIdeal := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI := prime_liesOver_under K L w
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : (w.under (𝓞 K)).asIdeal.IsMaximal := (w.under (𝓞 K)).isMaximal
  letI := Ideal.Quotient.field (w.under (𝓞 K)).asIdeal
  letI := Ideal.Quotient.field w.asIdeal
  haveI : Algebra.IsSeparable (𝓞 K ⧸ (w.under (𝓞 K)).asIdeal) (𝓞 L ⧸ w.asIdeal) := inferInstance
  rw [primeStabilizer_eq, Ideal.card_stabilizer_eq _ (w.under (𝓞 K)).ne_bot w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg _ w.asIdeal (L ≃ₐ[K] L)]

/-- Transitivity gives exactly e f automorphisms carrying one prime to another in its fiber. -/
theorem primeTransporter_card (w z : HeightOneSpectrum (𝓞 L))
    (h : w.under (𝓞 K) = z.under (𝓞 K)) :
    Nat.card {σ : L ≃ₐ[K] L // σ • w = z} =
      Ideal.ramificationIdx (w.under (𝓞 K)).asIdeal w.asIdeal *
        Ideal.inertiaDeg (w.under (𝓞 K)).asIdeal w.asIdeal := by
  rw [card_transporter_eq_card_stabilizer w z (prime_fiber_transitive K L w z h),
    primeStabilizer_card]

omit hGalois in
/-- The literal product of all Galois conjugates, bundled as a homomorphism. -/
def idealConjugateProduct : (FractionalIdeal (𝓞 L)⁰ L)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  ∏ σ : L ≃ₐ[K] L, idealConjugation K L σ

omit hGalois in
/-- The exponent in the group norm of a prime counts its actual transporters. -/
theorem idealConjugateProduct_prime_count (w z : HeightOneSpectrum (𝓞 L)) :
    FractionalIdeal.count L z (idealConjugateProduct K L (primeIdealUnit L w)) =
      (Nat.card {σ : L ≃ₐ[K] L // σ • w = z} : ℤ) := by
  classical
  rw [idealConjugateProduct, MonoidHom.finsetProd_apply]
  simp only [idealConjugation_prime]
  rw [Units.coe_prod, FractionalIdeal.count_prod L z _ _ (fun σ _ => Units.ne_zero _)]
  simp only [primeIdealUnit_coe]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : σ • w = z
  · rw [h, FractionalIdeal.count_self, if_pos rfl, Nat.cast_one]
  · rw [FractionalIdeal.count_maximal_coprime L z h, if_neg h]

/-- Counting complete prime fibers identifies the group norm of a prime with its extended norm. -/
theorem idealConjugateProduct_prime (w : HeightOneSpectrum (𝓞 L)) :
    idealConjugateProduct K L (primeIdealUnit L w) =
      idealUnitExtension K L (idealUnitNorm K L (primeIdealUnit L w)) := by
  apply Additive.ofMul.injective
  apply (idealExponentEquiv L).injective
  ext z
  rw [idealExponentEquiv_apply, idealExponentEquiv_apply, toMul_ofMul, toMul_ofMul,
    idealConjugateProduct_prime_count, idealExtension_count, idealUnitNorm_prime,
    Units.val_pow_eq_pow_val, primeIdealUnit_coe, FractionalIdeal.count_pow]
  by_cases h : w.under (𝓞 K) = z.under (𝓞 K)
  · obtain ⟨τ, hτ⟩ := prime_fiber_transitive K L w z h
    rw [primeTransporter_card K L w z h, ← h, FractionalIdeal.count_self, mul_one, ← hτ,
      ramificationIdx_primePermutation]
    push_cast
    ring
  · have h0 : Nat.card {σ : L ≃ₐ[K] L // σ • w = z} = 0 := by
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun ⟨σ, hσ⟩ => h (by rw [← hσ, primePermutation_under])⟩
    rw [h0, FractionalIdeal.count_maximal_coprime K (z.under (𝓞 K)) h]
    simp

/-- Agreement on prime powers gives the norm identity on all fractional-ideal units. -/
theorem idealConjugateProduct_eq (I : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    idealConjugateProduct K L I = idealUnitExtension K L (idealUnitNorm K L I) := by
  rw [← exponentIdealProduct_idealExponentVector L I]
  generalize idealExponentVector L I = e
  induction e using Finsupp.induction with
  | zero => rw [exponentIdealProduct, Finsupp.prod_zero_index, map_one, map_one, map_one]
  | single_add a b f _ _ ih =>
    have hsingle : exponentIdealProduct L (Finsupp.single a b) = primeIdealUnit L a ^ b := by
      rw [exponentIdealProduct, Finsupp.prod_single_index (zpow_zero _)]
    simp only [exponentIdealProduct_add, map_mul, hsingle, map_zpow, ih,
      idealConjugateProduct_prime]

omit hGalois in
/-- The additive representation norm is this same product of conjugate ideals. -/
theorem idealRepresentation_norm (I : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    (idealRepresentation K L).norm (Additive.ofMul I) =
      Additive.ofMul (idealConjugateProduct K L I) := by
  apply Additive.toMul.injective
  rw [Representation.norm, LinearMap.sum_apply, toMul_sum, toMul_ofMul, idealConjugateProduct,
    MonoidHom.finsetProd_apply]
  exact Finset.prod_congr rfl fun σ _ => idealRepresentation_apply K L σ I

/-- The norm on the good-ideal module is the actual extension of the relative norm. -/
theorem awayIdeal_norm_formula (m : Ideal (𝓞 K)) (I : awayIdealSubmodule K L m) :
    (awayIdealRepresentation K L m).norm I =
      awayIdealExtension K L m (Additive.ofMul
        (awayIdealNorm K L m ⟨I.val.toMul, I.property⟩)) := by
  apply Subtype.ext
  have h1 := intertwining_norm _ (idealRepresentation K L)
    (submoduleIntertwining (idealRepresentation K L) (awayIdealSubmodule K L m)
      (awayIdealSubmodule_stable K L m)) I
  have h2 := idealRepresentation_norm K L
    (Additive.toMul (I : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ))
  rw [ofMul_toMul, idealConjugateProduct_eq] at h2
  exact h1.trans h2

/-- Invariant descent carries the actual norm submodule to the original norm-image subgroup. -/
theorem fixedIdealsEquiv_normRange (m : Ideal (𝓞 K)) (hU : IsUnramifiedAway K m L)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    ((LinearMap.range (awayIdealRepresentation K L m).norm).comap
      (LinearMap.ker (awayIdealRepresentation K L m σ - LinearMap.id)).subtype).map
        (fixedIdealsEquiv K L m hU σ hσ).toLinearMap =
      (normImage K m L).toAddSubgroup.toIntSubmodule := by
  ext k
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨y, hy⟩ := ha
    have ha' : a = fixedIdealMap K L m σ (Additive.ofMul
        (awayIdealNorm K L m ⟨(y : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ).toMul, y.property⟩)) :=
      Subtype.ext (hy.symm.trans (awayIdeal_norm_formula K L m y))
    rw [ha']
    change fixedIdealsEquiv K L m hU σ hσ (fixedIdealMap K L m σ _) ∈ _
    rw [fixedIdealsEquiv_apply]
    have hmem : awayIdealNorm K L m
        ⟨(y : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ).toMul, y.property⟩ ∈
          (awayIdealNorm K L m).range := ⟨_, rfl⟩
    rw [awayIdealNorm_range] at hmem
    exact hmem
  · intro hk
    have hk' : Additive.toMul k ∈ (awayIdealNorm K L m).range := by
      rw [awayIdealNorm_range]
      exact hk
    obtain ⟨J, hJ⟩ := hk'
    refine ⟨fixedIdealMap K L m σ k, Submodule.mem_comap.mpr (LinearMap.mem_range.mpr
      ⟨⟨Additive.ofMul (J : (FractionalIdeal (𝓞 L)⁰ L)ˣ), J.2⟩, ?_⟩),
      fixedIdealsEquiv_apply K L m hU σ hσ k⟩
    rw [awayIdeal_norm_formula]
    change awayIdealExtension K L m (Additive.ofMul (awayIdealNorm K L m J)) =
      awayIdealExtension K L m k
    rw [hJ]
    rfl

/-- The actual quotient equivalence induced by invariant ideal descent and norm transport. -/
def awayIdealTateEquiv (m : Ideal (𝓞 K))
    (hU : IsUnramifiedAway K m L) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    tateZero (awayIdealRepresentation K L m) σ ≃+
      Additive (coprimeIdeals K m ⧸ normImage K m L) :=
  (Submodule.Quotient.equiv _ _ (fixedIdealsEquiv K L m hU σ hσ)
    (fixedIdealsEquiv_normRange K L m hU σ hσ)).toAddEquiv.trans
      (additiveIntQuotientEquiv (normImage K m L))

/-- Extended ideals have exactly the required base-ideal classes under the Tate identification. -/
theorem awayIdealTateEquiv_apply (m : Ideal (𝓞 K))
    (hU : IsUnramifiedAway K m L) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (I : coprimeIdeals K m)
    (a : LinearMap.ker (awayIdealRepresentation K L m σ - LinearMap.id))
    (ha : a.val.val.toMul = idealUnitExtension K L I) :
    awayIdealTateEquiv K L m hU σ hσ (zeroClass _ σ a) =
      Additive.ofMul (QuotientGroup.mk I) := by
  have ha' : a = fixedIdealMap K L m σ (Additive.ofMul I) := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Additive.ofMul ha
  subst ha'
  change Submodule.Quotient.mk
    (fixedIdealsEquiv K L m hU σ hσ (fixedIdealMap K L m σ (Additive.ofMul I))) = _
  rw [fixedIdealsEquiv_apply]
  rfl

/-- Janusz V.2.1(c), preserving the public extension-of-fractional-ideals
representative condition. -/
theorem exists_awayIdealTateEquiv (m : Ideal (𝓞 K))
    (hU : IsUnramifiedAway K m L) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    ∃ e : tateZero (awayIdealRepresentation K L m) σ ≃+
        Additive (coprimeIdeals K m ⧸ normImage K m L),
      ∀ (I : coprimeIdeals K m)
        (a : LinearMap.ker (awayIdealRepresentation K L m σ - LinearMap.id)),
        Additive.toMul ((a : awayIdealSubmodule K L m) :
            Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ) =
          Units.map (FractionalIdeal.extendedHom L (𝓞 L)).toMonoidHom
            (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) →
        e (zeroClass _ σ a) = Additive.ofMul (QuotientGroup.mk I) := by
  exact ⟨awayIdealTateEquiv K L m hU σ hσ,
    fun I a ha => awayIdealTateEquiv_apply K L m hU σ hσ I a ha⟩

end Cox.ClassFieldTheory
