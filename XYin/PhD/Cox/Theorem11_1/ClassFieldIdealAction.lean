/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealGroups
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
# The actual ideal and prime actions in Janusz V.2

Conjugation and its prime-exponent coordinates live below the supported and S-unit representations.
Principal ideals transform by the specified field automorphism, and extension of a base modulus is
invariant. No Galois hypothesis is used here.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- Conjugation of a fractional ideal, induced by the automorphism of integer rings. -/
def idealConjugation (σ : L ≃ₐ[K] L) :
    (FractionalIdeal (𝓞 L)⁰ L)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  Units.map (FractionalIdeal.ringEquivOfRingEquiv L L
    (RingOfIntegers.mapRingEquiv σ.toRingEquiv)).toMonoidHom

-- `[NumberField K]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Identity field conjugation induces the identity on fractional-ideal units. -/
theorem idealConjugation_one :
    idealConjugation K L 1 = MonoidHom.id (FractionalIdeal (𝓞 L)⁰ L)ˣ := by
  have h : RingOfIntegers.mapRingEquiv (1 : L ≃ₐ[K] L).toRingEquiv = RingEquiv.refl (𝓞 L) := by
    ext x
    rfl
  ext I
  simp only [idealConjugation, h, FractionalIdeal.ringEquivOfRingEquiv_refl, Units.coe_map,
    MonoidHom.id_apply]
  rfl

-- `[NumberField K]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Composition of field automorphisms gives composition of the actual ideal maps. -/
theorem idealConjugation_mul (σ τ : L ≃ₐ[K] L) :
    idealConjugation K L (σ * τ) = (idealConjugation K L σ).comp (idealConjugation K L τ) := by
  have h : RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv =
      (RingOfIntegers.mapRingEquiv τ.toRingEquiv).trans
        (RingOfIntegers.mapRingEquiv σ.toRingEquiv) := by
    ext x
    rfl
  refine MonoidHom.ext fun I => Units.ext ?_
  simp only [idealConjugation, h, Units.coe_map, MonoidHom.comp_apply]
  rw [FractionalIdeal.ringEquivOfRingEquiv_trans L L L]
  rfl

/-- The conjugation maps form a genuine integral representation on fractional ideals. -/
theorem exists_idealRepresentation :
    ∃ ρ : Representation ℤ (L ≃ₐ[K] L) (Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ),
      ∀ σ I, Additive.toMul (ρ σ (Additive.ofMul I)) = idealConjugation K L σ I := by
  let ρ : Representation ℤ (L ≃ₐ[K] L) (Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ) :=
    { toFun := fun σ => (idealConjugation K L σ).toAdditive.toIntLinearMap
      map_one' := by
        simp only [idealConjugation_one]
        exact LinearMap.ext fun I => rfl
      map_mul' := fun σ τ => by
        simp only [idealConjugation_mul]
        exact LinearMap.ext fun I => rfl }
  exact ⟨ρ, fun σ I => rfl⟩

/-- The actual fractional-ideal representation, chosen from conjugation. -/
def idealRepresentation :
    Representation ℤ (L ≃ₐ[K] L) (Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ) :=
  Classical.choose (exists_idealRepresentation K L)

/-- The chosen representation acts by the specified literal fractional-ideal conjugation. -/
theorem idealRepresentation_apply (σ : L ≃ₐ[K] L) (I : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    Additive.toMul (idealRepresentation K L σ (Additive.ofMul I)) =
      idealConjugation K L σ I := by
  exact Classical.choose_spec (exists_idealRepresentation K L) σ I

-- `[NumberField K]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Extending the restricted integer-ring automorphism recovers the specified field automorphism. -/
theorem fractionRingEquiv_mapRingEquiv_eq (σ : L ≃ₐ[K] L) :
    (IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L)
      (RingOfIntegers.mapRingEquiv σ.toRingEquiv)) = σ.toRingEquiv := by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (𝓞 L)⁰
  ext x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

/-- The actual principal-ideal homomorphism commutes with the specified field action. -/
theorem idealConjugation_principal (σ : L ≃ₐ[K] L) (u : Lˣ) :
    idealConjugation K L σ (toPrincipalIdeal (𝓞 L) L u) =
      toPrincipalIdeal (𝓞 L) L (σ • u) := by
  apply Units.ext
  rw [idealConjugation, Units.coe_map, coe_toPrincipalIdeal, coe_toPrincipalIdeal]
  change FractionalIdeal.ringEquivOfRingEquiv L L (RingOfIntegers.mapRingEquiv σ.toRingEquiv)
    (FractionalIdeal.spanSingleton _ (u : L)) = _
  rw [FractionalIdeal.ringEquivOfRingEquiv_spanSingleton, fractionRingEquiv_mapRingEquiv_eq]
  rfl

-- `[NumberField K] [NumberField L]` come from the section `variable`; the plan keeps them.
set_option linter.unusedSectionVars false in
/-- The restricted integer-ring automorphism fixes the actual base algebra map. -/
theorem mapRingEquiv_comp_algebraMap (σ : L ≃ₐ[K] L) :
    (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom.comp
      (algebraMap (𝓞 K) (𝓞 L)) = algebraMap (𝓞 K) (𝓞 L) := by
  ext x
  exact σ.commutes (x : K)

/-- Extending a base ideal gives a modulus invariant under every base-field automorphism. -/
theorem map_extendedModulus (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    (m.map (algebraMap (𝓞 K) (𝓞 L))).map
      (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom =
      m.map (algebraMap (𝓞 K) (𝓞 L)) := by
  rw [Ideal.map_map, mapRingEquiv_comp_algebraMap]

/-- Reconstructing a prime product and taking its exponent vector returns the original vector. -/
theorem idealExponentVector_exponentIdealProduct (e : HeightOneSpectrum (𝓞 L) →₀ ℤ) :
    idealExponentVector L (exponentIdealProduct L e) = e := by
  ext v
  rw [idealExponentVector_apply, count_exponentIdealProduct]

/-- The actual prime-exponent additive equivalence, using the existing inverse prime product. -/
def idealExponentEquiv : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ ≃+
    (HeightOneSpectrum (𝓞 L) →₀ ℤ) where
  toFun I := idealExponentVector L I.toMul
  invFun e := Additive.ofMul (exponentIdealProduct L e)
  left_inv I := congrArg Additive.ofMul (exponentIdealProduct_idealExponentVector L I.toMul)
  right_inv e := idealExponentVector_exponentIdealProduct L e
  map_add' I J := idealExponentVector_mul L I.toMul J.toMul

/-- The coordinate of the actual equivalence is the pinned fractional-ideal prime count. -/
theorem idealExponentEquiv_apply (I : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ)
    (v : HeightOneSpectrum (𝓞 L)) :
    idealExponentEquiv L I v = FractionalIdeal.count L v I.toMul := by
  rfl

/-- The actual permutation of nonzero prime ideals induced by a field automorphism. -/
def primePermutation (σ : L ≃ₐ[K] L) : HeightOneSpectrum (𝓞 L) ≃ HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv σ.toRingEquiv)

-- `[NumberField K] [NumberField L]` come from the section `variable`; the plan keeps them.
set_option linter.unusedSectionVars false in
/-- The spectrum permutation is exactly direct image of the underlying prime ideal. -/
theorem primePermutation_asIdeal (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 L)) :
    (primePermutation K L σ v).asIdeal =
      v.asIdeal.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom := by
  exact (Ideal.map_comap_of_equiv _).symm

/-- Identity conjugation fixes each prime. -/
theorem primePermutation_one (v : HeightOneSpectrum (𝓞 L)) :
    primePermutation K L 1 v = v := by
  apply HeightOneSpectrum.ext
  rw [primePermutation_asIdeal]
  have h : (RingOfIntegers.mapRingEquiv (1 : L ≃ₐ[K] L).toRingEquiv).toRingHom =
      RingHom.id (𝓞 L) := by
    ext x
    rfl
  rw [h, Ideal.map_id]

/-- Prime conjugation follows the actual order of composition of field automorphisms. -/
theorem primePermutation_mul (σ τ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 L)) :
    primePermutation K L (σ * τ) v = primePermutation K L σ (primePermutation K L τ v) := by
  apply HeightOneSpectrum.ext
  rw [primePermutation_asIdeal, primePermutation_asIdeal, primePermutation_asIdeal, Ideal.map_map]
  congr 1

/-- The actual Galois action on the set of nonzero prime ideals. -/
instance primeMulAction : MulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L)) where
  smul σ v := primePermutation K L σ v
  one_smul := primePermutation_one K L
  mul_smul := primePermutation_mul K L

/-- Conjugation carries the actual prime-ideal unit to the unit of the conjugate prime. -/
theorem idealConjugation_prime (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 L)) :
    idealConjugation K L σ (primeIdealUnit L v) = primeIdealUnit L (σ • v) := by
  apply Units.ext
  change FractionalIdeal.ringEquivOfRingEquiv L L (RingOfIntegers.mapRingEquiv σ.toRingEquiv)
      (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) =
    ((primePermutation K L σ v).asIdeal : FractionalIdeal (𝓞 L)⁰ L)
  rw [primePermutation_asIdeal]
  set e := RingOfIntegers.mapRingEquiv σ.toRingEquiv
  ext x
  rw [FractionalIdeal.mem_coeIdeal, ← FractionalIdeal.mem_coe,
    FractionalIdeal.ringEquivOfRingEquiv_apply, FractionalIdeal.coe_mk, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [FractionalIdeal.val_eq_coe, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨e a, Ideal.mem_map_of_mem _ ha,
      (IsFractionRing.ringEquivOfRingEquiv_algebraMap e a).symm⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_of_equiv e b).mp hb
    refine ⟨algebraMap (𝓞 L) L a, ?_, IsFractionRing.ringEquivOfRingEquiv_algebraMap e a⟩
    rw [FractionalIdeal.val_eq_coe, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]
    exact ⟨a, ha, rfl⟩

/-- Conjugation permutes the actual exponent coordinates without changing their values. -/
theorem idealExponentVector_conjugation (σ : L ≃ₐ[K] L)
    (I : (FractionalIdeal (𝓞 L)⁰ L)ˣ) (v : HeightOneSpectrum (𝓞 L)) :
    idealExponentVector L (idealConjugation K L σ I) (σ • v) = idealExponentVector L I v := by
  set e := idealExponentVector L I
  have hI : I = exponentIdealProduct L e := (exponentIdealProduct_idealExponentVector L I).symm
  have hconj : idealConjugation K L σ (exponentIdealProduct L e) =
      exponentIdealProduct L (e.mapDomain (σ • ·)) := by
    rw [exponentIdealProduct, exponentIdealProduct, map_finsuppProd,
      Finsupp.prod_mapDomain_index (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)]
    refine Finsupp.prod_congr fun w _ => ?_
    rw [map_zpow, idealConjugation_prime]
  rw [hI, hconj, idealExponentVector_exponentIdealProduct,
    Finsupp.mapDomain_apply (MulAction.injective σ)]

/-- The actual fractional-ideal representation is transported to the prime permutation module. -/
theorem idealExponentEquiv_equivariant (σ : L ≃ₐ[K] L)
    (I : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    idealExponentEquiv L (idealRepresentation K L σ I) =
      Representation.ofMulAction ℤ (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L)) σ
        (idealExponentEquiv L I) := by
  ext v
  rw [Representation.ofMulAction_apply]
  have h := idealRepresentation_apply K L σ (Additive.toMul I)
  rw [ofMul_toMul] at h
  change idealExponentVector L (Additive.toMul (idealRepresentation K L σ I)) v =
    idealExponentVector L (Additive.toMul I) (σ⁻¹ • v)
  rw [h]
  have h2 := idealExponentVector_conjugation K L σ (Additive.toMul I) (σ⁻¹ • v)
  rwa [smul_inv_smul] at h2

/-- Precisely the upstairs primes not dividing the extended base modulus. -/
def awayPrimes (m : Ideal (𝓞 K)) :=
  {v : HeightOneSpectrum (𝓞 L) // ¬m.map (algebraMap (𝓞 K) (𝓞 L)) ≤ v.asIdeal}

-- `[NumberField K] [NumberField L]` come from the section `variable`; the plan keeps them.
set_option linter.unusedSectionVars false in
/-- Excluding divisors of the extended modulus is exactly excluding primes lying above m. -/
theorem awayPrime_iff_under (m : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 L)) :
    (¬m.map (algebraMap (𝓞 K) (𝓞 L)) ≤ v.asIdeal) ↔
      ¬m ≤ (v.under (𝓞 K)).asIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  rfl

/-- Conjugation over K preserves the exact complement of the primes over m. -/
theorem awayPrime_conjugation (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L)) :
    (¬m.map (algebraMap (𝓞 K) (𝓞 L)) ≤ (σ • v).asIdeal) ↔
      ¬m.map (algebraMap (𝓞 K) (𝓞 L)) ≤ v.asIdeal := by
  have hsmul : (σ • v).asIdeal =
      v.asIdeal.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom :=
    primePermutation_asIdeal K L σ v
  rw [hsmul]
  apply not_congr
  conv_lhs => rw [← map_extendedModulus K L m σ]
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective
    (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom
    (RingOfIntegers.mapRingEquiv σ.toRingEquiv).bijective]

/-- The restriction of the actual prime action to the exact good-prime carrier. -/
instance awayPrimeMulAction (m : Ideal (𝓞 K)) : MulAction (L ≃ₐ[K] L) (awayPrimes K L m) where
  smul σ v := ⟨σ • v.val, (awayPrime_conjugation K L m σ v.val).mpr v.property⟩
  one_smul v := Subtype.ext (one_smul _ v.val)
  mul_smul σ τ v := Subtype.ext (mul_smul σ τ v.val)

end Cox.ClassFieldTheory
