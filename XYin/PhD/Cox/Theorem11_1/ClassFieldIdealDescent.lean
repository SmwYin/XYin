/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealCohomology
import XYin.PhD.Cox.Theorem11_1.ClassFieldFieldUnits
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! # Invariant ideals in Janusz V.2.1(c)

The map is the actual extension of fractional ideals. Invariant exponent descent
uses the entire fiber of primes over each base prime and the unramified hypothesis.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise
noncomputable section

namespace Cox.CyclicCohomology

/-- A finitely supported function constant on fibers descends through a surjection.
Its descended support lies in the image of the original finite support. -/
theorem exists_finsupp_factor {X Y A : Type*} [Zero A] (π : X → Y)
    (hπ : Function.Surjective π) (f : X →₀ A)
    (hf : ∀ x y, π x = π y → f x = f y) :
    ∃ g : Y →₀ A, ∀ x, g (π x) = f x := by
  classical
  refine ⟨Finsupp.ofSupportFinite (fun y => f (Function.surjInv hπ y)) ?_, fun x => ?_⟩
  · apply (f.support.finite_toSet.image π).subset
    intro y hy
    exact ⟨Function.surjInv hπ y, Finsupp.mem_support_iff.mpr hy, Function.surjInv_eq hπ y⟩
  · change f (Function.surjInv hπ (π x)) = f x
    exact hf _ _ (Function.surjInv_eq hπ (π x))

open scoped Classical in
/-- The fractional count of a nonzero integral ideal is the multiplicity of the prime in it. -/
theorem count_coeIdeal_eq_multiplicity {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) {J : Ideal R}
    (hJ : J ≠ ⊥) :
    FractionalIdeal.count F v (J : FractionalIdeal R⁰ F) = multiplicity v.asIdeal J := by
  have hJ0 : J ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  rw [FractionalIdeal.count_coe F v hJ0]
  have h := v.maxPowDividing_eq_pow_multiplicity hJ
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing] at h
  have hinj := pow_injective_of_not_isUnit (q := v.asIdeal)
    (by rw [Ideal.isUnit_iff]; exact v.isPrime.ne_top)
    (by rw [Ne, Ideal.zero_eq_bot]; exact v.ne_bot)
  exact_mod_cast hinj h

end Cox.CyclicCohomology

namespace Cox.ClassFieldTheory
open Cox.CyclicCohomology
variable (K L : Type*) [Field K] [Field L] [hNK : NumberField K] [hNL : NumberField L]
  [Algebra K L]

/-- The actual extension homomorphism on invertible fractional ideals. -/
def idealUnitExtension : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  Units.map (FractionalIdeal.extendedHom L (𝓞 L)).toMonoidHom

include hNK hNL in
/-- Integral closure makes extension of fractional ideals injective. -/
theorem idealUnitExtension_injective : Function.Injective (idealUnitExtension K L) := by
  intro I J h
  apply Units.ext
  exact FractionalIdeal.extendedHom_injective (𝓞 K) K L (𝓞 L) (congrArg Units.val h)

include hNK hNL in
/-- The count of an extended prime is its ramification exponent. -/
theorem idealExtension_prime_count (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) :
    FractionalIdeal.count L w (idealUnitExtension K L (primeIdealUnit K v)) =
      (Ideal.ramificationIdx v.asIdeal w.asIdeal : ℤ) := by
  have hmap : v.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot v.ne_bot
  have hE : ((idealUnitExtension K L (primeIdealUnit K v) : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
      FractionalIdeal (𝓞 L)⁰ L) =
      ((v.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) := by
    change FractionalIdeal.extendedHom L (𝓞 L)
      ((primeIdealUnit K v : FractionalIdeal (𝓞 K)⁰ K)) = _
    rw [primeIdealUnit_coe, FractionalIdeal.extendedHom_coeIdeal_eq_map]
  rw [hE, count_coeIdeal_eq_multiplicity w hmap,
    Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity hmap w.isPrime]

include hNK hNL in
/-- A prime over a different base prime has zero count in the extension. -/
theorem idealExtension_prime_count_of_under_ne (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : w.under (𝓞 K) ≠ v) :
    FractionalIdeal.count L w (idealUnitExtension K L (primeIdealUnit K v)) = 0 := by
  rw [idealExtension_prime_count, Ideal.ramificationIdx_of_not_le, Nat.cast_zero]
  intro hle
  apply hw
  have h1 : v.asIdeal ≤ (w.under (𝓞 K)).asIdeal := Ideal.map_le_iff_le_comap.mp hle
  exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 K)).isPrime.ne_top h1)).symm

include hNK hNL in
/-- Extension multiplies the exponent at a prime by its ramification index. -/
theorem idealExtension_count (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (w : HeightOneSpectrum (𝓞 L)) :
    FractionalIdeal.count L w (idealUnitExtension K L I) =
      (Ideal.ramificationIdx (w.under (𝓞 K)).asIdeal w.asIdeal : ℤ) *
        FractionalIdeal.count K (w.under (𝓞 K)) I := by
  have hprime : ∀ a : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count L w (idealUnitExtension K L (primeIdealUnit K a) :
        FractionalIdeal (𝓞 L)⁰ L) =
        (Ideal.ramificationIdx (w.under (𝓞 K)).asIdeal w.asIdeal : ℤ) *
          FractionalIdeal.count K (w.under (𝓞 K))
            (primeIdealUnit K a : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a
    by_cases h : w.under (𝓞 K) = a
    · subst h
      rw [idealExtension_prime_count, primeIdealUnit_coe, FractionalIdeal.count_self, mul_one]
    · rw [idealExtension_prime_count_of_under_ne K L a w h, primeIdealUnit_coe,
        FractionalIdeal.count_maximal_coprime K (w.under (𝓞 K)) (Ne.symm h), mul_zero]
  rw [← exponentIdealProduct_idealExponentVector K I]
  generalize idealExponentVector K I = e
  induction e using Finsupp.induction with
  | zero =>
    rw [exponentIdealProduct, Finsupp.prod_zero_index, map_one, Units.val_one, Units.val_one,
      FractionalIdeal.count_one, FractionalIdeal.count_one, mul_zero]
  | single_add a b f _ _ ih =>
    have hsingle : exponentIdealProduct K (Finsupp.single a b) = primeIdealUnit K a ^ b := by
      rw [exponentIdealProduct, Finsupp.prod_single_index (zpow_zero _)]
    rw [exponentIdealProduct_add, map_mul, Units.val_mul, Units.val_mul,
      FractionalIdeal.count_mul L w (Units.ne_zero _) (Units.ne_zero _),
      FractionalIdeal.count_mul K _ (Units.ne_zero _) (Units.ne_zero _), ih, hsingle, map_zpow,
      Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, FractionalIdeal.count_zpow,
      FractionalIdeal.count_zpow, hprime a]
    ring

include hNK hNL in
/-- Extension takes ideals avoiding m to ideals avoiding its actual extended modulus. -/
theorem idealUnitExtension_coprime (m : Ideal (𝓞 K)) (I : coprimeIdeals K m) :
    idealUnitExtension K L I ∈ coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L))) := by
  rw [mem_coprimeIdeals_iff_count_eq_zero]
  intro p hp
  rw [idealExtension_count]
  have hI := (mem_coprimeIdeals_iff_count_eq_zero K m I).mp I.2
  rw [hI (p.under (𝓞 K)) (Ideal.map_le_iff_le_comap.mp hp), mul_zero]

/-- Restrict the actual extension map to the prime-to-modulus additive module. -/
def awayIdealExtension (m : Ideal (𝓞 K)) :
    Additive (coprimeIdeals K m) →ₗ[ℤ] awayIdealSubmodule K L m :=
  ((idealUnitExtension K L).comp (coprimeIdeals K m).subtype).toAdditive.toIntLinearMap.codRestrict
    _ (fun I ↦ idealUnitExtension_coprime K L m I.toMul)

include hNK hNL in
/-- A K-automorphism preserves the contraction of each prime. -/
theorem primePermutation_under (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).under (𝓞 K) = w.under (𝓞 K) := by
  apply HeightOneSpectrum.ext
  change (σ • w).asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) =
    w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))
  have hsmul : (σ • w).asIdeal =
      w.asIdeal.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom :=
    primePermutation_asIdeal K L σ w
  rw [hsmul]
  conv_lhs => rw [← mapRingEquiv_comp_algebraMap K L σ, ← Ideal.comap_comap]
  rw [Ideal.comap_map_of_bijective (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom
    (RingOfIntegers.mapRingEquiv σ.toRingEquiv).bijective]

include hNK hNL in
/-- Conjugating an upstairs prime preserves its ramification index. -/
theorem ramificationIdx_primePermutation (σ : L ≃ₐ[K] L)
    (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.ramificationIdx (w.under (𝓞 K)).asIdeal (σ • w).asIdeal =
      Ideal.ramificationIdx (w.under (𝓞 K)).asIdeal w.asIdeal := by
  let e : 𝓞 L ≃ₐ[𝓞 K] 𝓞 L := RingOfIntegers.mapAlgEquiv σ
  have hsmul : (σ • w).asIdeal = w.asIdeal.map e := primePermutation_asIdeal K L σ w
  rw [hsmul, Ideal.ramificationIdx_map_eq]

include hNK hNL in
/-- The actual extended ideal is fixed by every K-automorphism. -/
theorem idealUnitExtension_fixed (σ : L ≃ₐ[K] L) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    idealConjugation K L σ (idealUnitExtension K L I) = idealUnitExtension K L I := by
  apply Additive.ofMul.injective
  apply (idealExponentEquiv L).injective
  ext p
  rw [idealExponentEquiv_apply, idealExponentEquiv_apply, toMul_ofMul, toMul_ofMul,
    count_idealConjugation, idealExtension_count, idealExtension_count,
    primePermutation_under, ramificationIdx_primePermutation]

include hNK hNL in
/-- Extended good ideals belong to the actual generator-difference kernel. -/
theorem awayIdealExtension_mem_fixed (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L)
    (I : Additive (coprimeIdeals K m)) :
    awayIdealExtension K L m I ∈
      LinearMap.ker (awayIdealRepresentation K L m σ - LinearMap.id) := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  apply Subtype.ext
  apply Additive.toMul.injective
  change Additive.toMul (idealRepresentation K L σ (Additive.ofMul (idealUnitExtension K L
      ((Additive.toMul I : coprimeIdeals K m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ)))) =
    idealUnitExtension K L ((Additive.toMul I : coprimeIdeals K m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  rw [idealRepresentation_apply, idealUnitExtension_fixed]

/-- The actual extension map with codomain restricted to generator-fixed good ideals. -/
def fixedIdealMap (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    Additive (coprimeIdeals K m) →ₗ[ℤ]
      LinearMap.ker (awayIdealRepresentation K L m σ - LinearMap.id) :=
  (awayIdealExtension K L m).codRestrict _ (awayIdealExtension_mem_fixed K L m σ)

include hNK hNL in
/-- Restriction of the codomain preserves the injective extension map. -/
theorem fixedIdealMap_injective (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    Function.Injective (fixedIdealMap K L m σ) := by
  intro I J h
  have h1 : idealUnitExtension K L
      ((Additive.toMul I : coprimeIdeals K m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      idealUnitExtension K L
        ((Additive.toMul J : coprimeIdeals K m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
    congrArg (fun x : LinearMap.ker (awayIdealRepresentation K L m σ - LinearMap.id) =>
      Additive.toMul ((x.val : awayIdealSubmodule K L m) :
        Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ)) h
  exact Additive.toMul.injective (Subtype.ext (idealUnitExtension_injective K L h1))

omit hNK hNL in
/-- The spectrum contraction has the literal ideal lying-over witness.
Install this locally when the ideal API does not unfold the spectrum projection during search. -/
theorem prime_liesOver_under (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩

-- `hNL` is included as in the planned signature; the proof does not need it.
set_option linter.unusedSectionVars false in
include hNK hNL in
/-- Every nonzero base prime has an upstairs prime above it. -/
theorem primeUnder_surjective : Function.Surjective
    (fun w : HeightOneSpectrum (𝓞 L) ↦ w.under (𝓞 K)) := by
  intro v
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [hQ.over]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))
  refine ⟨⟨Q, hQmax.isPrime, hQ0⟩, ?_⟩
  apply HeightOneSpectrum.ext
  exact hQ.over.symm

variable [hGalois : IsGalois K L]
include hNK hNL hGalois

/-- Primes over one base prime form one actual Galois orbit. -/
theorem prime_fiber_transitive (w z : HeightOneSpectrum (𝓞 L))
    (h : w.under (𝓞 K) = z.under (𝓞 K)) :
    ∃ τ : L ≃ₐ[K] L, τ • w = z := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hw : w.asIdeal ∈ (w.under (𝓞 K)).asIdeal.primesOver (𝓞 L) := ⟨w.isPrime, ⟨rfl⟩⟩
  have hz : z.asIdeal ∈ (w.under (𝓞 K)).asIdeal.primesOver (𝓞 L) :=
    ⟨z.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal h⟩⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 K) K L (𝓞 L) hw hz
  have hval : ∀ x : 𝓞 L, ((galRestrict (𝓞 K) K L (𝓞 L) σ x : 𝓞 L) : L) = σ (x : L) :=
    fun x => algebraMap_galRestrict_apply (𝓞 K) σ x
  refine ⟨σ⁻¹, HeightOneSpectrum.ext ?_⟩
  have hsmul : (σ⁻¹ • w).asIdeal =
      w.asIdeal.map (RingOfIntegers.mapRingEquiv (σ⁻¹).toRingEquiv : 𝓞 L →+* 𝓞 L) :=
    primePermutation_asIdeal K L σ⁻¹ w
  rw [hsmul, ← hσ, Ideal.map_comap_of_equiv]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have hx : (RingOfIntegers.mapRingEquiv (σ⁻¹).toRingEquiv).symm x =
      galRestrict (𝓞 K) K L (𝓞 L) σ x := by
    apply (RingOfIntegers.mapRingEquiv (σ⁻¹).toRingEquiv).injective
    rw [RingEquiv.apply_symm_apply]
    apply RingOfIntegers.ext
    change (x : L) = σ.symm ((galRestrict (𝓞 K) K L (𝓞 L) σ x : 𝓞 L) : L)
    rw [hval]
    exact (σ.symm_apply_apply (x : L)).symm
  rw [hx]

/-- Generator-invariance makes prime exponents constant on every complete prime fiber. -/
theorem fixedIdeal_counts_constant (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (a : LinearMap.ker (awayIdealRepresentation K L m σ - LinearMap.id))
    (w z : HeightOneSpectrum (𝓞 L)) (h : w.under (𝓞 K) = z.under (𝓞 K)) :
    FractionalIdeal.count L w ((a.val.val.toMul : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
      FractionalIdeal (𝓞 L)⁰ L) =
    FractionalIdeal.count L z ((a.val.val.toMul : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
      FractionalIdeal (𝓞 L)⁰ L) := by
  have hfix : awayIdealRepresentation K L m σ a.val = a.val :=
    sub_eq_zero.mp (LinearMap.mem_ker.mp a.2)
  have hinv := ((awayIdealRepresentation K L m).mem_invariants_iff_of_forall_mem_zpowers
    σ hσ a.val).mpr hfix
  obtain ⟨τ, hτ⟩ := prime_fiber_transitive K L w z h
  have hτfix : idealConjugation K L τ a.val.val.toMul = a.val.val.toMul := by
    have h1 := congrArg (fun x : awayIdealSubmodule K L m =>
      Additive.toMul (x : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ)) (hinv τ)
    have h2 := idealRepresentation_apply K L τ a.val.val.toMul
    rw [ofMul_toMul] at h2
    exact h2.symm.trans h1
  rw [← hτ]
  conv_rhs => rw [← hτfix, count_idealConjugation, inv_smul_smul]

/-- The constant prime-fiber exponents descend to a genuinely finitely supported vector. -/
theorem exists_fixedIdeal_exponents (m : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (a : LinearMap.ker (awayIdealRepresentation K L m σ - LinearMap.id)) :
    ∃ e : HeightOneSpectrum (𝓞 K) →₀ ℤ, ∀ w : HeightOneSpectrum (𝓞 L),
      e (w.under (𝓞 K)) = FractionalIdeal.count L w
        ((a.val.val.toMul : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 L)⁰ L) := by
  obtain ⟨e, he⟩ := exists_finsupp_factor (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K))
    (primeUnder_surjective K L) (idealExponentVector L a.val.val.toMul)
    (fun x y hxy => fixedIdeal_counts_constant K L m σ hσ a x y hxy)
  exact ⟨e, he⟩

omit hGalois in
/-- Descended prime exponents vanish at divisors of m, so their product is a good base ideal. -/
theorem descended_exponents_coprime (m : Ideal (𝓞 K))
    (I : awayIdealSubmodule K L m) (e : HeightOneSpectrum (𝓞 K) →₀ ℤ)
    (he : ∀ w : HeightOneSpectrum (𝓞 L), e (w.under (𝓞 K)) =
      FractionalIdeal.count L w ((I.val.toMul : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
        FractionalIdeal (𝓞 L)⁰ L)) :
    exponentIdealProduct K e ∈ coprimeIdeals K m := by
  rw [mem_coprimeIdeals_iff_count_eq_zero]
  intro p hp
  rw [count_exponentIdealProduct]
  obtain ⟨w, rfl⟩ := primeUnder_surjective K L p
  rw [he w]
  have hI : Additive.toMul I.val ∈ coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L))) := I.2
  exact (mem_coprimeIdeals_iff_count_eq_zero L _ _).mp hI w (Ideal.map_le_iff_le_comap.mpr hp)

omit hGalois in
/-- The stated unramified-away condition is exactly e=1 at the good upstairs primes. -/
theorem ramificationIdx_eq_one_of_away (m : Ideal (𝓞 K))
    (hU : IsUnramifiedAway K m L) (w : HeightOneSpectrum (𝓞 L))
    (hw : ¬m.map (algebraMap (𝓞 K) (𝓞 L)) ≤ w.asIdeal) :
    Ideal.ramificationIdx (w.under (𝓞 K)).asIdeal w.asIdeal = 1 := by
  have hmax := (w.under (𝓞 K)).isMaximal
  have hnot : ¬m ≤ (w.under (𝓞 K)).asIdeal := (awayPrime_iff_under K L m w).mp hw
  have hsup : (w.under (𝓞 K)).asIdeal ⊔ m = ⊤ := by
    by_contra hne
    exact hnot (le_sup_right.trans (hmax.eq_of_le hne le_sup_left).ge)
  exact hU _ (w.under (𝓞 K)).isPrime (w.under (𝓞 K)).ne_bot hsup w.asIdeal ⟨w.isPrime, ⟨rfl⟩⟩

/-- If e=1 on good primes, the extended finite prime product is the original invariant ideal. -/
theorem fixedIdeal_descends (m : Ideal (𝓞 K)) (hU : IsUnramifiedAway K m L)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (a : LinearMap.ker (awayIdealRepresentation K L m σ - LinearMap.id)) :
    ∃ I : coprimeIdeals K m,
      a.val.val.toMul = idealUnitExtension K L I := by
  obtain ⟨e, he⟩ := exists_fixedIdeal_exponents K L m σ hσ a
  have hcop := descended_exponents_coprime K L m a.val e he
  have key : a.val.val.toMul = idealUnitExtension K L (exponentIdealProduct K e) := by
    apply Additive.ofMul.injective
    apply (idealExponentEquiv L).injective
    ext w
    rw [idealExponentEquiv_apply, idealExponentEquiv_apply, toMul_ofMul, toMul_ofMul,
      idealExtension_count, count_exponentIdealProduct]
    by_cases hw : m.map (algebraMap (𝓞 K) (𝓞 L)) ≤ w.asIdeal
    · have hJ : Additive.toMul a.val.val ∈ coprimeIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L))) :=
        a.val.2
      rw [he w, (mem_coprimeIdeals_iff_count_eq_zero L _ _).mp hJ w hw, mul_zero]
    · rw [ramificationIdx_eq_one_of_away K L m hU w hw, he w, Nat.cast_one, one_mul]
  exact ⟨⟨exponentIdealProduct K e, hcop⟩, key⟩

/-- Unramified invariant-ideal descent gives surjectivity of the specified extension map. -/
theorem fixedIdealMap_surjective (m : Ideal (𝓞 K)) (hU : IsUnramifiedAway K m L)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Function.Surjective (fixedIdealMap K L m σ) := by
  intro a
  obtain ⟨I, hI⟩ := fixedIdeal_descends K L m hU σ hσ a
  refine ⟨Additive.ofMul I, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (congrArg Additive.ofMul hI).symm

/-- The actual inverse of base-ideal extension onto the invariant good ideals. -/
def fixedIdealsEquiv (m : Ideal (𝓞 K)) (hU : IsUnramifiedAway K m L)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    LinearMap.ker (awayIdealRepresentation K L m σ - LinearMap.id) ≃ₗ[ℤ]
      Additive (coprimeIdeals K m) :=
  (LinearEquiv.ofBijective (fixedIdealMap K L m σ)
    ⟨fixedIdealMap_injective K L m σ, fixedIdealMap_surjective K L m hU σ hσ⟩).symm

/-- The invariant ideal equivalence returns the base ideal whose extension represents it. -/
theorem fixedIdealsEquiv_apply (m : Ideal (𝓞 K)) (hU : IsUnramifiedAway K m L)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (I : Additive (coprimeIdeals K m)) :
    fixedIdealsEquiv K L m hU σ hσ (fixedIdealMap K L m σ I) = I := by
  exact (LinearEquiv.ofBijective _ _).symm_apply_apply I

end Cox.ClassFieldTheory
