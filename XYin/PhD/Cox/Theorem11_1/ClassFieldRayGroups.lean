/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldApproximation
import Mathlib.NumberTheory.NumberField.ClassNumber

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Global elements whose principal fractional ideal is prime to the modulus. -/
def modulusElements (m : Ideal (𝓞 K)) : Subgroup Kˣ :=
  (coprimeIdeals K m).comap (toPrincipalIdeal (𝓞 K) K)

/-- A residue has an inverse exactly when a lifted product differs from one by the ideal. -/
theorem isUnit_quotient_iff_exists_mul_sub_mem {R : Type*} [CommRing R]
    (m : Ideal R) (a : R) :
    IsUnit (Ideal.Quotient.mk m a) ↔ ∃ b : R, a * b - 1 ∈ m := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨b, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, map_one, sub_self]
  · rintro ⟨b, hb⟩
    refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk m b, ?_⟩
    rw [← map_mul, ← map_one (Ideal.Quotient.mk m)]
    exact Ideal.Quotient.eq.mpr hb

/-- A residue is a unit precisely when its principal ideal is prime to the modulus. -/
theorem isUnit_quotient_iff_coprime_span {R : Type*} [CommRing R]
    (m : Ideal R) (a : R) :
    IsUnit (Ideal.Quotient.mk m a) ↔ Ideal.span {a} ⊔ m = ⊤ := by
  rw [isUnit_quotient_iff_exists_mul_sub_mem, Ideal.eq_top_iff_one, Ideal.mem_span_singleton_sup]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, -(a * b - 1), m.neg_mem hb, by ring⟩
  · rintro ⟨b, c, hc, h⟩
    refine ⟨b, ?_⟩
    have h' : a * b - 1 = -c := by linear_combination h
    rw [h']
    exact m.neg_mem hc

/-- Subgroup membership for an integral ideal agrees with actual ideal coprimality. -/
theorem integral_unit_mem_coprime_iff (m A : Ideal (𝓞 K)) (hA : A ≠ ⊥)
    (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hu : (u : FractionalIdeal (𝓞 K)⁰ K) = A) :
    u ∈ coprimeIdeals K m ↔ A ⊔ m = ⊤ := by
  rw [mem_coprimeIdeals_iff_count_eq_zero, hu, integral_coprime_iff_count K m A hA]

/-- The valuation of a nonzero integer is the exponential of its negative prime count. -/
theorem valuation_integer_eq_exp_neg_count (v : HeightOneSpectrum (𝓞 K))
    (a : 𝓞 K) (ha : a ≠ 0) :
    v.valuation K (a : K) = WithZero.exp
      (-FractionalIdeal.count K v
        ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) := by
  have hspan : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  rw [show (a : K) = algebraMap (𝓞 K) K a from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg v ha, FractionalIdeal.count_coe K v hspan]

/-- Principal ideal counts and the finite-place valuation agree for fractional elements. -/
theorem valuation_eq_exp_neg_principal_count (v : HeightOneSpectrum (𝓞 K)) (u : Kˣ) :
    v.valuation K (u : K) = WithZero.exp
      (-FractionalIdeal.count K v (toPrincipalIdeal (𝓞 K) K u)) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (u : K)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact u.ne_zero hab.symm
  have hspan : ∀ c : 𝓞 K, c ≠ 0 →
      ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    intro c hc
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
    exact hc
  have hI : (toPrincipalIdeal (𝓞 K) K u : FractionalIdeal (𝓞 K)⁰ K) =
      ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
        ((Ideal.span {b} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.spanSingleton_mul_spanSingleton, ← hab, div_eq_mul_inv]
  have h1 : v.valuation K (algebraMap (𝓞 K) K a) = _ := valuation_integer_eq_exp_neg_count K v a ha0
  have h2 : v.valuation K (algebraMap (𝓞 K) K b) = _ := valuation_integer_eq_exp_neg_count K v b hb0
  rw [hI, FractionalIdeal.count_mul K v (hspan a ha0) (inv_ne_zero (hspan b hb0)),
    FractionalIdeal.count_inv, ← hab, map_div₀, h1, h2, ← WithZero.exp_sub]
  congr 1
  ring

/-- A good principal element has integral numerator and denominator both prime to m. -/
theorem exists_modulusElements_fraction (m : Ideal (𝓞 K)) (u : modulusElements K m) :
    ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ IsUnit (Ideal.Quotient.mk m a) ∧
      IsUnit (Ideal.Quotient.mk m b) ∧ ((u : Kˣ) : K) = (a : K) / b := by
  have hu : toPrincipalIdeal (𝓞 K) K (u : Kˣ) ∈ coprimeIdeals K m := u.2
  rcases eq_or_ne m ⊥ with rfl | hm
  · have h1 : toPrincipalIdeal (𝓞 K) K (u : Kˣ) = 1 := by
      apply fractionalIdealUnit_eq_one_of_count_eq_zero
      exact fun p => (mem_coprimeIdeals_iff_count_eq_zero K ⊥ _).mp hu p bot_le
    obtain ⟨w, hw⟩ := (principalIdeal_eq_one_iff K _).mp h1
    refine ⟨(w : 𝓞 K), 1, w.ne_zero, one_ne_zero, (w.isUnit.map _), isUnit_one.map _, ?_⟩
    rw [← hw]
    simp
  · let S : Finset (HeightOneSpectrum (𝓞 K)) := (Ideal.finite_factors hm).toFinset
    have hS : ∀ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal → v ∈ S := fun v hv =>
      (Ideal.finite_factors hm).mem_toFinset.mpr (Ideal.dvd_iff_le.mpr hv)
    have hSm : ∀ v ∈ S, m ≤ v.asIdeal := fun v hv =>
      Ideal.dvd_iff_le.mp ((Ideal.finite_factors hm).mem_toFinset.mp hv)
    have hval : ∀ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal →
        v.valuation K ((u : Kˣ) : K) = 1 := by
      intro v hv
      rw [valuation_eq_exp_neg_principal_count K v (u : Kˣ),
        (mem_coprimeIdeals_iff_count_eq_zero K m _).mp hu v hv, neg_zero, WithZero.exp_zero]
    obtain ⟨a, b, hb0, hbS, hab⟩ := exists_locally_integral_fraction K S ((u : Kˣ) : K)
      (fun v => (hval v.1 (hSm v.1 v.2)).le)
    have hb0K : (b : K) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hb0
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply (u : Kˣ).ne_zero
      rw [hab]
      simp
    have hbv : ∀ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal → b ∉ v.asIdeal :=
      fun v hv => hbS ⟨v, hS v hv⟩
    have hav : ∀ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal → a ∉ v.asIdeal := by
      intro v hv hav
      have hbv1 : v.valuation K (b : K) = 1 := by
        rw [show (b : K) = algebraMap (𝓞 K) K b from rfl,
          HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_eq_one_iff.mpr (hbv v hv)
      have hav1 : v.valuation K (a : K) < 1 := by
        rw [show (a : K) = algebraMap (𝓞 K) K a from rfl,
          HeightOneSpectrum.valuation_of_algebraMap]
        exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v a).mpr hav
      have hau : (a : K) = ((u : Kˣ) : K) * b := by
        rw [hab]
        field_simp
      rw [hau, map_mul, hval v hv, hbv1, one_mul] at hav1
      exact lt_irrefl _ hav1
    exact ⟨a, b, ha0, hb0, (quotient_unit_iff_avoid_primes K m hm a).mpr hav,
      (quotient_unit_iff_avoid_primes K m hm b).mpr hbv, hab⟩

/-- The residue of a good fractional element, expressed independently of its fraction. -/
def IsModulusResidue (m : Ideal (𝓞 K)) (u : modulusElements K m) (r : (𝓞 K ⧸ m)ˣ) : Prop :=
  ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ IsUnit (Ideal.Quotient.mk m b) ∧
    ((u : Kˣ) : K) = (a : K) / b ∧ Ideal.Quotient.mk m a = r * Ideal.Quotient.mk m b

/-- Every good fractional element has a residue unit. -/
theorem exists_modulusResidue (m : Ideal (𝓞 K)) (u : modulusElements K m) :
    ∃ r : (𝓞 K ⧸ m)ˣ, IsModulusResidue K m u r := by
  obtain ⟨a, b, ha, hb, hau, hbu, huab⟩ := exists_modulusElements_fraction K m u
  refine ⟨hau.unit * hbu.unit⁻¹, a, b, ha, hb, hbu, huab, ?_⟩
  have hV : (hbu.unit : 𝓞 K ⧸ m) = Ideal.Quotient.mk m b := hbu.unit_spec
  calc Ideal.Quotient.mk m a = (hau.unit : 𝓞 K ⧸ m) := hau.unit_spec.symm
    _ = ((hau.unit * hbu.unit⁻¹ : (𝓞 K ⧸ m)ˣ) : 𝓞 K ⧸ m) * (hbu.unit : 𝓞 K ⧸ m) := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    _ = _ := by rw [hV]

/-- The residue unit is independent of the fraction used to compute it. -/
theorem modulusResidue_unique (m : Ideal (𝓞 K)) (u : modulusElements K m)
    (r s : (𝓞 K ⧸ m)ˣ) (hr : IsModulusResidue K m u r) (hs : IsModulusResidue K m u s) :
    r = s := by
  obtain ⟨a, b, ha, hb, hbu, hu, hr⟩ := hr
  obtain ⟨a', b', ha', hb', hbu', hu', hs⟩ := hs
  have hb0 : (b : K) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hb
  have hb0' : (b' : K) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hb'
  have hK : (a : K) * b' = a' * b := by
    rw [hu] at hu'
    field_simp at hu'
    linear_combination hu'
  have hO : a * b' = a' * b := IsFractionRing.injective (𝓞 K) K (by
    rw [map_mul, map_mul]
    exact hK)
  have hq := congrArg (Ideal.Quotient.mk m) hO
  rw [map_mul, map_mul, hr, hs] at hq
  apply Units.ext
  apply (hbu.mul hbu').mul_right_cancel
  linear_combination hq

/-- Multiplying fractions multiplies their residues. -/
theorem isModulusResidue_mul (m : Ideal (𝓞 K)) (u v : modulusElements K m)
    (r s : (𝓞 K ⧸ m)ˣ) (hr : IsModulusResidue K m u r) (hs : IsModulusResidue K m v s) :
    IsModulusResidue K m (u * v) (r * s) := by
  obtain ⟨a, b, ha, hb, hbu, hu, hr⟩ := hr
  obtain ⟨a', b', ha', hb', hbu', hv, hs⟩ := hs
  refine ⟨a * a', b * b', mul_ne_zero ha ha', mul_ne_zero hb hb', ?_, ?_, ?_⟩
  · rw [map_mul]
    exact hbu.mul hbu'
  · change ((u : Kˣ) : K) * ((v : Kˣ) : K) =
      algebraMap (𝓞 K) K (a * a') / algebraMap (𝓞 K) K (b * b')
    rw [map_mul, map_mul, hu, hv]
    exact div_mul_div_comm _ _ _ _
  · rw [map_mul, map_mul, hr, hs, Units.val_mul]
    ring

/-- The unique residue of a good fractional element. -/
def modulusResidue (m : Ideal (𝓞 K)) (u : modulusElements K m) : (𝓞 K ⧸ m)ˣ :=
  Classical.choose (exists_modulusResidue K m u)

/-- Its defining fraction relation. -/
theorem modulusResidue_spec (m : Ideal (𝓞 K)) (u : modulusElements K m) :
    IsModulusResidue K m u (modulusResidue K m u) := by
  exact Classical.choose_spec (exists_modulusResidue K m u)

/-- Residues respect multiplication. -/
theorem modulusResidue_mul (m : Ideal (𝓞 K)) (u v : modulusElements K m) :
    modulusResidue K m (u*v) = modulusResidue K m u * modulusResidue K m v := by
  exact modulusResidue_unique K m (u * v) _ _ (modulusResidue_spec K m (u * v))
    (isModulusResidue_mul K m u v _ _ (modulusResidue_spec K m u) (modulusResidue_spec K m v))

/-- Janusz IV.1.3: the finite-residue homomorphism on elements prime to m. -/
def modulusResidueHom (m : Ideal (𝓞 K)) : modulusElements K m →* (𝓞 K ⧸ m)ˣ :=
  MonoidHom.mk' (modulusResidue K m) (modulusResidue_mul K m)

/-- Every ray element is prime to its modulus. -/
theorem rayElements_le_modulusElements (m : Ideal (𝓞 K)) :
    rayElements K m ≤ modulusElements K m := by
  exact fun u hu => principal_mem_coprime_of_mem_rayElements K m u hu

/-- The finite residue homomorphism has the actual ray elements as kernel. -/
theorem modulusResidueHom_ker (m : Ideal (𝓞 K)) :
    (modulusResidueHom K m).ker = (rayElements K m).comap (modulusElements K m).subtype := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  obtain ⟨a, b, ha, hb, hbu, hu, hr⟩ := modulusResidue_spec K m u
  change modulusResidue K m u = 1 ↔ _
  rw [Subgroup.coe_subtype, mem_rayElements_fraction_iff K m (u : Kˣ) a b ha hb hu hbu,
    ← Ideal.Quotient.eq]
  constructor
  · intro h1
    rw [hr, h1, Units.val_one, one_mul]
  · intro h1
    apply Units.ext
    rw [Units.val_one]
    apply hbu.mul_right_cancel
    rw [← hr, h1, one_mul]

/-- The element ray quotient is finite, including the trivial modulus. -/
theorem rayElements_finiteIndex (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    ((rayElements K m).comap (modulusElements K m).subtype).FiniteIndex := by
  haveI : Finite (𝓞 K ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm
  rw [← modulusResidueHom_ker]
  exact Subgroup.finiteIndex_ker (modulusResidueHom K m)

/-- The ordinary ideal-class map restricted to good ideals. -/
def coprimeIdealClassMap (m : Ideal (𝓞 K)) : coprimeIdeals K m →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp (coprimeIdeals K m).subtype

/-- The principal-ideal map on good elements. -/
def modulusPrincipalMap (m : Ideal (𝓞 K)) : modulusElements K m →* coprimeIdeals K m :=
  ((toPrincipalIdeal (𝓞 K) K).comp (modulusElements K m).subtype).codRestrict
    (coprimeIdeals K m) (fun u => u.property)

/-- The kernel of the ideal-class map is precisely the principal image. -/
theorem coprimeIdealClassMap_ker (m : Ideal (𝓞 K)) :
    (coprimeIdealClassMap K m).ker = (modulusPrincipalMap K m).range := by
  ext u
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  change ClassGroup.mk K (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1 ↔ _
  rw [← MonoidHom.mem_ker, classGroup_mk_ker_eq_principal_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨a, ha⟩
    have ha' : toPrincipalIdeal (𝓞 K) K a ∈ coprimeIdeals K m := by
      rw [ha]
      exact u.2
    exact ⟨⟨a, ha'⟩, Subtype.ext ha⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

/-- Ray elements map onto the actual ray-principal subgroup. -/
theorem modulusPrincipalMap_ray_image (m : Ideal (𝓞 K)) :
    ((rayElements K m).comap (modulusElements K m).subtype).map (modulusPrincipalMap K m) =
      raySubgroup K m := by
  ext u
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := principal_mem_ray_of_mem_rayElements K m (x : Kˣ) hx
    have hyx' : y = modulusPrincipalMap K m x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  · intro hu
    obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := (raySubgroup_mem_iff_fraction K m u).mp hu
    have hb0 : (b : K) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hb
    have ha0 : (a : K) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
    let α : Kˣ := Units.mk0 ((a : K) / b) (div_ne_zero ha0 hb0)
    have hα : α ∈ rayElements K m :=
      (mem_rayElements_iff_fraction K m α).mpr ⟨a, b, ha, hb, ha1, hb1, rfl⟩
    refine ⟨⟨α, rayElements_le_modulusElements K m hα⟩, hα, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change (toPrincipalIdeal (𝓞 K) K α : FractionalIdeal (𝓞 K)⁰ K) = _
    rw [coe_toPrincipalIdeal, hab, FractionalIdeal.spanSingleton_div_spanSingleton]
    rfl

/-- The principal class-map kernel has finite quotient by the ray subgroup. -/
theorem raySubgroup_relIndex_finite (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    ((raySubgroup K m).comap (coprimeIdealClassMap K m).ker.subtype).FiniteIndex := by
  have hrange : (modulusPrincipalMap K m).range = (coprimeIdealClassMap K m).ker :=
    (coprimeIdealClassMap_ker K m).symm
  let f : modulusElements K m →* (coprimeIdealClassMap K m).ker :=
    (modulusPrincipalMap K m).codRestrict _
      (fun x => hrange ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  haveI := rayElements_finiteIndex K m hm
  have hmap : ((rayElements K m).comap (modulusElements K m).subtype).map f =
      (raySubgroup K m).comap (coprimeIdealClassMap K m).ker.subtype := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_comap, ← modulusPrincipalMap_ray_image K m,
      Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext hxy⟩
  rw [← hmap, Subgroup.finiteIndex_iff]
  intro h
  have hdvd := Subgroup.index_map_dvd ((rayElements K m).comap (modulusElements K m).subtype) hf
  rw [h, zero_dvd_iff] at hdvd
  exact Subgroup.FiniteIndex.index_ne_zero hdvd

/-- A ray-principal ideal is trivial in the ordinary class group. -/
theorem raySubgroup_le_classMap_ker (m : Ideal (𝓞 K)) :
    raySubgroup K m ≤ (coprimeIdealClassMap K m).ker := by
  rw [coprimeIdealClassMap_ker, ← modulusPrincipalMap_ray_image]
  exact Subgroup.map_le_range _ _

/-- Finiteness of the finite-modulus ray quotient. Infinite-place sign conditions are
not required for this finiteness assertion. -/
theorem raySubgroup_finiteIndex (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    (raySubgroup K m).FiniteIndex := by
  haveI : (coprimeIdealClassMap K m).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  rw [Subgroup.finiteIndex_iff, ← Subgroup.relIndex_mul_index (raySubgroup_le_classMap_ker K m)]
  exact mul_ne_zero (Subgroup.finiteIndex_iff.mp (raySubgroup_relIndex_finite K m hm))
    Subgroup.FiniteIndex.index_ne_zero

/-- Approximation realizes prescribed prime counts while imposing a ray congruence. -/
theorem exists_ray_element_with_counts (n : Ideal (𝓞 K)) (hn : n ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), n ≤ v.asIdeal → v ∈ S)
    (e : S → ℤ) (he : ∀ v : S, n ≤ v.1.asIdeal → e v = 0) :
    ∃ a : Kˣ, a ∈ rayElements K n ∧ ∀ v : S,
      FractionalIdeal.count K v.1 (toPrincipalIdeal (𝓞 K) K a) = e v := by
  classical
  choose π hπ using fun v : HeightOneSpectrum (𝓞 K) => v.valuation_exists_uniformizer K
  rcases S.eq_empty_or_nonempty with hSe | ⟨v₀, hv₀⟩
  · subst hSe
    exact ⟨1, one_mem _, fun v => absurd v.2 (Finset.notMem_empty _)⟩
  let t : S → K := fun v => if n ≤ v.1.asIdeal then 1 else π v.1 ^ e v
  let N : S → ℤ := fun v => if n ≤ v.1.asIdeal then (Ideal.absNorm n : ℤ) else e v
  obtain ⟨x, hx⟩ := exists_global_valuation_approx K S t N
  have hval : ∀ v : S, v.1.valuation K x = WithZero.exp (-e v) := by
    intro v
    by_cases hv : n ≤ v.1.asIdeal
    · have h1 := hx v
      simp only [t, N, if_pos hv] at h1
      rw [he v hv, neg_zero, WithZero.exp_zero]
      have hlt : v.1.valuation K (x - 1) < v.1.valuation K 1 := by
        rw [map_one]
        exact lt_of_lt_of_le h1 (by
          rw [← WithZero.exp_zero]
          exact WithZero.exp_le_exp.mpr (by simp))
      rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
    · have h1 := hx v
      simp only [t, N, if_neg hv] at h1
      have hπe : v.1.valuation K (π v.1 ^ e v) = WithZero.exp (-e v) := by
        rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
        congr 1
        simp
      rw [← hπe] at h1
      rw [Valuation.map_eq_of_sub_lt _ h1, hπe]
  have hx0 : x ≠ 0 := by
    intro h
    have h1 := hval ⟨v₀, hv₀⟩
    rw [h, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  refine ⟨Units.mk0 x hx0, ?_, fun v => ?_⟩
  · rw [mem_rayElements_iff_all_primePowers K n hn]
    intro v t' ht hvt
    have hnv : n ≤ v.asIdeal := hvt.trans (Ideal.pow_le_self ht.ne')
    have h1 := hx ⟨v, hS v hnv⟩
    simp only [t, N, if_pos hnv] at h1
    have hlt := lt_absNorm_of_le_pow K hn v hvt
    exact (lt_of_lt_of_le h1 (WithZero.exp_le_exp.mpr (by omega))).le
  · have hc := valuation_eq_exp_neg_principal_count K v.1 (Units.mk0 x hx0)
    rw [Units.val_mk0, hval v] at hc
    have := WithZero.exp_injective hc
    omega

/-- Janusz V.6.1: correct finitely many bad prime exponents by a ray-principal ideal. -/
theorem exists_ray_principal_correction (m n : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (hmn : m ≤ n) (u : coprimeIdeals K n) :
    ∃ a : Kˣ, a ∈ rayElements K n ∧
      (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) * (toPrincipalIdeal (𝓞 K) K a)⁻¹ ∈
        coprimeIdeals K m := by
  classical
  have hn : n ≠ ⊥ := fun h => hm (eq_bot_iff.mpr (h ▸ hmn))
  let S : Finset (HeightOneSpectrum (𝓞 K)) := (Ideal.finite_factors hm).toFinset
  have hSmem : ∀ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal → v ∈ S := fun v hv =>
    (Ideal.finite_factors hm).mem_toFinset.mpr (Ideal.dvd_iff_le.mpr hv)
  let e : S → ℤ := fun v =>
    FractionalIdeal.count K v.1 ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
  have he : ∀ v : S, n ≤ v.1.asIdeal → e v = 0 := fun v hv =>
    (mem_coprimeIdeals_iff_count_eq_zero K n _).mp u.2 v.1 hv
  obtain ⟨a, ha, hcount⟩ := exists_ray_element_with_counts K n hn S
    (fun v hv => hSmem v (hmn.trans hv)) e he
  refine ⟨a, ha, ?_⟩
  rw [mem_coprimeIdeals_iff_count_eq_zero]
  intro v hv
  rw [Units.val_mul, Units.val_inv_eq_inv_val, FractionalIdeal.count_mul K v (Units.ne_zero _)
    (inv_ne_zero (Units.ne_zero _)), FractionalIdeal.count_inv, hcount ⟨v, hSmem v hv⟩]
  exact add_neg_cancel _

/-- The source identity I^n=I^m i(K_n,1). -/
theorem coprimeIdeals_eq_sup_ray (m n : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hmn : m ≤ n) :
    coprimeIdeals K n = coprimeIdeals K m ⊔ Subgroup.closure (rayGenerators K n) := by
  apply le_antisymm
  · intro u hu
    obtain ⟨a, ha, hmem⟩ := exists_ray_principal_correction K m n hm hmn ⟨u, hu⟩
    have hP : toPrincipalIdeal (𝓞 K) K a ∈ Subgroup.closure (rayGenerators K n) := by
      obtain ⟨y, hy, hya⟩ := principal_mem_ray_of_mem_rayElements K n a ha
      rw [← hya]
      exact hy
    rw [← inv_mul_cancel_right u (toPrincipalIdeal (𝓞 K) K a)]
    exact Subgroup.mul_mem_sup hmem hP
  · exact sup_le (coprimeIdeals_mono K hmn)
      ((Subgroup.closure_le _).mpr (rayGenerators_mem_coprimeIdeals K n))

omit [NumberField K] in
/-- A nonzero proper ideal of the ring of integers lies in a height-one prime. -/
theorem exists_heightOneSpectrum_le (r : Ideal (𝓞 K)) (hr : r ≠ ⊥) (hrt : r ≠ ⊤) :
    ∃ v : HeightOneSpectrum (𝓞 K), r ≤ v.asIdeal := by
  obtain ⟨M, hM, hrM⟩ := Ideal.exists_le_maximal r hrt
  exact ⟨⟨M, hM.isPrime, fun h => hr (eq_bot_iff.mpr (h ▸ hrM))⟩, hrM⟩

/-- A ray-principal ideal comes from an actual ray element. -/
theorem exists_rayElement_of_mem_closure (m : Ideal (𝓞 K))
    {ρ : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hρ : ρ ∈ Subgroup.closure (rayGenerators K m)) :
    ∃ α : Kˣ, α ∈ rayElements K m ∧ toPrincipalIdeal (𝓞 K) K α = ρ := by
  have hρI : ρ ∈ coprimeIdeals K m :=
    (Subgroup.closure_le _).mpr (rayGenerators_mem_coprimeIdeals K m) hρ
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := (raySubgroup_mem_iff_fraction K m ⟨ρ, hρI⟩).mp hρ
  have hb0 : (b : K) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hb
  have ha0 : (a : K) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
  refine ⟨Units.mk0 ((a : K) / b) (div_ne_zero ha0 hb0),
    (mem_rayElements_iff_fraction K m _).mpr ⟨a, b, ha, hb, ha1, hb1, rfl⟩, ?_⟩
  apply Units.ext
  rw [coe_toPrincipalIdeal, Units.val_mk0, ← FractionalIdeal.spanSingleton_div_spanSingleton]
  exact hab.symm

/-- Ray generators are monotone in the modulus. -/
theorem rayGenerators_mono {m n : Ideal (𝓞 K)} (hmn : m ≤ n) :
    rayGenerators K m ⊆ rayGenerators K n :=
  fun _ ⟨α, hα, h1, hu⟩ => ⟨α, hα, hmn h1, hu⟩

/-- Janusz V.6.2: split a gcd ray element, preserving coprimality to a common modulus. -/
theorem exists_ray_gcd_split (m₁ m₂ r : Ideal (𝓞 K)) (hr : r ≠ ⊥)
    (hr₁ : r ≤ m₁) (hr₂ : r ≤ m₂) (a : Kˣ)
    (ha : a ∈ rayElements K (m₁ ⊔ m₂))
    (hgood : toPrincipalIdeal (𝓞 K) K a ∈ coprimeIdeals K r) :
    ∃ b : Kˣ, b ∈ rayElements K m₁ ∧ a * b⁻¹ ∈ rayElements K m₂ ∧
      toPrincipalIdeal (𝓞 K) K b ∈ coprimeIdeals K r := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 K)) := (Ideal.finite_factors hr).toFinset
  have hSmem : ∀ v : HeightOneSpectrum (𝓞 K), r ≤ v.asIdeal ↔ v ∈ S := fun v =>
    ⟨fun h => (Ideal.finite_factors hr).mem_toFinset.mpr (Ideal.dvd_iff_le.mpr h),
      fun h => Ideal.dvd_iff_le.mp ((Ideal.finite_factors hr).mem_toFinset.mp h)⟩
  have hm₁ : m₁ ≠ ⊥ := fun h => hr (eq_bot_iff.mpr (h ▸ hr₁))
  have hm₂ : m₂ ≠ ⊥ := fun h => hr (eq_bot_iff.mpr (h ▸ hr₂))
  have hsup : m₁ ⊔ m₂ ≠ ⊥ := fun h => hm₁ (eq_bot_iff.mpr (h ▸ le_sup_left))
  rcases S.eq_empty_or_nonempty with hSe | ⟨v₀, hv₀⟩
  · have hrt : r = ⊤ := by
      by_contra hrt
      obtain ⟨v, hv⟩ := exists_heightOneSpectrum_le K r hr hrt
      have h := (hSmem v).mp hv
      rw [hSe] at h
      exact Finset.notMem_empty v h
    have h₂ : m₂ = ⊤ := top_le_iff.mp (hrt ▸ hr₂)
    refine ⟨1, one_mem _, ?_, by rw [map_one]; exact one_mem _⟩
    rw [h₂, rayElements_top]
    exact Subgroup.mem_top _
  have hvalA : ∀ v : HeightOneSpectrum (𝓞 K), r ≤ v.asIdeal → v.valuation K (a : K) = 1 := by
    intro v hv
    rw [valuation_eq_exp_neg_principal_count K v a,
      (mem_coprimeIdeals_iff_count_eq_zero K r _).mp hgood v hv, neg_zero, WithZero.exp_zero]
  let P : S → Prop := fun v => ∀ t : ℕ, m₂ ≤ v.1.asIdeal ^ t → m₁ ≤ v.1.asIdeal ^ t
  let tgt : S → K := fun v => if P v then 1 else (a : K)
  obtain ⟨x, hx⟩ := exists_global_valuation_approx K S tgt (fun _ => (Ideal.absNorm r : ℤ))
  have hN : ∀ v : HeightOneSpectrum (𝓞 K), ∀ t : ℕ, r ≤ v.asIdeal ^ t →
      WithZero.exp (-(Ideal.absNorm r : ℤ)) ≤ WithZero.exp (-(t : ℤ)) := by
    intro v t h
    have := lt_absNorm_of_le_pow K hr v h
    exact WithZero.exp_le_exp.mpr (by omega)
  have htgt1 : ∀ v : S, v.1.valuation K (tgt v) = 1 := by
    intro v
    simp only [tgt]
    split_ifs
    · exact map_one _
    · exact hvalA v.1 ((hSmem v.1).mpr v.2)
  have hxv : ∀ v : S, v.1.valuation K x = 1 := by
    intro v
    have h1 : v.1.valuation K (x - tgt v) < v.1.valuation K (tgt v) := by
      rw [htgt1]
      exact lt_of_lt_of_le (hx v) (by
        rw [← WithZero.exp_zero]
        exact WithZero.exp_le_exp.mpr (by simp))
    rw [Valuation.map_eq_of_sub_lt _ h1, htgt1]
  have hx0 : x ≠ 0 := by
    intro h
    have h1 := hxv ⟨v₀, hv₀⟩
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  refine ⟨Units.mk0 x hx0, ?_, ?_, ?_⟩
  · rw [mem_rayElements_iff_all_primePowers K m₁ hm₁]
    intro v t ht hvt
    change v.valuation K (x - 1) ≤ _
    have hrv : r ≤ v.asIdeal ^ t := hr₁.trans hvt
    have hvS : v ∈ S := (hSmem v).mp (hrv.trans (Ideal.pow_le_self ht.ne'))
    have h1 := hx ⟨v, hvS⟩
    by_cases hP : P ⟨v, hvS⟩
    · simp only [tgt, if_pos hP] at h1
      exact (lt_of_lt_of_le h1 (hN v t hrv)).le
    · simp only [tgt, if_neg hP] at h1
      simp only [P, not_forall] at hP
      obtain ⟨t₀, ht₀, hnt₀⟩ := hP
      have htt₀ : t ≤ t₀ := by
        by_contra hlt
        push Not at hlt
        exact hnt₀ (hvt.trans (Ideal.pow_le_pow_right hlt.le))
      have hm₂t : m₂ ≤ v.asIdeal ^ t := ht₀.trans (Ideal.pow_le_pow_right htt₀)
      have ha1 : v.valuation K ((a : K) - 1) ≤ WithZero.exp (-(t : ℤ)) :=
        (mem_rayElements_iff_all_primePowers K (m₁ ⊔ m₂) hsup a).mp ha v t ht (sup_le hvt hm₂t)
      calc v.valuation K (x - 1) = v.valuation K ((x - a) + ((a : K) - 1)) := by
            congr 1
            ring
        _ ≤ max (v.valuation K (x - a)) (v.valuation K ((a : K) - 1)) := Valuation.map_add _ _ _
        _ ≤ WithZero.exp (-(t : ℤ)) := max_le (lt_of_lt_of_le h1 (hN v t hrv)).le ha1
  · rw [mem_rayElements_iff_all_primePowers K m₂ hm₂]
    intro v t ht hvt
    have hrv : r ≤ v.asIdeal ^ t := hr₂.trans hvt
    have hvS : v ∈ S := (hSmem v).mp (hrv.trans (Ideal.pow_le_self ht.ne'))
    have h1 := hx ⟨v, hvS⟩
    have heq : ((a * (Units.mk0 x hx0)⁻¹ : Kˣ) : K) - 1 = ((a : K) - x) / x := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
    rw [heq, map_div₀, hxv ⟨v, hvS⟩, div_one]
    by_cases hP : P ⟨v, hvS⟩
    · simp only [tgt, if_pos hP] at h1
      have ha1 : v.valuation K ((a : K) - 1) ≤ WithZero.exp (-(t : ℤ)) :=
        (mem_rayElements_iff_all_primePowers K (m₁ ⊔ m₂) hsup a).mp ha v t ht
          (sup_le (hP t hvt) hvt)
      calc v.valuation K ((a : K) - x) = v.valuation K (((a : K) - 1) - (x - 1)) := by
            congr 1
            ring
        _ ≤ max (v.valuation K ((a : K) - 1)) (v.valuation K (x - 1)) := Valuation.map_sub _ _ _
        _ ≤ WithZero.exp (-(t : ℤ)) := max_le ha1 (lt_of_lt_of_le h1 (hN v t hrv)).le
    · simp only [tgt, if_neg hP] at h1
      rw [Valuation.map_sub_swap]
      exact (lt_of_lt_of_le h1 (hN v t hrv)).le
  · rw [mem_coprimeIdeals_iff_count_eq_zero]
    intro v hv
    have hc := valuation_eq_exp_neg_principal_count K v (Units.mk0 x hx0)
    rw [Units.val_mk0, hxv ⟨v, (hSmem v).mp hv⟩] at hc
    have h0 : WithZero.exp (-FractionalIdeal.count K v
        (toPrincipalIdeal (𝓞 K) K (Units.mk0 x hx0) : FractionalIdeal (𝓞 K)⁰ K)) =
          WithZero.exp 0 := by
      rw [← hc, WithZero.exp_zero]
    have := WithZero.exp_injective h0
    omega

variable {K} in
/-- Membership in a congruence subgroup is membership of the underlying ideal in its ambient
subgroup. -/
theorem CongruenceSubgroup.mem_subgroup_iff (H : CongruenceSubgroup K)
    (x : coprimeIdeals K H.modulus) :
    x ∈ H.subgroup ↔ (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ H.ambient :=
  ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, hyx⟩ => (Subtype.ext hyx : y = x) ▸ hy⟩

variable {K} in
/-- The ambient congruence subgroup consists of ideals prime to its modulus. -/
theorem CongruenceSubgroup.ambient_le_coprimeIdeals (H : CongruenceSubgroup K) :
    H.ambient ≤ coprimeIdeals K H.modulus := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

variable {K} in
/-- The ray principal ideals at the modulus lie in every congruence subgroup. -/
theorem CongruenceSubgroup.closure_rayGenerators_le_ambient (H : CongruenceSubgroup K) :
    Subgroup.closure (rayGenerators K H.modulus) ≤ H.ambient := fun ρ hρ =>
  ⟨⟨ρ, (Subgroup.closure_le _).mpr (rayGenerators_mem_coprimeIdeals K H.modulus) hρ⟩,
    H.contains_ray hρ, rfl⟩

variable {K} in
/-- Principal ideals of ray elements lie in every congruence subgroup at that modulus. -/
theorem CongruenceSubgroup.principal_mem_ambient (H : CongruenceSubgroup K) (a : Kˣ)
    (ha : a ∈ rayElements K H.modulus) : toPrincipalIdeal (𝓞 K) K a ∈ H.ambient := by
  obtain ⟨y, hy, hya⟩ := principal_mem_ray_of_mem_rayElements K H.modulus a ha
  exact ⟨y, H.contains_ray hy, hya⟩

/-- Janusz V.6.1: restriction to a larger modulus does not change a congruence quotient. -/
theorem congruence_quotient_equiv (H J : CongruenceSubgroup K)
    (hm : H.modulus ≤ J.modulus)
    (hres : H.ambient = J.ambient ⊓ coprimeIdeals K H.modulus) :
    Nonempty ((coprimeIdeals K H.modulus ⧸ H.subgroup) ≃*
      (coprimeIdeals K J.modulus ⧸ J.subgroup)) := by
  have hincl : coprimeIdeals K H.modulus ≤ coprimeIdeals K J.modulus := coprimeIdeals_mono K hm
  let ι : coprimeIdeals K H.modulus →* coprimeIdeals K J.modulus := Subgroup.inclusion hincl
  let φ := (QuotientGroup.mk' J.subgroup).comp ι
  have hker : φ.ker = H.subgroup := by
    ext x
    have hιx : ((ι x : coprimeIdeals K J.modulus) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := Subgroup.coe_inclusion hincl x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, CongruenceSubgroup.mem_subgroup_iff,
      CongruenceSubgroup.mem_subgroup_iff, hιx, hres, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective J.subgroup q
    have hy : (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ coprimeIdeals K H.modulus ⊔
        Subgroup.closure (rayGenerators K J.modulus) := by
      rw [← coprimeIdeals_eq_sup_ray K H.modulus J.modulus H.modulus_ne_bot hm]
      exact y.2
    obtain ⟨u, hu, ρ, hρ, huρ⟩ := Subgroup.mem_sup.mp hy
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    apply J.contains_ray
    change (((ι ⟨u, hu⟩)⁻¹ * y : coprimeIdeals K J.modulus) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈
      Subgroup.closure (rayGenerators K J.modulus)
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have hιu : ((ι ⟨u, hu⟩ : coprimeIdeals K J.modulus) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = u :=
      Subgroup.coe_inclusion hincl _
    rw [hιu, ← huρ, inv_mul_cancel_left]
    exact hρ
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

/-- Janusz V.6.1: the larger-modulus restriction and the ray subgroup recover the group. -/
theorem congruence_ambient_eq_sup_ray (H J : CongruenceSubgroup K)
    (hm : H.modulus ≤ J.modulus)
    (hres : H.ambient = J.ambient ⊓ coprimeIdeals K H.modulus) :
    J.ambient = H.ambient ⊔ Subgroup.closure (rayGenerators K J.modulus) := by
  apply le_antisymm
  · intro j hj
    have hj' : j ∈ coprimeIdeals K H.modulus ⊔ Subgroup.closure (rayGenerators K J.modulus) := by
      rw [← coprimeIdeals_eq_sup_ray K H.modulus J.modulus H.modulus_ne_bot hm]
      exact J.ambient_le_coprimeIdeals hj
    obtain ⟨u, hu, ρ, hρ, rfl⟩ := Subgroup.mem_sup.mp hj'
    have huJ : u ∈ J.ambient := by
      have h := J.ambient.mul_mem hj (J.ambient.inv_mem (J.closure_rayGenerators_le_ambient hρ))
      rwa [mul_inv_cancel_right] at h
    have huH : u ∈ H.ambient := by
      rw [hres]
      exact ⟨huJ, hu⟩
    exact Subgroup.mul_mem_sup huH hρ
  · refine sup_le ?_ J.closure_rayGenerators_le_ambient
    rw [hres]
    exact inf_le_left

/-- The source's common-restriction relation is an equivalence relation. -/
theorem congruenceEquivalent_equivalence :
    Equivalence (CongruenceEquivalent K) := by
  refine ⟨fun H => ⟨H.modulus, H.modulus_ne_bot, le_rfl, le_rfl, rfl⟩,
    fun ⟨m, hm, h1, h2, h⟩ => ⟨m, hm, h2, h1, h.symm⟩, ?_⟩
  rintro H J L ⟨m₁, hm₁, h1H, h1J, e1⟩ ⟨m₂, hm₂, h2J, h2L, e2⟩
  refine ⟨m₁ * m₂, mul_ne_zero hm₁ hm₂, Ideal.mul_le_right.trans h1H,
    Ideal.mul_le_left.trans h2L, ?_⟩
  have hI1 : coprimeIdeals K (m₁ * m₂) ≤ coprimeIdeals K m₁ :=
    coprimeIdeals_mono K Ideal.mul_le_right
  have hI2 : coprimeIdeals K (m₁ * m₂) ≤ coprimeIdeals K m₂ :=
    coprimeIdeals_mono K Ideal.mul_le_left
  calc H.ambient ⊓ coprimeIdeals K (m₁ * m₂) =
        H.ambient ⊓ coprimeIdeals K m₁ ⊓ coprimeIdeals K (m₁ * m₂) := by
          rw [inf_assoc, inf_eq_right.mpr hI1]
    _ = J.ambient ⊓ coprimeIdeals K m₁ ⊓ coprimeIdeals K (m₁ * m₂) := by rw [e1]
    _ = J.ambient ⊓ coprimeIdeals K m₂ ⊓ coprimeIdeals K (m₁ * m₂) := by
          rw [inf_assoc, inf_eq_right.mpr hI1, inf_assoc, inf_eq_right.mpr hI2]
    _ = L.ambient ⊓ coprimeIdeals K m₂ ⊓ coprimeIdeals K (m₁ * m₂) := by rw [e2]
    _ = L.ambient ⊓ coprimeIdeals K (m₁ * m₂) := by rw [inf_assoc, inf_eq_right.mpr hI2]

/-- Recovering at a smaller modulus preserves the common restriction. -/
theorem gcd_congruence_ambient_restriction (H J : CongruenceSubgroup K)
    (r : Ideal (𝓞 K)) (hr : r ≠ ⊥) (hrH : r ≤ H.modulus) (hrJ : r ≤ J.modulus)
    (heq : H.ambient ⊓ coprimeIdeals K r = J.ambient ⊓ coprimeIdeals K r) :
    ((H.ambient ⊓ coprimeIdeals K r) ⊔
        Subgroup.closure (rayGenerators K (H.modulus ⊔ J.modulus))) ⊓ coprimeIdeals K r =
      H.ambient ⊓ coprimeIdeals K r := by
  apply le_antisymm
  · rintro x ⟨hxs, hxr⟩
    obtain ⟨c, hc, ρ, hρ, rfl⟩ := Subgroup.mem_sup.mp hxs
    obtain ⟨α, hα, rfl⟩ := exists_rayElement_of_mem_closure K _ hρ
    have hαr : toPrincipalIdeal (𝓞 K) K α ∈ coprimeIdeals K r := by
      have h := (coprimeIdeals K r).mul_mem ((coprimeIdeals K r).inv_mem hc.2) hxr
      rwa [inv_mul_cancel_left] at h
    obtain ⟨b, hb₁, hb₂, hbr⟩ :=
      exists_ray_gcd_split K H.modulus J.modulus r hr hrH hrJ α hα hαr
    have hcb : c * toPrincipalIdeal (𝓞 K) K b ∈ J.ambient ⊓ coprimeIdeals K r := by
      rw [← heq]
      exact ⟨H.ambient.mul_mem hc.1 (H.principal_mem_ambient b hb₁),
        (coprimeIdeals K r).mul_mem hc.2 hbr⟩
    have hαb : toPrincipalIdeal (𝓞 K) K (α * b⁻¹) ∈ J.ambient := J.principal_mem_ambient _ hb₂
    have hx : c * toPrincipalIdeal (𝓞 K) K α =
        (c * toPrincipalIdeal (𝓞 K) K b) * toPrincipalIdeal (𝓞 K) K (α * b⁻¹) := by
      rw [map_mul, map_inv, mul_comm (toPrincipalIdeal (𝓞 K) K α)
        (toPrincipalIdeal (𝓞 K) K b)⁻¹, ← mul_assoc, mul_inv_cancel_right]
    rw [heq]
    refine ⟨?_, hxr⟩
    rw [hx]
    exact J.ambient.mul_mem hcb.1 hαb
  · exact le_inf le_sup_left inf_le_right

/-- Janusz V.6.2: equivalent congruence groups descend to the greatest common divisor
of their moduli, represented by the sum of the two integral ideals. -/
theorem exists_congruence_gcd (H J : CongruenceSubgroup K)
    (hHJ : CongruenceEquivalent K H J) :
    ∃ G : CongruenceSubgroup K, G.modulus = H.modulus ⊔ J.modulus ∧
      H.ambient = G.ambient ⊓ coprimeIdeals K H.modulus ∧
      J.ambient = G.ambient ⊓ coprimeIdeals K J.modulus := by
  obtain ⟨r, hr, hrH, hrJ, heq⟩ := hHJ
  set g := H.modulus ⊔ J.modulus with hg
  have hg0 : g ≠ ⊥ := fun h => H.modulus_ne_bot (eq_bot_iff.mpr (h ▸ le_sup_left))
  set A := H.ambient ⊓ coprimeIdeals K r with hA
  set B := A ⊔ Subgroup.closure (rayGenerators K g) with hB
  have hBg : B ≤ coprimeIdeals K g := sup_le
    (inf_le_left.trans (H.ambient_le_coprimeIdeals.trans (coprimeIdeals_mono K le_sup_left)))
    ((Subgroup.closure_le _).mpr (rayGenerators_mem_coprimeIdeals K g))
  have hBr : B ⊓ coprimeIdeals K r = A :=
    gcd_congruence_ambient_restriction K H J r hr hrH hrJ heq
  have key : ∀ C : CongruenceSubgroup K, r ≤ C.modulus → C.modulus ≤ g →
      C.ambient ⊓ coprimeIdeals K r = A → C.ambient = B ⊓ coprimeIdeals K C.modulus := by
    intro C hrC hCg hCA
    apply le_antisymm
    · refine le_inf ?_ C.ambient_le_coprimeIdeals
      intro x hx
      have hx' : x ∈ coprimeIdeals K r ⊔ Subgroup.closure (rayGenerators K C.modulus) := by
        rw [← coprimeIdeals_eq_sup_ray K r C.modulus hr hrC]
        exact C.ambient_le_coprimeIdeals hx
      obtain ⟨u, hu, ρ, hρ, rfl⟩ := Subgroup.mem_sup.mp hx'
      have huC : u ∈ C.ambient := by
        have h := C.ambient.mul_mem hx (C.ambient.inv_mem (C.closure_rayGenerators_le_ambient hρ))
        rwa [mul_inv_cancel_right] at h
      have huA : u ∈ A := by
        rw [← hCA]
        exact ⟨huC, hu⟩
      exact Subgroup.mul_mem_sup huA (Subgroup.closure_mono (rayGenerators_mono K hCg) hρ)
    · rintro x ⟨hxB, hxC⟩
      have hx' : x ∈ coprimeIdeals K r ⊔ Subgroup.closure (rayGenerators K C.modulus) := by
        rw [← coprimeIdeals_eq_sup_ray K r C.modulus hr hrC]
        exact hxC
      obtain ⟨u, hu, ρ, hρ, rfl⟩ := Subgroup.mem_sup.mp hx'
      have hρB : ρ ∈ B :=
        Subgroup.mem_sup_right (Subgroup.closure_mono (rayGenerators_mono K hCg) hρ)
      have huB : u ∈ B := by
        have h := B.mul_mem hxB (B.inv_mem hρB)
        rwa [mul_inv_cancel_right] at h
      have huA : u ∈ A := by
        rw [← hBr]
        exact ⟨huB, hu⟩
      rw [← hCA] at huA
      exact C.ambient.mul_mem huA.1 (C.closure_rayGenerators_le_ambient hρ)
  let G : CongruenceSubgroup K :=
    { modulus := g
      modulus_ne_bot := hg0
      subgroup := B.comap (coprimeIdeals K g).subtype
      contains_ray := Subgroup.comap_mono le_sup_right }
  have hGamb : G.ambient = B := by
    change (B.comap (coprimeIdeals K g).subtype).map (coprimeIdeals K g).subtype = B
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.mpr hBg]
  refine ⟨G, rfl, ?_, ?_⟩
  · rw [hGamb]
    exact key H hrH le_sup_left rfl
  · rw [hGamb]
    exact key J hrJ le_sup_right heq.symm

end Cox.ClassFieldTheory
