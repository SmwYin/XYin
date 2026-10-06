/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldPairedDefs
import XYin.PhD.Cox.Theorem11_1.ClassFieldSupportedModulus
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnitIndices

/-! # The deletion map in Janusz V.9.9

The map is the actual principal ideal map followed by deletion of supported prime
factors. Its surjectivity and ray containment follow the book's factorization.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Class equality in the actual fraction field is equality modulo principal ideals. -/
theorem classGroup_mk_eq_iff {R : Type*} [CommRing R] [IsDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    (I J : (FractionalIdeal R⁰ F)ˣ) :
    ClassGroup.mk F I = ClassGroup.mk F J ↔
      I * J⁻¹ ∈ (toPrincipalIdeal R F).range := by
  rw [← div_eq_one, ← map_div, ClassGroup.mk_eq_one_iff, mem_principal_ideals_iff,
    div_eq_mul_inv]
  constructor
  · rintro ⟨⟨x, hx⟩⟩
    exact ⟨x, FractionalIdeal.coeToSubmodule_inj.mp
      (by rw [FractionalIdeal.coe_spanSingleton]; exact hx.symm)⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, by rw [← hx, FractionalIdeal.coe_spanSingleton]⟩⟩

/-- A class representative supported on S gives the source factorization A = B(a). -/
theorem exists_supported_mul_principal
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : SupportsClassRepresentatives K S)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ B : (FractionalIdeal (𝓞 K)⁰ K)ˣ, B ∈ supportedIdeals K S ∧
      ∃ a : Kˣ, I = B * toPrincipalIdeal (𝓞 K) K a := by
  obtain ⟨B, hB, hBI⟩ := hS (ClassGroup.mk K I)
  obtain ⟨a, ha⟩ := (classGroup_mk_eq_iff K I B).mp hBI.symm
  refine ⟨B, hB, a, ?_⟩
  rw [ha, mul_comm I, mul_inv_cancel_left]

/-- A positive support modulus has exactly the specified supported ideal group. -/
theorem modulusSupported_supportModulus (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t : ℕ) (ht : 0 < t) :
    modulusSupportedIdeals K (supportModulus K S t) = supportedIdeals K S := by
  unfold modulusSupportedIdeals supportedIdeals
  congr 1
  ext u
  simp only [Set.mem_setOf_eq, supportModulus_le_prime_iff K S t ht]

/-- The product of the two positive support moduli has their combined support. -/
theorem modulusSupported_paired (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hdisj : Disjoint S T) (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    modulusSupportedIdeals K (supportModulus K S s * supportModulus K T t) =
      supportedIdeals K (S.disjUnion T hdisj) := by
  unfold modulusSupportedIdeals supportedIdeals
  congr 1
  ext u
  simp only [Set.mem_setOf_eq, Finset.mem_disjUnion]
  constructor
  · rintro ⟨v, hv, hu⟩
    rcases (Ideal.IsPrime.mul_le v.isPrime).mp hv with h | h
    · exact ⟨v, Or.inl ((supportModulus_le_prime_iff K S s hs v).mp h), hu⟩
    · exact ⟨v, Or.inr ((supportModulus_le_prime_iff K T t ht v).mp h), hu⟩
  · rintro ⟨v, hv, hu⟩
    refine ⟨v, (Ideal.IsPrime.mul_le v.isPrime).mpr ?_, hu⟩
    rcases hv with h | h
    · exact Or.inl ((supportModulus_le_prime_iff K S s hs v).mpr h)
    · exact Or.inr ((supportModulus_le_prime_iff K T t ht v).mpr h)

/-- Principal ideals followed by deletion are onto when the support represents every class. -/
theorem erasePrincipal_surjective_of_classRepresentatives
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : SupportsClassRepresentatives K S)
    (m : Ideal (𝓞 K)) (hm : modulusSupportedIdeals K m = supportedIdeals K S) :
    Function.Surjective ((eraseModulusFactors K m).comp (toPrincipalIdeal (𝓞 K) K)) := by
  intro I
  obtain ⟨B, hB, a, ha⟩ := exists_supported_mul_principal K S hS I
  refine ⟨a, ?_⟩
  have hPa : toPrincipalIdeal (𝓞 K) K a = B⁻¹ * (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
    rw [ha, inv_mul_cancel_left]
  have hB' : B ∈ modulusSupportedIdeals K m := by
    rw [hm]
    exact hB
  rw [MonoidHom.comp_apply, hPa, map_mul, map_inv, eraseModulusFactors_supported K m B hB',
    inv_one, one_mul, eraseModulusFactors_coprime]

/-- The first isomorphism theorem for the preimage of a subgroup under a surjection. -/
theorem quotientComapEquiv_of_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (N : Subgroup H) [N.Normal] :
    Nonempty ((G ⧸ N.comap f) ≃* (H ⧸ N)) := by
  let q : G →* H ⧸ N := (QuotientGroup.mk' N).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective N).comp hf
  have hker : q.ker = N.comap f := by
    ext x
    simp [q, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)⟩

/-- A combined-support ideal coprime to the first support is supported on the second. -/
theorem supported_union_coprime_left
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S T)
    (s : ℕ) (hs : 0 < s) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hI : I ∈ supportedIdeals K (S.disjUnion T hdisj))
    (hgood : I ∈ coprimeIdeals K (supportModulus K S s)) :
    I ∈ supportedIdeals K T := by
  rw [mem_supportedIdeals_iff_count_eq_zero] at hI ⊢
  rw [mem_coprimeIdeals_iff_count_eq_zero] at hgood
  intro v hvT
  by_cases hvS : v ∈ S
  · exact hgood v ((supportModulus_le_prime_iff K S s hs v).mpr hvS)
  · exact hI v (by rw [Finset.mem_disjUnion]; exact fun h => h.elim hvS hvT)

/-- Deleting the combined support from an ideal coprime to the first removes only the second. -/
theorem removedFactor_mem_opposite
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S T)
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hgood : I ∈ coprimeIdeals K (supportModulus K S s)) :
    I * (eraseModulusFactors K (supportModulus K S s * supportModulus K T t) I :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹ ∈ supportedIdeals K T := by
  have hC : I * (eraseModulusFactors K (supportModulus K S s * supportModulus K T t) I :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹ ∈ supportedIdeals K (S.disjUnion T hdisj) := by
    rw [← modulusSupported_paired K S T hdisj s t hs ht]
    exact eraseModulusFactors_spec K _ I
  have hjI : (eraseModulusFactors K (supportModulus K S s * supportModulus K T t) I :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ coprimeIdeals K (supportModulus K S s) := by
    have h := (eraseModulusFactors K (supportModulus K S s * supportModulus K T t) I).2
    rw [mem_coprimeIdeals_iff_count_eq_zero] at h ⊢
    exact fun p hp => h p (le_trans Ideal.mul_le_right hp)
  exact supported_union_coprime_left K S T hdisj s hs _ hC
    (Subgroup.mul_mem _ hgood (Subgroup.inv_mem _ hjI))

/-- The erased principal ideal of a ray element belongs to the actual paired subgroup. -/
theorem erased_ray_principal_mem_paired
    (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S T)
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (a : Kˣ)
    (ha : a ∈ rayElements K (supportModulus K S s)) :
    (eraseModulusFactors K (supportModulus K S s * supportModulus K T t)
      (toPrincipalIdeal (𝓞 K) K a) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈
      (pairedSubgroup K n (supportModulus K S s) T).map
        (coprimeIdeals K (supportModulus K S s)).subtype := by
  have hI := principal_mem_coprime_of_mem_rayElements K _ a ha
  have hC := removedFactor_mem_opposite K S T hdisj s t hs ht _ hI
  obtain ⟨X, hX, hXeq⟩ := Subgroup.mem_map.mp (principal_mem_ray_of_mem_rayElements K _ a ha)
  have hjcop : (eraseModulusFactors K (supportModulus K S s * supportModulus K T t)
      (toPrincipalIdeal (𝓞 K) K a) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈
        coprimeIdeals K (supportModulus K S s) := by
    have h := (eraseModulusFactors K (supportModulus K S s * supportModulus K T t)
      (toPrincipalIdeal (𝓞 K) K a)).2
    rw [mem_coprimeIdeals_iff_count_eq_zero] at h ⊢
    exact fun p hp => h p (le_trans Ideal.mul_le_right hp)
  have hCcop := Subgroup.mul_mem _ hI (Subgroup.inv_mem _ hjcop)
  refine Subgroup.mem_map.mpr ⟨⟨_, hjcop⟩, ?_, rfl⟩
  have hJ : (⟨_, hjcop⟩ : coprimeIdeals K (supportModulus K S s)) =
      X * (⟨_, hCcop⟩ : coprimeIdeals K (supportModulus K S s))⁻¹ := by
    apply Subtype.ext
    change _ = (X : (FractionalIdeal (𝓞 K)⁰ K)ˣ) * (toPrincipalIdeal (𝓞 K) K a *
      (eraseModulusFactors K (supportModulus K S s * supportModulus K T t)
        (toPrincipalIdeal (𝓞 K) K a) : (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹)⁻¹
    rw [show (X : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = toPrincipalIdeal (𝓞 K) K a from hXeq]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [hJ]
  refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ ?_)
  · exact (le_sup_left.trans le_sup_left :
      raySubgroup K (supportModulus K S s) ≤ pairedSubgroup K n (supportModulus K S s) T) hX
  · exact (le_sup_right : _ ≤ pairedSubgroup K n (supportModulus K S s) T) hC

/-- The paired subgroup preimage is contained in powers, supported units, and ray elements. -/
theorem erased_principal_preimage_le
    (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S T)
    (hreps : SupportsClassRepresentatives K (S.disjUnion T hdisj))
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (a : Kˣ)
    (ha : (eraseModulusFactors K (supportModulus K S s * supportModulus K T t)
      (toPrincipalIdeal (𝓞 K) K a) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈
      (pairedSubgroup K n (supportModulus K S s) T).map
        (coprimeIdeals K (supportModulus K S s)).subtype) :
    a ∈ nthPowers K n ⊔ sUnits K (S.disjUnion T hdisj) ⊔
      rayElements K (supportModulus K S s) := by
  obtain ⟨X, hX, hXJ⟩ := Subgroup.mem_map.mp ha
  obtain ⟨B, u, C, hu, hC, hXeq⟩ :=
    pairedSubgroup_mem_factorization K n (supportModulus K S s) T X hX
  obtain ⟨B₀, hB₀, d, hBd⟩ := exists_supported_mul_principal K (S.disjUnion T hdisj) hreps B
  have hD : toPrincipalIdeal (𝓞 K) K a * (eraseModulusFactors K
      (supportModulus K S s * supportModulus K T t) (toPrincipalIdeal (𝓞 K) K a) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹ ∈ supportedIdeals K (S.disjUnion T hdisj) := by
    rw [← modulusSupported_paired K S T hdisj s t hs ht]
    exact eraseModulusFactors_spec K _ _
  have hCST : C ∈ supportedIdeals K (S.disjUnion T hdisj) := by
    rw [mem_supportedIdeals_iff_count_eq_zero] at hC ⊢
    intro v hv
    exact hC v (fun hvT => hv (Finset.mem_disjUnion.mpr (Or.inr hvT)))
  have hJ : (eraseModulusFactors K (supportModulus K S s * supportModulus K T t)
      (toPrincipalIdeal (𝓞 K) K a) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      (B₀ * toPrincipalIdeal (𝓞 K) K d) ^ n * toPrincipalIdeal (𝓞 K) K u * C := by
    rw [← hBd, ← hXeq]
    exact hXJ.symm
  have hz : a * (d ^ n * u)⁻¹ ∈ sUnits K (S.disjUnion T hdisj) := by
    have hPz : toPrincipalIdeal (𝓞 K) K (a * (d ^ n * u)⁻¹) =
        (toPrincipalIdeal (𝓞 K) K a * (eraseModulusFactors K
          (supportModulus K S s * supportModulus K T t) (toPrincipalIdeal (𝓞 K) K a) :
            (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹) * B₀ ^ n * C := by
      rw [hJ, map_mul, map_inv, map_mul, map_pow, mul_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    change toPrincipalIdeal (𝓞 K) K (a * (d ^ n * u)⁻¹) ∈ supportedIdeals K (S.disjUnion T hdisj)
    rw [hPz]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hD (Subgroup.pow_mem _ hB₀ n)) hCST
  have ha_eq : a = d ^ n * (a * (d ^ n * u)⁻¹) * u := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  rw [ha_eq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨d, rfl⟩))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hz))) (Subgroup.mem_sup_right hu)

/-- Powers, supported units, and ray elements lie in the paired subgroup preimage. -/
theorem le_erased_principal_preimage
    (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S T)
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    nthPowers K n ⊔ sUnits K (S.disjUnion T hdisj) ⊔ rayElements K (supportModulus K S s) ≤
      (((pairedSubgroup K n (supportModulus K S s) T).map
        (coprimeIdeals K (supportModulus K S s)).subtype).comap
          (coprimeIdeals K (supportModulus K S s * supportModulus K T t)).subtype).comap
        ((eraseModulusFactors K (supportModulus K S s * supportModulus K T t)).comp
          (toPrincipalIdeal (𝓞 K) K)) := by
  have hcop : ∀ J ∈ coprimeIdeals K (supportModulus K S s * supportModulus K T t),
      J ∈ coprimeIdeals K (supportModulus K S s) := by
    intro J hJ
    rw [mem_coprimeIdeals_iff_count_eq_zero] at hJ ⊢
    exact fun p hp => hJ p (le_trans Ideal.mul_le_right hp)
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro a ⟨b, rfl⟩
    have hb := hcop _ (eraseModulusFactors K (supportModulus K S s * supportModulus K T t)
      (toPrincipalIdeal (𝓞 K) K b)).2
    change (eraseModulusFactors K (supportModulus K S s * supportModulus K T t)
        (toPrincipalIdeal (𝓞 K) K (b ^ n)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈
      (pairedSubgroup K n (supportModulus K S s) T).map
        (coprimeIdeals K (supportModulus K S s)).subtype
    refine Subgroup.mem_map.mpr ⟨⟨_, hb⟩ ^ n, ?_, ?_⟩
    · exact (le_sup_right.trans le_sup_left :
        (powMonoidHom n : coprimeIdeals K (supportModulus K S s) →*
          coprimeIdeals K (supportModulus K S s)).range ≤
          pairedSubgroup K n (supportModulus K S s) T) ⟨⟨_, hb⟩, rfl⟩
    · simp [map_pow]
  · intro a ha
    have h1 : toPrincipalIdeal (𝓞 K) K a ∈
        modulusSupportedIdeals K (supportModulus K S s * supportModulus K T t) := by
      rw [modulusSupported_paired K S T hdisj s t hs ht]
      exact ha
    change (eraseModulusFactors K (supportModulus K S s * supportModulus K T t)
        (toPrincipalIdeal (𝓞 K) K a) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈
      (pairedSubgroup K n (supportModulus K S s) T).map
        (coprimeIdeals K (supportModulus K S s)).subtype
    rw [eraseModulusFactors_supported K _ _ h1]
    exact Subgroup.one_mem _
  · intro a ha
    exact erased_ray_principal_mem_paired K n S T hdisj s t hs ht a ha

end Cox.ClassFieldTheory
