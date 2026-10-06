/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinTranslation
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinIntegral
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormSign
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormResidue
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicPrincipal
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicUnramified
import XYin.PhD.Cox.Theorem11_1.ChebotarevFrobenius
import XYin.PhD.Cox.Theorem11_1.ChebotarevIdealSublattice
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicBaseChange
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinModulus

/-! # Finite-modulus cyclotomic reciprocity

The declarations follow Janusz V.5.1.1–5.1.5. The rational principal
calculation retains its sign hypothesis; total complexity supplies that
hypothesis only after base change.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors IsMulCommutative
noncomputable section
namespace Cox.ClassFieldTheory

/-- Janusz V.5.1.1–5.1.2, pp158–159; III.3.3, pp104–105. -/
theorem cyclotomic_baseChange_principal_eq_one
    (L E F : Type*) [Field L] [NumberField L] [Field E] [NumberField E]
    [Field F] [NumberField F]
    [Algebra L F] [Algebra E F]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ n)
    (hgen : Algebra.adjoin E (Set.range (algebraMap L F)) = ⊤)
    (hU : IsUnramifiedAway ℚ (Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))) L)
    (φ : coprimeIdeals ℚ (Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))) →* (L ≃ₐ[ℚ] L))
    (hφ : IsArtinMap ℚ (Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))) L φ)
    (ψ : coprimeIdeals E ((Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map
      (algebraMap (𝓞 ℚ) (𝓞 E))) →* (F ≃ₐ[E] F))
    (hψ : IsArtinMap E ((Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map
      (algebraMap (𝓞 ℚ) (𝓞 E))) F ψ)
    (a : 𝓞 E) (ha : a ≠ 0) (hN : 0 ≤ Algebra.norm ℤ a)
    (hcong : a - 1 ∈ (Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map
      (algebraMap (𝓞 ℚ) (𝓞 E)))
    (u : coprimeIdeals E ((Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map
      (algebraMap (𝓞 ℚ) (𝓞 E))))
    (hu : ((u : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      (Ideal.span ({a} : Set (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) : ψ u = 1 := by
  letI := IsCyclotomicExtension.isAbelianGalois {n} ℚ L
  let m : Ideal (𝓞 ℚ) := Ideal.span {(n : 𝓞 ℚ)}
  let A : Ideal (𝓞 E) := Ideal.span {a}
  let b : 𝓞 ℚ := Algebra.intNorm (𝓞 ℚ) (𝓞 E) a
  have hA : A ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp ha
  have hAm : A ⊔ m.map (algebraMap (𝓞 ℚ) (𝓞 E)) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hmem := (A ⊔ m.map (algebraMap (𝓞 ℚ) (𝓞 E))).sub_mem
      (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))
      (Ideal.mem_sup_right hcong)
    simpa only [sub_sub_cancel] using hmem
  obtain ⟨uN, huN⟩ := exists_coprime_relNorm_unit ℚ E m A hA hAm
  have hb : b ≠ 0 := (Algebra.intNorm_eq_zero).not.mpr ha
  have hbideal : Ideal.relNorm (𝓞 ℚ) A = Ideal.span {b} := Ideal.relNorm_singleton (𝓞 ℚ) a
  have hbN : Algebra.norm ℤ b = Algebra.norm ℤ a := by
    rw [norm_int_rat_eq, rat_intNorm_eq_norm_int]
  have hpositive : 0 ≤ Algebra.norm ℤ b := by
    rw [hbN]
    exact hN
  have hresidue : (Algebra.norm ℤ b : ZMod n) = 1 := by
    rw [hbN]
    apply norm_int_zmod_eq_one E n a
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hcong
  have hφone : φ uN = 1 := by
    rw [artin_eq_frobeniusIdeal ℚ m L hU φ hφ (Ideal.span {b})
      (mt Ideal.span_singleton_eq_bot.mp hb)
      (by simpa only [← hbideal] using relNorm_coprime ℚ E m A hAm) uN
      (by simpa only [hbideal] using huN)]
    exact frobenius_principal_eq_one ℚ L n ζ hζ b hb hpositive hresidue
  have hres := artin_baseChange_quotient_norm ℚ L E F m φ hφ hU ψ hψ u A ⊤ hA
    (by simp) hAm (by simp)
    (by simpa only [FractionalIdeal.coeIdeal_top, mul_one] using hu)
    uN (by simpa only [Ideal.relNorm_top, FractionalIdeal.coeIdeal_top, mul_one] using huN)
  apply compositum_restriction_injective ℚ L E F hgen
  beta_reduce
  rw [hres, hφone]
  change 1 = (AlgEquiv.restrictNormalHom L) (1 : F ≃ₐ[ℚ] F)
  exact (map_one _).symm

-- The original totally-complex application supplies the sign premise.
/-- Janusz V.5.1.1–5.1.2, pp158–159; III.3.3, pp104–105. -/
theorem cyclotomic_baseChange_ray_le_ker
    (L E F : Type*) [Field L] [NumberField L] [Field E] [NumberField E] [IsTotallyComplex E]
    [Field F] [NumberField F]
    [Algebra L F] [Algebra E F]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ n)
    (hgen : Algebra.adjoin E (Set.range (algebraMap L F)) = ⊤)
    (hU : IsUnramifiedAway ℚ (Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))) L)
    (φ : coprimeIdeals ℚ (Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))) →* (L ≃ₐ[ℚ] L))
    (hφ : IsArtinMap ℚ (Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))) L φ)
    (ψ : coprimeIdeals E ((Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map
      (algebraMap (𝓞 ℚ) (𝓞 E))) →* (F ≃ₐ[E] F))
    (hψ : IsArtinMap E ((Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map
      (algebraMap (𝓞 ℚ) (𝓞 E))) F ψ) :
    raySubgroup E ((Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map
      (algebraMap (𝓞 ℚ) (𝓞 E))) ≤ ψ.ker := by
  let m : Ideal (𝓞 E) := (Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map
    (algebraMap (𝓞 ℚ) (𝓞 E))
  have hg : rayGenerators E m ⊆ ψ.ker.map (coprimeIdeals E m).subtype := by
    intro u hu
    have huI := rayGenerators_mem_coprimeIdeals E m hu
    refine ⟨⟨u, huI⟩, ?_, rfl⟩
    rcases hu with ⟨a, ha, hcong, hua⟩
    have hN : 0 ≤ Algebra.norm ℤ a := by
      have hs := norm_nonneg_of_isTotallyComplex E (a : E)
      rw [← Algebra.coe_norm_int] at hs
      exact_mod_cast hs
    apply cyclotomic_baseChange_principal_eq_one L E F n ζ hζ hgen hU φ hφ ψ hψ
      a ha hN hcong
    simpa only [FractionalIdeal.coeIdeal_span_singleton] using hua
  intro u hu
  have hmapped := (Subgroup.closure_le _).mpr hg hu
  rcases hmapped with ⟨v, hv, hvu⟩
  have hvu' : v = u := Subtype.ext hvu
  simpa only [hvu'] using hv

/-- Janusz III.3.3, pp104–105: cyclotomic ramification support. -/
theorem cyclotomic_isUnramifiedAway
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} K L] :
    IsUnramifiedAway K (Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) L := by
  letI := IsCyclotomicExtension.isGalois {n} K L
  intro q hq hq0 hqn
  letI := hq
  have hcop : q.absNorm.Coprime n :=
    Cox.Chebotarev.absNorm_coprime_of_isCoprime_span
      ⟨q, by simpa only [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot] using hq0⟩ n
      (Ideal.isCoprime_iff_sup_eq.mpr hqn)
  have hU := CyclotomicUnramified.unramifiedIn_cyclotomic_of_coprime K L n q hq0 hcop
  intro P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver q := hP.2
  have hram := Cox.Chebotarev.UnramifiedIn.ramificationIdx_eq_one K L hU P hP.2
  simpa only [← Ideal.over_def P q] using hram

/-- Janusz V.5.1.4, p158. -/
theorem cyclotomic_ray_le_artin_ker
    (K L : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    [Field L] [NumberField L] [Algebra K L]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ n)
    (ψ : coprimeIdeals K (Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) →* (L ≃ₐ[K] L))
    (hψ : IsArtinMap K (Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) L ψ) :
    raySubgroup K (Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) ≤ ψ.ker := by
  let Qζ : IntermediateField ℚ L := IntermediateField.adjoin ℚ {ζ}
  let ζ₀ : Qζ := ⟨ζ, IntermediateField.subset_adjoin _ _ (Set.mem_singleton ζ)⟩
  have hζ₀ : IsPrimitiveRoot ζ₀ n := IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ
  letI : IsCyclotomicExtension {n} ℚ Qζ :=
    CyclotomicBaseChange.rootField_isCyclotomic n (NeZero.pos n) ζ hζ
  letI := IsCyclotomicExtension.isAbelianGalois {n} ℚ Qζ
  let m : Ideal (𝓞 ℚ) := Ideal.span {(n : 𝓞 ℚ)}
  have hU : IsUnramifiedAway ℚ m Qζ := cyclotomic_isUnramifiedAway ℚ Qζ n
  let φ := arithmeticArtin ℚ m Qζ
  have hφ : IsArtinMap ℚ m Qζ φ := arithmeticArtin_isArtinMap ℚ m Qζ hU
  have hgen : Algebra.adjoin K (Set.range (algebraMap Qζ L)) = ⊤ := by
    apply top_unique
    rw [← IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]
    apply Algebra.adjoin_mono
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨ζ₀, rfl⟩
  have h : ∀ (ψ : coprimeIdeals K (Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) →*
      (L ≃ₐ[K] L)), IsArtinMap K (Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) L ψ →
      raySubgroup K (Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) ≤ ψ.ker := by
    have hraw := cyclotomic_baseChange_ray_le_ker Qζ K L n ζ₀ hζ₀ hgen hU φ hφ
    have hm : (Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map
        (algebraMap (𝓞 ℚ) (𝓞 K)) = Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    change ∀ (ψ : coprimeIdeals K ((Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map
      (algebraMap (𝓞 ℚ) (𝓞 K))) →* (L ≃ₐ[K] L)),
      IsArtinMap K ((Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map
        (algebraMap (𝓞 ℚ) (𝓞 K))) L ψ →
      raySubgroup K ((Ideal.span ({(n : 𝓞 ℚ)} : Set (𝓞 ℚ))).map
        (algebraMap (𝓞 ℚ) (𝓞 K))) ≤ ψ.ker at hraw
    rw [hm] at hraw
    exact hraw
  exact h ψ hψ

/-- Janusz V.5.1.4–5.1.5, pp158–159. -/
theorem cyclotomic_subfield_ray_le_artin_ker
    (K L : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    [Field L] [NumberField L] [Algebra K L]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} K L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ n)
    (E : IntermediateField K L) (m : Ideal (𝓞 K))
    (hm : m ≤ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)))
    (ψ : coprimeIdeals K m →* (E ≃ₐ[K] E)) (hψ : IsArtinMap K m E ψ) :
    raySubgroup K m ≤ ψ.ker := by
  letI := IsCyclotomicExtension.isAbelianGalois {n} K L
  let nI : Ideal (𝓞 K) := Ideal.span {(n : 𝓞 K)}
  have hUn : IsUnramifiedAway K nI L := cyclotomic_isUnramifiedAway K L n
  have hUm : IsUnramifiedAway K m L := by
    intro q hq hq0 hqm
    exact hUn q hq hq0 (top_unique (hqm ▸ sup_le_sup_left hm q))
  let φn := arithmeticArtin K nI L
  let φm := arithmeticArtin K m L
  have hnArtin : IsArtinMap K nI L φn := arithmeticArtin_isArtinMap K nI L hUn
  have hmArtin : IsArtinMap K m L φm := arithmeticArtin_isArtinMap K m L hUm
  have hnRay : raySubgroup K nI ≤ φn.ker :=
    cyclotomic_ray_le_artin_ker K L n ζ hζ φn hnArtin
  have hmRay : raySubgroup K m ≤ φm.ker :=
    ray_le_artin_ker_of_modulus_le K L m nI hm hUm φn hnArtin φm hmArtin hnRay
  exact ray_le_artin_ker_subfield K L E m
    (isUnramifiedAway_subfield K m L E hUm) φm hmArtin ψ hψ hmRay

end Cox.ClassFieldTheory
