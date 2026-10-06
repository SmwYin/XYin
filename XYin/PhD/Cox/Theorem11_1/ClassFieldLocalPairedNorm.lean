/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalTranslation
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalNorm

/-! # The paired-subgroup norm containment in Janusz V.11.2

This is the finite-prime calculation on printed p. 185. Erasure expresses exactly the
cancellation of the supported factor in `X = B^q (α) C`: the erased norm of `B` has Artin
image in `D`, its `[D : G₀]`-th power lies in `G₀`, and the norm of a ray element does too.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K F : Type*) [Field K] [hNF_K : NumberField K] [Field F] [hNF_F : NumberField F]
  [Algebra K F]

include hNF_K hNF_F in
/-- The field norm sends an upstairs ray unit to a downstairs ray unit. -/
theorem fieldNorm_mem_rayElements (m : Ideal (𝓞 K)) (m' : Ideal (𝓞 F))
    (hmm' : m' ≤ m.map (algebraMap (𝓞 K) (𝓞 F)))
    (u : Fˣ) (hu : u ∈ rayElements F m') :
    Units.map (Algebra.norm K) u ∈ rayElements K m := by
  haveI : Module.Finite (𝓞 K) (𝓞 F) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 F)
  haveI : FiniteDimensional K F := Module.Finite.of_restrictScalars_finite ℚ K F
  have hle : rayElements F m' ≤
      (rayElements K m).comap (Units.map (Algebra.norm K : F →* K)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨α, hαu, hαm⟩
    refine Subgroup.subset_closure ⟨Algebra.intNorm (𝓞 K) (𝓞 F) α, ?_,
      intNorm_sub_one_mem K F m α (hmm' hαm)⟩
    change algebraMap (𝓞 K) K (Algebra.intNorm (𝓞 K) (𝓞 F) α) = Algebra.norm K (u : F)
    rw [Algebra.algebraMap_intNorm (L := F), ← hαu]
  exact hle hu

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
include hNF_K hNF_F in
/-- The selected opposite primes are supported at the finer extended base modulus. -/
theorem supportedIdeals_le_extended_modulus (m : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S, m.map (algebraMap (𝓞 K) (𝓞 F)) ≤ v.asIdeal) :
    supportedIdeals F S ≤
      modulusSupportedIdeals F (m.map (algebraMap (𝓞 K) (𝓞 F))) := by
  refine Subgroup.closure_mono ?_
  rintro u ⟨v, hv, hu⟩
  exact ⟨v, hS v hv, hu⟩

variable (L : Type*) [Field L] [hNF_L : NumberField L] [Algebra K L] [IsAbelianGalois K L]

include hNF_K hNF_F hNF_L in
/-- Norms from a field containing the fixed field of D have Artin image in D,
even after removing the modulus factors. -/
theorem artin_erased_norm_mem_subgroup
    (D : Subgroup (L ≃ₐ[K] L)) [Algebra (IntermediateField.fixedField D) F]
    [IsScalarTower K (IntermediateField.fixedField D) F]
    (n : Ideal (𝓞 K))
    (φ : coprimeIdeals K n →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K n L φ)
    (hU : IsUnramifiedAway K n L) (B : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    φ (eraseModulusFactors K n (idealUnitNorm K F B)) ∈ D := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : IsAbelianGalois K (IntermediateField.fixedField D) :=
    IsAbelianGalois.tower_bot K (IntermediateField.fixedField D) L
  haveI : NumberField (IntermediateField.fixedField D) :=
    NumberField.of_module_finite K (IntermediateField.fixedField D)
  haveI : Module.Finite (𝓞 K) (𝓞 (IntermediateField.fixedField D)) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Finite (𝓞 K) (𝓞 F) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Finite (𝓞 (IntermediateField.fixedField D)) (𝓞 F) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  have hEr := idealUnitNorm_erase K F n B
  have hmapZ : (n.map (algebraMap (𝓞 K) (𝓞 (IntermediateField.fixedField D)))).map
      (algebraMap (𝓞 (IntermediateField.fixedField D)) (𝓞 F)) =
        n.map (algebraMap (𝓞 K) (𝓞 F)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hB'Z : (eraseModulusFactors F (n.map (algebraMap (𝓞 K) (𝓞 F))) B :
      (FractionalIdeal (𝓞 F)⁰ F)ˣ) ∈ coprimeIdeals F
        ((n.map (algebraMap (𝓞 K) (𝓞 (IntermediateField.fixedField D)))).map
          (algebraMap (𝓞 (IntermediateField.fixedField D)) (𝓞 F))) := by
    rw [hmapZ]
    exact (eraseModulusFactors F (n.map (algebraMap (𝓞 K) (𝓞 F))) B).2
  have hC := idealUnitNorm_coprime (IntermediateField.fixedField D) F _ _ hB'Z
  have hnorm := idealUnitNorm_mem_normImage K (IntermediateField.fixedField D) n ⟨_, hC⟩
  have hUZ := isUnramifiedAway_subfield K n L (IntermediateField.fixedField D) hU
  have hφZ := isArtinMap_restrict K n L (IntermediateField.fixedField D) φ hφ
  have hker := normImage_le_artin_ker K n (IntermediateField.fixedField D) hUZ _ hφZ hnorm
  have heq : (⟨idealUnitNorm K (IntermediateField.fixedField D) (idealUnitNorm
      (IntermediateField.fixedField D) F (eraseModulusFactors F
        (n.map (algebraMap (𝓞 K) (𝓞 F))) B)), idealUnitNorm_coprime K _ n _ hC⟩ :
          coprimeIdeals K n) = eraseModulusFactors K n (idealUnitNorm K F B) := by
    apply Subtype.ext
    change idealUnitNorm K (IntermediateField.fixedField D) (idealUnitNorm
      (IntermediateField.fixedField D) F (eraseModulusFactors F
        (n.map (algebraMap (𝓞 K) (𝓞 F))) B)) = _
    rw [idealUnitNorm_tower K (IntermediateField.fixedField D) F, hEr]
  rw [MonoidHom.mem_ker, heq, MonoidHom.comp_apply] at hker
  rw [← IntermediateField.fixingSubgroup_fixedField D, ← IntermediateField.restrictNormalHom_ker,
    MonoidHom.mem_ker]
  exact hker

-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
include hNF_K hNF_F hNF_L in
/-- Janusz p185's norm containment: the q-th power, ray-principal and supported
factors each have the required Artin image. -/
theorem pairedSubgroup_erased_norm_mem
    (D G₀ : Subgroup (L ≃ₐ[K] L)) (hG₀ : G₀ ≤ D)
    [Algebra (IntermediateField.fixedField D) F]
    [IsScalarTower K (IntermediateField.fixedField D) F]
    (n m : Ideal (𝓞 K)) (m' : Ideal (𝓞 F))
    (hmm' : m' ≤ m.map (algebraMap (𝓞 K) (𝓞 F)))
    (φ : coprimeIdeals K n →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K n L φ)
    (hU : IsUnramifiedAway K n L)
    (hray : ∀ u : Kˣ, u ∈ rayElements K m →
      φ (eraseModulusFactors K n (toPrincipalIdeal (𝓞 K) K u)) ∈ G₀)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S, n.map (algebraMap (𝓞 K) (𝓞 F)) ≤ v.asIdeal)
    (X : coprimeIdeals F m')
    (hX : X ∈ pairedSubgroup F (G₀.relIndex D) m' S) :
    φ (eraseModulusFactors K n (idealUnitNorm K F X)) ∈ G₀ := by
  haveI : Module.Finite (𝓞 K) (𝓞 F) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 F)
  haveI : G₀.Normal := ⟨fun g hg x => by
    have hc : x * g = g * x :=
      (inferInstance : IsMulCommutative (L ≃ₐ[K] L)).is_comm.comm x g
    rw [hc, mul_inv_cancel_right]
    exact hg⟩
  obtain ⟨B, u, C, hu, hC, hX'⟩ := pairedSubgroup_mem_factorization F (G₀.relIndex D) m' S X hX
  have hC' := supportedIdeals_le_extended_modulus K F n S hS hC
  rw [hX', erase_norm_paired_product K F n (G₀.relIndex D) _ C u hC', map_mul, map_pow]
  exact G₀.mul_mem (Subgroup.pow_relIndex_mem G₀
      (artin_erased_norm_mem_subgroup K F L D n φ hφ hU _))
    (hray _ (fieldNorm_mem_rayElements K F m m' hmm' u hu))

include hNF_K hNF_F in
/-- For a good X, norm-preimage membership is the unerased norm condition. -/
theorem mem_normPreimage_iff_idealUnitNorm
    [Module.Finite (𝓞 K) (𝓞 F)] (H : CongruenceSubgroup K)
    (X : coprimeIdeals F (H.modulus.map (algebraMap (𝓞 K) (𝓞 F)))) :
    X ∈ normPreimage K F H ↔
      (⟨idealUnitNorm K F X,
        idealUnitNorm_coprime K F H.modulus X X.property⟩ :
          coprimeIdeals K H.modulus) ∈ H.subgroup := by
  have key : ∀ A B : Ideal (𝓞 F), B ≠ ⊥ →
      ((X : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) * B = A →
        ((idealUnitNorm K F X : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
          (Ideal.relNorm (𝓞 K) B : FractionalIdeal (𝓞 K)⁰ K) = Ideal.relNorm (𝓞 K) A := by
    intro A B hB hXAB
    have hBne : (B : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hB
    have h1 := idealUnitNorm_integral K F (Units.mk0 _ hBne) B rfl
    have h2 := idealUnitNorm_integral K F ((X : (FractionalIdeal (𝓞 F)⁰ F)ˣ) * Units.mk0 _ hBne) A
      (by rw [Units.val_mul, Units.val_mk0, hXAB])
    rw [map_mul, Units.val_mul, h1] at h2
    exact h2
  constructor
  · intro hX
    obtain ⟨A, B, -, hB, -, -, hXAB, v, hv, hvn⟩ := (mem_normPreimage_iff K F H X).mp hX
    have hNB : (Ideal.relNorm (𝓞 K) B : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (Ideal.relNorm_eq_bot_iff.not.mpr hB)
    have hvX : (⟨idealUnitNorm K F X, idealUnitNorm_coprime K F H.modulus X X.property⟩ :
        coprimeIdeals K H.modulus) = v := by
      apply Subtype.ext
      apply Units.ext
      exact mul_right_cancel₀ hNB ((key A B hB hXAB).trans hvn.symm)
    rw [hvX]
    exact hv
  · intro hX
    obtain ⟨A, B, hA, hB, hAm, hBm, hXAB⟩ := exists_coprime_ideal_quotient F _ X
    exact (mem_normPreimage_iff K F H X).mpr
      ⟨A, B, hA, hB, hAm, hBm, hXAB, _, hX, key A B hB hXAB⟩

end Cox.ClassFieldTheory
