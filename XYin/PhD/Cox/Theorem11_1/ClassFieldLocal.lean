/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalArtinKernel
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalUnitNorm
import XYin.PhD.Cox.Theorem11_1.ClassFieldConductorCriterion
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory

/-!
# Local Artin maps and conductor support

Janusz V.11–12 obtains the local maps from global reciprocity and approximation, then
identifies their kernels with the local norm groups by a local norm-index calculation. This
gives the conductor-support theorem (a prime divides the conductor exactly when it ramifies)
and Cox's fixed-modulus existence statement. Definitions use actual completions, determinant
norms, ideal factor removal and decomposition groups.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise WithZero

noncomputable section

namespace Cox.ClassFieldTheory

variable (K : Type*) [Field K] [NumberField K]

section Extension

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]

/-- A local Artin map is characterized by its decomposition-group image and by its
agreement on global elements congruent to one away from `v`. This definition does
not mention the local norm group or conductor. -/
def IsLocalArtinMap (m : Ideal (𝓞 K)) (a : ℕ)
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L))
    (θ : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L)) : Prop :=
  θ.range = MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal ∧
    ∀ x : rayElements K m,
      θ (Units.map (FinitePlace.embedding v).toMonoidHom (x : Kˣ)) =
        φ (eraseModulusFactors K (v.asIdeal ^ a * m) (toPrincipalIdeal (𝓞 K) K x))

/-- Janusz V.12.1: approximation identifies the local principal-unit quotient with
the quotient of global elements congruent to one at all other modulus primes. -/
theorem local_unit_quotient_equiv_ray (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (hcop : v.asIdeal ⊔ m = ⊤) (b : ℕ) :
    Nonempty (((v.adicCompletion K)ˣ ⧸ localFieldUnitFiltration K v b) ≃*
      (rayElements K m ⧸ (localFieldUnitFiltration K v b).comap
        ((Units.map (FinitePlace.embedding v).toMonoidHom).comp
          (rayElements K m).subtype))) := by
  exact localRay_quotient_equiv_ray K v m hm hcop b

include hvw in
/-- Janusz V.12.1 constructs a local Artin map by this approximation quotient. -/
theorem exists_localArtinMap [IsTotallyComplex K] [IsAbelianGalois K L]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤)
    (a : ℕ) (ha : 0 < a)
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K (v.asIdeal ^ a * m) L φ)
    (hsurj : Function.Surjective φ)
    (hU : IsUnramifiedAway K (v.asIdeal ^ a * m) L)
    (hray : raySubgroup K (v.asIdeal ^ a * m) ≤ φ.ker) :
    ∃ θ : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L),
      IsLocalArtinMap K L v w m a φ θ ∧ localFieldUnitFiltration K v a ≤ θ.ker := by
  refine ⟨localArtinMapOfRay K L v m hm hcop a ha φ hray, ⟨?_, fun x => ?_⟩,
    localArtinMapOfRay_deep_units_le_ker K L v m hm hcop a ha φ hray⟩
  · rw [localArtinMapOfRay_range]
    exact rayArtin_range_eq_stabilizer K L v w m hm hcop a ha φ hφ hsurj hU hray
  · exact DFunLike.congr_fun (localArtinMapOfRay_comp_ray K L v m hm hcop a ha φ hray) x

/-- Janusz V.12.2: local norms are killed, by approximation with global norms. -/
theorem localNormGroup_le_localArtin_ker [IsAbelianGalois K L]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤) (a : ℕ)
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K (v.asIdeal ^ a * m) L φ)
    (hU : IsUnramifiedAway K (v.asIdeal ^ a * m) L)
    (θ : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L))
    (hθ : IsLocalArtinMap K L v w m a φ θ)
    (b : ℕ) (hb : localFieldUnitFiltration K v b ≤ θ.ker) :
    localNormGroup K L v w ≤ θ.ker := by
  exact localNormGroup_le_ker_of_ray_agreement K L v w m hm hcop a φ hφ hU θ
    (MonoidHom.ext fun x => hθ.2 x) b hb

/-- Janusz V.12.5: surjectivity onto the decomposition group and the local index
bound force equality of the local Artin kernel with the local norm group. -/
theorem localArtin_ker_eq_normGroup [IsAbelianGalois K L]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤) (a : ℕ)
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K (v.asIdeal ^ a * m) L φ)
    (hU : IsUnramifiedAway K (v.asIdeal ^ a * m) L)
    (θ : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L))
    (hθ : IsLocalArtinMap K L v w m a φ θ)
    (b : ℕ) (hb : localFieldUnitFiltration K v b ≤ θ.ker) :
    θ.ker = localNormGroup K L v w := by
  haveI := localNormGroup_finiteIndex K L v w
  have hle := localNormGroup_le_localArtin_ker K L v w m hm hcop a φ hφ hU θ hθ b hb
  letI := completionAlgebra K L v w
  have hidx : (localNormGroup K L v w).index ≤
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := localNormGroup_index_le K L v w
  have hθidx : θ.ker.index = Module.finrank (v.adicCompletion K) (w.adicCompletion L) :=
    localArtin_ker_index_of_range K L v w θ hθ.1
  by_contra hne
  have hlt := Subgroup.index_strictAnti (lt_of_le_of_ne hle (Ne.symm hne))
  omega

end Extension

/-- A class field admits an admissible Artin-kernel model at a modulus `v^a * m` with
`v` prime to `m`. -/
theorem exists_refined_artinKernel_model (H : CongruenceSubgroup K) (L : Type*) [Field L]
    [Algebra K L] (hL : IsClassFieldFor K H L) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ (a : ℕ) (m : Ideal (𝓞 K)) (hN : v.asIdeal ^ a * m ≠ ⊥)
      (B : Subgroup (coprimeIdeals K (v.asIdeal ^ a * m)))
      (hB : raySubgroup K (v.asIdeal ^ a * m) ≤ B),
      0 < a ∧ m ≠ ⊥ ∧ v.asIdeal ⊔ m = ⊤ ∧ CongruenceEquivalent K H ⟨_, hN, B, hB⟩ ∧
        HasArtinKernel K (v.asIdeal ^ a * m) L B := by
  obtain ⟨J, hHJ, hJ⟩ := hL
  obtain ⟨a, m, ha, hm, hcop, hle⟩ :=
    exists_primePower_complement_refinement K v J.modulus J.modulus_ne_bot
  have hN0 : v.asIdeal ^ a * m ≠ ⊥ := mul_ne_zero (pow_ne_zero _ v.ne_bot) hm
  exact ⟨a, m, hN0, _, raySubgroup_le_restrict K J _ hle, ha, hm, hcop,
    (congruenceEquivalent_equivalence K).trans hHJ (restrictCongruence_equivalent K J _ hN0 hle),
    hasArtinKernel_restrictModulus K _ J.modulus hN0 hle L J.subgroup hJ⟩

/-- An admissible ray kernel gives the exact local norm index via its actual local Artin map. -/
theorem localNormGroup_index_eq_of_hasArtinKernel [IsTotallyComplex K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤)
    (a : ℕ) (ha : 0 < a)
    (B : Subgroup (coprimeIdeals K (v.asIdeal ^ a * m)))
    (hL : HasArtinKernel K (v.asIdeal ^ a * m) L B)
    (hray : raySubgroup K (v.asIdeal ^ a * m) ≤ B) :
    letI := completionAlgebra K L v w
    (localNormGroup K L v w).index =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  obtain ⟨hfin, hgal, hcomm, hU, φ, hφ, hsurj, hφk⟩ := hL
  haveI := hfin
  haveI := hgal
  haveI := hcomm
  haveI : IsAbelianGalois K L := ⟨⟩
  have hray' : raySubgroup K (v.asIdeal ^ a * m) ≤ φ.ker := hφk ▸ hray
  obtain ⟨θ, hθ, hθb⟩ := exists_localArtinMap K L v w m hm hcop a ha φ hφ hsurj hU hray'
  have hker := localArtin_ker_eq_normGroup K L v w m hm hcop a φ hφ hU θ hθ a hθb
  letI := completionAlgebra K L v w
  have hidx : θ.ker.index = Module.finrank (v.adicCompletion K) (w.adicCompletion L) :=
    localArtin_ker_index_of_range K L v w θ hθ.1
  rw [hker] at hidx
  exact hidx

/-- Janusz V.11.3 and V.12.6: removing `v` from the global conductor is equivalent
to the depth-zero local units being norms. -/
theorem conductor_not_le_iff_local_units_norm [IsTotallyComplex K]
    (H : CongruenceSubgroup K) (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (hL : IsClassFieldFor K H L) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    ¬idealGroupConductor K H ≤ v.asIdeal ↔
      localFieldUnitFiltration K v 0 ≤ localNormGroup K L v w := by
  obtain ⟨a, m, hN, B, hB, ha, hm, hcop, hHJ, hJ⟩ := exists_refined_artinKernel_model K H L hL v
  obtain ⟨hfin, hgal, hcomm, hU, φ, hφ, hsurj, hφk⟩ := hJ
  haveI := hfin
  haveI := hgal
  haveI := hcomm
  haveI : IsAbelianGalois K L := ⟨⟩
  have hray : raySubgroup K (v.asIdeal ^ a * m) ≤ φ.ker := hφk ▸ hB
  obtain ⟨θ, hθ, hθb⟩ := exists_localArtinMap K L v w m hm hcop a ha φ hφ hsurj hU hray
  have hcomp : θ.comp ((completionUnitMap K v).comp (rayElements K m).subtype) =
      (φ.comp (eraseModulusFactors K (v.asIdeal ^ a * m))).comp
        ((toPrincipalIdeal (𝓞 K) K).comp (rayElements K m).subtype) :=
    MonoidHom.ext fun x => hθ.2 x
  have hamb : φ.ker.map (coprimeIdeals K (v.asIdeal ^ a * m)).subtype =
      (⟨_, hN, B, hB⟩ : CongruenceSubgroup K).ambient := by
    rw [hφk]
    rfl
  rw [conductor_not_le_iff_localCharacter_units K H ⟨_, hN, B, hB⟩ hHJ v m hm hcop a ha rfl
    (L ≃ₐ[K] L) φ hamb θ hcomp a hθb,
    localArtin_ker_eq_normGroup K L v w m hm hcop a φ hφ hU θ hθ a hθb]

/-- Janusz V.12.7: the finite-prime support of the conductor is exactly the ramified
prime support. Its local norm/conductor children remain explicit prerequisites. -/
theorem ramified_iff_conductor_le [IsTotallyComplex K]
    (H : CongruenceSubgroup K) (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (hL : IsClassFieldFor K H L) (v : HeightOneSpectrum (𝓞 K)) :
    (∃ P ∈ v.asIdeal.primesOver (𝓞 L), Ideal.ramificationIdx v.asIdeal P ≠ 1) ↔
      idealGroupConductor K H ≤ v.asIdeal := by
  obtain ⟨a, m, hN, B, hB, ha, hm, hcop, hHJ, hJ⟩ := exists_refined_artinKernel_model K H L hL v
  haveI := hJ.finiteDimensional
  haveI := hJ.isGalois
  haveI := hJ.commutative
  haveI : IsAbelianGalois K L := ⟨⟩
  constructor
  · rintro ⟨P, ⟨hPp, hPo⟩, hPe⟩
    by_contra hc
    let w : HeightOneSpectrum (𝓞 L) := ⟨P, hPp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
    haveI : w.asIdeal.LiesOver v.asIdeal := hPo
    have hU0 := (conductor_not_le_iff_local_units_norm K H L hL v w).mp hc
    exact hPe (unramified_of_local_units_le_normGroup K L v w hU0
      (localNormGroup_index_eq_of_hasArtinKernel K L v w m hm hcop a ha B hJ hB))
  · intro hc
    by_contra hnr
    obtain ⟨Q, hQp, hQc⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) v.asIdeal (by simp)
    haveI : Q.LiesOver v.asIdeal := ⟨hQc.symm⟩
    let w : HeightOneSpectrum (𝓞 L) := ⟨Q, hQp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
    have he : Ideal.ramificationIdx v.asIdeal Q = 1 := by
      by_contra h
      exact hnr ⟨Q, ⟨hQp, inferInstance⟩, h⟩
    have hU0 := local_units_le_normGroup_of_unramified K L v w he
    exact (conductor_not_le_iff_local_units_norm K H L hL v w).mpr hU0 hc

/-- Janusz V.9.16 plus V.12.7 gives Cox's fixed-modulus existence formulation. -/
theorem exists_artinKernel_at_modulus [IsTotallyComplex K] (H : CongruenceSubgroup K) :
    ∃ L : IntermediateField K (AlgebraicClosure K),
      HasArtinKernel K H.modulus L H.subgroup := by
  classical
  obtain ⟨L, hL⟩ := exists_classField K H
  refine ⟨L, ?_⟩
  obtain ⟨J, hHJ, hJ⟩ := id hL
  haveI := hJ.finiteDimensional
  haveI := hJ.isGalois
  haveI := hJ.commutative
  haveI : IsAbelianGalois K L := ⟨⟩
  haveI : NumberField L := NumberField.of_module_finite K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hHc : H.modulus ≤ idealGroupConductor K H :=
    le_sSup ⟨H, (congruenceEquivalent_equivalence K).refl H, rfl⟩
  have hUH : IsUnramifiedAway K H.modulus L := by
    intro q hq hq0 hqm P hP
    by_contra he
    have hc := (ramified_iff_conductor_le K H L hL ⟨q, hq, hq0⟩).mp ⟨P, hP, he⟩
    rw [sup_eq_left.mpr (hHc.trans hc)] at hqm
    exact hq.ne_top hqm
  obtain ⟨φ, hφ, hsurj⟩ := exists_artinMap K H.modulus L H.modulus_ne_bot hUH
  obtain ⟨r, hr0, hrH, hrJ, hamb⟩ := hHJ
  obtain ⟨-, -, -, -, ψ, hψ, -, hψk⟩ := hJ
  have hUr : IsUnramifiedAway K r L := fun q hq hq0 hqr =>
    hUH q hq hq0 (eq_top_mono (sup_le_sup_left hrH q) hqr)
  have hφψ := isArtinMap_unique K r L hUr (isArtinMap_comp_inclusion K L hrH φ hφ)
    (isArtinMap_comp_inclusion K L hrJ ψ hψ)
  have hcomap := comap_inclusion_eq_of_inf_eq K H J r hrH hrJ hamb
  have hkey : ∀ y : coprimeIdeals K r,
      φ (Subgroup.inclusion (coprimeIdeals_mono K hrH) y) = 1 ↔
        Subgroup.inclusion (coprimeIdeals_mono K hrH) y ∈ H.subgroup := by
    intro y
    rw [show φ (Subgroup.inclusion (coprimeIdeals_mono K hrH) y) =
        ψ (Subgroup.inclusion (coprimeIdeals_mono K hrJ) y) from DFunLike.congr_fun hφψ y,
      ← MonoidHom.mem_ker, hψk, ← Subgroup.mem_comap, ← Subgroup.mem_comap, hcomap]
  obtain ⟨S, hS⟩ := exists_modulus_support K H.modulus H.modulus_ne_bot
  have hUS : IsUnramifiedAway K (supportModulus K S 1) L := by
    intro q hq hq0 hqS P hP
    refine hUH q hq hq0 ?_ P hP
    by_contra hqm
    have hmq : H.modulus ≤ q :=
      le_sup_right.trans ((hq.isMaximal hq0).eq_of_le hqm le_sup_left).symm.le
    have hle : supportModulus K S 1 ≤ q :=
      (supportModulus_le_prime_iff K S 1 one_pos ⟨q, hq, hq0⟩).mpr ((hS _).mpr hmq)
    rw [sup_eq_left.mpr hle] at hqS
    exact hq.ne_top hqS
  obtain ⟨t₀, ht₀⟩ := artin_reciprocity_supported K L S hUS
  obtain ⟨t₁, ht₁⟩ := exists_supportModulus_le K H.modulus H.modulus_ne_bot S
    (fun w hw => (hS w).mpr hw)
  have ht0 : 0 < max 1 (max t₀ t₁) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have htm : supportModulus K S (max 1 (max t₀ t₁)) ≤ H.modulus :=
    ht₁ _ (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨χ, hχ, -, hχray⟩ := ht₀ _ (le_trans (le_max_left _ _) (le_max_right _ _))
  have hUt : IsUnramifiedAway K (supportModulus K S (max 1 (max t₀ t₁))) L :=
    fun q hq hq0 hqm => hUH q hq hq0 (eq_top_mono (sup_le_sup_left htm q) hqm)
  have hχφ := isArtinMap_unique K _ L hUt hχ (isArtinMap_comp_inclusion K L htm φ hφ)
  obtain ⟨Sr, hSr⟩ := exists_modulus_support K r hr0
  have hray : raySubgroup K H.modulus ≤ φ.ker := by
    intro ρ hρ
    obtain ⟨α, hα, hαρ⟩ := exists_rayElement_of_mem_closure K H.modulus hρ
    have hαH := principal_mem_coprime_of_mem_rayElements K H.modulus α hα
    obtain ⟨β, hβ, hβc⟩ := exists_ray_element_with_counts K
      (supportModulus K S (max 1 (max t₀ t₁))) (supportModulus_ne_bot K S _) (S ∪ Sr)
      (fun p hp => Finset.mem_union_left _ ((supportModulus_le_prime_iff K S _ ht0 p).mp hp))
      (fun p => if p.1 ∈ S then 0 else FractionalIdeal.count K p.1
        (toPrincipalIdeal (𝓞 K) K α : FractionalIdeal (𝓞 K)⁰ K))
      (fun p hp => by
        simp only [if_pos ((supportModulus_le_prime_iff K S _ ht0 p.1).mp hp)])
    have hβH : β ∈ rayElements K H.modulus := rayElements_mono K htm hβ
    have hγ : α * β⁻¹ ∈ rayElements K H.modulus := mul_mem hα (inv_mem hβH)
    have hγr : toPrincipalIdeal (𝓞 K) K (α * β⁻¹) ∈ coprimeIdeals K r := by
      rw [mem_coprimeIdeals_iff_count_eq_zero]
      intro p hp
      have hcβ := hβc ⟨p, Finset.mem_union_right _ ((hSr p).mpr hp)⟩
      rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
        FractionalIdeal.count_mul K p (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _)),
        FractionalIdeal.count_inv, hcβ]
      by_cases hpS : p ∈ S
      · simp only [if_pos hpS, neg_zero, add_zero]
        exact (mem_coprimeIdeals_iff_count_eq_zero K H.modulus _).mp hαH p ((hS p).mp hpS)
      · simp only [if_neg hpS, add_neg_cancel]
    have hγH := principal_mem_coprime_of_mem_rayElements K H.modulus _ hγ
    have hβt := principal_mem_coprime_of_mem_rayElements K _ β hβ
    have hβH' : toPrincipalIdeal (𝓞 K) K β ∈ coprimeIdeals K H.modulus :=
      coprimeIdeals_mono K htm hβt
    have hincl1 : Subgroup.inclusion (coprimeIdeals_mono K hrH) ⟨_, hγr⟩ = ⟨_, hγH⟩ :=
      Subtype.ext (Subgroup.coe_inclusion (coprimeIdeals_mono K hrH) _)
    have hmemH : (⟨_, hγH⟩ : coprimeIdeals K H.modulus) ∈ H.subgroup := by
      apply H.contains_ray
      obtain ⟨y, hy, hyγ⟩ := principal_mem_ray_of_mem_rayElements K H.modulus _ hγ
      rw [show (⟨_, hγH⟩ : coprimeIdeals K H.modulus) = y from Subtype.ext hyγ.symm]
      exact hy
    have h1 : φ ⟨_, hγH⟩ = 1 := by
      rw [← hincl1]
      exact (hkey ⟨_, hγr⟩).mpr (by rw [hincl1]; exact hmemH)
    have h2 : φ ⟨_, hβH'⟩ = 1 := by
      obtain ⟨y, hy, hyβ⟩ := principal_mem_ray_of_mem_rayElements K _ β hβ
      have hχy : χ y = 1 := hχray hy
      rw [hχφ, MonoidHom.comp_apply] at hχy
      rw [show (⟨_, hβH'⟩ : coprimeIdeals K H.modulus) =
        Subgroup.inclusion (coprimeIdeals_mono K htm) y from
          Subtype.ext (by rw [Subgroup.coe_inclusion]; exact hyβ.symm)]
      exact hχy
    have hρeq : ρ = ⟨_, hγH⟩ * ⟨_, hβH'⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      change (ρ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        toPrincipalIdeal (𝓞 K) K (α * β⁻¹) * toPrincipalIdeal (𝓞 K) K β
      rw [← map_mul, inv_mul_cancel_right, hαρ]
      rfl
    rw [MonoidHom.mem_ker, hρeq, map_mul, h1, h2, one_mul]
  let K₀ : CongruenceSubgroup K := ⟨H.modulus, H.modulus_ne_bot, φ.ker, hray⟩
  have hK₀H : CongruenceEquivalent K K₀ H := by
    refine ⟨r, hr0, hrH, hrH, ?_⟩
    ext x
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hxr⟩
      have hk' : Subgroup.inclusion (coprimeIdeals_mono K hrH) ⟨_, hxr⟩ = k :=
        Subtype.ext (Subgroup.coe_inclusion (coprimeIdeals_mono K hrH) _)
      have h1 : φ (Subgroup.inclusion (coprimeIdeals_mono K hrH) ⟨_, hxr⟩) = 1 := by
        rw [hk']
        exact MonoidHom.mem_ker.mp hk
      have h2 := (hkey _).mp h1
      rw [hk'] at h2
      exact ⟨⟨k, h2, rfl⟩, hxr⟩
    · rintro ⟨⟨k, hk, rfl⟩, hxr⟩
      have hk' : Subgroup.inclusion (coprimeIdeals_mono K hrH) ⟨_, hxr⟩ = k :=
        Subtype.ext (Subgroup.coe_inclusion (coprimeIdeals_mono K hrH) _)
      have h1 : Subgroup.inclusion (coprimeIdeals_mono K hrH) ⟨_, hxr⟩ ∈ H.subgroup := by
        rw [hk']
        exact hk
      have h2 := (hkey _).mpr h1
      rw [hk'] at h2
      exact ⟨⟨k, MonoidHom.mem_ker.mpr h2, rfl⟩, hxr⟩
  have hamb' : K₀.ambient = H.ambient :=
    (congruenceEquivalent_ambient_restriction K K₀ H le_rfl hK₀H).trans
      (inf_eq_left.mpr H.ambient_le_coprimeIdeals)
  have hker : φ.ker = H.subgroup :=
    Subgroup.map_injective (coprimeIdeals K H.modulus).subtype_injective hamb'
  exact ⟨inferInstance, inferInstance, inferInstance, hUH, φ, hφ, hsurj, hker⟩

end Cox.ClassFieldTheory
