/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormalBasis
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicRayDiagram
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormApproximation
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormLocalApproximation
import XYin.PhD.Cox.Theorem11_1.ClassFieldGlobalLocalUnits
import XYin.PhD.Cox.Theorem11_1.ClassFieldGlobalNormIndexAssembly
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalAnalytic
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalUnitCohomology
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalUnitInvariants
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnitFiltration
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalCyclicNorm
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormInequality
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnits
import XYin.PhD.Cox.Theorem11_1.ClassFieldSupportedModulus
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormModulus

/-!
# Janusz's cyclic fundamental equality

The Herbrand quotient uses Janusz's convention H¹/H⁰_Tate. The Tate groups in `ClassFieldCohomology`
are the actual kernel/image quotients of the norm and difference operators. Their
comparison with the existing positive-degree cyclic cohomology API is explicit;
ordinary H⁰ is not substituted for the Tate denominator.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise WithZero

noncomputable section



namespace Cox.ClassFieldTheory

open Cox.CyclicCohomology

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

variable [hGalois : IsGalois K L]
include hGalois

namespace LocalCyclic

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] localAlgebra localFinite

end LocalCyclic

/-- Janusz V.3.3–3.9: deep congruence at one finite prime gives its local degree. -/
theorem elementNormRay_index_primePower [IsCyclic (L ≃ₐ[K] L)]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀,
      (elementNormGroup K L ⊔ rayElements K (v.asIdeal ^ t)).index =
        v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) := by
  haveI := v.isPrime
  obtain ⟨P, hPp, hPlo, hP0⟩ := Chebotarev.exists_prime_liesOver K L v.asIdeal v.ne_bot
  let w : HeightOneSpectrum (𝓞 L) := ⟨P, hPp, hP0⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := hPlo
  haveI : w.asIdeal.IsPrime := hPp
  haveI := LocalCyclic.completion_isGalois K L v w
  haveI := LocalCyclic.completion_aut_isCyclic K L v w
  obtain ⟨c, hc⟩ := LocalCyclic.deep_units_le_unitNormGroup K L v w
  refine ⟨max 1 c, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) ht)
  have hct : c ≤ t := le_trans (le_max_right _ _) ht
  rw [LocalCyclic.global_primePower_index K L v w t ht0, sup_eq_left.mpr (hc t hct),
    LocalCyclic.unit_norm_index K L v w,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal (L ≃ₐ[K] L), mul_comm]

/-- Janusz V.3.10: all primes in a fixed support can be made deep at once. -/
theorem elementNormRay_index_supported [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀,
      (elementNormGroup K L ⊔ rayElements K (supportModulus K S t)).index =
        localDegreeProduct K L (supportModulus K S t) := by
  classical
  choose c hc using fun v : HeightOneSpectrum (𝓞 K) => elementNormRay_index_primePower K L v
  refine ⟨max 1 (S.sup c), fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) ht)
  rw [elementNormRay_index_support_product K L S t, localDegreeProduct_supportModulus K L S t ht0]
  exact Finset.prod_congr rfl fun v hv =>
    hc v t (le_trans (Finset.le_sup hv) (le_trans (le_max_right _ _) ht))

/-- Janusz V.4.3 with the prescribed support retained: the first inequality forces
n(m)=1 after the local-degree products cancel. -/
theorem cyclic_norm_index_supported [IsTotallyComplex K] [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hU : IsUnramifiedAway K (supportModulus K S 1) L) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀,
      (normRaySubgroup K (supportModulus K S t) L).index = Module.finrank K L := by
  obtain ⟨c, hc⟩ := elementNormRay_index_supported K L S
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  refine ⟨max 1 c, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have htc : c ≤ t := le_trans (le_max_right _ _) ht
  have hm : supportModulus K S t ≠ ⊥ := supportModulus_ne_bot K S t
  have hUm : IsUnramifiedAway K (supportModulus K S t) L := fun q hq hq0 hqm =>
    hU q hq hq0 (eq_top_mono (sup_le_sup_left (supportModulus_antitone K S ht1) q) hqm)
  have hfund := fundamental_index_factorization K L (supportModulus K S t) hm hUm σ hσ
  rw [hc t htc, sUnit_herbrandQuotient K L (supportModulus K S t) hm σ hσ] at hfund
  have hd : (0 : ℚ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have hn : (1 : ℚ) ≤ normCorrectionIndex K L (supportModulus K S t) := by
    exact_mod_cast normCorrectionIndex_pos K L (supportModulus K S t) hm hUm σ hσ
  have hle : ((normRaySubgroup K (supportModulus K S t) L).index : ℚ) ≤ Module.finrank K L := by
    exact_mod_cast normRaySubgroup_index_le K (supportModulus K S t) L hm
  have hge : (Module.finrank K L : ℚ) ≤ (normRaySubgroup K (supportModulus K S t) L).index :=
    calc (Module.finrank K L : ℚ) = Module.finrank K L * 1 := (mul_one _).symm
      _ ≤ Module.finrank K L * normCorrectionIndex K L (supportModulus K S t) :=
        mul_le_mul_of_nonneg_left hn hd.le
      _ = _ := hfund.symm
  exact_mod_cast le_antisymm hle hge

end Cox.ClassFieldTheory
