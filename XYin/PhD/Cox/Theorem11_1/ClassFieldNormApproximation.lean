/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicModules
import XYin.PhD.Cox.Theorem11_1.ClassFieldApproximation
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormCongruence

/-! # Approximation for global norm congruences

Janusz V.3.1, printed pp.148–149. The proof uses simultaneous upstairs
approximation and the actual norm map, then identifies the quotient kernel.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
section Approximation
variable (K : Type*) [Field K] [hNK : NumberField K]
include hNK

/-- Janusz V.3.1: prescribe two multiplicative ray classes at coprime moduli. -/
theorem exists_ray_pair_approx (m n : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hn : n ≠ ⊥)
    (hcop : m ⊔ n = ⊤) (α β : Kˣ) :
    ∃ γ : Kˣ, γ * α⁻¹ ∈ rayElements K m ∧ γ * β⁻¹ ∈ rayElements K n := by
  have hmem : β * α⁻¹ ∈ rayElements K m ⊔ rayElements K n := by
    rw [rayElements_sup_of_coprime K m n hm hn hcop]
    exact Subgroup.mem_top _
  obtain ⟨r, hr, s, hs, hrs⟩ := Subgroup.mem_sup.mp hmem
  refine ⟨s⁻¹ * β, ?_, ?_⟩
  · rw [mul_assoc, ← hrs, mul_comm r s, inv_mul_cancel_left]
    exact hr
  · rw [mul_inv_cancel_right]
    exact inv_mem hs

variable (L : Type*) [Field L] [hNL : NumberField L] [Algebra K L]
include hNL

/-- The norm of an integral one-congruence is an integral one-congruence. -/
theorem norm_integralRayGenerator_mem (m : Ideal (𝓞 K)) (u : Lˣ) (α : 𝓞 L)
    (hα : (α : L) = u) (hcong : α - 1 ∈ m.map (algebraMap (𝓞 K) (𝓞 L))) :
    Units.map (Algebra.norm K : L →* K) u ∈ rayElements K m := by
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  apply Subgroup.subset_closure
  refine ⟨Algebra.intNorm (𝓞 K) (𝓞 L) α, ?_, intNorm_sub_one_mem K L m α hcong⟩
  change algebraMap (𝓞 K) K (Algebra.intNorm (𝓞 K) (𝓞 L) α) = Algebra.norm K (u : L)
  rw [Algebra.algebraMap_intNorm (L := L), ← hα]

/-- Janusz V.3.1: the norm carries an extended finite ray into the base ray. -/
theorem norm_rayElements_le (m : Ideal (𝓞 K)) :
    rayElements L (m.map (algebraMap (𝓞 K) (𝓞 L))) ≤
      (rayElements K m).comap (Units.map (Algebra.norm K : L →* K)) := by
  rw [rayElements, Subgroup.closure_le]
  rintro u ⟨α, hα, hcong⟩
  exact norm_integralRayGenerator_mem K L m u α hα hcong

/-- Approximate both upstairs elements before taking their norms. -/
theorem exists_norm_pair_approx (m n : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hn : n ≠ ⊥)
    (hcop : m ⊔ n = ⊤) (β₁ β₂ : Lˣ) :
    ∃ β : Lˣ,
      Units.map (Algebra.norm K : L →* K) (β * β₁⁻¹) ∈ rayElements K m ∧
      Units.map (Algebra.norm K : L →* K) (β * β₂⁻¹) ∈ rayElements K n := by
  have hm' : m.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hm
  have hn' : n.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hn
  have hcop' : m.map (algebraMap (𝓞 K) (𝓞 L)) ⊔ n.map (algebraMap (𝓞 K) (𝓞 L)) = ⊤ := by
    rw [← Ideal.map_sup, hcop, Ideal.map_top]
  obtain ⟨β, h1, h2⟩ := exists_ray_pair_approx L _ _ hm' hn' hcop' β₁ β₂
  exact ⟨β, norm_rayElements_le K L m h1, norm_rayElements_le K L n h2⟩

omit hNK hNL in
/-- Membership in the norm/ray product has an actual upstairs norm witness. -/
theorem mem_elementNormRay_iff (m : Ideal (𝓞 K)) (α : Kˣ) :
    α ∈ elementNormGroup K L ⊔ rayElements K m ↔
      ∃ β : Lˣ, α * (Units.map (Algebra.norm K : L →* K) β)⁻¹ ∈ rayElements K m := by
  rw [Subgroup.mem_sup]
  constructor
  · rintro ⟨y, ⟨β, rfl⟩, z, hz, rfl⟩
    refine ⟨β, ?_⟩
    rwa [mul_comm, inv_mul_cancel_left]
  · rintro ⟨β, hβ⟩
    exact ⟨Units.map (Algebra.norm K : L →* K) β, ⟨β, rfl⟩, _, hβ,
      by rw [mul_comm α, mul_inv_cancel_left]⟩

/-- The kernel computation in Janusz V.3.1 uses one common norm witness. -/
theorem exists_common_norm_ray (m n : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hn : n ≠ ⊥)
    (hcop : m ⊔ n = ⊤) (α : Kˣ)
    (hαm : α ∈ elementNormGroup K L ⊔ rayElements K m)
    (hαn : α ∈ elementNormGroup K L ⊔ rayElements K n) :
    ∃ β : Lˣ,
      α * (Units.map (Algebra.norm K : L →* K) β)⁻¹ ∈ rayElements K (m * n) := by
  obtain ⟨β₁, h1⟩ := (mem_elementNormRay_iff K L m α).mp hαm
  obtain ⟨β₂, h2⟩ := (mem_elementNormRay_iff K L n α).mp hαn
  obtain ⟨β, hβ1, hβ2⟩ := exists_norm_pair_approx K L m n hm hn hcop β₁ β₂
  refine ⟨β, ?_⟩
  have key : ∀ γ : Lˣ, α * (Units.map (Algebra.norm K : L →* K) β)⁻¹ =
      α * (Units.map (Algebra.norm K : L →* K) γ)⁻¹ *
        (Units.map (Algebra.norm K : L →* K) (β * γ⁻¹))⁻¹ := by
    intro γ
    rw [map_mul, map_inv]
    group
  have hmn : m * n = m ⊓ n :=
    Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr hcop)
  rw [hmn, rayElements_inf K m n hm hn]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [key β₁]
    exact mul_mem h1 (inv_mem hβ1)
  · rw [key β₂]
    exact mul_mem h2 (inv_mem hβ2)

/-- The norm/ray kernel is the intersection of the two coprime-modulus kernels. -/
theorem elementNormRay_inf (m n : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hn : n ≠ ⊥)
    (hcop : m ⊔ n = ⊤) :
    (elementNormGroup K L ⊔ rayElements K m) ⊓
        (elementNormGroup K L ⊔ rayElements K n) =
      elementNormGroup K L ⊔ rayElements K (m * n) := by
  apply le_antisymm
  · intro α hα
    obtain ⟨hαm, hαn⟩ := Subgroup.mem_inf.mp hα
    obtain ⟨β, hβ⟩ := exists_common_norm_ray K L m n hm hn hcop α hαm hαn
    exact (mem_elementNormRay_iff K L (m * n) α).mpr ⟨β, hβ⟩
  · have hmn : m * n = m ⊓ n :=
      Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr hcop)
    rw [hmn, rayElements_inf K m n hm hn]
    exact le_inf (sup_le_sup_left inf_le_left _) (sup_le_sup_left inf_le_right _)

/-- Janusz V.3.1: the norm/ray quotient is the product of the two component quotients. -/
theorem elementNormRay_quotient_CRT (m n : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hn : n ≠ ⊥)
    (hcop : m ⊔ n = ⊤) :
    Nonempty ((Kˣ ⧸ (elementNormGroup K L ⊔ rayElements K (m * n))) ≃*
      (Kˣ ⧸ (elementNormGroup K L ⊔ rayElements K m)) ×
        (Kˣ ⧸ (elementNormGroup K L ⊔ rayElements K n))) := by
  have htop : (elementNormGroup K L ⊔ rayElements K m) ⊔
      (elementNormGroup K L ⊔ rayElements K n) = ⊤ := by
    rw [eq_top_iff, ← rayElements_sup_of_coprime K m n hm hn hcop]
    exact sup_le_sup le_sup_right le_sup_right
  obtain ⟨e⟩ := quotient_inf_equiv_prod Kˣ _ _ htop
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (elementNormRay_inf K L m n hm hn hcop).symm).trans e⟩

end Approximation

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- Janusz V.3.1: approximation separates element-norm congruences at coprime moduli. -/
theorem elementNormRay_index_mul (m n : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hn : n ≠ ⊥)
    (hcop : m ⊔ n = ⊤) :
    (elementNormGroup K L ⊔ rayElements K (m * n)).index =
      (elementNormGroup K L ⊔ rayElements K m).index *
      (elementNormGroup K L ⊔ rayElements K n).index := by
  obtain ⟨e⟩ := elementNormRay_quotient_CRT K L m n hm hn hcop
  rw [Subgroup.index, Subgroup.index, Subgroup.index, Nat.card_congr e.toEquiv, Nat.card_prod]

end Cox.ClassFieldTheory
