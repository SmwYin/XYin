/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldRayCountingDefs
import XYin.PhD.Cox.Theorem11_1.ChebotarevIdealSublattice
import XYin.PhD.Cox.Theorem11_1.ChebotarevNormBoundary

/-! # Janusz's ray-class lattice count

Janusz IV.2.3–2.15 counts principalized ideals using a unit fundamental region and
translated ideal lattices. We retain Mathlib's full-unit fundamental cone: the finite
image of the full units modulo the finite modulus replaces the larger fundamental
region for ray units. This is the finite-union formulation of IV.2.6–2.7, with w_K
normalized generators per ideal. It yields exactly the same leading coefficient.

No norm-residue counting theorem is substituted for a ray-class assertion. Every
congruence is a congruence of the generator itself.
-/

open NumberField MeasureTheory
open NumberField.Units NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open scoped nonZeroDivisors Pointwise
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K))

/-- The finite residue image of the full unit group, Janusz IV.2.6. -/
def rayUnitResidues : Subgroup ((𝓞 K ⧸ m)ˣ) :=
  (Units.map (Ideal.Quotient.mk m).toMonoidHom).range

/-- An integral generator can be made congruent to one by multiplying by a global unit. -/
def HasUnitResidue (α : 𝓞 K) : Prop :=
  ∃ ε : (𝓞 K)ˣ, Ideal.Quotient.mk m α = Ideal.Quotient.mk m (ε : 𝓞 K)

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- Unit-residue membership expressed in the actual finite subgroup. -/
theorem hasUnitResidue_iff (α : 𝓞 K) : HasUnitResidue K m α ↔
    ∃ t : rayUnitResidues K m, Ideal.Quotient.mk m α = (t : (𝓞 K ⧸ m)ˣ) := by
  constructor
  · rintro ⟨ε, hε⟩
    exact ⟨⟨Units.map (Ideal.Quotient.mk m).toMonoidHom ε, ε, rfl⟩, hε⟩
  · rintro ⟨⟨t, ε, rfl⟩, ht⟩
    exact ⟨ε, ht⟩

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- Changing an integral generator by a global unit preserves the allowed residues. -/
theorem hasUnitResidue_mul_unit_iff (α : 𝓞 K) (ε : (𝓞 K)ˣ) :
    HasUnitResidue K m (α * ε) ↔ HasUnitResidue K m α := by
  constructor
  · rintro ⟨δ, hδ⟩
    refine ⟨δ * ε⁻¹, ?_⟩
    rw [Units.val_mul, map_mul, ← hδ, map_mul, mul_assoc, ← map_mul, Units.mul_inv, map_one,
      mul_one]
  · rintro ⟨δ, hδ⟩
    exact ⟨δ * ε, by rw [map_mul, hδ, Units.val_mul, map_mul]⟩

/-- The residue unit image is finite for a nonzero modulus. -/
theorem finite_rayUnitResidues (hm : m ≠ ⊥) : Finite (rayUnitResidues K m) := by
  haveI : Finite (𝓞 K ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm
  infer_instance

/-- The identity residue is present even when m=top and its quotient ring is trivial. -/
theorem rayUnitResidues_card_pos (hm : m ≠ ⊥) : 0 < Nat.card (rayUnitResidues K m) := by
  haveI := finite_rayUnitResidues K m hm
  exact Nat.card_pos

/-- For an integral principal ideal, the ray condition permits a global-unit residue. -/
theorem principal_mem_ray_iff_hasUnitResidue (α : 𝓞 K) (hα : α ≠ 0)
    (u : coprimeIdeals K m)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K)) :
    u ∈ raySubgroup K m ↔ HasUnitResidue K m α := by
  have hmk : ∀ a : 𝓞 K, a - 1 ∈ m → Ideal.Quotient.mk m a = 1 := fun a ha => by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk m), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact ha
  constructor
  · intro hray
    obtain ⟨a, b, ha, hb, ham, hbm, hab⟩ := (raySubgroup_mem_iff_fraction K m u).mp hray
    rw [hu] at hab
    have hb' : FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) ≠ 0 := by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
      exact_mod_cast hb
    have h1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((α : K) * b) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) := by
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, hab, div_mul_cancel₀ _ hb']
    obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp h1
    have h2 : (z : 𝓞 K) * (α * b) = a := by
      apply RingOfIntegers.coe_injective
      change ((z : 𝓞 K) : K) * ((α : K) * (b : K)) = (a : K)
      rw [← hz, Units.smul_def, Algebra.smul_def]
    refine ⟨z⁻¹, ?_⟩
    have h3 := congrArg (Ideal.Quotient.mk m) h2
    rw [map_mul, map_mul, hmk a ham, hmk b hbm, mul_one] at h3
    calc Ideal.Quotient.mk m α
        = Ideal.Quotient.mk m ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
            (Ideal.Quotient.mk m (z : 𝓞 K) * Ideal.Quotient.mk m α) := by
          rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      _ = Ideal.Quotient.mk m ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by rw [h3, mul_one]
  · rintro ⟨ε, hε⟩
    apply (raySubgroup_mem_iff_fraction K m u).mpr
    refine ⟨α * ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K), 1, mul_ne_zero hα (Units.ne_zero _), one_ne_zero,
      ?_, by simp, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hε, ← map_mul, Units.mul_inv,
        map_one, sub_self]
    · rw [hu, show ((1 : 𝓞 K) : K) = 1 from rfl, FractionalIdeal.spanSingleton_one, div_one]
      apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
      refine ⟨ε⁻¹, ?_⟩
      rw [Units.smul_def, Algebra.smul_def, mul_comm]
      push_cast
      rfl

/-- Janusz IV.2.3: a finite ray quotient lets one clear an ideal denominator within its class. -/
theorem exists_integral_ray_class_representative (hm : m ≠ ⊥)
    (c : coprimeIdeals K m ⧸ raySubgroup K m) :
    ∃ J : (Ideal (𝓞 K))⁰, ∃ uJ : coprimeIdeals K m,
      (J : Ideal (𝓞 K)) ⊔ m = ⊤ ∧
      ((uJ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = J ∧
      QuotientGroup.mk uJ = c := by
  haveI : (raySubgroup K m).FiniteIndex := raySubgroup_finiteIndex K m hm
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨A, B, hA, hB, hAm, hBm, hu⟩ := exists_coprime_integral_fraction K m u
  obtain ⟨vA, hvA⟩ := exists_coprimeIdealUnit K m A hA hAm
  obtain ⟨vB, hvB⟩ := exists_coprimeIdealUnit K m B hB hBm
  set t := Nat.card (coprimeIdeals K m ⧸ raySubgroup K m) with ht_def
  have ht : 0 < t := Nat.card_pos
  have huAB : u = vA * vB⁻¹ := by
    apply Subtype.ext
    apply Units.ext
    rw [hu, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val, hvA,
      hvB, div_eq_mul_inv]
  have hJ0 : A * B ^ (t - 1) ≠ ⊥ := mul_ne_zero hA (pow_ne_zero _ hB)
  refine ⟨⟨A * B ^ (t - 1), mem_nonZeroDivisors_of_ne_zero hJ0⟩, vA * vB ^ (t - 1), ?_, ?_, ?_⟩
  · have h1 : IsCoprime A m := Ideal.isCoprime_iff_sup_eq.mpr hAm
    have h2 : IsCoprime B m := Ideal.isCoprime_iff_sup_eq.mpr hBm
    exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2.pow_left)
  · rw [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val, hvA, hvB]
    change _ = ((A * B ^ (t - 1) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow]
  · rw [huAB, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
      QuotientGroup.mk_inv]
    congr 1
    have hBt : (QuotientGroup.mk vB : coprimeIdeals K m ⧸ raySubgroup K m) ^ t = 1 :=
      pow_card_eq_one'
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel ht, hBt]

/-- Principalized integral ideals whose generator has the allowed residue orbit. -/
def rayPrincipalMultiples (J : (Ideal (𝓞 K))⁰) : Set (Ideal (𝓞 K)) :=
  {I | ∃ α : 𝓞 K, α ≠ 0 ∧ α ∈ (J : Ideal (𝓞 K)) ∧
    I = Ideal.span {α} ∧ HasUnitResidue K m α}

-- The unused hypotheses are kept: the planned signature includes them.
set_option linter.unusedVariables false in
/-- Janusz IV.2.4: multiply by an integral representative of the inverse RAY class. -/
theorem ray_class_principalization_count (hm : m ≠ ⊥)
    (c : coprimeIdeals K m ⧸ raySubgroup K m) (J : (Ideal (𝓞 K))⁰)
    (uJ : coprimeIdeals K m) (hJ : (J : Ideal (𝓞 K)) ⊔ m = ⊤)
    (huJ : ((uJ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = J)
    (hc : QuotientGroup.mk uJ = c⁻¹) (x : ℝ) :
    congruenceClassIdealCount K m (raySubgroup K m) c x =
      Nat.card {I : Ideal (𝓞 K) // I ∈ rayPrincipalMultiples K m J ∧
        (I.absNorm : ℝ) ≤ x * (J : Ideal (𝓞 K)).absNorm} := by
  have hJ0 : (J : Ideal (𝓞 K)) ≠ ⊥ := fun h => by
    have h' := Ideal.absNorm_pos_of_nonZeroDivisors J
    rw [h, Ideal.absNorm_bot] at h'
    exact lt_irrefl 0 h'
  have hNJ : (0 : ℝ) < ((J : Ideal (𝓞 K)).absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors J
  have hfwd : ∀ A : Ideal (𝓞 K), A ∈ integralIdealsInCongruenceClass K m (raySubgroup K m) c →
      A * J ∈ rayPrincipalMultiples K m J := by
    rintro A ⟨hA0, -, uA, huA, hcA⟩
    have hray : uA * uJ ∈ raySubgroup K m := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hcA, hc, mul_inv_cancel]
    obtain ⟨a, b, -, -, -, -, hab⟩ := (raySubgroup_mem_iff_fraction K m _).mp hray
    have hAJ : ((A * J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ ((a : K) / b) := by
      rw [FractionalIdeal.coeIdeal_mul, ← huA, ← huJ, ← Units.val_mul, ← Subgroup.coe_mul, hab,
        FractionalIdeal.spanSingleton_div_spanSingleton]
    have hmem : (a : K) / b ∈ ((A * J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [hAJ]
      exact FractionalIdeal.mem_spanSingleton_self _ _
    obtain ⟨β, hβ, hβab⟩ := (FractionalIdeal.mem_coeIdeal _).mp hmem
    have hspan : A * J = Ideal.span {β} := by
      apply FractionalIdeal.coeIdeal_injective (K := K)
      beta_reduce
      rw [hAJ, FractionalIdeal.coeIdeal_span_singleton, hβab]
    have hβ0 : β ≠ 0 := by
      intro h0
      apply mul_ne_zero hA0 hJ0
      rw [hspan, h0, Ideal.span_singleton_eq_bot.mpr rfl]
      rfl
    refine ⟨β, hβ0, Ideal.mul_le_left hβ, hspan, ?_⟩
    refine (principal_mem_ray_iff_hasUnitResidue K m β hβ0 (uA * uJ) ?_).mp hray
    rw [Subgroup.coe_mul, Units.val_mul, huA, huJ, ← FractionalIdeal.coeIdeal_mul, hspan,
      FractionalIdeal.coeIdeal_span_singleton]
  have hbwd : ∀ I : Ideal (𝓞 K), I ∈ rayPrincipalMultiples K m J →
      ∃ A : Ideal (𝓞 K), A ∈ integralIdealsInCongruenceClass K m (raySubgroup K m) c ∧
        I = A * J := by
    rintro I ⟨α, hα0, hαJ, rfl, hres⟩
    obtain ⟨A, hA⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hαJ)
    have hA0 : A ≠ ⊥ := by
      rintro rfl
      rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hA
      exact hα0 hA
    have hαm : Ideal.span {α} ⊔ m = ⊤ := by
      obtain ⟨ε, hε⟩ := hres
      have h1 : ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * α - 1 ∈ m := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hε, ← map_mul, Units.inv_mul,
          map_one, sub_self]
      rw [Ideal.eq_top_iff_one]
      have h2 : ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * α ∈ Ideal.span {α} ⊔ m :=
        Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self α))
      simpa using Ideal.sub_mem _ h2 (Ideal.mem_sup_right h1)
    have hAm : A ⊔ m = ⊤ := by
      refine eq_top_iff.mpr (hαm ▸ sup_le_sup_right ?_ m)
      rw [hA]
      exact Ideal.mul_le_left
    obtain ⟨uA, huA⟩ := exists_coprimeIdealUnit K m A hA0 hAm
    refine ⟨A, ⟨hA0, hAm, uA, huA, ?_⟩, by rw [hA, mul_comm]⟩
    have hray : uA * uJ ∈ raySubgroup K m := by
      refine (principal_mem_ray_iff_hasUnitResidue K m α hα0 (uA * uJ) ?_).mpr hres
      rw [Subgroup.coe_mul, Units.val_mul, huA, huJ, ← FractionalIdeal.coeIdeal_mul, mul_comm,
        ← hA, FractionalIdeal.coeIdeal_span_singleton]
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hc] at hray
    exact mul_inv_eq_one.mp hray
  unfold congruenceClassIdealCount
  let F : {A : Ideal (𝓞 K) //
      A ∈ integralIdealsInCongruenceClass K m (raySubgroup K m) c ∧ (A.absNorm : ℝ) ≤ x} →
      {I : Ideal (𝓞 K) // I ∈ rayPrincipalMultiples K m J ∧
        (I.absNorm : ℝ) ≤ x * (J : Ideal (𝓞 K)).absNorm} :=
    fun A => ⟨A.1 * J, hfwd A.1 A.2.1, by
      rw [map_mul, Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right A.2.2 hNJ.le⟩
  refine Nat.card_congr (Equiv.ofBijective F ⟨fun A B h => ?_, fun I => ?_⟩)
  · exact Subtype.ext (mul_right_cancel₀ hJ0 (congrArg Subtype.val h))
  · obtain ⟨A, hA, hIA⟩ := hbwd I.1 I.2.1
    refine ⟨⟨A, hA, ?_⟩, Subtype.ext hIA.symm⟩
    have h := I.2.2
    rw [hIA, map_mul, Nat.cast_mul] at h
    exact le_of_mul_le_mul_right h hNJ

/-- The lattice points in one generator residue class inside the full-unit cone. -/
def rayCell (J : (Ideal (𝓞 K))⁰) (t : 𝓞 K ⧸ m) (x : ℝ) : Set (𝓞 K) :=
  {α | α ∈ (J : Ideal (𝓞 K)) ∧ Ideal.Quotient.mk m α = t ∧
    mixedEmbedding K (α : K) ∈ fundamentalCone K ∧
    mixedEmbedding.norm (mixedEmbedding K (α : K)) ≤
      x * (J : Ideal (𝓞 K)).absNorm}

/-- The union of the allowed finite generator-residue cells. -/
def rayNormalizedGenerators (J : (Ideal (𝓞 K))⁰) (x : ℝ) : Set (𝓞 K) :=
  {α | α ∈ (J : Ideal (𝓞 K)) ∧ HasUnitResidue K m α ∧
    mixedEmbedding K (α : K) ∈ fundamentalCone K ∧
    mixedEmbedding.norm (mixedEmbedding K (α : K)) ≤
      x * (J : Ideal (𝓞 K)).absNorm}

/-- Lattice points of an integral ideal in a bounded part of the fundamental cone. -/
theorem finite_cone_ideal_points (J : (Ideal (𝓞 K))⁰) (B : ℝ) :
    {α : 𝓞 K | α ∈ (J : Ideal (𝓞 K)) ∧ mixedEmbedding K (α : K) ∈ fundamentalCone K ∧
      mixedEmbedding.norm (mixedEmbedding K (α : K)) ≤ B}.Finite := by
  rw [← Set.finite_coe_iff]
  haveI := Chebotarev.finite_idealSet_norm_le J B
  refine Finite.of_injective
    (β := {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ B})
    (fun α => ⟨⟨mixedEmbedding K ((α : 𝓞 K) : K),
      mem_idealSet.mpr ⟨α.2.2.1, α, α.2.1, rfl⟩⟩, α.2.2.2⟩) ?_
  intro a b h
  have h' := congrArg (fun z : {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ B} =>
    ((z : idealSet K J) : mixedSpace K)) h
  exact Subtype.ext (RingOfIntegers.coe_injective (mixedEmbedding_injective K h'))

/-- The fundamental cone contains no zero element. -/
theorem rayNormalizedGenerators_ne_zero (J : (Ideal (𝓞 K))⁰) (x : ℝ)
    {α : 𝓞 K} (hα : α ∈ rayNormalizedGenerators K m J x) : α ≠ 0 := by
  rintro rfl
  have h := NumberField.mixedEmbedding.fundamentalCone.norm_pos_of_mem hα.2.2.1
  simp at h

/-- Bounded lattice regions contain finitely many normalized generators. -/
theorem finite_rayNormalizedGenerators (J : (Ideal (𝓞 K))⁰) (x : ℝ) :
    (rayNormalizedGenerators K m J x).Finite := by
  exact (finite_cone_ideal_points K J (x * (J : Ideal (𝓞 K)).absNorm)).subset
    fun α hα => ⟨hα.1, hα.2.2.1, hα.2.2.2⟩

/-- Each residue cell is a bounded lattice intersection. -/
theorem finite_rayCell (J : (Ideal (𝓞 K))⁰) (t : 𝓞 K ⧸ m) (x : ℝ) :
    (rayCell K m J t x).Finite := by
  exact (finite_cone_ideal_points K J (x * (J : Ideal (𝓞 K)).absNorm)).subset
    fun α hα => ⟨hα.1, hα.2.2.1, hα.2.2.2⟩

/-- Janusz IV.2.7 in the full-unit normalization: each ideal has w_K generators. -/
theorem ray_normalized_generator_count (J : (Ideal (𝓞 K))⁰) (x : ℝ) :
    Nat.card {I : Ideal (𝓞 K) // I ∈ rayPrincipalMultiples K m J ∧
      (I.absNorm : ℝ) ≤ x * (J : Ideal (𝓞 K)).absNorm} * torsionOrder K =
        Nat.card (rayNormalizedGenerators K m J x) := by
  classical
  set B : ℝ := x * (J : Ideal (𝓞 K)).absNorm with hB
  let Q : {I : (Ideal (𝓞 K))⁰ // Submodule.IsPrincipal (I : Ideal (𝓞 K))} → Prop := fun I =>
    (J : Ideal (𝓞 K)) ∣ I.1 ∧
      (∃ β : 𝓞 K, (I.1 : Ideal (𝓞 K)) = Ideal.span {β} ∧ HasUnitResidue K m β) ∧
      ((I.1 : Ideal (𝓞 K)).absNorm : ℝ) ≤ B
  let P : integerSet K → Prop := fun a =>
    (preimageOfMemIntegerSet a : 𝓞 K) ∈ (J : Ideal (𝓞 K)) ∧
      HasUnitResidue K m (preimageOfMemIntegerSet a : 𝓞 K) ∧
      mixedEmbedding.norm (a : mixedSpace K) ≤ B
  have e1 : rayNormalizedGenerators K m J x ≃ {a : integerSet K // P a} :=
    { toFun := fun α => ⟨⟨mixedEmbedding K ((α : 𝓞 K) : K),
          mem_integerSet.mpr ⟨α.2.2.2.1, α, rfl⟩⟩, by
        simp only [P, preimageOfMemIntegerSet_mixedEmbedding]
        exact ⟨α.2.1, α.2.2.1, α.2.2.2.2⟩⟩
      invFun := fun a => ⟨preimageOfMemIntegerSet a.1, a.2.1, a.2.2.1, by
          rw [mixedEmbedding_preimageOfMemIntegerSet]
          exact a.1.2.1, by
          rw [mixedEmbedding_preimageOfMemIntegerSet]
          exact a.2.2.2⟩
      left_inv := fun α => Subtype.ext (preimageOfMemIntegerSet_mixedEmbedding _)
      right_inv := fun a =>
        Subtype.ext (Subtype.ext (mixedEmbedding_preimageOfMemIntegerSet a.1)) }
  have hPQ : ∀ a : integerSet K, P a ↔ Q (integerSetEquiv K a).1 := by
    intro a
    simp only [P, Q, integerSetEquiv_apply_fst, Ideal.dvd_span_singleton]
    refine and_congr Iff.rfl (and_congr ?_ ?_)
    · constructor
      · exact fun h => ⟨_, rfl, h⟩
      · rintro ⟨β, hβ, hres⟩
        obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hβ
        rw [← hu] at hres
        exact (hasUnitResidue_mul_unit_iff K m _ u).mp hres
    · rw [Ideal.absNorm_span_singleton, ← intNorm, intNorm_coe]
  have e2 := ((integerSetEquiv K).subtypeEquiv hPQ).trans
    (Equiv.prodSubtypeFstEquivSubtypeProd (p := Q))
  have e4 : {I : {I : (Ideal (𝓞 K))⁰ // Submodule.IsPrincipal (I : Ideal (𝓞 K))} // Q I} ≃
      {I : Ideal (𝓞 K) // I ∈ rayPrincipalMultiples K m J ∧ (I.absNorm : ℝ) ≤ B} :=
    { toFun := fun I => ⟨I.1.1.1, by
        obtain ⟨hdvd, ⟨β, hβ, hres⟩, hN⟩ := I.2
        refine ⟨⟨β, ?_, ?_, hβ, hres⟩, hN⟩
        · rintro rfl
          apply nonZeroDivisors.coe_ne_zero I.1.1
          rw [hβ, Ideal.span_singleton_eq_bot.mpr rfl]
          rfl
        · rw [hβ] at hdvd
          exact Ideal.dvd_span_singleton.mp hdvd⟩
      invFun := fun I => ⟨⟨⟨I.1, by
          obtain ⟨⟨α, hα0, -, hα, -⟩, -⟩ := I.2
          refine mem_nonZeroDivisors_of_ne_zero ?_
          rw [hα]
          exact (Ideal.span_singleton_eq_bot.not).mpr hα0⟩, by
          obtain ⟨⟨α, -, -, hα, -⟩, -⟩ := I.2
          exact ⟨⟨α, hα⟩⟩⟩, by
          obtain ⟨⟨α, -, hαJ, hα, hres⟩, hN⟩ := I.2
          refine ⟨?_, ⟨α, hα, hres⟩, hN⟩
          change (J : Ideal (𝓞 K)) ∣ I.1
          rw [hα]
          exact Ideal.dvd_span_singleton.mpr hαJ⟩
      left_inv := fun I => rfl
      right_inv := fun I => rfl }
  rw [Nat.card_congr e1, Nat.card_congr e2, Nat.card_prod, Nat.card_congr e4, torsionOrder,
    ← Nat.card_eq_fintype_card]

/-- Generator residues partition the normalized point set. -/
theorem ray_normalized_count_eq_sum (hm : m ≠ ⊥) (J : (Ideal (𝓞 K))⁰) (x : ℝ) :
    letI := finite_rayUnitResidues K m hm
    letI := Fintype.ofFinite (rayUnitResidues K m)
    Nat.card (rayNormalizedGenerators K m J x) =
      ∑ t : rayUnitResidues K m, Nat.card (rayCell K m J (t : (𝓞 K ⧸ m)ˣ) x) := by
  letI := finite_rayUnitResidues K m hm
  letI := Fintype.ofFinite (rayUnitResidues K m)
  classical
  haveI := (finite_rayNormalizedGenerators K m J x).to_subtype
  have hres : ∀ α : rayNormalizedGenerators K m J x, ∃ t : rayUnitResidues K m,
      Ideal.Quotient.mk m (α : 𝓞 K) = ((t : (𝓞 K ⧸ m)ˣ) : 𝓞 K ⧸ m) :=
    fun α => (hasUnitResidue_iff K m α).mp α.2.2.1
  choose f hf using hres
  have hfib : ∀ t : rayUnitResidues K m,
      {α : rayNormalizedGenerators K m J x // f α = t} ≃
        rayCell K m J (t : (𝓞 K ⧸ m)ˣ) x := fun t =>
    { toFun := fun α => ⟨α.1.1, α.1.2.1, by rw [hf α.1, α.2], α.1.2.2.2.1, α.1.2.2.2.2⟩
      invFun := fun β => ⟨⟨β.1, β.2.1, (hasUnitResidue_iff K m β.1).mpr ⟨t, β.2.2.1⟩,
        β.2.2.2.1, β.2.2.2.2⟩, by
          apply Subtype.ext
          apply Units.ext
          rw [← hf, β.2.2.1]⟩
      left_inv := fun α => rfl
      right_inv := fun β => rfl }
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  exact Finset.sum_congr rfl fun t _ => Nat.card_congr (hfib t)

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- Janusz IV.2.5: each residue is achieved inside an ideal prime to the modulus. -/
theorem exists_ideal_residue (J : (Ideal (𝓞 K))⁰)
    (hJ : (J : Ideal (𝓞 K)) ⊔ m = ⊤) (t : 𝓞 K ⧸ m) :
    ∃ α : 𝓞 K, α ∈ (J : Ideal (𝓞 K)) ∧ Ideal.Quotient.mk m α = t := by
  obtain ⟨β, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨j, hj, b, hb, hjb⟩ := Submodule.mem_sup.mp
    (hJ.symm ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ (J : Ideal (𝓞 K)) ⊔ m)
  refine ⟨β * j, Ideal.mul_mem_left _ β hj, ?_⟩
  have hj1 : Ideal.Quotient.mk m j = 1 := by
    rw [← map_one (Ideal.Quotient.mk m), ← hjb, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero]
  rw [map_mul, hj1, mul_one]

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- Janusz IV.2.5: the simultaneous ideal/residue condition is one coset of mJ. -/
theorem ideal_residue_iff_sub_mem_mul (J : (Ideal (𝓞 K))⁰)
    (hJ : (J : Ideal (𝓞 K)) ⊔ m = ⊤) (α₀ : 𝓞 K) (hα₀ : α₀ ∈ (J : Ideal (𝓞 K)))
    (α : 𝓞 K) :
    (α ∈ (J : Ideal (𝓞 K)) ∧ Ideal.Quotient.mk m α = Ideal.Quotient.mk m α₀) ↔
      α - α₀ ∈ m * (J : Ideal (𝓞 K)) := by
  have hcop : IsCoprime m (J : Ideal (𝓞 K)) := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
    exact hJ
  rw [Ideal.mul_eq_inf_of_isCoprime hcop, Ideal.mem_inf, Ideal.Quotient.eq]
  constructor
  · rintro ⟨hα, hm⟩
    exact ⟨hm, Ideal.sub_mem _ hα hα₀⟩
  · rintro ⟨hm, hJ'⟩
    refine ⟨?_, hm⟩
    simpa using Ideal.add_mem _ hJ' hα₀

open Classical in
/-- The standard real/complex coordinate chart preserves the canonical volume. -/
theorem measurePreserving_mixedStdChart :
    MeasurePreserving (mixedEmbedding.stdBasis K).equivFunL := by
  refine ⟨(mixedEmbedding.stdBasis K).equivFunL.continuous.measurable, ?_⟩
  have hvol : (mixedEmbedding.stdBasis K).addHaar = (volume : Measure (mixedSpace K)) := by
    rw [Module.Basis.addHaar_eq_iff, Module.Basis.coe_parallelepiped,
      ← measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped (mixedEmbedding.stdBasis K)
        volume), mixedEmbedding.volume_fundamentalDomain_stdBasis K]
  have hmap : (mixedEmbedding.stdBasis K).map
      (mixedEmbedding.stdBasis K).equivFunL.toLinearEquiv = Pi.basisFun ℝ (index K) := by
    refine Module.Basis.eq_of_apply_eq fun i => ?_
    rw [Module.Basis.map_apply, Pi.basisFun_apply]
    ext j
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [← hvol, Module.Basis.map_addHaar, hmap, ← addHaarMeasure_eq_volume_pi,
    ← Module.Basis.parallelepiped_basisFun, ← Module.Basis.addHaar_def]

open Classical in
/-- The standard chart is volume preserving in the inverse direction. -/
theorem measurePreserving_mixedStdChart_symm :
    MeasurePreserving (mixedEmbedding.stdBasis K).equivFunL.symm := by
  have h : MeasurePreserving
      (mixedEmbedding.stdBasis K).equivFunL.toHomeomorph.toMeasurableEquiv :=
    measurePreserving_mixedStdChart K
  exact h.symm

open Classical in
/-- An ideal lattice has covolume the determinant of any chart change of basis onto it. -/
theorem covolume_idealLattice_eq_abs_det (I : (Ideal (𝓞 K))⁰)
    (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) =
      ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
        (FractionalIdeal.mk0 K I)) : Set (index K → ℝ))) :
    ZLattice.covolume (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K I)) =
      |LinearMap.det (T : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| := by
  rw [← Chebotarev.covolume_image_basisFun_eq_abs_det T,
    ← ZLattice.covolume_comap (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K I))
      volume volume (measurePreserving_mixedStdChart_symm K)]
  congr 1
  rw [Chebotarev.chart_lattice_eq_map I T hT]
  ext x
  simp only [ZLattice.comap, Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨_, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

open Classical in
/-- An integral ideal lattice has covolume N(J) times that of the integer lattice. -/
theorem covolume_ideal_eq_absNorm_mul (J : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) =
      ((J : Ideal (𝓞 K)).absNorm : ℝ) *
        ZLattice.covolume (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K 1)) := by
  obtain ⟨T, hT⟩ := Chebotarev.exists_latticeEquiv_image_idealLattice (1 : (Ideal (𝓞 K))⁰)
  obtain ⟨T', hT'⟩ := Chebotarev.exists_latticeEquiv_image_idealLattice J
  have hT'' : ⇑T' '' ↑(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (index K)))) =
      ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
        (FractionalIdeal.mk0 K (J * 1))) : Set (index K → ℝ)) := by
    rwa [mul_one]
  rw [covolume_idealLattice_eq_abs_det K J T' hT', covolume_idealLattice_eq_abs_det K 1 T hT,
    Chebotarev.abs_det_latticeEquiv_mul 1 J T T' hT hT'']

open Classical in
/-- The common leading coefficient for a single residue cell. -/
def rayCellConstant : ℝ :=
  volume.real (normLeOne K) /
    ((m.absNorm : ℝ) * ZLattice.covolume
      (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K 1)))

open Classical in
/-- The geometric coefficient is positive for every nonzero modulus. -/
theorem volumeReal_normLeOne_pos : 0 < volume.real (normLeOne K) := by
  rw [Measure.real, NumberField.mixedEmbedding.fundamentalCone.volume_normLeOne]
  have hreg := NumberField.Units.regulator_pos K
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hreg.le,
    ENNReal.toReal_ofNat, ENNReal.coe_toReal, NNReal.coe_real_pi]
  positivity

/-- Divide the positive region volume by the positive modulus norm and lattice covolume. -/
theorem rayCellConstant_pos (hm : m ≠ ⊥) : 0 < rayCellConstant K m := by
  classical
  unfold rayCellConstant
  have h1 := volumeReal_normLeOne_pos K
  have h2 : (0 : ℝ) < m.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero fun h => hm (Ideal.absNorm_eq_zero_iff.mp h)
  have h3 :=
    ZLattice.covolume_pos (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K 1)) volume
  positivity

open Classical in
/-- Multiplying an integral ideal lattice by m multiplies its covolume by N(m). -/
theorem covolume_modulus_ideal (hm : m ≠ ⊥) (J : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume (mixedEmbedding.idealLattice K
      (FractionalIdeal.mk0 K
        (⟨m, by simpa only [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot] using hm⟩ * J))) =
      (m.absNorm : ℝ) * ((J : Ideal (𝓞 K)).absNorm : ℝ) *
        ZLattice.covolume (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K 1)) := by
  rw [covolume_ideal_eq_absNorm_mul, Submonoid.coe_mul, map_mul, Nat.cast_mul]

open Classical in
/-- The norm bound is the radial scale t=(x N(J))^(1/d), so the ideal norm cancels. -/
theorem ray_scale_leading_term (hm : m ≠ ⊥) (J : (Ideal (𝓞 K))⁰) {x : ℝ} (hx : 1 ≤ x) :
    let t := (x * ((J : Ideal (𝓞 K)).absNorm : ℝ)) ^ (1 / (Module.finrank ℚ K : ℝ))
    volume.real (normLeOne K) /
      ((m.absNorm : ℝ) * ((J : Ideal (𝓞 K)).absNorm : ℝ) *
        ZLattice.covolume (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K 1))) *
      t ^ Module.finrank ℚ K = rayCellConstant K m * x := by
  classical
  intro t
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hNJ : (0 : ℝ) < ((J : Ideal (𝓞 K)).absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors J
  have hx0 : 0 < x := by linarith
  have ht : t ^ Module.finrank ℚ K = x * (J : Ideal (𝓞 K)).absNorm := by
    change ((x * ((J : Ideal (𝓞 K)).absNorm : ℝ)) ^ (1 / (Module.finrank ℚ K : ℝ))) ^
      Module.finrank ℚ K = _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div_mul_cancel hd.ne',
      Real.rpow_one]
  have hm' : (0 : ℝ) < m.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero fun h => hm (Ideal.absNorm_eq_zero_iff.mp h)
  have hcov :=
    ZLattice.covolume_pos (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K 1)) volume
  rw [ht, rayCellConstant]
  field_simp

/-- Janusz IV.2.5/2.8: identify a generator cell with a translated lattice in a dilated region. -/
theorem rayCell_equiv_lattice_coset (hm : m ≠ ⊥) (J : (Ideal (𝓞 K))⁰)
    (hJ : (J : Ideal (𝓞 K)) ⊔ m = ⊤) (t : 𝓞 K ⧸ m)
    (α₀ : 𝓞 K) (hα₀ : α₀ ∈ (J : Ideal (𝓞 K))) (ht : Ideal.Quotient.mk m α₀ = t)
    {x : ℝ} (hx : 1 ≤ x) :
    let B : (Ideal (𝓞 K))⁰ :=
      ⟨m, by simpa only [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot] using hm⟩ * J
    let r := (x * ((J : Ideal (𝓞 K)).absNorm : ℝ)) ^ (1 / (Module.finrank ℚ K : ℝ))
    Nonempty ((rayCell K m J t x) ≃
      ↥((mixedEmbedding K (α₀ : K) +ᵥ
          (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K B) : Set (mixedSpace K))) ∩
        r • normLeOne K)) := by
  intro B r
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hNJ : (1 : ℝ) ≤ ((J : Ideal (𝓞 K)).absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors J
  have hxN : 1 ≤ x * ((J : Ideal (𝓞 K)).absNorm : ℝ) := one_le_mul_of_one_le_of_one_le hx hNJ
  have hr1 : 1 ≤ r := Real.one_le_rpow hxN (by positivity)
  have hrd : r ^ Module.finrank ℚ K = x * (J : Ideal (𝓞 K)).absNorm := by
    change ((x * ((J : Ideal (𝓞 K)).absNorm : ℝ)) ^ (1 / (Module.finrank ℚ K : ℝ))) ^
      Module.finrank ℚ K = _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div_mul_cancel hd.ne',
      Real.rpow_one]
  rw [← Chebotarev.cone_normLe_eq_smul_normLeOne hr1, hrd]
  have hmemL : ∀ β : 𝓞 K, mixedEmbedding K (β : K) ∈
      (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K B) : Set (mixedSpace K)) ↔
        β ∈ m * (J : Ideal (𝓞 K)) := by
    intro β
    rw [SetLike.mem_coe, mixedEmbedding.mem_idealLattice]
    constructor
    · rintro ⟨y, hy, hyβ⟩
      rw [FractionalIdeal.coe_mk0] at hy
      obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
      have hzβ : z = β := RingOfIntegers.coe_injective (mixedEmbedding_injective K hyβ)
      rw [← hzβ]
      exact hz
    · intro hβ
      refine ⟨(β : K), ?_, rfl⟩
      rw [FractionalIdeal.coe_mk0]
      exact FractionalIdeal.mem_coeIdeal_of_mem _ hβ
  let f : 𝓞 K → mixedSpace K := fun α => mixedEmbedding K (α : K)
  have hinj : Function.Injective f :=
    (mixedEmbedding_injective K).comp RingOfIntegers.coe_injective
  refine ⟨Set.BijOn.equiv f ⟨?_, hinj.injOn, ?_⟩⟩
  · rintro α ⟨hαJ, hαt, hcone, hnorm⟩
    refine ⟨?_, hcone, hnorm⟩
    have hsub : α - α₀ ∈ m * (J : Ideal (𝓞 K)) :=
      (ideal_residue_iff_sub_mem_mul K m J hJ α₀ hα₀ α).mp ⟨hαJ, hαt.trans ht.symm⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
    have h1 : f α - mixedEmbedding K (α₀ : K) = mixedEmbedding K ((α - α₀ : 𝓞 K) : K) := by
      simp only [f]
      push_cast
      rw [map_sub]
    rw [h1]
    exact (hmemL _).mpr hsub
  · rintro y ⟨hyv, hcone, hnorm⟩
    obtain ⟨z, hz, rfl⟩ := Set.mem_vadd_set.mp hyv
    rw [SetLike.mem_coe, mixedEmbedding.mem_idealLattice] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [FractionalIdeal.coe_mk0] at hw
    obtain ⟨β, hβ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hw
    have hfy : f (α₀ + β) = mixedEmbedding K (α₀ : K) +ᵥ
        mixedEmbedding K (algebraMap (𝓞 K) K β) := by
      simp only [f, vadd_eq_add]
      push_cast
      rw [map_add]
    refine ⟨α₀ + β, ?_, hfy⟩
    have hiff := (ideal_residue_iff_sub_mem_mul K m J hJ α₀ hα₀ (α₀ + β)).mpr
      (by simpa using hβ)
    refine ⟨hiff.1, hiff.2.trans ht, ?_, ?_⟩
    · change f (α₀ + β) ∈ fundamentalCone K
      rw [hfy]
      exact hcone
    · change mixedEmbedding.norm (f (α₀ + β)) ≤ _
      rw [hfy]
      exact hnorm

/-- Janusz IV.2.8/2.15: count a translated ideal lattice in the bounded fundamental region. -/
theorem exists_ray_cell_error (hm : m ≠ ⊥) (J : (Ideal (𝓞 K))⁰)
    (hJ : (J : Ideal (𝓞 K)) ⊔ m = ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : 𝓞 K ⧸ m) (x : ℝ), 1 ≤ x →
      |(Nat.card (rayCell K m J t x) : ℝ) - rayCellConstant K m * x| ≤
        C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  classical
  set d := Module.finrank ℚ K with hd_def
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hd : (0 : ℝ) < d := by exact_mod_cast hd1
  let Φ := (mixedEmbedding.stdBasis K).equivFunL
  let B : (Ideal (𝓞 K))⁰ :=
    ⟨m, by simpa only [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot] using hm⟩ * J
  obtain ⟨T, hT⟩ := Chebotarev.exists_latticeEquiv_image_idealLattice B
  let D : Set (index K → ℝ) := Φ '' normLeOne K
  have hbdd : Bornology.IsBounded D := Φ.lipschitz.isBounded_image (isBounded_normLeOne K)
  have hmeas : MeasurableSet D := by
    change MeasurableSet (Φ '' normLeOne K)
    rw [ContinuousLinearEquiv.image_eq_preimage_symm]
    exact (measurableSet_normLeOne K).preimage Φ.symm.continuous.measurable
  obtain ⟨C, hC⟩ := Chebotarev.exists_card_coset_inter_smul_sub_volume_mul_rpow_le T D hbdd
    hmeas (Chebotarev.normLeOne_frontier_lipschitz_cover_index K)
  have hcard : Fintype.card (index K) = d := by
    rw [← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K), mixedEmbedding.finrank]
  have hvolD : volume.real D = volume.real (normLeOne K) := by
    change volume.real (Φ '' normLeOne K) = _
    rw [Measure.real, Measure.real, ContinuousLinearEquiv.image_eq_preimage_symm,
      (measurePreserving_mixedStdChart_symm K).measure_preimage
        (measurableSet_normLeOne K).nullMeasurableSet]
  have hdetT : |LinearMap.det (T : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| =
      (m.absNorm : ℝ) * ((J : Ideal (𝓞 K)).absNorm : ℝ) *
        ZLattice.covolume (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K 1)) := by
    rw [← covolume_idealLattice_eq_abs_det K B T hT, covolume_modulus_ideal K m hm J]
  have hNJ : (1 : ℝ) ≤ ((J : Ideal (𝓞 K)).absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors J
  have hC0 : 0 ≤ C := by
    have h := hC 0 1 le_rfl
    simp only [one_pow, mul_one] at h
    exact le_trans (abs_nonneg _) h
  set E : ℝ := ((J : Ideal (𝓞 K)).absNorm : ℝ) ^ (1 - 1 / (d : ℝ)) with hE
  have hE0 : 0 ≤ E := Real.rpow_nonneg (by linarith) _
  refine ⟨C * E + 1, add_pos_of_nonneg_of_pos (mul_nonneg hC0 hE0) one_pos, fun t x hx => ?_⟩
  obtain ⟨α₀, hα₀, ht⟩ := exists_ideal_residue K m J hJ t
  obtain ⟨e⟩ := rayCell_equiv_lattice_coset K m hm J hJ t α₀ hα₀ ht hx
  set r : ℝ := (x * ((J : Ideal (𝓞 K)).absNorm : ℝ)) ^ (1 / (d : ℝ)) with hr
  have hxN : 1 ≤ x * ((J : Ideal (𝓞 K)).absNorm : ℝ) := one_le_mul_of_one_le_of_one_le hx hNJ
  have hr1 : 1 ≤ r := Real.one_le_rpow hxN (by positivity)
  have hset : Φ '' ((mixedEmbedding K (α₀ : K) +ᵥ (mixedEmbedding.idealLattice K
      (FractionalIdeal.mk0 K B) : Set (mixedSpace K))) ∩ r • normLeOne K) =
      (Φ (mixedEmbedding K (α₀ : K)) +ᵥ (T '' (Submodule.span ℤ
        (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) ∩ r • D := by
    rw [Set.image_inter Φ.injective, Set.image_vadd_distrib, hT, image_smul_set]
  have hcount : Nat.card (rayCell K m J t x) = Nat.card ↑((Φ (mixedEmbedding K (α₀ : K)) +ᵥ
      (T '' (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (index K))) :
        Set (index K → ℝ)))) ∩ r • D) := by
    rw [Nat.card_congr e, ← hset, Nat.card_image_of_injective Φ.injective]
  have key := hC (Φ (mixedEmbedding K (α₀ : K))) r hr1
  rw [← hcount, hcard, hvolD, hdetT] at key
  have hlead : volume.real (normLeOne K) / ((m.absNorm : ℝ) *
      ((J : Ideal (𝓞 K)).absNorm : ℝ) *
        ZLattice.covolume (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K 1))) * r ^ d =
      rayCellConstant K m * x := ray_scale_leading_term K m hm J hx
  rw [hlead] at key
  have hrpow : r ^ (d - 1) = E * x ^ (1 - 1 / (d : ℝ)) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    have he : 1 / (d : ℝ) * ((d - 1 : ℕ) : ℝ) = 1 - 1 / (d : ℝ) := by
      rw [Nat.cast_sub hd1, Nat.cast_one]
      field_simp
    rw [he, hE, mul_comm]
  rw [hrpow] at key
  have hxe : 0 ≤ x ^ (1 - 1 / (d : ℝ)) := Real.rpow_nonneg (by linarith) _
  calc _ ≤ C * (E * x ^ (1 - 1 / (d : ℝ))) := key
    _ ≤ (C * E + 1) * x ^ (1 - 1 / (d : ℝ)) := by nlinarith

/-- Janusz IV.2.12/2.13: sum allowed residues and divide by full-unit torsion. -/
def rayClassConstant : ℝ :=
  (Nat.card (rayUnitResidues K m) : ℝ) * rayCellConstant K m / torsionOrder K

/-- This form of the regulator/torsion ratio is positive, including unit rank zero. -/
theorem rayClassConstant_pos (hm : m ≠ ⊥) : 0 < rayClassConstant K m := by
  unfold rayClassConstant
  have h1 : (0 : ℝ) < Nat.card (rayUnitResidues K m) := by
    exact_mod_cast rayUnitResidues_card_pos K m hm
  have h2 := rayCellConstant_pos K m hm
  have h3 : (0 : ℝ) < torsionOrder K := by exact_mod_cast NumberField.Units.torsionOrder_pos K
  positivity

/-- Sum the finite residue-cell errors and divide by the number of normalized generators. -/
theorem exists_ray_principal_count_error (hm : m ≠ ⊥) (J : (Ideal (𝓞 K))⁰)
    (hJ : (J : Ideal (𝓞 K)) ⊔ m = ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |(Nat.card {I : Ideal (𝓞 K) // I ∈ rayPrincipalMultiples K m J ∧
          (I.absNorm : ℝ) ≤ x * (J : Ideal (𝓞 K)).absNorm} : ℝ) -
          rayClassConstant K m * x| ≤ C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  classical
  letI := finite_rayUnitResidues K m hm
  letI := Fintype.ofFinite (rayUnitResidues K m)
  obtain ⟨C, hC0, hC⟩ := exists_ray_cell_error K m hm J hJ
  have hw : (0 : ℝ) < torsionOrder K := by exact_mod_cast NumberField.Units.torsionOrder_pos K
  have hNT : (0 : ℝ) < (Nat.card (rayUnitResidues K m) : ℝ) := by
    exact_mod_cast rayUnitResidues_card_pos K m hm
  refine ⟨(Nat.card (rayUnitResidues K m) : ℝ) * C / torsionOrder K,
    div_pos (mul_pos hNT hC0) hw, fun x hx => ?_⟩
  have hcount := ray_normalized_generator_count K m J x
  have hsum := ray_normalized_count_eq_sum K m hm J x
  have h1 : (Nat.card {I : Ideal (𝓞 K) // I ∈ rayPrincipalMultiples K m J ∧
      (I.absNorm : ℝ) ≤ x * (J : Ideal (𝓞 K)).absNorm} : ℝ) =
      (∑ t : rayUnitResidues K m,
        (Nat.card (rayCell K m J (t : (𝓞 K ⧸ m)ˣ) x) : ℝ)) / torsionOrder K := by
    rw [eq_div_iff hw.ne']
    exact_mod_cast hcount.trans hsum
  have h2 : rayClassConstant K m * x =
      (∑ _t : rayUnitResidues K m, rayCellConstant K m * x) / torsionOrder K := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, rayClassConstant,
      Fintype.card_eq_nat_card]
    ring
  rw [h1, h2, ← sub_div, abs_div, abs_of_pos hw, ← Finset.sum_sub_distrib, div_le_iff₀ hw]
  have hxe : 0 ≤ x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := Real.rpow_nonneg (by linarith) _
  calc |∑ t : rayUnitResidues K m, ((Nat.card (rayCell K m J (t : (𝓞 K ⧸ m)ˣ) x) : ℝ) -
        rayCellConstant K m * x)|
      ≤ ∑ t : rayUnitResidues K m, |(Nat.card (rayCell K m J (t : (𝓞 K ⧸ m)ˣ) x) : ℝ) -
        rayCellConstant K m * x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : rayUnitResidues K m, C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) :=
        Finset.sum_le_sum fun t _ => hC _ x hx
    _ = (Nat.card (rayUnitResidues K m) : ℝ) * C / torsionOrder K *
        x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) * torsionOrder K := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_eq_nat_card]
      field_simp

/-- The leading coefficient is independent of the ray class; finitely many error constants unify. -/
theorem exists_rayClassIdealCount_error (hm : m ≠ ⊥) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : coprimeIdeals K m ⧸ raySubgroup K m) (x : ℝ), 1 ≤ x →
      |(congruenceClassIdealCount K m (raySubgroup K m) c x : ℝ) -
        rayClassConstant K m * x| ≤ C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  classical
  haveI : (raySubgroup K m).FiniteIndex := raySubgroup_finiteIndex K m hm
  letI := Fintype.ofFinite (coprimeIdeals K m ⧸ raySubgroup K m)
  have hrep : ∀ c : coprimeIdeals K m ⧸ raySubgroup K m, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |(congruenceClassIdealCount K m (raySubgroup K m) c x : ℝ) -
        rayClassConstant K m * x| ≤ C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
    intro c
    obtain ⟨J, uJ, hJ, huJ, hcJ⟩ := exists_integral_ray_class_representative K m hm c⁻¹
    obtain ⟨C, hC0, hC⟩ := exists_ray_principal_count_error K m hm J hJ
    refine ⟨C, hC0, fun x hx => ?_⟩
    rw [ray_class_principalization_count K m hm c J uJ hJ huJ hcJ x]
    exact hC x hx
  choose Cc hCc0 hCc using hrep
  refine ⟨∑ c, Cc c, Finset.sum_pos (fun c _ => hCc0 c) Finset.univ_nonempty,
    fun c x hx => (hCc c x hx).trans ?_⟩
  have hxe : 0 ≤ x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := Real.rpow_nonneg (by linarith) _
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun c' _ => (hCc0 c').le) (Finset.mem_univ c)) hxe

/-- Passing from ray classes to classes of a larger congruence subgroup. -/
def congruenceProjection (H : Subgroup (coprimeIdeals K m)) (hH : raySubgroup K m ≤ H) :
    (coprimeIdeals K m ⧸ raySubgroup K m) →* (coprimeIdeals K m ⧸ H) :=
  QuotientGroup.map _ _ (MonoidHom.id _) hH

/-- The quotient projection sends the class of an ideal to its class modulo H. -/
theorem congruenceProjection_mk (H : Subgroup (coprimeIdeals K m))
    (hH : raySubgroup K m ≤ H) (u : coprimeIdeals K m) :
    congruenceProjection K m H hH (QuotientGroup.mk u) = QuotientGroup.mk u := by
  rfl

/-- All congruence classes are images of ray classes. -/
theorem congruenceProjection_surjective (H : Subgroup (coprimeIdeals K m))
    (hH : raySubgroup K m ≤ H) : Function.Surjective (congruenceProjection K m H hH) := by
  intro c
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨QuotientGroup.mk u, rfl⟩

/-- Surjective homomorphisms of finite groups have nonempty fibers of one common size. -/
theorem congruenceProjection_uniform_fibers (hm : m ≠ ⊥)
    (H : Subgroup (coprimeIdeals K m)) (hH : raySubgroup K m ≤ H) :
    ∃ h : ℕ, 0 < h ∧ ∀ c : coprimeIdeals K m ⧸ H,
      Nat.card {r : coprimeIdeals K m ⧸ raySubgroup K m //
        congruenceProjection K m H hH r = c} = h := by
  haveI : (raySubgroup K m).FiniteIndex := raySubgroup_finiteIndex K m hm
  let f := congruenceProjection K m H hH
  refine ⟨Nat.card f.ker, Nat.card_pos, fun c => ?_⟩
  obtain ⟨r, rfl⟩ := congruenceProjection_surjective K m H hH c
  exact Nat.card_congr (f.fiberEquivKer r)

/-- Each ideal has a unique ray class, so a congruence-class count sums its ray fibers. -/
theorem congruenceClassIdealCount_eq_sum_ray (hm : m ≠ ⊥)
    (H : Subgroup (coprimeIdeals K m)) (hH : raySubgroup K m ≤ H)
    (c : coprimeIdeals K m ⧸ H) (x : ℝ) :
    letI : (raySubgroup K m).FiniteIndex := raySubgroup_finiteIndex K m hm
    letI := Fintype.ofFinite {r : coprimeIdeals K m ⧸ raySubgroup K m //
      congruenceProjection K m H hH r = c}
    congruenceClassIdealCount K m H c x =
      ∑ r : {r : coprimeIdeals K m ⧸ raySubgroup K m //
        congruenceProjection K m H hH r = c},
          congruenceClassIdealCount K m (raySubgroup K m) r.val x := by
  letI : (raySubgroup K m).FiniteIndex := raySubgroup_finiteIndex K m hm
  letI := Fintype.ofFinite {r : coprimeIdeals K m ⧸ raySubgroup K m //
    congruenceProjection K m H hH r = c}
  classical
  have huniq : ∀ (A : Ideal (𝓞 K)) (u u' : coprimeIdeals K m),
      ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = A →
      ((u' : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = A → u = u' :=
    fun A u u' hu hu' => Subtype.ext (Units.ext (hu.trans hu'.symm))
  let S := {A : Ideal (𝓞 K) //
    A ∈ integralIdealsInCongruenceClass K m H c ∧ (A.absNorm : ℝ) ≤ x}
  have hrep : ∀ A : S, ∃ u : coprimeIdeals K m,
      ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = A.1 ∧
        QuotientGroup.mk u = c :=
    fun A => A.2.1.2.2
  choose ρ hρ using hrep
  let g : S → {r : coprimeIdeals K m ⧸ raySubgroup K m //
      congruenceProjection K m H hH r = c} :=
    fun A => ⟨QuotientGroup.mk (ρ A), by rw [congruenceProjection_mk]; exact (hρ A).2⟩
  haveI := (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) ⌊x⌋₊).to_subtype
  haveI : Finite S := Finite.of_injective
    (β := {I : Ideal (𝓞 K) | I.absNorm ≤ ⌊x⌋₊}) (fun A => ⟨A.1, Nat.le_floor A.2.2⟩)
    (fun A B h => Subtype.ext
      (congrArg (fun z : {I : Ideal (𝓞 K) | I.absNorm ≤ ⌊x⌋₊} => (z : Ideal (𝓞 K))) h))
  have hfib : ∀ r, {A : S // g A = r} ≃ {A : Ideal (𝓞 K) //
      A ∈ integralIdealsInCongruenceClass K m (raySubgroup K m) r.val ∧
        (A.absNorm : ℝ) ≤ x} := fun r =>
    { toFun := fun A => ⟨A.1.1, ⟨A.1.2.1.1, A.1.2.1.2.1, ρ A.1, (hρ A.1).1,
        congrArg Subtype.val A.2⟩, A.1.2.2⟩
      invFun := fun B => ⟨⟨B.1, ⟨B.2.1.1, B.2.1.2.1, by
          obtain ⟨u, hu, hur⟩ := B.2.1.2.2
          refine ⟨u, hu, ?_⟩
          rw [← congruenceProjection_mk K m H hH u, hur]
          exact r.2⟩, B.2.2⟩, by
        obtain ⟨u, hu, hur⟩ := B.2.1.2.2
        apply Subtype.ext
        change QuotientGroup.mk (ρ _) = r.val
        exact (congrArg QuotientGroup.mk (huniq B.1 _ u (hρ _).1 hu)).trans hur⟩
      left_inv := fun A => rfl
      right_inv := fun B => rfl }
  change Nat.card S = _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma]
  exact Finset.sum_congr rfl fun r _ => Nat.card_congr (hfib r)

end Cox.ClassFieldTheory
