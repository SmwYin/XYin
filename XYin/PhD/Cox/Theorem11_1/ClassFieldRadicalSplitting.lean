/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldKummer
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalPower
import XYin.PhD.Cox.Theorem11_1.ClassFieldRayNormApproximation
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionDegree
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Local radical splitting

Janusz V.9.2 is decomposed through local nth powers, the actual adjoin, density
of global elements, and the completion degree formula. No reciprocity hypothesis is used.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace Cox.ClassFieldTheory

/-- Every root of a nonzero base nth power belongs to the base when it contains the nth roots
of unity. -/
theorem root_mem_base_of_power_eq {F E : Type*} [Field F] [Field E] [Algebra F E]
    (n : ℕ) (hn : 0 < n) (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (x : E) (y : F) (hy : y ≠ 0) (hx : x ^ n = algebraMap F E (y ^ n)) :
    x ∈ Set.range (algebraMap F E) := by
  have hy' : algebraMap F E y ≠ 0 := (map_ne_zero _).mpr hy
  have hz : (x / algebraMap F E y) ^ n = 1 := by
    rw [div_pow, ← map_pow, hx, div_self ((map_ne_zero _).mpr (pow_ne_zero n hy))]
  obtain ⟨u, hu⟩ := Kummer.rootOfUnity_mem_base F E n hn ζ hζ _ hz
  refine ⟨(u : F) * y, ?_⟩
  rw [map_mul, hu, div_mul_cancel₀ _ hy']

/-- An algebra homomorphism from an adjoin lands in any intermediate field containing its
generators. -/
theorem adjoin_image_le {K E M : Type*} [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] (S : Set E)
    (f : IntermediateField.adjoin K S →ₐ[K] M) (N : IntermediateField K M)
    (hS : ∀ x hx, f ⟨x, IntermediateField.subset_adjoin K S hx⟩ ∈ N) :
    ∀ x, f x ∈ N := by
  intro x
  have key : ∀ (y : E) (hy : y ∈ IntermediateField.adjoin K S), f ⟨y, hy⟩ ∈ N := by
    intro y hy
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy => exact hS y hy
    | algebraMap c =>
      have h : (⟨algebraMap K E c, IntermediateField.algebraMap_mem _ c⟩ :
          IntermediateField.adjoin K S) = algebraMap K (IntermediateField.adjoin K S) c := rfl
      rw [h, AlgHom.commutes]
      exact N.algebraMap_mem c
    | add y z hy hz ihy ihz =>
      have h : (⟨y + z, add_mem hy hz⟩ : IntermediateField.adjoin K S) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [h, map_add]
      exact add_mem ihy ihz
    | inv y hy ihy =>
      have h : (⟨y⁻¹, inv_mem hy⟩ : IntermediateField.adjoin K S) = (⟨y, hy⟩)⁻¹ := rfl
      rw [h, map_inv₀]
      exact inv_mem ihy
    | mul y z hy hz ihy ihz =>
      have h : (⟨y * z, mul_mem hy hz⟩ : IntermediateField.adjoin K S) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [h, map_mul]
      exact mul_mem ihy ihz
  exact key x.1 x.2

open scoped Valued in
/-- Dense global elements in the closed local base force completion degree one. -/
theorem completion_finrank_one_of_global_mem_range
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (h : ∀ x : L, FinitePlace.embedding w x ∈ Set.range (completionEmbedding K L v w)) :
    letI := completionAlgebra K L v w
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1 := by
  letI := completionAlgebra K L v w
  letI : NontriviallyNormedField (v.adicCompletion K) :=
    Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  haveI := completion_continuousSMul K L v w
  let R : Submodule (v.adicCompletion K) (w.adicCompletion L) :=
    LinearMap.range (Algebra.linearMap (v.adicCompletion K) (w.adicCompletion L))
  haveI : FiniteDimensional (v.adicCompletion K) R := LinearMap.finiteDimensional_range _
  have hclosed : IsClosed (R : Set (w.adicCompletion L)) := Submodule.closed_of_finiteDimensional R
  have hdense : Dense (R : Set (w.adicCompletion L)) := by
    refine Dense.mono ?_ (w.denseRange_algebraMap L)
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := h x
    exact ⟨y, hy⟩
  have hR : (R : Set (w.adicCompletion L)) = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  have hsurj : Function.Surjective
      (Algebra.linearMap (v.adicCompletion K) (w.adicCompletion L)) := by
    intro z
    have hz : z ∈ (R : Set (w.adicCompletion L)) := hR ▸ Set.mem_univ z
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, hy⟩
  have hbij : Function.Bijective
      (Algebra.linearMap (v.adicCompletion K) (w.adicCompletion L)) :=
    ⟨(algebraMap (v.adicCompletion K) (w.adicCompletion L)).injective, hsurj⟩
  rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq, Module.finrank_self]

/-- A support modulus is contained in each of its prime-power factors. -/
theorem supportModulus_le_primePower (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∈ S) (t : ℕ) : supportModulus K S t ≤ v.asIdeal ^ t := by
  exact Ideal.prod_le_inf.trans (Finset.inf_le (f := fun w => w.asIdeal ^ t) hv)

/-- The actual local ray kernel and deep integer-unit powers give a field-unit nth power. -/
theorem completion_ray_mem_nthPowers
    (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (n t : ℕ) (ht : 0 < t)
    (hpow : localUnitFiltration K v t ≤
      (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* _).range)
    (a : Kˣ) (ha : a ∈ rayElements K (v.asIdeal ^ t)) :
    completionUnitMap K v a ∈ (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range := by
  rw [← localRayMap_ker K v t ht, MonoidHom.mem_ker, localRayMap_apply,
    QuotientGroup.eq_one_iff] at ha
  obtain ⟨u, hu, hua⟩ := ha
  obtain ⟨r, hr⟩ := hpow hu
  refine ⟨Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom r, ?_⟩
  rw [← hua, ← hr]
  exact (map_pow _ r n).symm

/-- A radical field maps into a coherent intermediate base when every radicand is an nth power
there. -/
theorem radicalField_image_mem_base {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (W : Subgroup Kˣ)
    (f : radicalField K n W →ₐ[K] E)
    (hW : ∀ a ∈ W, ∃ b : F, algebraMap K F (a : K) = b ^ n) :
    ∀ x, f x ∈ Set.range (algebraMap F E) := by
  intro x
  let N : IntermediateField K E := (IsScalarTower.toAlgHom K F E).fieldRange
  have key := adjoin_image_le (K := K)
    {a : AlgebraicClosure K | ∃ w : Kˣ, w ∈ W ∧ a ^ n = algebraMap K (AlgebraicClosure K) (w : K)}
    f N ?_ x
  · obtain ⟨y, hy⟩ := key
    exact ⟨y, hy⟩
  · rintro a ⟨w, hwW, ha⟩
    obtain ⟨b, hb⟩ := hW w hwW
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne', map_eq_zero] at hb
      exact w.ne_zero hb
    have h1 : (⟨a, IntermediateField.subset_adjoin K _ ⟨w, hwW, ha⟩⟩ : radicalField K n W) ^ n =
        algebraMap K (radicalField K n W) (w : K) := Subtype.ext ha
    have hfa : f ⟨a, IntermediateField.subset_adjoin K _ ⟨w, hwW, ha⟩⟩ ^ n =
        algebraMap F E (b ^ n) := by
      rw [← map_pow, h1, AlgHom.commutes, ← hb, ← IsScalarTower.algebraMap_apply]
    obtain ⟨c, hc⟩ := root_mem_base_of_power_eq n hn (algebraMap K F ζ)
      (hζ.map_of_injective (algebraMap K F).injective) _ b hb0 hfa
    exact ⟨c, hc⟩

/-- Finitely many primes admit one positive ray depth above which every local image is an nth
power. -/
theorem eventually_ray_local_nthPowers (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 0 < n) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ v ∈ T, ∀ a ∈ rayElements K (supportModulus K T t),
      completionUnitMap K v a ∈ (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range := by
  classical
  choose c hc using fun v : HeightOneSpectrum (𝓞 K) => localUnitFiltration_le_nthPowers K v n hn
  refine ⟨max 1 (T.sup c), fun t ht v hv a ha => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) ht)
  have hct : c v ≤ t := le_trans (Finset.le_sup hv) (le_trans (le_max_right _ _) ht)
  exact completion_ray_mem_nthPowers K v n t ht0 (hc v t hct) a
    (rayElements_mono K (supportModulus_le_primePower K T v hv t) ha)

/-- Completion degree one at every upper prime implies complete splitting. -/
theorem splittingIdeals_of_completion_finrank_one
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (h : ∀ w : HeightOneSpectrum (𝓞 L), ∀ hw : w.asIdeal.LiesOver v.asIdeal,
      letI := hw
      letI := completionAlgebra K L v w
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1) :
    v.asIdeal ∈ splittingIdeals K L := by
  refine ⟨v.isPrime, v.ne_bot, fun P hP => ?_⟩
  obtain ⟨hPp, hlo⟩ := hP
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  let w : HeightOneSpectrum (𝓞 L) := ⟨P, hPp, hP0⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := hlo
  have h1 := h w hlo
  rw [completion_finrank_eq_ramification_mul_inertia K L v w] at h1
  exact ⟨Nat.eq_one_of_mul_eq_one_right h1, Nat.eq_one_of_mul_eq_one_left h1⟩

/-- Janusz V.9.2: local nth powers of the radicands force complete splitting in a finite radical
field. -/
theorem radicalField_splits_of_local_nthPowers
    (K : Type*) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (W : Subgroup Kˣ)
    [Finite (W ⧸ (nthPowers K n).subgroupOf W)] (v : HeightOneSpectrum (𝓞 K))
    (hW : ∀ a ∈ W, completionUnitMap K v a ∈
      (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range) :
    v.asIdeal ∈ splittingIdeals K (radicalField K n W) := by
  haveI := radicalField_finiteDimensional K n hn W
  haveI : NumberField (radicalField K n W) := NumberField.of_module_finite K (radicalField K n W)
  have hW' : ∀ a ∈ W, ∃ b : v.adicCompletion K,
      algebraMap K (v.adicCompletion K) (a : K) = b ^ n := by
    intro a ha
    obtain ⟨b, hb⟩ := hW a ha
    exact ⟨(b : v.adicCompletion K), (congrArg Units.val hb).symm⟩
  refine splittingIdeals_of_completion_finrank_one K (radicalField K n W) v fun w hw => ?_
  letI := hw
  letI := completionAlgebra K (radicalField K n W) v w
  haveI := completion_isScalarTower K (radicalField K n W) v w
  let f : radicalField K n W →ₐ[K] w.adicCompletion (radicalField K n W) :=
    { FinitePlace.embedding w with
      commutes' := fun c => rfl }
  have himg := radicalField_image_mem_base (F := v.adicCompletion K) n hn ζ hζ W f hW'
  exact completion_finrank_one_of_global_mem_range K (radicalField K n W) v w fun x => himg x

end Cox.ClassFieldTheory
