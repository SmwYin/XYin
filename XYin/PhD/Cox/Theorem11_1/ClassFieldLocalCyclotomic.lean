/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicSquare
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalSplitDescent
import XYin.PhD.Cox.Theorem11_1.ClassFieldExistence

/-! # Supports and depths for the cyclotomic square in Janusz V.11.2

The source uses `Z′ = Z(μ_q)` and `E′ = E(μ_q)`. These lemmas supply the independent
finite-prime data: the primes above a given prime, the support of a modulus, disjoint
complementary supports, and uniform depths of support moduli refining given ideals.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K E : Type*) [Field K] [hNF_K : NumberField K] [Field E] [hNF_E : NumberField E]
  [Algebra K E]
variable (q : ℕ) [hq_nonzero : NeZero q]

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
include hNF_K hNF_E in
/-- There are only finitely many primes above the chosen finite prime. -/
theorem exists_primesAbove_support (v : HeightOneSpectrum (𝓞 K)) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 E)),
      ∀ w : HeightOneSpectrum (𝓞 E), w ∈ S ↔ w.asIdeal.LiesOver v.asIdeal := by
  classical
  have hfin := Ideal.finite_factors
    (Ideal.map_ne_bot_of_ne_bot (S := 𝓞 E) v.ne_bot : v.asIdeal.map (algebraMap (𝓞 K) (𝓞 E)) ≠ ⊥)
  refine ⟨hfin.toFinset.filter (fun w => w.asIdeal.LiesOver v.asIdeal), fun w => ?_⟩
  rw [Finset.mem_filter, hfin.mem_toFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
    exact h.over.le

include hNF_K in
/-- A nonzero ideal is divisible by only finitely many height-one primes. -/
theorem exists_modulus_support (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ v,
      v ∈ S ↔ m ≤ v.asIdeal := by
  classical
  have hfin := Ideal.finite_factors hm
  exact ⟨hfin.toFinset, fun v => by rw [hfin.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le]⟩

include hNF_K in
/-- A sufficiently high uniform power of every support prime is divisible by the modulus. -/
theorem exists_supportModulus_depth (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal → v ∈ S) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, supportModulus K S t ≤ m := by
  exact exists_supportModulus_le K m hm S hS

open scoped Classical in
include hNF_K in
/-- The opposite support can include all required class, exponent and modulus primes
while remaining disjoint from the selected primes. -/
theorem exists_paired_complement (n : ℕ) (hn : 0 < n)
    (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (hcop : ∀ v ∈ S₁, v.asIdeal ⊔ m = ⊤) :
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 K)), Disjoint S₁ S₂ ∧
      SupportsClassRepresentatives K (S₁ ∪ S₂) ∧ CoversNthPrimes K n (S₁ ∪ S₂) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal → v ∈ S₂) ∧
      ∃ t₀ : ℕ, ∀ t ≥ t₀, supportModulus K S₂ t ≤ m := by
  obtain ⟨S₀, hreps, hcover⟩ := exists_suitable_support K n hn
  obtain ⟨Sm, hSm⟩ := exists_modulus_support K m hm
  have hsub : S₀ ⊆ S₁ ∪ (S₀ ∪ Sm) \ S₁ := by
    intro v hv
    by_cases h : v ∈ S₁
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hv, h⟩)
  have hmS : ∀ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal → v ∈ (S₀ ∪ Sm) \ S₁ := by
    intro v hv
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ ((hSm v).mpr hv), fun h1 => ?_⟩
    have h := hcop v h1
    rw [sup_eq_left.mpr hv] at h
    exact v.isPrime.ne_top h
  refine ⟨(S₀ ∪ Sm) \ S₁, Finset.disjoint_sdiff, fun c => ?_, fun v hv => hsub (hcover v hv),
    hmS, exists_supportModulus_le K m hm _ hmS⟩
  obtain ⟨u, hu, huc⟩ := hreps c
  refine ⟨u, Subgroup.closure_mono ?_ hu, huc⟩
  rintro x ⟨v, hv, hx⟩
  exact ⟨v, hsub hv, hx⟩

include hNF_K hNF_E in
/-- Source n|m₁m₂ and m|m₂: sufficiently deep support moduli refine both original ideals. -/
theorem exists_paired_moduli_depth (v : HeightOneSpectrum (𝓞 K))
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (a : ℕ)
    (S₁ S₂ : Finset (HeightOneSpectrum (𝓞 E)))
    (hS₁ : ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal → w ∈ S₁)
    (hS₂ : ∀ w : HeightOneSpectrum (𝓞 E),
      m.map (algebraMap (𝓞 K) (𝓞 E)) ≤ w.asIdeal → w ∈ S₂) :
    ∃ t₀ : ℕ, ∀ s ≥ t₀, ∀ t ≥ t₀,
      supportModulus E S₂ t ≤ m.map (algebraMap (𝓞 K) (𝓞 E)) ∧
      supportModulus E S₁ s * supportModulus E S₂ t ≤
        (v.asIdeal ^ a * m).map (algebraMap (𝓞 K) (𝓞 E)) := by
  have hm' : m.map (algebraMap (𝓞 K) (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hm
  have hv' : (v.asIdeal.map (algebraMap (𝓞 K) (𝓞 E))) ^ a ≠ ⊥ :=
    pow_ne_zero _ (Ideal.map_ne_bot_of_ne_bot v.ne_bot)
  have hS₁' : ∀ w : HeightOneSpectrum (𝓞 E),
      (v.asIdeal.map (algebraMap (𝓞 K) (𝓞 E))) ^ a ≤ w.asIdeal → w ∈ S₁ := by
    intro w hw
    apply hS₁
    have hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 E)) :=
      Ideal.map_le_iff_le_comap.mp (w.isPrime.le_of_pow_le hw)
    exact ⟨(v.isPrime.isMaximal v.ne_bot).eq_of_le (w.isPrime.comap _).ne_top hle⟩
  obtain ⟨t₁, ht₁⟩ := exists_supportModulus_le E _ hv' S₁ hS₁'
  obtain ⟨t₂, ht₂⟩ := exists_supportModulus_le E _ hm' S₂ hS₂
  refine ⟨max t₁ t₂, fun s hs t ht => ⟨ht₂ t (le_trans (le_max_right _ _) ht), ?_⟩⟩
  rw [Ideal.map_mul, Ideal.map_pow]
  exact Ideal.mul_mono (ht₁ s (le_trans (le_max_left _ _) hs))
    (ht₂ t (le_trans (le_max_right _ _) ht))

end Cox.ClassFieldTheory
