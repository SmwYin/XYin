/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldRayElements
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Localization.Integer

/-! # Finite-place approximation and fractional congruence

These are the approximation steps used in Janusz V.3.1–3.4, V.6.1–6.2 and V.(9.12)–(9.13). No
reciprocity, existence, or local Galois theory is assumed.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors WithZero
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Distinct finite primes have coprime powers, including exponent zero. -/
theorem prime_powers_pairwise_coprime (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : S → ℕ) : Pairwise (fun v w : S ↦ IsCoprime (v.1.asIdeal ^ e v)
      (w.1.asIdeal ^ e w)) := by
  intro v w hvw
  have hne : v.1.asIdeal ≠ w.1.asIdeal := fun h =>
    hvw (Subtype.ext (HeightOneSpectrum.ext h))
  haveI := v.1.isMaximal
  haveI := w.1.isMaximal
  exact (Ideal.isCoprime_of_isMaximal hne).pow

/-- Integral CRT with an independently chosen precision at each finite prime. -/
theorem exists_integer_prime_approx (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : S → 𝓞 K) (e : S → ℕ) :
    ∃ x : 𝓞 K, ∀ v : S, x - a v ∈ v.1.asIdeal ^ e v := by
  exact Ideal.exists_forall_sub_mem_ideal (prime_powers_pairwise_coprime K S e) a

/-- Clearing the denominators of a finite family preserves a nonzero denominator. -/
theorem exists_common_integral_denominator (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : S → K) : ∃ d : 𝓞 K, d ≠ 0 ∧ ∃ b : S → 𝓞 K,
      ∀ v : S, (b v : K) = (d : K) * a v := by
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 K)⁰ a
  have hint' : ∀ v, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = (d : 𝓞 K) • a v := fun v => hint v
  choose b hb using hint'
  refine ⟨d, nonZeroDivisors.ne_zero hd, b, fun v => ?_⟩
  change algebraMap (𝓞 K) K (b v) = _
  rw [hb v, Algebra.smul_def]

/-- A deep enough integral congruence survives division by a fixed nonzero denominator. -/
theorem exists_precision_after_division (v : HeightOneSpectrum (𝓞 K))
    (d : 𝓞 K) (hd : d ≠ 0) (N : ℤ) :
    ∃ e : ℕ, ∀ x : 𝓞 K, x ∈ v.asIdeal ^ e →
      v.valuation K ((x : K) / d) < WithZero.exp (-N) := by
  have hd' : (d : K) ≠ 0 := by exact_mod_cast hd
  have hvd : v.valuation K (d : K) ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact hd'
  obtain ⟨e, he⟩ := WithZero.exists_exp_neg_natCast_lt
    (mul_ne_zero (WithZero.exp_ne_zero (a := -N)) hvd)
  refine ⟨e, fun x hx => ?_⟩
  have hx' : v.valuation K (x : K) ≤ WithZero.exp (-(e : ℤ)) := by
    have h1 : v.valuation K (x : K) = v.intValuation x := v.valuation_of_algebraMap (K := K) x
    rw [h1]
    exact (v.intValuation_le_pow_iff_mem x e).mpr hx
  rw [map_div₀, div_lt_iff₀ (zero_lt_iff.mpr hvd)]
  exact lt_of_le_of_lt hx' he

/-- Janusz approximation: prescribe finitely many finite-place neighborhoods in K. -/
theorem exists_global_valuation_approx (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : S → K) (N : S → ℤ) :
    ∃ x : K, ∀ v : S, v.1.valuation K (x - a v) < WithZero.exp (-N v) := by
  obtain ⟨d, hd, b, hb⟩ := exists_common_integral_denominator K S a
  choose e he using fun v : S => exists_precision_after_division K v.1 d hd (N v)
  obtain ⟨c, hc⟩ := exists_integer_prime_approx K S b e
  have hd' : (d : K) ≠ 0 := by exact_mod_cast hd
  refine ⟨(c : K) / d, fun v => ?_⟩
  have h1 : (c : K) / d - a v = ((c - b v : 𝓞 K) : K) / d := by
    have hbv : (b v : K) = (d : K) * a v := hb v
    have hsub : ((c - b v : 𝓞 K) : K) = (c : K) - (b v : K) := by push_cast; ring
    rw [hsub, hbv]
    field_simp
  rw [h1]
  exact he v _ (hc v)

/-- Normalized valuation balls in the completion are actual neighborhoods. -/
theorem completion_small_ball_mem_nhds (v : HeightOneSpectrum (𝓞 K))
    (a : v.adicCompletion K) (N : ℤ) :
    {x : v.adicCompletion K | Valued.v (x - a) < WithZero.exp (-N)} ∈ nhds a := by
  obtain ⟨c, hc⟩ := v.valuedAdicCompletion_surjective K (WithZero.exp (-N))
  have heq : {x : v.adicCompletion K | Valued.v x < WithZero.exp (-N)} =
      {x | Valued.v.restrict x < Valued.v.restrict c} := by
    ext x
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff, hc]
  have hopen : IsOpen {x : v.adicCompletion K | Valued.v x < WithZero.exp (-N)} := by
    rw [heq]
    exact Valued.isOpen_ball _ _
  have hopen' : IsOpen {x : v.adicCompletion K | Valued.v (x - a) < WithZero.exp (-N)} :=
    hopen.preimage (continuous_id.sub continuous_const)
  apply hopen'.mem_nhds
  simp only [Set.mem_setOf_eq, sub_self, map_zero]
  exact zero_lt_iff.mpr WithZero.exp_ne_zero

/-- The defining dense embedding approximates any point in one completion. -/
theorem exists_field_completion_approx (v : HeightOneSpectrum (𝓞 K))
    (a : v.adicCompletion K) (N : ℤ) :
    ∃ x : K, Valued.v (algebraMap K (v.adicCompletion K) x - a) <
      WithZero.exp (-N) := by
  obtain ⟨x, hx⟩ := (v.denseRange_algebraMap K).mem_nhds (completion_small_ball_mem_nhds K v a N)
  exact ⟨x, hx⟩

/-- Global approximation also applies to a finite collection of completed targets. -/
theorem exists_global_completion_approx (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : (v : S) → v.1.adicCompletion K) (N : S → ℤ) :
    ∃ x : K, ∀ v : S,
      Valued.v (algebraMap K (v.1.adicCompletion K) x - a v) <
        WithZero.exp (-N v) := by
  choose y hy using fun v : S => exists_field_completion_approx K v.1 (a v) (N v)
  obtain ⟨x, hx⟩ := exists_global_valuation_approx K S y N
  refine ⟨x, fun v => ?_⟩
  have h1 : Valued.v (algebraMap K (v.1.adicCompletion K) x -
      algebraMap K (v.1.adicCompletion K) (y v)) < WithZero.exp (-N v) := by
    rw [← map_sub]
    change Valued.v ((x - y v : K) : v.1.adicCompletion K) < _
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hx v
  have h2 := hy v
  rw [← sub_add_sub_cancel _ (algebraMap K (v.1.adicCompletion K) (y v)) (a v)]
  exact Valuation.map_add_lt _ h1 h2

/-- Nonzero completed targets admit one nonzero global approximant. -/
theorem exists_global_unit_approx (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : (v : S) → (v.1.adicCompletion K)ˣ) (N : S → ℤ) :
    ∃ x : Kˣ, ∀ v : S,
      Valued.v (algebraMap K (v.1.adicCompletion K) (x : K) - (a v : _)) <
        WithZero.exp (-N v) := by
  have hM : ∀ v : S, ∃ M : ℕ, WithZero.exp (-(M : ℤ)) <
      Valued.v ((a v : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) := fun v =>
    WithZero.exists_exp_neg_natCast_lt ((Valuation.ne_zero_iff _).mpr (a v).ne_zero)
  choose M hM using hM
  obtain ⟨x, hx⟩ := exists_global_completion_approx K S
    (fun v => ((a v : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K))
    (fun v => max (N v) (M v : ℤ))
  by_cases hx0 : x = 0
  · by_cases hS : IsEmpty S
    · exact ⟨1, fun v => (hS.false v).elim⟩
    · rw [not_isEmpty_iff] at hS
      obtain ⟨v⟩ := hS
      exfalso
      have h1 := hx v
      rw [hx0, map_zero, zero_sub, Valuation.map_neg] at h1
      have h2 : WithZero.exp (-(max (N v) (M v : ℤ))) ≤ WithZero.exp (-(M v : ℤ)) :=
        WithZero.exp_le_exp.mpr (by omega)
      exact absurd (h1.trans_le h2) (not_lt.mpr (hM v).le)
  · refine ⟨Units.mk0 x hx0, fun v => ?_⟩
    have h2 : WithZero.exp (-(max (N v) (M v : ℤ))) ≤ WithZero.exp (-(N v)) :=
      WithZero.exp_le_exp.mpr (by omega)
    exact (hx v).trans_le h2

/-- A completed integer is approximated by global integers to arbitrary precision. -/
theorem exists_integer_completion_approx (v : HeightOneSpectrum (𝓞 K))
    (a : v.adicCompletionIntegers K) (N : ℤ) :
    ∃ x : 𝓞 K, Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) x :
      v.adicCompletion K) - a) < WithZero.exp (-N) := by
  obtain ⟨y, hy⟩ := exists_field_completion_approx K v (a : v.adicCompletion K) (max N 0)
  have hle1 : WithZero.exp (-(max N 0)) ≤ 1 := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hya : Valued.v (algebraMap K (v.adicCompletion K) y) ≤ 1 := by
    rw [← sub_add_cancel (algebraMap K (v.adicCompletion K) y) (a : v.adicCompletion K)]
    exact (Valuation.map_add _ _ _).trans (max_le (hy.trans_le hle1).le a.2)
  have hvy : v.valuation K y ≤ 1 := by
    have h1 : Valued.v (algebraMap K (v.adicCompletion K) y) = v.valuation K y := by
      change Valued.v (y : v.adicCompletion K) = _
      exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y
    rwa [h1] at hya
  obtain ⟨c, hc⟩ := v.exists_valuation_sub_lt_of_integer (K := K) hvy
    (Units.mk0 (WithZero.exp (-N)) WithZero.exp_ne_zero)
  rw [Units.val_mk0] at hc
  refine ⟨c, ?_⟩
  have h1 : Valued.v (algebraMap K (v.adicCompletion K) ((c : K) - y)) < WithZero.exp (-N) := by
    change Valued.v (((c : K) - y : K) : v.adicCompletion K) < _
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hc
  have h2 : Valued.v (algebraMap K (v.adicCompletion K) y - a) < WithZero.exp (-N) :=
    hy.trans_le (WithZero.exp_le_exp.mpr (by omega))
  change Valued.v (algebraMap K (v.adicCompletion K) (c : K) - (a : v.adicCompletion K)) < _
  rw [← sub_add_sub_cancel _ (algebraMap K (v.adicCompletion K) y), ← map_sub]
  exact Valuation.map_add_lt _ h1 h2

/-- A fractional element locally integral at a finite set has one denominator avoiding it. -/
theorem exists_locally_integral_fraction (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : K) (hu : ∀ v : S, v.1.valuation K u ≤ 1) :
    ∃ a b : 𝓞 K, b ≠ 0 ∧ (∀ v : S, b ∉ v.1.asIdeal) ∧ u = (a : K) / b := by
  classical
  by_cases hS : S = ∅
  · obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) u
    refine ⟨a, b, nonZeroDivisors.ne_zero hb, fun v => absurd v.2 (by simp [hS]), hab.symm⟩
  · have hloc : ∀ v : S, ∃ (n : 𝓞 K) (d : v.1.asIdeal.primeCompl),
        u * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K n := fun v =>
      v.1.exists_primeCompl_mul_eq_of_integer u (hu v)
    choose n d hnd using hloc
    have hc : ∀ v : S, ∃ c : 𝓞 K, c - 1 ∈ v.1.asIdeal ∧ ∀ w : S, w ≠ v → c ∈ w.1.asIdeal :=
      fun v => by
        obtain ⟨c, hc⟩ := exists_integer_prime_approx K S
          (fun w => if w = v then 1 else 0) (fun _ => 1)
        refine ⟨c, ?_, fun w hw => ?_⟩
        · simpa using hc v
        · simpa [hw] using hc w
    choose c hc1 hc0 using hc
    have hbv : ∀ v : S, (∑ w, c w * (d w : 𝓞 K)) ∉ v.1.asIdeal := fun v hb => by
      have hrest : ∑ w ∈ Finset.univ.erase v, c w * (d w : 𝓞 K) ∈ v.1.asIdeal :=
        Ideal.sum_mem _ fun w hw =>
          Ideal.mul_mem_right _ _ (hc0 w v (Finset.ne_of_mem_erase hw).symm)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)] at hb
      have h1 : c v * (d v : 𝓞 K) ∈ v.1.asIdeal := by
        have h2 := v.1.asIdeal.sub_mem hb hrest
        simpa using h2
      have h2 : (c v - 1) * (d v : 𝓞 K) ∈ v.1.asIdeal := Ideal.mul_mem_right _ _ (hc1 v)
      have h3 : (d v : 𝓞 K) ∈ v.1.asIdeal := by
        have h4 := v.1.asIdeal.sub_mem h1 h2
        simpa [sub_mul] using h4
      exact (d v).2 h3
    obtain ⟨v₀, hv₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have hb0 : (∑ w, c w * (d w : 𝓞 K)) ≠ 0 := fun h =>
      hbv ⟨v₀, hv₀⟩ (h ▸ v₀.asIdeal.zero_mem)
    refine ⟨∑ w, c w * n w, ∑ w, c w * (d w : 𝓞 K), hb0, hbv, ?_⟩
    have hb0' : ((∑ w, c w * (d w : 𝓞 K) : 𝓞 K) : K) ≠ 0 := by exact_mod_cast hb0
    rw [eq_div_iff hb0']
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h1 : u * ((d w : 𝓞 K) : K) = ((n w : 𝓞 K) : K) := hnd w
    rw [mul_left_comm, h1]

/-- A nonzero finite modulus has a finite factorization into positive prime powers. -/
theorem exists_modulus_prime_powers (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ e : S → ℕ,
      (∀ v : S, 0 < e v) ∧ m = ∏ v : S, v.1.asIdeal ^ e v := by
  classical
  have hm0 : m ≠ 0 := hm
  refine ⟨(Ideal.finite_factors hm0).toFinset,
    fun v => (Associates.mk v.1.asIdeal).count (Associates.mk m).factors, fun v => ?_, ?_⟩
  · have hv : v.1.asIdeal ∣ m := (Ideal.finite_factors hm0).mem_toFinset.mp v.2
    exact Nat.pos_of_ne_zero ((Associates.count_ne_zero_iff_dvd hm0 v.1.irreducible).mpr hv)
  · conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hm0]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := (Ideal.finite_factors hm0).toFinset) ?_]
    · rw [← Finset.prod_coe_sort]
      rfl
    · intro v hv
      rw [Function.mem_mulSupport] at hv
      rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      by_contra hdvd
      apply hv
      rw [HeightOneSpectrum.maxPowDividing]
      have hc : (Associates.mk v.asIdeal).count (Associates.mk m).factors = 0 := by
        by_contra hc
        exact hdvd ((Associates.count_ne_zero_iff_dvd hm0 v.irreducible).mp hc)
      rw [hc, pow_zero]

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- A denominator is a residue unit exactly when it avoids the modulus's finite primes. -/
theorem quotient_unit_iff_avoid_primes (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (b : 𝓞 K) :
    IsUnit (Ideal.Quotient.mk m b) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal → b ∉ v.asIdeal := by
  constructor
  · rintro ⟨w, hw⟩ v hmv hbv
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (↑w⁻¹ : 𝓞 K ⧸ m)
    have h1 : Ideal.Quotient.mk m (b * c) = 1 := by rw [map_mul, ← hw, hc, Units.mul_inv]
    have h2 : b * c - 1 ∈ m := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
    have h3 : (1 : 𝓞 K) ∈ v.asIdeal := by
      have h4 := v.asIdeal.sub_mem (v.asIdeal.mul_mem_right c hbv) (hmv h2)
      simpa using h4
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  · intro h
    by_contra hnu
    have hne : Ideal.span {b} ⊔ m ≠ ⊤ := by
      intro htop
      apply hnu
      have h1 : (1 : 𝓞 K) ∈ Ideal.span {b} ⊔ m := htop ▸ Submodule.mem_top
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk m c) ?_
      rw [← map_mul, mul_comm, ← map_one (Ideal.Quotient.mk m), Ideal.Quotient.eq]
      have h2 : c * b - 1 = -z := by rw [← hyz]; ring
      rw [h2]
      exact m.neg_mem hz
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hM0 : M ≠ ⊥ := fun h0 => hm (eq_bot_iff.mpr (h0 ▸ le_sup_right.trans hle))
    exact h ⟨M, hM.isPrime, hM0⟩ (le_sup_right.trans hle)
      (le_sup_left.trans hle (Ideal.mem_span_singleton_self b))

/-- Fractional one-congruence can be tested with any denominator invertible modulo m. -/
theorem mem_rayElements_fraction_iff (m : Ideal (𝓞 K)) (u : Kˣ)
    (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hu : (u : K) = (a : K) / b) (hunit : IsUnit (Ideal.Quotient.mk m b)) :
    u ∈ rayElements K m ↔ a - b ∈ m := by
  constructor
  · intro h
    obtain ⟨α, β, hα, hβ, hαm, hβm, huαβ⟩ := (mem_rayElements_iff_fraction K m u).mp h
    have hcross : a * β = α * b := by
      have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
      have hβ' : (β : K) ≠ 0 := by exact_mod_cast hβ
      have h1 : (a : K) / b = α / β := hu.symm.trans huαβ
      rw [div_eq_div_iff hb' hβ'] at h1
      exact_mod_cast h1
    have h1 : a - b = b * (α - 1) - a * (β - 1) + (a * β - α * b) := by ring
    rw [h1, hcross, sub_self, add_zero]
    exact m.sub_mem (m.mul_mem_left b hαm) (m.mul_mem_left a hβm)
  · intro h
    obtain ⟨a', b', ha', hb', ha'm, hb'm, heq⟩ := exists_integral_ray_fraction K m a b ha hb h hunit
    refine (mem_rayElements_iff_fraction K m u).mpr ⟨a', b', ha', hb', ha'm, hb'm, ?_⟩
    rw [hu]
    exact heq

omit [NumberField K] in
/-- Ray groups grow when the modulus grows. Private: the public lemma is
`rayElements_mono` in `ClassFieldRayNormApproximation`. -/
private theorem rayElements_mono {m m' : Ideal (𝓞 K)} (h : m ≤ m') :
    rayElements K m ≤ rayElements K m' :=
  Subgroup.closure_mono fun _ ⟨α, hα, hαm⟩ => ⟨α, hα, h hαm⟩

/-- A small `u - 1` makes `u` integral at the place. -/
theorem valuation_le_one_of_sub_one_le (v : HeightOneSpectrum (𝓞 K)) {u : K} {t : ℕ}
    (h : v.valuation K (u - 1) ≤ WithZero.exp (-(t : ℤ))) : v.valuation K u ≤ 1 := by
  have h1 : WithZero.exp (-(t : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)
  rw [← sub_add_cancel u 1]
  exact (Valuation.map_add _ _ _).trans (max_le (h.trans h1) (by rw [map_one]))

/-- With a denominator outside `v`, the size of `u - 1` is that of the numerator difference. -/
theorem valuation_sub_one_le_iff_mem_of_fraction (v : HeightOneSpectrum (𝓞 K)) (t : ℕ)
    (u : K) (a b : 𝓞 K) (hb : b ∉ v.asIdeal) (hu : u = (a : K) / b) :
    v.valuation K (u - 1) ≤ WithZero.exp (-(t : ℤ)) ↔ a - b ∈ v.asIdeal ^ t := by
  have hb0 : (b : K) ≠ 0 := by
    intro h
    apply hb
    have hb' : b = 0 := by exact_mod_cast h
    rw [hb']
    exact v.asIdeal.zero_mem
  have hvb : v.valuation K (b : K) = 1 := by
    rw [show v.valuation K (b : K) = v.intValuation b from v.valuation_of_algebraMap (K := K) b,
      v.intValuation_eq_one_iff_mem_primeCompl]
    exact hb
  have h : u - 1 = ((a - b : 𝓞 K) : K) / b := by
    rw [hu]
    push_cast
    field_simp
  rw [h, map_div₀, hvb, div_one, ← v.intValuation_le_pow_iff_mem,
    show v.valuation K ((a - b : 𝓞 K) : K) = v.intValuation (a - b) from
      v.valuation_of_algebraMap (K := K) (a - b)]

/-- A positive prime-power ray condition is precisely its valuation inequality. -/
theorem mem_rayElements_primePower_iff (v : HeightOneSpectrum (𝓞 K))
    (t : ℕ) (ht : 0 < t) (u : Kˣ) :
    u ∈ rayElements K (v.asIdeal ^ t) ↔
      v.valuation K ((u : K) - 1) ≤ WithZero.exp (-(t : ℤ)) := by
  have hvt : v.asIdeal ^ t ≤ v.asIdeal := Ideal.pow_le_self ht.ne'
  have key : ∀ a b : 𝓞 K, a ≠ 0 → b ≠ 0 → b ∉ v.asIdeal → (u : K) = a / b →
      (u ∈ rayElements K (v.asIdeal ^ t) ↔
        v.valuation K ((u : K) - 1) ≤ WithZero.exp (-(t : ℤ))) := by
    intro a b ha hb hbv hu
    have hne : v.asIdeal ^ t ≠ ⊥ := pow_ne_zero t v.ne_bot
    have hunit : IsUnit (Ideal.Quotient.mk (v.asIdeal ^ t) b) := by
      rw [quotient_unit_iff_avoid_primes K _ hne]
      intro w hw hbw
      haveI := w.isPrime
      have hvw : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le hw
      have hvw' : v.asIdeal = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top hvw
      exact hbv (hvw' ▸ hbw)
    rw [mem_rayElements_fraction_iff K _ u a b ha hb hu hunit,
      valuation_sub_one_le_iff_mem_of_fraction K v t (u : K) a b hbv hu]
  constructor
  · intro h
    obtain ⟨α, β, hα, hβ, hαm, hβm, huαβ⟩ := (mem_rayElements_iff_fraction K _ u).mp h
    have hβv : β ∉ v.asIdeal := fun hβv => by
      have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
        have h2 := v.asIdeal.sub_mem hβv (hvt hβm)
        simpa using h2
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    exact (key α β hα hβ hβv huαβ).mp h
  · intro h
    have hvu : v.valuation K (u : K) ≤ 1 := valuation_le_one_of_sub_one_le K v h
    obtain ⟨a, b, hb, hbS, hab⟩ := exists_locally_integral_fraction K {v} (u : K)
      (fun w => by
        have hw : w.1 = v := Finset.mem_singleton.mp w.2
        rw [hw]
        exact hvu)
    have ha : a ≠ 0 := by
      rintro rfl
      apply u.ne_zero
      rw [hab]
      simp
    exact (key a b ha hb (hbS ⟨v, Finset.mem_singleton_self v⟩) hab).mpr h

/-- Prime-power exponents detect membership in a nonzero modulus. -/
theorem ideal_mem_iff_all_primePowers (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (a : 𝓞 K) :
    a ∈ m ↔ ∀ v : HeightOneSpectrum (𝓞 K), ∀ t : ℕ,
      m ≤ v.asIdeal ^ t → a ∈ v.asIdeal ^ t := by
  have hm0 : m ≠ 0 := hm
  constructor
  · intro ha v t hle
    exact hle ha
  · intro h
    rw [← Ideal.iInf_maxPowDividing_eq hm0, Submodule.mem_iInf]
    intro v
    have hle : m ≤ v.maxPowDividing m := by
      conv_lhs => rw [← Ideal.iInf_maxPowDividing_eq hm0]
      exact iInf_le _ v
    exact h v _ hle

/-- The finite fractional congruence is detected at all prime-power divisors. -/
theorem mem_rayElements_iff_all_primePowers (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (u : Kˣ) :
    u ∈ rayElements K m ↔ ∀ v : HeightOneSpectrum (𝓞 K), ∀ t : ℕ,
      0 < t → m ≤ v.asIdeal ^ t →
        v.valuation K ((u : K) - 1) ≤ WithZero.exp (-(t : ℤ)) := by
  classical
  have hm0 : m ≠ 0 := hm
  constructor
  · intro hu v t ht hle
    exact (mem_rayElements_primePower_iff K v t ht u).mp (rayElements_mono K hle hu)
  · intro h
    have hloc : ∀ v : (Ideal.finite_factors hm0).toFinset, v.1.valuation K (u : K) ≤ 1 := by
      intro v
      have hv : m ≤ v.1.asIdeal := Ideal.le_of_dvd ((Ideal.finite_factors hm0).mem_toFinset.mp v.2)
      exact valuation_le_one_of_sub_one_le K v.1 (h v.1 1 one_pos (by rwa [pow_one]))
    obtain ⟨a, b, hb, hbS, hab⟩ := exists_locally_integral_fraction K _ (u : K) hloc
    have hbm : ∀ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal → b ∉ v.asIdeal := fun v hv =>
      hbS ⟨v, (Ideal.finite_factors hm0).mem_toFinset.mpr (Ideal.dvd_iff_le.mpr hv)⟩
    have ha : a ≠ 0 := by
      rintro rfl
      apply u.ne_zero
      rw [hab]
      simp
    have hunit := (quotient_unit_iff_avoid_primes K m hm b).mpr hbm
    rw [mem_rayElements_fraction_iff K m u a b ha hb hab hunit,
      ideal_mem_iff_all_primePowers K m hm]
    intro v t hle
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · have hv : m ≤ v.asIdeal := hle.trans (Ideal.pow_le_self ht.ne')
      exact (valuation_sub_one_le_iff_mem_of_fraction K v t (u : K) a b (hbm v hv) hab).mp
        (h v t ht hle)

/-- The unit ideal imposes no finite congruence condition. -/
theorem rayElements_top : rayElements K (⊤ : Ideal (𝓞 K)) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  rw [mem_rayElements_iff_fraction]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (u : K)
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact u.ne_zero hab.symm
  exact ⟨a, b, ha, nonZeroDivisors.ne_zero hb, Submodule.mem_top, Submodule.mem_top, hab.symm⟩

/-- Congruence at an intersection is equivalent to congruence at both moduli. -/
theorem rayElements_inf (m₁ m₂ : Ideal (𝓞 K)) (hm₁ : m₁ ≠ ⊥) (hm₂ : m₂ ≠ ⊥) :
    rayElements K (m₁ ⊓ m₂) = rayElements K m₁ ⊓ rayElements K m₂ := by
  classical
  apply le_antisymm
  · exact le_inf (rayElements_mono K inf_le_left) (rayElements_mono K inf_le_right)
  · intro u hu
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    have hm0 : m₁ ⊓ m₂ ≠ ⊥ := by
      intro h
      have h1 : m₁ * m₂ = ⊥ := eq_bot_iff.mpr (h ▸ Ideal.mul_le_inf)
      rcases Ideal.mul_eq_bot.mp h1 with h2 | h2
      · exact hm₁ h2
      · exact hm₂ h2
    have hm₁0 : m₁ ≠ 0 := hm₁
    have hm₂0 : m₂ ≠ 0 := hm₂
    let S : Finset (HeightOneSpectrum (𝓞 K)) :=
      (Ideal.finite_factors hm₁0).toFinset ∪ (Ideal.finite_factors hm₂0).toFinset
    have hloc : ∀ v : S, v.1.valuation K (u : K) ≤ 1 := by
      intro v
      rcases Finset.mem_union.mp v.2 with hv | hv
      · have hv' : m₁ ≤ v.1.asIdeal :=
          Ideal.le_of_dvd ((Ideal.finite_factors hm₁0).mem_toFinset.mp hv)
        exact valuation_le_one_of_sub_one_le K v.1
          ((mem_rayElements_iff_all_primePowers K m₁ hm₁ u).mp hu1 v.1 1 one_pos
            (by rwa [pow_one]))
      · have hv' : m₂ ≤ v.1.asIdeal :=
          Ideal.le_of_dvd ((Ideal.finite_factors hm₂0).mem_toFinset.mp hv)
        exact valuation_le_one_of_sub_one_le K v.1
          ((mem_rayElements_iff_all_primePowers K m₂ hm₂ u).mp hu2 v.1 1 one_pos
            (by rwa [pow_one]))
    obtain ⟨a, b, hb, hbS, hab⟩ := exists_locally_integral_fraction K _ (u : K) hloc
    have ha : a ≠ 0 := by
      rintro rfl
      apply u.ne_zero
      rw [hab]
      simp
    have hb1 : ∀ v : HeightOneSpectrum (𝓞 K), m₁ ≤ v.asIdeal → b ∉ v.asIdeal := fun v hv =>
      hbS ⟨v, Finset.mem_union_left _
        ((Ideal.finite_factors hm₁0).mem_toFinset.mpr (Ideal.dvd_iff_le.mpr hv))⟩
    have hb2 : ∀ v : HeightOneSpectrum (𝓞 K), m₂ ≤ v.asIdeal → b ∉ v.asIdeal := fun v hv =>
      hbS ⟨v, Finset.mem_union_right _
        ((Ideal.finite_factors hm₂0).mem_toFinset.mpr (Ideal.dvd_iff_le.mpr hv))⟩
    have hb12 : ∀ v : HeightOneSpectrum (𝓞 K), m₁ ⊓ m₂ ≤ v.asIdeal → b ∉ v.asIdeal :=
      fun v hv => by
        rcases (Ideal.IsPrime.inf_le v.isPrime).mp hv with h | h
        · exact hb1 v h
        · exact hb2 v h
    have h1 := (mem_rayElements_fraction_iff K m₁ u a b ha hb hab
      ((quotient_unit_iff_avoid_primes K m₁ hm₁ b).mpr hb1)).mp hu1
    have h2 := (mem_rayElements_fraction_iff K m₂ u a b ha hb hab
      ((quotient_unit_iff_avoid_primes K m₂ hm₂ b).mpr hb2)).mp hu2
    exact (mem_rayElements_fraction_iff K (m₁ ⊓ m₂) u a b ha hb hab
      ((quotient_unit_iff_avoid_primes K _ hm0 b).mpr hb12)).mpr ⟨h1, h2⟩

/-- A nonzero ideal is divisible by a prime power only below its absolute norm. -/
theorem lt_absNorm_of_le_pow {m : Ideal (𝓞 K)} (hm : m ≠ ⊥) (v : HeightOneSpectrum (𝓞 K))
    {t : ℕ} (h : m ≤ v.asIdeal ^ t) : t < Ideal.absNorm m := by
  have h1 : Ideal.absNorm (v.asIdeal ^ t) ∣ Ideal.absNorm m := Ideal.absNorm_dvd_absNorm_of_le h
  have h2 : Ideal.absNorm m ≠ 0 := fun h0 => hm (Ideal.absNorm_eq_zero_iff.mp h0)
  have h3 : 2 ≤ Ideal.absNorm v.asIdeal := by
    have h4 : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
    have h5 : Ideal.absNorm v.asIdeal ≠ 1 := fun h0 =>
      v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h0)
    omega
  rw [map_pow] at h1
  calc t < 2 ^ t := Nat.lt_two_pow_self
    _ ≤ Ideal.absNorm v.asIdeal ^ t := Nat.pow_le_pow_left h3 t
    _ ≤ Ideal.absNorm m := Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1

/-- Approximation separates the two ray conditions for coprime nonzero moduli. -/
theorem rayElements_sup_of_coprime (m₁ m₂ : Ideal (𝓞 K))
    (hm₁ : m₁ ≠ ⊥) (hm₂ : m₂ ≠ ⊥) (hcop : m₁ ⊔ m₂ = ⊤) :
    rayElements K m₁ ⊔ rayElements K m₂ = ⊤ := by
  classical
  by_cases htop : m₁ = ⊤
  · rw [htop, rayElements_top, top_sup_eq]
  rw [eq_top_iff]
  intro u _
  have hm₁0 : m₁ ≠ 0 := hm₁
  have hm₂0 : m₂ ≠ 0 := hm₂
  have hmem₁ : ∀ v : HeightOneSpectrum (𝓞 K),
      v ∈ (Ideal.finite_factors hm₁0).toFinset ↔ m₁ ≤ v.asIdeal := fun v => by
    rw [(Ideal.finite_factors hm₁0).mem_toFinset]
    exact Ideal.dvd_iff_le
  have hmem₂ : ∀ v : HeightOneSpectrum (𝓞 K),
      v ∈ (Ideal.finite_factors hm₂0).toFinset ↔ m₂ ≤ v.asIdeal := fun v => by
    rw [(Ideal.finite_factors hm₂0).mem_toFinset]
    exact Ideal.dvd_iff_le
  have hdisj : ∀ v, v ∈ (Ideal.finite_factors hm₂0).toFinset →
      v ∉ (Ideal.finite_factors hm₁0).toFinset := fun v h2 h1 => by
    rw [hmem₁] at h1
    rw [hmem₂] at h2
    exact v.isPrime.ne_top (eq_top_iff.mpr (hcop ▸ sup_le h1 h2))
  have hvu : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (u : K) ≠ 0 := fun v => by
    rw [ne_eq, map_eq_zero]
    exact u.ne_zero
  choose n hn using fun v : HeightOneSpectrum (𝓞 K) =>
    WithZero.exists_exp_neg_natCast_lt
      (mul_ne_zero (WithZero.exp_ne_zero (a := -(Ideal.absNorm m₂ : ℤ))) (hvu v))
  obtain ⟨x, hx⟩ := exists_global_valuation_approx K
    ((Ideal.finite_factors hm₁0).toFinset ∪ (Ideal.finite_factors hm₂0).toFinset)
    (fun v => if v.1 ∈ (Ideal.finite_factors hm₁0).toFinset then 1 else (u : K))
    (fun v => if v.1 ∈ (Ideal.finite_factors hm₁0).toFinset then (Ideal.absNorm m₁ : ℤ)
      else (n v.1 : ℤ))
  have hx1 : ∀ v, v ∈ (Ideal.finite_factors hm₁0).toFinset →
      v.valuation K (x - 1) < WithZero.exp (-(Ideal.absNorm m₁ : ℤ)) := fun v hv => by
    have h := hx ⟨v, Finset.mem_union_left _ hv⟩
    simpa [hv] using h
  have hx2 : ∀ v, v ∈ (Ideal.finite_factors hm₂0).toFinset →
      v.valuation K (x - u) < WithZero.exp (-(n v : ℤ)) := fun v hv => by
    have h := hx ⟨v, Finset.mem_union_right _ hv⟩
    simpa [hdisj v hv] using h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal m₁ htop
  have hM0 : M ≠ ⊥ := fun h0 => hm₁ (eq_bot_iff.mpr (h0 ▸ hle))
  have hv₀ : (⟨M, hM.isPrime, hM0⟩ : HeightOneSpectrum (𝓞 K)) ∈
      (Ideal.finite_factors hm₁0).toFinset := (hmem₁ _).mpr hle
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h := hx1 _ hv₀
    rw [zero_sub, Valuation.map_neg, map_one] at h
    exact absurd h (not_lt.mpr (by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)))
  refine Subgroup.mem_sup.mpr ⟨Units.mk0 x hx0, ?_, (Units.mk0 x hx0)⁻¹ * u, ?_, by group⟩
  · rw [mem_rayElements_iff_all_primePowers K m₁ hm₁]
    intro v t ht hle'
    have hv : v ∈ (Ideal.finite_factors hm₁0).toFinset :=
      (hmem₁ v).mpr (hle'.trans (Ideal.pow_le_self ht.ne'))
    have htlt := lt_absNorm_of_le_pow K hm₁ v hle'
    rw [Units.val_mk0]
    exact (hx1 v hv).le.trans (WithZero.exp_le_exp.mpr (by omega))
  · rw [mem_rayElements_iff_all_primePowers K m₂ hm₂]
    intro v t ht hle'
    have hv : v ∈ (Ideal.finite_factors hm₂0).toFinset :=
      (hmem₂ v).mpr (hle'.trans (Ideal.pow_le_self ht.ne'))
    have htlt := lt_absNorm_of_le_pow K hm₂ v hle'
    have h1 : v.valuation K (x - u) <
        WithZero.exp (-(Ideal.absNorm m₂ : ℤ)) * v.valuation K (u : K) :=
      (hx2 v hv).trans (hn v)
    have hP : WithZero.exp (-(Ideal.absNorm m₂ : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have h2 : v.valuation K (x - u) < v.valuation K (u : K) :=
      h1.trans_le (mul_le_of_le_one_left zero_le' hP)
    have hvx : v.valuation K x = v.valuation K (u : K) := Valuation.map_eq_of_sub_lt _ h2
    have h3 : (((Units.mk0 x hx0)⁻¹ * u : Kˣ) : K) - 1 = ((u : K) - x) / x := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
    rw [h3, map_div₀, hvx, Valuation.map_sub_swap,
      div_le_iff₀ (zero_lt_iff.mpr (hvu v))]
    exact h1.le.trans (mul_le_mul_left (WithZero.exp_le_exp.mpr (by omega)) _)

/-- The group Chinese remainder map is bijective when the two subgroups generate G. -/
theorem quotient_inf_equiv_prod (G : Type*) [CommGroup G] (H J : Subgroup G)
    (h : H ⊔ J = ⊤) : Nonempty ((G ⧸ (H ⊓ J)) ≃* (G ⧸ H) × (G ⧸ J)) := by
  let φ : G →* (G ⧸ H) × (G ⧸ J) := (QuotientGroup.mk' H).prod (QuotientGroup.mk' J)
  have hker : φ.ker = H ⊓ J := by
    ext g
    simp [φ, MonoidHom.mem_ker, Prod.ext_iff, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective H x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective J y
    have hab : a * b⁻¹ ∈ H ⊔ J := h ▸ Subgroup.mem_top _
    obtain ⟨p, hp, q, hq, hpq⟩ := Subgroup.mem_sup.mp hab
    refine ⟨a * p⁻¹, Prod.ext ?_ ?_⟩
    · change QuotientGroup.mk' H (a * p⁻¹) = QuotientGroup.mk' H a
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have h1 : (a * p⁻¹)⁻¹ * a = p := by group
      rw [h1]
      exact hp
    · change QuotientGroup.mk' J (a * p⁻¹) = QuotientGroup.mk' J b
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have hq' : q = p⁻¹ * (a * b⁻¹) := by rw [← hpq]; group
      have h1 : (a * p⁻¹)⁻¹ * b = q⁻¹ := by
        rw [hq']
        simp only [mul_inv_rev, inv_inv]
        simp only [mul_comm, mul_left_comm]
      rw [h1]
      exact J.inv_mem hq
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

end Cox.ClassFieldTheory
