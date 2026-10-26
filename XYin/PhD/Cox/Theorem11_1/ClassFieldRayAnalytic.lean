/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldRayCounting
import XYin.PhD.Cox.Theorem11_1.ChebotarevCyclotomic

/-! # Janusz IV.4.7: primes in a congruence subgroup

Finite character orthogonality and an upper bound on nonprincipal L-series suffice.
No nonvanishing at one, reciprocity, or class-field existence is assumed. The upper
bound comes from Abel summation and the uniform congruence-class count.
-/

open NumberField Filter Topology Set
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K))
variable (H : Subgroup (coprimeIdeals K m))

/-- Extend a finite ideal-class character by zero on ideals meeting the modulus. -/
def congruenceCharacterValue (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ)
    (A : Ideal (𝓞 K)) : ℂ :=
  if h : A ≠ ⊥ ∧ A ⊔ m = ⊤ then
    χ (QuotientGroup.mk (Classical.choose (exists_coprimeIdealUnit K m A h.1 h.2)))
  else 0

/-- Independence of the chosen unit representative of an integral ideal. -/
theorem congruenceCharacterValue_eq (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ)
    (A : Ideal (𝓞 K)) (hA : A ≠ ⊥) (hAm : A ⊔ m = ⊤) (u : coprimeIdeals K m)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = A) :
    congruenceCharacterValue K m H χ A = χ (QuotientGroup.mk u) := by
  have hrep : Classical.choose (exists_coprimeIdealUnit K m A hA hAm) = u :=
    Subtype.ext (Units.ext
      ((Classical.choose_spec (exists_coprimeIdealUnit K m A hA hAm)).trans hu.symm))
  unfold congruenceCharacterValue
  rw [dif_pos ⟨hA, hAm⟩, hrep]

/-- The ideal-character weight equals one at the unit ideal. -/
theorem congruenceCharacterValue_one (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) :
    congruenceCharacterValue K m H χ ⊤ = 1 := by
  rw [congruenceCharacterValue_eq K m H χ ⊤ top_ne_bot (top_sup_eq m) 1
    (by simp [FractionalIdeal.coeIdeal_top])]
  simp

/-- Complete multiplicativity includes the zero weights at excluded prime factors. -/
theorem congruenceCharacterValue_mul (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ)
    (A B : Ideal (𝓞 K)) : congruenceCharacterValue K m H χ (A * B) =
      congruenceCharacterValue K m H χ A * congruenceCharacterValue K m H χ B := by
  by_cases hA : A ≠ ⊥ ∧ A ⊔ m = ⊤
  · by_cases hB : B ≠ ⊥ ∧ B ⊔ m = ⊤
    · have hAB0 : A * B ≠ ⊥ := mul_ne_zero hA.1 hB.1
      have hABm : A * B ⊔ m = ⊤ := Ideal.isCoprime_iff_sup_eq.mp
        ((Ideal.isCoprime_iff_sup_eq.mpr hA.2).mul_left (Ideal.isCoprime_iff_sup_eq.mpr hB.2))
      obtain ⟨uA, huA⟩ := exists_coprimeIdealUnit K m A hA.1 hA.2
      obtain ⟨uB, huB⟩ := exists_coprimeIdealUnit K m B hB.1 hB.2
      rw [congruenceCharacterValue_eq K m H χ A hA.1 hA.2 uA huA,
        congruenceCharacterValue_eq K m H χ B hB.1 hB.2 uB huB,
        congruenceCharacterValue_eq K m H χ (A * B) hAB0 hABm (uA * uB)
          (by rw [Subgroup.coe_mul, Units.val_mul, huA, huB, FractionalIdeal.coeIdeal_mul]),
        QuotientGroup.mk_mul, map_mul, Units.val_mul]
    · have hAB : ¬ (A * B ≠ ⊥ ∧ A * B ⊔ m = ⊤) := by
        rintro ⟨h0, hm⟩
        apply hB
        refine ⟨fun hB0 => h0 (by rw [hB0, Ideal.mul_bot]), ?_⟩
        exact eq_top_iff.mpr (hm ▸ sup_le_sup_right Ideal.mul_le_left m)
      simp only [congruenceCharacterValue, dif_neg hAB, dif_neg hB, mul_zero]
  · have hAB : ¬ (A * B ≠ ⊥ ∧ A * B ⊔ m = ⊤) := by
      rintro ⟨h0, hm⟩
      apply hA
      refine ⟨fun hA0 => h0 (by rw [hA0, Ideal.bot_mul]), ?_⟩
      exact eq_top_iff.mpr (hm ▸ sup_le_sup_right Ideal.mul_le_right m)
    simp only [congruenceCharacterValue, dif_neg hAB, dif_neg hA, zero_mul]

/-- Values of a character of a finite quotient lie on the unit circle. -/
theorem norm_character_eq_one [H.FiniteIndex] (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ)
    (q : coprimeIdeals K m ⧸ H) : ‖((χ q : ℂˣ) : ℂ)‖ = 1 := by
  have h1 : (χ q) ^ Nat.card (coprimeIdeals K m ⧸ H) = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  have h2 : ((χ q : ℂˣ) : ℂ) ^ Nat.card (coprimeIdeals K m ⧸ H) = 1 := by
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h2 Nat.card_pos.ne'

/-- Characters of a finite quotient have modulus one on good ideals and vanish elsewhere. -/
theorem norm_congruenceCharacterValue_le_one [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (A : Ideal (𝓞 K)) :
    ‖congruenceCharacterValue K m H χ A‖ ≤ 1 := by
  unfold congruenceCharacterValue
  split_ifs with h
  · exact (norm_character_eq_one K m H χ _).le
  · simp

/-- The ideal Dirichlet series attached to a congruence character. -/
def congruenceLSeries (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (s : ℂ) : ℂ :=
  ∑' A : Chebotarev.NonzeroIdeal K,
    congruenceCharacterValue K m H χ A.1 * (A.1.absNorm : ℂ) ^ (-s)

/-- Group ideal weights by their positive integral norm. -/
def congruenceCharacterCoeff (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (n : ℕ) : ℂ :=
  ∑' A : {A : Chebotarev.NonzeroIdeal K // A.1.absNorm = n},
    congruenceCharacterValue K m H χ A.1.1

/-- The ideal Dirichlet series of a bounded character weight converges absolutely. -/
theorem summable_congruenceIdealSeries [H.FiniteIndex] (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun A : Chebotarev.NonzeroIdeal K =>
      congruenceCharacterValue K m H χ A.1 * (A.1.absNorm : ℂ) ^ (-s)) := by
  refine Summable.of_norm_bounded
    (Chebotarev.hasSum_nonzeroIdeal_absNorm_cpow K hs).summable.norm fun A => ?_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_congruenceCharacterValue_le_one K m H χ A.1)

/-- The L-series terms of the coefficient sequence are the norm-fibre sums. -/
theorem term_congruenceCharacterCoeff (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (s : ℂ) (n : ℕ) :
    LSeries.term (congruenceCharacterCoeff K m H χ) s n =
      ∑' y : {I : Chebotarev.NonzeroIdeal K // Ideal.absNorm I.1 = n},
        congruenceCharacterValue K m H χ y.1.1 * (y.1.1.absNorm : ℂ) ^ (-s) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [LSeries.term_zero]
    haveI : IsEmpty {I : Chebotarev.NonzeroIdeal K // Ideal.absNorm I.1 = 0} :=
      ⟨fun I => I.1.2 (Ideal.absNorm_eq_zero_iff.mp I.2)⟩
    rw [tsum_empty]
  · rw [LSeries.term_of_ne_zero hn.ne', congruenceCharacterCoeff, div_eq_mul_inv,
      ← tsum_mul_right]
    refine tsum_congr fun y => ?_
    rw [y.2, Complex.cpow_neg]

/-- Absolute convergence to the right of one follows from Dedekind zeta domination. -/
theorem congruenceCharacterCoeff_summable [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (congruenceCharacterCoeff K m H χ) s := by
  set e := Equiv.sigmaFiberEquiv (fun I : Chebotarev.NonzeroIdeal K ↦ Ideal.absNorm I.1)
  have hFs : Summable (fun p => congruenceCharacterValue K m H χ (e p).1 *
      ((e p).1.absNorm : ℂ) ^ (-s)) :=
    e.summable_iff.mpr (summable_congruenceIdealSeries K m H χ hs)
  unfold LSeriesSummable
  refine hFs.sigma.congr fun n => ?_
  rw [term_congruenceCharacterCoeff]
  rfl

/-- Norm-fiber regrouping agrees with the ordinary L-series coefficients. -/
theorem lSeries_congruenceCharacterCoeff_eq [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (s : ℂ) (hs : 1 < s.re) :
    LSeries (congruenceCharacterCoeff K m H χ) s = congruenceLSeries K m H χ s := by
  set e := Equiv.sigmaFiberEquiv (fun I : Chebotarev.NonzeroIdeal K ↦ Ideal.absNorm I.1)
  have hFs : Summable (fun p => congruenceCharacterValue K m H χ (e p).1 *
      ((e p).1.absNorm : ℂ) ^ (-s)) :=
    e.summable_iff.mpr (summable_congruenceIdealSeries K m H χ hs)
  rw [congruenceLSeries, ← e.tsum_eq, hFs.tsum_sigma, LSeries]
  exact tsum_congr fun n => term_congruenceCharacterCoeff K m H χ s n

/-- Regroup a finite coefficient sum by its ideal class. -/
theorem sum_congruenceCharacterCoeff_eq_class_sum [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, congruenceCharacterCoeff K m H χ k =
      ∑' c : coprimeIdeals K m ⧸ H,
        (congruenceClassIdealCount K m H c (n : ℝ) : ℂ) * (χ c : ℂ) := by
  classical
  letI := Fintype.ofFinite (coprimeIdeals K m ⧸ H)
  let cls : Ideal (𝓞 K) → Option (coprimeIdeals K m ⧸ H) := fun A =>
    if h : A ≠ ⊥ ∧ A ⊔ m = ⊤ then
      some (QuotientGroup.mk (Classical.choose (exists_coprimeIdealUnit K m A h.1 h.2)))
    else none
  let val : Option (coprimeIdeals K m ⧸ H) → ℂ := fun o => o.elim 0 (fun c => (χ c : ℂ))
  have hcCV : ∀ A, congruenceCharacterValue K m H χ A = val (cls A) := by
    intro A
    unfold congruenceCharacterValue
    simp only [cls, val]
    split_ifs <;> rfl
  have hmem : ∀ A c, A ∈ integralIdealsInCongruenceClass K m H c ↔ cls A = some c := by
    intro A c
    constructor
    · rintro ⟨hA0, hAm, u, hu, huc⟩
      have hrep : Classical.choose (exists_coprimeIdealUnit K m A hA0 hAm) = u :=
        Subtype.ext (Units.ext
          ((Classical.choose_spec (exists_coprimeIdealUnit K m A hA0 hAm)).trans hu.symm))
      simp only [cls, dif_pos (show A ≠ ⊥ ∧ A ⊔ m = ⊤ from ⟨hA0, hAm⟩), hrep, huc]
    · intro h
      simp only [cls] at h
      split_ifs at h with hg
      exact ⟨hg.1, hg.2, _, Classical.choose_spec (exists_coprimeIdealUnit K m A hg.1 hg.2),
        Option.some.inj h⟩
  set T : Finset (Ideal (𝓞 K)) :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) n).toFinset.filter (· ≠ ⊥) with hTdef
  have hT : ∀ A, A ∈ T ↔ A ≠ ⊥ ∧ A.absNorm ≤ n := by
    intro A
    simp only [hTdef, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact and_comm
  have hcoeff : ∀ k ∈ Finset.Icc 1 n, congruenceCharacterCoeff K m H χ k =
      ∑ A ∈ T.filter (fun A => A.absNorm = k), congruenceCharacterValue K m H χ A := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    unfold congruenceCharacterCoeff
    let e : {I : Chebotarev.NonzeroIdeal K // Ideal.absNorm I.1 = k} ≃
        {A : Ideal (𝓞 K) // A ∈ T.filter (fun A => A.absNorm = k)} :=
      { toFun := fun y => ⟨y.1.1, Finset.mem_filter.mpr
          ⟨(hT _).mpr ⟨y.1.2, (le_of_eq y.2).trans hk.2⟩, y.2⟩⟩
        invFun := fun A => ⟨⟨A.1, ((hT _).mp (Finset.mem_filter.mp A.2).1).1⟩,
          (Finset.mem_filter.mp A.2).2⟩
        left_inv := fun y => rfl
        right_inv := fun A => rfl }
    rw [← Finset.tsum_subtype]
    exact e.tsum_eq (fun A : {A : Ideal (𝓞 K) // A ∈ T.filter (fun A => A.absNorm = k)} =>
      congruenceCharacterValue K m H χ A.1)
  have hstep1 : ∑ k ∈ Finset.Icc 1 n, congruenceCharacterCoeff K m H χ k =
      ∑ A ∈ T, congruenceCharacterValue K m H χ A := by
    rw [Finset.sum_congr rfl hcoeff]
    exact Finset.sum_fiberwise_of_maps_to (fun A hA => by
      obtain ⟨h0, hle⟩ := (hT A).mp hA
      exact Finset.mem_Icc.mpr
        ⟨Nat.pos_of_ne_zero (fun h => h0 (Ideal.absNorm_eq_zero_iff.mp h)), hle⟩) _
  have hfib : ∀ o, ∑ A ∈ T with cls A = o, val (cls A) =
      (T.filter (fun A => cls A = o)).card • val o := by
    intro o
    rw [Finset.sum_congr rfl (fun A hA => by rw [(Finset.mem_filter.mp hA).2]),
      Finset.sum_const]
  have hcount : ∀ c, congruenceClassIdealCount K m H c (n : ℝ) =
      (T.filter (fun A => cls A = some c)).card := by
    intro c
    have hset : {A : Ideal (𝓞 K) | A ∈ integralIdealsInCongruenceClass K m H c ∧
        (A.absNorm : ℝ) ≤ n} = ↑(T.filter (fun A => cls A = some c)) := by
      ext A
      simp only [Set.mem_setOf_eq, Finset.coe_filter, hT, Nat.cast_le]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1.1, h2⟩, (hmem A c).mp h1⟩
      · rintro ⟨⟨-, h2⟩, h3⟩
        exact ⟨(hmem A c).mpr h3, h2⟩
    unfold congruenceClassIdealCount
    rw [show Nat.card {A : Ideal (𝓞 K) // A ∈ integralIdealsInCongruenceClass K m H c ∧
        (A.absNorm : ℝ) ≤ n} = Nat.card ↥{A : Ideal (𝓞 K) | A ∈
          integralIdealsInCongruenceClass K m H c ∧ (A.absNorm : ℝ) ≤ n} from rfl, hset,
      Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hstep1, tsum_fintype]
  simp_rw [hcCV]
  rw [← Finset.sum_fiberwise T cls (fun A => val (cls A)), Fintype.sum_option]
  simp only [hfib]
  simp only [val, Option.elim_none, Option.elim_some, smul_zero, zero_add, nsmul_eq_mul,
    hcount]

/-- Uniform class counting and row orthogonality cancel the common leading term. -/
theorem sum_congruenceCharacterCoeff_bound (hm : m ≠ ⊥)
    (hH : raySubgroup K m ≤ H) [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, congruenceCharacterCoeff K m H χ k‖ ≤
        C * (n : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  classical
  letI := Fintype.ofFinite (coprimeIdeals K m ⧸ H)
  obtain ⟨κ, -, C₀, hC₀, hcount⟩ := exists_congruenceClassIdealCount_error K m hm H hH
  have hN : (0 : ℝ) < Fintype.card (coprimeIdeals K m ⧸ H) := by
    exact_mod_cast Fintype.card_pos
  refine ⟨Fintype.card (coprimeIdeals K m ⧸ H) * C₀, mul_pos hN hC₀, fun n => ?_⟩
  have he : 0 ≤ (n : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_pos hN hC₀).le he
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [sum_congruenceCharacterCoeff_eq_class_sum K m H χ n, tsum_fintype]
  have hrow : ∑ c : coprimeIdeals K m ⧸ H, (κ * n : ℂ) * (χ c : ℂ) = 0 := by
    rw [← Finset.mul_sum, Chebotarev.sum_char_self_eq_zero_of_ne_one hχ, mul_zero]
  rw [← sub_zero (∑ c : coprimeIdeals K m ⧸ H,
      (congruenceClassIdealCount K m H c (n : ℝ) : ℂ) * (χ c : ℂ)), ← hrow,
    ← Finset.sum_sub_distrib]
  calc ‖∑ c : coprimeIdeals K m ⧸ H, ((congruenceClassIdealCount K m H c (n : ℝ) : ℂ) *
        (χ c : ℂ) - (κ * n : ℂ) * (χ c : ℂ))‖
      ≤ ∑ c : coprimeIdeals K m ⧸ H, ‖(congruenceClassIdealCount K m H c (n : ℝ) : ℂ) *
        (χ c : ℂ) - (κ * n : ℂ) * (χ c : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _c : coprimeIdeals K m ⧸ H, C₀ * (n : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
      refine Finset.sum_le_sum fun c _ => ?_
      rw [← sub_mul, norm_mul, norm_character_eq_one K m H χ c, mul_one]
      have h := hcount c n hx
      have heq : ((congruenceClassIdealCount K m H c (n : ℝ) : ℂ) - (κ * n : ℂ)) =
          (((congruenceClassIdealCount K m H c (n : ℝ) : ℝ) - κ * n : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
      exact h
    _ = Fintype.card (coprimeIdeals K m ⧸ H) * C₀ *
        (n : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The Abel integral is dominated uniformly by C times the integral of t^(r-2). -/
theorem norm_abelIntegral_le (a : ℕ → ℂ) {r C : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 < C)
    (hpartial : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, a k‖ ≤ C * (n : ℝ) ^ r)
    {s : ℝ} (hs : 1 < s) :
    ‖∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, a k) * (t : ℂ) ^ (-((s : ℂ) + 1))‖ ≤ C / (1 - r) := by
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => C * t ^ (r - 2)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul C
  have hbound : ∀ᵐ (t : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))),
      ‖(∑ k ∈ Finset.Icc 1 ⌊t⌋₊, a k) * (t : ℂ) ^ (-((s : ℂ) + 1))‖ ≤ C * t ^ (r - 2) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Set.mem_Ioi] at ht
    have ht0 : 0 < t := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have h1 : ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, a k‖ ≤ C * t ^ r :=
      (hpartial _).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le ht0.le) hr0) hC.le)
    have h2 : t ^ (-((s : ℂ) + 1)).re ≤ t ^ (-(2 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le ht.le
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
      linarith
    calc ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, a k‖ * t ^ (-((s : ℂ) + 1)).re
        ≤ C * t ^ r * t ^ (-(2 : ℝ)) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg ht0.le _) (by positivity)
      _ = C * t ^ (r - 2) := by
          rw [mul_assoc, ← Real.rpow_add ht0]
          ring_nf
  refine (MeasureTheory.norm_integral_le_of_norm_le hint hbound).trans (le_of_eq ?_)
  have h2 : r - 2 + 1 = -(1 - r) := by ring
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos,
    Real.one_rpow, h2, neg_div_neg_eq, mul_one_div]

/-- Abel summation bounds an L-series uniformly near one when its partial sums grow sublinearly. -/
theorem lSeries_norm_bounded_of_partial_sum_bound (a : ℕ → ℂ)
    {r C : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 < C)
    (hpartial : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, a k‖ ≤ C * (n : ℝ) ^ r)
    (hsum : ∀ s : ℝ, 1 < s → LSeriesSummable a (s : ℂ)) :
    ∃ D : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1, ‖LSeries a (s : ℂ)‖ ≤ D := by
  have hO : (fun n ↦ ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop] fun n ↦ (n : ℝ) ^ r :=
    Asymptotics.IsBigO.of_bound C (Eventually.of_forall fun n => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact hpartial n)
  refine ⟨2 * (C / (1 - r)), ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with s hs
  have hs1 : 1 < s := hs.1
  rw [LSeries_eq_mul_integral a hr0 (by simp only [Complex.ofReal_re]; linarith) (hsum s hs1) hO,
    norm_mul]
  have hnorm : ‖(s : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact hs.2.le
  exact mul_le_mul hnorm (norm_abelIntegral_le a hr0 hr1 hC hpartial hs1) (norm_nonneg _)
    zero_le_two

/-- The boundedness input to IV.4.7; nonvanishing at one is unnecessary. -/
theorem congruenceLSeries_norm_bounded (hm : m ≠ ⊥)
    (hH : raySubgroup K m ≤ H) [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1, ‖congruenceLSeries K m H χ (s : ℂ)‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := sum_congruenceCharacterCoeff_bound K m H hm hH χ hχ
  have hd : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hr0 : 0 ≤ 1 - 1 / (Module.finrank ℚ K : ℝ) := by
    rw [sub_nonneg]
    exact div_le_one_of_le₀ hd (by linarith)
  have hr1 : 1 - 1 / (Module.finrank ℚ K : ℝ) < 1 := by
    have : 0 < 1 / (Module.finrank ℚ K : ℝ) := by positivity
    linarith
  obtain ⟨D, hD⟩ := lSeries_norm_bounded_of_partial_sum_bound
    (congruenceCharacterCoeff K m H χ) hr0 hr1 hC0 hC
    (fun s hs => congruenceCharacterCoeff_summable K m H χ (s : ℂ) (by simpa using hs))
  refine ⟨D, ?_⟩
  filter_upwards [hD, self_mem_nhdsWithin] with s hs hs1
  rw [Set.mem_Ioi] at hs1
  rw [← lSeries_congruenceCharacterCoeff_eq K m H χ (s : ℂ) (by simpa using hs1)]
  exact hs

/-- Janusz IV.4.2: the Euler product for the completely multiplicative ideal weight. -/
theorem congruenceLSeries_eq_eulerProduct [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (s : ℂ) (hs : 1 < s.re) :
    congruenceLSeries K m H χ s =
      ∏' q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥},
        (1 - congruenceCharacterValue K m H χ q.1 * (q.1.absNorm : ℂ) ^ (-s))⁻¹ := by
  rw [congruenceLSeries, Chebotarev.weighted_eulerProduct_eq_tsum K hs
    (congruenceCharacterValue K m H χ) (congruenceCharacterValue_one K m H χ)
    (fun _ _ => congruenceCharacterValue_mul K m H χ _ _)
    (norm_congruenceCharacterValue_le_one K m H χ)]

/-- The prime-ideal linear term of the logarithmic Euler expansion. -/
def congruencePrimeSum (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (s : ℝ) : ℂ :=
  ∑' q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥},
    congruenceCharacterValue K m H χ q.1 * (q.1.absNorm : ℂ) ^ (-(s : ℂ))

/-- The absolutely convergent logarithmic Euler sum for real s>1. -/
def congruenceLogSum (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (s : ℝ) : ℂ :=
  ∑' q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥},
    -Complex.log (1 - congruenceCharacterValue K m H χ q.1 *
      (q.1.absNorm : ℂ) ^ (-(s : ℂ)))

/-- A weighted prime term with weight of norm at most one is dominated by the norm power. -/
theorem norm_weighted_prime_term_le (w : Ideal (𝓞 K) → ℂ) (hw : ∀ A, ‖w A‖ ≤ 1)
    (q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥}) (s : ℝ) :
    ‖w q.1 * (q.1.absNorm : ℂ) ^ (-(s : ℂ))‖ ≤ (Ideal.absNorm q.1 : ℝ) ^ (-s) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp q.2.2))]
  simp only [Complex.neg_re, Complex.ofReal_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hw q.1)

/-- Prime sums with weights of norm at most one converge absolutely to the right of one. -/
theorem summable_weighted_primeSum (w : Ideal (𝓞 K) → ℂ) (hw : ∀ A, ‖w A‖ ≤ 1)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥} ↦
      w q.1 * (q.1.absNorm : ℂ) ^ (-(s : ℂ))) :=
  Summable.of_norm_bounded (Chebotarev.summable_prime2_absNorm_rpow K hs)
    fun q => norm_weighted_prime_term_le K w hw q s

/-- Prime-sum absolute convergence permits finite-character interchange. -/
theorem summable_congruencePrimeSum [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) {s : ℝ} (hs : 1 < s) :
    Summable (fun q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥} ↦
      congruenceCharacterValue K m H χ q.1 * (q.1.absNorm : ℂ) ^ (-(s : ℂ))) := by
  exact summable_weighted_primeSum K _ (norm_congruenceCharacterValue_le_one K m H χ) hs

/-- Exponentiating the convergent log sum recovers the nonzero Euler product. -/
theorem exp_congruenceLogSum_eq [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) {s : ℝ} (hs : 1 < s) :
    Complex.exp (congruenceLogSum K m H χ s) = congruenceLSeries K m H χ (s : ℂ) := by
  have hsl : ∀ q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥},
      (1 - congruenceCharacterValue K m H χ q.1 * (q.1.absNorm : ℂ) ^ (-(s : ℂ))) ∈
        Complex.slitPlane := by
    intro q
    rw [sub_eq_add_neg]
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_neg]
    exact (norm_weighted_prime_term_le K _ (norm_congruenceCharacterValue_le_one K m H χ) q
      s).trans_lt (Chebotarev.absNorm_rpow_neg_lt_one K q.2.1 q.2.2 hs)
  rw [congruenceLogSum, Chebotarev.cexp_logSum_eq_tprod _
    (summable_congruencePrimeSum K m H χ hs) hsl,
    congruenceLSeries_eq_eulerProduct K m H χ (s : ℂ) (by simpa using hs)]

/-- Norms remove the branch ambiguity in the complex logarithmic Euler sum. -/
theorem re_congruenceLogSum_eq_log_norm [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) {s : ℝ} (hs : 1 < s) :
    (congruenceLogSum K m H χ s).re = Real.log ‖congruenceLSeries K m H χ (s : ℂ)‖ := by
  rw [← exp_congruenceLogSum_eq K m H χ hs, Complex.norm_exp, Real.log_exp]

/-- The quadratic log remainder is dominated by the convergent prime-norm square sum. -/
theorem congruenceLogSum_sub_primeSum_bounded [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      ‖congruenceLogSum K m H χ s - congruencePrimeSum K m H χ s‖ ≤ C := by
  refine ⟨∑' q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥},
    (Ideal.absNorm q.1 : ℝ) ^ (-(2 : ℝ)), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  have hterm : ∀ q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥},
      ‖-Complex.log (1 - congruenceCharacterValue K m H χ q.1 *
          (q.1.absNorm : ℂ) ^ (-(s : ℂ))) -
        congruenceCharacterValue K m H χ q.1 * (q.1.absNorm : ℂ) ^ (-(s : ℂ))‖ ≤
      (Ideal.absNorm q.1 : ℝ) ^ (-(2 : ℝ)) := by
    intro q
    have hN := Chebotarev.two_le_absNorm_prime K q.1 q.2.1 q.2.2
    by_cases hgood : q.1 ≠ ⊥ ∧ q.1 ⊔ m = ⊤
    · have hc : ‖congruenceCharacterValue K m H χ q.1‖ = 1 := by
        unfold congruenceCharacterValue
        rw [dif_pos hgood]
        exact norm_character_eq_one K m H χ _
      exact Chebotarev.norm_logSumTerm_sub_self_le_aux (ι := Unit)
        (fun _ => Ideal.absNorm q.1) (fun _ => congruenceCharacterValue K m H χ q.1) s hs
        (fun _ => hN) (fun _ => hc) ()
    · have h0 : congruenceCharacterValue K m H χ q.1 = 0 := by
        unfold congruenceCharacterValue
        rw [dif_neg hgood]
      rw [h0]
      simp only [zero_mul, sub_zero, Complex.log_one, neg_zero, norm_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsumw := summable_congruencePrimeSum K m H χ hs
  have hsumlog : Summable (fun q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥} =>
      -Complex.log (1 - congruenceCharacterValue K m H χ q.1 *
        (q.1.absNorm : ℂ) ^ (-(s : ℂ)))) := hsumw.clog_one_sub.neg
  have hsum2 := Chebotarev.summable_prime2_absNorm_rpow K one_lt_two
  rw [congruenceLogSum, congruencePrimeSum, ← hsumlog.tsum_sub hsumw]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) hterm hsum2
  · exact (Summable.of_nonneg_of_le (fun q => norm_nonneg _) hterm hsum2).tsum_le_tsum hterm
      hsum2

/-- The higher prime-power terms form a uniformly bounded remainder near one. -/
theorem log_norm_congruenceLSeries_sub_primeSum_bounded [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      |Real.log ‖congruenceLSeries K m H χ (s : ℂ)‖ -
        (congruencePrimeSum K m H χ s).re| ≤ C := by
  obtain ⟨C, hC⟩ := congruenceLogSum_sub_primeSum_bounded K m H χ
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hsC hs
  rw [Set.mem_Ioi] at hs
  rw [← re_congruenceLogSum_eq_log_norm K m H χ hs, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans hsC

/-- Bounded norm gives the one-sided prime-sum bound required by IV.4.7. -/
theorem congruencePrimeSum_re_le_of_ne_one (hm : m ≠ ⊥)
    (hH : raySubgroup K m ≤ H) [H.FiniteIndex]
    (χ : (coprimeIdeals K m ⧸ H) →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1, (congruencePrimeSum K m H χ s).re ≤ C := by
  obtain ⟨C₁, h₁⟩ := congruenceLSeries_norm_bounded K m H hm hH χ hχ
  obtain ⟨C₂, h₂⟩ := log_norm_congruenceLSeries_sub_primeSum_bounded K m H χ
  refine ⟨max C₁ 1 + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs1 hs2
  have hlog : Real.log ‖congruenceLSeries K m H χ (s : ℂ)‖ ≤ max C₁ 1 := by
    rcases eq_or_lt_of_le (norm_nonneg (congruenceLSeries K m H χ (s : ℂ))) with h0 | hpos
    · rw [← h0, Real.log_zero]
      exact le_max_of_le_right zero_le_one
    · exact (Real.log_le_sub_one_of_pos hpos).trans (by linarith [le_max_left C₁ 1])
  linarith [(abs_le.mp hs2).1]

/-- The principal-character prime sum is bounded above by the unrestricted prime sum. -/
theorem congruencePrimeSum_one_re_le {s : ℝ} (hs : 1 < s) :
    (congruencePrimeSum K m H 1 s).re ≤
      Chebotarev.primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s := by
  have hw1 : ∀ A, ‖congruenceCharacterValue K m H 1 A‖ ≤ 1 := by
    intro A
    unfold congruenceCharacterValue
    split_ifs <;> simp
  have hsum := summable_weighted_primeSum K _ hw1 hs
  rw [congruencePrimeSum, Complex.re_tsum hsum, Chebotarev.primeIdealZetaSum_univ_eq_tsum_prime2 K]
  refine (hsum.mapL Complex.reCLM).tsum_le_tsum (fun q => ?_)
    (Chebotarev.summable_prime2_absNorm_rpow K hs)
  exact (Complex.re_le_norm _).trans (norm_weighted_prime_term_le K _ hw1 q s)

/-- Good prime ideals whose ideal classes belong to the chosen subgroup. -/
def primesInCongruenceSubgroup : Set (Ideal (𝓞 K)) :=
  {q | q.IsPrime ∧ q ∈ integralIdealsInCongruenceClass K m H 1}

/-- Column orthogonality singles out exactly the identity quotient class. -/
theorem index_mul_primeSum_eq_character_sum [H.FiniteIndex] {s : ℝ} (hs : 1 < s) :
    (H.index : ℂ) * (Chebotarev.primeIdealZetaSum (primesInCongruenceSubgroup K m H) s : ℂ) =
      ∑' χ : (coprimeIdeals K m ⧸ H) →* ℂˣ, congruencePrimeSum K m H χ s := by
  classical
  letI : Fintype (coprimeIdeals K m ⧸ H) := Fintype.ofFinite _
  have hcardχ : Nat.card ((coprimeIdeals K m ⧸ H) →* ℂˣ) = Nat.card (coprimeIdeals K m ⧸ H) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ _
  haveI : Finite ((coprimeIdeals K m ⧸ H) →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by rw [hcardχ]; exact Nat.card_pos.ne')
  letI : Fintype ((coprimeIdeals K m ⧸ H) →* ℂˣ) := Fintype.ofFinite _
  let cls : ∀ A : Ideal (𝓞 K), A ≠ ⊥ ∧ A ⊔ m = ⊤ → coprimeIdeals K m ⧸ H := fun A h =>
    QuotientGroup.mk (Classical.choose (exists_coprimeIdealUnit K m A h.1 h.2))
  have hcol : ∀ q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥},
      (∑ χ : (coprimeIdeals K m ⧸ H) →* ℂˣ, congruenceCharacterValue K m H χ q.1) =
        if q.1 ∈ primesInCongruenceSubgroup K m H then
          (Nat.card (coprimeIdeals K m ⧸ H) : ℂ) else 0 := by
    intro q
    by_cases hg : q.1 ≠ ⊥ ∧ q.1 ⊔ m = ⊤
    · have hv : ∀ χ : (coprimeIdeals K m ⧸ H) →* ℂˣ,
          congruenceCharacterValue K m H χ q.1 = (χ (cls q.1 hg) : ℂ) := by
        intro χ
        unfold congruenceCharacterValue
        rw [dif_pos hg]
      simp_rw [hv]
      have hS : q.1 ∈ primesInCongruenceSubgroup K m H ↔ cls q.1 hg = 1 := by
        constructor
        · rintro ⟨-, -, -, u, hu, hu1⟩
          have hrep : Classical.choose (exists_coprimeIdealUnit K m q.1 hg.1 hg.2) = u :=
            Subtype.ext (Units.ext ((Classical.choose_spec
              (exists_coprimeIdealUnit K m q.1 hg.1 hg.2)).trans hu.symm))
          simp only [cls, hrep, hu1]
        · intro h1
          exact ⟨q.2.1, hg.1, hg.2, _,
            Classical.choose_spec (exists_coprimeIdealUnit K m q.1 hg.1 hg.2), h1⟩
      by_cases h1 : cls q.1 hg = 1
      · rw [if_pos (hS.mpr h1), h1]
        simp only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_one]
        rw [Fintype.card_eq_nat_card, hcardχ]
      · rw [if_neg (fun h => h1 (hS.mp h))]
        exact Chebotarev.sum_char_apply_eq_zero_of_ne_one h1
    · have hv : ∀ χ : (coprimeIdeals K m ⧸ H) →* ℂˣ,
          congruenceCharacterValue K m H χ q.1 = 0 := by
        intro χ
        unfold congruenceCharacterValue
        rw [dif_neg hg]
      simp_rw [hv]
      rw [Finset.sum_const_zero, if_neg]
      rintro ⟨-, h0, hm', -⟩
      exact hg ⟨h0, hm'⟩
  have hinterchange : ∑ χ : (coprimeIdeals K m ⧸ H) →* ℂˣ, congruencePrimeSum K m H χ s =
      ∑' q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥},
        (∑ χ : (coprimeIdeals K m ⧸ H) →* ℂˣ, congruenceCharacterValue K m H χ q.1) *
          (q.1.absNorm : ℂ) ^ (-(s : ℂ)) := by
    unfold congruencePrimeSum
    rw [← Summable.tsum_finsetSum (fun χ _ => summable_congruencePrimeSum K m H χ hs)]
    exact tsum_congr fun q => (Finset.sum_mul _ _ _).symm
  have hfreal : ∀ q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥},
      (q.1.absNorm : ℂ) ^ (-(s : ℂ)) = (((q.1.absNorm : ℝ) ^ (-s) : ℝ) : ℂ) := fun q => by
    rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast]
  have hfinj : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) //
          𝔭 ∈ primesInCongruenceSubgroup K m H ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
        (⟨𝔭.1, 𝔭.2.2⟩ : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥})) :=
    fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab)
  have hfibre : Chebotarev.primeIdealZetaSum (primesInCongruenceSubgroup K m H) s =
      ∑' q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥},
        (if q.1 ∈ primesInCongruenceSubgroup K m H then (q.1.absNorm : ℝ) ^ (-s) else 0) := by
    rw [Chebotarev.primeIdealZetaSum_def, ← hfinj.tsum_eq
      (f := fun q : {q : Ideal (𝓞 K) // q.IsPrime ∧ q ≠ ⊥} =>
        if q.1 ∈ primesInCongruenceSubgroup K m H then (q.1.absNorm : ℝ) ^ (-s) else 0) ?_]
    · exact tsum_congr fun 𝔭 => (if_pos 𝔭.2.1).symm
    · rintro q hq
      have h : q.1 ∈ primesInCongruenceSubgroup K m H := by
        by_contra hne
        exact hq (if_neg hne)
      exact ⟨⟨q.1, h, q.2⟩, rfl⟩
  rw [tsum_fintype, hinterchange, hfibre, Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [hcol q]
  split_ifs with h
  · rw [hfreal q]
    rfl
  · simp

/-- The finite character sum yields h times the subgroup prime sum at most log(1/(s-1))+O(1). -/
theorem index_mul_primeSum_le_log_add (hm : m ≠ ⊥)
    (hH : raySubgroup K m ≤ H) [H.FiniteIndex] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      (H.index : ℝ) * Chebotarev.primeIdealZetaSum (primesInCongruenceSubgroup K m H) s ≤
        Real.log (1 / (s - 1)) + C := by
  classical
  letI : Fintype (coprimeIdeals K m ⧸ H) := Fintype.ofFinite _
  have hcardχ : Nat.card ((coprimeIdeals K m ⧸ H) →* ℂˣ) = Nat.card (coprimeIdeals K m ⧸ H) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ _
  haveI : Finite ((coprimeIdeals K m ⧸ H) →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by rw [hcardχ]; exact Nat.card_pos.ne')
  letI : Fintype ((coprimeIdeals K m ⧸ H) →* ℂˣ) := Fintype.ofFinite _
  have hb : ∀ χ : (coprimeIdeals K m ⧸ H) →* ℂˣ, ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      χ ≠ 1 → (congruencePrimeSum K m H χ s).re ≤ C := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨0, Eventually.of_forall fun s h => absurd hχ h⟩
    · obtain ⟨C, hC⟩ := congruencePrimeSum_re_le_of_ne_one K m H hm hH χ hχ
      exact ⟨C, hC.mono fun s hs _ => hs⟩
  choose Cχ hCχ using hb
  obtain ⟨C₀, hC₀⟩ := Chebotarev.primeIdealZetaSum_le_log_plus_bounded K
  refine ⟨C₀ + ∑ χ ∈ Finset.univ.erase (1 : (coprimeIdeals K m ⧸ H) →* ℂˣ), Cχ χ, ?_⟩
  have hall : ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ χ : (coprimeIdeals K m ⧸ H) →* ℂˣ,
      χ ≠ 1 → (congruencePrimeSum K m H χ s).re ≤ Cχ χ := Filter.eventually_all.mpr hCχ
  filter_upwards [hall, hC₀, self_mem_nhdsWithin] with s hs hs0 hs1
  rw [Set.mem_Ioi] at hs1
  have heq := index_mul_primeSum_eq_character_sum K m H hs1
  rw [tsum_fintype, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1)] at heq
  have hre := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum] at hre
  rw [hre]
  have h1 := congruencePrimeSum_one_re_le K m H hs1
  have h2 : ∑ χ ∈ Finset.univ.erase (1 : (coprimeIdeals K m ⧸ H) →* ℂˣ),
      (congruencePrimeSum K m H χ s).re ≤
        ∑ χ ∈ Finset.univ.erase (1 : (coprimeIdeals K m ⧸ H) →* ℂˣ), Cχ χ :=
    Finset.sum_le_sum fun χ hχ => hs χ (Finset.ne_of_mem_erase hχ)
  linarith

/-- Divide an actual one-sided prime-sum bound by the divergent logarithm and take limits. -/
theorem density_mul_le_one_of_log_bound {S : Set (Ideal (𝓞 K))} {δ h : ℝ}
    (hdensity : Chebotarev.HasDirichletDensity S δ)
    (hbound : ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      h * Chebotarev.primeIdealZetaSum S s ≤ Real.log (1 / (s - 1)) + C) :
    h * δ ≤ 1 := by
  obtain ⟨C, hC⟩ := hbound
  have hlog := Chebotarev.tendsto_log_one_div_sub_one_atTop
  have hratio := Chebotarev.primeIdealZetaSum_univ_tendsto_log K
  have hPpos := (Chebotarev.primeIdealZetaSum_univ_tendsto_atTop K).eventually_gt_atTop 0
  have hlim1 : Tendsto (fun s : ℝ => h * (Chebotarev.primeIdealZetaSum S s /
      Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) *
      (Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s / Real.log (1 / (s - 1))))
      (𝓝[>] 1) (𝓝 (h * δ * 1)) :=
    (hdensity.const_mul h).mul hratio
  have hlim2 : Tendsto (fun s : ℝ => 1 + C / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hlog)
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 1, h * (Chebotarev.primeIdealZetaSum S s /
      Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) *
      (Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s / Real.log (1 / (s - 1))) ≤
      1 + C / Real.log (1 / (s - 1)) := by
    filter_upwards [hC, hlog.eventually_gt_atTop 0, hPpos] with s hs hpos hP
    have heq : h * (Chebotarev.primeIdealZetaSum S s /
        Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) *
        (Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s / Real.log (1 / (s - 1))) =
        h * Chebotarev.primeIdealZetaSum S s / Real.log (1 / (s - 1)) := by
      field_simp
    rw [heq, div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
    linarith
  simpa using le_of_tendsto_of_tendsto hlim1 hlim2 hle

/-- Janusz IV.4.7: any prime subset of a congruence subgroup has density at most 1/h. -/
theorem density_le_inv_index_of_subset_congruence (hm : m ≠ ⊥)
    (hH : raySubgroup K m ≤ H) [H.FiniteIndex]
    {S : Set (Ideal (𝓞 K))} {δ : ℝ}
    (hS : S ⊆ primesInCongruenceSubgroup K m H)
    (hdensity : Chebotarev.HasDirichletDensity S δ) : δ ≤ 1 / (H.index : ℝ) := by
  obtain ⟨C, hC⟩ := index_mul_primeSum_le_log_add K m H hm hH
  have hbound : ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      (H.index : ℝ) * Chebotarev.primeIdealZetaSum S s ≤ Real.log (1 / (s - 1)) + C := by
    refine ⟨C, ?_⟩
    filter_upwards [hC, self_mem_nhdsWithin] with s hs hs1
    refine le_trans ?_ hs
    exact mul_le_mul_of_nonneg_left (Chebotarev.primeIdealZetaSum_le_of_subset K hS hs1)
      (Nat.cast_nonneg _)
  have h := density_mul_le_one_of_log_bound K hdensity hbound
  have hpos : (0 : ℝ) < H.index := by
    exact_mod_cast Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  rw [le_div_iff₀ hpos, mul_comm]
  exact h

end Cox.ClassFieldTheory
