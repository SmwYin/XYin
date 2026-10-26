/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldPowerSeries
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-! # Convergent evaluation of Janusz's formal identities

Geometric coefficient bounds make the required double series unconditionally
summable. Formal equality alone is not used as a convergence theorem.
-/

open Filter
open scoped Topology

noncomputable section

namespace Cox.ClassFieldConvergentSeries

section Semiring

variable {R : Type*} [Semiring R]

/-- Actual evaluated monomials, with no assumed domain of convergence. -/
def term (f : PowerSeries R) (x : R) (n : ℕ) : R := f.coeff n * x ^ n

/-- The double family behind substituting g into f, indexed by outer power and degree. -/
def compositionTerm (f g : PowerSeries R) (x : R) (i : ℕ × ℕ) : R :=
  f.coeff i.1 * (g ^ i.1).coeff i.2 * x ^ i.2

/-- A zero-constant inner series has no coefficient below its power. -/
theorem coeff_pow_eq_zero_of_lt (g : PowerSeries R) (hg₀ : g.constantCoeff = 0)
    (n k : ℕ) (hkn : k < n) : (g ^ n).coeff k = 0 := by
  apply PowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hkn)
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero n hg₀)

/-- Substitution terms vanish outside the triangular support n≤k. -/
theorem compositionTerm_eq_zero_of_lt (f g : PowerSeries R)
    (hg₀ : g.constantCoeff = 0) (x : R) (n k : ℕ) (hkn : k < n) :
    compositionTerm f g x (n, k) = 0 := by
  simp [compositionTerm, coeff_pow_eq_zero_of_lt g hg₀ n k hkn]

end Semiring

variable {F : Type*} [NormedField F] [hUltra : IsUltrametricDist F] [hComplete : CompleteSpace F]

/-- The total sum of the evaluated monomials; geometric-radius lemmas establish convergence. -/
def value (f : PowerSeries F) (x : F) : F := ∑' n, term f x n

include hUltra hComplete

omit hComplete in
/-- The ultrametric inequality preserves a geometric coefficient bound under multiplication. -/
theorem coeff_mul_norm_le (f g : PowerSeries F) (C : ℝ)
    (hf : ∀ n, ‖f.coeff n‖ ≤ C ^ n) (hg : ∀ n, ‖g.coeff n‖ ≤ C ^ n)
    (k : ℕ) : ‖(f * g).coeff k‖ ≤ C ^ k := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hf 1)
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hC k) fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [norm_mul, ← hp, pow_add]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) (pow_nonneg hC _)

omit hComplete in
/-- Finite powers have the same geometric coefficient bound. -/
theorem coeff_pow_norm_le (g : PowerSeries F) (C : ℝ)
    (hg : ∀ n, ‖g.coeff n‖ ≤ C ^ n) (n k : ℕ) :
    ‖(g ^ n).coeff k‖ ≤ C ^ k := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hg 1)
  induction n generalizing k with
  | zero =>
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs with h
    · subst h; simp
    · simpa using pow_nonneg hC k
  | succ n ih =>
    rw [pow_succ]
    exact coeff_mul_norm_le _ _ C ih hg k

omit hUltra hComplete in
/-- Geometric coefficient bounds give a geometric bound on the evaluated terms. -/
theorem term_norm_le (f : PowerSeries F) (C : ℝ)
    (hf : ∀ n, ‖f.coeff n‖ ≤ C ^ n) (x : F) (n : ℕ) :
    ‖term f x n‖ ≤ (C * ‖x‖) ^ n := by
  rw [term, norm_mul, norm_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right (hf n) (pow_nonneg (norm_nonneg _) _)

omit hUltra hComplete in
/-- The real norms of the terms are dominated by a convergent geometric series. -/
theorem summable_norm_term (f : PowerSeries F) (C : ℝ)
    (hf : ∀ n, ‖f.coeff n‖ ≤ C ^ n) (x : F) (hx : C * ‖x‖ < 1) :
    Summable (fun n ↦ ‖term f x n‖) := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hf 1)
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (term_norm_le f C hf x)
    (summable_geometric_of_lt_one (mul_nonneg hC (norm_nonneg _)) hx)

omit hUltra in
/-- A bounded-coefficient series converges strictly inside its geometric radius. -/
theorem summable_term (f : PowerSeries F) (C : ℝ)
    (hf : ∀ n, ‖f.coeff n‖ ≤ C ^ n) (x : F) (hx : C * ‖x‖ < 1) :
    Summable (term f x) := by
  exact (summable_norm_term f C hf x hx).of_norm

omit hComplete in
/-- The sum of a zero-constant series lies in the closed geometric bound on its input. -/
theorem value_norm_le (g : PowerSeries F) (C : ℝ)
    (hg : ∀ n, ‖g.coeff n‖ ≤ C ^ n) (hg₀ : g.constantCoeff = 0)
    (x : F) (hx : C * ‖x‖ ≤ 1) : ‖value g x‖ ≤ C * ‖x‖ := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hg 1)
  have hCx : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hCx fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : term g x 0 = 0 := by
      simp [term, PowerSeries.coeff_zero_eq_constantCoeff_apply, hg₀]
    rw [h0, norm_zero]
    exact hCx
  · exact (term_norm_le g C hg x n).trans (pow_le_of_le_one hCx hx hn.ne')

omit hComplete in
/-- On triangular support the double family is bounded by a geometric function of degree. -/
theorem compositionTerm_norm_le (f g : PowerSeries F) (C : ℝ) (hC : 1 ≤ C)
    (hf : ∀ n, ‖f.coeff n‖ ≤ C ^ n) (hg : ∀ n, ‖g.coeff n‖ ≤ C ^ n)
    (x : F) (n k : ℕ) (hnk : n ≤ k) :
    ‖compositionTerm f g x (n, k)‖ ≤ (C ^ 2 * ‖x‖) ^ k := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  rw [compositionTerm, norm_mul, norm_mul, norm_pow]
  calc ‖f.coeff n‖ * ‖(g ^ n).coeff k‖ * ‖x‖ ^ k ≤ C ^ k * C ^ k * ‖x‖ ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul ((hf n).trans (pow_le_pow_right₀ hC hnk))
          (coeff_pow_norm_le g C hg n k) (norm_nonneg _) (pow_nonneg hC0 k))
          (pow_nonneg (norm_nonneg _) k)
    _ = (C ^ 2 * ‖x‖) ^ k := by ring

/-- The triangular support and degree bound imply unconditional double summability. -/
theorem summable_compositionTerm (f g : PowerSeries F) (C : ℝ) (hC : 1 ≤ C)
    (hf : ∀ n, ‖f.coeff n‖ ≤ C ^ n) (hg : ∀ n, ‖g.coeff n‖ ≤ C ^ n)
    (hg₀ : g.constantCoeff = 0) (x : F) (hx : C ^ 2 * ‖x‖ < 1) :
    Summable (compositionTerm f g x) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hq0 : 0 ≤ C ^ 2 * ‖x‖ := mul_nonneg (pow_nonneg hC0 2) (norm_nonneg _)
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hx
  rw [Filter.eventually_cofinite]
  refine ((Finset.range N ×ˢ Finset.range N : Finset (ℕ × ℕ)).finite_toSet).subset ?_
  rintro ⟨n, k⟩ hnk
  simp only [Set.mem_setOf_eq, not_lt] at hnk
  rcases lt_or_ge k n with hkn | hkn
  · rw [compositionTerm_eq_zero_of_lt f g hg₀ x n k hkn, norm_zero] at hnk
    exact absurd hε (not_lt.mpr hnk)
  · have hk : k < N := by
      by_contra hk
      rw [not_lt] at hk
      have := (compositionTerm_norm_le f g C hC hf hg x n k hkn).trans
        (pow_le_pow_of_le_one hq0 hx.le hk)
      linarith
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
    omega

omit hUltra in
/-- Evaluation of a product follows from its unconditionally summable Cauchy product. -/
theorem value_mul (f g : PowerSeries F) (C : ℝ)
    (hf : ∀ n, ‖f.coeff n‖ ≤ C ^ n) (hg : ∀ n, ‖g.coeff n‖ ≤ C ^ n)
    (x : F) (hx : C * ‖x‖ < 1) :
    value (f * g) x = value f x * value g x := by
  unfold value
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_term f C hf x hx)
    (summable_norm_term g C hg x hx)]
  refine tsum_congr fun n => ?_
  rw [term, PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [term, term, ← hp, pow_add]
  ring

/-- The product evaluation identity iterates over any natural power. -/
theorem value_pow (g : PowerSeries F) (C : ℝ)
    (hg : ∀ n, ‖g.coeff n‖ ≤ C ^ n) (x : F) (hx : C * ‖x‖ < 1) (n : ℕ) :
    value (g ^ n) x = value g x ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, value, tsum_eq_single 0]
    · simp [term]
    · intro m hm
      simp [term, PowerSeries.coeff_one, hm]
  | succ n ih =>
    rw [pow_succ, pow_succ, value_mul (g ^ n) g C (coeff_pow_norm_le g C hg n) hg x hx, ih]

/-- Summing the double family in either order justifies convergent formal substitution. -/
theorem value_subst (f g : PowerSeries F) (C : ℝ) (hC : 1 ≤ C)
    (hf : ∀ n, ‖f.coeff n‖ ≤ C ^ n) (hg : ∀ n, ‖g.coeff n‖ ≤ C ^ n)
    (hg₀ : g.constantCoeff = 0) (x : F) (hx : C ^ 2 * ‖x‖ < 1) :
    value (f.subst g) x = value f (value g x) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCC : C ≤ C ^ 2 := by nlinarith
  have hxC : C * ‖x‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hCC (norm_nonneg _)) hx
  have hsum : Summable (Function.uncurry fun n k => compositionTerm f g x (n, k)) :=
    summable_compositionTerm f g C hC hf hg hg₀ x hx
  have hrow : ∀ n, ∑' k, compositionTerm f g x (n, k) = term f (value g x) n := by
    intro n
    have h : ∀ k, compositionTerm f g x (n, k) = f.coeff n * term (g ^ n) x k := fun k => by
      simp only [compositionTerm, term]
      ring
    rw [tsum_congr h, tsum_mul_left]
    change _ = f.coeff n * value g x ^ n
    rw [← value_pow g C hg x hxC n]
    rfl
  have hcol : ∀ k, ∑' n, compositionTerm f g x (n, k) = term (f.subst g) x k := by
    intro k
    have hsupp : Function.support (fun n => f.coeff n * (g ^ n).coeff k) ⊆
        ↑(Finset.range (k + 1)) := by
      intro n hn
      rw [Function.mem_support] at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h
      exact hn (by rw [coeff_pow_eq_zero_of_lt g hg₀ n k (by omega), mul_zero])
    simp only [compositionTerm]
    rw [tsum_mul_right, term,
      PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hg₀),
      tsum_eq_sum' hsupp,
      finsum_eq_sum_of_support_subset _ (by simpa only [smul_eq_mul] using hsupp)]
    simp only [smul_eq_mul]
  calc value (f.subst g) x = ∑' k, ∑' n, compositionTerm f g x (n, k) :=
        tsum_congr fun k => (hcol k).symm
    _ = ∑' n, ∑' k, compositionTerm f g x (n, k) := hsum.tsum_comm
    _ = value f (value g x) := tsum_congr hrow

end Cox.ClassFieldConvergentSeries
