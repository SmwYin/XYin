/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevEulerProduct
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Dirichlet-density analysis

Source AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87` is not an imported dependency.
Contracts are adapted to pinned Lean 4.30.0. Local prerequisites precede their consumers. See the
declaration records for exact source matches and remaining port boundaries.
-/

noncomputable section
open Filter NumberField Topology Set UniqueFactorizationMonoid
namespace Cox.Chebotarev
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]
variable {S : Set (Ideal (𝓞 K))} {δ : ℝ}

/-- Planning source: Density.lean:55; statement placeholder. -/
theorem primeIdealZetaSum_def (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    primeIdealZetaSum S s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := rfl

/-- Planning source: Density.lean:120; statement placeholder. -/
theorem primeIdealZetaSum_nonneg (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    0 ≤ primeIdealZetaSum S s :=
  tsum_nonneg fun _ ↦ by positivity

/-- Planning source: Density.lean:285; statement placeholder. -/
theorem two_le_absNorm_of_prime {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) :
    (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) :=
  mod_cast (Nat.two_le_iff _).2
    ⟨mt Ideal.absNorm_eq_zero_iff.1 hne, mt Ideal.absNorm_eq_one_iff.1 hp.ne_top⟩

/-- Planning source: Density.lean:297; statement placeholder. -/
theorem primeIdealHigherTail_term_le {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥)
    {s : ℝ} (hs : 1 < s) :
    (Ideal.absNorm 𝔭 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s)) ≤
      2 * (Ideal.absNorm 𝔭 : ℝ) ^ (-(2 : ℝ)) := by
  set x : ℝ := (Ideal.absNorm 𝔭 : ℝ)
  have hx : (2 : ℝ) ≤ x := two_le_absNorm_of_prime K hp hne
  have hxs_half : x ^ (-s) ≤ 1 / 2 :=
    calc x ^ (-s) ≤ (2 : ℝ) ^ (-s) := Real.rpow_le_rpow_of_nonpos zero_lt_two hx (by linarith)
      _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hden_pos : (0 : ℝ) < 1 - x ^ (-s) := by linarith
  have hinv_le : (1 - x ^ (-s))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden_pos (by norm_num)]; linarith
  have hexp : x ^ (-(2 : ℝ) * s) ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
  rw [div_eq_mul_inv, mul_comm]
  exact mul_le_mul hinv_le hexp (by positivity) (by positivity)

/-- Planning source: Density.lean:291; statement placeholder. -/
theorem absNorm_rpow_neg_lt_one {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) {s : ℝ}
    (hs : 1 < s) : (Ideal.absNorm 𝔭 : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by linarith [two_le_absNorm_of_prime K hp hne]) (by linarith)

/-- Planning source: Density.lean:103; statement placeholder. -/
theorem summable_nonzeroIdeal_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) :=
  ((hasSum_nonzeroIdeal_absNorm_cpow K (s := (s : ℂ)) (by simpa using hs)).summable.norm).congr
    fun I ↦ (Complex.norm_natCast_cpow_of_pos
      (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp

/-- Planning source: Density.lean:111; statement placeholder. -/
theorem summable_prime_absNorm_rpow (S : Set (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
  ((summable_nonzeroIdeal_absNorm_rpow K hs).comp_injective
    (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal K))
    fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl

/-- Planning source: Density.lean:278; statement placeholder. -/
theorem summable_prime2_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
  ((summable_prime_absNorm_rpow K (univ : Set (Ideal (𝓞 K))) hs).comp_injective
    (Equiv.subtypeEquivRight fun _ ↦ ⟨(⟨mem_univ _, ·⟩), And.right⟩).injective).congr fun _ ↦ rfl

/-- Planning source: Density.lean:319; statement placeholder. -/
theorem primeIdealZetaHigherTail_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤ C := by
  refine ⟨2 * ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [mem_Ioi] at hs
  have hbound : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤
        2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)) := fun 𝔭 ↦
    primeIdealHigherTail_term_le K 𝔭.2.1 𝔭.2.2 hs
  have hnonneg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
    fun 𝔭 ↦ div_nonneg (Real.rpow_nonneg (by positivity) _)
      (by have := absNorm_rpow_neg_lt_one K 𝔭.2.1 𝔭.2.2 hs; linarith)
  have hsummable_rhs : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ))) :=
    (summable_prime2_absNorm_rpow K one_lt_two).mul_left 2
  exact ((Summable.of_nonneg_of_le hnonneg hbound hsummable_rhs).tsum_le_tsum hbound
    hsummable_rhs).trans_eq tsum_mul_left

/-- Planning source: Density.lean:354, lower bound; statement placeholder. -/
theorem neg_log_one_sub_sub_nonneg {x : ℝ} (hx1 : x < 1) :
    0 ≤ - Real.log (1 - x) - x := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - x by linarith)
  linarith

/-- Planning source: Density.lean:354, upper bound; statement placeholder. -/
theorem neg_log_one_sub_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    - Real.log (1 - x) - x ≤ x ^ 2 / (1 - x) := by
  have habs : |x| < 1 := by rwa [abs_of_nonneg hx0]
  have key := Real.abs_log_sub_add_sum_range_le habs 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one,
    abs_of_nonneg hx0] at key
  linarith [(abs_le.mp key).1]

/-- Planning source: Density.lean:349; statement placeholder. -/
theorem one_sub_absNorm_rpow_pos {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥)
    {s : ℝ} (hs : 1 < s) : (0 : ℝ) < 1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s) :=
  sub_pos.mpr (absNorm_rpow_neg_lt_one K hp hne hs)

/-- Planning source: Density.lean:396; statement placeholder. -/
theorem abs_tsum_neg_log_one_sub_sub_rpow_le :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
      |∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (- Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))
          - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))| ≤ C := by
  obtain ⟨C, hC⟩ := primeIdealZetaHigherTail_bounded K
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hs_tail hs1
  simp only [mem_Ioi] at hs1
  set f : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℝ :=
    fun 𝔭 ↦ - Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
  set h : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℝ :=
    fun 𝔭 ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) with hh
  have hxbound : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) < 1 := fun 𝔭 ↦ absNorm_rpow_neg_lt_one K 𝔭.2.1 𝔭.2.2 hs1
  have hxnn : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun 𝔭 ↦ Real.rpow_nonneg (by positivity) _
  have hfnn : ∀ 𝔭, 0 ≤ f 𝔭 := fun 𝔭 ↦ neg_log_one_sub_sub_nonneg (hxbound 𝔭)
  have hfle : ∀ 𝔭, f 𝔭 ≤ h 𝔭 := fun 𝔭 ↦ by
    refine (neg_log_one_sub_sub_le (hxnn 𝔭) (hxbound 𝔭)).trans_eq ?_
    rw [hh]
    congr 1
    rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
    ring_nf
  have hsummh : Summable h :=
    Summable.of_nonneg_of_le
      (fun 𝔭 ↦ div_nonneg (Real.rpow_nonneg (by positivity) _)
        (one_sub_absNorm_rpow_pos K 𝔭.2.1 𝔭.2.2 hs1).le)
      (fun 𝔭 ↦ primeIdealHigherTail_term_le K 𝔭.2.1 𝔭.2.2 hs1)
      ((summable_prime2_absNorm_rpow K one_lt_two).mul_left 2)
  have hsummf : Summable f := Summable.of_nonneg_of_le hfnn hfle hsummh
  rw [abs_of_nonneg (tsum_nonneg hfnn)]
  exact (hsummf.tsum_le_tsum hfle hsummh).trans hs_tail

/-- Planning source: Density.lean:364; statement placeholder. -/
theorem summable_neg_log_one_sub_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      - Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))) :=
  ((Real.summable_log_one_add_of_summable
    (summable_prime2_absNorm_rpow K hs).neg).neg).congr fun _ ↦ rfl

/-- Planning source: Density.lean:371; statement placeholder. -/
theorem log_dedekindZeta_re_eq_tsum_neg_log_one_sub {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K (s : ℂ)).re =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (- Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))) := by
  set g : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℝ :=
    fun 𝔭 ↦ (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))⁻¹ with hg
  have hgpos : ∀ 𝔭, 0 < g 𝔭 :=
    fun 𝔭 ↦ inv_pos.mpr (one_sub_absNorm_rpow_pos K 𝔭.2.1 𝔭.2.2 hs)
  have hlogsum : Summable (fun 𝔭 ↦ Real.log (g 𝔭)) :=
    (summable_neg_log_one_sub_absNorm_rpow K hs).congr fun 𝔭 ↦ by rw [hg, Real.log_inv]
  have hCprod : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))⁻¹)
      ((Real.exp (∑' 𝔭, Real.log (g 𝔭)) : ℝ) : ℂ) := by
    refine ((Real.hasProd_of_hasSum_log hgpos hlogsum.hasSum).map Complex.ofRealHom
      Complex.continuous_ofReal).congr_fun fun 𝔭 ↦ ?_
    rw [Function.comp_apply, Complex.ofRealHom_eq_coe, hg]
    push_cast [Complex.ofReal_cpow (show (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) by positivity)]
    ring
  have hre : (dedekindZeta K (s : ℂ)).re = Real.exp (∑' 𝔭, Real.log (g 𝔭)) := by
    rw [dedekindZeta_eq_tprod_primeIdeal K (by simpa using hs), hCprod.tprod_eq,
      Complex.ofReal_re]
  rw [hre, Real.log_exp]
  exact tsum_congr fun 𝔭 ↦ by rw [hg, Real.log_inv]

/-- Planning source: Density.lean:341; statement placeholder. -/
theorem primeIdealZetaSum_univ_eq_tsum_prime2 (s : ℝ) :
    primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := by
  rw [primeIdealZetaSum_def K, ← (Equiv.subtypeEquivRight fun 𝔭 ↦
    ⟨fun h ↦ ⟨mem_univ _, h⟩, And.right⟩).tsum_eq _]
  rfl

/-- Planning source: Density.lean:432; statement placeholder. -/
theorem logDedekindZeta_sub_primeIdealZetaSum_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ), |Real.log (dedekindZeta K (s : ℂ)).re
      - primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s| ≤ C := by
  obtain ⟨C, hC⟩ := abs_tsum_neg_log_one_sub_sub_rpow_le K
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hs_bound hs1
  simp only [mem_Ioi] at hs1
  rwa [log_dedekindZeta_re_eq_tsum_neg_log_one_sub K hs1,
    primeIdealZetaSum_univ_eq_tsum_prime2 K s,
    ← (summable_neg_log_one_sub_absNorm_rpow K hs1).tsum_sub
      (summable_prime2_absNorm_rpow K hs1)]

/-- Planning source: Density.lean:447; statement placeholder. -/
theorem logDedekindZeta_sub_log_inv_sub_one_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
      |Real.log (dedekindZeta K (s : ℂ)).re - Real.log (1 / (s - 1))| ≤ C := by
  set r := dedekindZeta_residue K
  have hrpos : 0 < r := dedekindZeta_residue_pos K
  have hF : Tendsto (fun s : ℝ ↦ (s - 1) * (dedekindZeta K (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 r) := by
    refine ((Complex.continuous_re.tendsto _).comp
      (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)).congr fun s ↦ ?_
    rw [Function.comp_apply, show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  refine ⟨max |Real.log (r / 2)| |Real.log (2 * r)|, ?_⟩
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      (s - 1) * (dedekindZeta K (s : ℂ)).re ∈ Ioo (r / 2) (2 * r) :=
    hF.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hev, self_mem_nhdsWithin] with s hF_s hs1
  simp only [mem_Ioi] at hs1
  have hsm1 : (0 : ℝ) < s - 1 := by linarith
  obtain ⟨hlo, hhi⟩ := hF_s
  have hFpos : (0 : ℝ) < (s - 1) * (dedekindZeta K (s : ℂ)).re := by linarith
  have hζpos : (0 : ℝ) < (dedekindZeta K (s : ℂ)).re := (mul_pos_iff_of_pos_left hsm1).mp hFpos
  rw [one_div, Real.log_inv, sub_neg_eq_add,
    ← Real.log_mul hζpos.ne' hsm1.ne', mul_comm]
  exact abs_le_max_abs_abs (Real.log_lt_log (by linarith) hlo).le (Real.log_lt_log hFpos hhi).le

/-- Planning source: Density.lean:473–495; statement placeholder. -/
theorem log_minus_bounded_le_primeIdealZetaSum :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      Real.log (1 / (s - 1)) - C
        ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

/-- Planning source: Density.lean:473–495; statement placeholder. -/
theorem primeIdealZetaSum_le_log_plus_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
        ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

/-- Planning source: ForMathlib/LogOneDivSubOne.lean:43; statement placeholder. -/
theorem tendsto_log_one_div_sub_one_atTop :
    Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
  refine Real.tendsto_log_atTop.comp ?_
  have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by
        simp only [Set.mem_Ioi] at hs ⊢
        linarith)
  simpa only [one_div] using h1.inv_tendsto_nhdsGT_zero

/-- Planning source: ForMathlib/LogOneDivSubOne.lean:59; statement placeholder. -/
theorem tendsto_ratio_one_of_div_atTop_pm_bounded
    {l : Filter ℝ} {g f : ℝ → ℝ} (hg : Tendsto g l atTop)
    (h_le : ∃ C : ℝ, ∀ᶠ s in l, f s ≤ g s + C)
    (h_lower : ∃ C : ℝ, ∀ᶠ s in l, g s - C ≤ f s) :
    Tendsto (fun s : ℝ ↦ f s / g s) l (𝓝 1) := by
  obtain ⟨C₁, hle⟩ := h_le
  obtain ⟨C₂, hlower⟩ := h_lower
  have h0 : Tendsto (fun s ↦ (f s - g s) / g s) l (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (b := -C₂) (B := C₁)
      (hlower.mono fun s h ↦ by linarith) (hle.mono fun s h ↦ by linarith) hg
  refine (add_zero (1 : ℝ) ▸ h0.const_add 1).congr' ?_
  filter_upwards [hg.eventually_gt_atTop 0] with s h
  rw [add_div_eq_mul_add_div _ _ h.ne', one_mul, add_sub_cancel]

/-- Planning source: ForMathlib/LogOneDivSubOne.lean:78; statement placeholder. -/
theorem tendsto_ratio_one_of_log_pm_bounded (f : ℝ → ℝ)
    (h_le : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), f s ≤ Real.log (1 / (s - 1)) + C)
    (h_lower : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), Real.log (1 / (s - 1)) - C ≤ f s) :
    Tendsto (fun s : ℝ ↦ f s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_div_atTop_pm_bounded tendsto_log_one_div_sub_one_atTop h_le h_lower

/-- Planning source: Density.lean:499; statement placeholder. -/
theorem primeIdealZetaSum_univ_tendsto_log :
    Tendsto
      (fun s : ℝ ↦ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
        / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_log_pm_bounded _
    (primeIdealZetaSum_le_log_plus_bounded K)
    (log_minus_bounded_le_primeIdealZetaSum K)

/-- Planning source: Density.lean:510; statement placeholder. -/
theorem primeIdealZetaSum_univ_tendsto_atTop :
    Tendsto (primeIdealZetaSum (univ : Set (Ideal (𝓞 K)))) (𝓝[>] 1) atTop := by
  have hL := tendsto_log_one_div_sub_one_atTop
  have hhalf : Tendsto (fun s : ℝ ↦ (1 / 2 : ℝ) * Real.log (1 / (s - 1))) (𝓝[>] 1) atTop :=
    hL.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hhalf
  filter_upwards [(primeIdealZetaSum_univ_tendsto_log K).eventually
      (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)), hL.eventually_gt_atTop 0] with s hs hpos
  exact ((lt_div_iff₀ hpos).mp hs).le

/-- Planning source: Density.lean:523; statement placeholder. -/
theorem primeIdealZetaSum_le_card_of_finite (hS : S.Finite)
    {s : ℝ} (hs : 0 < s) :
    primeIdealZetaSum S s ≤
      Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := by
  have : Finite {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    (hS.subset fun _ hx ↦ hx.1).to_subtype
  have : Fintype {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := Fintype.ofFinite _
  rw [primeIdealZetaSum_def K, tsum_fintype, Nat.card_eq_fintype_card]
  calc ∑ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
      ≤ ∑ _𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (1 : ℝ) := by
        refine Finset.sum_le_sum fun 𝔭 _ ↦ Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔭.2.2.2)
    _ = (Fintype.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} : ℝ) := by simp

/-- Planning source: Density.lean:544; statement placeholder. -/
theorem tendsto_primeIdealZetaSum_div_univ_zero_of_le_const (U : Set (Ideal (𝓞 K))) (C : ℝ)
    (hbd : ∀ᶠ s in 𝓝[>] (1 : ℝ), primeIdealZetaSum U s ≤ C) :
    Tendsto (fun s : ℝ ↦ primeIdealZetaSum U s
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) (𝓝[>] 1) (𝓝 0) := by
  have hUniv := primeIdealZetaSum_univ_tendsto_atTop K
  have hUnivPos : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s :=
    hUniv.eventually_gt_atTop 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ ↦ 0)
    (h := fun s ↦ C / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    tendsto_const_nhds (tendsto_const_nhds.div_atTop hUniv) ?_ ?_
  · filter_upwards [hUnivPos] with s hpos
    exact div_nonneg (primeIdealZetaSum_nonneg K U s) hpos.le
  · filter_upwards [hUnivPos, hbd] with s hpos hle
    exact div_le_div_of_nonneg_right hle hpos.le

/-- Planning source: Density.lean:562; statement placeholder. -/
theorem hasDirichletDensity_of_finite (hS : S.Finite) :
    HasDirichletDensity S 0 :=
  tendsto_primeIdealZetaSum_div_univ_zero_of_le_const K S _
    (eventually_nhdsWithin_of_forall fun _ hs ↦
      primeIdealZetaSum_le_card_of_finite K hS (zero_lt_one.trans hs))

/-- Planning source: Density.lean:148; statement placeholder. -/
theorem primeIdealZetaSum_union_of_disjoint {T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T) {s : ℝ}
    (hs : 1 < s) :
    primeIdealZetaSum (S ∪ T) s = primeIdealZetaSum S s + primeIdealZetaSum T s := by
  let eS : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S} :=
    { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inl 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
      invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2.2.1, x.1.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let eT : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S}ᶜ :=
    { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inr 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩,
        fun h ↦ hDisj.le_bot ⟨h, 𝔭.2.1⟩⟩
      invFun := fun x ↦ ⟨x.1.1, x.1.2.1.resolve_left x.2, x.1.2.2.1, x.1.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [primeIdealZetaSum_def K, primeIdealZetaSum_def K, primeIdealZetaSum_def K,
    ← (summable_prime_absNorm_rpow K (S ∪ T) hs).tsum_subtype_add_tsum_subtype_compl
      {x | (x.1 : Ideal (𝓞 K)) ∈ S},
    ← eS.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)),
    ← eT.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
  rfl

/-- Planning source: Density.lean:194; statement placeholder. -/
theorem primeIdealZetaSum_eq_univ_of_forall_prime_mem
    (hS : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ S) (s : ℝ) :
    primeIdealZetaSum S s = primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  let e : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (univ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    Equiv.subtypeEquivRight fun 𝔭 ↦
      ⟨fun h ↦ ⟨mem_univ _, h.2⟩, fun h ↦ ⟨hS 𝔭 h.2.1 h.2.2, h.2⟩⟩
  rw [primeIdealZetaSum_def K, primeIdealZetaSum_def K,
    ← e.tsum_eq (fun 𝔭 ↦ (Ideal.absNorm (𝔭.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
  rfl

/-- Planning source: Density.lean:137; statement placeholder. -/
theorem primeIdealZetaSum_le_of_subset {T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum S s ≤ primeIdealZetaSum T s := by
  rw [primeIdealZetaSum_def K, primeIdealZetaSum_def K]
  refine (summable_prime_absNorm_rpow K S hs).tsum_le_tsum_of_inj
    (fun 𝔭 ↦ ⟨𝔭.1, hST 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩)
    (fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))
    (fun c _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ ↦ le_rfl) (summable_prime_absNorm_rpow K T hs)

/-- Planning source: Density.lean:95; statement placeholder. -/
theorem hasDirichletDensity_empty :
    HasDirichletDensity (∅ : Set (Ideal (𝓞 K))) 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := ⟨(·.2.1)⟩
  simpa only [HasDirichletDensity, primeIdealZetaSum_def K, tsum_empty, zero_div]
    using tendsto_const_nhds

/-- Planning source: Density.lean:241; statement placeholder. -/
theorem HasDirichletDensity.union_of_disjoint {T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T)
    {ε : ℝ} (hS : HasDirichletDensity S δ) (hT : HasDirichletDensity T ε) :
    HasDirichletDensity (S ∪ T) (δ + ε) := by
  rw [HasDirichletDensity] at hS hT ⊢
  refine (hS.add hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [primeIdealZetaSum_union_of_disjoint K hDisj hs, add_div]

/-- Planning source: Abelian.lean:109; statement placeholder. -/
theorem hasDirichletDensity_biUnion_const {F : Type*} [Field F] [NumberField F]
    {ι : Type*} (t : Finset ι) (S : ι → Set (Ideal (𝓞 F))) (c : ℝ)
    (hdisj : (t : Set ι).PairwiseDisjoint S)
    (hdens : ∀ i ∈ t, HasDirichletDensity (S i) c) :
    HasDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using hasDirichletDensity_empty (K := F)
  | insert a t ha ih =>
      have hdisj' : (t : Set ι).PairwiseDisjoint S :=
        hdisj.subset (Finset.coe_subset.mpr (Finset.subset_insert a t))
      have hdisjUnion : Disjoint (S a) (⋃ i ∈ t, S i) :=
        Set.disjoint_iUnion₂_right.2 fun i hi ↦
          hdisj (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hi) fun h ↦ ha (h ▸ hi)
      have hbase := hdens a (Finset.mem_insert_self a t)
      have hrec := ih hdisj' fun i hi ↦ hdens i (Finset.mem_insert_of_mem hi)
      have hcard : ((insert a t).card : ℝ) • c = c + (t.card : ℝ) • c := by
        rw [Finset.card_insert_of_notMem ha]; push_cast; ring
      rw [Finset.set_biUnion_insert, hcard]
      exact HasDirichletDensity.union_of_disjoint F hdisjUnion hbase hrec

/-- Planning source: Density.lean:236; statement placeholder. -/
theorem HasDirichletDensity.hasLower (h : HasDirichletDensity S δ) :
    HasLowerDirichletDensity S δ :=
  h.liminf_eq

/-- Planning source: Density.lean:206; statement placeholder. -/
theorem isBoundedUnder_ge_primeIdealZetaSum_ratio (S : Set (Ideal (𝓞 K))) :
    IsBoundedUnder (· ≥ ·) (𝓝[>] (1 : ℝ))
      (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) :=
  isBoundedUnder_of ⟨0, fun s ↦ div_nonneg (primeIdealZetaSum_nonneg K S s)
    (primeIdealZetaSum_nonneg K univ s)⟩

/-- Planning source: Density.lean:126; statement placeholder. -/
theorem primeIdealZetaSum_le_univ {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum S s ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  rw [primeIdealZetaSum_def K, primeIdealZetaSum_def K]
  refine (summable_prime_absNorm_rpow K S hs).tsum_le_tsum_of_inj
    (fun 𝔭 ↦ ⟨𝔭.1, mem_univ _, 𝔭.2.2.1, 𝔭.2.2.2⟩)
    (fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))
    (fun c _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ ↦ le_rfl) (summable_prime_absNorm_rpow K (univ : Set (Ideal (𝓞 K))) hs)

/-- Planning source: Density.lean:214; statement placeholder. -/
theorem eventually_primeIdealZetaSum_ratio_le_one (S : Set (Ideal (𝓞 K))) :
    ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s ≤ 1 := by
  filter_upwards [self_mem_nhdsWithin] with s hs using
    div_le_one_of_le₀ (primeIdealZetaSum_le_univ K hs) (primeIdealZetaSum_nonneg K univ s)

/-- Planning source: Density.lean:250; statement placeholder. -/
theorem HasLowerDirichletDensity.mono {T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {ε : ℝ}
    (hS : HasLowerDirichletDensity S δ) (hT : HasLowerDirichletDensity T ε) :
    δ ≤ ε := by
  rw [HasLowerDirichletDensity] at hS hT
  rw [← hS, ← hT]
  refine liminf_le_liminf ?_ (isBoundedUnder_ge_primeIdealZetaSum_ratio K S)
    (isCoboundedUnder_ge_of_eventually_le (x := 1) _
      (eventually_primeIdealZetaSum_ratio_le_one K T))
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact div_le_div_of_nonneg_right (primeIdealZetaSum_le_of_subset K hST hs)
    (primeIdealZetaSum_nonneg K univ s)

/-- Planning source: Density.lean:172; statement placeholder. -/
theorem primeIdealZetaSum_empty (s : ℝ) : primeIdealZetaSum (∅ : Set (Ideal (𝓞 K))) s = 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    ⟨(·.2.1)⟩
  rw [primeIdealZetaSum_def K, tsum_empty]

/-- Planning source: Density.lean:179; statement placeholder. -/
theorem primeIdealZetaSum_biUnion_of_pairwiseDisjoint {ι : Type*} (t : Finset ι)
    (g : ι → Set (Ideal (𝓞 K))) (hg : (t : Set ι).PairwiseDisjoint g) {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum (⋃ i ∈ t, g i) s = ∑ i ∈ t, primeIdealZetaSum (g i) s := by
  classical
  induction t using Finset.induction with
  | empty => simp [primeIdealZetaSum_empty]
  | insert a t ha ih =>
      have hdisj : Disjoint (g a) (⋃ i ∈ t, g i) :=
        disjoint_iUnion₂_right.2 fun i hi ↦
          hg (t.mem_insert_self a) (Finset.mem_insert_of_mem hi) fun h ↦ ha (h ▸ hi)
      rw [Finset.set_biUnion_insert, primeIdealZetaSum_union_of_disjoint K hdisj hs,
        Finset.sum_insert ha, ih (hg.subset (Finset.coe_subset.mpr (Finset.subset_insert a t)))]

/-- Planning source: Density.lean:570; statement placeholder. -/
theorem hasDirichletDensity_univ : HasDirichletDensity (univ : Set (Ideal (𝓞 K))) 1 := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(primeIdealZetaSum_univ_tendsto_atTop K).eventually_gt_atTop 0] with s hs
  exact (div_self hs.ne').symm

/-- Planning source: Abelian.lean:1449; finite-sum child. -/
theorem sum_liminf_le_liminf_sum {ι α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
    [DenselyOrdered α] [AddLeftMono α] {l : Filter ι} [l.NeBot] {κ : Type*} (g : κ → ι → α)
    (t : Finset κ)
    (hbelow : ∀ j ∈ t, l.IsBoundedUnder (· ≥ ·) (g j))
    (habove : ∀ j ∈ t, l.IsBoundedUnder (· ≤ ·) (g j)) :
    ∑ j ∈ t, liminf (g j) l ≤ liminf (fun x ↦ ∑ j ∈ t, g j x) l := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hbS : l.IsBoundedUnder (· ≥ ·) (fun x ↦ ∑ j ∈ s, g j x) :=
        Finset.sum_fn s g ▸ Filter.isBoundedUnder_ge_sum s
          (fun j hj ↦ hbelow j (Finset.mem_insert_of_mem hj))
      have haS : l.IsBoundedUnder (· ≤ ·) (fun x ↦ ∑ j ∈ s, g j x) :=
        Finset.sum_fn s g ▸ Filter.isBoundedUnder_le_sum s
          (fun j hj ↦ habove j (Finset.mem_insert_of_mem hj))
      have step : liminf (g a) l + liminf (fun x ↦ ∑ j ∈ s, g j x) l
          ≤ liminf (fun x ↦ g a x + ∑ j ∈ s, g j x) l :=
        le_liminf_add (hbelow a (Finset.mem_insert_self a s))
          (habove a (Finset.mem_insert_self a s)) hbS (IsBoundedUnder.isCoboundedUnder_ge haS)
      calc liminf (g a) l + ∑ j ∈ s, liminf (g j) l
          ≤ liminf (g a) l + liminf (fun x ↦ ∑ j ∈ s, g j x) l := by
            gcongr
            exact ih (fun j hj ↦ hbelow j (Finset.mem_insert_of_mem hj))
              (fun j hj ↦ habove j (Finset.mem_insert_of_mem hj))
        _ ≤ liminf (fun x ↦ g a x + ∑ j ∈ s, g j x) l := step
        _ = liminf (fun x ↦ ∑ j ∈ insert a s, g j x) l := by simp_rw [Finset.sum_insert ha]

/-- Planning source: Abelian.lean:1480; finite-sum child. -/
theorem isBoundedUnder_le_of_isBoundedUnder_le_sum {β ι : Type*} [Fintype ι] {l : Filter β}
    (g : ι → β → ℝ) (hF : l.IsBoundedUnder (· ≤ ·) (fun s ↦ ∑ i, g i s))
    (hbelow : ∀ i, l.IsBoundedUnder (· ≥ ·) (g i)) (i : ι) :
    l.IsBoundedUnder (· ≤ ·) (g i) := by
  classical
  obtain ⟨a, ha⟩ := hF.eventually_le
  obtain ⟨b, hb⟩ := (Finset.sum_fn _ g ▸
    Filter.isBoundedUnder_ge_sum (Finset.univ.erase i) (fun j _ ↦ hbelow j)).eventually_ge
  refine isBoundedUnder_of_eventually_le (a := a - b) ?_
  filter_upwards [ha, hb] with s hsa hsb
  have := Finset.add_sum_erase Finset.univ (fun j ↦ g j s) (Finset.mem_univ i)
  linarith

/-- Planning source: Abelian.lean:1504; statement placeholder. -/
theorem tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one {ι : Type*} [Fintype ι]
    {γ : Type*} {l : Filter γ} [l.NeBot] (g : ι → γ → ℝ)
    (hlo : ∀ i, (Fintype.card ι : ℝ)⁻¹ ≤ Filter.liminf (g i) l)
    (hbelow : ∀ i, Filter.IsBoundedUnder (· ≥ ·) l (g i))
    (hsum : Filter.Tendsto (fun s ↦ ∑ i, g i s) l (𝓝 (1 : ℝ))) (i₀ : ι) :
    Filter.Tendsto (g i₀) l (𝓝 (Fintype.card ι : ℝ)⁻¹) := by
  classical
  set N : ℕ := Fintype.card ι with hN
  set F : γ → ℝ := fun s ↦ ∑ i, g i s with hF
  have hFle : l.IsBoundedUnder (· ≤ ·) F := hsum.isBoundedUnder_le
  have hFlimsup : limsup F l = 1 := hsum.limsup_eq
  have hgle : ∀ i, l.IsBoundedUnder (· ≤ ·) (g i) :=
    isBoundedUnder_le_of_isBoundedUnder_le_sum g hFle hbelow
  haveI : Nonempty ι := ⟨i₀⟩
  have hNpos : 0 < N := Fintype.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  set t : Finset ι := Finset.univ.erase i₀ with ht
  have hrestge : l.IsBoundedUnder (· ≥ ·) (fun s ↦ ∑ j ∈ t, g j s) :=
    Finset.sum_fn t g ▸ Filter.isBoundedUnder_ge_sum t (fun j _ ↦ hbelow j)
  have hrestle : l.IsBoundedUnder (· ≤ ·) (fun s ↦ ∑ j ∈ t, g j s) :=
    Finset.sum_fn t g ▸ Filter.isBoundedUnder_le_sum t (fun j _ ↦ hgle j)
  have hcard : t.card = N - 1 := Finset.card_erase_of_mem (Finset.mem_univ i₀)
  have hliminf_rest : ((N : ℝ) - 1) / N ≤ liminf (fun s ↦ ∑ j ∈ t, g j s) l := by
    have hsuper : ∑ j ∈ t, liminf (g j) l ≤ liminf (fun s ↦ ∑ j ∈ t, g j s) l :=
      sum_liminf_le_liminf_sum g t (fun j _ ↦ hbelow j) (fun j _ ↦ hgle j)
    have hlb : ∑ j ∈ t, ((N : ℝ))⁻¹ ≤ ∑ j ∈ t, liminf (g j) l :=
      Finset.sum_le_sum (fun j _ ↦ hlo j)
    have hconst : ∑ _j ∈ t, ((N : ℝ))⁻¹ = (t.card : ℝ) * (N : ℝ)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst, hcard] at hlb
    have hcast : ((N : ℝ) - 1) / N = ((N - 1 : ℕ) : ℝ) * (N : ℝ)⁻¹ := by
      have hsub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        have : (1 : ℕ) ≤ N := hNpos
        push_cast [Nat.cast_sub this]
        ring
      rw [hsub]
      ring
    rw [hcast]
    exact le_trans hlb hsuper
  have hFeq : (fun s ↦ g i₀ s + ∑ j ∈ t, g j s) = F := by
    funext s
    rw [hF]
    exact Finset.add_sum_erase Finset.univ (fun j ↦ g j s) (Finset.mem_univ i₀)
  have hadd : limsup (g i₀) l + liminf (fun s ↦ ∑ j ∈ t, g j s) l
      ≤ limsup (fun s ↦ g i₀ s + ∑ j ∈ t, g j s) l :=
    le_limsup_add (hgle i₀) (IsBoundedUnder.isCoboundedUnder_le (hbelow i₀)) hrestle hrestge
  rw [hFeq, hFlimsup] at hadd
  have hlimsup_le : limsup (g i₀) l ≤ (N : ℝ)⁻¹ := by
    have hrest_le : liminf (fun s ↦ ∑ j ∈ t, g j s) l ≤ 1 - limsup (g i₀) l := by linarith
    have h1 : limsup (g i₀) l ≤ 1 - ((N : ℝ) - 1) / N := by
      linarith [le_trans hliminf_rest hrest_le]
    have h2 : 1 - ((N : ℝ) - 1) / N = (N : ℝ)⁻¹ := by
      field_simp
      ring
    rwa [h2] at h1
  exact tendsto_of_le_liminf_of_limsup_le (hlo i₀) hlimsup_le (hgle i₀) (hbelow i₀)

/-- Planning source: Main.lean:112; statement placeholder. -/
theorem infinite_of_hasDirichletDensity_pos
    {S : Set (Ideal (𝓞 K))} {δ : ℝ} (h : HasDirichletDensity S δ) (hδ : 0 < δ) :
    S.Infinite :=
  fun hfin ↦ hδ.ne' (tendsto_nhds_unique h (hasDirichletDensity_of_finite K hfin))

/-- Planning source: Main.lean:118; statement placeholder. -/
theorem ConjClasses_carrier_card_pos
    {G : Type*} [Monoid G] [Finite G] (C : ConjClasses G) :
    0 < Nat.card C.carrier := by
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C
  have : Nonempty (ConjClasses.mk a).carrier := ⟨⟨a, ConjClasses.mem_carrier_mk⟩⟩
  exact Nat.card_pos

/-- Planning source: Density.lean:223; statement placeholder. -/
theorem HasDirichletDensity.of_upper_eq_lower (hUp : HasUpperDirichletDensity S δ)
    (hLow : HasLowerDirichletDensity S δ) :
    HasDirichletDensity S δ :=
  tendsto_of_liminf_eq_limsup hLow hUp
    ⟨1, eventually_map.mpr (eventually_primeIdealZetaSum_ratio_le_one K S)⟩
    (isBoundedUnder_ge_primeIdealZetaSum_ratio K S)

/-- Planning source: Density.lean:231; statement placeholder. -/
theorem HasDirichletDensity.hasUpper (h : HasDirichletDensity S δ) :
    HasUpperDirichletDensity S δ :=
  h.limsup_eq

end Cox.Chebotarev
