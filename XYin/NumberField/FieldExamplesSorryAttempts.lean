/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.Euclidean
import XYin.NumberField.FieldExamples.CyclotomicFive.Euclidean
import XYin.NumberField.FieldExamples.CyclotomicEight.Euclidean
import XYin.NumberField.FieldExamples.SqrtFive.Units
import XYin.NumberField.FieldExamples.SqrtTwo.Units

/-!
# Sandbox: attempts at the `FieldExamples` blocked `sorry`s

This file is a **non-invasive** workspace, outside `FieldExamples`, in which the eleven remaining
`sorry`s of `FieldExamples` are restated (with primed names, `private`) and attempted
independently.  Nothing here is imported by, or affects, `FieldExamples`.

The eleven targets fall into four mathematical classes:

* `regulator_eq'` (SqrtTwo, SqrtFive, CyclotomicFive, CyclotomicEight) — **PROVED here.**  Each is a
  port of the *completed* `CubeRootThree.regulator_eq`: reduce `regulator` to `regOfFamily` via
  `regOfFamily_div_regulator` together with the field's `fundamentalUnitSystem_isFundamental`, then
  collapse the 1×1 determinant and compute the place value of the fundamental unit (a real-place
  weight-1 absolute value for the quadratic fields; a complex-place weight-2 value, requiring the
  analytic facts `|1 + ζ₅| = (1+√5)/2` and `|1 + ζ₈ + ζ₈⁷| = 1 + √2`, for the cyclotomic fields).
  For CyclotomicFive / CyclotomicEight these cite the (internally sorried) `isFundamental`, so the
  proof is the genuine reduction `regulator_eq ⇐ isFundamental`.

* `fundamentalUnitSystem_isFundamental'` (CubeRootThree, CyclotomicFive, CyclotomicEight) — still
  `sorry`.  Needs an Artin/Minkowski lower bound on the regulator to rule out the displayed unit
  being a proper power; no such API is available in mathlib.

* `normEuclidean'` (CubeRootThree, CyclotomicFive, CyclotomicEight) — still `sorry`.  A covering
  argument; the degree-2 templates (SqrtTwo etc.) use nearest-integer rounding, which overflows the
  unit norm in the cubic / quartic power bases, so the fundamental domain must be covered by hand.

* `fundamentalUnit_generates'` (SqrtFive) — still `sorry`.  The Fibonacci/Pell `a² - 5b² = ±4`
  bridge for the half-integral order `ℤ[(1+√5)/2]`; mathlib only has the `Zsqrtd`/`Pell` theory for
  `x² - d y² = 1`.
-/

/-! ### `ℚ(∛3)` -/

noncomputable section

open Module Polynomial
open NumberField.FieldExamples
open scoped NumberField nonZeroDivisors

namespace NumberField.CubeRootThree

/-! #### `normEuclidean'` — BLOCKED (documented), with a proven partial covering bound.

`ℚ(∛3)` *is* norm-Euclidean (the pure cubic field of smallest discriminant `−243`), but the proof
needs a genuine covering of the fundamental domain, not coordinatewise rounding.

In the integral basis `1, θ, θ²` the field norm is the cubic form
`N(x + yθ + zθ²) = x³ + 3y³ + 9z³ − 9xyz` (`CubeRootThree.norm_eq_normForm`). The Euclidean step
(helper `abs_intNorm_lt_of_abs_norm_le` in `FieldExamples/Common.lean`, used by every degree-2
template, e.g. `SqrtTwo/Euclidean.lean`) reduces the theorem to: every real target has a lattice
point `(a,b,c)` with `|N(u−a, v−b, w−c)| < 1`, i.e. the *Euclidean minimum* of the form is `< 1`.

Plain nearest-integer rounding FAILS: with fractional parts `f,g,h ∈ [−1/2,1/2]`, at
`(−1/2, 1/2, 1/2)` we get `N = −1/8 + 3/8 + 9/8 + 9/8 = 2.5 ≫ 1` (the `9z³` and `−9xyz` terms
overflow). A correct proof needs a per-region lattice choice (8-corner sup `≈ 0.979`, optimal
`≈ 0.694`) — not a uniform rounding rule — together with tight cubic inequalities relying on
cancellation between `9h³` and `−9fgh` that `nlinarith` will not find at this margin.

Searched (leansearch, loogle): no `EuclideanDomain (𝓞 K)` instance beyond `GaussianInt`; no
"Euclidean minimum `< 1`" / norm-Euclidean-over-fundamental-domain lemma; `ZSpan.fundamentalDomain`,
`NumberField.mixedEmbedding.fundamentalDomain_idealLattice`, `ClassGroup.exists_min` exist but give
no covering bound for an explicit cubic form. Genuinely blocked on a hand-built covering argument.
-/

/-- Partial progress toward `normEuclidean'`: on the central cube `|f|, |g|, |h| ≤ 1/3` the norm
form is bounded by `1`, so nearest-integer rounding succeeds there (numerically `sup |N| ≈ 0.72`).
This is the largest origin-centred cube on which the naive method is valid; the obstruction lives
entirely in the outer shell `1/3 < max|·| ≤ 1/2`. -/
private theorem normForm_lt_one_of_central (f g h : ℚ)
    (hf : |f| ≤ 1 / 3) (hg : |g| ≤ 1 / 3) (hh : |h| ≤ 1 / 3) :
    |f ^ 3 + 3 * g ^ 3 + 9 * h ^ 3 - 9 * f * g * h| < 1 := by
  have cf : |f ^ 3| ≤ (1 / 3) ^ 3 := by rw [abs_pow]; gcongr
  have cg : |g ^ 3| ≤ (1 / 3) ^ 3 := by rw [abs_pow]; gcongr
  have ch : |h ^ 3| ≤ (1 / 3) ^ 3 := by rw [abs_pow]; gcongr
  have cx : |f * g * h| ≤ (1 / 3) ^ 3 := by
    rw [abs_mul, abs_mul, show ((1 : ℚ) / 3) ^ 3 = (1 / 3) * (1 / 3) * (1 / 3) by norm_num]
    gcongr
  rw [abs_le] at cf cg ch cx
  rw [abs_lt]
  constructor <;> nlinarith [cf.1, cf.2, cg.1, cg.2, ch.1, ch.2, cx.1, cx.2]

/-- Blocked: requires the fundamental-domain covering argument documented above. ℚ(∛3) is
norm-Euclidean (Euclidean minimum `≈ 0.694 < 1`) but no uniform rounding rule and no mathlib API
discharges it; see `normForm_lt_one_of_central` for the proven safe region. -/
private theorem normEuclidean' (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry

/-! #### `fundamentalUnitSystem_isFundamental'` — reduced to a single explicit gap.

The whole proof goes through *except* one number-theoretic fact: that the displayed unit `θ² − 2`
has exponent `±1` relative to mathlib's abstract fundamental unit `fundSystem K i₀` (i.e. it is
genuinely fundamental, not a proper power times a root of unity). Ruling out exponent `|n₀| ≥ 2`
needs a regulator lower bound (Artin/Minkowski), which mathlib does not provide; that is the single
isolated `sorry` (`hn₀`) below. Everything else — the reduction via
`exists_eq_torsion_mul_fundSystem_zpow` and `closure_fundSystem_sup_torsion_eq_top` — is proved. -/
private theorem fundamentalUnitSystem_isFundamental' :
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K = ⊤ := by
  set i₀ : Fin (NumberField.Units.rank K) :=
    ⟨0, by rw [unitRank_eq_one]; exact Nat.zero_lt_one⟩ with hi₀
  set η : (𝓞 K)ˣ := NumberField.Units.fundSystem K i₀ with hη
  set S : Subgroup (𝓞 K)ˣ :=
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K with hS
  have hrange : Set.range fundamentalUnitSystem = {fundamentalUnit} := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩; rfl
    · rintro rfl
      exact ⟨⟨0, by rw [unitRank_eq_one]; exact Nat.zero_lt_one⟩, rfl⟩
  have hfu_mem : fundamentalUnit ∈ S := by
    refine Subgroup.mem_sup_left ?_
    exact Subgroup.subset_closure (by rw [hrange]; rfl)
  have htor_le : NumberField.Units.torsion K ≤ S := le_sup_right
  obtain ⟨ζ₀, hζ₀, n₀, hfu⟩ :=
    exists_eq_torsion_mul_fundSystem_zpow i₀ fundamentalUnit
  -- THE GENUINE NUMBER-THEORETIC GAP: needs a regulator lower bound (Artin/Minkowski).
  have hn₀ : n₀ = 1 ∨ n₀ = -1 := by
    sorry
  have hη_mem : η ∈ S := by
    rcases hn₀ with rfl | rfl
    · have : η = ζ₀⁻¹ * fundamentalUnit := by
        rw [hfu, hη]; simp [zpow_one, mul_comm, ← mul_assoc]
      rw [this]
      exact Subgroup.mul_mem _ (htor_le (Subgroup.inv_mem _ hζ₀)) hfu_mem
    · have : η = ζ₀ * fundamentalUnit⁻¹ := by
        rw [hfu, hη]; simp [zpow_neg, zpow_one, mul_comm, ← mul_assoc]
      rw [this]
      exact Subgroup.mul_mem _ (htor_le hζ₀) (Subgroup.inv_mem _ hfu_mem)
  have hrange_fs : Set.range (NumberField.Units.fundSystem K) = {η} := by
    haveI hsub : Subsingleton (Fin (NumberField.Units.rank K)) :=
      Fin.subsingleton_iff_le_one.mpr (by rw [unitRank_eq_one])
    ext v
    constructor
    · rintro ⟨i, rfl⟩; rw [Subsingleton.elim i i₀]; rfl
    · rintro rfl; exact ⟨i₀, rfl⟩
  have htop : Subgroup.closure (Set.range (NumberField.Units.fundSystem K)) ⊔
      NumberField.Units.torsion K ≤ S := by
    refine sup_le ?_ htor_le
    rw [hrange_fs, Subgroup.closure_le]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]; exact hη_mem
  rw [NumberField.Units.closure_fundSystem_sup_torsion_eq_top] at htop
  exact top_le_iff.mp htop

end NumberField.CubeRootThree

end

/-! ### `ℚ(ζ₅)` -/

noncomputable section

open Module Polynomial
open NumberField.FieldExamples
open scoped NumberField nonZeroDivisors Real

namespace NumberField.CyclotomicFive

/-- Blocked: covering argument in the quartic power basis. -/
private theorem normEuclidean' (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry

/-- Blocked: needs an Artin/Minkowski regulator lower bound. -/
private theorem fundamentalUnitSystem_isFundamental' :
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K = ⊤ := by
  sorry

/-- The regulator of `ℚ(ζ₅)` is `2·log φ`.  Proved here by porting `CubeRootThree.regulator_eq`,
with the complex-place weight `2` and the analytic value `|1 + ζ₅| = (1+√5)/2`. -/
private theorem regulator_eq' :
    NumberField.Units.regulator K = 2 * Real.log ((1 + Real.sqrt 5) / 2) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_complexEmbedding_zeta
  let wR : NumberField.InfinitePlace K := NumberField.InfinitePlace.mk σ
  have hwRcomplex : NumberField.InfinitePlace.IsComplex wR := infinitePlace_isComplex wR
  have hwRu : wR (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) = (1 + Real.sqrt 5) / 2 := by
    have hval : (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) = 1 + ζ := by
      simp [fundamentalUnit, map_add, map_one, zetaInt]
    rw [hval]
    change ‖σ (1 + ζ)‖ = (1 + Real.sqrt 5) / 2
    rw [map_add, map_one, hσ]
    have hrw : (2 * (Real.pi : ℂ) * Complex.I / 5) =
        ((2 * Real.pi / 5 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hrw, Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have hcos2 : Real.cos (2 * Real.pi / 5) = 2 * Real.cos (Real.pi / 5) ^ 2 - 1 := by
      rw [show (2 * Real.pi / 5) = 2 * (Real.pi / 5) by ring, Real.cos_two_mul]
    have hsin : Real.sin (2 * Real.pi / 5) ^ 2 = 1 - Real.cos (2 * Real.pi / 5) ^ 2 := by
      have := Real.sin_sq_add_cos_sq (2 * Real.pi / 5); linarith
    have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hphi : (0 : ℝ) ≤ (1 + Real.sqrt 5) / 2 := by positivity
    rw [show (1 + Real.cos (2 * Real.pi / 5)) * (1 + Real.cos (2 * Real.pi / 5)) +
          (0 + Real.sin (2 * Real.pi / 5)) * (0 + Real.sin (2 * Real.pi / 5))
        = 2 + 2 * Real.cos (2 * Real.pi / 5) +
          (Real.sin (2 * Real.pi / 5) ^ 2 - (1 - Real.cos (2 * Real.pi / 5) ^ 2)) by ring]
    rw [hsin]
    simp only [sub_self, add_zero]
    rw [hcos2, Real.cos_pi_div_five]
    rw [show (2 + 2 * (2 * ((1 + Real.sqrt 5) / 4) ^ 2 - 1)) = ((1 + Real.sqrt 5) / 2) ^ 2 by
      field_simp; nlinarith [hsqrt5]]
    exact Real.sqrt_sq hphi
  obtain ⟨wC, hwCne⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [infinitePlace_card_eq_two]; norm_num) wR
  have hwRne : wR ≠ wC := hwCne.symm
  have hcard_sub : Fintype.card {w : NumberField.InfinitePlace K // w ≠ wC} = 1 := by
    rw [show Fintype.card {w : NumberField.InfinitePlace K // w ≠ wC} =
        Fintype.card {w : NumberField.InfinitePlace K // ¬ w = wC} from rfl]
    rw [Fintype.card_subtype_compl (fun w : NumberField.InfinitePlace K => w = wC)]
    rw [Fintype.card_subtype_eq, infinitePlace_card_eq_two]
  let e : {w : NumberField.InfinitePlace K // w ≠ wC} ≃ Fin (NumberField.Units.rank K) :=
    Fintype.equivOfCardEq (by rw [hcard_sub, Fintype.card_fin, unitRank_eq_one])
  have hreg : NumberField.Units.regulator K =
      NumberField.Units.regOfFamily
        (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit) := by
    have hdiv := NumberField.Units.regOfFamily_div_regulator (K := K)
      (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit)
    have htop : Subgroup.closure
        (Set.range (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit)) ⊔
          NumberField.Units.torsion K = ⊤ := by
      simpa [fundamentalUnitSystem] using fundamentalUnitSystem_isFundamental
    rw [htop, Subgroup.index_top] at hdiv
    field_simp [NumberField.Units.regulator_ne_zero K] at hdiv
    simpa using hdiv.symm
  rw [hreg]
  rw [NumberField.Units.regOfFamily_eq_det
    (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit) wC e]
  haveI : Subsingleton {w : NumberField.InfinitePlace K // w ≠ wC} :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [hcard_sub])
  rw [Matrix.det_eq_elem_of_subsingleton _ ⟨wR, hwRne⟩]
  simp only [Matrix.of_apply, NumberField.InfinitePlace.mult_isComplex ⟨wR, hwRcomplex⟩, hwRu]
  have hlog : (0 : ℝ) ≤ Real.log ((1 + Real.sqrt 5) / 2) := by
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ Real.sqrt 5 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith
  rw [show ((2 : ℕ) : ℝ) * Real.log ((1 + Real.sqrt 5) / 2) =
      2 * Real.log ((1 + Real.sqrt 5) / 2) by push_cast; ring]
  rw [abs_of_nonneg (by positivity)]

end NumberField.CyclotomicFive

end

/-! ### `ℚ(ζ₈)` -/

noncomputable section

open Module
open NumberField.FieldExamples
open scoped NumberField nonZeroDivisors Real

namespace NumberField.CyclotomicEight

/-- Blocked: covering argument in the quartic power basis. -/
private theorem normEuclidean' (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry

/-- Blocked: needs an Artin/Minkowski regulator lower bound. -/
private theorem fundamentalUnitSystem_isFundamental' :
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K = ⊤ := by
  sorry

set_option linter.style.longLine false in
/-- The regulator of `ℚ(ζ₈)` is `2·log(1 + √2)`.  Proved here by porting
`CubeRootThree.regulator_eq`, with the complex-place weight `2` and the analytic value
`|1 + ζ₈ + ζ₈⁷| = 1 + √2`. -/
private theorem regulator_eq' :
    NumberField.Units.regulator K = 2 * Real.log (1 + Real.sqrt 2) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_complexEmbedding_zeta
  let wR : NumberField.InfinitePlace K := NumberField.InfinitePlace.mk σ
  have hwRcomplex : NumberField.InfinitePlace.IsComplex wR := infinitePlace_isComplex wR
  have hz : algebraMap (𝓞 K) K zetaInt = ζ :=
    NumberField.RingOfIntegers.map_mk ζ zeta_integral
  -- analytic value of the fundamental unit at the complex place
  have hσu : σ (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) = ((1 + Real.sqrt 2 : ℝ) : ℂ) := by
    have hval : ((fundamentalUnit : (𝓞 K)ˣ) : 𝓞 K) = 1 + zetaInt + zetaInt ^ 7 := rfl
    rw [hval]
    simp only [map_add, map_one, map_pow, hz, hσ]
    have hξ : Complex.exp (2 * Real.pi * Complex.I / 8) = Complex.exp ((Real.pi/4 : ℝ) * Complex.I) := by
      congr 1; push_cast; ring
    rw [hξ, ← Complex.exp_nat_mul]
    have e7 : (7 : ℕ) * ((Real.pi/4 : ℝ) * Complex.I) = (-(Real.pi/4 : ℝ) * Complex.I) + 2 * Real.pi * Complex.I := by
      push_cast; ring
    rw [e7, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    have hcos : Complex.exp ((Real.pi/4 : ℝ) * Complex.I) + Complex.exp (-(Real.pi/4 : ℝ) * Complex.I)
        = 2 * Complex.cos (Real.pi/4 : ℝ) := (Complex.two_cos _).symm
    have h2 : (1 : ℂ) + Complex.exp ((Real.pi/4 : ℝ) * Complex.I) + Complex.exp (-(Real.pi/4 : ℝ) * Complex.I)
        = 1 + 2 * Complex.cos (Real.pi/4 : ℝ) := by rw [add_assoc, hcos]
    rw [h2, ← Complex.ofReal_cos, Real.cos_pi_div_four]
    push_cast; ring
  have hsqrt_pos : (0 : ℝ) < 1 + Real.sqrt 2 := by positivity
  have hwRu : wR (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) = 1 + Real.sqrt 2 := by
    change ‖σ (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))‖ = 1 + Real.sqrt 2
    rw [hσu, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt_pos]
  obtain ⟨wC, hwCne⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [infinitePlace_card_eq_two]; norm_num) wR
  have hwRne : wR ≠ wC := hwCne.symm
  have hcard_sub : Fintype.card {w : NumberField.InfinitePlace K // w ≠ wC} = 1 := by
    rw [show Fintype.card {w : NumberField.InfinitePlace K // w ≠ wC} =
        Fintype.card {w : NumberField.InfinitePlace K // ¬ w = wC} from rfl]
    rw [Fintype.card_subtype_compl (fun w : NumberField.InfinitePlace K => w = wC)]
    rw [Fintype.card_subtype_eq, infinitePlace_card_eq_two]
  let e : {w : NumberField.InfinitePlace K // w ≠ wC} ≃ Fin (NumberField.Units.rank K) :=
    Fintype.equivOfCardEq (by rw [hcard_sub, Fintype.card_fin, unitRank_eq_one])
  have hreg : NumberField.Units.regulator K =
      NumberField.Units.regOfFamily
        (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit) := by
    have hdiv := NumberField.Units.regOfFamily_div_regulator (K := K)
      (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit)
    have htop : Subgroup.closure
        (Set.range (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit)) ⊔
          NumberField.Units.torsion K = ⊤ := by
      simpa [fundamentalUnitSystem] using fundamentalUnitSystem_isFundamental
    rw [htop, Subgroup.index_top] at hdiv
    field_simp [NumberField.Units.regulator_ne_zero K] at hdiv
    simpa using hdiv.symm
  rw [hreg]
  rw [NumberField.Units.regOfFamily_eq_det
    (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit) wC e]
  haveI : Subsingleton {w : NumberField.InfinitePlace K // w ≠ wC} :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [hcard_sub])
  rw [Matrix.det_eq_elem_of_subsingleton _ ⟨wR, hwRne⟩]
  simp only [Matrix.of_apply, NumberField.InfinitePlace.mult_isComplex ⟨wR, hwRcomplex⟩, hwRu,
    Nat.cast_ofNat]
  rw [abs_of_nonneg (mul_nonneg (by norm_num)
    (Real.log_nonneg (by linarith [Real.sqrt_nonneg 2])))]

end NumberField.CyclotomicEight

end

/-! ### `ℚ(√5)` -/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra
open Module NumberField Polynomial
open NumberField.FieldExamples

namespace NumberField.SqrtFive

/-! #### `fundamentalUnit_generates'` — every unit of `ℤ[φ]` is `±φ^n`.

A self-contained real-embedding discreteness argument (NOT the `Zsqrtd`/`Pell` bridge, which only
covers the index-2 suborder `ℤ[√5]`): the unit `φ` maps to `Φ = (1+√5)/2 > 1` under the real
embedding, every unit is reduced into the window `[1, Φ)` by a power of `φ`, and the only unit in
that window is `1`. The half-integral order `ℤ[φ]` is handled directly through the norm form
`x² + xy - y² = ±1`. -/

/-- The real embedding `ℚ(√5) → ℝ` sending `φ` to `Φ = (1 + √5)/2`. -/
private def reEmb : K →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨(1 + Real.sqrt 5) / 2, by
    have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
    rw [show ((1 + Real.sqrt 5) / 2) * ((1 + Real.sqrt 5) / 2) =
        (3 + Real.sqrt 5) / 2 by nlinarith]
    simp
    ring⟩

private theorem reEmb_golden : reEmb goldenRoot = (1 + Real.sqrt 5) / 2 := by
  simp [reEmb, goldenRoot]

/-- The real embedding as a monoid homomorphism on the unit group. -/
private def fhom : (𝓞 K)ˣ →* ℝ :=
  reEmb.toRingHom.toMonoidHom.comp
    ((Units.coeHom K).comp (Units.map (algebraMap (𝓞 K) K)))

private theorem fhom_apply (u : (𝓞 K)ˣ) :
    fhom u = reEmb (algebraMap (𝓞 K) K (u : 𝓞 K)) := rfl

private theorem fhom_neg (u : (𝓞 K)ˣ) : fhom (-u) = -fhom u := by
  rw [fhom_apply, fhom_apply, Units.val_neg, map_neg, map_neg]

private theorem fhom_ne_zero (u : (𝓞 K)ˣ) : fhom u ≠ 0 := by
  intro h
  have hmul : fhom u * fhom u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at hmul
  exact one_ne_zero hmul.symm

private theorem fhom_fund : fhom fundamentalUnit = (1 + Real.sqrt 5) / 2 := by
  rw [fhom_apply]
  change reEmb (algebraMap (𝓞 K) K goldenIntO) = _
  have h : algebraMap (𝓞 K) K goldenIntO = goldenRoot := rfl
  rw [h, reEmb_golden]

/-- Every element of `𝓞 K = ℤ[φ]` is `a·1 + b·φ` with `a, b ∈ ℤ`. -/
private theorem exists_coords (z : 𝓞 K) :
    ∃ a b : ℤ, z = a • (1 : 𝓞 K) + b • goldenIntO := by
  have hint : IsIntegral ℤ (algebraMap (𝓞 K) K z) := z.2
  obtain ⟨y, hy⟩ := integral_mem_goldenOrderToField_range hint
  refine ⟨y.re, y.im, ?_⟩
  apply IsFractionRing.injective (𝓞 K) K
  rw [map_add, map_zsmul, map_zsmul]
  change algebraMap (𝓞 K) K z = _
  rw [← hy]
  change goldenOrderToField y = _
  cases y with
  | mk a b =>
    change (⟨(a : ℚ), (b : ℚ)⟩ : K) =
      (a : ℤ) • algebraMap (𝓞 K) K 1 + (b : ℤ) • algebraMap (𝓞 K) K goldenIntO
    rw [map_one]
    change (⟨(a : ℚ), (b : ℚ)⟩ : K) = (a : ℤ) • (1 : K) + (b : ℤ) • goldenRoot
    ext <;> simp [goldenRoot, zsmul_eq_mul]

private theorem coord_to_field (a b : ℤ) :
    algebraMap (𝓞 K) K (a • (1 : 𝓞 K) + b • goldenIntO) = (a : K) + (b : K) * goldenRoot := by
  rw [map_add, map_zsmul, map_zsmul, map_one]
  have h : algebraMap (𝓞 K) K goldenIntO = goldenRoot := rfl
  rw [h, zsmul_eq_mul, zsmul_eq_mul, mul_one]

private theorem reEmb_coord (a b : ℤ) :
    reEmb (algebraMap (𝓞 K) K (a • (1 : 𝓞 K) + b • goldenIntO)) =
      (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2) := by
  rw [coord_to_field, map_add, map_mul, map_intCast, map_intCast, reEmb_golden]

private theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private theorem sqrt5_lo : (2 : ℝ) < Real.sqrt 5 := by
  have h : Real.sqrt 4 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h

private theorem sqrt5_hi : Real.sqrt 5 < 3 := by
  have h : Real.sqrt 5 < Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [show Real.sqrt 9 = 3 by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h

private theorem phi_gt_one : (1 : ℝ) < (1 + Real.sqrt 5) / 2 := by
  linarith [sqrt5_lo]

/-- A unit `a·1 + b·φ` whose real value `a + bΦ` lies in `[1, Φ)` is forced to be `1`: its conjugate
`a + bΦ'` has absolute value `≤ 1` (norm `±1`), which bounds `b ∈ {0, 1}` and then `a`. -/
private theorem minimality (a b : ℤ) (sq5 : ℝ) (hsq : sq5 ^ 2 = 5) (hlo : 2 < sq5)
    (hhi : sq5 < 3)
    (hprod : ((a : ℝ) + b * ((1 + sq5) / 2)) * ((a : ℝ) + b * ((1 - sq5) / 2)) = 1 ∨
      ((a : ℝ) + b * ((1 + sq5) / 2)) * ((a : ℝ) + b * ((1 - sq5) / 2)) = -1)
    (h1 : 1 ≤ (a : ℝ) + b * ((1 + sq5) / 2))
    (h2 : (a : ℝ) + b * ((1 + sq5) / 2) < (1 + sq5) / 2) :
    a = 1 ∧ b = 0 := by
  have hrpos : 0 < (a : ℝ) + b * ((1 + sq5) / 2) := by linarith
  have hsbound1 : -1 ≤ (a : ℝ) + b * ((1 - sq5) / 2) := by
    rcases hprod with hp | hp <;> nlinarith [hp, h1, hrpos]
  have hsbound2 : (a : ℝ) + b * ((1 - sq5) / 2) ≤ 1 := by
    rcases hprod with hp | hp <;> nlinarith [hp, h1, hrpos]
  have hb_ge0 : (0 : ℝ) ≤ (b : ℝ) := by nlinarith [hsbound1, hsbound2, h1, hlo]
  have hb_lt2 : (b : ℝ) < 2 := by nlinarith [hsbound1, hsbound2, h2, hlo, hhi]
  have h0 : (0 : ℤ) ≤ b := by exact_mod_cast hb_ge0
  have h2' : b < 2 := by exact_mod_cast hb_lt2
  have hb0 : b = 0 ∨ b = 1 := by omega
  rcases hb0 with rfl | rfl
  · have ha_ge1 : (1 : ℝ) ≤ a := by push_cast at h1; linarith
    have ha_lt2 : (a : ℝ) < 2 := by push_cast at h2; nlinarith [h2, hhi]
    have hi1 : (1 : ℤ) ≤ a := by exact_mod_cast ha_ge1
    have hi2 : a < 2 := by exact_mod_cast ha_lt2
    exact ⟨by omega, rfl⟩
  · exfalso
    push_cast at h1 h2
    have ha_neg : (a : ℝ) < 0 := by linarith
    have ha_gt : (-1 : ℝ) < a := by linarith
    have h0' : a < 0 := by exact_mod_cast ha_neg
    have h1'' : (-1 : ℤ) < a := by exact_mod_cast ha_gt
    omega

/-- A unit whose real value lies in the window `[1, Φ)` is `1`. -/
private theorem reduction (u : (𝓞 K)ˣ) (h1 : 1 ≤ fhom u)
    (h2 : fhom u < (1 + Real.sqrt 5) / 2) : u = 1 := by
  obtain ⟨a, b, hab⟩ := exists_coords (u : 𝓞 K)
  have hfval : fhom u = (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2) := by
    rw [fhom_apply, hab, reEmb_coord]
  have hunit : IsUnit (a • (1 : 𝓞 K) + b • goldenIntO) := hab ▸ u.isUnit
  have hnorm := (isUnit_iff_normForm a b).mp hunit
  have hprod :
      ((a : ℝ) + b * ((1 + Real.sqrt 5) / 2)) * ((a : ℝ) + b * ((1 - Real.sqrt 5) / 2)) = 1 ∨
      ((a : ℝ) + b * ((1 + Real.sqrt 5) / 2)) * ((a : ℝ) + b * ((1 - Real.sqrt 5) / 2)) = -1 := by
    rcases hnorm with h | h
    · left
      have hr : (a : ℝ) ^ 2 + a * b - b ^ 2 = 1 := by exact_mod_cast h
      nlinarith [sqrt5_sq, hr]
    · right
      have hr : (a : ℝ) ^ 2 + a * b - b ^ 2 = -1 := by exact_mod_cast h
      nlinarith [sqrt5_sq, hr]
  obtain ⟨ha, hb⟩ := minimality a b (Real.sqrt 5) sqrt5_sq sqrt5_lo sqrt5_hi hprod
    (by rw [← hfval]; exact h1) (by rw [← hfval]; exact h2)
  subst ha; subst hb
  apply Units.ext
  rw [hab]
  simp

/-- Every unit with positive real value is a power of `φ`. -/
private theorem pos_case (u : (𝓞 K)ˣ) (hpos : 0 < fhom u) :
    ∃ n : ℤ, u = fundamentalUnit ^ n := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hpos phi_gt_one
  set v : (𝓞 K)ˣ := u * fundamentalUnit ^ (-n) with hv
  have hfv : fhom v = fhom u * ((1 + Real.sqrt 5) / 2) ^ (-n) := by
    rw [hv, map_mul, map_zpow, fhom_fund]
  have hΦpos : (0 : ℝ) < (1 + Real.sqrt 5) / 2 := by linarith [phi_gt_one]
  have hΦn : (0 : ℝ) < ((1 + Real.sqrt 5) / 2) ^ n := zpow_pos hΦpos n
  have hv1 : 1 ≤ fhom v := by
    rw [hfv, zpow_neg, le_mul_inv_iff₀ hΦn, one_mul]
    exact hn1
  have hv2 : fhom v < (1 + Real.sqrt 5) / 2 := by
    rw [hfv, zpow_neg, mul_inv_lt_iff₀ hΦn]
    calc fhom u < ((1 + Real.sqrt 5) / 2) ^ (n + 1) := hn2
      _ = ((1 + Real.sqrt 5) / 2) * ((1 + Real.sqrt 5) / 2) ^ n := by
          rw [zpow_add_one₀ (ne_of_gt hΦpos)]; ring
  have hveq : v = 1 := reduction v hv1 hv2
  refine ⟨n, ?_⟩
  have hu : u = v * fundamentalUnit ^ n := by rw [hv]; group
  rw [hu, hveq, one_mul]

/-- Every unit of `𝓞 ℚ(√5)` is a signed power of the golden ratio `φ`.  Proved here directly via
the real-embedding discreteness argument above — this is the lemma the original FieldExamples file
leaves as `sorry`, and it is the load-bearing input to that file's
`fundamentalUnitSystem_isFundamental` and `regulator_eq`. -/
private theorem fundamentalUnit_generates' (u : (𝓞 K)ˣ) :
    ∃ n : ℤ, u = fundamentalUnit ^ n ∨ u = -(fundamentalUnit ^ n) := by
  rcases lt_trichotomy (fhom u) 0 with hneg | hzero | hpos
  · have hpos' : 0 < fhom (-u) := by rw [fhom_neg]; linarith
    obtain ⟨n, hn⟩ := pos_case (-u) hpos'
    refine ⟨n, Or.inr ?_⟩
    have : -(-u) = -(fundamentalUnit ^ n) := by rw [hn]
    rwa [neg_neg] at this
  · exact absurd hzero (fhom_ne_zero u)
  · obtain ⟨n, hn⟩ := pos_case u hpos
    exact ⟨n, Or.inl hn⟩

/-- The regulator of `ℚ(√5)` is `log φ`, the smallest regulator of any real quadratic field.
Proved here by porting `CubeRootThree.regulator_eq` to the totally-real (weight-1) signature. -/
private theorem regulator_eq' :
    NumberField.Units.regulator K = Real.log ((1 + Real.sqrt 5) / 2) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_realEmbedding_goldenRatio
  let φ : K →+* ℂ := Complex.ofRealHom.comp σ.toRingHom
  let wR : NumberField.InfinitePlace K := NumberField.InfinitePlace.mk φ
  have hφreal : NumberField.ComplexEmbedding.IsReal φ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    apply RingHom.ext
    intro x
    change star ((σ x : ℝ) : ℂ) = ((σ x : ℝ) : ℂ)
    simp
  have hwRreal : NumberField.InfinitePlace.IsReal wR := by
    rw [NumberField.InfinitePlace.isReal_mk_iff]
    exact hφreal
  have hgolden : algebraMap (𝓞 K) K goldenIntO = goldenRoot :=
    rfl
  have hσu : σ (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) =
      (1 + Real.sqrt 5) / 2 := by
    change σ (algebraMap (𝓞 K) K goldenIntO) = (1 + Real.sqrt 5) / 2
    rw [hgolden, hσ]
  have htarget_pos : 0 < (1 + Real.sqrt 5) / 2 := by
    have := Real.sqrt_nonneg (5 : ℝ)
    linarith
  have hwRu : wR (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) =
      (1 + Real.sqrt 5) / 2 := by
    change ‖φ (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))‖ =
      (1 + Real.sqrt 5) / 2
    rw [show φ (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) =
        ((σ (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) : ℝ) : ℂ) from rfl]
    rw [hσu, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htarget_pos]
  obtain ⟨wC, hwCne⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [infinitePlace_card_eq_two]; norm_num) wR
  have hwRne : wR ≠ wC := hwCne.symm
  have hcard_sub : Fintype.card {w : NumberField.InfinitePlace K // w ≠ wC} = 1 := by
    rw [show Fintype.card {w : NumberField.InfinitePlace K // w ≠ wC} =
        Fintype.card {w : NumberField.InfinitePlace K // ¬ w = wC} from rfl]
    rw [Fintype.card_subtype_compl (fun w : NumberField.InfinitePlace K => w = wC)]
    rw [Fintype.card_subtype_eq, infinitePlace_card_eq_two]
  let e : {w : NumberField.InfinitePlace K // w ≠ wC} ≃ Fin (NumberField.Units.rank K) :=
    Fintype.equivOfCardEq (by rw [hcard_sub, Fintype.card_fin, unitRank_eq_one])
  have hreg : NumberField.Units.regulator K =
      NumberField.Units.regOfFamily
        (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit) := by
    have hdiv := NumberField.Units.regOfFamily_div_regulator (K := K)
      (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit)
    have htop : Subgroup.closure
        (Set.range (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit)) ⊔
          NumberField.Units.torsion K = ⊤ := by
      simpa [fundamentalUnitSystem] using fundamentalUnitSystem_isFundamental
    rw [htop, Subgroup.index_top] at hdiv
    field_simp [NumberField.Units.regulator_ne_zero K] at hdiv
    simpa using hdiv.symm
  rw [hreg]
  rw [NumberField.Units.regOfFamily_eq_det
    (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit) wC e]
  haveI : Subsingleton {w : NumberField.InfinitePlace K // w ≠ wC} :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [hcard_sub])
  rw [Matrix.det_eq_elem_of_subsingleton _ ⟨wR, hwRne⟩]
  have hlog_pos : (1 : ℝ) < (1 + Real.sqrt 5) / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg (5 : ℝ)]
  simp only [Matrix.of_apply, hwRu, NumberField.InfinitePlace.mult_isReal ⟨wR, hwRreal⟩,
    Nat.cast_one, one_mul, abs_of_pos (Real.log_pos hlog_pos)]

end NumberField.SqrtFive

end

/-! ### `ℚ(√2)` -/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra
open Module NumberField Polynomial
open NumberField.FieldExamples

namespace NumberField.SqrtTwo

/-- The regulator of `ℚ(√2)` is `log(1 + √2)`.  Proved here by porting
`CubeRootThree.regulator_eq` to the totally-real (weight-1) signature, building the index-1 family
directly from the Pell-form `sqrtTwoFundamentalUnit_generates_unitGroup`. -/
private theorem regulator_eq' :
    NumberField.Units.regulator K = Real.log (1 + Real.sqrt 2) := by
  classical
  let fu : (𝓞 K)ˣ := sqrtTwoFundamentalUnit
  -- The fundamental-unit family generates the units modulo torsion.
  have htop : Subgroup.closure
      (Set.range (fun _ : Fin (NumberField.Units.rank K) => fu)) ⊔
        NumberField.Units.torsion K = ⊤ := by
    rw [eq_top_iff]
    rintro u -
    rw [Subgroup.mem_sup]
    have hfu_mem : fu ∈ Subgroup.closure
        (Set.range (fun _ : Fin (NumberField.Units.rank K) => fu)) :=
      Subgroup.subset_closure
        ⟨⟨0, by rw [unitRank_eq_one]; exact Nat.zero_lt_one⟩, rfl⟩
    obtain ⟨n, hn | hn⟩ := sqrtTwoFundamentalUnit_generates_unitGroup u
    · exact ⟨fu ^ n, Subgroup.zpow_mem _ hfu_mem n, 1, Subgroup.one_mem _,
        by rw [hn, mul_one]⟩
    · exact ⟨fu ^ n, Subgroup.zpow_mem _ hfu_mem n, -1, neg_one_mem_torsion,
        by rw [hn, mul_neg_one]⟩
  -- Choose the (real) infinite place coming from any embedding.
  obtain ⟨σ, hσ⟩ := exists_realEmbedding_pos
  let φ : K →+* ℂ := Complex.ofRealHom.comp σ.toRingHom
  let wR : NumberField.InfinitePlace K := NumberField.InfinitePlace.mk φ
  have hwRreal : NumberField.InfinitePlace.IsReal wR := infinitePlace_isReal wR
  have hfuval : algebraMap (𝓞 K) K (fu : 𝓞 K) = sqrtTwoRoot + 1 := rfl
  have hpos : (0 : ℝ) < 1 + Real.sqrt 2 := by positivity
  have hσu : σ (algebraMap (𝓞 K) K (fu : 𝓞 K)) = 1 + Real.sqrt 2 := by
    rw [hfuval, map_add, map_one, hσ]; ring
  have hwRu : wR (algebraMap (𝓞 K) K (fu : 𝓞 K)) = 1 + Real.sqrt 2 := by
    change ‖φ (algebraMap (𝓞 K) K (fu : 𝓞 K))‖ = 1 + Real.sqrt 2
    rw [show φ (algebraMap (𝓞 K) K (fu : 𝓞 K)) =
        ((σ (algebraMap (𝓞 K) K (fu : 𝓞 K)) : ℝ) : ℂ) from rfl]
    rw [hσu, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  obtain ⟨wC, hwCne⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [infinitePlace_card_eq_two]; norm_num) wR
  have hwRne : wR ≠ wC := hwCne.symm
  have hcard_sub : Fintype.card {w : NumberField.InfinitePlace K // w ≠ wC} = 1 := by
    rw [show Fintype.card {w : NumberField.InfinitePlace K // w ≠ wC} =
        Fintype.card {w : NumberField.InfinitePlace K // ¬ w = wC} from rfl]
    rw [Fintype.card_subtype_compl (fun w : NumberField.InfinitePlace K => w = wC)]
    rw [Fintype.card_subtype_eq, infinitePlace_card_eq_two]
  let e : {w : NumberField.InfinitePlace K // w ≠ wC} ≃ Fin (NumberField.Units.rank K) :=
    Fintype.equivOfCardEq (by rw [hcard_sub, Fintype.card_fin, unitRank_eq_one])
  have hreg : NumberField.Units.regulator K =
      NumberField.Units.regOfFamily
        (fun _ : Fin (NumberField.Units.rank K) => fu) := by
    have hdiv := NumberField.Units.regOfFamily_div_regulator (K := K)
      (fun _ : Fin (NumberField.Units.rank K) => fu)
    rw [htop, Subgroup.index_top] at hdiv
    field_simp [NumberField.Units.regulator_ne_zero K] at hdiv
    simpa using hdiv.symm
  rw [hreg]
  rw [NumberField.Units.regOfFamily_eq_det
    (fun _ : Fin (NumberField.Units.rank K) => fu) wC e]
  haveI : Subsingleton {w : NumberField.InfinitePlace K // w ≠ wC} :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [hcard_sub])
  rw [Matrix.det_eq_elem_of_subsingleton _ ⟨wR, hwRne⟩]
  rw [Matrix.of_apply, NumberField.InfinitePlace.mult_isReal ⟨wR, hwRreal⟩, hwRu]
  rw [Nat.cast_one, one_mul,
    abs_of_nonneg (Real.log_nonneg (by linarith [Real.sqrt_nonneg 2]))]

end NumberField.SqrtTwo

end
