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

/-- Blocked: needs a manual covering of the fundamental domain in the power basis `{1, θ, θ²}`
(nearest-integer rounding overflows `|N| < 1`). -/
private theorem normEuclidean' (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry

/-- Blocked: needs an Artin/Minkowski regulator lower bound to exclude `θ² - 2` being a proper
power. -/
private theorem fundamentalUnitSystem_isFundamental' :
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K = ⊤ := by
  sorry

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

/-- Blocked: the Fibonacci/Pell `a² - 5b² = ±4` bridge for the half-integral order
`ℤ[(1+√5)/2]`; mathlib only has `Zsqrtd`/`Pell` for `x² - d y² = 1`. -/
private theorem fundamentalUnit_generates' (u : (𝓞 K)ˣ) :
    ∃ n : ℤ, u = fundamentalUnit ^ n ∨ u = -(fundamentalUnit ^ n) := by
  sorry

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
