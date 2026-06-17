/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.Euclidean
import XYin.NumberField.FieldExamples.CyclotomicFive.Euclidean
import XYin.NumberField.FieldExamples.CyclotomicEight.Euclidean

/-!
# Workbench: attempts at the six remaining `FieldExamples` `sorry`s

This file is a **non-invasive** workspace, *outside* the `FieldExamples` folder, in which the six
remaining `sorry`s of `FieldExamples` are restated with primed (`'`), `private` names and attempted
independently. Nothing here is imported by, or affects, any file inside `FieldExamples`.

The six targets fall into two mathematical classes, one per field of
`{ℚ(∛3), ℚ(ζ₅), ℚ(ζ₈)}` (the other example fields are already `sorry`-free):

* `fundamentalUnitSystem_isFundamental'` — the displayed unit together with torsion generates the
  whole unit group (i.e. it is genuinely fundamental, not a proper power times a root of unity).

* `normEuclidean'` — the ring of integers is norm-Euclidean.

The corresponding live statements are
`NumberField.{CubeRootThree,CyclotomicFive,CyclotomicEight}.{fundamentalUnitSystem_isFundamental,
normEuclidean}`. The primed copies here let us iterate without touching the canonical files; once a
proof is complete it can be ported back verbatim.
-/

noncomputable section

open Module Polynomial
open NumberField.FieldExamples
open scoped NumberField nonZeroDivisors

/-! ### `ℚ(∛3)` -/

namespace NumberField.CubeRootThree

/-! #### Skeleton for `fundamentalUnitSystem_isFundamental'` (port of the proven SqrtFive route).

Source template: `NumberField.SqrtFive.fundamentalUnit_generates` and its helper chain
(`SqrtFive/Units.lean:258-464`), proved sorry-free. The chain is: a real embedding `reEmb`, the
induced `fhom : (𝓞 K)ˣ →* ℝ`, integral-basis coordinates, a window-reduction into `[1, Λ)`, a
`minimality`/`reduction` leaf forcing the only window unit to be `1`, then `pos_case` and the sign
trichotomy. The single genuine number-theoretic gap is `reduction` (the cubic analog of SqrtFive's
`minimality`), which needs the complex place to bound the off-real coordinates. -/

/-- A fixed real embedding `θ ↦ ∛3`, from `exists_realEmbedding_cubeRootThree`. -/
private noncomputable def reEmb : K →ₐ[ℚ] ℝ :=
  exists_realEmbedding_cubeRootThree.choose

private theorem reEmb_root : reEmb cubeRootThree = (3 : ℝ) ^ ((1 : ℝ) / 3) :=
  exists_realEmbedding_cubeRootThree.choose_spec

/-- The real embedding as a monoid homomorphism on the unit group. -/
private noncomputable def fhom : (𝓞 K)ˣ →* ℝ :=
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

/-- Real value of the displayed fundamental unit `θ² − 2`: numerically `∛9 − 2 ≈ 0.080`. -/
private theorem fhom_fund : fhom fundamentalUnit = (3 : ℝ) ^ ((2 : ℝ) / 3) - 2 := by
  rw [fhom_apply, show ((fundamentalUnit : (𝓞 K)ˣ) : 𝓞 K) = thetaInt ^ 2 - 2 from rfl]
  have ht : algebraMap (𝓞 K) K thetaInt = cubeRootThree := rfl
  simp only [map_sub, map_pow, map_ofNat, ht, reEmb_root]
  rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- The real value `Λ` of the generator `(θ²−2)⁻¹ = 2θ²+3θ+4`, numerically `≈ 12.48`. -/
private theorem fhom_fund_inv_val : fhom fundamentalUnit⁻¹ =
    4 + 3 * (3 : ℝ) ^ ((1 : ℝ) / 3) + 2 * ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [fhom_apply, show ((fundamentalUnit⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
    = 2 * thetaInt ^ 2 + 3 * thetaInt + 4 from rfl]
  have ht : algebraMap (𝓞 K) K thetaInt = cubeRootThree := rfl
  simp only [map_add, map_mul, map_pow, map_ofNat, ht, reEmb_root]; ring

/-- Every element of `𝓞 K = ℤ[θ]` is `a·1 + b·θ + c·θ²` with `a, b, c ∈ ℤ`
(from `mem_adjoin_iff` + `integralClosure_eq_adjoin`). -/
private theorem exists_coords (z : 𝓞 K) :
    ∃ a b c : ℤ, z = a • (1 : 𝓞 K) + b • thetaInt + c • thetaInt ^ 2 := by
  have hint : IsIntegral ℤ (algebraMap (𝓞 K) K z) := z.2
  have hmem : algebraMap (𝓞 K) K z ∈ Algebra.adjoin ℤ ({cubeRootThree} : Set K) := by
    rw [← integralClosure_eq_adjoin]; exact hint
  obtain ⟨a, b, c, habc⟩ := (mem_adjoin_iff _).mp hmem
  refine ⟨a, b, c, ?_⟩
  apply IsFractionRing.injective (𝓞 K) K
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_one]
  have ht : algebraMap (𝓞 K) K thetaInt = cubeRootThree := rfl
  rw [ht, map_pow, ht]; exact habc

private theorem reEmb_coord (a b c : ℤ) :
    reEmb (algebraMap (𝓞 K) K (a • (1 : 𝓞 K) + b • thetaInt + c • thetaInt ^ 2)) =
      (a : ℝ) + b * (3 : ℝ) ^ ((1 : ℝ) / 3) + c * ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
  have ht : algebraMap (𝓞 K) K thetaInt = cubeRootThree := rfl
  simp only [map_add, map_mul, map_pow, map_intCast, zsmul_eq_mul, map_one, ht, reEmb_root]
  ring

set_option maxHeartbeats 2000000 in -- finite geometry-of-numbers search (~315 cases)
/-- THE GENUINE GAP, NOW PROVED (cubic analog of `SqrtFive.minimality`/`reduction`): the only unit
whose real embedding value lies in the window `[1, Λ)` is `1`. The off-real coordinates are bounded
without the complex embedding: the norm factors over `ℝ` as `v · Q = N` with
`Q = ((2a−bs−cs²)/2)² + (3/4)(bs−cs²)²` (a sum of two squares `= |τ(u)|²`), so `Q ≥ 0`,
`N = +1`, `Q = 1/v ≤ 1`, which bounds `a,b,c` to a finite box; a search over
`a³+3b³+9c³−9abc = 1` finishes (the only window unit `≠ 1` would be `(θ²−2)⁻¹`, excluded by
the strict `< Λ`). -/
private theorem reduction (u : (𝓞 K)ˣ) (h1 : 1 ≤ fhom u)
    (h2 : fhom u < fhom fundamentalUnit⁻¹) : u = 1 := by
  obtain ⟨a, b, c, habc⟩ := exists_coords (u : 𝓞 K)
  have hv : fhom u = (a : ℝ) + b * (3 : ℝ) ^ ((1 : ℝ) / 3)
      + c * ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by rw [fhom_apply, habc, reEmb_coord]
  have hunit : IsUnit (a • (1 : 𝓞 K) + b • thetaInt + c • thetaInt ^ 2) := habc ▸ u.isUnit
  have hNor := (isUnit_iff_normForm a b c).mp hunit
  rw [fhom_fund_inv_val] at h2
  rw [hv] at h1 h2
  set s : ℝ := (3 : ℝ) ^ ((1 : ℝ) / 3) with hsdef
  have hspos : 0 < s := Real.rpow_pos_of_pos (by norm_num) _
  have hsc : s ^ 3 = 3 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hslo : (1.442 : ℝ) < s := by nlinarith [hsc, hspos, sq_nonneg s, sq_nonneg (s - 1.442)]
  have hshi : s < 1.4423 := by nlinarith [hsc, hspos, sq_nonneg s, sq_nonneg (s - 1.4423)]
  have hs2lo : (2.079 : ℝ) < s ^ 2 := by nlinarith [hslo, sq_nonneg (s - 1.442)]
  have hs2hi : s ^ 2 < 2.0803 := by nlinarith [hshi, hspos, sq_nonneg (s - 1.4423)]
  set Q : ℝ := (a : ℝ) ^ 2 - 3 * b * c + (3 * c ^ 2 - a * b) * s + (b ^ 2 - a * c) * s ^ 2
    with hQdef
  have hfactR : ((a : ℝ) + b * s + c * s ^ 2) * Q
      = (a : ℝ) ^ 3 + 3 * b ^ 3 + 9 * c ^ 3 - 9 * a * b * c := by
    rw [hQdef]
    linear_combination
      (c * (b ^ 2 - a * c) * s + b * (b ^ 2 - a * c) + c * (3 * c ^ 2 - a * b)) * hsc
  have hQsos : Q = ((2 * a - b * s - c * s ^ 2) / 2) ^ 2 + (3 / 4) * (b * s - c * s ^ 2) ^ 2 := by
    rw [hQdef]; linear_combination (b * c - c ^ 2 * s) * hsc
  have hvpos : 0 < (a : ℝ) + b * s + c * s ^ 2 := by linarith
  have hQnn : 0 ≤ Q := by rw [hQsos]; positivity
  have hN : a ^ 3 + 3 * b ^ 3 + 9 * c ^ 3 - 9 * a * b * c = 1 := by
    rcases hNor with h | h
    · exact h
    · exfalso
      have hRneg : (a : ℝ) ^ 3 + 3 * b ^ 3 + 9 * c ^ 3 - 9 * a * b * c = -1 := by exact_mod_cast h
      nlinarith [hfactR, mul_nonneg hvpos.le hQnn, hRneg]
  have hNr : (a : ℝ) ^ 3 + 3 * b ^ 3 + 9 * c ^ 3 - 9 * a * b * c = 1 := by exact_mod_cast hN
  have hfact : ((a : ℝ) + b * s + c * s ^ 2) * Q = 1 := by rw [hfactR, hNr]
  have hQle1 : Q ≤ 1 := by nlinarith [hfact, h1, hQnn]
  have hRe2 : (2 * (a : ℝ) - b * s - c * s ^ 2) ^ 2 ≤ 4 := by
    nlinarith [hQsos, hQle1, sq_nonneg (b * s - c * s ^ 2)]
  have hIm2 : ((b : ℝ) * s - c * s ^ 2) ^ 2 ≤ 4 / 3 := by
    nlinarith [hQsos, hQle1, sq_nonneg (2 * (a : ℝ) - b * s - c * s ^ 2)]
  have hRe_hi : 2 * (a : ℝ) - b * s - c * s ^ 2 ≤ 2 := by
    nlinarith [hRe2, sq_nonneg (2 * (a : ℝ) - b * s - c * s ^ 2 - 2)]
  have hRe_lo : -2 ≤ 2 * (a : ℝ) - b * s - c * s ^ 2 := by
    nlinarith [hRe2, sq_nonneg (2 * (a : ℝ) - b * s - c * s ^ 2 + 2)]
  have hD_hi : (b : ℝ) * s - c * s ^ 2 ≤ 2 := by
    nlinarith [hIm2, sq_nonneg ((b : ℝ) * s - c * s ^ 2 - 2)]
  have hD_lo : -2 ≤ (b : ℝ) * s - c * s ^ 2 := by
    nlinarith [hIm2, sq_nonneg ((b : ℝ) * s - c * s ^ 2 + 2)]
  have ha_hi : (a : ℝ) < 5 := by linarith [hRe_hi, h2, hshi, hs2hi]
  have ha_lo : (-1 : ℝ) < a := by linarith [hRe_lo, h1]
  have ha_hi' : a ≤ 4 := by have : a < 5 := (by exact_mod_cast ha_hi); omega
  have ha_lo' : 0 ≤ a := by have : -1 < a := (by exact_mod_cast ha_lo); omega
  have hbs_hi : (b : ℝ) * s < 8 := by linarith [h2, hD_hi, ha_lo', hshi, hs2hi]
  have hbs_lo : (-3 : ℝ) < (b : ℝ) * s := by linarith [h1, hD_lo, ha_hi']
  have hcs_hi : (c : ℝ) * s ^ 2 < 8 := by linarith [h2, hD_lo, ha_lo', hshi, hs2hi]
  have hcs_lo : (-3 : ℝ) < (c : ℝ) * s ^ 2 := by linarith [h1, hD_hi, ha_hi']
  have hb_hi : (b : ℝ) < 6 := by nlinarith [hbs_hi, hslo, hspos]
  have hb_lo : (-3 : ℝ) < b := by nlinarith [hbs_lo, hslo, hspos]
  have hc_hi : (c : ℝ) < 4 := by nlinarith [hcs_hi, hs2lo]
  have hc_lo : (-3 : ℝ) < c := by nlinarith [hcs_lo, hs2lo]
  have hb_hi' : b ≤ 5 := by have : b < 6 := (by exact_mod_cast hb_hi); omega
  have hb_lo' : -2 ≤ b := by have : -3 < b := (by exact_mod_cast hb_lo); omega
  have hc_hi' : c ≤ 3 := by have : c < 4 := (by exact_mod_cast hc_hi); omega
  have hc_lo' : -2 ≤ c := by have : -3 < c := (by exact_mod_cast hc_lo); omega
  suffices hsol : a = 1 ∧ b = 0 ∧ c = 0 by
    obtain ⟨ha, hb, hc⟩ := hsol
    apply Units.ext
    rw [habc, ha, hb, hc]; simp
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    first
      | (revert hN; decide)
      | (exfalso; push_cast at h2; linarith)

/-- Every unit with positive real value is a power of the fundamental unit. Window-reduction:
divide by powers of the generator `g = fund⁻¹` (real value `Λ > 1`) into the window `[1, Λ)`,
where `reduction` forces the result to `1`. -/
private theorem pos_case (u : (𝓞 K)ˣ) (hpos : 0 < fhom u) :
    ∃ n : ℤ, u = fundamentalUnit ^ n := by
  have hΛpos : 0 < fhom fundamentalUnit⁻¹ := by
    rw [fhom_fund_inv_val]
    have hs : (0 : ℝ) < (3 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hΛ1 : 1 < fhom fundamentalUnit⁻¹ := by
    rw [fhom_fund_inv_val]
    have hs : (0 : ℝ) < (3 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith [hs]
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hpos hΛ1
  set g : (𝓞 K)ˣ := fundamentalUnit⁻¹ with hgdef
  set v : (𝓞 K)ˣ := u * g ^ (-n) with hvdef
  have hfv : fhom v = fhom u * (fhom g) ^ (-n) := by rw [hvdef, map_mul, map_zpow]
  have hΛn : 0 < (fhom g) ^ n := zpow_pos hΛpos n
  have hv1 : 1 ≤ fhom v := by rw [hfv, zpow_neg, le_mul_inv_iff₀ hΛn, one_mul]; exact hn1
  have hv2 : fhom v < fhom fundamentalUnit⁻¹ := by
    rw [hfv, zpow_neg, mul_inv_lt_iff₀ hΛn]
    calc fhom u < (fhom g) ^ (n + 1) := hn2
      _ = fhom fundamentalUnit⁻¹ * (fhom g) ^ n := by
          rw [hgdef, zpow_add_one₀ (ne_of_gt hΛpos)]; ring
  have hveq : v = 1 := reduction v hv1 hv2
  refine ⟨-n, ?_⟩
  have hu : u = v * g ^ n := by rw [hvdef]; group
  rw [hu, hveq, one_mul, hgdef, inv_zpow, zpow_neg]

/-- Every unit is a signed power of the fundamental unit (sign trichotomy on `fhom`). -/
private theorem fundamentalUnit_generates (u : (𝓞 K)ˣ) :
    ∃ n : ℤ, u = fundamentalUnit ^ n ∨ u = -(fundamentalUnit ^ n) := by
  rcases lt_trichotomy (fhom u) 0 with hneg | hzero | hpos
  · obtain ⟨n, hn⟩ := pos_case (-u) (by rw [fhom_neg]; linarith)
    refine ⟨n, Or.inr ?_⟩
    have : -(-u) = -(fundamentalUnit ^ n) := by rw [hn]
    rwa [neg_neg] at this
  · exact absurd hzero (fhom_ne_zero u)
  · obtain ⟨n, hn⟩ := pos_case u hpos
    exact ⟨n, Or.inl hn⟩

/-- Workbench copy of `CubeRootThree.fundamentalUnitSystem_isFundamental`, reduced to
`fundamentalUnit_generates` exactly as in SqrtFive. -/
private theorem fundamentalUnitSystem_isFundamental' :
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have hfund : fundamentalUnit ∈ Subgroup.closure (Set.range fundamentalUnitSystem) :=
    Subgroup.subset_closure ⟨⟨0, by rw [unitRank_eq_one]; exact Nat.zero_lt_one⟩, rfl⟩
  have hneg_tor : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K := by
    change IsOfFinOrder _
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩
  rw [Subgroup.mem_sup]
  obtain ⟨n, hn | hn⟩ := fundamentalUnit_generates u
  · exact ⟨fundamentalUnit ^ n, Subgroup.zpow_mem _ hfund n, 1, Subgroup.one_mem _, by rw [hn, mul_one]⟩
  · refine ⟨fundamentalUnit ^ n, Subgroup.zpow_mem _ hfund n, -1, hneg_tor, ?_⟩
    rw [hn]
    apply Units.ext
    change ((fundamentalUnit ^ n : (𝓞 K)ˣ) : 𝓞 K) * (-1 : 𝓞 K)
      = -((fundamentalUnit ^ n : (𝓞 K)ˣ) : 𝓞 K)
    ring

/-! #### Skeleton for `normEuclidean'` — hand-built covering of the fundamental domain.

Reduce (via `Common.abs_intNorm_lt_of_abs_norm_le`) to: every rational target `(f,g,h)` has an
integer point `(a,b,c)` with `|N(f−a, g−b, h−c)| < 1` for the cubic form
`N(x,y,z) = x³+3y³+9z³−9xyz`. The naive central region `|·| ≤ 1/3` is handled (`normForm_central`);
the obstruction is the outer shell, which needs a per-region lattice choice. -/

/-- Proven safe region: on the central cube the cubic form is `< 1` (numerically `sup ≈ 0.72`). -/
private theorem normForm_central (f g h : ℚ)
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

/-- The Euclidean-minimum covering bound: every rational target has a lattice point of value `< 1`.
THE GENUINE GAP — needs the per-region (8-corner) lattice choice, not uniform rounding. -/
private theorem euclidean_min (f g h : ℚ) :
    ∃ a b c : ℤ, |(f - a) ^ 3 + 3 * (g - b) ^ 3 + 9 * (h - c) ^ 3
      - 9 * (f - a) * (g - b) * (h - c)| < 1 := by
  sorry

/-- Workbench copy of `CubeRootThree.normEuclidean`. -/
private theorem normEuclidean' (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry

end NumberField.CubeRootThree

/-! ### `ℚ(ζ₅)` -/

namespace NumberField.CyclotomicFive

/-- Workbench copy of `CyclotomicFive.fundamentalUnitSystem_isFundamental`. -/
private theorem fundamentalUnitSystem_isFundamental' :
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K = ⊤ := by
  sorry

/-- Workbench copy of `CyclotomicFive.normEuclidean`. -/
private theorem normEuclidean' (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry

end NumberField.CyclotomicFive

/-! ### `ℚ(ζ₈)` -/

namespace NumberField.CyclotomicEight

/-- Workbench copy of `CyclotomicEight.fundamentalUnitSystem_isFundamental`. -/
private theorem fundamentalUnitSystem_isFundamental' :
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K = ⊤ := by
  sorry

/-- Workbench copy of `CyclotomicEight.normEuclidean`. -/
private theorem normEuclidean' (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry

end NumberField.CyclotomicEight
