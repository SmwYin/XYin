/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NFIL.NumberField.FieldExamples.CubeRootThree.ClassGroup

/-!
# `ℚ(∛3)` Units

Unit group, torsion, fundamental units, Dirichlet rank, regulator, and abstract unit-group
structure.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Units
-/

noncomputable section

open Module Polynomial
open NumberField.FieldExamples
open scoped NumberField nonZeroDivisors

namespace NumberField.CubeRootThree

/-- A torsion generator of `𝓞 Kˣ`, mathematically `-1`. -/
abbrev torsionGenerator : (𝓞 K)ˣ := -1

/-- The concrete torsion units `{1, -1}`. -/
def torsionUnits : Set ((𝓞 K)ˣ) := {u | ∃ k : Fin 2, u = torsionGenerator ^ k.val}

/-- The torsion subgroup of `𝓞 Kˣ` is exactly `{1, -1}`: a field of odd degree over `ℚ` has a
real embedding, so its only roots of unity are `±1`. -/
theorem torsionUnits_eq : {u : (𝓞 K)ˣ | IsOfFinOrder u} = torsionUnits := by
  have hodd : Odd (Module.finrank ℚ K) := by rw [degree_eq_three]; decide
  ext u
  simp only [Set.mem_setOf_eq, torsionUnits]
  constructor
  · intro hu
    have hmem : u ∈ NumberField.Units.torsion K := (CommGroup.mem_torsion _).mpr hu
    rcases NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank hodd ⟨u, hmem⟩ with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  · rintro ⟨k, rfl⟩
    have hgen : IsOfFinOrder (torsionGenerator) := by
      rw [isOfFinOrder_iff_pow_eq_one]; exact ⟨2, by norm_num, by rw [neg_one_sq]⟩
    exact hgen.pow

/-- The torsion subgroup of `𝓞 Kˣ` has order `2`. -/
theorem torsionOrder_eq_two : NumberField.Units.torsionOrder K = 2 := by
  apply NumberField.Units.torsionOrder_eq_two_of_odd_finrank
  rw [degree_eq_three]; decide

/-- The Dirichlet unit rank of `ℚ(∛3)` is `1`: the signature is `(r₁, r₂) = (1, 1)`, so the
rank is `r₁ + r₂ - 1 = 1`. -/
theorem unitRank_eq_one : NumberField.Units.rank K = 1 := by
  have hsig : NumberField.InfinitePlace.nrRealPlaces K +
      2 * NumberField.InfinitePlace.nrComplexPlaces K = 3 := by
    rw [← degree_eq_three]; exact NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 := by
    rw [Ne, NumberField.nrComplexPlaces_eq_zero_iff]; exact not_totallyReal
  have hcard : Fintype.card (NumberField.InfinitePlace K) = 2 := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]; omega
  rw [NumberField.Units.rank, hcard]

/-- A fundamental unit of `𝓞 K`, mathematically `θ² - 2` (of norm `1`), with explicit inverse
`2θ² + 3θ + 4`. -/
noncomputable def fundamentalUnit : (𝓞 K)ˣ where
  val := thetaInt ^ 2 - 2
  inv := 2 * thetaInt ^ 2 + 3 * thetaInt + 4
  val_inv := by have h := thetaInt_cube; linear_combination (2 * thetaInt + 3) * h
  inv_val := by have h := thetaInt_cube; linear_combination (2 * thetaInt + 3) * h

/-- The system of fundamental units for the rank-`1` unit group: the single unit `θ² - 2`. -/
noncomputable def fundamentalUnitSystem : Fin (NumberField.Units.rank K) → (𝓞 K)ˣ :=
  fun _ => fundamentalUnit

/-! ### Real-embedding window-reduction machinery for `fundamentalUnit_generates`.

A self-contained argument inside `ℝ` (no Artin/Minkowski regulator bound, which mathlib lacks),
ported from the totally-real `SqrtFive` template to the signature-`(1,1)` cubic field: the real
embedding `θ ↦ ∛3` induces `fhom : (𝓞 K)ˣ →* ℝ`; every positive unit is reduced into the window
`[1, Λ)` (`Λ = ∛9 − 2`'s inverse `≈ 12.48`) by a power of the fundamental unit, and the only unit
in that window is `1`. The off-real coordinates are bounded without the complex embedding: the
cubic norm factors over `ℝ` as `v · Q = N` with `Q` a sum of two squares (`= |τ(u)|²`). -/

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

/-- Every element of `𝓞 K = ℤ[θ]` is `a·1 + b·θ + c·θ²` with `a, b, c ∈ ℤ`. -/
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
/-- The only unit whose real embedding value lies in the window `[1, Λ)` is `1`. The off-real
coordinates are bounded without the complex embedding: the cubic norm factors over `ℝ` as
`v · Q = N` with `Q = ((2a−bs−cs²)/2)² + (3/4)(bs−cs²)²` (a sum of two squares `= |τ(u)|²`), so
`Q ≥ 0` forces `N = +1` and `Q = 1/v ≤ 1`, bounding `a,b,c` to a finite box; a search over
`a³+3b³+9c³−9abc = 1` finishes (the only window unit `≠ 1` would be `(θ²−2)⁻¹`, excluded by the
strict `< Λ`). -/
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

/-- Every unit of `𝓞 ℚ(∛3)` is a signed power of the fundamental unit `θ² − 2`. Proved via the
real-embedding window-reduction above, bypassing the (missing) Artin/Minkowski regulator bound. -/
theorem fundamentalUnit_generates (u : (𝓞 K)ˣ) :
    ∃ n : ℤ, u = fundamentalUnit ^ n ∨ u = -(fundamentalUnit ^ n) := by
  rcases lt_trichotomy (fhom u) 0 with hneg | hzero | hpos
  · obtain ⟨n, hn⟩ := pos_case (-u) (by rw [fhom_neg]; linarith)
    refine ⟨n, Or.inr ?_⟩
    have : -(-u) = -(fundamentalUnit ^ n) := by rw [hn]
    rwa [neg_neg] at this
  · exact absurd hzero (fhom_ne_zero u)
  · obtain ⟨n, hn⟩ := pos_case u hpos
    exact ⟨n, Or.inl hn⟩

/-- The displayed family is a system of fundamental units: together with roots of unity, it
generates all units of `𝓞 K`. In rank `1` this says exactly that `θ² - 2` is a fundamental
unit (not a proper power times torsion). -/
theorem fundamentalUnitSystem_isFundamental :
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
  · exact ⟨fundamentalUnit ^ n, Subgroup.zpow_mem _ hfund n, 1, Subgroup.one_mem _,
      by rw [hn, mul_one]⟩
  · refine ⟨fundamentalUnit ^ n, Subgroup.zpow_mem _ hfund n, -1, hneg_tor, ?_⟩
    rw [hn]
    apply Units.ext
    change ((fundamentalUnit ^ n : (𝓞 K)ˣ) : 𝓞 K) * (-1 : 𝓞 K)
      = -((fundamentalUnit ^ n : (𝓞 K)ˣ) : 𝓞 K)
    ring

/-- Equivalently, every unit is a root of unity times a power of `θ² - 2`. -/
theorem unit_eq_torsion_mul_fundamentalUnit_zpow (u : (𝓞 K)ˣ) :
    ∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧ ∃ n : ℤ, u = ζ * fundamentalUnit ^ n := by
  have hu : u ∈ Subgroup.closure (Set.range fundamentalUnitSystem) ⊔
      NumberField.Units.torsion K := by
    rw [fundamentalUnitSystem_isFundamental]; trivial
  rw [Subgroup.mem_sup] at hu
  obtain ⟨x, hx, y, hy, hxy⟩ := hu
  have hrange : Set.range fundamentalUnitSystem = {fundamentalUnit} := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩; rfl
    · rintro rfl
      exact ⟨⟨0, by rw [unitRank_eq_one]; exact Nat.zero_lt_one⟩, rfl⟩
  rw [hrange, Subgroup.mem_closure_singleton] at hx
  obtain ⟨n, hn⟩ := hx
  exact ⟨y, hy, n, by rw [hn, ← hxy]; exact mul_comm x y⟩

/-- Mathlib's abstract fundamental unit `fundSystem K i₀`, together with the torsion, generates
the whole unit group (rank-one specialization of `closure_fundSystem_sup_torsion_eq_top`). -/
theorem exists_eq_torsion_mul_fundSystem_zpow (i₀ : Fin (NumberField.Units.rank K))
    (u : (𝓞 K)ˣ) :
    ∃ ζ ∈ NumberField.Units.torsion K, ∃ n : ℤ,
      u = ζ * NumberField.Units.fundSystem K i₀ ^ n := by
  haveI hsub : Subsingleton (Fin (NumberField.Units.rank K)) :=
    Fin.subsingleton_iff_le_one.mpr (by rw [unitRank_eq_one])
  have hu : u ∈ Subgroup.closure (Set.range (NumberField.Units.fundSystem K)) ⊔
      NumberField.Units.torsion K := by
    rw [NumberField.Units.closure_fundSystem_sup_torsion_eq_top]; trivial
  rw [Subgroup.mem_sup] at hu
  obtain ⟨x, hx, y, hy, hxy⟩ := hu
  have hrange : Set.range (NumberField.Units.fundSystem K) =
      {NumberField.Units.fundSystem K i₀} := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      rw [Subsingleton.elim i i₀]
      rfl
    · rintro rfl
      exact ⟨i₀, rfl⟩
  rw [hrange, Subgroup.mem_closure_singleton] at hx
  obtain ⟨n, hn⟩ := hx
  exact ⟨y, hy, n, by rw [hn, ← hxy]; exact mul_comm x y⟩

/-- A power of the abstract fundamental unit is torsion only for exponent zero: its image in
the (free) quotient modulo torsion is a basis vector. -/
theorem fundSystem_zpow_mem_torsion (i₀ : Fin (NumberField.Units.rank K)) (n : ℤ)
    (hn : NumberField.Units.fundSystem K i₀ ^ n ∈ NumberField.Units.torsion K) : n = 0 := by
  have hq : Additive.ofMul ((QuotientGroup.mk ((NumberField.Units.fundSystem K i₀) ^ n) :
      (𝓞 K)ˣ ⧸ NumberField.Units.torsion K)) = 0 := by
    rw [ofMul_eq_zero]
    exact (QuotientGroup.eq_one_iff ((NumberField.Units.fundSystem K i₀) ^ n)).mpr hn
  rw [QuotientGroup.mk_zpow, ofMul_zpow, NumberField.Units.fundSystem_mk] at hq
  letI : Module ℤ (Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K)) :=
    AddCommGroup.toIntModule (Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K))
  have hrepr := congrArg
    (fun x : Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) =>
      ((NumberField.Units.basisModTorsion K).repr x) i₀) hq
  simpa [Module.Basis.repr_self, Module.Basis.repr_self_apply] using hrepr

/-- Pointwise classification of the torsion: a torsion unit is `1` or `-1`. -/
theorem eq_one_or_neg_one_of_mem_torsion {ζ : (𝓞 K)ˣ}
    (hζ : ζ ∈ NumberField.Units.torsion K) : ζ = 1 ∨ ζ = -1 := by
  have hfin : IsOfFinOrder ζ := (CommGroup.mem_torsion _).mp hζ
  have hmem : ζ ∈ {u : (𝓞 K)ˣ | IsOfFinOrder u} := hfin
  rw [torsionUnits_eq] at hmem
  obtain ⟨k, hk⟩ := hmem
  fin_cases k
  · exact Or.inl (by simpa using hk)
  · exact Or.inr (by simpa using hk)

private theorem unitGroupStructure_bijective
    (i₀ : Fin (NumberField.Units.rank K)) (η : (𝓞 K)ˣ)
    (hη : η = NumberField.Units.fundSystem K i₀)
    (hneg_tor : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K) :
    Function.Bijective
      ((torsionPowerHom 2 (-1 : (𝓞 K)ˣ) (by rw [neg_one_sq])).coprod
        (rankOnePowerHom η)) := by
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨a, f⟩ h
    have h' : (-1 : (𝓞 K)ˣ) ^ ((Multiplicative.toAdd a).val) *
        η ^ (Multiplicative.toAdd f 0) = 1 := h
    have htor : η ^ (Multiplicative.toAdd f 0) ∈ NumberField.Units.torsion K := by
      have heq : η ^ (Multiplicative.toAdd f 0) =
          ((-1 : (𝓞 K)ˣ) ^ ((Multiplicative.toAdd a).val))⁻¹ :=
        (mul_eq_one_iff_inv_eq.mp h').symm
      rw [heq]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hneg_tor _)
    have hn0 : Multiplicative.toAdd f 0 = 0 :=
      fundSystem_zpow_mem_torsion i₀ _ (by simpa [hη] using htor)
    rw [hn0, zpow_zero, mul_one] at h'
    have ha : Multiplicative.toAdd a = 0 := by
      rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (Multiplicative.toAdd a) with
        hx | hx
      · exact hx
      · exfalso
        rw [hx, show ((1 : ZMod 2)).val = 1 from rfl, pow_one] at h'
        have hcoe : (-1 : 𝓞 K) = 1 := congrArg Units.val h'
        norm_num at hcoe
    refine Prod.ext ?_ ?_
    · exact Multiplicative.toAdd.injective ha
    · refine Multiplicative.toAdd.injective (funext fun i => ?_)
      rw [Subsingleton.elim i 0]
      exact hn0
  · intro u
    obtain ⟨ζ, hζ, n, hu⟩ := exists_eq_torsion_mul_fundSystem_zpow i₀ u
    rcases eq_one_or_neg_one_of_mem_torsion hζ with rfl | rfl
    · refine ⟨(Multiplicative.ofAdd (0 : ZMod 2), Multiplicative.ofAdd (fun _ => n)), ?_⟩
      change (-1 : (𝓞 K)ˣ) ^ ((0 : ZMod 2)).val * η ^ n = u
      rw [hη, show ((0 : ZMod 2)).val = 0 from rfl, pow_zero, hu, one_mul]
    · refine ⟨(Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (fun _ => n)), ?_⟩
      change (-1 : (𝓞 K)ˣ) ^ ((1 : ZMod 2)).val * η ^ n = u
      rw [hη, show ((1 : ZMod 2)).val = 1 from rfl, pow_one, hu]

/-- The unit group is `μ₂ × ℤ` as an abstract abelian group. -/
theorem unitGroupStructure :
    Nonempty ((𝓞 K)ˣ ≃* (Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ))) := by
  set i₀ : Fin (NumberField.Units.rank K) :=
    ⟨0, by rw [unitRank_eq_one]; exact Nat.zero_lt_one⟩ with hi₀
  set η : (𝓞 K)ˣ := NumberField.Units.fundSystem K i₀ with hη
  let ψ₁ : Multiplicative (ZMod 2) →* (𝓞 K)ˣ :=
    torsionPowerHom 2 (-1 : (𝓞 K)ˣ) (by rw [neg_one_sq])
  let ψ₂ : Multiplicative (Fin 1 → ℤ) →* (𝓞 K)ˣ :=
    rankOnePowerHom η
  let ψ : Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ) →* (𝓞 K)ˣ := ψ₁.coprod ψ₂
  have hneg_tor : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).mpr (by
      rw [isOfFinOrder_iff_pow_eq_one]; exact ⟨2, by norm_num, by rw [neg_one_sq]⟩)
  have hbij : Function.Bijective ψ := unitGroupStructure_bijective i₀ η hη hneg_tor
  exact ⟨(MulEquiv.ofBijective ψ hbij).symm⟩

/-- The regulator of `ℚ(∛3)` is `|log(∛9 - 2)| = log(2∛9 + 3∛3 + 4) ≈ 2.5246`, the covolume
of the unit lattice. This is the analytic restatement that `θ² - 2` is a fundamental unit:
the regulator equals the absolute logarithm of its image under the real embedding. -/
theorem regulator_eq :
    NumberField.Units.regulator K = |Real.log ((3 : ℝ) ^ ((2 : ℝ) / 3) - 2)| := by
  classical
  obtain ⟨σ, hσ⟩ := exists_realEmbedding_cubeRootThree
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
  have ht : algebraMap (𝓞 K) K thetaInt = cubeRootThree :=
    NumberField.RingOfIntegers.map_mk cubeRootThree cubeRootThree_integral
  have hσu : σ (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) =
      (3 : ℝ) ^ ((2 : ℝ) / 3) - 2 := by
    change σ (algebraMap (𝓞 K) K (thetaInt ^ 2 - 2)) =
      (3 : ℝ) ^ ((2 : ℝ) / 3) - 2
    simp only [map_sub, map_pow, map_ofNat, ht, hσ]
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 3)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have htarget_pos : 0 < (3 : ℝ) ^ ((2 : ℝ) / 3) - 2 := by
    have hpow : (3 : ℝ) ^ ((2 : ℝ) / 3) = (9 : ℝ) ^ ((3 : ℝ)⁻¹) := by
      rw [show ((2 : ℝ) / 3) = ((2 : ℕ) : ℝ) * (3 : ℝ)⁻¹ by norm_num]
      rw [Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3) 2 ((3 : ℝ)⁻¹)]
      norm_num
    have hlt : (2 : ℝ) < (9 : ℝ) ^ ((3 : ℝ)⁻¹) := by
      rw [Real.lt_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 2)
        (by norm_num : (0 : ℝ) ≤ 9) (by norm_num : (0 : ℝ) < 3)]
      norm_num
    nlinarith
  have hwRu : wR (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) =
      (3 : ℝ) ^ ((2 : ℝ) / 3) - 2 := by
    change ‖φ (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))‖ =
      (3 : ℝ) ^ ((2 : ℝ) / 3) - 2
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
  simp [NumberField.InfinitePlace.mult_isReal ⟨wR, hwRreal⟩, hwRu]


end NumberField.CubeRootThree
