/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.ClassGroup

/-!
# `ℚ(√5)` Units

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

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open NumberField.FieldExamples

namespace NumberField.SqrtFive

/-- The golden ratio `φ` is a unit of `𝓞 K`, with inverse `φ - 1 = 1/φ`: this is the
fundamental unit of `ℚ(√5)`, the smallest fundamental unit of any real quadratic field. -/
noncomputable def fundamentalUnit : (𝓞 K)ˣ where
  val := goldenIntO
  inv := goldenIntO - 1
  val_inv := by
    rw [show goldenIntO * (goldenIntO - 1) = goldenIntO ^ 2 - goldenIntO by ring]
    rw [goldenIntO_sq]
    ring
  inv_val := by
    rw [show (goldenIntO - 1) * goldenIntO = goldenIntO ^ 2 - goldenIntO by ring]
    rw [goldenIntO_sq]
    ring

/-- A torsion generator of `𝓞 Kˣ`, mathematically `-1`. -/
abbrev torsionGenerator : (𝓞 K)ˣ := -1

/-- The concrete torsion units `{1, -1}`. -/
def torsionUnits : Set ((𝓞 K)ˣ) := {u | ∃ k : Fin 2, u = torsionGenerator ^ k.val}

private noncomputable def realEmb : K →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨(1 + Real.sqrt 5) / 2, by
    have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
    rw [show ((1 + Real.sqrt 5) / 2) * ((1 + Real.sqrt 5) / 2) =
        (3 + Real.sqrt 5) / 2 by nlinarith]
    simp
    ring⟩

/-- The torsion subgroup of `𝓞 Kˣ` is exactly `{1, -1}`. -/
theorem torsionUnits_eq : {u : (𝓞 K)ˣ | IsOfFinOrder u} = torsionUnits := by
  set e : K →+* ℝ := realEmb.toRingHom with he
  ext u
  constructor
  · intro hu
    obtain ⟨n, hn, hun⟩ := isOfFinOrder_iff_pow_eq_one.mp hu
    set x : K :=
      algebraMap (𝓞 K) K ((u : (𝓞 K)ˣ) : 𝓞 K) with hx
    have hxn : x ^ n = 1 := by
      have hval : ((u ^ n : (𝓞 K)ˣ) : 𝓞 K) = 1 := by rw [hun]; rfl
      rw [hx, ← map_pow,
        show (((u : (𝓞 K)ˣ) : 𝓞 K)) ^ n =
          ((u ^ n : (𝓞 K)ˣ) : 𝓞 K) from
          (Units.val_pow_eq_pow_val _ _).symm,
        hval, map_one]
    have hen : (e x) ^ n = 1 := by rw [← map_pow, hxn, map_one]
    have habs : |e x| = 1 := by
      have h1 : |e x| ^ n = 1 := by rw [← abs_pow, hen, abs_one]
      rcases lt_trichotomy |e x| 1 with h | h | h
      · exfalso
        have h2 := pow_lt_one₀ (abs_nonneg _) h hn.ne'
        rw [h1] at h2
        norm_num at h2
      · exact h
      · exfalso
        have h2 := one_lt_pow₀ h hn.ne'
        rw [h1] at h2
        norm_num at h2
    have hex : e x = 1 ∨ e x = -1 := abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp habs
    have hinj := IsFractionRing.injective (𝓞 K) K
    rcases hex with h | h
    · refine ⟨0, ?_⟩
      have hx1 : x = 1 := e.injective (by rw [h, map_one])
      have hu1 : ((u : (𝓞 K)ˣ) : 𝓞 K) = 1 :=
        hinj (by rw [map_one, ← hx]; exact hx1)
      rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, pow_zero]
      exact Units.ext hu1
    · refine ⟨1, ?_⟩
      have hx1 : x = -1 := e.injective (by rw [h]; simp)
      have hu1 : ((u : (𝓞 K)ˣ) : 𝓞 K) = -1 :=
        hinj (by rw [map_neg, map_one, ← hx]; exact hx1)
      rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, pow_one]
      exact Units.ext hu1
  · rintro ⟨k, rfl⟩
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, ?_⟩
    rw [← pow_mul, mul_comm, pow_mul]
    simp

/-- The torsion subgroup of `𝓞 Kˣ` has order `2`: a totally real field has only the roots of
unity `±1`. -/
theorem torsionOrder_eq_two : Units.torsionOrder K = 2 := by
  have hcard : Nat.card (NumberField.Units.torsion K) = 2 := by
    rw [Nat.card_eq_two_iff]
    have hmem1 : (1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩
    have hmemn : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K := by
      change IsOfFinOrder _
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩
    refine ⟨⟨1, hmem1⟩, ⟨-1, hmemn⟩, ?_, ?_⟩
    · intro h
      have hval := congrArg (fun z => ((z : (𝓞 K)ˣ) : 𝓞 K))
        (Subtype.ext_iff.mp h)
      simp only [Units.val_one, Units.val_neg] at hval
      have h2 := congrArg (algebraMap (𝓞 K) K) hval
      simp only [map_one, map_neg] at h2
      exact two_ne_zero (by linear_combination h2 : (2 : K) = 0)
    · ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      have hz : (z : (𝓞 K)ˣ) ∈ {u : (𝓞 K)ˣ | IsOfFinOrder u} := z.2
      rw [torsionUnits_eq] at hz
      obtain ⟨k, hk⟩ := hz
      fin_cases k
      · left
        exact Subtype.ext (by simpa using hk)
      · right
        exact Subtype.ext (by simpa using hk)
  simpa [NumberField.Units.torsionOrder] using hcard

/-- The Dirichlet unit rank of `ℚ(√5)` is `1`: the signature is `(2, 0)`, so the rank is
`r₁ + r₂ - 1 = 1`. -/
theorem unitRank_eq_one : Units.rank K = 1 := by
  rw [NumberField.Units.rank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_eq_two, nrComplexPlaces_eq_zero]

/-- The system of fundamental units for the rank-`1` unit group: the single unit `φ`. -/
noncomputable def fundamentalUnitSystem : Fin (Units.rank K) → (𝓞 K)ˣ :=
  fun _ => fundamentalUnit

/-- The golden ratio has norm `-1`. -/
theorem intNorm_goldenInt : Algebra.norm ℤ goldenIntO = -1 := by
  have h := intNorm_eq_normForm 0 1
  simpa using h

private theorem normFundamentalUnit_map :
    Units.map (Algebra.norm ℤ : (𝓞 K) →* ℤ) fundamentalUnit = (-1 : ℤˣ) := by
  apply Units.ext
  change Algebra.norm ℤ goldenIntO = (-1 : ℤ)
  exact intNorm_goldenInt

private theorem normNegOneUnit_map :
    Units.map (Algebra.norm ℤ : (𝓞 K) →* ℤ) (-1 : (𝓞 K)ˣ) = 1 := by
  apply Units.ext
  change Algebra.norm ℤ ((-1 : (𝓞 K)ˣ) : 𝓞 K) = (1 : ℤ)
  have h := intNorm_eq_normForm (-1) 0
  have hneg : (-1 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • goldenIntO =
      ((-1 : (𝓞 K)ˣ) : 𝓞 K) := by
    simp
  rw [hneg] at h
  norm_num at h
  simpa using h

private theorem even_of_negOneUnit_zpow_eq_one {n : ℤ} (h : ((-1 : ℤˣ) ^ n) = 1) :
    ∃ k : ℤ, n = 2 * k := by
  by_cases he : Even n
  · rcases he with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  · have ho : Odd n := Int.not_even_iff_odd.mp he
    change ((-1 : ℤˣ) ^ n) = (1 : ℤˣ) at h
    have hodd : ((-1 : ℤˣ) ^ n) = (-1 : ℤˣ) := Odd.neg_one_zpow (α := ℤˣ) ho
    rw [hodd] at h
    norm_num at h

private theorem normFundamentalUnit_zpow_map (n : ℤ) :
    Units.map (Algebra.norm ℤ : (𝓞 K) →* ℤ) (fundamentalUnit ^ n) =
      (-1 : ℤˣ) ^ n := by
  rw [map_zpow, normFundamentalUnit_map]
  rfl

private theorem normNegFundamentalUnit_zpow_map (n : ℤ) :
    Units.map (Algebra.norm ℤ : (𝓞 K) →* ℤ) (-(fundamentalUnit ^ n)) =
      (-1 : ℤˣ) ^ n := by
  rw [show (-(fundamentalUnit ^ n) : (𝓞 K)ˣ) =
      (-1 : (𝓞 K)ˣ) * fundamentalUnit ^ n by
    rw [neg_eq_neg_one_mul]]
  rw [map_mul, normNegOneUnit_map, one_mul, normFundamentalUnit_zpow_map]

/-- Mathlib's abstract fundamental unit `fundSystem K i₀`, together with the torsion,
generates the whole unit group. -/
theorem exists_eq_torsion_mul_fundSystem_zpow (i₀ : Fin (Units.rank K))
    (u : (𝓞 K)ˣ) :
    ∃ ζ ∈ NumberField.Units.torsion K, ∃ n : ℤ,
      u = ζ * NumberField.Units.fundSystem K i₀ ^ n := by
  haveI hsub : Subsingleton (Fin (Units.rank K)) :=
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

/-- A power of the abstract fundamental unit is torsion only for exponent zero. -/
theorem fundSystem_zpow_mem_torsion (i₀ : Fin (Units.rank K)) (n : ℤ)
    (hn : NumberField.Units.fundSystem K i₀ ^ n ∈
      NumberField.Units.torsion K) : n = 0 := by
  have hq : Additive.ofMul
      ((QuotientGroup.mk ((NumberField.Units.fundSystem K i₀) ^ n) :
        (𝓞 K)ˣ ⧸ NumberField.Units.torsion K)) = 0 := by
    rw [ofMul_eq_zero]
    exact (QuotientGroup.eq_one_iff
      ((NumberField.Units.fundSystem K i₀) ^ n)).mpr hn
  rw [QuotientGroup.mk_zpow, ofMul_zpow, NumberField.Units.fundSystem_mk] at hq
  letI : Module ℤ (Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K)) :=
    AddCommGroup.toIntModule
      (Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K))
  have hrepr := congrArg
    (fun x : Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) =>
      ((NumberField.Units.basisModTorsion K).repr x) i₀) hq
  simpa [Module.Basis.repr_self, Module.Basis.repr_self_apply] using hrepr

/-- Pointwise classification of the torsion: a torsion unit is `1` or `-1`. -/
theorem eq_one_or_neg_one_of_mem_torsion {ζ : (𝓞 K)ˣ}
    (hζ : ζ ∈ NumberField.Units.torsion K) : ζ = 1 ∨ ζ = -1 := by
  have hfin : IsOfFinOrder ζ := hζ
  have hmem : ζ ∈ {u : (𝓞 K)ˣ | IsOfFinOrder u} := hfin
  rw [torsionUnits_eq] at hmem
  obtain ⟨k, hk⟩ := hmem
  fin_cases k
  · exact Or.inl (by simpa using hk)
  · exact Or.inr (by simpa using hk)

/-! ### Real-embedding discreteness machinery for `fundamentalUnit_generates`.

A self-contained argument inside `ℝ` (NOT the `Zsqrtd`/`Pell` `x² - 5y² = 1` machinery, which
only covers the index-2 suborder `ℤ[√5]`): the unit `φ` maps to `Φ = (1 + √5)/2 > 1` under the
real embedding, every unit is reduced into the window `[1, Φ)` by a power of `φ`, and the only
unit in that window is `1`. The half-integral order `ℤ[φ]` is handled directly through the norm
form `x² + xy - y² = ±1` (`isUnit_iff_normForm`). -/

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

/-- A unit `a·1 + b·φ` whose real value `a + bΦ` lies in `[1, Φ)` is forced to be `1`: its
conjugate `a + bΦ'` has absolute value `≤ 1` (norm `±1`), which bounds `b ∈ {0, 1}` and then
`a`. -/
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

/-- Every unit of `𝓞 ℚ(√5)` is a signed power of the golden ratio `φ`.  Proved via the
real-embedding discreteness argument above (window-reduction into `[1, Φ)`), bypassing the
`Zsqrtd`/`Pell` bridge which only covers the index-2 suborder `ℤ[√5]`. -/
theorem fundamentalUnit_generates (u : (𝓞 K)ˣ) :
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

/-- The displayed family is a system of fundamental units: together with `±1`, the golden
ratio generates all units of `ℤ[φ]`. -/
theorem fundamentalUnitSystem_isFundamental :
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K =
      ⊤ := by
  rw [eq_top_iff]
  intro u _
  have hfund : fundamentalUnit ∈ Subgroup.closure (Set.range fundamentalUnitSystem) := by
    exact Subgroup.subset_closure
      ⟨⟨0, by rw [unitRank_eq_one]; exact Nat.zero_lt_one⟩, rfl⟩
  have hneg_tor : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K := by
    change IsOfFinOrder _
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩
  rw [Subgroup.mem_sup]
  obtain ⟨n, hn | hn⟩ := fundamentalUnit_generates u
  · refine ⟨fundamentalUnit ^ n, Subgroup.zpow_mem _ hfund n, 1, Subgroup.one_mem _, ?_⟩
    rw [hn, mul_one]
  · refine ⟨fundamentalUnit ^ n, Subgroup.zpow_mem _ hfund n, -1, hneg_tor, ?_⟩
    rw [hn]
    apply Units.ext
    change ((fundamentalUnit ^ n : (𝓞 K)ˣ) : 𝓞 K) *
        (-1 : 𝓞 K) = -((fundamentalUnit ^ n : (𝓞 K)ˣ) : 𝓞 K)
    ring

/-- Equivalently, every unit of `ℤ[φ]` is a torsion unit times a power of `φ`. -/
theorem unit_eq_torsion_mul_fundamentalUnit_zpow (u : (𝓞 K)ˣ) :
    ∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧
      ∃ n : ℤ, u = ζ * fundamentalUnit ^ n := by
  have hneg_tor : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K := by
    change IsOfFinOrder _
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩
  obtain ⟨n, hn | hn⟩ := fundamentalUnit_generates u
  · exact ⟨1, Subgroup.one_mem _, n, by rw [hn, one_mul]⟩
  · exact ⟨-1, hneg_tor, n, by rw [hn, neg_eq_neg_one_mul]⟩

/-- The norm-one Pell solutions are generated by the square of the fundamental unit. -/
theorem normOneUnit_generated_by_fundamentalUnit_sq (u : (𝓞 K)ˣ)
    (hu : Algebra.norm ℤ (u : 𝓞 K) = 1) :
    ∃ n : ℤ, u = fundamentalUnit ^ (2 * n) ∨
      u = -(fundamentalUnit ^ (2 * n)) := by
  have hnormUnit : Units.map (Algebra.norm ℤ : (𝓞 K) →* ℤ) u = 1 := by
    apply Units.ext
    exact hu
  obtain ⟨n, hn | hn⟩ := fundamentalUnit_generates u
  · have hpow : ((-1 : ℤˣ) ^ n) = 1 := by
      rw [hn, normFundamentalUnit_zpow_map] at hnormUnit
      exact hnormUnit
    obtain ⟨k, hk⟩ := even_of_negOneUnit_zpow_eq_one hpow
    exact ⟨k, Or.inl (by simpa [hk] using hn)⟩
  · have hpow : ((-1 : ℤˣ) ^ n) = 1 := by
      rw [hn, normNegFundamentalUnit_zpow_map] at hnormUnit
      exact hnormUnit
    obtain ⟨k, hk⟩ := even_of_negOneUnit_zpow_eq_one hpow
    exact ⟨k, Or.inr (by simpa [hk] using hn)⟩

/-- The regulator of `ℚ(√5)` is `log φ = log((1 + √5)/2) ≈ 0.4812` — the smallest regulator
of any real quadratic field. This is the analytic restatement that `φ` is a fundamental
unit. -/
theorem regulator_eq :
    Units.regulator K = Real.log ((1 + Real.sqrt 5) / 2) := by
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

private theorem unitGroupStructure_bijective
    (i₀ : Fin (Units.rank K)) (η : (𝓞 K)ˣ)
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
    have htor : η ^ (Multiplicative.toAdd f 0) ∈
        NumberField.Units.torsion K := by
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
        have h2 := congrArg (algebraMap (𝓞 K) K) hcoe
        simp only [map_one, map_neg] at h2
        exact two_ne_zero (by linear_combination -h2 : (2 : K) = 0)
    refine Prod.ext (Multiplicative.toAdd.injective ha) ?_
    refine Multiplicative.toAdd.injective (funext fun i => ?_)
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
  set i₀ : Fin (Units.rank K) :=
    ⟨0, by rw [unitRank_eq_one]; exact Nat.zero_lt_one⟩ with hi₀
  set η : (𝓞 K)ˣ := NumberField.Units.fundSystem K i₀ with hη
  let ψ₁ : Multiplicative (ZMod 2) →* (𝓞 K)ˣ :=
    torsionPowerHom 2 (-1 : (𝓞 K)ˣ) (by rw [neg_one_sq])
  let ψ₂ : Multiplicative (Fin 1 → ℤ) →* (𝓞 K)ˣ :=
    rankOnePowerHom η
  let ψ : Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ) →* (𝓞 K)ˣ :=
    ψ₁.coprod ψ₂
  have hneg_tor : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K := by
    change IsOfFinOrder _
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by rw [neg_one_sq]⟩
  have hbij : Function.Bijective ψ := unitGroupStructure_bijective i₀ η hη hneg_tor
  exact ⟨(MulEquiv.ofBijective ψ hbij).symm⟩

end NumberField.SqrtFive

/-!
## Regulator
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

end NumberField.SqrtFive
