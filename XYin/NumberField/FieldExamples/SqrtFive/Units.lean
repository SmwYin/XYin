/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.PrimeSplitting

/-!
# `ℚ(√5)` Unit group

This file develops the unit group part of the `ℚ(√5)` number field example.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open NumberField.FieldExamples

namespace NumberField.SqrtFive

private theorem goldenIntO_sq : goldenIntO ^ 2 = goldenIntO + 1 :=
  Subtype.ext (by push_cast [goldenIntO]; exact goldenRoot_sq)

private theorem ringHom_ext_golden {f g : K →+* ℂ} (h : f goldenRoot = g goldenRoot) :
    f = g := by
  ext z
  obtain ⟨x, y⟩ := z
  rw [QuadraticAlgebra.mk_eq_add_smul_omega, map_add, map_add]
  congr 1
  · exact (eq_ratCast (f.comp (algebraMap ℚ K)) x).trans
      (eq_ratCast (g.comp (algebraMap ℚ K)) x).symm
  · rw [Algebra.smul_def, map_mul, map_mul]
    exact congrArg₂ (fun a b => a * b)
      ((eq_ratCast (f.comp (algebraMap ℚ K)) y).trans
        (eq_ratCast (g.comp (algebraMap ℚ K)) y).symm) h

/-- `ℚ(√5)` is totally real. -/
theorem isTotallyReal : NumberField.IsTotallyReal K := by
  refine ⟨fun v => ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
  refine ringHom_ext_golden ?_
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  set z := NumberField.InfinitePlace.embedding v goldenRoot with hz
  have hsq : z ^ 2 = z + 1 := by
    rw [hz, ← map_pow, goldenRoot_sq, map_add, map_one]
  have hc : (starRingEnd ℂ) z ^ 2 = (starRingEnd ℂ) z + 1 := by
    rw [← map_pow, hsq, map_add, map_one]
  have hfac : ((starRingEnd ℂ) z - z) * ((starRingEnd ℂ) z + z - 1) = 0 := by
    linear_combination hc - hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hre : z.re = 1 / 2 := by
      have hcr := congrArg Complex.re h
      rw [Complex.sub_re, Complex.add_re, Complex.conj_re] at hcr
      norm_num at hcr
      linarith
    have hreal := congrArg Complex.re hsq
    rw [sq, Complex.mul_re, Complex.add_re, Complex.one_re, hre] at hreal
    norm_num at hreal
    nlinarith [sq_nonneg z.im]

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

/-- The field `ℚ(√5)` has two real infinite places: the signature is `(r₁, r₂) = (2, 0)`. -/
theorem nrRealPlaces_eq_two : InfinitePlace.nrRealPlaces K = 2 := by
  haveI := isTotallyReal
  have hcomplex := NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hcomplex, degree_eq_two] at h
  omega

/-- The field `ℚ(√5)` has no complex infinite places. -/
theorem nrComplexPlaces_eq_zero : InfinitePlace.nrComplexPlaces K = 0 := by
  haveI := isTotallyReal
  exact NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K

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

/-- Every unit of `𝓞 ℚ(√5)` is a signed power of the golden ratio `φ`. -/
theorem fundamentalUnit_generates (u : (𝓞 K)ˣ) :
    ∃ n : ℤ, u = fundamentalUnit ^ n ∨ u = -(fundamentalUnit ^ n) := by
  -- Blocked: `SqrtTwo.lean` proves the analogous statement through `Zsqrtd` and
  -- `Pell.Solution₁` for `x^2 - d*y^2 = 1`.  Here the full ring of integers is the
  -- half-integral order `ℤ[(1 + √5)/2]`; the corresponding equation is
  -- `x^2 + x*y - y^2 = ±1` (equivalently `a^2 - 5*b^2 = ±4`).  The project currently has
  -- no completed bridge from that Fibonacci/Pell-±4 equation to the displayed unit `φ`.
  sorry

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
  -- Blocked: this is intentionally the final theorem with no complete reference proof yet.
  sorry

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
