/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.ClassGroup

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

/-- The displayed family is a system of fundamental units: together with roots of unity, it
generates all units of `𝓞 K`. In rank `1` this says exactly that `θ² - 2` is a fundamental
unit (not a proper power times torsion). -/
theorem fundamentalUnitSystem_isFundamental :
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K = ⊤ := by
  sorry

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
