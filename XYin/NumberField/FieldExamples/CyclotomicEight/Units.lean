/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.ClassGroup

/-!
# `ℚ(ζ₈)` Units

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

open Module
open NumberField.FieldExamples
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicEight

private theorem coe_zetaInt : algebraMap (𝓞 K) K zetaInt = ζ := rfl

/-- A torsion generator of `𝓞 Kˣ`: the eighth root of unity `ζ` itself, with explicit
inverse `ζ⁷`. -/
noncomputable def torsionGenerator : (𝓞 K)ˣ where
  val := zetaInt
  inv := zetaInt ^ 7
  val_inv := by linear_combination (zetaInt ^ 4 - 1) * zetaInt_pow_four
  inv_val := by linear_combination (zetaInt ^ 4 - 1) * zetaInt_pow_four

/-- The concrete torsion units: the eight roots of unity `ζ^k`. -/
def torsionUnits : Set ((𝓞 K)ˣ) := {u | ∃ k : Fin 8, u = torsionGenerator ^ k.val}

/-- The torsion subgroup of `𝓞 Kˣ` is exactly `μ₈ = {ζ^k}` (note `-1 = ζ⁴` is already a
power of `ζ`, unlike in `ℚ(ζ₅)`). -/
private theorem torsionOrder_eq' : NumberField.Units.torsionOrder K = 8 := by
  rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 8)]
  norm_num

theorem torsionUnits_eq : {u : (𝓞 K)ˣ | IsOfFinOrder u} = torsionUnits := by
  have htg8 : torsionGenerator ^ 8 = 1 := by
    ext
    exact zeta_pow_eight
  ext u
  constructor
  · intro hu
    have humem : u ∈ NumberField.Units.torsion K := hu
    rw [← NumberField.Units.rootsOfUnity_eq_torsion K, torsionOrder_eq'] at humem
    have h8 : u ^ 8 = 1 := humem
    have hK : (algebraMap (𝓞 K) K ((u : (𝓞 K)ˣ) : 𝓞 K)) ^ 8 = 1 := by
      have hval : ((u ^ 8 : (𝓞 K)ˣ) : 𝓞 K) = ((1 : (𝓞 K)ˣ) : 𝓞 K) := by rw [h8]
      rw [Units.val_pow_eq_pow_val, Units.val_one] at hval
      rw [← map_pow, hval, map_one]
    obtain ⟨i, hi, hieq⟩ := zeta_isPrimitiveRoot.eq_pow_of_pow_eq_one hK
    refine ⟨⟨i, hi⟩, Units.ext (IsFractionRing.injective (𝓞 K) K ?_)⟩
    rw [← hieq]
    change ζ ^ i = algebraMap (𝓞 K) K ((torsionGenerator ^ i : (𝓞 K)ˣ) : 𝓞 K)
    rw [Units.val_pow_eq_pow_val, map_pow]
    rfl
  · rintro ⟨k, rfl⟩
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨8, by norm_num, ?_⟩
    rw [← pow_mul, mul_comm, pow_mul, htg8, one_pow]

/-- The torsion subgroup of `𝓞 Kˣ` has order `8`. -/
theorem torsionOrder_eq_eight : NumberField.Units.torsionOrder K = 8 :=
  torsionOrder_eq'

/-- The Dirichlet unit rank of `ℚ(ζ₈)` is `1`: the signature is `(0, 2)`, so the rank is
`r₁ + r₂ - 1 = 1`. -/
theorem unitRank_eq_one : NumberField.Units.rank K = 1 := by
  rw [NumberField.Units.rank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_eq_zero, nrComplexPlaces_eq_two]

/-- The fundamental unit of `𝓞 K`: `1 + √2 = 1 + ζ + ζ⁷`, with explicit inverse
`√2 - 1 = ζ + ζ⁷ - 1` (the fundamental unit of the real quadratic subfield `ℚ(√2)`). -/
noncomputable def fundamentalUnit : (𝓞 K)ˣ where
  val := 1 + zetaInt + zetaInt ^ 7
  inv := zetaInt + zetaInt ^ 7 - 1
  val_inv := by
    linear_combination (zetaInt ^ 10 - zetaInt ^ 6 + 2 * zetaInt ^ 4 + zetaInt ^ 2 - 2) *
      zetaInt_pow_four
  inv_val := by
    linear_combination (zetaInt ^ 10 - zetaInt ^ 6 + 2 * zetaInt ^ 4 + zetaInt ^ 2 - 2) *
      zetaInt_pow_four

/-- The system of fundamental units for the rank-`1` unit group: the single unit `1 + √2`. -/
noncomputable def fundamentalUnitSystem : Fin (NumberField.Units.rank K) → (𝓞 K)ˣ :=
  fun _ => fundamentalUnit

/-- Mathlib's abstract fundamental unit `fundSystem K i₀`, together with the torsion, generates
the whole unit group (rank-one specialization of `closure_fundSystem_sup_torsion_eq_top`). -/
private theorem exists_eq_torsion_mul_fundSystem_zpow (i₀ : Fin (NumberField.Units.rank K))
    (u : (𝓞 K)ˣ) :
    ∃ ζ' ∈ NumberField.Units.torsion K, ∃ n : ℤ,
      u = ζ' * NumberField.Units.fundSystem K i₀ ^ n := by
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
private theorem fundSystem_zpow_mem_torsion (i₀ : Fin (NumberField.Units.rank K)) (n : ℤ)
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

/-- Pointwise classification of the torsion: every torsion unit is a power of `ζ`. -/
private theorem eq_torsionGenerator_pow_of_mem_torsion {ζ' : (𝓞 K)ˣ}
    (hζ' : ζ' ∈ NumberField.Units.torsion K) : ∃ k : Fin 8, ζ' = torsionGenerator ^ k.val := by
  have hfin : IsOfFinOrder ζ' := hζ'
  have hmem : ζ' ∈ {u : (𝓞 K)ˣ | IsOfFinOrder u} := hfin
  rw [torsionUnits_eq] at hmem
  exact hmem

/-- The displayed family is a system of fundamental units: together with `μ₈`, the unit
`1 + √2` generates all units of `ℤ[ζ₈]`. -/
theorem fundamentalUnitSystem_isFundamental :
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K = ⊤ := by
  sorry

/-- Equivalently, every unit of `ℤ[ζ₈]` is `ζ^j (1 + √2)ⁿ`. -/
theorem unit_eq_torsion_mul_fundamentalUnit_zpow (u : (𝓞 K)ˣ) :
    ∃ ζ' : (𝓞 K)ˣ, ζ' ∈ NumberField.Units.torsion K ∧ ∃ n : ℤ, u = ζ' * fundamentalUnit ^ n := by
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

private theorem unitGroupStructure_bijective
    (i₀ : Fin (NumberField.Units.rank K)) (η : (𝓞 K)ˣ)
    (hη : η = NumberField.Units.fundSystem K i₀) (htg8 : torsionGenerator ^ 8 = 1)
    (htg_tor : torsionGenerator ∈ NumberField.Units.torsion K) :
    Function.Bijective
      ((torsionPowerHom 8 torsionGenerator htg8).coprod (rankOnePowerHom η)) := by
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨a, f⟩ h
    have h' : torsionGenerator ^ ((Multiplicative.toAdd a).val) *
        η ^ (Multiplicative.toAdd f 0) = 1 := h
    have htor : η ^ (Multiplicative.toAdd f 0) ∈ NumberField.Units.torsion K := by
      have heq : η ^ (Multiplicative.toAdd f 0) =
          (torsionGenerator ^ ((Multiplicative.toAdd a).val))⁻¹ :=
        (mul_eq_one_iff_inv_eq.mp h').symm
      rw [heq]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ htg_tor _)
    have hn0 : Multiplicative.toAdd f 0 = 0 :=
      fundSystem_zpow_mem_torsion i₀ _ (by simpa [hη] using htor)
    rw [hn0, zpow_zero, mul_one] at h'
    have haval : (Multiplicative.toAdd a).val = 0 := by
      have hOK : zetaInt ^ (Multiplicative.toAdd a).val = 1 := by
        have hval := congrArg Units.val h'
        simpa [Units.val_pow_eq_pow_val] using hval
      have hK : ζ ^ (Multiplicative.toAdd a).val = 1 := by
        have hmap := congrArg (algebraMap (𝓞 K) K) hOK
        simpa [map_pow, coe_zetaInt] using hmap
      have hdvd := (IsPrimitiveRoot.pow_eq_one_iff_dvd zeta_isPrimitiveRoot _).mp hK
      have hlt : (Multiplicative.toAdd a).val < 8 := ZMod.val_lt _
      omega
    have ha0 : Multiplicative.toAdd a = 0 := by
      have hinv := ZMod.natCast_rightInverse (n := 8) (Multiplicative.toAdd a)
      rw [← hinv, haval]
      rfl
    refine Prod.ext (Multiplicative.toAdd.injective ha0) ?_
    refine Multiplicative.toAdd.injective (funext fun i => ?_)
    rw [Subsingleton.elim i 0]
    exact hn0
  · intro u
    obtain ⟨ζ', hζ', n, hu⟩ := exists_eq_torsion_mul_fundSystem_zpow i₀ u
    obtain ⟨k, hk⟩ := eq_torsionGenerator_pow_of_mem_torsion hζ'
    refine ⟨(Multiplicative.ofAdd ((k.val : ZMod 8)), Multiplicative.ofAdd (fun _ => n)), ?_⟩
    change torsionGenerator ^ ((k.val : ZMod 8)).val * η ^ n = u
    rw [hη, ZMod.val_cast_of_lt k.isLt, hu, hk]

/-- The unit group is `μ₈ × ℤ` as an abstract abelian group. -/
theorem unitGroupStructure :
    Nonempty ((𝓞 K)ˣ ≃* (Multiplicative (ZMod 8) × Multiplicative (Fin 1 → ℤ))) := by
  set i₀ : Fin (NumberField.Units.rank K) :=
    ⟨0, by rw [unitRank_eq_one]; exact Nat.zero_lt_one⟩ with hi₀
  set η : (𝓞 K)ˣ := NumberField.Units.fundSystem K i₀ with hη
  have htg8 : torsionGenerator ^ 8 = 1 := by
    ext
    exact zeta_pow_eight
  let ψ₁ : Multiplicative (ZMod 8) →* (𝓞 K)ˣ :=
    torsionPowerHom 8 torsionGenerator htg8
  let ψ₂ : Multiplicative (Fin 1 → ℤ) →* (𝓞 K)ˣ :=
    rankOnePowerHom η
  let ψ : Multiplicative (ZMod 8) × Multiplicative (Fin 1 → ℤ) →* (𝓞 K)ˣ := ψ₁.coprod ψ₂
  have htg_tor : torsionGenerator ∈ NumberField.Units.torsion K := by
    change IsOfFinOrder torsionGenerator
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨8, by norm_num, htg8⟩
  have hbij : Function.Bijective ψ := unitGroupStructure_bijective i₀ η hη htg8 htg_tor
  exact ⟨(MulEquiv.ofBijective ψ hbij).symm⟩

/-- The regulator of `ℚ(ζ₈)` is `2·log(1 + √2) ≈ 1.7627`: the complex place contributes
weight `2`, and `|1 + ζ + ζ⁷| = 1 + √2` at one of the two places. -/
theorem regulator_eq :
    NumberField.Units.regulator K = 2 * Real.log (1 + Real.sqrt 2) := by
  sorry


end NumberField.CyclotomicEight


/-!
## Regulator
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

theorem regulator_eq_two_mul_log_one_add_sqrtTwo :
    NumberField.Units.regulator K = 2 * Real.log (1 + Real.sqrt 2) := by
  exact regulator_eq

end NumberField.CyclotomicEight
