/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.PrimeSplitting

/-!
# `ℚ(√2)` Unit group

This file develops the unit group part of the `ℚ(√2)` number field example.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open NumberField.FieldExamples

namespace NumberField.SqrtTwo

/-!
This Pell-theoretic unit analysis is genuinely specific to the real quadratic side.
There is no corresponding Pell section for `ℚ(ζ₃)`, which is imaginary quadratic.
-/

/-- The concrete quadratic order `ℤ[√2]` from mathlib's Pell API. -/
abbrev ZSqrtTwo : Type := Zsqrtd (2 : ℤ)

/-- The concrete `ℤ√2` model maps to the ring of integers by `√2 ↦ √2`. -/
abbrev zsqrtTwoToRingOfIntegers : ZSqrtTwo →+* 𝓞 K :=
  Zsqrtd.lift ⟨sqrtTwoInteger, by simpa [sq] using sqrtTwoInteger_sq⟩

theorem zsqrtTwoToRingOfIntegers_apply (a b : ℤ) :
    zsqrtTwoToRingOfIntegers (⟨a, b⟩ : ZSqrtTwo) =
      (a : 𝓞 K) + b * sqrtTwoInteger := by
  simp [zsqrtTwoToRingOfIntegers]

theorem two_not_int_square : ∀ n : ℤ, (2 : ℤ) ≠ n * n := by
  intro n hn
  have hsquare : IsSquare (2 : ℤ) := ⟨n, hn⟩
  norm_num at hsquare

theorem zsqrtTwoToRingOfIntegers_injective : Function.Injective zsqrtTwoToRingOfIntegers :=
  Zsqrtd.lift_injective
    ⟨sqrtTwoInteger, by simpa [sq] using sqrtTwoInteger_sq⟩
    two_not_int_square

theorem zsqrtTwoToRingOfIntegers_surjective : Function.Surjective zsqrtTwoToRingOfIntegers := by
  intro x
  let a : ℤ := sqrtTwoExplicitIntegralBasis.repr x 0
  let b : ℤ := sqrtTwoExplicitIntegralBasis.repr x 1
  refine ⟨(⟨a, b⟩ : ZSqrtTwo), ?_⟩
  rw [zsqrtTwoToRingOfIntegers_apply]
  have hsum := sqrtTwoExplicitIntegralBasis.sum_repr x
  have h0 :
      sqrtTwoExplicitIntegralPowerBasis.basis
          ((finCongr sqrtTwoExplicitIntegralPowerBasis_dim).symm (0 : Fin 2)) =
        (1 : 𝓞 K) := by
    simpa [sqrtTwoExplicitIntegralBasis, Basis.reindex_apply] using
      sqrtTwoExplicitIntegralBasis_zero
  have h1 :
      sqrtTwoExplicitIntegralPowerBasis.basis
          ((finCongr sqrtTwoExplicitIntegralPowerBasis_dim).symm (1 : Fin 2)) =
        sqrtTwoInteger := by
    simpa [sqrtTwoExplicitIntegralBasis, Basis.reindex_apply] using
      sqrtTwoExplicitIntegralBasis_one
  rw [show (a : 𝓞 K) = (a : 𝓞 K) * (1 : 𝓞 K) by rw [mul_one]]
  rw [← h0, ← h1]
  simpa [a, b, Fin.sum_univ_two] using hsum

/-- The explicit ring equivalence `ℤ√2 ≃ 𝓞 ℚ(√2)`. -/
abbrev zsqrtTwoEquivRingOfIntegers : ZSqrtTwo ≃+* 𝓞 K :=
  RingEquiv.ofBijective zsqrtTwoToRingOfIntegers
    ⟨zsqrtTwoToRingOfIntegers_injective, zsqrtTwoToRingOfIntegers_surjective⟩

/-- The unit `1 + √2` in the ring of integers. -/
abbrev sqrtTwoFundamentalUnit : (𝓞 K)ˣ where
  val := sqrtTwoInteger + 1
  inv := sqrtTwoInteger - 1
  val_inv := by
    apply Subtype.ext
    calc
      (sqrtTwoRoot + 1) * (sqrtTwoRoot - 1) = sqrtTwoRoot ^ 2 - 1 := by ring
      _ = (1 : K) := by rw [sqrtTwoRoot_sq]; ring
  inv_val := by
    apply Subtype.ext
    calc
      (sqrtTwoRoot - 1) * (sqrtTwoRoot + 1) = sqrtTwoRoot ^ 2 - 1 := by ring
      _ = (1 : K) := by rw [sqrtTwoRoot_sq]; ring

/-- The same unit `1 + √2`, but in mathlib's concrete `ℤ√2` model. -/
abbrev zsqrtTwoFundamentalUnit : ZSqrtTwoˣ where
  val := ⟨1, 1⟩
  inv := ⟨-1, 1⟩
  val_inv := by
    ext <;> norm_num
  inv_val := by
    ext <;> norm_num

theorem zsqrtTwoFundamentalUnit_norm :
    Zsqrtd.norm (zsqrtTwoFundamentalUnit : ZSqrtTwo) = -1 := by
  norm_num [zsqrtTwoFundamentalUnit, Zsqrtd.norm]

theorem zsqrtTwoEquivRingOfIntegers_fundamentalUnit :
    Units.mapEquiv zsqrtTwoEquivRingOfIntegers.toMulEquiv zsqrtTwoFundamentalUnit =
      sqrtTwoFundamentalUnit := by
  apply Units.ext
  change zsqrtTwoEquivRingOfIntegers (⟨1, 1⟩ : ZSqrtTwo) = sqrtTwoInteger + 1
  change zsqrtTwoToRingOfIntegers (⟨1, 1⟩ : ZSqrtTwo) = sqrtTwoInteger + 1
  rw [zsqrtTwoToRingOfIntegers_apply]
  ring

theorem zsqrtTwoEquivRingOfIntegers_unitsMap_neg (v : ZSqrtTwoˣ) :
    Units.mapEquiv zsqrtTwoEquivRingOfIntegers.toMulEquiv (-v) =
      -(Units.mapEquiv zsqrtTwoEquivRingOfIntegers.toMulEquiv v) := by
  apply Units.ext
  change zsqrtTwoEquivRingOfIntegers (-(v : ZSqrtTwo)) =
    -zsqrtTwoEquivRingOfIntegers (v : ZSqrtTwo)
  rw [map_neg]

/--
The square of `1 + √2` is `3 + 2√2`, a norm-one unit.
Mathlib's Pell API phrases "fundamental" for norm-one solutions, so this is
the Pell solution attached to the fundamental unit `1 + √2`.
-/
theorem sqrtTwoFundamentalUnit_sq :
    ((sqrtTwoFundamentalUnit ^ 2 : (𝓞 K)ˣ) : 𝓞 K) =
      3 + 2 * sqrtTwoInteger := by
  apply Subtype.ext
  calc
    (sqrtTwoRoot + 1) ^ 2 =
        sqrtTwoRoot ^ 2 + 2 * sqrtTwoRoot + 1 := by ring
    _ = (3 : K) + 2 * sqrtTwoRoot := by rw [sqrtTwoRoot_sq]; ring

/-- The Pell solution `3 + 2√2`, i.e. `(1 + √2)^2`. -/
abbrev pellTwoFundamentalSolution : Pell.Solution₁ (2 : ℤ) :=
  Pell.Solution₁.mk 3 2 (by norm_num)

/--
`3 + 2√2` is the fundamental norm-one solution of Pell's equation
`x^2 - 2y^2 = 1`. Equivalently, the unit `1 + √2` is the usual fundamental
unit, with square equal to the fundamental positive norm-one unit.
-/
theorem pellTwoFundamentalSolution_isFundamental :
    Pell.IsFundamental pellTwoFundamentalSolution := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [pellTwoFundamentalSolution]
  · norm_num [pellTwoFundamentalSolution]
  · intro b hb
    by_contra hlt
    have hsmall : b.x < 3 := by
      have h := not_le.mp hlt
      simpa [pellTwoFundamentalSolution] using h
    have hx2 : b.x = 2 := by omega
    have hprop := b.prop
    rw [hx2] at hprop
    have hodd : 2 * b.y ^ 2 = 3 := by nlinarith
    omega

/-- Every norm-one Pell unit for `d = 2` is a signed power of `3 + 2√2`. -/
theorem pellTwoFundamentalSolution_generates_normOnePell
    (a : Pell.Solution₁ (2 : ℤ)) :
    ∃ n : ℤ, a = pellTwoFundamentalSolution ^ n ∨
      a = -pellTwoFundamentalSolution ^ n :=
  pellTwoFundamentalSolution_isFundamental.eq_zpow_or_neg_zpow a

theorem zsqrtTwoFundamentalUnit_sq_toPell :
    (Unitary.toUnits pellTwoFundamentalSolution : ZSqrtTwoˣ) =
      zsqrtTwoFundamentalUnit ^ 2 := by
  ext <;> norm_num [pellTwoFundamentalSolution, zsqrtTwoFundamentalUnit,
    pow_two]

theorem zsqrtTwo_normOneUnit_generated_by_square
    (u : ZSqrtTwoˣ) (hnorm : Zsqrtd.norm (u : ZSqrtTwo) = 1) :
    ∃ n : ℤ, u = zsqrtTwoFundamentalUnit ^ (2 * n) ∨
      u = -(zsqrtTwoFundamentalUnit ^ (2 * n)) := by
  let a : Pell.Solution₁ (2 : ℤ) :=
    ⟨(u : ZSqrtTwo), Zsqrtd.norm_eq_one_iff_mem_unitary.mp hnorm⟩
  have hua : u = Unitary.toUnits a := by
    apply Units.ext
    rfl
  obtain ⟨n, hn | hn⟩ := pellTwoFundamentalSolution_generates_normOnePell a
  · refine ⟨n, Or.inl ?_⟩
    calc
      u = Unitary.toUnits a := hua
      _ = Unitary.toUnits (pellTwoFundamentalSolution ^ n) := by rw [hn]
      _ = (Unitary.toUnits pellTwoFundamentalSolution : ZSqrtTwoˣ) ^ n := by
        exact (Unitary.toUnits : unitary ZSqrtTwo →* ZSqrtTwoˣ).map_zpow
          pellTwoFundamentalSolution n
      _ = (zsqrtTwoFundamentalUnit ^ 2) ^ n := by
        rw [zsqrtTwoFundamentalUnit_sq_toPell]
      _ = zsqrtTwoFundamentalUnit ^ (2 * n) :=
        (zpow_mul zsqrtTwoFundamentalUnit 2 n).symm
  · refine ⟨n, Or.inr ?_⟩
    calc
      u = Unitary.toUnits a := hua
      _ = Unitary.toUnits (-(pellTwoFundamentalSolution ^ n)) := by rw [hn]
      _ = -Unitary.toUnits (pellTwoFundamentalSolution ^ n) := by
        apply Units.ext
        rfl
      _ = -((Unitary.toUnits pellTwoFundamentalSolution : ZSqrtTwoˣ) ^ n) := by
        have hpow :
            Unitary.toUnits (pellTwoFundamentalSolution ^ n) =
              (Unitary.toUnits pellTwoFundamentalSolution : ZSqrtTwoˣ) ^ n :=
          (Unitary.toUnits : unitary ZSqrtTwo →* ZSqrtTwoˣ).map_zpow
            pellTwoFundamentalSolution n
        rw [hpow]
      _ = -(zsqrtTwoFundamentalUnit ^ (2 * n)) := by
        rw [zsqrtTwoFundamentalUnit_sq_toPell]
        exact congrArg Neg.neg
          (zpow_mul zsqrtTwoFundamentalUnit 2 n).symm

/-- Every unit of `ℤ√2` is a signed power of `1 + √2`. -/
theorem zsqrtTwo_units_generated_by_fundamental (u : ZSqrtTwoˣ) :
    ∃ n : ℤ, u = zsqrtTwoFundamentalUnit ^ n ∨
      u = -(zsqrtTwoFundamentalUnit ^ n) := by
  have hnormUnit : IsUnit (Zsqrtd.norm (u : ZSqrtTwo)) :=
    (Zsqrtd.isUnit_iff_norm_isUnit (u : ZSqrtTwo)).mp u.isUnit
  rcases Int.isUnit_eq_one_or hnormUnit with hnorm | hnorm
  · obtain ⟨n, hn | hn⟩ :=
      zsqrtTwo_normOneUnit_generated_by_square u hnorm
    · exact ⟨2 * n, Or.inl hn⟩
    · exact ⟨2 * n, Or.inr hn⟩
  · have hmulnorm :
        Zsqrtd.norm ((u * zsqrtTwoFundamentalUnit : ZSqrtTwoˣ) :
          ZSqrtTwo) = 1 := by
      rw [Units.val_mul, Zsqrtd.norm_mul, hnorm,
        zsqrtTwoFundamentalUnit_norm]
      norm_num
    obtain ⟨n, hn | hn⟩ :=
      zsqrtTwo_normOneUnit_generated_by_square
        (u * zsqrtTwoFundamentalUnit) hmulnorm
    · refine ⟨2 * n - 1, Or.inl ?_⟩
      calc
        u = (u * zsqrtTwoFundamentalUnit) *
            zsqrtTwoFundamentalUnit⁻¹ := by group
        _ = (zsqrtTwoFundamentalUnit ^ (2 * n)) *
            zsqrtTwoFundamentalUnit⁻¹ := by rw [hn]
        _ = zsqrtTwoFundamentalUnit ^ (2 * n - 1) := by
          rw [← zpow_neg_one zsqrtTwoFundamentalUnit, ← zpow_add]
          ring_nf
    · refine ⟨2 * n - 1, Or.inr ?_⟩
      calc
        u = (u * zsqrtTwoFundamentalUnit) *
            zsqrtTwoFundamentalUnit⁻¹ := by group
        _ = (-(zsqrtTwoFundamentalUnit ^ (2 * n))) *
            zsqrtTwoFundamentalUnit⁻¹ := by rw [hn]
        _ = -(zsqrtTwoFundamentalUnit ^ (2 * n - 1)) := by
          rw [neg_mul, ← zpow_neg_one zsqrtTwoFundamentalUnit, ← zpow_add]
          ring_nf

/-- Every unit of `𝓞 ℚ(√2)` is a signed power of the unit `1 + √2`. -/
theorem sqrtTwoFundamentalUnit_generates_unitGroup (u : (𝓞 K)ˣ) :
    ∃ n : ℤ, u = sqrtTwoFundamentalUnit ^ n ∨
      u = -(sqrtTwoFundamentalUnit ^ n) := by
  let e : ZSqrtTwoˣ ≃* (𝓞 K)ˣ :=
    Units.mapEquiv zsqrtTwoEquivRingOfIntegers.toMulEquiv
  obtain ⟨n, hn | hn⟩ :=
    zsqrtTwo_units_generated_by_fundamental (e.symm u)
  · refine ⟨n, Or.inl ?_⟩
    calc
      u = e (e.symm u) := (e.apply_symm_apply u).symm
      _ = e (zsqrtTwoFundamentalUnit ^ n) := by rw [hn]
      _ = e zsqrtTwoFundamentalUnit ^ n := by
        exact map_zpow e zsqrtTwoFundamentalUnit n
      _ = sqrtTwoFundamentalUnit ^ n := by
        rw [zsqrtTwoEquivRingOfIntegers_fundamentalUnit]
  · refine ⟨n, Or.inr ?_⟩
    calc
      u = e (e.symm u) := (e.apply_symm_apply u).symm
      _ = e (-(zsqrtTwoFundamentalUnit ^ n)) := by rw [hn]
      _ = -(e (zsqrtTwoFundamentalUnit ^ n)) := by
        exact zsqrtTwoEquivRingOfIntegers_unitsMap_neg (zsqrtTwoFundamentalUnit ^ n)
      _ = -(e zsqrtTwoFundamentalUnit ^ n) := by
        rw [map_zpow e zsqrtTwoFundamentalUnit n]
      _ = -(sqrtTwoFundamentalUnit ^ n) := by
        rw [zsqrtTwoEquivRingOfIntegers_fundamentalUnit]

/--
The unit `1 + √2` is fundamental, in the standard Pell normalization: its
square is the positive norm-one generator, and that generator produces all
norm-one Pell units up to sign.
-/
theorem sqrtTwoFundamentalUnit_isFundamental :
    ((sqrtTwoFundamentalUnit ^ 2 : (𝓞 K)ˣ) : 𝓞 K) =
        3 + 2 * sqrtTwoInteger ∧
      ∀ a : Pell.Solution₁ (2 : ℤ), ∃ n : ℤ,
        a = pellTwoFundamentalSolution ^ n ∨
          a = -pellTwoFundamentalSolution ^ n := by
  exact ⟨sqrtTwoFundamentalUnit_sq,
    pellTwoFundamentalSolution_generates_normOnePell⟩

/-- The field `ℚ(√2)` has no complex infinite places. -/
theorem nrComplexPlaces_eq_zero :
    NumberField.InfinitePlace.nrComplexPlaces K = 0 := by
  have hfin : Module.finrank ℚ K = 2 := by
    rw [PowerBasis.finrank sqrtTwoPowerBasis]
    exact sqrtTwoPowerBasis_dim
  have hsig := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  rw [hfin] at hsig
  have hsign := NumberField.sign_discr (K := K)
  rw [sqrtTwo_numberField_discr] at hsign
  have hnle : NumberField.InfinitePlace.nrComplexPlaces K ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hnle with hn | hn
  · exact hn
  · rw [hn] at hsign
    norm_num at hsign

/-- The field `ℚ(√2)` has two real infinite places: the signature is `(r₁, r₂) = (2, 0)`,
i.e. the field is totally real. -/
theorem nrRealPlaces_eq_two :
    NumberField.InfinitePlace.nrRealPlaces K = 2 := by
  have hfin : Module.finrank ℚ K = 2 := by
    rw [PowerBasis.finrank sqrtTwoPowerBasis]
    exact sqrtTwoPowerBasis_dim
  have hsig := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  rw [hfin, nrComplexPlaces_eq_zero] at hsig
  omega

/-- `ℚ(√2)` is totally real. -/
theorem isTotallyReal : NumberField.IsTotallyReal K :=
  (NumberField.nrComplexPlaces_eq_zero_iff (K := K)).mp nrComplexPlaces_eq_zero

/-- The torsion subgroup of `𝓞 ℚ(√2)ˣ` has order `2`: a totally real field has only the
roots of unity `±1`. -/
private theorem sqrtTwo_torsion_eq_one_or_neg_one
    (x : Units.torsion K) : (x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1 := by
  by_cases! hc : 2 < orderOf (x : (𝓞 K)ˣ)
  · have horder :
        orderOf ((x : (𝓞 K)ˣ) : K) = orderOf (x : (𝓞 K)ˣ) := by
      simpa using
        (orderOf_injective
          ((Units.coeHom K).comp (Units.map (algebraMap (𝓞 K) K)))
          (by
            intro u v huv
            exact NumberField.Units.coe_injective (K := K) huv)
          (x : (𝓞 K)ˣ))
    have hcK : 2 < orderOf ((x : (𝓞 K)ˣ) : K) := by
      rwa [horder]
    linarith [
      NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hcK
        (IsPrimitiveRoot.orderOf ((x : (𝓞 K)ˣ) : K)),
      show 0 < NumberField.InfinitePlace.nrRealPlaces K by
        rw [nrRealPlaces_eq_two]
        norm_num]
  · interval_cases hi : orderOf (x : (𝓞 K)ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
    · exact Or.inl (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, Units.val_neg, Units.val_one, hi]

theorem torsionOrder_eq_two : Units.torsionOrder K = 2 := by
  classical
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact sqrtTwo_torsion_eq_one_or_neg_one x

/-- The Dirichlet unit rank of `ℚ(√2)` is `1`: the signature is `(2, 0)`, so the rank is
`r₁ + r₂ - 1 = 1`. -/
theorem unitRank_eq_one : Units.rank K = 1 := by
  dsimp [Units.rank]
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_eq_two, nrComplexPlaces_eq_zero]

private theorem exists_eq_torsion_mul_fundSystem_zpow
    (i₀ : Fin (NumberField.Units.rank K)) (u : (𝓞 K)ˣ) :
    ∃ ζ ∈ NumberField.Units.torsion K, ∃ n : ℤ,
      u = ζ * NumberField.Units.fundSystem K i₀ ^ n := by
  haveI hsub : Subsingleton (Fin (NumberField.Units.rank K)) :=
    Fin.subsingleton_iff_le_one.mpr (by rw [unitRank_eq_one])
  have hu : u ∈ Subgroup.closure (Set.range (NumberField.Units.fundSystem K)) ⊔
      NumberField.Units.torsion K := by
    rw [NumberField.Units.closure_fundSystem_sup_torsion_eq_top]
    trivial
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

private theorem fundSystem_zpow_mem_torsion
    (i₀ : Fin (NumberField.Units.rank K)) (n : ℤ)
    (hn : NumberField.Units.fundSystem K i₀ ^ n ∈
      NumberField.Units.torsion K) : n = 0 := by
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

private theorem eq_one_or_neg_one_of_mem_torsion {ζ : (𝓞 K)ˣ}
    (hζ : ζ ∈ NumberField.Units.torsion K) : ζ = 1 ∨ ζ = -1 := by
  simpa using
    (sqrtTwo_torsion_eq_one_or_neg_one
      (⟨ζ, hζ⟩ : NumberField.Units.torsion K))

/-- The only roots of unity in `𝓞 ℚ(√2)` are `1` and `-1`. -/
theorem mem_torsion_iff_eq_one_or_neg_one (u : (𝓞 K)ˣ) :
    u ∈ NumberField.Units.torsion K ↔ u = 1 ∨ u = -1 := by
  constructor
  · exact eq_one_or_neg_one_of_mem_torsion
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact neg_one_mem_torsion

/-- The regulator of `ℚ(√2)` is `log(1 + √2) ≈ 0.8814`, the covolume of the unit lattice.
This is the analytic restatement that `1 + √2` is a fundamental unit. -/
theorem regulator_eq : Units.regulator K = Real.log (1 + Real.sqrt 2) := by
  sorry

private theorem unitGroupStructure_bijective
    (i₀ : Fin (NumberField.Units.rank K)) (η : (𝓞 K)ˣ)
    (hη : η = NumberField.Units.fundSystem K i₀)
    (hneg_tor : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K) :
    Function.Bijective
      ((torsionPowerHom 2 (-1 : (𝓞 K)ˣ) (by rw [neg_one_sq])).coprod (rankOnePowerHom η)) := by
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
  set i₀ : Fin (NumberField.Units.rank K) :=
    ⟨0, by rw [unitRank_eq_one]; exact Nat.zero_lt_one⟩ with hi₀
  set η : (𝓞 K)ˣ := NumberField.Units.fundSystem K i₀ with hη
  let ψ₁ : Multiplicative (ZMod 2) →* (𝓞 K)ˣ :=
    torsionPowerHom 2 (-1 : (𝓞 K)ˣ) (by rw [neg_one_sq])
  let ψ₂ : Multiplicative (Fin 1 → ℤ) →* (𝓞 K)ˣ :=
    rankOnePowerHom η
  let ψ : Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ) →* (𝓞 K)ˣ := ψ₁.coprod ψ₂
  have hneg_tor : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K := by
    change IsOfFinOrder _
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by rw [neg_one_sq]⟩
  have hbij : Function.Bijective ψ := unitGroupStructure_bijective i₀ η hη hneg_tor
  exact ⟨(MulEquiv.ofBijective ψ hbij).symm⟩


end NumberField.SqrtTwo
