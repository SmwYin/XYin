import XYin.NumberField.FieldExamples.SqrtTwo.PrimeSplitting

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace XYin.NumberField.SqrtTwo

/-! ## 6. Ring of units -/

/-!
This Pell-theoretic unit analysis is genuinely specific to the real quadratic side.
There is no corresponding Pell section for `ℚ(ζ₃)`, which is imaginary quadratic.
-/

/-- The concrete quadratic order `ℤ[√2]` from mathlib's Pell API. -/
abbrev ZSqrtTwo : Type := Zsqrtd (2 : ℤ)

/-- The concrete `ℤ√2` model maps to the ring of integers by `√2 ↦ √2`. -/
abbrev zsqrtTwoToO2 : ZSqrtTwo →+* O2 :=
  Zsqrtd.lift ⟨sqrtTwoInteger, by simpa [sq] using sqrtTwoInteger_sq⟩

theorem zsqrtTwoToO2_apply (a b : ℤ) :
    zsqrtTwoToO2 (⟨a, b⟩ : ZSqrtTwo) =
      (a : O2) + b * sqrtTwoInteger := by
  simp [zsqrtTwoToO2]

theorem two_not_int_square : ∀ n : ℤ, (2 : ℤ) ≠ n * n := by
  intro n hn
  have hsquare : IsSquare (2 : ℤ) := ⟨n, hn⟩
  norm_num at hsquare

theorem zsqrtTwoToO2_injective : Function.Injective zsqrtTwoToO2 :=
  Zsqrtd.lift_injective
    ⟨sqrtTwoInteger, by simpa [sq] using sqrtTwoInteger_sq⟩
    two_not_int_square

theorem zsqrtTwoToO2_surjective : Function.Surjective zsqrtTwoToO2 := by
  intro x
  let a : ℤ := sqrtTwoExplicitIntegralBasis.repr x 0
  let b : ℤ := sqrtTwoExplicitIntegralBasis.repr x 1
  refine ⟨(⟨a, b⟩ : ZSqrtTwo), ?_⟩
  rw [zsqrtTwoToO2_apply]
  have hsum := sqrtTwoExplicitIntegralBasis.sum_repr x
  have h0 :
      sqrtTwoExplicitIntegralPowerBasis.basis
          ((finCongr sqrtTwoExplicitIntegralPowerBasis_dim).symm (0 : Fin 2)) =
        (1 : O2) := by
    simpa [sqrtTwoExplicitIntegralBasis, Basis.reindex_apply] using
      sqrtTwoExplicitIntegralBasis_zero
  have h1 :
      sqrtTwoExplicitIntegralPowerBasis.basis
          ((finCongr sqrtTwoExplicitIntegralPowerBasis_dim).symm (1 : Fin 2)) =
        sqrtTwoInteger := by
    simpa [sqrtTwoExplicitIntegralBasis, Basis.reindex_apply] using
      sqrtTwoExplicitIntegralBasis_one
  rw [show (a : O2) = (a : O2) * (1 : O2) by rw [mul_one]]
  rw [← h0, ← h1]
  simpa [a, b, Fin.sum_univ_two] using hsum

/-- The explicit ring equivalence `ℤ√2 ≃ 𝓞 ℚ(√2)`. -/
abbrev zsqrtTwoEquivO2 : ZSqrtTwo ≃+* O2 :=
  RingEquiv.ofBijective zsqrtTwoToO2
    ⟨zsqrtTwoToO2_injective, zsqrtTwoToO2_surjective⟩

/-- The unit `1 + √2` in the ring of integers. -/
abbrev sqrtTwoFundamentalUnit : O2ˣ where
  val := sqrtTwoInteger + 1
  inv := sqrtTwoInteger - 1
  val_inv := by
    ext
    calc
      (sqrtTwoRoot + 1) * (sqrtTwoRoot - 1) = sqrtTwoRoot ^ 2 - 1 := by ring
      _ = (1 : QSqrtTwo) := by rw [sqrtTwoRoot_sq]; ring
  inv_val := by
    ext
    calc
      (sqrtTwoRoot - 1) * (sqrtTwoRoot + 1) = sqrtTwoRoot ^ 2 - 1 := by ring
      _ = (1 : QSqrtTwo) := by rw [sqrtTwoRoot_sq]; ring

/-- The same unit `1 + √2`, but in mathlib's concrete `ℤ√2` model. -/
abbrev zsqrtTwoFundamentalUnit : ZSqrtTwoˣ where
  val := ⟨1, 1⟩
  inv := ⟨-1, 1⟩
  val_inv := by ext <;> norm_num
  inv_val := by ext <;> norm_num

theorem zsqrtTwoFundamentalUnit_norm :
    Zsqrtd.norm (zsqrtTwoFundamentalUnit : ZSqrtTwo) = -1 := by
  norm_num [zsqrtTwoFundamentalUnit, Zsqrtd.norm]

theorem zsqrtTwoEquivO2_fundamentalUnit :
    Units.mapEquiv zsqrtTwoEquivO2.toMulEquiv zsqrtTwoFundamentalUnit =
      sqrtTwoFundamentalUnit := by
  apply Units.ext
  change zsqrtTwoEquivO2 (⟨1, 1⟩ : ZSqrtTwo) = sqrtTwoInteger + 1
  change zsqrtTwoToO2 (⟨1, 1⟩ : ZSqrtTwo) = sqrtTwoInteger + 1
  rw [zsqrtTwoToO2_apply]
  ring

theorem zsqrtTwoEquivO2_unitsMap_neg (v : ZSqrtTwoˣ) :
    Units.mapEquiv zsqrtTwoEquivO2.toMulEquiv (-v) =
      -(Units.mapEquiv zsqrtTwoEquivO2.toMulEquiv v) := by
  apply Units.ext
  change zsqrtTwoEquivO2 (-(v : ZSqrtTwo)) =
    -zsqrtTwoEquivO2 (v : ZSqrtTwo)
  rw [map_neg]

/--
The square of `1 + √2` is `3 + 2√2`, a norm-one unit.
Mathlib's Pell API phrases "fundamental" for norm-one solutions, so this is
the Pell solution attached to the fundamental unit `1 + √2`.
-/
theorem sqrtTwoFundamentalUnit_sq :
    ((sqrtTwoFundamentalUnit ^ 2 : O2ˣ) : O2) =
      3 + 2 * sqrtTwoInteger := by
  ext
  calc
    (sqrtTwoRoot + 1) ^ 2 =
        sqrtTwoRoot ^ 2 + 2 * sqrtTwoRoot + 1 := by ring
    _ = (3 : QSqrtTwo) + 2 * sqrtTwoRoot := by rw [sqrtTwoRoot_sq]; ring

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
theorem sqrtTwoFundamentalUnit_generates_unitGroup (u : O2ˣ) :
    ∃ n : ℤ, u = sqrtTwoFundamentalUnit ^ n ∨
      u = -(sqrtTwoFundamentalUnit ^ n) := by
  let e : ZSqrtTwoˣ ≃* O2ˣ :=
    Units.mapEquiv zsqrtTwoEquivO2.toMulEquiv
  obtain ⟨n, hn | hn⟩ :=
    zsqrtTwo_units_generated_by_fundamental (e.symm u)
  · refine ⟨n, Or.inl ?_⟩
    calc
      u = e (e.symm u) := (e.apply_symm_apply u).symm
      _ = e (zsqrtTwoFundamentalUnit ^ n) := by rw [hn]
      _ = e zsqrtTwoFundamentalUnit ^ n := by
        exact map_zpow e zsqrtTwoFundamentalUnit n
      _ = sqrtTwoFundamentalUnit ^ n := by
        rw [zsqrtTwoEquivO2_fundamentalUnit]
  · refine ⟨n, Or.inr ?_⟩
    calc
      u = e (e.symm u) := (e.apply_symm_apply u).symm
      _ = e (-(zsqrtTwoFundamentalUnit ^ n)) := by rw [hn]
      _ = -(e (zsqrtTwoFundamentalUnit ^ n)) := by
        exact zsqrtTwoEquivO2_unitsMap_neg (zsqrtTwoFundamentalUnit ^ n)
      _ = -(e zsqrtTwoFundamentalUnit ^ n) := by
        rw [map_zpow e zsqrtTwoFundamentalUnit n]
      _ = -(sqrtTwoFundamentalUnit ^ n) := by
        rw [zsqrtTwoEquivO2_fundamentalUnit]

/-- The field `ℚ(√2)` has no complex infinite places. -/
theorem sqrtTwo_nrComplexPlaces :
    NumberField.InfinitePlace.nrComplexPlaces QSqrtTwo = 0 := by
  have hfin : Module.finrank ℚ QSqrtTwo = 2 := by
    rw [PowerBasis.finrank sqrtTwoPowerBasis]
    exact sqrtTwoPowerBasis_dim
  have hsig := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := QSqrtTwo)
  rw [hfin] at hsig
  have hsign := NumberField.sign_discr (K := QSqrtTwo)
  rw [sqrtTwo_numberField_discr] at hsign
  have hnle : NumberField.InfinitePlace.nrComplexPlaces QSqrtTwo ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hnle with hn | hn
  · exact hn
  · rw [hn] at hsign
    norm_num at hsign

/-- The field `ℚ(√2)` has two real infinite places. -/
theorem sqrtTwo_nrRealPlaces :
    NumberField.InfinitePlace.nrRealPlaces QSqrtTwo = 2 := by
  have hfin : Module.finrank ℚ QSqrtTwo = 2 := by
    rw [PowerBasis.finrank sqrtTwoPowerBasis]
    exact sqrtTwoPowerBasis_dim
  have hsig := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := QSqrtTwo)
  rw [hfin, sqrtTwo_nrComplexPlaces] at hsig
  omega

/-- The only torsion units in `𝓞 ℚ(√2)` are `±1`. -/
theorem sqrtTwo_torsion_eq_one_or_neg_one
    (x : Units.torsion QSqrtTwo) : (x : O2ˣ) = 1 ∨ (x : O2ˣ) = -1 := by
  by_cases! hc : 2 < orderOf (x : O2ˣ)
  · have horder :
        orderOf ((x : O2ˣ) : QSqrtTwo) = orderOf (x : O2ˣ) := by
      simpa using
        (orderOf_injective
          ((Units.coeHom QSqrtTwo).comp (Units.map (algebraMap O2 QSqrtTwo)))
          (by
            intro u v huv
            exact NumberField.Units.coe_injective (K := QSqrtTwo) huv)
          (x : O2ˣ))
    have hcK : 2 < orderOf ((x : O2ˣ) : QSqrtTwo) := by
      rwa [horder]
    linarith [
      NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hcK
        (IsPrimitiveRoot.orderOf ((x : O2ˣ) : QSqrtTwo)),
      show 0 < NumberField.InfinitePlace.nrRealPlaces QSqrtTwo by
        rw [sqrtTwo_nrRealPlaces]
        norm_num]
  · interval_cases hi : orderOf (x : O2ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
    · exact Or.inl (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, Units.val_neg, Units.val_one, hi]

/-- The torsion subgroup of `𝓞 ℚ(√2)` has order `2`. -/
theorem sqrtTwo_units_torsionOrder :
    Units.torsionOrder QSqrtTwo = 2 := by
  classical
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact sqrtTwo_torsion_eq_one_or_neg_one x

/-- Dirichlet's unit rank is `1` for this real quadratic field. -/
theorem sqrtTwo_units_rank :
    Units.rank QSqrtTwo = 1 := by
  dsimp [Units.rank]
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    sqrtTwo_nrRealPlaces, sqrtTwo_nrComplexPlaces]

example : Units.torsionOrder QSqrtTwo = 2 :=
  sqrtTwo_units_torsionOrder

example : Units.rank QSqrtTwo = 1 :=
  sqrtTwo_units_rank

/-- The regulator of `ℚ(√2)` is `log(1 + √2) ≈ 0.8814`, the covolume of the unit lattice.
This is the analytic restatement that `1 + √2` is a fundamental unit. -/
theorem regulator_eq : Units.regulator QSqrtTwo = Real.log (1 + Real.sqrt 2) := by
  sorry

/-- The unit group is `μ₂ × ℤ` as an abstract abelian group. -/
theorem unitGroupStructure :
    Nonempty (O2ˣ ≃* (Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ))) := by
  sorry


end XYin.NumberField.SqrtTwo
