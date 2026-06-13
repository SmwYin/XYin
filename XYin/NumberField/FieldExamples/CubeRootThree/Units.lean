import XYin.NumberField.FieldExamples.CubeRootThree.PrimeSplitting

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CubeRootThree

/-! ## 6. Ring of units -/

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

/-- `ℚ(∛3)` is not totally real: `θ = ∛3` has a non-real conjugate (`∛3 · ζ₃`), giving a
non-real complex embedding. -/
theorem not_totallyReal : ¬ NumberField.IsTotallyReal K := by
  intro h
  obtain ⟨c, hc3, hcim⟩ : ∃ c : ℂ, c ^ 3 = 3 ∧ c.im ≠ 0 := by
    obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 3 :=
      ⟨_, Complex.isPrimitiveRoot_exp 3 (by norm_num)⟩
    have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
    have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
    have hquad : ζ ^ 2 + ζ + 1 = 0 := by
      have hfac : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
      rcases mul_eq_zero.mp hfac with hh | hh
      · exact absurd (sub_eq_zero.mp hh) hζ1
      · exact hh
    have hζim : ζ.im ≠ 0 := by
      intro him
      have hre : (ζ ^ 2 + ζ + 1).re = 0 := by rw [hquad]; simp
      rw [sq] at hre
      simp only [Complex.add_re, Complex.mul_re, Complex.one_re, him, mul_zero, sub_zero] at hre
      nlinarith [hre, sq_nonneg ζ.re]
    obtain ⟨c0, hc0⟩ := IsAlgClosed.exists_pow_nat_eq (3 : ℂ) (n := 3) (by norm_num)
    have hc0ne : c0 ≠ 0 := by intro hh; rw [hh] at hc0; norm_num at hc0
    by_cases hc0im : c0.im = 0
    · refine ⟨c0 * ζ, by rw [mul_pow, hc0, hζ3]; ring, ?_⟩
      rw [Complex.mul_im, hc0im, zero_mul, add_zero]
      exact mul_ne_zero (fun hh => hc0ne (Complex.ext hh hc0im)) hζim
    · exact ⟨c0, hc0, hc0im⟩
  have hroot : eval₂ (algebraMap ℚ ℂ) c cubePolynomial = 0 := by
    simp only [cubePolynomial, eval₂_sub, eval₂_pow, eval₂_X, map_ofNat]
    rw [hc3]; norm_num
  let φ : K →+* ℂ := AdjoinRoot.lift (algebraMap ℚ ℂ) c hroot
  have hφ : φ cubeRootThree = c := AdjoinRoot.lift_root hroot
  have hreal : NumberField.ComplexEmbedding.IsReal φ := h.complexEmbedding_isReal φ
  rw [NumberField.ComplexEmbedding.isReal_iff] at hreal
  have hpt := RingHom.congr_fun hreal cubeRootThree
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, hφ] at hpt
  exact hcim (Complex.conj_eq_iff_im.mp hpt)

/-- `ℚ(∛3)` has exactly one complex place: the signature is `(r₁, r₂) = (1, 1)`. -/
theorem nrComplexPlaces_eq_one : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
  have hsig : NumberField.InfinitePlace.nrRealPlaces K +
      2 * NumberField.InfinitePlace.nrComplexPlaces K = 3 := by
    rw [← degree_eq_three]; exact NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 := by
    rw [Ne, NumberField.nrComplexPlaces_eq_zero_iff]; exact not_totallyReal
  omega

/-- `ℚ(∛3)` has exactly one real place. -/
theorem nrRealPlaces_eq_one : NumberField.InfinitePlace.nrRealPlaces K = 1 := by
  have hsig : NumberField.InfinitePlace.nrRealPlaces K +
      2 * NumberField.InfinitePlace.nrComplexPlaces K = 3 := by
    rw [← degree_eq_three]; exact NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [nrComplexPlaces_eq_one] at hsig
  omega

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

/-- The unit group is `μ₂ × ℤ` as an abstract abelian group. -/
theorem unitGroupStructure :
    Nonempty ((𝓞 K)ˣ ≃* (Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ))) := by
  set i₀ : Fin (NumberField.Units.rank K) :=
    ⟨0, by rw [unitRank_eq_one]; exact Nat.zero_lt_one⟩ with hi₀
  set η : (𝓞 K)ˣ := NumberField.Units.fundSystem K i₀ with hη
  have hpow : ∀ k : ℕ, ((-1 : (𝓞 K)ˣ)) ^ k = (-1) ^ (k % 2) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k 2]
    rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
  have hsign : ∀ a b : ZMod 2,
      ((-1 : (𝓞 K)ˣ) ^ (a + b).val) = (-1) ^ a.val * (-1) ^ b.val := by
    intro a b
    calc ((-1 : (𝓞 K)ˣ) ^ (a + b).val) = (-1) ^ ((a + b).val % 2) := hpow _
      _ = (-1) ^ ((a.val + b.val) % 2) := by
          rw [ZMod.val_add, Nat.mod_mod_of_dvd _ (dvd_refl 2)]
      _ = (-1) ^ (a.val + b.val) := (hpow _).symm
      _ = (-1) ^ a.val * (-1) ^ b.val := pow_add _ _ _
  let ψ₁ : Multiplicative (ZMod 2) →* (𝓞 K)ˣ :=
    MonoidHom.mk' (fun a => (-1 : (𝓞 K)ˣ) ^ (Multiplicative.toAdd a).val)
      (fun a b => hsign (Multiplicative.toAdd a) (Multiplicative.toAdd b))
  let ψ₂ : Multiplicative (Fin 1 → ℤ) →* (𝓞 K)ˣ :=
    MonoidHom.mk' (fun f => η ^ (Multiplicative.toAdd f 0))
      (fun f g => by
        change η ^ ((Multiplicative.toAdd f + Multiplicative.toAdd g) 0) = _
        rw [Pi.add_apply, zpow_add])
  let ψ : Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ) →* (𝓞 K)ˣ := ψ₁.coprod ψ₂
  have hneg_tor : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).mpr (by
      rw [isOfFinOrder_iff_pow_eq_one]; exact ⟨2, by norm_num, by rw [neg_one_sq]⟩)
  have hbij : Function.Bijective ψ := by
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
      have hn0 : Multiplicative.toAdd f 0 = 0 := fundSystem_zpow_mem_torsion i₀ _ htor
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
        rw [show ((0 : ZMod 2)).val = 0 from rfl, pow_zero, hu, one_mul]
      · refine ⟨(Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (fun _ => n)), ?_⟩
        change (-1 : (𝓞 K)ˣ) ^ ((1 : ZMod 2)).val * η ^ n = u
        rw [show ((1 : ZMod 2)).val = 1 from rfl, pow_one, hu]
  exact ⟨(MulEquiv.ofBijective ψ hbij).symm⟩

/-- The regulator of `ℚ(∛3)` is `|log(∛9 - 2)| = log(2∛9 + 3∛3 + 4) ≈ 2.5246`, the covolume
of the unit lattice. This is the analytic restatement that `θ² - 2` is a fundamental unit:
the regulator equals the absolute logarithm of its image under the real embedding. -/
theorem regulator_eq :
    NumberField.Units.regulator K = |Real.log ((3 : ℝ) ^ ((2 : ℝ) / 3) - 2)| := by
  sorry


end NumberField.CubeRootThree
