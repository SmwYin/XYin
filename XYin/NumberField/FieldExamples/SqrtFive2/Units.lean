import XYin.NumberField.FieldExamples.SqrtFive2.PrimeSplitting

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace XYin.NumberField.SqrtFiveGoldenAdjoinRoot

/-! ## 6. Ring of units -/

/-- A torsion generator of `𝓞 Kˣ`, mathematically `-1`. -/
abbrev torsionGenerator : (𝓞 K)ˣ := -1

/-- The concrete torsion units `{1, -1}`. -/
def torsionUnits : Set ((𝓞 K)ˣ) := {u | ∃ k : Fin 2, u = torsionGenerator ^ k.val}

/-- An explicit real embedding `√5 ↦ √5`. -/
noncomputable def realEmb : K →ₐ[ℚ] ℝ :=
  AdjoinRoot.liftAlgHom sqrtFivePolynomial (Algebra.ofId ℚ ℝ) (Real.sqrt 5) (by
    calc sqrtFivePolynomial.eval₂ (Algebra.ofId ℚ ℝ) (Real.sqrt 5)
        = (Real.sqrt 5) ^ 2 - 5 := by simp [sqrtFivePolynomial]
      _ = 0 := by
          rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
          ring)

/-- The torsion subgroup of `𝓞 Kˣ` is exactly `{1, -1}`: a real embedding only allows the
roots of unity `±1`. -/
theorem torsionUnits_eq : {u : (𝓞 K)ˣ | IsOfFinOrder u} = torsionUnits := by
  set e : K →+* ℝ := realEmb.toRingHom with he
  ext u
  constructor
  · intro hu
    obtain ⟨n, hn, hun⟩ := isOfFinOrder_iff_pow_eq_one.mp hu
    set x : K := algebraMap (𝓞 K) K ((u : (𝓞 K)ˣ) : 𝓞 K) with hx
    have hxn : x ^ n = 1 := by
      have hval : ((u ^ n : (𝓞 K)ˣ) : 𝓞 K) = 1 := by rw [hun]; rfl
      rw [hx, ← map_pow, show (((u : (𝓞 K)ˣ) : 𝓞 K)) ^ n = ((u ^ n : (𝓞 K)ˣ) : 𝓞 K) from
        (Units.val_pow_eq_pow_val _ _).symm, hval, map_one]
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
      have hu1 : ((u : (𝓞 K)ˣ) : 𝓞 K) = 1 := hinj (by rw [map_one, ← hx]; exact hx1)
      rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, pow_zero]
      exact Units.ext hu1
    · refine ⟨1, ?_⟩
      have hx1 : x = -1 := e.injective (by rw [h]; simp)
      have hu1 : ((u : (𝓞 K)ˣ) : 𝓞 K) = -1 := hinj (by rw [map_neg, map_one, ← hx]; exact hx1)
      rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, pow_one]
      exact Units.ext hu1
  · rintro ⟨k, rfl⟩
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, ?_⟩
    rw [← pow_mul, mul_comm, pow_mul]
    simp

/-- The torsion subgroup of `𝓞 Kˣ` has order `2`. -/
theorem torsionOrder_eq_two : NumberField.Units.torsionOrder K = 2 := by
  have hcard : Nat.card (NumberField.Units.torsion K) = 2 := by
    rw [Nat.card_eq_two_iff]
    have hmem1 : (1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩
    have hmemn : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K := by
      change IsOfFinOrder _
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩
    refine ⟨⟨1, hmem1⟩, ⟨-1, hmemn⟩, ?_, ?_⟩
    · intro h
      have hval := congrArg (fun z => ((z : (𝓞 K)ˣ) : 𝓞 K)) (Subtype.ext_iff.mp h)
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

/-- `ℚ(√5)` is totally real: both embeddings `√5 ↦ ±√5` land in `ℝ`. (Contrast with the
pure cubic `ℚ(∛3)`, which has a complex place.) -/
theorem ringHom_ext_sqrtFive {f g : K →+* ℂ} (h : f sqrtFive = g sqrtFive) :
    f = g := by
  refine RingHom.ext fun z => ?_
  obtain ⟨a, b, rfl⟩ := exists_coords z
  rw [map_add, map_add, map_mul, map_mul]
  congr 1
  · exact (eq_ratCast (f.comp (algebraMap ℚ K)) a).trans
      (eq_ratCast (g.comp (algebraMap ℚ K)) a).symm
  · exact congrArg₂ (fun u v => u * v)
      ((eq_ratCast (f.comp (algebraMap ℚ K)) b).trans
        (eq_ratCast (g.comp (algebraMap ℚ K)) b).symm) h

theorem isTotallyReal : NumberField.IsTotallyReal K := by
  refine ⟨fun v => ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
  refine ringHom_ext_sqrtFive ?_
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  set z := NumberField.InfinitePlace.embedding v sqrtFive with hz
  have hsq : z ^ 2 = 5 := by
    rw [hz, ← map_pow, sqrtFive_sq, map_ofNat]
  have hc : (starRingEnd ℂ) z ^ 2 = 5 := by
    rw [← map_pow, hsq]
    exact map_ofNat _ 5
  have hfac : ((starRingEnd ℂ) z - z) * ((starRingEnd ℂ) z + z) = 0 := by
    linear_combination hc - hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hzneg : (starRingEnd ℂ) z = -z := by linear_combination h
    have hre : z.re = 0 := by
      have hcr := congrArg Complex.re hzneg
      rw [Complex.conj_re, Complex.neg_re] at hcr
      linarith
    have h5 := congrArg Complex.re hsq
    rw [sq, Complex.mul_re, hre] at h5
    norm_num at h5
    nlinarith [sq_nonneg z.im, h5]

/-- The signature of `ℚ(√5)` is `(2, 0)`: two real places, no complex place. -/
theorem nrComplexPlaces_eq_zero :
    NumberField.InfinitePlace.nrComplexPlaces K = 0 := by
  haveI := isTotallyReal
  exact NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K

theorem nrRealPlaces_eq_two : NumberField.InfinitePlace.nrRealPlaces K = 2 := by
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [nrComplexPlaces_eq_zero, degree_eq_two] at h
  omega

/-- The Dirichlet unit rank of `ℚ(√5)` is `1`: the signature is `(2, 0)`, so the rank is
`r₁ + r₂ - 1 = 1`. -/
theorem unitRank_eq_one : NumberField.Units.rank K = 1 := by
  rw [NumberField.Units.rank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_eq_two, nrComplexPlaces_eq_zero]

/-- The fundamental unit of `𝓞 K`: the golden ratio `φ`, with explicit inverse `φ - 1`
(since `φ(φ - 1) = φ² - φ = 1`). -/
noncomputable def fundamentalUnit : (𝓞 K)ˣ where
  val := goldenInt
  inv := goldenInt - 1
  val_inv := by linear_combination goldenInt_sq
  inv_val := by linear_combination goldenInt_sq

/-- The golden ratio has norm `-1`: equivalently, the negative Pell equation
`x² + xy - y² = -1` is solvable (e.g. `(x, y) = (0, 1)`). Not every real quadratic field has
a unit of norm `-1`. -/
theorem intNorm_goldenInt : Algebra.norm ℤ goldenInt = -1 := by
  have h := intNorm_eq_normForm 0 1
  simpa using h

/-- The system of fundamental units for the rank-`1` unit group: the single unit `φ`. -/
noncomputable def fundamentalUnitSystem : Fin (NumberField.Units.rank K) → (𝓞 K)ˣ :=
  fun _ => fundamentalUnit

/-- Mathlib's abstract fundamental unit `fundSystem K i₀`, together with the torsion,
generates the whole unit group. -/
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

/-- A power of the abstract fundamental unit is torsion only for exponent zero. -/
theorem fundSystem_zpow_mem_torsion (i₀ : Fin (NumberField.Units.rank K)) (n : ℤ)
    (hn : NumberField.Units.fundSystem K i₀ ^ n ∈ NumberField.Units.torsion K) : n = 0 := by
  sorry

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

/-- The displayed family is a system of fundamental units: together with `±1`, the golden
ratio generates all units of `ℤ[φ]`. -/
theorem fundamentalUnitSystem_isFundamental :
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K = ⊤ := by
  sorry

/-- Equivalently, every unit of `ℤ[φ]` is `±φⁿ` for some `n ∈ ℤ`. -/
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

/-- Every unit of `𝓞 ℚ(√5)` is a signed power of the golden ratio `φ`. -/
theorem fundamentalUnit_generates (u : (𝓞 K)ˣ) :
    ∃ n : ℤ, u = fundamentalUnit ^ n ∨ u = -(fundamentalUnit ^ n) := by
  obtain ⟨ζ, hζ, n, hu⟩ := unit_eq_torsion_mul_fundamentalUnit_zpow u
  rcases eq_one_or_neg_one_of_mem_torsion hζ with hζ | hζ
  · refine ⟨n, Or.inl ?_⟩
    simpa [hζ] using hu
  · refine ⟨n, Or.inr ?_⟩
    rw [hζ] at hu
    simpa using hu

/-- The norm-one Pell solutions are generated by the square of the fundamental unit. -/
theorem normOneUnit_generated_by_fundamentalUnit_sq (u : (𝓞 K)ˣ)
    (hu : Algebra.norm ℤ (u : 𝓞 K) = 1) :
    ∃ n : ℤ, u = fundamentalUnit ^ (2 * n) ∨
      u = -(fundamentalUnit ^ (2 * n)) := by
  sorry

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
  have hneg_tor : (-1 : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K := by
    change IsOfFinOrder _
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by rw [neg_one_sq]⟩
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
        rw [show ((0 : ZMod 2)).val = 0 from rfl, pow_zero, hu, one_mul]
      · refine ⟨(Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (fun _ => n)), ?_⟩
        change (-1 : (𝓞 K)ˣ) ^ ((1 : ZMod 2)).val * η ^ n = u
        rw [show ((1 : ZMod 2)).val = 1 from rfl, pow_one, hu]
  exact ⟨(MulEquiv.ofBijective ψ hbij).symm⟩

/-- The regulator of `ℚ(√5)` is `log φ = log((1 + √5)/2) ≈ 0.4812` — the smallest regulator
of any number field with infinite unit group. -/
theorem regulator_eq :
    NumberField.Units.regulator K = Real.log ((1 + Real.sqrt 5) / 2) := by
  sorry


end XYin.NumberField.SqrtFiveGoldenAdjoinRoot
