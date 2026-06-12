import XYin.NumberField.FieldExamples.SqrtFive.PrimeSplitting

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace XYin.NumberField.SqrtFive

private theorem goldenIntO_sq : goldenIntO ^ 2 = goldenIntO + 1 :=
  Subtype.ext (by push_cast [goldenIntO]; exact goldenRoot_sq)

/-! ## 6. Ring of units -/

private theorem ringHom_ext_golden {f g : QSqrtFive →+* ℂ} (h : f goldenRoot = g goldenRoot) :
    f = g := by
  ext z
  obtain ⟨x, y⟩ := z
  rw [QuadraticAlgebra.mk_eq_add_smul_omega, map_add, map_add]
  congr 1
  · exact (eq_ratCast (f.comp (algebraMap ℚ QSqrtFive)) x).trans
      (eq_ratCast (g.comp (algebraMap ℚ QSqrtFive)) x).symm
  · rw [Algebra.smul_def, map_mul, map_mul]
    exact congrArg₂ (fun a b => a * b)
      ((eq_ratCast (f.comp (algebraMap ℚ QSqrtFive)) y).trans
        (eq_ratCast (g.comp (algebraMap ℚ QSqrtFive)) y).symm) h

private theorem isTotallyReal : NumberField.IsTotallyReal QSqrtFive := by
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
noncomputable def fundamentalUnit : (𝓞 QSqrtFive)ˣ where
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
theorem nrRealPlaces_eq_two : InfinitePlace.nrRealPlaces QSqrtFive = 2 := by
  haveI := isTotallyReal
  have hcomplex := NumberField.IsTotallyReal.nrComplexPlaces_eq_zero QSqrtFive
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank QSqrtFive
  rw [hcomplex, degree_eq_two] at h
  omega

/-- The field `ℚ(√5)` has no complex infinite places. -/
theorem nrComplexPlaces_eq_zero : InfinitePlace.nrComplexPlaces QSqrtFive = 0 := by
  haveI := isTotallyReal
  exact NumberField.IsTotallyReal.nrComplexPlaces_eq_zero QSqrtFive

/-- A torsion generator of `𝓞 QSqrtFiveˣ`, mathematically `-1`. -/
abbrev torsionGenerator : (𝓞 QSqrtFive)ˣ := -1

/-- The concrete torsion units `{1, -1}`. -/
def torsionUnits : Set ((𝓞 QSqrtFive)ˣ) := {u | ∃ k : Fin 2, u = torsionGenerator ^ k.val}

private noncomputable def realEmb : QSqrtFive →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨(1 + Real.sqrt 5) / 2, by
    have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
    rw [show ((1 + Real.sqrt 5) / 2) * ((1 + Real.sqrt 5) / 2) =
        (3 + Real.sqrt 5) / 2 by nlinarith]
    simp
    ring⟩

private theorem torsionUnits_eq : {u : (𝓞 QSqrtFive)ˣ | IsOfFinOrder u} = torsionUnits := by
  set e : QSqrtFive →+* ℝ := realEmb.toRingHom with he
  ext u
  constructor
  · intro hu
    obtain ⟨n, hn, hun⟩ := isOfFinOrder_iff_pow_eq_one.mp hu
    set x : QSqrtFive :=
      algebraMap (𝓞 QSqrtFive) QSqrtFive ((u : (𝓞 QSqrtFive)ˣ) : 𝓞 QSqrtFive) with hx
    have hxn : x ^ n = 1 := by
      have hval : ((u ^ n : (𝓞 QSqrtFive)ˣ) : 𝓞 QSqrtFive) = 1 := by rw [hun]; rfl
      rw [hx, ← map_pow,
        show (((u : (𝓞 QSqrtFive)ˣ) : 𝓞 QSqrtFive)) ^ n =
          ((u ^ n : (𝓞 QSqrtFive)ˣ) : 𝓞 QSqrtFive) from
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
    have hinj := IsFractionRing.injective (𝓞 QSqrtFive) QSqrtFive
    rcases hex with h | h
    · refine ⟨0, ?_⟩
      have hx1 : x = 1 := e.injective (by rw [h, map_one])
      have hu1 : ((u : (𝓞 QSqrtFive)ˣ) : 𝓞 QSqrtFive) = 1 :=
        hinj (by rw [map_one, ← hx]; exact hx1)
      rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, pow_zero]
      exact Units.ext hu1
    · refine ⟨1, ?_⟩
      have hx1 : x = -1 := e.injective (by rw [h]; simp)
      have hu1 : ((u : (𝓞 QSqrtFive)ˣ) : 𝓞 QSqrtFive) = -1 :=
        hinj (by rw [map_neg, map_one, ← hx]; exact hx1)
      rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, pow_one]
      exact Units.ext hu1
  · rintro ⟨k, rfl⟩
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, ?_⟩
    rw [← pow_mul, mul_comm, pow_mul]
    simp

/-- The torsion subgroup of `𝓞 Kˣ` has order `2`: a totally real field has only the roots of
unity `±1`. -/
theorem torsionOrder_eq_two : Units.torsionOrder QSqrtFive = 2 := by
  have hcard : Nat.card (NumberField.Units.torsion QSqrtFive) = 2 := by
    rw [Nat.card_eq_two_iff]
    have hmem1 : (1 : (𝓞 QSqrtFive)ˣ) ∈ NumberField.Units.torsion QSqrtFive :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩
    have hmemn : (-1 : (𝓞 QSqrtFive)ˣ) ∈ NumberField.Units.torsion QSqrtFive := by
      change IsOfFinOrder _
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simp⟩
    refine ⟨⟨1, hmem1⟩, ⟨-1, hmemn⟩, ?_, ?_⟩
    · intro h
      have hval := congrArg (fun z => ((z : (𝓞 QSqrtFive)ˣ) : 𝓞 QSqrtFive))
        (Subtype.ext_iff.mp h)
      simp only [Units.val_one, Units.val_neg] at hval
      have h2 := congrArg (algebraMap (𝓞 QSqrtFive) QSqrtFive) hval
      simp only [map_one, map_neg] at h2
      exact two_ne_zero (by linear_combination h2 : (2 : QSqrtFive) = 0)
    · ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      have hz : (z : (𝓞 QSqrtFive)ˣ) ∈ {u : (𝓞 QSqrtFive)ˣ | IsOfFinOrder u} := z.2
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
theorem unitRank_eq_one : Units.rank QSqrtFive = 1 := by
  rw [NumberField.Units.rank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_eq_two, nrComplexPlaces_eq_zero]

private theorem normFundamentalUnit_map :
    Units.map (Algebra.norm ℤ : (𝓞 QSqrtFive) →* ℤ) fundamentalUnit = (-1 : ℤˣ) := by
  apply Units.ext
  change Algebra.norm ℤ goldenIntO = (-1 : ℤ)
  have h := intNorm_eq_normForm 0 1
  simpa using h

private theorem normNegOneUnit_map :
    Units.map (Algebra.norm ℤ : (𝓞 QSqrtFive) →* ℤ) (-1 : (𝓞 QSqrtFive)ˣ) = 1 := by
  apply Units.ext
  change Algebra.norm ℤ ((-1 : (𝓞 QSqrtFive)ˣ) : 𝓞 QSqrtFive) = (1 : ℤ)
  have h := intNorm_eq_normForm (-1) 0
  have hneg : (-1 : ℤ) • (1 : 𝓞 QSqrtFive) + (0 : ℤ) • goldenIntO =
      ((-1 : (𝓞 QSqrtFive)ˣ) : 𝓞 QSqrtFive) := by
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
    Units.map (Algebra.norm ℤ : (𝓞 QSqrtFive) →* ℤ) (fundamentalUnit ^ n) =
      (-1 : ℤˣ) ^ n := by
  rw [map_zpow, normFundamentalUnit_map]
  rfl

private theorem normNegFundamentalUnit_zpow_map (n : ℤ) :
    Units.map (Algebra.norm ℤ : (𝓞 QSqrtFive) →* ℤ) (-(fundamentalUnit ^ n)) =
      (-1 : ℤˣ) ^ n := by
  rw [show (-(fundamentalUnit ^ n) : (𝓞 QSqrtFive)ˣ) =
      (-1 : (𝓞 QSqrtFive)ˣ) * fundamentalUnit ^ n by
    rw [neg_eq_neg_one_mul]]
  rw [map_mul, normNegOneUnit_map, one_mul, normFundamentalUnit_zpow_map]

/-- Every unit of `𝓞 ℚ(√5)` is a signed power of the golden ratio `φ`. -/
theorem fundamentalUnit_generates (u : (𝓞 QSqrtFive)ˣ) :
    ∃ n : ℤ, u = fundamentalUnit ^ n ∨ u = -(fundamentalUnit ^ n) := by
  -- Blocked: `SqrtTwo.lean` proves the analogous statement through `Zsqrtd` and
  -- `Pell.Solution₁` for `x^2 - d*y^2 = 1`.  Here the full ring of integers is the
  -- half-integral order `ℤ[(1 + √5)/2]`; the corresponding equation is
  -- `x^2 + x*y - y^2 = ±1` (equivalently `a^2 - 5*b^2 = ±4`).  The project currently has
  -- no completed bridge from that Fibonacci/Pell-±4 equation to the displayed unit `φ`.
  sorry

/-- The norm-one Pell solutions are generated by the square of the fundamental unit. -/
theorem normOneUnit_generated_by_fundamentalUnit_sq (u : (𝓞 QSqrtFive)ˣ)
    (hu : Algebra.norm ℤ (u : 𝓞 QSqrtFive) = 1) :
    ∃ n : ℤ, u = fundamentalUnit ^ (2 * n) ∨
      u = -(fundamentalUnit ^ (2 * n)) := by
  have hnormUnit : Units.map (Algebra.norm ℤ : (𝓞 QSqrtFive) →* ℤ) u = 1 := by
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
    Units.regulator QSqrtFive = Real.log ((1 + Real.sqrt 5) / 2) := by
  -- Blocked: this is intentionally the final theorem with no complete reference proof yet.
  sorry

/-- The unit group is `μ₂ × ℤ` as an abstract abelian group. -/
theorem unitGroupStructure :
    Nonempty ((𝓞 QSqrtFive)ˣ ≃* (Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ))) := by
  -- Blocked: the abstract rank/torsion APIs are available, but the reference proof still
  -- depends on an unfinished independence/generation lemma for a fundamental system.
  sorry


end XYin.NumberField.SqrtFive
