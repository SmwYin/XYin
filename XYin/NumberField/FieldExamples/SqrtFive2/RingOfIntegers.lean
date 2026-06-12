import XYin.NumberField.FieldExamples.SqrtFive2.Basic

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace XYin.NumberField.SqrtFiveGoldenAdjoinRoot

noncomputable abbrev sqrtFivePB : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis (f := sqrtFivePolynomial)
    ((Fact.out : Irreducible sqrtFivePolynomial).ne_zero)

theorem sqrtFivePB_dim : sqrtFivePB.dim = 2 := by
  change sqrtFivePolynomial.natDegree = 2
  rw [sqrtFivePolynomial, natDegree_X_pow_sub_C]

theorem sqrtFivePB_gen : sqrtFivePB.gen = sqrtFive := by
  simp [sqrtFivePB, sqrtFive]

/-! ## 2. Integral basis and ring of integers -/

/-- The golden ratio is integral over `ℤ` (a root of the monic `X² - X - 1`), hence lies in
`𝓞 K`. This is where `5 ≡ 1 (mod 4)` enters: for `d ≡ 1 (mod 4)` the integers of `ℚ(√d)`
are `ℤ[(1 + √d)/2]`, not `ℤ[√d]`. -/
theorem goldenInteger_integral : goldenInteger ∈ integralClosure ℤ K := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X - 1, ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_one]
    linear_combination goldenInteger_sq

/-- `φ` as an element of the ring of integers `𝓞 K`. -/
noncomputable def goldenInt : 𝓞 K := ⟨goldenInteger, goldenInteger_integral⟩

/-- The integral golden ratio also satisfies `φ² = φ + 1` in `𝓞 K`. -/
theorem goldenInt_sq : goldenInt ^ 2 = goldenInt + 1 :=
  Subtype.ext (by push_cast [goldenInt]; exact goldenInteger_sq)

/-- `√5 = 2φ - 1` as an element of `𝓞 K`. -/
noncomputable def sqrtFiveInt : 𝓞 K := 2 * goldenInt - 1

/-! ### The auxiliary integral `AdjoinRoot` model `ℤ[φ]` -/

/-- The golden-ratio polynomial over `ℤ`. -/
abbrev goldenIntegerPolynomial : ℤ[X] :=
  C (1 : ℤ) * X ^ 2 + C (-1 : ℤ) * X + C (-1 : ℤ)

theorem goldenIntegerPolynomial_monic : goldenIntegerPolynomial.Monic := by
  rw [goldenIntegerPolynomial]
  monicity
  all_goals norm_num

theorem goldenIntegerPolynomial_natDegree : goldenIntegerPolynomial.natDegree = 2 := by
  rw [goldenIntegerPolynomial]
  exact natDegree_quadratic (by norm_num : (1 : ℤ) ≠ 0)

/-- The integral order `ℤ[φ]`, presented as an `AdjoinRoot`. -/
abbrev O5 : Type := AdjoinRoot goldenIntegerPolynomial

/-- The algebraic integer `φ` in the auxiliary order `O5`. -/
abbrev goldenIntegerO5 : O5 := AdjoinRoot.root goldenIntegerPolynomial

theorem goldenIntegerO5_sq : goldenIntegerO5 ^ 2 = goldenIntegerO5 + 1 := by
  have hroot : goldenIntegerO5 ^ 2 - goldenIntegerO5 - 1 = 0 := by
    simpa [goldenIntegerO5, goldenIntegerPolynomial] using
      AdjoinRoot.eval₂_root goldenIntegerPolynomial
  calc
    goldenIntegerO5 ^ 2 = goldenIntegerO5 + 1 + (goldenIntegerO5 ^ 2 - goldenIntegerO5 - 1) := by
      ring
    _ = goldenIntegerO5 + 1 := by rw [hroot]; ring

theorem goldenIntegerO5_isIntegral : IsIntegral ℤ goldenIntegerO5 :=
  AdjoinRoot.isIntegral_root' goldenIntegerPolynomial_monic

theorem goldenRoot_is_root_goldenIntegerPolynomial :
    goldenIntegerPolynomial.eval₂ (algebraMap ℤ K) goldenRoot = 0 := by
  simp [goldenIntegerPolynomial, goldenRoot_sq]

/-- The natural embedding of the auxiliary integral model into the field model. -/
def goldenOrderToField : O5 →+* K :=
  AdjoinRoot.lift (algebraMap ℤ K) goldenRoot
    goldenRoot_is_root_goldenIntegerPolynomial

@[simp]
theorem goldenOrderToField_goldenIntegerO5 :
    goldenOrderToField goldenIntegerO5 = goldenRoot :=
  AdjoinRoot.lift_root goldenRoot_is_root_goldenIntegerPolynomial

instance : Algebra O5 K :=
  goldenOrderToField.toAlgebra

@[simp]
theorem algebraMap_O5_QSqrtFive_eq_goldenOrderToField (x : O5) :
    algebraMap O5 K x = goldenOrderToField x :=
  rfl

instance : IsScalarTower ℤ O5 K :=
  IsScalarTower.of_algebraMap_eq fun _ => by simp

/-- The integral power basis `1, φ` of the auxiliary order `ℤ[φ]`. -/
abbrev sqrtFiveExplicitIntegralPowerBasis : PowerBasis ℤ O5 :=
  AdjoinRoot.powerBasis' goldenIntegerPolynomial_monic

theorem sqrtFiveExplicitIntegralPowerBasis_gen :
    sqrtFiveExplicitIntegralPowerBasis.gen = goldenIntegerO5 := by
  rfl

theorem sqrtFiveExplicitIntegralPowerBasis_dim :
    sqrtFiveExplicitIntegralPowerBasis.dim = 2 := by
  rw [sqrtFiveExplicitIntegralPowerBasis]
  exact goldenIntegerPolynomial_natDegree

instance : Module.Finite ℤ O5 :=
  sqrtFiveExplicitIntegralPowerBasis.finite

instance : Algebra.IsIntegral ℤ O5 where
  isIntegral x := by
    exact @IsIntegral.of_finite ℤ O5 _ _ _ sqrtFiveExplicitIntegralPowerBasis.finite x

/-- The explicit integral basis `[1, φ]` of the auxiliary order. -/
abbrev sqrtFiveExplicitIntegralBasis : Basis (Fin 2) ℤ O5 :=
  sqrtFiveExplicitIntegralPowerBasis.basis.reindex
    (finCongr sqrtFiveExplicitIntegralPowerBasis_dim)

theorem sqrtFiveExplicitIntegralBasis_zero :
    sqrtFiveExplicitIntegralBasis 0 = 1 := by
  rw [sqrtFiveExplicitIntegralBasis]
  change (sqrtFiveExplicitIntegralPowerBasis.basis.reindex
      (finCongr sqrtFiveExplicitIntegralPowerBasis_dim)) 0 = 1
  rw [sqrtFiveExplicitIntegralPowerBasis.basis.reindex_apply]
  rw [sqrtFiveExplicitIntegralPowerBasis.basis_eq_pow]
  have hcoe :
      (((finCongr sqrtFiveExplicitIntegralPowerBasis_dim).symm (0 : Fin 2) :
        Fin sqrtFiveExplicitIntegralPowerBasis.dim) : ℕ) = 0 := rfl
  rw [hcoe]
  simp

theorem sqrtFiveExplicitIntegralBasis_one :
    sqrtFiveExplicitIntegralBasis 1 = goldenIntegerO5 := by
  rw [sqrtFiveExplicitIntegralBasis]
  change (sqrtFiveExplicitIntegralPowerBasis.basis.reindex
      (finCongr sqrtFiveExplicitIntegralPowerBasis_dim)) 1 = goldenIntegerO5
  rw [sqrtFiveExplicitIntegralPowerBasis.basis.reindex_apply]
  rw [sqrtFiveExplicitIntegralPowerBasis.basis_eq_pow]
  have hcoe :
      (((finCongr sqrtFiveExplicitIntegralPowerBasis_dim).symm (1 : Fin 2) :
        Fin sqrtFiveExplicitIntegralPowerBasis.dim) : ℕ) = 1 := rfl
  rw [hcoe]
  simp

theorem goldenOrderToField_basis_zero :
    goldenOrderToField (sqrtFiveExplicitIntegralBasis 0) = 1 := by
  rw [sqrtFiveExplicitIntegralBasis_zero]
  exact goldenOrderToField.map_one

theorem goldenOrderToField_basis_one :
    goldenOrderToField (sqrtFiveExplicitIntegralBasis 1) = goldenRoot := by
  rw [sqrtFiveExplicitIntegralBasis_one]
  exact goldenOrderToField_goldenIntegerO5

theorem goldenOrderToField_basis_one_as_sqrtFive :
    goldenOrderToField (sqrtFiveExplicitIntegralBasis 1) = (sqrtFiveRoot + 1) / 2 := by
  rw [goldenOrderToField_basis_one, ← goldenRoot_eq_half_sqrtFiveRoot_add_one]

/-- The conjugation `√5 ↦ -√5` as an algebra map, via the universal property. -/
noncomputable def conjHom : K →ₐ[ℚ] K :=
  AdjoinRoot.liftAlgHom sqrtFivePolynomial (Algebra.ofId ℚ K) (-sqrtFive) (by
    calc sqrtFivePolynomial.eval₂ (Algebra.ofId ℚ K) (-sqrtFive)
        = (-sqrtFive) ^ 2 - 5 := by simp [sqrtFivePolynomial]
      _ = sqrtFive ^ 2 - 5 := by ring
      _ = 0 := by rw [sqrtFive_sq]; ring)

theorem conjHom_root : conjHom sqrtFive = -sqrtFive := by
  change conjHom (AdjoinRoot.root sqrtFivePolynomial) = -sqrtFive
  rw [conjHom]
  exact AdjoinRoot.liftAlgHom_root sqrtFivePolynomial (Algebra.ofId ℚ K) (-sqrtFive) _

theorem conjHom_conjHom : conjHom.comp conjHom = AlgHom.id ℚ K := by
  apply AdjoinRoot.algHom_ext
  change conjHom (conjHom sqrtFive) = sqrtFive
  rw [conjHom_root, map_neg, conjHom_root, neg_neg]

noncomputable def conj' : K ≃ₐ[ℚ] K :=
  AlgEquiv.ofAlgHom conjHom conjHom conjHom_conjHom conjHom_conjHom

theorem conj'_root : conj' sqrtFive = -sqrtFive := conjHom_root

/-- Every element of `K` has rational coordinates in the basis `1, √5`. -/
theorem exists_coords (x : K) :
    ∃ a b : ℚ, x = algebraMap ℚ K a + algebraMap ℚ K b * sqrtFive := by
  obtain ⟨f, hf, hx⟩ := sqrtFivePB.exists_eq_aeval x
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  have hdeg : f.natDegree ≤ 1 := by
    have := sqrtFivePB_dim ▸ hf
    omega
  conv_lhs => rw [hx, Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
  rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X,
    sqrtFivePB_gen]
  ring

theorem coords_eq_zero {a b : ℚ}
    (h : algebraMap ℚ K a + algebraMap ℚ K b * sqrtFive = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    rw [map_zero, zero_mul, add_zero] at h
    exact ⟨FaithfulSMul.algebraMap_injective ℚ K (by rw [h, map_zero]), rfl⟩
  · exfalso
    have hbK : algebraMap ℚ K b ≠ 0 := fun h0 =>
      hb (FaithfulSMul.algebraMap_injective ℚ K (by rw [h0, map_zero]))
    have hs : sqrtFive = algebraMap ℚ K (-a / b) := by
      rw [map_div₀, map_neg, eq_div_iff hbK]
      linear_combination h
    have h5 : ((-a / b) : ℚ) ^ 2 = 5 := by
      have h2 := sqrtFive_sq
      rw [hs, ← map_pow] at h2
      have h5' : algebraMap ℚ K ((-a / b) ^ 2) = algebraMap ℚ K 5 := by
        rw [h2, map_ofNat]
      exact FaithfulSMul.algebraMap_injective ℚ K h5'
    have hsq : IsSquare (5 : ℚ) := by
      rw [isSquare_iff_exists_sq]
      exact ⟨_, h5.symm⟩
    norm_num at hsq

/-- The displayed integral-basis vectors `1, φ` (as elements of `K`). -/
def integralBasisVectors : Fin 2 → K := ![1, goldenInteger]

theorem coe_goldenInt : algebraMap (𝓞 K) K goldenInt = goldenInteger := rfl

theorem conj'_coords (a b : ℚ) :
    conj' (algebraMap ℚ K a + algebraMap ℚ K b * sqrtFive) =
      algebraMap ℚ K a - algebraMap ℚ K b * sqrtFive := by
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, conj'_root]
  ring

theorem conj'_golden : conj' goldenInteger = 1 - goldenInteger := by
  rw [show goldenInteger = (1 + sqrtFive) / 2 from rfl, map_div₀, map_add, map_one, conj'_root,
    map_ofNat]
  ring

/-- Integrality forces half-integer coordinates with matching parity: every algebraic integer
of `ℚ(√5)` is `A + mφ` with `A, m ∈ ℤ`. -/
theorem exists_int_coords {x : K} (hx : IsIntegral ℤ x) :
    ∃ A m : ℤ, x = (A : ℚ) • (1 : K) + (m : ℚ) • goldenInteger := by
  obtain ⟨p, q, rfl⟩ := exists_coords x
  have hconj : IsIntegral ℤ (conj' (algebraMap ℚ K p + algebraMap ℚ K q * sqrtFive)) :=
    hx.map (conj'.toAlgHom.restrictScalars ℤ)
  rw [conj'_coords] at hconj
  have htr : IsIntegral ℤ (algebraMap ℚ K (2 * p)) := by
    have h : (algebraMap ℚ K p + algebraMap ℚ K q * sqrtFive) +
        (algebraMap ℚ K p - algebraMap ℚ K q * sqrtFive) = algebraMap ℚ K (2 * p) := by
      rw [map_mul, map_ofNat]
      ring
    rw [← h]
    exact hx.add hconj
  have hS : ∃ S : ℤ, (S : ℚ) = 2 * p := by
    have := (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ K)).mp htr
    obtain ⟨S, hS⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
    exact ⟨S, by exact_mod_cast hS⟩
  have hnm : IsIntegral ℤ (algebraMap ℚ K (p ^ 2 - 5 * q ^ 2)) := by
    have h : (algebraMap ℚ K p + algebraMap ℚ K q * sqrtFive) *
        (algebraMap ℚ K p - algebraMap ℚ K q * sqrtFive) =
          algebraMap ℚ K (p ^ 2 - 5 * q ^ 2) := by
      rw [map_sub, map_pow, map_mul, map_ofNat, map_pow]
      linear_combination (-(algebraMap ℚ K q) ^ 2) * sqrtFive_sq
    rw [← h]
    exact hx.mul hconj
  have hN : ∃ N : ℤ, (N : ℚ) = p ^ 2 - 5 * q ^ 2 := by
    have := (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ K)).mp hnm
    obtain ⟨N, hN⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
    exact ⟨N, by exact_mod_cast hN⟩
  have hxphi : IsIntegral ℤ
      ((algebraMap ℚ K p + algebraMap ℚ K q * sqrtFive) * goldenInteger) :=
    hx.mul goldenInteger_integral
  have hconjphi : IsIntegral ℤ
      (conj' ((algebraMap ℚ K p + algebraMap ℚ K q * sqrtFive) * goldenInteger)) :=
    hxphi.map (conj'.toAlgHom.restrictScalars ℤ)
  have htr2 : IsIntegral ℤ (algebraMap ℚ K (p + 5 * q)) := by
    have h : (algebraMap ℚ K p + algebraMap ℚ K q * sqrtFive) * goldenInteger +
        conj' ((algebraMap ℚ K p + algebraMap ℚ K q * sqrtFive) * goldenInteger) =
          algebraMap ℚ K (p + 5 * q) := by
      rw [map_mul, conj'_coords, conj'_golden,
        show goldenInteger = (1 + sqrtFive) / 2 from rfl, map_add, map_mul, map_ofNat]
      field_simp
      linear_combination 2 * (algebraMap ℚ K q) * sqrtFive_sq
    rw [← h]
    exact hxphi.add hconjphi
  have hU : ∃ U : ℤ, (U : ℚ) = p + 5 * q := by
    have := (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ K)).mp htr2
    obtain ⟨U, hU⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
    exact ⟨U, by exact_mod_cast hU⟩
  obtain ⟨S, hSv⟩ := hS
  obtain ⟨N, hNv⟩ := hN
  obtain ⟨U, hUv⟩ := hU
  set k : ℤ := 2 * U - S with hk
  have hkv : (k : ℚ) = 10 * q := by push_cast [hk]; linarith [hSv, hUv]
  have hk2 : k ^ 2 = 5 * (S ^ 2 - 4 * N) := by
    have hcast : ((k ^ 2 : ℤ) : ℚ) = ((5 * (S ^ 2 - 4 * N) : ℤ) : ℚ) := by
      push_cast
      rw [hkv]
      have hS2 : (S : ℚ) ^ 2 = 4 * p ^ 2 := by rw [hSv]; ring
      rw [hS2, hNv]
      ring
    exact_mod_cast hcast
  have h5k : (5 : ℤ) ∣ k := by
    have hprime : Prime (5 : ℤ) := by norm_num
    refine hprime.dvd_of_dvd_pow (n := 2) ⟨S ^ 2 - 4 * N, hk2⟩
  obtain ⟨m, hm⟩ := h5k
  have hmv : (m : ℚ) = 2 * q := by
    have h10 : ((10 : ℚ)) * q = 5 * (m : ℚ) := by
      rw [← hkv, hm]
      push_cast
      ring
    linarith
  have hA : IsIntegral ℤ (algebraMap ℚ K (p - q)) := by
    have h : algebraMap ℚ K (p - q) =
        (algebraMap ℚ K p + algebraMap ℚ K q * sqrtFive) - (m : ℚ) • goldenInteger := by
      rw [Algebra.smul_def, show algebraMap ℚ K (m : ℚ) = algebraMap ℚ K (2 * q) from by
        rw [hmv], show goldenInteger = (1 + sqrtFive) / 2 from rfl, map_sub, map_mul,
        map_ofNat]
      field_simp
      ring
    rw [h]
    have hsm : IsIntegral ℤ ((m : ℚ) • goldenInteger) := by
      rw [show ((m : ℚ)) • goldenInteger = (m : ℤ) • goldenInteger from
        (Int.cast_smul_eq_zsmul ℚ m goldenInteger)]
      exact goldenInteger_integral.smul m
    exact hx.sub hsm
  obtain ⟨A, hAv⟩ : ∃ A : ℤ, (A : ℚ) = p - q := by
    have := (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ K)).mp hA
    obtain ⟨A, hA2⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
    exact ⟨A, by exact_mod_cast hA2⟩
  refine ⟨A, m, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, mul_one,
    show algebraMap ℚ K (A : ℚ) = algebraMap ℚ K (p - q) from by rw [hAv],
    show algebraMap ℚ K (m : ℚ) = algebraMap ℚ K (2 * q) from by rw [hmv],
    show goldenInteger = (1 + sqrtFive) / 2 from rfl, map_sub, map_mul, map_ofNat]
  field_simp
  ring

/-- `1, φ` is an integral basis of `ℚ(√5)`: their `ℤ`-span in `K` is exactly the ring of
integers `𝓞 K`. -/
theorem span_integralBasisVectors_eq :
    Submodule.span ℤ (Set.range integralBasisVectors) =
      Subalgebra.toSubmodule (integralClosure ℤ K) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (fun x hx => ?_)
  · rintro y ⟨i, rfl⟩
    fin_cases i
    · exact Subalgebra.one_mem _
    · exact goldenInteger_integral
  · obtain ⟨A, m, hAm⟩ := exists_int_coords hx
    have h1 : x = A • (1 : K) + m • goldenInteger := by
      rw [hAm, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    rw [h1]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)

theorem li_one_golden : LinearIndependent ℤ ![(1 : 𝓞 K), goldenInt] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_two] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  have hgK : algebraMap (𝓞 K) K (g 0 • (1 : 𝓞 K) + g 1 • goldenInt) = 0 := by
    rw [hg, map_zero]
  rw [map_add, map_zsmul, map_zsmul, map_one, coe_goldenInt] at hgK
  have hform : (g 0 : ℤ) • (1 : K) + (g 1 : ℤ) • goldenInteger =
      algebraMap ℚ K ((g 0 : ℚ) + (g 1 : ℚ) / 2) +
        algebraMap ℚ K ((g 1 : ℚ) / 2) * sqrtFive := by
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_one,
      ← map_intCast (algebraMap ℚ K) (g 0), ← map_intCast (algebraMap ℚ K) (g 1),
      show goldenInteger = (1 + sqrtFive) / 2 from rfl, map_add, map_div₀, map_ofNat]
    field_simp
    ring
  rw [hform] at hgK
  obtain ⟨h1, h2⟩ := coords_eq_zero hgK
  have hg1 : g 1 = 0 := by
    have : (g 1 : ℚ) = 0 := by linarith [h2]
    exact_mod_cast this
  have hg0 : g 0 = 0 := by
    have h1' : (g 0 : ℚ) = 0 := by
      have : (g 1 : ℚ) = 0 := by exact_mod_cast hg1
      linarith [h1]
    exact_mod_cast h1'
  intro i
  fin_cases i
  · exact hg0
  · exact hg1

theorem span_one_golden :
    ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), goldenInt]) := by
  intro z _
  obtain ⟨A, m, hAm⟩ := exists_int_coords z.2
  have hz : z = A • (1 : 𝓞 K) + m • goldenInt := by
    refine Subtype.ext ?_
    have hmap : algebraMap (𝓞 K) K (A • (1 : 𝓞 K) + m • goldenInt) =
        (A : ℚ) • (1 : K) + (m : ℚ) • goldenInteger := by
      rw [map_add, map_zsmul, map_zsmul, map_one, coe_goldenInt,
        Int.cast_smul_eq_zsmul ℚ A (1 : K), Int.cast_smul_eq_zsmul ℚ m goldenInteger]
    exact hAm.trans hmap.symm
  rw [hz]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

/-- The integral basis `1, φ` packaged as a genuine `ℤ`-basis of the ring of integers `𝓞 K`. -/
noncomputable def concreteIntegralBasis : Basis (Fin 2) ℤ (𝓞 K) :=
  Basis.mk li_one_golden span_one_golden

/-- The packaged integral basis is, vector by vector, the displayed family `1, φ`. -/
theorem concreteIntegralBasis_apply (i : Fin 2) :
    (algebraMap (𝓞 K) K) (concreteIntegralBasis i) = integralBasisVectors i := by
  fin_cases i <;>
    simp [concreteIntegralBasis, Basis.mk_apply, integralBasisVectors, coe_goldenInt]

/-- The displayed integral basis `1, φ` spans the same `ℤ`-lattice in `K` as mathlib's
`NumberField.integralBasis K` (the correct form of "the two integral bases agree": equality
of lattices, not a mere reindexing). -/
theorem span_integralBasisVectors_eq_integralBasis :
    Submodule.span ℤ (Set.range integralBasisVectors) =
      Submodule.span ℤ (Set.range (NumberField.integralBasis K)) := by
  rw [span_integralBasisVectors_eq]
  ext x
  rw [Subalgebra.mem_toSubmodule]
  constructor
  · intro hx
    exact (NumberField.mem_span_integralBasis K).mpr (RingHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)
  · intro hx
    obtain ⟨y, hy⟩ := RingHom.mem_range.mp ((NumberField.mem_span_integralBasis K).mp hx)
    exact hy ▸ y.2

/-- The concrete order `ℤ[φ]` inside `K`. -/
abbrev concreteRingOfIntegers : Subalgebra ℤ K := Algebra.adjoin ℤ ({goldenInteger} : Set K)

/-- The full ring of integers of `ℚ(√5)` is `ℤ[φ]`: the golden ratio generates a maximal
order. -/
theorem ringOfIntegers_eq : integralClosure ℤ K = concreteRingOfIntegers := by
  refine le_antisymm (fun x hx => ?_)
    (Algebra.adjoin_le (Set.singleton_subset_iff.mpr goldenInteger_integral))
  obtain ⟨A, m, hAm⟩ := exists_int_coords hx
  rw [show x = (A : ℚ) • (1 : K) + (m : ℚ) • goldenInteger from hAm,
    Int.cast_smul_eq_zsmul ℚ A (1 : K), Int.cast_smul_eq_zsmul ℚ m goldenInteger, zsmul_one]
  have hφ : goldenInteger ∈ concreteRingOfIntegers := Algebra.subset_adjoin rfl
  have hm : m • goldenInteger ∈ concreteRingOfIntegers := zsmul_mem hφ m
  have hA : ((A : ℤ) : K) ∈ concreteRingOfIntegers := intCast_mem concreteRingOfIntegers A
  exact add_mem hA hm

/-- By contrast, the naive order `ℤ[√5]` is NOT the full ring of integers: it has index `2`
in `ℤ[φ]`, since `φ = (1 + √5)/2 ∉ ℤ[√5]`. -/
theorem adjoin_sqrtFive_ne_integralClosure :
    Algebra.adjoin ℤ ({sqrtFive} : Set K) ≠ integralClosure ℤ K := by
  intro h
  let S : Subalgebra ℤ K :=
    { carrier := {z : K | ∃ a b : ℤ,
        z = algebraMap ℚ K (a : ℚ) + algebraMap ℚ K (b : ℚ) * sqrtFive}
      add_mem' := by
        rintro z w ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
        refine ⟨a + c, b + d, ?_⟩
        rw [show ((a + c : ℤ) : ℚ) = (a : ℚ) + (c : ℚ) by push_cast; ring,
          show ((b + d : ℤ) : ℚ) = (b : ℚ) + (d : ℚ) by push_cast; ring, map_add, map_add]
        ring
      mul_mem' := by
        rintro z w ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
        refine ⟨a * c + 5 * b * d, a * d + b * c, ?_⟩
        rw [show ((a * c + 5 * b * d : ℤ) : ℚ) =
            (a : ℚ) * (c : ℚ) + 5 * ((b : ℚ) * (d : ℚ)) by push_cast; ring,
          show ((a * d + b * c : ℤ) : ℚ) =
            (a : ℚ) * (d : ℚ) + (b : ℚ) * (c : ℚ) by push_cast; ring,
          map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_mul, map_ofNat]
        linear_combination (algebraMap ℚ K (b : ℚ) * algebraMap ℚ K (d : ℚ)) * sqrtFive_sq
      one_mem' := ⟨1, 0, by simp⟩
      zero_mem' := ⟨0, 0, by simp⟩
      algebraMap_mem' := fun n => ⟨n, 0, by simp⟩ }
  have hsub : Algebra.adjoin ℤ ({sqrtFive} : Set K) ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro z rfl
    exact ⟨0, 1, by push_cast; simp⟩
  have hφ : goldenInteger ∈ Algebra.adjoin ℤ ({sqrtFive} : Set K) := by
    rw [h]
    exact goldenInteger_integral
  obtain ⟨a, b, hab⟩ := hsub hφ
  have hzero : algebraMap ℚ K ((1 : ℚ) / 2 - (a : ℚ)) +
      algebraMap ℚ K ((1 : ℚ) / 2 - (b : ℚ)) * sqrtFive = 0 := by
    rw [map_sub, map_sub]
    have hgold : goldenInteger = algebraMap ℚ K ((1 : ℚ) / 2) +
        algebraMap ℚ K ((1 : ℚ) / 2) * sqrtFive := by
      rw [show goldenInteger = (1 + sqrtFive) / 2 from rfl, map_div₀, map_one, map_ofNat]
      ring
    linear_combination hab - hgold
  obtain ⟨h1, h2⟩ := coords_eq_zero hzero
  have h2a : (2 * a : ℤ) = 1 := by
    have hq : ((2 * a : ℤ) : ℚ) = 1 := by
      push_cast
      linarith [h1]
    exact_mod_cast hq
  omega

/-! ## 3. Discriminant -/

instance : Algebra.IsQuadraticExtension ℚ K where
  finrank_eq_two' := degree_eq_two

theorem aut_eq_or' (σ : K ≃ₐ[ℚ] K) : σ = AlgEquiv.refl ∨ σ = conj' := by
  have hsq : (σ sqrtFive) ^ 2 = (5 : K) := by
    rw [← map_pow, sqrtFive_sq, map_ofNat]
  have hfactor : (σ sqrtFive - sqrtFive) * (σ sqrtFive + sqrtFive) = 0 := by
    linear_combination hsq - sqrtFive_sq
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    have hσ : (σ : K →ₐ[ℚ] K) = AlgHom.id ℚ K := by
      apply AdjoinRoot.algHom_ext
      change σ sqrtFive = sqrtFive
      exact sub_eq_zero.mp h
    ext x
    change (σ : K →ₐ[ℚ] K) x = x
    rw [hσ]
    rfl
  · right
    have hσ : (σ : K →ₐ[ℚ] K) = conj'.toAlgHom := by
      apply AdjoinRoot.algHom_ext
      change σ sqrtFive = conj' sqrtFive
      rw [conj'_root]
      exact eq_neg_of_add_eq_zero_left h
    ext x
    change (σ : K →ₐ[ℚ] K) x = conj'.toAlgHom x
    rw [hσ]

theorem conj'_ne_refl : conj' ≠ (AlgEquiv.refl : K ≃ₐ[ℚ] K) := by
  intro h
  have hroot : -sqrtFive = sqrtFive := by
    calc -sqrtFive = conj' sqrtFive := conj'_root.symm
      _ = sqrtFive := by rw [h]; rfl
  have h2 : (2 : K) * sqrtFive = 0 := by linear_combination -hroot
  rcases mul_eq_zero.mp h2 with h2' | hs0
  · norm_num at h2'
  · have h5 : (5 : K) = 0 := by rw [← sqrtFive_sq, hs0]; ring
    norm_num at h5

theorem prod_auts (z : K) : ∏ σ : K ≃ₐ[ℚ] K, σ z = z * conj' z := by
  classical
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) =
      insert AlgEquiv.refl {conj'} := by
    symm
    rw [Finset.eq_univ_iff_forall]
    intro σ
    rcases aut_eq_or' σ with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [huniv, Finset.prod_insert (Finset.notMem_singleton.mpr (Ne.symm conj'_ne_refl)),
    Finset.prod_singleton]
  rfl

/-- The `K`-level norm form, computed as the product over the two automorphisms. -/
theorem norm_eq_normForm' (x y : ℚ) :
    Algebra.norm ℚ (x • (1 : K) + y • goldenInteger) = x ^ 2 + x * y - y ^ 2 := by
  apply FaithfulSMul.algebraMap_injective ℚ K
  rw [Algebra.norm_eq_prod_automorphisms, prod_auts]
  have hconj : conj' (x • (1 : K) + y • goldenInteger) =
      x • (1 : K) + y • (1 - goldenInteger) := by
    simp only [Algebra.smul_def, mul_one]
    rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, conj'_golden]
  rw [hconj]
  simp only [Algebra.smul_def, mul_one]
  rw [map_sub, map_add, map_mul, map_pow, map_pow]
  linear_combination (-(algebraMap ℚ K y) ^ 2) * goldenInteger_sq

theorem li_one_golden_K : LinearIndependent ℚ ![(1 : K), goldenInteger] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_two] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  have hform : g 0 • (1 : K) + g 1 • goldenInteger =
      algebraMap ℚ K (g 0 + g 1 / 2) + algebraMap ℚ K (g 1 / 2) * sqrtFive := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one,
      show goldenInteger = (1 + sqrtFive) / 2 from rfl, map_add, map_div₀, map_ofNat]
    field_simp
    ring
  rw [hform] at hg
  obtain ⟨h1, h2⟩ := coords_eq_zero hg
  have hg1 : g 1 = 0 := by linarith
  have hg0 : g 0 = 0 := by linarith
  intro i
  fin_cases i
  · exact hg0
  · exact hg1

theorem span_one_golden_K :
    ⊤ ≤ Submodule.span ℚ (Set.range ![(1 : K), goldenInteger]) := by
  intro z _
  obtain ⟨a, b, rfl⟩ := exists_coords z
  have hz : algebraMap ℚ K a + algebraMap ℚ K b * sqrtFive =
      (a - b) • (1 : K) + (2 * b) • goldenInteger := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_sub, map_mul, map_ofNat,
      show goldenInteger = (1 + sqrtFive) / 2 from rfl]
    field_simp
    ring
  rw [hz]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

noncomputable def goldenBasisK : Basis (Fin 2) ℚ K :=
  Basis.mk li_one_golden_K span_one_golden_K

/-- The golden ratio gives a `ℚ`-power basis `1, φ` of `K`. -/
noncomputable abbrev goldenPowerBasis : PowerBasis ℚ K where
  gen := goldenInteger
  dim := 2
  basis := goldenBasisK
  basis_eq_pow := by
    intro i
    fin_cases i
    · simp [goldenBasisK, Basis.mk_apply]
    · simp [goldenBasisK, Basis.mk_apply]

theorem goldenPowerBasis_basis_zero :
    goldenPowerBasis.basis 0 = (1 : K) := by
  rw [goldenPowerBasis.basis_eq_pow]
  simp

theorem goldenPowerBasis_basis_one :
    goldenPowerBasis.basis 1 = goldenRoot := by
  rw [goldenPowerBasis.basis_eq_pow]
  simp [goldenPowerBasis, goldenRoot]

@[simp]
theorem goldenPowerBasis_equivFun_one_zero :
    goldenPowerBasis.basis.equivFun (1 : K) 0 = 1 := by
  rw [← goldenPowerBasis_basis_zero]
  simp

@[simp]
theorem goldenPowerBasis_equivFun_one_one :
    goldenPowerBasis.basis.equivFun (1 : K) 1 = 0 := by
  rw [← goldenPowerBasis_basis_zero]
  simp

@[simp]
theorem goldenPowerBasis_equivFun_goldenRoot_zero :
    goldenPowerBasis.basis.equivFun goldenRoot 0 = 0 := by
  rw [← goldenPowerBasis_basis_one]
  simp

@[simp]
theorem goldenPowerBasis_equivFun_goldenRoot_one :
    goldenPowerBasis.basis.equivFun goldenRoot 1 = 1 := by
  rw [← goldenPowerBasis_basis_one]
  simp

@[simp]
theorem goldenPowerBasis_equivFun_rat_zero (q : ℚ) :
    goldenPowerBasis.basis.equivFun (algebraMap ℚ K q) 0 = q := by
  rw [Algebra.algebraMap_eq_smul_one]
  rw [← goldenPowerBasis_basis_zero]
  simp

@[simp]
theorem goldenPowerBasis_equivFun_rat_one (q : ℚ) :
    goldenPowerBasis.basis.equivFun (algebraMap ℚ K q) 1 = 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  rw [← goldenPowerBasis_basis_zero]
  simp

@[simp]
theorem goldenPowerBasis_equivFun_linear_zero (a b : ℚ) :
    goldenPowerBasis.basis.equivFun (a • (1 : K) + b • goldenRoot) 0 = a := by
  rw [← goldenPowerBasis_basis_zero, ← goldenPowerBasis_basis_one]
  simp

@[simp]
theorem goldenPowerBasis_equivFun_linear_one (a b : ℚ) :
    goldenPowerBasis.basis.equivFun (a • (1 : K) + b • goldenRoot) 1 = b := by
  rw [← goldenPowerBasis_basis_zero, ← goldenPowerBasis_basis_one]
  simp

theorem goldenOrderToField_integralBasis (i : Fin 2) :
    goldenOrderToField (sqrtFiveExplicitIntegralBasis i) = goldenPowerBasis.basis i := by
  fin_cases i
  · change goldenOrderToField (sqrtFiveExplicitIntegralBasis (0 : Fin 2)) =
      goldenPowerBasis.basis (0 : Fin 2)
    rw [goldenOrderToField_basis_zero, goldenPowerBasis_basis_zero]
  · change goldenOrderToField (sqrtFiveExplicitIntegralBasis (1 : Fin 2)) =
      goldenPowerBasis.basis (1 : Fin 2)
    rw [goldenOrderToField_basis_one, goldenPowerBasis_basis_one]

theorem goldenOrderToField_coord (z : O5) (i : Fin 2) :
    goldenPowerBasis.basis.equivFun (goldenOrderToField z) i =
      (sqrtFiveExplicitIntegralBasis.equivFun z i : ℚ) := by
  rw [← sqrtFiveExplicitIntegralBasis.sum_equivFun z]
  simp_rw [map_sum, map_zsmul]
  simp_rw [goldenOrderToField_integralBasis]
  rw [Basis.equivFun_apply]
  classical
  fin_cases i <;> simp

theorem goldenOrderToField_injective : Function.Injective goldenOrderToField := by
  intro x y hxy
  apply sqrtFiveExplicitIntegralBasis.equivFun.injective
  ext i
  have hcoord := congr_arg (fun z => goldenPowerBasis.basis.equivFun z i) hxy
  change goldenPowerBasis.basis.equivFun (goldenOrderToField x) i =
    goldenPowerBasis.basis.equivFun (goldenOrderToField y) i at hcoord
  rw [goldenOrderToField_coord x i, goldenOrderToField_coord y i] at hcoord
  exact_mod_cast hcoord

/-- The minimal polynomial of the golden ratio is `X² - X - 1`. -/
theorem goldenInteger_minpoly :
    minpoly ℚ goldenInteger = Polynomial.X ^ 2 - Polynomial.X - 1 := by
  have hint : IsIntegral ℚ goldenInteger := IsIntegral.of_finite ℚ _
  have hmonic : (Polynomial.X ^ 2 - Polynomial.X - 1 : Polynomial ℚ).Monic := by monicity!
  have hdeg2 : (Polynomial.X ^ 2 - Polynomial.X - 1 : Polynomial ℚ).natDegree = 2 := by
    compute_degree!
  have haev :
      Polynomial.aeval goldenInteger (Polynomial.X ^ 2 - Polynomial.X - 1 : Polynomial ℚ) = 0 := by
    rw [map_sub, map_sub, map_pow, Polynomial.aeval_X, map_one]
    linear_combination goldenInteger_sq
  obtain ⟨c, hc⟩ := minpoly.dvd ℚ goldenInteger haev
  have hmin_monic : (minpoly ℚ goldenInteger).Monic := minpoly.monic hint
  have hmindeg : (minpoly ℚ goldenInteger).natDegree = 2 :=
    goldenPowerBasis.natDegree_minpoly
  have hcne : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact hmonic.ne_zero hc
  have hcdeg : c.natDegree = 0 := by
    have hfdeg := congrArg Polynomial.natDegree hc
    rw [Polynomial.natDegree_mul (minpoly.ne_zero hint) hcne, hdeg2, hmindeg] at hfdeg
    omega
  have hlead := congrArg Polynomial.leadingCoeff hc
  rw [Polynomial.leadingCoeff_mul, hmin_monic.leadingCoeff, one_mul,
    hmonic.leadingCoeff] at hlead
  have hc1 : c = 1 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hcdeg,
      show c.coeff 0 = c.leadingCoeff by rw [Polynomial.leadingCoeff, hcdeg], ← hlead]
    simp
  rw [hc1, mul_one] at hc
  exact hc.symm

/-- The `K`-level discriminant of the power basis `1, φ` is `5`. -/
theorem goldenPowerBasis_discr :
    Algebra.discr ℚ goldenPowerBasis.basis = (5 : ℚ) := by
  rw [Algebra.discr_powerBasis_eq_norm]
  have hgen : goldenPowerBasis.gen = goldenInteger := rfl
  rw [hgen, degree_eq_two, goldenInteger_minpoly]
  have hder : Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X - 1 : Polynomial ℚ) =
      2 * Polynomial.X - 1 := by
    simp
    ring
  rw [hder]
  have haev :
      Polynomial.aeval goldenInteger (2 * Polynomial.X - 1 : Polynomial ℚ) = sqrtFive := by
    rw [map_sub, map_mul, Polynomial.aeval_X, map_one, map_ofNat,
      show goldenInteger = (1 + sqrtFive) / 2 from rfl]
    ring
  rw [haev]
  have hnorm : Algebra.norm ℚ sqrtFive = (-5 : ℚ) := by
    have h := norm_eq_normForm' (-1) 2
    rw [show ((-1 : ℚ)) • (1 : K) + (2 : ℚ) • goldenInteger = sqrtFive from by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_neg, map_one, map_ofNat,
        show goldenInteger = (1 + sqrtFive) / 2 from rfl]
      ring] at h
    rw [h]
    norm_num
  rw [hnorm]
  norm_num

set_option linter.flexible false in
/-- The `ℤ`-discriminant of the integral basis `1, φ` is `5`. -/
theorem concreteIntegralBasis_discr :
    Algebra.discr ℤ concreteIntegralBasis = (5 : ℤ) := by
  let bInt : Basis (Fin 2) ℤ (𝓞 K) := concreteIntegralBasis
  haveI : IsScalarTower ℤ (𝓞 K) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hdiscLoc :=
    @Algebra.discr_localizationLocalization
      ℤ (𝓞 K) _ _ _ ℚ _ _ ℤ⁰ _ K _ _ _ _
      (by infer_instance : IsScalarTower ℤ ℚ K)
      (by infer_instance : IsScalarTower ℤ (𝓞 K) K)
      (by infer_instance : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) K)
      (Fin 2) (by infer_instance) (by infer_instance) bInt
  let bLoc : Basis (Fin 2) ℚ K :=
    @Module.Basis.localizationLocalization
      ℤ ℚ _ ℤ⁰ _ _ _ (𝓞 K) _ _ K _ _ _ _
      (by infer_instance : IsScalarTower ℤ ℚ K)
      (by infer_instance : IsScalarTower ℤ (𝓞 K) K)
      (by infer_instance : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) K)
      (Fin 2) bInt
  apply (algebraMap ℤ ℚ).injective_int
  change (algebraMap ℤ ℚ) (Algebra.discr ℤ bInt) = (algebraMap ℤ ℚ) 5
  rw [← hdiscLoc]
  change Algebra.discr ℚ bLoc = (5 : ℚ)
  have hfun : ⇑bLoc = ⇑goldenPowerBasis.basis := by
    funext i
    fin_cases i
    · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = (0 : Fin 2) from rfl]
      simp only [bLoc, bInt, Module.Basis.localizationLocalization_apply]
      rw [concreteIntegralBasis_apply 0]
      simp only [integralBasisVectors, goldenBasisK, Matrix.cons_val_zero]
      exact (Module.Basis.mk_apply li_one_golden_K span_one_golden_K 0).symm
    · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = (1 : Fin 2) from rfl]
      simp only [bLoc, bInt, Module.Basis.localizationLocalization_apply]
      rw [concreteIntegralBasis_apply 1]
      simp only [integralBasisVectors, goldenBasisK, Matrix.cons_val_one]
      exact (Module.Basis.mk_apply li_one_golden_K span_one_golden_K 1).symm
  rw [hfun]
  exact goldenPowerBasis_discr

/-- The number-field discriminant of `ℚ(√5)` is `5` (for `d ≡ 1 (mod 4)` squarefree the
discriminant of `ℚ(√d)` is `d` itself). This is the smallest discriminant of any real
quadratic field; in particular `5` is the only ramified prime, cf. `ramified_iff_eq_five`. -/
theorem numberField_discr_eq : NumberField.discr K = (5 : ℤ) := by
  rw [← NumberField.discr_eq_discr K concreteIntegralBasis]
  exact concreteIntegralBasis_discr


end XYin.NumberField.SqrtFiveGoldenAdjoinRoot
