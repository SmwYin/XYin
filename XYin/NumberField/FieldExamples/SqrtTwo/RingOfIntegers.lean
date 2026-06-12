import XYin.NumberField.FieldExamples.SqrtTwo.Basic

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

/-! ## 2. Integral basis and ring of integers -/

/-- The ring of integers of `ℚ(√2)`. -/
abbrev O2 : Type := 𝓞 QSqrtTwo

example : CommRing O2 := by infer_instance

example : IsDomain O2 := by infer_instance

example : Algebra O2 QSqrtTwo := by infer_instance

theorem sqrtTwoRoot_isIntegral : IsIntegral ℤ sqrtTwoRoot := by
  refine ⟨X ^ 2 - C (2 : ℤ), ?_, ?_⟩
  · exact monic_X_pow_sub_C (2 : ℤ) (by norm_num : (2 : ℕ) ≠ 0)
  · simp [sqrtTwoRoot_sq]

/-- The algebraic integer `√2`. -/
abbrev sqrtTwoInteger : O2 :=
  ⟨sqrtTwoRoot, sqrtTwoRoot_isIntegral⟩

local notation "𝓟₂" => Submodule.span ℤ ({(2 : ℤ)} : Set ℤ)

/-- The same polynomial, now over `ℤ`. -/
abbrev sqrtTwoIntegerPolynomial : ℤ[X] := X ^ 2 - C (2 : ℤ)

/-- The rational minimal polynomial of the chosen root `√2`. -/
theorem sqrtTwo_minpoly_rat : minpoly ℚ sqrtTwoRoot = sqrtTwoPolynomial := by
  rw [← sqrtTwoAdjoinRootToQuadratic_root]
  change minpoly ℚ (sqrtTwoAdjoinRootEquivQuadratic sqrtTwoAdjoinRoot) =
    sqrtTwoPolynomial
  rw [minpoly.algEquiv_eq sqrtTwoAdjoinRootEquivQuadratic sqrtTwoAdjoinRoot]
  simpa [sqrtTwoPolynomial] using
    (AdjoinRoot.minpoly_root ((Fact.out : Irreducible sqrtTwoPolynomial).ne_zero) :
      minpoly ℚ (AdjoinRoot.root sqrtTwoPolynomial) =
        sqrtTwoPolynomial * C sqrtTwoPolynomial.leadingCoeff⁻¹)

theorem sqrtTwoPolynomial_eq_minpoly : sqrtTwoPolynomial = minpoly ℚ sqrtTwoRoot := by
  rw [sqrtTwo_minpoly_rat]

/-- The integral minimal polynomial of `√2`, viewed as an element of the field. -/
theorem sqrtTwo_minpoly_int : minpoly ℤ sqrtTwoRoot = sqrtTwoIntegerPolynomial := by
  apply (Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) sqrtTwoRoot_isIntegral,
    sqrtTwo_minpoly_rat]
  change X ^ 2 - C (2 : ℚ) =
    map (algebraMap ℤ ℚ) (X ^ 2 - C (2 : ℤ))
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rw [show (algebraMap ℤ ℚ) (2 : ℤ) = (2 : ℚ) by norm_num]

/-- The polynomial `X^2 - 2` is Eisenstein at `2`. -/
theorem sqrtTwo_minpoly_int_isEisenstein :
    (minpoly ℤ sqrtTwoRoot).IsEisensteinAt 𝓟₂ := by
  rw [sqrtTwo_minpoly_int]
  refine
    (monic_X_pow_sub_C (2 : ℤ)
      (by norm_num : (2 : ℕ) ≠ 0)).isEisensteinAt_of_mem_of_notMem ?_ ?_ ?_
  · rw [ne_eq, Ideal.eq_top_iff_one]
    simp [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
  · intro n hn
    rw [natDegree_X_pow_sub_C] at hn
    interval_cases n <;>
      simp [Ideal.submodule_span_eq]
  · simp [Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-! ## 3. Discriminant -/

/-- The discriminant of the order `ℤ[√2]` with basis `1, √2` is `8`. -/
theorem sqrtTwoPowerBasis_discr :
    Algebra.discr ℚ sqrtTwoPowerBasis.basis = (8 : ℚ) := by
  rw [Algebra.discr_powerBasis_eq_norm]
  have hdim : sqrtTwoPowerBasis.dim = 2 := by
    change sqrtTwoPolynomial.natDegree = 2
    rw [sqrtTwoPolynomial, natDegree_X_pow_sub_C]
  have hfin : Module.finrank ℚ QSqrtTwo = 2 := by
    rw [PowerBasis.finrank sqrtTwoPowerBasis]
    exact hdim
  have hgen : sqrtTwoPowerBasis.gen = sqrtTwoRoot := by
    exact sqrtTwoPowerBasis_gen
  have hnorm_two : Algebra.norm ℚ (1 + 1 : QSqrtTwo) = (4 : ℚ) := by
    rw [show (1 + 1 : QSqrtTwo) = algebraMap ℚ QSqrtTwo (2 : ℚ) by norm_num]
    rw [Algebra.norm_algebraMap, hfin]
    norm_num
  have hnorm_root : Algebra.norm ℚ sqrtTwoRoot = (-2 : ℚ) := by
    rw [← hgen, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly sqrtTwoPowerBasis]
    rw [hdim, hgen, sqrtTwo_minpoly_rat]
    simp [sqrtTwoPolynomial]
  rw [hfin, hgen, sqrtTwo_minpoly_rat]
  simp [sqrtTwoRoot, sqrtTwoPolynomial, hnorm_two, hnorm_root]
  norm_num

/--
Every algebraic integer in `ℚ(√2)` lies in `ℤ[√2]`.

The proof uses the discriminant bound `8 • z ∈ ℤ[√2]`, then removes the factor
`2^3` with the Eisenstein theorem for `X^2 - 2`.
-/
theorem sqrtTwo_integral_mem_adjoin (z : QSqrtTwo) (hz : IsIntegral ℤ z) :
    z ∈ Algebra.adjoin ℤ ({sqrtTwoRoot} : Set QSqrtTwo) := by
  have hBint : IsIntegral ℤ sqrtTwoPowerBasis.gen := by
    rw [sqrtTwoPowerBasis_gen]
    exact sqrtTwoRoot_isIntegral
  have hdiscr :=
    Algebra.discr_mul_isIntegral_mem_adjoin (K := ℚ) (L := QSqrtTwo)
      (R := ℤ) (B := sqrtTwoPowerBasis) hBint hz
  have hpow :
      (2 : ℤ) ^ 3 • z ∈ Algebra.adjoin ℤ ({sqrtTwoPowerBasis.gen} : Set QSqrtTwo) := by
    convert hdiscr using 1
    rw [sqrtTwoPowerBasis_discr]
    norm_num [Algebra.smul_def]
  have hmem :
      z ∈ Algebra.adjoin ℤ ({sqrtTwoPowerBasis.gen} : Set QSqrtTwo) :=
    mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
      (R := ℤ) (K := ℚ) (L := QSqrtTwo) (B := sqrtTwoPowerBasis)
      (p := (2 : ℤ)) (n := 3) Int.prime_two hBint hz hpow
      (by rw [sqrtTwoPowerBasis_gen]; exact sqrtTwo_minpoly_int_isEisenstein)
  rwa [sqrtTwoPowerBasis_gen] at hmem

/--
`ℤ[√2]` is integrally closed in `ℚ(√2)` in the same sense as the cyclotomic
singleton-adjoin theorem on the `ζ₃` side.
-/
example :
    IsIntegralClosure
      (Algebra.adjoin ℤ ({sqrtTwoRoot} : Set QSqrtTwo)) ℤ QSqrtTwo := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext hxy
  · intro x
    constructor
    · intro hx
      exact ⟨⟨x, sqrtTwo_integral_mem_adjoin x hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      letI : Algebra.IsIntegral ℤ (Algebra.adjoin ℤ ({sqrtTwoRoot} : Set QSqrtTwo)) :=
        Algebra.IsIntegral.adjoin
          (by
            intro x hx
            simp only [Set.mem_singleton_iff] at hx
            rw [hx]
            exact sqrtTwoRoot_isIntegral)
      exact IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral y)

/-- The ring of integers of `ℚ(√2)` is generated over `ℤ` by `√2`. -/
theorem sqrtTwoInteger_adjoin_eq_top :
    Algebra.adjoin ℤ ({sqrtTwoInteger} : Set O2) = ⊤ := by
  apply le_antisymm le_top
  intro x hx
  have hfield :
      (x : QSqrtTwo) ∈ Algebra.adjoin ℤ ({sqrtTwoRoot} : Set QSqrtTwo) :=
    sqrtTwo_integral_mem_adjoin (x : QSqrtTwo) x.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hfield
  rcases hfield with ⟨P, hP⟩
  have hx_eq : x = aeval sqrtTwoInteger P := by
    apply Subtype.ext
    change (x : QSqrtTwo) = ((aeval sqrtTwoInteger P : O2) : QSqrtTwo)
    rw [← hP]
    simpa [sqrtTwoInteger] using
      (Polynomial.aeval_algHom_apply
        (algebraMap O2 QSqrtTwo).toIntAlgHom sqrtTwoInteger P)
  rw [hx_eq]
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨P, rfl⟩

/-- The integral minimal polynomial of `√2` as an element of `𝓞 ℚ(√2)`. -/
theorem sqrtTwoInteger_minpoly :
    minpoly ℤ sqrtTwoInteger = sqrtTwoIntegerPolynomial := by
  letI : IsScalarTower ℤ O2 QSqrtTwo :=
    IsScalarTower.of_algebraMap_eq fun z => by
      rfl
  have hint : IsIntegral ℤ sqrtTwoInteger := Algebra.IsIntegral.isIntegral sqrtTwoInteger
  have hfrac :
      minpoly ℚ ((algebraMap O2 QSqrtTwo) sqrtTwoInteger) =
        map (algebraMap ℤ ℚ) (minpoly ℤ sqrtTwoInteger) :=
    @minpoly.isIntegrallyClosed_eq_field_fractions ℤ O2
      inferInstance inferInstance inferInstance inferInstance
      ℚ QSqrtTwo inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance this inferInstance inferInstance
      sqrtTwoInteger hint
  apply (Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective)
  rw [← hfrac]
  change minpoly ℚ sqrtTwoRoot = map (algebraMap ℤ ℚ) sqrtTwoIntegerPolynomial
  rw [sqrtTwo_minpoly_rat]
  change X ^ 2 - C (2 : ℚ) =
    map (algebraMap ℤ ℚ) (X ^ 2 - C (2 : ℤ))
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rw [show (algebraMap ℤ ℚ) (2 : ℤ) = (2 : ℚ) by norm_num]

/--
An explicit integral power basis of `𝓞 ℚ(√2)`: the generator is the algebraic
integer `√2`.
-/
abbrev sqrtTwoExplicitIntegralPowerBasis : PowerBasis ℤ O2 :=
  PowerBasis.ofAdjoinEqTop'
    (Algebra.IsIntegral.isIntegral sqrtTwoInteger)
    sqrtTwoInteger_adjoin_eq_top

theorem sqrtTwoExplicitIntegralPowerBasis_gen :
    sqrtTwoExplicitIntegralPowerBasis.gen = sqrtTwoInteger := by
  exact PowerBasis.ofAdjoinEqTop'_gen
    (Algebra.IsIntegral.isIntegral sqrtTwoInteger)
    sqrtTwoInteger_adjoin_eq_top

theorem sqrtTwoExplicitIntegralPowerBasis_dim :
    sqrtTwoExplicitIntegralPowerBasis.dim = 2 := by
  rw [sqrtTwoExplicitIntegralPowerBasis, PowerBasis.ofAdjoinEqTop'_dim,
    sqrtTwoInteger_minpoly]
  change sqrtTwoIntegerPolynomial.natDegree = 2
  rw [sqrtTwoIntegerPolynomial, natDegree_X_pow_sub_C]

/-- The explicit integral basis `[1, √2]` of the ring of integers. -/
abbrev sqrtTwoExplicitIntegralBasis : Basis (Fin 2) ℤ O2 :=
  sqrtTwoExplicitIntegralPowerBasis.basis.reindex
    (finCongr sqrtTwoExplicitIntegralPowerBasis_dim)

/-- The first vector in the explicit integral basis is `1`. -/
theorem sqrtTwoExplicitIntegralBasis_zero :
    sqrtTwoExplicitIntegralBasis 0 = 1 := by
  rw [sqrtTwoExplicitIntegralBasis, Basis.reindex_apply]
  rw [sqrtTwoExplicitIntegralPowerBasis.basis_eq_pow]
  have hcoe :
      (((finCongr sqrtTwoExplicitIntegralPowerBasis_dim).symm (0 : Fin 2) :
        Fin sqrtTwoExplicitIntegralPowerBasis.dim) : ℕ) = 0 := rfl
  rw [hcoe]
  simp

example : sqrtTwoExplicitIntegralBasis 0 = 1 :=
  sqrtTwoExplicitIntegralBasis_zero

/-- The second vector in the explicit integral basis is `√2`. -/
theorem sqrtTwoExplicitIntegralBasis_one :
    sqrtTwoExplicitIntegralBasis 1 = sqrtTwoInteger := by
  rw [sqrtTwoExplicitIntegralBasis, Basis.reindex_apply]
  rw [sqrtTwoExplicitIntegralPowerBasis.basis_eq_pow]
  have hcoe :
      (((finCongr sqrtTwoExplicitIntegralPowerBasis_dim).symm (1 : Fin 2) :
        Fin sqrtTwoExplicitIntegralPowerBasis.dim) : ℕ) = 1 := rfl
  rw [hcoe]
  simp

example : sqrtTwoExplicitIntegralBasis 1 = sqrtTwoInteger :=
  sqrtTwoExplicitIntegralBasis_one

theorem sqrtTwoInteger_sq : sqrtTwoInteger ^ 2 = (2 : O2) := by
  apply Subtype.ext
  change sqrtTwoRoot ^ 2 = (2 : QSqrtTwo)
  exact sqrtTwoRoot_sq

set_option linter.flexible false in
/-- The discriminant of the explicit integral basis `[1, √2]` is `8`. -/
theorem sqrtTwoExplicitIntegralBasis_discr :
    Algebra.discr ℤ sqrtTwoExplicitIntegralBasis = (8 : ℤ) := by
  let bInt : Basis (Fin 2) ℤ (𝓞 QSqrtTwo) := sqrtTwoExplicitIntegralBasis
  haveI : IsScalarTower ℤ (𝓞 QSqrtTwo) QSqrtTwo := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hdiscLoc :=
    @Algebra.discr_localizationLocalization
      ℤ (𝓞 QSqrtTwo) _ _ _ ℚ _ _ ℤ⁰ _ QSqrtTwo _ _ _ _
      (by infer_instance : IsScalarTower ℤ ℚ QSqrtTwo)
      (by infer_instance : IsScalarTower ℤ (𝓞 QSqrtTwo) QSqrtTwo)
      (by
        infer_instance :
          IsLocalization (Algebra.algebraMapSubmonoid (𝓞 QSqrtTwo) ℤ⁰) QSqrtTwo)
      (Fin 2) (by infer_instance) (by infer_instance) bInt
  let bLoc : Basis (Fin 2) ℚ QSqrtTwo :=
    @Module.Basis.localizationLocalization
      ℤ ℚ _ ℤ⁰ _ _ _ (𝓞 QSqrtTwo) _ _ QSqrtTwo _ _ _ _
      (by infer_instance : IsScalarTower ℤ ℚ QSqrtTwo)
      (by infer_instance : IsScalarTower ℤ (𝓞 QSqrtTwo) QSqrtTwo)
      (by
        infer_instance :
          IsLocalization (Algebra.algebraMapSubmonoid (𝓞 QSqrtTwo) ℤ⁰) QSqrtTwo)
      (Fin 2) bInt
  apply (algebraMap ℤ ℚ).injective_int
  change (algebraMap ℤ ℚ) (Algebra.discr ℤ bInt) = (algebraMap ℤ ℚ) 8
  rw [← hdiscLoc]
  change Algebra.discr ℚ bLoc = (8 : ℚ)
  have hBasis : bLoc = sqrtTwoPowerBasis.basis.reindex (finCongr sqrtTwoPowerBasis_dim) := by
    apply DFunLike.ext
    intro i
    fin_cases i
    · simp [bLoc, bInt, Basis.localizationLocalization_apply, sqrtTwoExplicitIntegralBasis_zero]
      change (1 : QSqrtTwo) =
        sqrtTwoPowerBasis.basis ((finCongr sqrtTwoPowerBasis_dim).symm (0 : Fin 2))
      rw [sqrtTwoPowerBasis.basis_eq_pow]
      have hcoe :
          (((finCongr sqrtTwoPowerBasis_dim).symm (0 : Fin 2) :
            Fin sqrtTwoPowerBasis.dim) : ℕ) = 0 := rfl
      rw [hcoe]
      simp
    · simp [bLoc, bInt, Basis.localizationLocalization_apply, sqrtTwoExplicitIntegralBasis_one]
      change sqrtTwoRoot =
        sqrtTwoPowerBasis.basis ((finCongr sqrtTwoPowerBasis_dim).symm (1 : Fin 2))
      rw [sqrtTwoPowerBasis.basis_eq_pow]
      have hcoe :
          (((finCongr sqrtTwoPowerBasis_dim).symm (1 : Fin 2) :
            Fin sqrtTwoPowerBasis.dim) : ℕ) = 1 := rfl
      rw [hcoe]
      rw [pow_one, sqrtTwoPowerBasis_gen]
  rw [hBasis]
  simpa [Basis.coe_reindex] using
    (Algebra.discr_reindex ℚ sqrtTwoPowerBasis.basis (finCongr sqrtTwoPowerBasis_dim)).trans
      sqrtTwoPowerBasis_discr

theorem sqrtTwo_numberField_discr :
    NumberField.discr QSqrtTwo = 8 := by
  rw [← NumberField.discr_eq_discr QSqrtTwo sqrtTwoExplicitIntegralBasis]
  exact sqrtTwoExplicitIntegralBasis_discr

attribute [local instance] DivisionRing.toRatAlgebra in
example : Algebra.discr ℚ (NumberField.integralBasis QSqrtTwo) = (8 : ℚ) := by
  have h := NumberField.coe_discr QSqrtTwo
  rw [sqrtTwo_numberField_discr] at h
  simpa using h.symm

theorem discr_matrix_mulVec_sqrtTwo
    (P : Matrix (Fin sqrtTwoPowerBasis.dim) (Fin sqrtTwoPowerBasis.dim) ℚ) :
    Algebra.discr ℚ (Matrix.mulVec (P.map (algebraMap ℚ QSqrtTwo)) sqrtTwoPowerBasis.basis) =
      P.det ^ 2 * Algebra.discr ℚ sqrtTwoPowerBasis.basis :=
  Algebra.discr_of_matrix_mulVec _ _

example (P : Matrix (Fin sqrtTwoPowerBasis.dim) (Fin sqrtTwoPowerBasis.dim) ℚ)
    (hdet : P.det = 1 ∨ P.det = -1) :
    Algebra.discr ℚ (Matrix.mulVec (P.map (algebraMap ℚ QSqrtTwo)) sqrtTwoPowerBasis.basis) =
      (8 : ℚ) := by
  rw [discr_matrix_mulVec_sqrtTwo, sqrtTwoPowerBasis_discr]
  rcases hdet with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/--
Ramification-flavoured analogue of `(ζ - 1) ∣ 3` on the cyclotomic side:
here the element `√2` divides `2` in `𝓞 ℚ(√2)`.
-/
example : sqrtTwoInteger ∣ (2 : O2) := by
  use sqrtTwoInteger
  simpa [pow_two] using sqrtTwoInteger_sq.symm


end NumberField.SqrtTwo
