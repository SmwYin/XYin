import XYin.NumberField.FieldExamples.SqrtNegSixAdjoinRoot.Basic

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace XYin.NumberField.New.SqrtNegSixAdjoinRoot

/-! ## 2. Integral basis and ring of integers -/

/-- The generator `θ = √-6` is integral over `ℤ` (a root of the monic `X² + 6`), hence lies
in `𝓞 K`. -/
theorem theta_integral : θ ∈ integralClosure ℤ K := by
  refine ⟨Polynomial.X ^ 2 + 6, ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_ofNat]
    linear_combination theta_sq

/-- `θ = √-6` as an element of the ring of integers `𝓞 K`. -/
noncomputable def thetaInt : 𝓞 K := ⟨θ, theta_integral⟩

/-- The integral generator also satisfies `θ² = -6` in `𝓞 K`. -/
theorem thetaInt_sq : thetaInt ^ 2 = -6 := by
  apply Subtype.ext
  change (θ : K) ^ 2 = (-6 : K)
  exact theta_sq

/-- The conjugation `θ ↦ -θ` as an algebra map, via the universal property. -/
private noncomputable def conjHom : K →ₐ[ℚ] K :=
  AdjoinRoot.liftAlgHom sqrtNegSixPolynomial (Algebra.ofId ℚ K) (-θ) (by
    calc sqrtNegSixPolynomial.eval₂ (Algebra.ofId ℚ K) (-θ)
        = (-θ) ^ 2 + 6 := by simp [sqrtNegSixPolynomial]
      _ = θ ^ 2 + 6 := by ring
      _ = 0 := by rw [theta_sq]; ring)

private theorem conjHom_root : conjHom θ = -θ := by
  change conjHom (AdjoinRoot.root sqrtNegSixPolynomial) = -θ
  rw [conjHom]
  exact AdjoinRoot.liftAlgHom_root sqrtNegSixPolynomial (Algebra.ofId ℚ K) (-θ) _

private theorem conjHom_conjHom : conjHom.comp conjHom = AlgHom.id ℚ K := by
  apply AdjoinRoot.algHom_ext
  change conjHom (conjHom θ) = θ
  rw [conjHom_root, map_neg, conjHom_root, neg_neg]

noncomputable def conj' : K ≃ₐ[ℚ] K :=
  AlgEquiv.ofAlgHom conjHom conjHom conjHom_conjHom conjHom_conjHom

theorem conj'_root : conj' θ = -θ := conjHom_root

theorem aut_eq_or' (σ : K ≃ₐ[ℚ] K) : σ = AlgEquiv.refl ∨ σ = conj' := by
  have hsq : (σ θ) ^ 2 = (-6 : K) := by
    rw [← map_pow, theta_sq]
    rw [show (-6 : K) = algebraMap ℚ K (-6) by norm_num]
    exact σ.commutes (-6)
  have hfactor : (σ θ - θ) * (σ θ + θ) = 0 := by
    have hθ := theta_sq
    linear_combination hsq - hθ
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    have hσ : (σ : K →ₐ[ℚ] K) = AlgHom.id ℚ K := by
      apply AdjoinRoot.algHom_ext
      change σ θ = θ
      exact sub_eq_zero.mp h
    ext x
    change (σ : K →ₐ[ℚ] K) x = x
    rw [hσ]
    rfl
  · right
    have hσ : (σ : K →ₐ[ℚ] K) = conj'.toAlgHom := by
      apply AdjoinRoot.algHom_ext
      change σ θ = conj' θ
      rw [conj'_root]
      exact eq_neg_of_add_eq_zero_left h
    ext x
    change (σ : K →ₐ[ℚ] K) x = conj'.toAlgHom x
    rw [hσ]

private theorem conj'_ne_refl : conj' ≠ (AlgEquiv.refl : K ≃ₐ[ℚ] K) := by
  intro h
  have hroot : -θ = θ := by
    calc -θ = conj' θ := conj'_root.symm
      _ = θ := by rw [h]; rfl
  have h2 : (2 : K) * θ = 0 := by linear_combination -hroot
  rcases mul_eq_zero.mp h2 with h2' | hθ0
  · norm_num at h2'
  · have h6 : (-6 : K) = 0 := by rw [← theta_sq, hθ0]; ring
    norm_num at h6

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

/-- The displayed integral-basis vectors `1, θ` (as elements of `K`). -/
def integralBasisVectors : Fin 2 → K := ![1, θ]

local notation "𝓟₂" => Submodule.span ℤ ({(2 : ℤ)} : Set ℤ)
local notation "𝓟₃" => Submodule.span ℤ ({(3 : ℤ)} : Set ℤ)

private noncomputable def sqrtNegSixArithmeticPowerBasis : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis (f := sqrtNegSixPolynomial)
    ((Fact.out : Irreducible sqrtNegSixPolynomial).ne_zero)

private theorem sqrtNegSixArithmeticPowerBasis_dim :
    sqrtNegSixArithmeticPowerBasis.dim = 2 := by
  change sqrtNegSixPolynomial.natDegree = 2
  rw [sqrtNegSixPolynomial, natDegree_X_pow_add_C]

private abbrev sqrtNegSixIntegerPolynomial : ℤ[X] := Polynomial.X ^ 2 + Polynomial.C (6 : ℤ)

private theorem sqrtNegSix_minpoly_rat : minpoly ℚ θ = sqrtNegSixPolynomial := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · exact (Fact.out : Irreducible sqrtNegSixPolynomial)
  · rw [sqrtNegSixPolynomial]
    simp only [map_add, map_pow, Polynomial.aeval_X, map_ofNat]
    linear_combination theta_sq
  · monicity!

private theorem sqrtNegSix_minpoly_int : minpoly ℤ θ = sqrtNegSixIntegerPolynomial := by
  apply (Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) theta_integral,
    sqrtNegSix_minpoly_rat]
  change Polynomial.X ^ 2 + Polynomial.C (6 : ℚ) =
    Polynomial.map (algebraMap ℤ ℚ) (Polynomial.X ^ 2 + Polynomial.C (6 : ℤ))
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rw [show (algebraMap ℤ ℚ) (6 : ℤ) = (6 : ℚ) by norm_num]

private theorem sqrtNegSix_minpoly_int_isEisensteinAt_two :
    (minpoly ℤ θ).IsEisensteinAt 𝓟₂ := by
  rw [sqrtNegSix_minpoly_int]
  refine
    (Polynomial.monic_X_pow_add_C (6 : ℤ)
      (by norm_num : (2 : ℕ) ≠ 0)).isEisensteinAt_of_mem_of_notMem
      ?_ ?_ ?_
  · rw [ne_eq, Ideal.eq_top_iff_one]
    simp [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
  · intro n hn
    rw [Polynomial.natDegree_X_pow_add_C] at hn
    interval_cases n
    · simpa using (show (6 : ℤ) ∈ 𝓟₂ by
        exact Ideal.mem_span_singleton.mpr ⟨3, by norm_num⟩)
    · simp [Ideal.submodule_span_eq]
  · simp [Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private theorem sqrtNegSix_minpoly_int_isEisensteinAt_three :
    (minpoly ℤ θ).IsEisensteinAt 𝓟₃ := by
  rw [sqrtNegSix_minpoly_int]
  refine
    (Polynomial.monic_X_pow_add_C (6 : ℤ)
      (by norm_num : (2 : ℕ) ≠ 0)).isEisensteinAt_of_mem_of_notMem
      ?_ ?_ ?_
  · rw [ne_eq, Ideal.eq_top_iff_one]
    simp [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
  · intro n hn
    rw [Polynomial.natDegree_X_pow_add_C] at hn
    interval_cases n
    · simpa using (show (6 : ℤ) ∈ 𝓟₃ by
        exact Ideal.mem_span_singleton.mpr ⟨2, by norm_num⟩)
    · simp [Ideal.submodule_span_eq]
  · simp [Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private theorem sqrtNegSixArithmeticPowerBasis_discr :
    Algebra.discr ℚ sqrtNegSixArithmeticPowerBasis.basis = (-24 : ℚ) := by
  rw [Algebra.discr_powerBasis_eq_norm]
  have hgen : sqrtNegSixArithmeticPowerBasis.gen = θ := by
    simp [sqrtNegSixArithmeticPowerBasis, θ]
  rw [hgen, degree_eq_two, sqrtNegSix_minpoly_rat]
  have hder : Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.C (6 : ℚ)) =
      2 * Polynomial.X := by
    simp
    ring
  rw [hder]
  have haev : Polynomial.aeval θ (2 * Polynomial.X : ℚ[X]) = 2 * θ := by
    rw [map_mul, Polynomial.aeval_X, map_ofNat]
  rw [haev]
  have hnorm : Algebra.norm ℚ (2 * θ) = (24 : ℚ) := by
    apply FaithfulSMul.algebraMap_injective ℚ K
    rw [Algebra.norm_eq_prod_automorphisms, prod_auts]
    have hconj : conj' (2 * θ) = -2 * θ := by
      rw [map_mul, map_ofNat, conj'_root]
      ring
    rw [hconj]
    ring_nf
    rw [theta_sq]
    norm_num
  rw [hnorm]
  norm_num

private theorem integralClosure_eq_adjoin :
    integralClosure ℤ K = Algebra.adjoin ℤ ({θ} : Set K) := by
  apply le_antisymm
  · intro z hz
    have hzI : IsIntegral ℤ z := hz
    have hBint : IsIntegral ℤ sqrtNegSixArithmeticPowerBasis.gen := by
      simpa [sqrtNegSixArithmeticPowerBasis] using theta_integral
    have hdiscr :=
      Algebra.discr_mul_isIntegral_mem_adjoin (K := ℚ) (L := K)
        (R := ℤ) (B := sqrtNegSixArithmeticPowerBasis) hBint hzI
    rw [sqrtNegSixArithmeticPowerBasis_discr] at hdiscr
    have h24z : (24 : ℤ) • z ∈
        Algebra.adjoin ℤ ({sqrtNegSixArithmeticPowerBasis.gen} : Set K) := by
      have hneg : (24 : ℤ) • z = -((-24 : ℚ) • z) := by
        simp [Algebra.smul_def]
      rw [hneg]
      exact neg_mem hdiscr
    have h8z_int : IsIntegral ℤ ((2 : ℤ) ^ 3 • z) := hzI.smul ((2 : ℤ) ^ 3)
    have h3pow : (3 : ℤ) ^ 1 • ((2 : ℤ) ^ 3 • z) ∈
        Algebra.adjoin ℤ ({sqrtNegSixArithmeticPowerBasis.gen} : Set K) := by
      convert h24z using 1
      norm_num [Algebra.smul_def]
      ring
    have h8z : (2 : ℤ) ^ 3 • z ∈
        Algebra.adjoin ℤ ({sqrtNegSixArithmeticPowerBasis.gen} : Set K) :=
      mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
        (R := ℤ) (K := ℚ) (L := K) (B := sqrtNegSixArithmeticPowerBasis)
        (p := (3 : ℤ)) (n := 1) (by norm_num : Prime (3 : ℤ)) hBint h8z_int h3pow
        (by
          simpa [sqrtNegSixArithmeticPowerBasis] using
            sqrtNegSix_minpoly_int_isEisensteinAt_three)
    have hzmem : z ∈ Algebra.adjoin ℤ ({sqrtNegSixArithmeticPowerBasis.gen} : Set K) :=
      mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
        (R := ℤ) (K := ℚ) (L := K) (B := sqrtNegSixArithmeticPowerBasis)
        (p := (2 : ℤ)) (n := 3) Int.prime_two hBint hzI h8z
        (by
          simpa [sqrtNegSixArithmeticPowerBasis] using
            sqrtNegSix_minpoly_int_isEisensteinAt_two)
    simpa [sqrtNegSixArithmeticPowerBasis] using hzmem
  · rw [Algebra.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact theta_integral

private theorem thetaInt_adjoin_eq_top : Algebra.adjoin ℤ ({thetaInt} : Set (𝓞 K)) = ⊤ := by
  apply le_antisymm le_top
  intro x hx
  have hfield : (x : K) ∈ Algebra.adjoin ℤ ({θ} : Set K) := by
    rw [← integralClosure_eq_adjoin]
    exact x.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hfield
  rcases hfield with ⟨P, hP⟩
  have hx_eq : x = Polynomial.aeval thetaInt P := by
    apply Subtype.ext
    change (x : K) = ((Polynomial.aeval thetaInt P : 𝓞 K) : K)
    rw [← hP]
    simpa [thetaInt] using
      (Polynomial.aeval_algHom_apply (algebraMap (𝓞 K) K).toIntAlgHom thetaInt P)
  rw [hx_eq]
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨P, rfl⟩

private theorem thetaInt_minpoly : minpoly ℤ thetaInt = sqrtNegSixIntegerPolynomial := by
  letI : IsScalarTower ℤ (𝓞 K) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hint : IsIntegral ℤ thetaInt := Algebra.IsIntegral.isIntegral thetaInt
  have hfrac :
      minpoly ℚ ((algebraMap (𝓞 K) K) thetaInt) =
        Polynomial.map (algebraMap ℤ ℚ) (minpoly ℤ thetaInt) :=
    @minpoly.isIntegrallyClosed_eq_field_fractions ℤ (𝓞 K)
      inferInstance inferInstance inferInstance inferInstance
      ℚ K inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance this inferInstance inferInstance
      thetaInt hint
  apply (Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective)
  rw [← hfrac]
  change minpoly ℚ θ = Polynomial.map (algebraMap ℤ ℚ) sqrtNegSixIntegerPolynomial
  rw [sqrtNegSix_minpoly_rat]
  change Polynomial.X ^ 2 + Polynomial.C (6 : ℚ) =
    Polynomial.map (algebraMap ℤ ℚ) (Polynomial.X ^ 2 + Polynomial.C (6 : ℤ))
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rw [show (algebraMap ℤ ℚ) (6 : ℤ) = (6 : ℚ) by norm_num]

private noncomputable def sqrtNegSixExplicitIntegralPowerBasis : PowerBasis ℤ (𝓞 K) :=
  PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral thetaInt) thetaInt_adjoin_eq_top

private theorem sqrtNegSixExplicitIntegralPowerBasis_dim :
    sqrtNegSixExplicitIntegralPowerBasis.dim = 2 := by
  rw [sqrtNegSixExplicitIntegralPowerBasis, PowerBasis.ofAdjoinEqTop'_dim, thetaInt_minpoly]
  change sqrtNegSixIntegerPolynomial.natDegree = 2
  rw [sqrtNegSixIntegerPolynomial, Polynomial.natDegree_X_pow_add_C]

private noncomputable def sqrtNegSixExplicitIntegralBasis : Basis (Fin 2) ℤ (𝓞 K) :=
  sqrtNegSixExplicitIntegralPowerBasis.basis.reindex
    (finCongr sqrtNegSixExplicitIntegralPowerBasis_dim)

private theorem sqrtNegSixExplicitIntegralBasis_zero :
    sqrtNegSixExplicitIntegralBasis 0 = 1 := by
  rw [sqrtNegSixExplicitIntegralBasis, Basis.reindex_apply]
  rw [sqrtNegSixExplicitIntegralPowerBasis.basis_eq_pow]
  have hcoe :
      (((finCongr sqrtNegSixExplicitIntegralPowerBasis_dim).symm (0 : Fin 2) :
        Fin sqrtNegSixExplicitIntegralPowerBasis.dim) : ℕ) = 0 := rfl
  rw [hcoe]
  simp

private theorem sqrtNegSixExplicitIntegralBasis_one :
    sqrtNegSixExplicitIntegralBasis 1 = thetaInt := by
  rw [sqrtNegSixExplicitIntegralBasis, Basis.reindex_apply]
  rw [sqrtNegSixExplicitIntegralPowerBasis.basis_eq_pow]
  have hcoe :
      (((finCongr sqrtNegSixExplicitIntegralPowerBasis_dim).symm (1 : Fin 2) :
        Fin sqrtNegSixExplicitIntegralPowerBasis.dim) : ℕ) = 1 := rfl
  rw [hcoe, pow_one]
  exact PowerBasis.ofAdjoinEqTop'_gen _ _

private noncomputable def integralBasisVectorsInt : Fin 2 → 𝓞 K := ![1, thetaInt]

private theorem algebraMap_integralBasisVectorsInt :
    (fun i => (algebraMap (𝓞 K) K) (integralBasisVectorsInt i)) = integralBasisVectors := by
  funext i
  fin_cases i <;> simp [integralBasisVectorsInt, integralBasisVectors, thetaInt]

private noncomputable def ringOfIntegersLinearMap : 𝓞 K →ₗ[ℤ] K :=
  (Algebra.linearMap (𝓞 K) K).restrictScalars ℤ

private theorem ringOfIntegersLinearMap_apply (u : 𝓞 K) :
    ringOfIntegersLinearMap u = (algebraMap (𝓞 K) K) u := rfl

private theorem span_integralBasisVectorsInt_eq_top :
    Submodule.span ℤ (Set.range integralBasisVectorsInt) = ⊤ := by
  have hbasis : ⇑sqrtNegSixExplicitIntegralBasis = integralBasisVectorsInt := by
    funext i
    fin_cases i
    · simp [sqrtNegSixExplicitIntegralBasis_zero, integralBasisVectorsInt]
    · simp [sqrtNegSixExplicitIntegralBasis_one, integralBasisVectorsInt]
  rw [← hbasis]
  exact sqrtNegSixExplicitIntegralBasis.span_eq

private theorem sqrtNegSixExplicitIntegralBasis_discr :
    Algebra.discr ℤ sqrtNegSixExplicitIntegralBasis = (-24 : ℤ) := by
  let bInt : Basis (Fin 2) ℤ (𝓞 K) := sqrtNegSixExplicitIntegralBasis
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
  change (algebraMap ℤ ℚ) (Algebra.discr ℤ bInt) = (algebraMap ℤ ℚ) (-24)
  rw [← hdiscLoc]
  change Algebra.discr ℚ bLoc = (-24 : ℚ)
  have hBasis :
      bLoc = sqrtNegSixArithmeticPowerBasis.basis.reindex
        (finCongr sqrtNegSixArithmeticPowerBasis_dim) := by
    apply DFunLike.ext
    intro i
    fin_cases i
    · simp [bLoc, bInt, Basis.localizationLocalization_apply,
        sqrtNegSixExplicitIntegralBasis_zero, Basis.reindex_apply]
    · simp [bLoc, bInt, Basis.localizationLocalization_apply,
        sqrtNegSixExplicitIntegralBasis_one, thetaInt]
      rfl
  rw [hBasis]
  simpa [Basis.coe_reindex] using
    (Algebra.discr_reindex ℚ sqrtNegSixArithmeticPowerBasis.basis
      (finCongr sqrtNegSixArithmeticPowerBasis_dim)).trans sqrtNegSixArithmeticPowerBasis_discr

/-- `1, θ` is an integral basis of `ℚ(√-6)`: their `ℤ`-span in `K` is exactly the ring of
integers `𝓞 K`. Since `-6 ≡ 2 (mod 4)`, the naive order `ℤ[√-6]` is already maximal — in
contrast with `ℚ(√5)`. -/
theorem span_integralBasisVectors_eq :
    Submodule.span ℤ (Set.range integralBasisVectors) =
      Subalgebra.toSubmodule (integralClosure ℤ K) := by
  have hmap :=
    congrArg (Submodule.map ringOfIntegersLinearMap) span_integralBasisVectorsInt_eq_top
  rw [Submodule.map_span, ← Set.range_comp] at hmap
  have hcomp : ringOfIntegersLinearMap ∘ integralBasisVectorsInt = integralBasisVectors := by
    funext i
    rw [Function.comp_apply, ringOfIntegersLinearMap_apply, ← algebraMap_integralBasisVectorsInt]
  rw [hcomp, Submodule.map_top] at hmap
  rw [hmap]
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact u.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The integral basis `1, θ` packaged as a genuine `ℤ`-basis of the ring of integers `𝓞 K`. -/
noncomputable def concreteIntegralBasis : Basis (Fin 2) ℤ (𝓞 K) := by
  exact sqrtNegSixExplicitIntegralBasis

/-- The packaged integral basis is, vector by vector, the displayed family `1, θ`. -/
theorem concreteIntegralBasis_apply (i : Fin 2) :
    (algebraMap (𝓞 K) K) (concreteIntegralBasis i) = integralBasisVectors i := by
  fin_cases i <;>
    simp [concreteIntegralBasis, sqrtNegSixExplicitIntegralBasis_zero,
      sqrtNegSixExplicitIntegralBasis_one, integralBasisVectors, thetaInt]

theorem exists_eq_smul_one_add_smul_theta (z : 𝓞 K) :
    ∃ x y : ℤ, z = x • (1 : 𝓞 K) + y • thetaInt := by
  refine ⟨concreteIntegralBasis.repr z 0, concreteIntegralBasis.repr z 1, ?_⟩
  apply IsFractionRing.injective (𝓞 K) K
  have hsum := concreteIntegralBasis.sum_repr z
  conv_lhs => rw [← hsum]
  rw [map_sum]
  rw [Fin.sum_univ_two]
  simp [concreteIntegralBasis_apply, integralBasisVectors, thetaInt]

theorem linearIndependent_one_theta : LinearIndependent ℤ ![(1 : 𝓞 K), thetaInt] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_two] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  have h0 : concreteIntegralBasis 0 = (1 : 𝓞 K) := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [concreteIntegralBasis_apply]
    simp [integralBasisVectors]
  have h1 : concreteIntegralBasis 1 = thetaInt := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [concreteIntegralBasis_apply]
    simp [integralBasisVectors, thetaInt]
  have hsum : ∑ i : Fin 2, g i • concreteIntegralBasis i = 0 := by
    rw [Fin.sum_univ_two, h0, h1]
    exact hg
  exact Fintype.linearIndependent_iff.mp concreteIntegralBasis.linearIndependent g hsum

/-- The displayed integral basis `1, θ` spans the same `ℤ`-lattice in `K` as mathlib's
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

/-- The concrete order `ℤ[θ]` inside `K`. -/
abbrev concreteRingOfIntegers : Subalgebra ℤ K := Algebra.adjoin ℤ ({θ} : Set K)

/-- The full ring of integers of `ℚ(√-6)` is `ℤ[θ]` (maximality of the naive order, since
`-6 ≡ 2 (mod 4)`). -/
theorem ringOfIntegers_eq : integralClosure ℤ K = concreteRingOfIntegers := by
  exact integralClosure_eq_adjoin

/-! ## 3. Discriminant -/

/-- The number-field discriminant of `ℚ(√-6)` is `-24` (for `d ≡ 2, 3 (mod 4)` squarefree
the discriminant of `ℚ(√d)` is `4d`). In particular the ramified primes are exactly `2`
and `3`, cf. `ramified_iff`. -/
theorem numberField_discr_eq : NumberField.discr K = (-24 : ℤ) := by
  rw [← NumberField.discr_eq_discr K concreteIntegralBasis]
  exact sqrtNegSixExplicitIntegralBasis_discr

/-- The discriminant of the explicit integral basis `1, θ` is `-24`. -/
theorem concreteIntegralBasis_discr :
    Algebra.discr ℤ concreteIntegralBasis = (-24 : ℤ) := by
  exact sqrtNegSixExplicitIntegralBasis_discr


end XYin.NumberField.New.SqrtNegSixAdjoinRoot
