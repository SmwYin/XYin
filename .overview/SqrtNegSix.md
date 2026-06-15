# SqrtNegSix declaration inventory

Field: `K = ℚ(√-6) = QuadraticAlgebra ℚ (-6) 0`. Imaginary quadratic, signature `(0,1)`,
discriminant `-24`, ring of integers `ℤ[√-6]` (maximal order), class number `2`,
non-trivial class group `ℤ/2`, **not** a UFD/PID, **not** norm-Euclidean.

All declarations live in `namespace NumberField.SqrtNegSix` unless noted.
`𝓞 K` denotes `NumberField.RingOfIntegers K`. `θ = √-6`, `thetaInt` its integral lift.

Common helpers referenced live in `namespace NumberField.FieldExamples`
(file `FieldExamples/Common.lean`).

---

## Basic.lean

### `instance : Fact (∀ r : ℚ, r ^ 2 ≠ (-6 : ℚ) + (0 : ℚ) * r)`
- **Type**: `Fact (∀ r : ℚ, r ^ 2 ≠ (-6 : ℚ) + (0 : ℚ) * r)`
- **What**: The nonsquare condition that makes `QuadraticAlgebra ℚ (-6) 0` a field.
- **How**: `sq_nonneg r` plus `nlinarith`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Visibility**: public (instance)
- **Lines**: 33-36
- **Notes**: none.

### `abbrev K`
- **Type**: `Type := QuadraticAlgebra ℚ (-6 : ℚ) 0`
- **What**: The number field `ℚ(√-6)`.
- **How**: definitional.
- **Hypotheses**: none.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 39
- **Notes**: none.

### `abbrev θ`
- **Type**: `K := QuadraticAlgebra.omega`
- **What**: The distinguished square root of `-6`.
- **How**: definitional.
- **Uses from project**: [`K`]
- **Visibility**: public
- **Lines**: 42

### `instance : Field K`
- **Type**: `Field K`
- **What**: Field structure on `K`.
- **How**: `infer_instance`.
- **Uses from project**: [`K`]
- **Visibility**: public (instance)
- **Lines**: 45-46

### `instance : FiniteDimensional ℚ K`
- **Type**: `FiniteDimensional ℚ K`
- **What**: `K` is finite-dimensional over `ℚ`.
- **How**: `QuadraticAlgebra.basis ... |>.finiteDimensional_of_finite`.
- **Uses from project**: [`K`]
- **Visibility**: public (instance)
- **Lines**: 49-50

### `instance : NumberField K`
- **Type**: `NumberField K`
- **What**: Number-field structure on `K`.
- **How**: `NumberField.of_module_finite ℚ K`.
- **Uses from project**: [`K`]
- **Visibility**: public (instance)
- **Lines**: 53-54

### `theorem degree_eq_two`
- **Type**: `Module.finrank ℚ K = 2`
- **What**: `[K : ℚ] = 2`.
- **How**: `Module.finrank_eq_card_basis` on `QuadraticAlgebra.basis`, then `Fintype.card_fin`.
- **Uses from project**: [`K`]
- **Visibility**: public
- **Lines**: 57-58

### `instance : Algebra.IsQuadraticExtension ℚ K`
- **Type**: `Algebra.IsQuadraticExtension ℚ K`
- **What**: Quadratic-extension class instance.
- **How**: field `finrank_eq_two' := degree_eq_two`.
- **Uses from project**: [`K`, `degree_eq_two`]
- **Visibility**: public (instance)
- **Lines**: 60-61

### `theorem theta_sq`
- **Type**: `θ ^ 2 = -6`
- **What**: `θ² = -6`.
- **How**: `QuadraticAlgebra.omega_mul_omega_eq_add`, simp.
- **Uses from project**: [`θ`]
- **Visibility**: public
- **Lines**: 64-66
- **Notes**: KEY API (used 15+ times across folder).

### `abbrev sqrtNegSixPolynomial`
- **Type**: `Polynomial ℚ := X ^ 2 + C 6`
- **What**: defining polynomial `X²+6`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 69-70

### `instance : Fact (Irreducible sqrtNegSixPolynomial)`
- **Type**: `Fact (Irreducible sqrtNegSixPolynomial)`
- **What**: `X²+6` is irreducible over `ℚ`.
- **How**: `Polynomial.irreducible_of_degree_le_three_of_not_isRoot`, `natDegree_X_pow_add_C`, `nlinarith` for no real root.
- **Uses from project**: [`sqrtNegSixPolynomial`]
- **Visibility**: public (instance)
- **Lines**: 72-84

### `abbrev KAdjoinRoot`
- **Type**: `Type := AdjoinRoot sqrtNegSixPolynomial`
- **What**: `AdjoinRoot` presentation of the same field.
- **Uses from project**: [`sqrtNegSixPolynomial`]
- **Visibility**: public
- **Lines**: 87

### `abbrev thetaAdjoinRoot`
- **Type**: `KAdjoinRoot := AdjoinRoot.root sqrtNegSixPolynomial`
- **What**: root in the `AdjoinRoot` model.
- **Uses from project**: [`KAdjoinRoot`, `sqrtNegSixPolynomial`]
- **Visibility**: public
- **Lines**: 90

### `theorem thetaAdjoinRoot_sq`
- **Type**: `thetaAdjoinRoot ^ 2 = (-6 : KAdjoinRoot)`
- **What**: root squares to `-6`.
- **How**: `AdjoinRoot.eval₂_root`, `linear_combination`.
- **Uses from project**: [`thetaAdjoinRoot`, `sqrtNegSixPolynomial`]
- **Visibility**: public
- **Lines**: 92-97

### `private theorem sqrtNegSixPolynomial_aeval_theta`
- **Type**: `Polynomial.eval₂ (Algebra.ofId ℚ K) θ sqrtNegSixPolynomial = 0`
- **What**: `θ` is a root of the defining polynomial via `eval₂`.
- **How**: calc to `θ²+6 = 0`, `theta_sq`.
- **Uses from project**: [`K`, `θ`, `sqrtNegSixPolynomial`, `theta_sq`]
- **Visibility**: private
- **Lines**: 99-103

### `private theorem thetaAdjoinRoot_mul_self`
- **Type**: `thetaAdjoinRoot * thetaAdjoinRoot = (-6) • 1 + 0 • thetaAdjoinRoot`
- **What**: multiplication table for the `AdjoinRoot` generator (quadratic-algebra form).
- **How**: rewrite to `^2`, `thetaAdjoinRoot_sq`, simp.
- **Uses from project**: [`thetaAdjoinRoot`, `thetaAdjoinRoot_sq`, `KAdjoinRoot`]
- **Visibility**: private
- **Lines**: 105-110

### `noncomputable def adjoinRootEquivQuadratic`
- **Type**: `KAdjoinRoot ≃ₐ[ℚ] K`
- **What**: equivalence between the `AdjoinRoot` and quadratic-algebra presentations.
- **How**: `AdjoinRoot.liftAlgHom` one way, `QuadraticAlgebra.lift` the other; `AlgEquiv.ofAlgHom` with `QuadraticAlgebra.algHom_ext` / `AdjoinRoot.algHom_ext` round-trips.
- **Uses from project**: [`KAdjoinRoot`, `K`, `θ`, `sqrtNegSixPolynomial_aeval_theta`, `thetaAdjoinRoot`, `thetaAdjoinRoot_mul_self`]
- **Visibility**: public
- **Lines**: 113-136
- **Notes**: proof >20 lines.

### `theorem adjoinRootEquivQuadratic_root`
- **Type**: `adjoinRootEquivQuadratic thetaAdjoinRoot = θ`
- **What**: the equivalence maps the formal root to `θ`.
- **How**: unfolds to `AdjoinRoot.liftAlgHom_root`.
- **Uses from project**: [`adjoinRootEquivQuadratic`, `thetaAdjoinRoot`, `θ`, `sqrtNegSixPolynomial`, `sqrtNegSixPolynomial_aeval_theta`]
- **Visibility**: public
- **Lines**: 138-143

**File Summary (Basic.lean)**: 17 decls (1 def + 1 noncomputable def, 7 theorems, 6 abbrevs, 5 instances).
Key API: `theta_sq` (used 15+×), `K`, `θ`, `degree_eq_two`. Unused outside file: `adjoinRootEquivQuadratic`, `adjoinRootEquivQuadratic_root`, `thetaAdjoinRoot*`, `KAdjoinRoot` (twin/parallel presentation, only consumed in Basic). No sorry, no set_option, no proof >30 lines.

---

## Galois.lean

### `noncomputable def idAut`
- **Type**: `K ≃ₐ[ℚ] K := AlgEquiv.refl`
- **What**: identity automorphism.
- **Uses from project**: [`K`]
- **Visibility**: public
- **Lines**: 32

### `private noncomputable def conjugationHom`
- **Type**: `K →ₐ[ℚ] K`
- **What**: the algebra map `θ ↦ -θ`.
- **How**: `QuadraticAlgebra.lift` with multiplication-table witness from `omega_mul_omega_eq_add`.
- **Uses from project**: [`K`]
- **Visibility**: private
- **Lines**: 35-39

### `private theorem conjugationHom_omega`
- **Type**: `conjugationHom θ = -θ`
- **How**: unfold lift, simp.
- **Uses from project**: [`conjugationHom`, `θ`]
- **Visibility**: private
- **Lines**: 41-44

### `private theorem conjugationHom_conjugationHom`
- **Type**: `conjugationHom.comp conjugationHom = AlgHom.id ℚ K`
- **What**: conjugation is an involution.
- **How**: `QuadraticAlgebra.algHom_ext`, `conjugationHom_omega`, `neg_neg`.
- **Uses from project**: [`conjugationHom`, `conjugationHom_omega`, `θ`]
- **Visibility**: private
- **Lines**: 46-50

### `noncomputable def conjugation`
- **Type**: `K ≃ₐ[ℚ] K`
- **What**: the nontrivial conjugation automorphism `θ ↦ -θ`.
- **How**: `AlgEquiv.ofAlgHom conjugationHom conjugationHom` using the involution lemma both ways.
- **Uses from project**: [`conjugationHom`, `conjugationHom_conjugationHom`, `K`]
- **Visibility**: public
- **Lines**: 54-56

### `theorem conjugation_apply_theta`
- **Type**: `conjugation θ = -θ`
- **How**: `conjugationHom_omega`.
- **Uses from project**: [`conjugation`, `θ`, `conjugationHom_omega`]
- **Visibility**: public
- **Lines**: 59-60

### `theorem isGalois`
- **Type**: `IsGalois ℚ K`
- **How**: `infer_instance`.
- **Uses from project**: [`K`]
- **Visibility**: public
- **Lines**: 62-63

### `theorem aut_eq_or`
- **Type**: `(σ : K ≃ₐ[ℚ] K) → σ = idAut ∨ σ = conjugation`
- **What**: every `ℚ`-automorphism is `id` or conjugation.
- **How**: `(σθ)² = -6 ⇒ (σθ-θ)(σθ+θ)=0`; `QuadraticAlgebra.algHom_ext` to extend equality on the generator.
- **Uses from project**: [`K`, `θ`, `theta_sq`, `idAut`, `conjugation`, `conjugation_apply_theta`]
- **Visibility**: public
- **Lines**: 66-82
- **Notes**: KEY (used by `prod_auts`, `galoisGroupStructure`).

### `private theorem conjugation_ne_id`
- **Type**: `conjugation ≠ idAut`
- **How**: would force `2θ=0`, contradicts `theta_sq` via `mul_eq_zero`.
- **Uses from project**: [`conjugation`, `idAut`, `conjugation_apply_theta`, `θ`, `theta_sq`]
- **Visibility**: private
- **Lines**: 84-93

### `theorem prod_auts`
- **Type**: `(z : K) → ∏ σ : K ≃ₐ[ℚ] K, σ z = z * conjugation z`
- **What**: product over the Galois group equals `z · conjugation z` (relative norm).
- **How**: `Finset.univ = {id, conjugation}` via `aut_eq_or`, `Finset.prod_insert`/`prod_singleton`.
- **Uses from project**: [`K`, `idAut`, `conjugation`, `aut_eq_or`, `conjugation_ne_id`]
- **Visibility**: public
- **Lines**: 95-107

### `theorem galoisGroupStructure`
- **Type**: `Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2))`
- **What**: `Gal(K/ℚ) ≅ ℤ/2`.
- **How**: `Nat.card_eq_two_iff` from `idAut`,`conjugation`; `mulEquivOfPrimeCardEq` (mathlib).
- **Uses from project**: [`K`, `idAut`, `conjugation`, `conjugation_ne_id`, `aut_eq_or`]
- **Visibility**: public
- **Lines**: 109-118

**File Summary (Galois.lean)**: 11 decls (3 defs, 8 theorems). Key API: `aut_eq_or`, `conjugation`, `conjugation_apply_theta`, `theta_sq`. Unused outside file: `prod_auts`, `galoisGroupStructure`, `isGalois`, `idAut` (terminal results). No sorry, no set_option, no proof >30 lines.

---

## Embeddings.lean

### `theorem isTotallyComplex`
- **Type**: `NumberField.IsTotallyComplex K`
- **What**: `K` is totally complex (no real embedding).
- **How**: any embedding has `z²=-6`; real-embedding ⇒ `z.im=0` ⇒ contradiction via `nlinarith [sq_nonneg z.re]`. Uses `ComplexEmbedding.isReal_iff`, `Complex.conj_eq_iff_im`.
- **Uses from project**: [`K`, `θ`, `theta_sq`]
- **Visibility**: public
- **Lines**: 34-48
- **Notes**: KEY (used by Embeddings, CMField, ClassGroup, LocalGlobal).

### `theorem nrRealPlaces_eq_zero`
- **Type**: `NumberField.InfinitePlace.nrRealPlaces K = 0`
- **How**: `IsTotallyComplex.nrRealPlaces_eq_zero`.
- **Uses from project**: [`K`, `isTotallyComplex`]
- **Visibility**: public
- **Lines**: 50-52
- **Notes**: KEY (used 5+×).

### `theorem nrComplexPlaces_eq_one`
- **Type**: `NumberField.InfinitePlace.nrComplexPlaces K = 1`
- **How**: `card_add_two_mul_card_eq_rank`, `nrRealPlaces_eq_zero`, `degree_eq_two`, omega.
- **Uses from project**: [`K`, `nrRealPlaces_eq_zero`, `degree_eq_two`]
- **Visibility**: public
- **Lines**: 54-57
- **Notes**: KEY (used 4+×).

### `theorem infinitePlace_card_eq_one`
- **Type**: `Fintype.card (NumberField.InfinitePlace K) = 1`
- **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces` + the two place counts.
- **Uses from project**: [`K`, `nrRealPlaces_eq_zero`, `nrComplexPlaces_eq_one`]
- **Visibility**: public
- **Lines**: 71-74

### `theorem infinitePlace_isComplex`
- **Type**: `(v : InfinitePlace K) → v.IsComplex`
- **How**: `isTotallyComplex.isComplex v`.
- **Uses from project**: [`K`, `isTotallyComplex`]
- **Visibility**: public
- **Lines**: 76-78
- **Notes**: used in LocalGlobal.

### `theorem exists_complexEmbedding_theta_pos`
- **Type**: `∃ σ : K →+* ℂ, σ θ = Complex.I * (Real.sqrt 6)`
- **How**: `QuadraticAlgebra.lift` to `I√6` with witness via `Complex.I_mul_I`, `Real.sq_sqrt`.
- **Uses from project**: [`K`, `θ`]
- **Visibility**: public
- **Lines**: 80-89

### `theorem exists_complexEmbedding_theta_neg`
- **Type**: `∃ σ : K →+* ℂ, σ θ = -Complex.I * (Real.sqrt 6)`
- **How**: as above with `-I√6`.
- **Uses from project**: [`K`, `θ`]
- **Visibility**: public
- **Lines**: 91-100

**File Summary (Embeddings.lean)**: 7 theorems. Key API: `isTotallyComplex`, `nrRealPlaces_eq_zero`, `nrComplexPlaces_eq_one`, `infinitePlace_isComplex`. Unused outside file: `infinitePlace_card_eq_one`, `exists_complexEmbedding_theta_pos/neg`. `attribute [-instance] DivisionRing.toRatAlgebra` (set_option-like attribute manipulation, line 26). No sorry. No proof >30 lines.

---

## RingOfIntegers.lean

### `theorem theta_integral`
- **Type**: `θ ∈ integralClosure ℤ K`
- **What**: `θ` is integral over `ℤ` (root of monic `X²+6`).
- **How**: provide `X²+6`, `monicity!`, `eval₂` simp + `theta_sq`.
- **Uses from project**: [`θ`, `K`, `theta_sq`]
- **Visibility**: public
- **Lines**: 33-37
- **Notes**: KEY.

### `noncomputable def thetaInt`
- **Type**: `𝓞 K := ⟨θ, theta_integral⟩`
- **What**: `θ` as an algebraic integer.
- **Uses from project**: [`K`, `θ`, `theta_integral`]
- **Visibility**: public
- **Lines**: 40
- **Notes**: KEY (the central generator, used everywhere downstream).

### `theorem thetaInt_sq`
- **Type**: `thetaInt ^ 2 = -6`
- **How**: `Subtype.ext`, `theta_sq`.
- **Uses from project**: [`thetaInt`, `θ`, `theta_sq`]
- **Visibility**: public
- **Lines**: 43-46
- **Notes**: KEY (used 20+×).

### `def integralBasisVectors`
- **Type**: `Fin 2 → K := ![1, θ]`
- **Uses from project**: [`K`, `θ`]
- **Visibility**: public
- **Lines**: 49

### `local notation 𝓟₂ / 𝓟₃`
- ideal `span ℤ {2}` / `span ℤ {3}` (local notation, lines 51-52).

### `private theorem quadraticBasis_zero / quadraticBasis_one`
- **Type**: `QuadraticAlgebra.basis (-6) 0 0 = 1` / `... 1 = θ`
- **How**: unfold `Basis.ofEquivFun`/`linearEquivTuple`, simp.
- **Uses from project**: [`K`, `θ`]
- **Visibility**: private
- **Lines**: 54-60

### `noncomputable def sqrtNegSixPowerBasis`
- **Type**: `PowerBasis ℚ K` (gen `θ`, dim 2, basis `QuadraticAlgebra.basis`)
- **Uses from project**: [`θ`, `K`, `quadraticBasis_zero`, `quadraticBasis_one`]
- **Visibility**: public
- **Lines**: 63-71

### `abbrev sqrtNegSixIntegerPolynomial`
- **Type**: `ℤ[X] := X ^ 2 + C 6`
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 74

### `theorem sqrtNegSix_minpoly_rat`
- **Type**: `minpoly ℚ θ = sqrtNegSixPolynomial`
- **How**: `minpoly.eq_of_irreducible_of_monic`, irreducibility `Fact`, `monicity!`.
- **Uses from project**: [`θ`, `sqrtNegSixPolynomial`, `theta_sq`]
- **Visibility**: public
- **Lines**: 77-83

### `theorem sqrtNegSix_minpoly_int`
- **Type**: `minpoly ℤ θ = sqrtNegSixIntegerPolynomial`
- **How**: `map_injective`, `minpoly.isIntegrallyClosed_eq_field_fractions'`, `sqrtNegSix_minpoly_rat`.
- **Uses from project**: [`θ`, `sqrtNegSixIntegerPolynomial`, `theta_integral`, `sqrtNegSix_minpoly_rat`]
- **Visibility**: public
- **Lines**: 87-94

### `theorem sqrtNegSix_minpoly_int_isEisensteinAt_two`
- **Type**: `(minpoly ℤ θ).IsEisensteinAt 𝓟₂`
- **How**: `monic_X_pow_add_C ... isEisensteinAt_of_mem_of_notMem`; membership of `6` in `(2)`, `6 ∉ (2)²=(4)`.
- **Uses from project**: [`θ`, `sqrtNegSix_minpoly_int`]
- **Visibility**: public
- **Lines**: 97-112

### `theorem sqrtNegSix_minpoly_int_isEisensteinAt_three`
- **Type**: `(minpoly ℤ θ).IsEisensteinAt 𝓟₃`
- **How**: as above at `3` (`6 ∈ (3)`, `6 ∉ (9)`).
- **Uses from project**: [`θ`, `sqrtNegSix_minpoly_int`]
- **Visibility**: public
- **Lines**: 115-130

### `private theorem algebraNorm_eq_quadraticNorm`
- **Type**: `(z : K) → Algebra.norm ℚ z = QuadraticAlgebra.norm z`
- **How**: `Algebra.norm_apply`, `QuadraticAlgebra.det_toLinearMap_eq_norm`.
- **Uses from project**: [`K`]
- **Visibility**: private
- **Lines**: 132-135
- **Notes**: GENERIC-looking — duplicated as inline `have` in `norm_eq_normForm`.

### `theorem sqrtNegSixPowerBasis_discr`
- **Type**: `Algebra.discr ℚ sqrtNegSixPowerBasis.basis = -24`
- **How**: `discr_powerBasis_eq_norm`, `degree_eq_two`, derivative `2X`, norm of `2θ`=24.
- **Uses from project**: [`sqrtNegSixPowerBasis`, `degree_eq_two`, `sqrtNegSix_minpoly_rat`, `θ`, `algebraNorm_eq_quadraticNorm`]
- **Visibility**: public
- **Lines**: 138-156

### `private theorem integralClosure_eq_adjoin`
- **Type**: `integralClosure ℤ K = Algebra.adjoin ℤ {θ}`
- **What**: `𝓞 K = ℤ[θ]` (maximality of naive order).
- **How**: `discr_mul_isIntegral_mem_adjoin` gives `24z ∈ ℤ[θ]`; `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt` strips primes 3 then 2 using Eisenstein lemmas.
- **Uses from project**: [`K`, `θ`, `sqrtNegSixPowerBasis`, `theta_integral`, `sqrtNegSixPowerBasis_discr`, `sqrtNegSix_minpoly_int_isEisensteinAt_two/three`]
- **Visibility**: private
- **Lines**: 158-196
- **Notes**: proof >30 lines.

### `private theorem thetaInt_adjoin_eq_top`
- **Type**: `Algebra.adjoin ℤ {thetaInt} = ⊤`
- **How**: lift integral elements through `adjoin_singleton_eq_range_aeval`, `aeval_algHom_apply`.
- **Uses from project**: [`thetaInt`, `θ`, `integralClosure_eq_adjoin`, `K`]
- **Visibility**: private
- **Lines**: 198-214

### `private theorem thetaInt_minpoly`
- **Type**: `minpoly ℤ thetaInt = sqrtNegSixIntegerPolynomial`
- **How**: `minpoly.isIntegrallyClosed_eq_field_fractions`, `sqrtNegSix_minpoly_rat`.
- **Uses from project**: [`thetaInt`, `sqrtNegSixIntegerPolynomial`, `K`, `sqrtNegSix_minpoly_rat`, `θ`]
- **Visibility**: private
- **Lines**: 216-234

### `private noncomputable def sqrtNegSixExplicitIntegralPowerBasis`
- **Type**: `PowerBasis ℤ (𝓞 K)`
- **How**: `PowerBasis.ofAdjoinEqTop'`.
- **Uses from project**: [`thetaInt`, `thetaInt_adjoin_eq_top`, `K`]
- **Visibility**: private
- **Lines**: 236-237

### `private theorem sqrtNegSixExplicitIntegralPowerBasis_dim`
- **Type**: `... .dim = 2`
- **Uses from project**: [`sqrtNegSixExplicitIntegralPowerBasis`, `thetaInt_minpoly`, `sqrtNegSixIntegerPolynomial`]
- **Visibility**: private
- **Lines**: 239-243

### `private noncomputable def sqrtNegSixExplicitIntegralBasis`
- **Type**: `Basis (Fin 2) ℤ (𝓞 K)` (reindexed power basis)
- **Uses from project**: [`sqrtNegSixExplicitIntegralPowerBasis`, `sqrtNegSixExplicitIntegralPowerBasis_dim`]
- **Visibility**: private
- **Lines**: 245-247

### `private theorem sqrtNegSixExplicitIntegralBasis_zero / _one`
- **Type**: `... 0 = 1` / `... 1 = thetaInt`
- **How**: `Basis.reindex_apply`, `basis_eq_pow`, `ofAdjoinEqTop'_gen`.
- **Uses from project**: [`sqrtNegSixExplicitIntegralBasis`, `sqrtNegSixExplicitIntegralPowerBasis*`, `thetaInt`]
- **Visibility**: private
- **Lines**: 249-267

### `private noncomputable def integralBasisVectorsInt`
- **Type**: `Fin 2 → 𝓞 K := ![1, thetaInt]`
- **Uses from project**: [`thetaInt`, `K`]
- **Visibility**: private
- **Lines**: 269

### `private theorem algebraMap_integralBasisVectorsInt`
- **Type**: `(fun i => algebraMap (𝓞 K) K (integralBasisVectorsInt i)) = integralBasisVectors`
- **Uses from project**: [`integralBasisVectorsInt`, `integralBasisVectors`, `thetaInt`, `K`]
- **Visibility**: private
- **Lines**: 271-274

### `private noncomputable def ringOfIntegersLinearMap`
- **Type**: `𝓞 K →ₗ[ℤ] K` (restriction of algebra map)
- **Uses from project**: [`K`]
- **Visibility**: private
- **Lines**: 276-277
- **Notes**: GENERIC-looking; restrictScalars of `Algebra.linearMap`.

### `private theorem span_integralBasisVectorsInt_eq_top`
- **Type**: `Submodule.span ℤ (range integralBasisVectorsInt) = ⊤`
- **Uses from project**: [`sqrtNegSixExplicitIntegralBasis`, `sqrtNegSixExplicitIntegralBasis_zero/_one`, `integralBasisVectorsInt`]
- **Visibility**: private
- **Lines**: 279-287

### `private theorem sqrtNegSixExplicitIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ sqrtNegSixExplicitIntegralBasis = -24`
- **How**: `Algebra.discr_localizationLocalization` + `Basis.localizationLocalization` to descend to `ℚ`, then `discr_reindex` and `sqrtNegSixPowerBasis_discr`.
- **Uses from project**: [`sqrtNegSixExplicitIntegralBasis`, `sqrtNegSixExplicitIntegralBasis_zero/_one`, `sqrtNegSixPowerBasis`, `quadraticBasis_one`, `thetaInt`, `sqrtNegSixPowerBasis_discr`]
- **Visibility**: private
- **Lines**: 289-324
- **Notes**: proof >30 lines.

### `theorem span_integralBasisVectors_eq`
- **Type**: `Submodule.span ℤ (range integralBasisVectors) = Subalgebra.toSubmodule (integralClosure ℤ K)`
- **What**: `1,θ` ℤ-span = ring of integers.
- **How**: image of `span_integralBasisVectorsInt_eq_top` under `ringOfIntegersLinearMap`.
- **Uses from project**: [`integralBasisVectors`, `K`, `ringOfIntegersLinearMap`, `span_integralBasisVectorsInt_eq_top`, `algebraMap_integralBasisVectorsInt`, `integralBasisVectorsInt`]
- **Visibility**: public
- **Lines**: 329-347

### `noncomputable def concreteIntegralBasis`
- **Type**: `Basis (Fin 2) ℤ (𝓞 K)` (= `sqrtNegSixExplicitIntegralBasis`)
- **Uses from project**: [`sqrtNegSixExplicitIntegralBasis`, `K`]
- **Visibility**: public
- **Lines**: 350-351
- **Notes**: KEY (used in `exists_eq_smul_one_add_smul_theta`, `linearIndependent_one_theta`, discriminant).

### `theorem concreteIntegralBasis_apply`
- **Type**: `(i : Fin 2) → algebraMap (𝓞 K) K (concreteIntegralBasis i) = integralBasisVectors i`
- **Uses from project**: [`concreteIntegralBasis`, `sqrtNegSixExplicitIntegralBasis_zero/_one`, `integralBasisVectors`, `thetaInt`, `K`]
- **Visibility**: public
- **Lines**: 354-358

### `theorem exists_eq_smul_one_add_smul_theta`
- **Type**: `(z : 𝓞 K) → ∃ x y : ℤ, z = x • 1 + y • thetaInt`
- **What**: every algebraic integer is `x + yθ`.
- **How**: `concreteIntegralBasis.repr`/`sum_repr`, `IsFractionRing.injective`.
- **Uses from project**: [`K`, `thetaInt`, `concreteIntegralBasis`, `concreteIntegralBasis_apply`, `integralBasisVectors`]
- **Visibility**: public
- **Lines**: 360-368
- **Notes**: KEY (used 25+× across folder).

### `theorem linearIndependent_one_theta`
- **Type**: `LinearIndependent ℤ ![(1 : 𝓞 K), thetaInt]`
- **How**: reduce to `concreteIntegralBasis.linearIndependent` via `Fintype.linearIndependent_iff`.
- **Uses from project**: [`K`, `thetaInt`, `concreteIntegralBasis`, `concreteIntegralBasis_apply`, `integralBasisVectors`]
- **Visibility**: public
- **Lines**: 370-386
- **Notes**: KEY (used in PrimeSplitting non-membership args).

### `theorem span_integralBasisVectors_eq_integralBasis`
- **Type**: `span ℤ (range integralBasisVectors) = span ℤ (range (NumberField.integralBasis K))`
- **What**: the displayed basis spans the same lattice as mathlib's `integralBasis`.
- **How**: `span_integralBasisVectors_eq`, `NumberField.mem_span_integralBasis`.
- **Uses from project**: [`integralBasisVectors`, `K`, `span_integralBasisVectors_eq`]
- **Visibility**: public
- **Lines**: 391-402

### `abbrev concreteRingOfIntegers`
- **Type**: `Subalgebra ℤ K := Algebra.adjoin ℤ {θ}`
- **Uses from project**: [`K`, `θ`]
- **Visibility**: public
- **Lines**: 405

### `theorem ringOfIntegers_eq`
- **Type**: `integralClosure ℤ K = concreteRingOfIntegers`
- **What**: **ring of integers = `ℤ[θ]`** (main result).
- **How**: `integralClosure_eq_adjoin`.
- **Uses from project**: [`K`, `concreteRingOfIntegers`, `integralClosure_eq_adjoin`]
- **Visibility**: public
- **Lines**: 409-410
- **Notes**: MAIN PUBLIC RESULT.

### `theorem numberField_discr_eq`
- **Type**: `NumberField.discr K = -24`
- **What**: **field discriminant = -24** (main result).
- **How**: `NumberField.discr_eq_discr K concreteIntegralBasis`, `sqrtNegSixExplicitIntegralBasis_discr`.
- **Uses from project**: [`K`, `concreteIntegralBasis`, `sqrtNegSixExplicitIntegralBasis_discr`]
- **Visibility**: public
- **Lines**: 415-417
- **Notes**: MAIN PUBLIC RESULT; used in ClassGroup (Minkowski) and PrimeSplitting (ramified_iff, different).

### `theorem concreteIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ concreteIntegralBasis = -24`
- **Uses from project**: [`concreteIntegralBasis`, `sqrtNegSixExplicitIntegralBasis_discr`]
- **Visibility**: public
- **Lines**: 420-422

### `theorem integralBasis_discr`
- **Type**: `Algebra.discr ℚ (NumberField.integralBasis K) = -24`
- **How**: `NumberField.coe_discr`, `numberField_discr_eq`.
- **Uses from project**: [`K`, `numberField_discr_eq`]
- **Visibility**: public
- **Lines**: 425-429

### `theorem norm_eq_normForm`
- **Type**: `(x y : ℚ) → Algebra.norm ℚ (x • 1 + y • θ) = x ^ 2 + 6 * y ^ 2`
- **What**: norm form `N(x+yθ) = x²+6y²` over `ℚ`.
- **How**: `QuadraticAlgebra.det_toLinearMap_eq_norm`, `norm_def`, ring.
- **Uses from project**: [`K`, `θ`]
- **Visibility**: public
- **Lines**: 446-454
- **Notes**: inline re-derivation of `algebraNorm_eq_quadraticNorm`.

### `theorem intNorm_eq_normForm`
- **Type**: `(x y : ℤ) → Algebra.norm ℤ (x • 1 + y • thetaInt) = x ^ 2 + 6 * y ^ 2`
- **What**: integral norm form.
- **How**: `Algebra.coe_norm_int`, push through algebraMap, `norm_eq_normForm`.
- **Uses from project**: [`K`, `thetaInt`, `θ`, `norm_eq_normForm`]
- **Visibility**: public
- **Lines**: 458-469
- **Notes**: KEY (used 25+×; the workhorse of all norm computations).

### `theorem normForm_ne_two`
- **Type**: `(x y : ℤ) → x ^ 2 + 6 * y ^ 2 ≠ 2`
- **How**: `nlinarith`/`interval_cases`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 471-479
- **Notes**: KEY (non-principality of `(2,θ)`).

### `private theorem normForm_ne_three / normForm_ne_five`
- **Type**: `... ≠ 3` / `... ≠ 5`
- **How**: same pattern.
- **Uses from project**: []
- **Visibility**: private
- **Lines**: 481-503

### `theorem isUnit_iff_normForm`
- **Type**: `(x y : ℤ) → IsUnit (x•1 + y•thetaInt) ↔ x²+6y²=1`
- **How**: `NumberField.isUnit_iff_norm`, `intNorm_eq_normForm`, `abs_eq`, sign analysis.
- **Uses from project**: [`K`, `thetaInt`, `intNorm_eq_normForm`]
- **Visibility**: public
- **Lines**: 507-519
- **Notes**: KEY (units, torsion).

### `theorem intNorm_nonneg`
- **Type**: `(z : 𝓞 K) → 0 ≤ Algebra.norm ℤ z`
- **How**: write `z = x+yθ`, `nlinarith`.
- **Uses from project**: [`K`, `exists_eq_smul_one_add_smul_theta`, `intNorm_eq_normForm`]
- **Visibility**: public
- **Lines**: 521-524
- **Notes**: KEY (irreducibility/non-principality).

### `theorem isUnit_iff_intNorm_eq_one`
- **Type**: `(z : 𝓞 K) → IsUnit z ↔ Algebra.norm ℤ z = 1`
- **Uses from project**: [`K`, `exists_eq_smul_one_add_smul_theta`, `isUnit_iff_normForm`, `intNorm_eq_normForm`]
- **Visibility**: public
- **Lines**: 526-529
- **Notes**: KEY.

### `theorem intNorm_ne_two / intNorm_ne_three / intNorm_ne_five`
- **Type**: `(z : 𝓞 K) → Algebra.norm ℤ z ≠ 2 / 3 / 5`
- **How**: `exists_eq_smul_one_add_smul_theta`, the `normForm_ne_*` lemmas.
- **Uses from project**: [`K`, `exists_eq_smul_one_add_smul_theta`, `intNorm_eq_normForm`, `normForm_ne_two/three/five`]
- **Visibility**: public
- **Lines**: 531-547
- **Notes**: KEY.

**File Summary (RingOfIntegers.lean)**: ~40 decls (8 defs incl. private, ~30 theorems, 2 abbrevs). Key API: `thetaInt`, `thetaInt_sq`, `concreteIntegralBasis`, `exists_eq_smul_one_add_smul_theta`, `linearIndependent_one_theta`, `intNorm_eq_normForm`, `isUnit_iff_intNorm_eq_one`, `intNorm_nonneg`, `numberField_discr_eq`, `intNorm_ne_two/three/five`. Main public: `ringOfIntegers_eq`, `numberField_discr_eq`. No sorry, no set_option. Proofs >30 lines: `integralClosure_eq_adjoin`, `sqrtNegSixExplicitIntegralBasis_discr`.

---

## Discriminant.lean

Empty (only namespace skeleton; discriminant results live in RingOfIntegers). **0 decls.**

---

## PrimeSplitting.lean

### `private theorem absNorm_span_natCast`
- **Type**: `(p : ℕ) → Ideal.absNorm (span {(p:𝓞 K)}) = p ^ 2`
- **How**: `intNorm_eq_normForm p 0`, `absNorm_span_singleton`.
- **Uses from project**: [`K`, `thetaInt`, `intNorm_eq_normForm`]
- **Visibility**: private
- **Lines**: 35-43
- **Notes**: KEY (used in ramified_iff, split machinery).

### `private theorem unit_theta_coeff_not_mem`
- **Type**: `(p : ℕ) (hp : 2 ≤ p) (A B : ℤ) (hB : B = ±1) → (A) + (B)·θ ∉ span {(p)}`
- **What**: an element with `θ`-coefficient `±1` is never divisible by `p`.
- **How**: `linearIndependent_one_theta` extracts coefficient, `Int.le_of_dvd`.
- **Uses from project**: [`K`, `thetaInt`, `exists_eq_smul_one_add_smul_theta`, `linearIndependent_one_theta`]
- **Visibility**: private
- **Lines**: 46-69
- **Notes**: KEY internal helper (norm-`p` lemmas).

### `private theorem isSquare_neg_six_iff_mod_twentyfour`
- **Type**: `(p prime, ≠2,≠3) → IsSquare ((-6):ZMod p) ↔ p%24 ∈ {1,5,7,11}`
- **How**: `jacobiSym.mod_right`, `ZMod.nonsquare_iff_jacobiSym_eq_neg_one`, `ZMod.isSquare_of_jacobiSym_eq_one`; omega case split mod 24.
- **Uses from project**: []
- **Visibility**: private
- **Lines**: 71-111
- **Notes**: proof >30 lines. KEY for splitting/inert laws.

### `def primeAboveTwo`
- **Type**: `Ideal (𝓞 K) := span {2, thetaInt}`
- **Uses from project**: [`K`, `thetaInt`]
- **Visibility**: public
- **Lines**: 115
- **Notes**: KEY (the nontrivial ideal class generator).

### `def primeAboveThree`
- **Type**: `Ideal (𝓞 K) := span {3, thetaInt}`
- **Uses from project**: [`K`, `thetaInt`]
- **Visibility**: public
- **Lines**: 118

### `theorem span_two_eq`
- **Type**: `span {2} = primeAboveTwo ^ 2`
- **What**: `2` is ramified.
- **How**: `span_pair_mul_span_pair`, `le_antisymm`, `thetaInt_sq`.
- **Uses from project**: [`K`, `primeAboveTwo`, `thetaInt`, `thetaInt_sq`]
- **Visibility**: public
- **Lines**: 121-146
- **Notes**: KEY.

### `theorem isPrime_primeAboveTwo`
- **Type**: `primeAboveTwo.IsPrime`
- **How**: `Ideal.isPrime_of_irreducible_absNorm`, norm `=2`.
- **Uses from project**: [`primeAboveTwo`, `intNorm_eq_normForm`, `thetaInt`, `span_two_eq`]
- **Visibility**: public
- **Lines**: 149-161
- **Notes**: KEY.

### `theorem absNorm_primeAboveTwo`
- **Type**: `Ideal.absNorm primeAboveTwo = 2`
- **Uses from project**: [`primeAboveTwo`, `intNorm_eq_normForm`, `thetaInt`, `span_two_eq`]
- **Visibility**: public
- **Lines**: 164-172
- **Notes**: KEY (used 10+×).

### `theorem liesOver_primeAboveTwo`
- **Type**: `primeAboveTwo.LiesOver (span {(2:ℤ)})`
- **Uses from project**: [`primeAboveTwo`, `isPrime_primeAboveTwo`]
- **Visibility**: public
- **Lines**: 175-180

### `theorem inertiaDeg_primeAboveTwo`
- **Type**: `(span {2:ℤ}).inertiaDeg primeAboveTwo = 1`
- **How**: `absNorm_eq_pow_inertiaDeg'`, `Nat.Prime.pow_eq_iff`.
- **Uses from project**: [`primeAboveTwo`, `liesOver_primeAboveTwo`, `absNorm_primeAboveTwo`]
- **Visibility**: public
- **Lines**: 183-188

### `theorem ramificationIdx_primeAboveTwo`
- **Type**: `(span {2:ℤ}).ramificationIdx primeAboveTwo = 2`
- **How**: `ramificationIdx_spec`, `span_two_eq`, norm-divisibility bound.
- **Uses from project**: [`primeAboveTwo`, `span_two_eq`, `intNorm_eq_normForm`, `thetaInt`, `absNorm_primeAboveTwo`]
- **Visibility**: public
- **Lines**: 191-211

### `theorem not_isPrincipal_primeAboveTwo`
- **Type**: `¬ Submodule.IsPrincipal primeAboveTwo`
- **What**: `(2,θ)` is non-principal (no element of norm 2).
- **How**: generator would have norm `±2`, `normForm_ne_two`.
- **Uses from project**: [`primeAboveTwo`, `absNorm_primeAboveTwo`, `exists_eq_smul_one_add_smul_theta`, `intNorm_eq_normForm`, `normForm_ne_two`]
- **Visibility**: public
- **Lines**: 215-230
- **Notes**: KEY (class number, Euclidean, ClassGroup).

### `theorem span_three_eq`
- **Type**: `span {3} = primeAboveThree ^ 2`
- **Uses from project**: [`K`, `primeAboveThree`, `thetaInt`, `thetaInt_sq`]
- **Visibility**: public
- **Lines**: 233-256

### `theorem isPrime_primeAboveThree`
- **Type**: `primeAboveThree.IsPrime`
- **Uses from project**: [`primeAboveThree`, `intNorm_eq_normForm`, `thetaInt`, `span_three_eq`]
- **Visibility**: public
- **Lines**: 260-272

### `theorem absNorm_primeAboveThree`
- **Type**: `Ideal.absNorm primeAboveThree = 3`
- **Uses from project**: [`primeAboveThree`, `intNorm_eq_normForm`, `thetaInt`, `span_three_eq`]
- **Visibility**: public
- **Lines**: 274-282
- **Notes**: KEY.

### `theorem liesOver_primeAboveThree`
- **Type**: `primeAboveThree.LiesOver (span {(3:ℤ)})`
- **Uses from project**: [`primeAboveThree`, `isPrime_primeAboveThree`]
- **Visibility**: public
- **Lines**: 285-290

### `theorem inertiaDeg_primeAboveThree`
- **Type**: `... .inertiaDeg primeAboveThree = 1`
- **Uses from project**: [`primeAboveThree`, `liesOver_primeAboveThree`, `absNorm_primeAboveThree`]
- **Visibility**: public
- **Lines**: 293-298

### `theorem ramificationIdx_primeAboveThree`
- **Type**: `... .ramificationIdx primeAboveThree = 2`
- **Uses from project**: [`primeAboveThree`, `span_three_eq`, `intNorm_eq_normForm`, `thetaInt`, `absNorm_primeAboveThree`]
- **Visibility**: public
- **Lines**: 301-321

### `theorem span_theta_eq`
- **Type**: `span {thetaInt} = primeAboveTwo * primeAboveThree`
- **What**: `(θ) = (2,θ)(3,θ)` (principal product of the two ramified primes).
- **Uses from project**: [`primeAboveTwo`, `primeAboveThree`, `thetaInt`, `thetaInt_sq`]
- **Visibility**: public
- **Lines**: 324-350
- **Notes**: KEY (used in ClassGroup to identify the two classes).

### `theorem ideal_eq_primeAboveTwo_of_absNorm_eq_two`
- **Type**: `(I) → absNorm I = 2 → I = primeAboveTwo`
- **How**: `isPrime_of_irreducible_absNorm`, membership of 2 and θ (θ²=−6≡0), `eq_of_le_of_absNorm_eq` (Common).
- **Uses from project**: [`K`, `primeAboveTwo`, `thetaInt`, `thetaInt_sq`, `absNorm_primeAboveTwo`, **Common** `eq_of_le_of_absNorm_eq`]
- **Visibility**: public
- **Lines**: 352-389
- **Notes**: proof >30 lines. KEY (class group representatives).

### `theorem ideal_eq_primeAboveThree_of_absNorm_eq_three`
- **Type**: `(I) → absNorm I = 3 → I = primeAboveThree`
- **Uses from project**: [`K`, `primeAboveThree`, `thetaInt`, `thetaInt_sq`, `absNorm_primeAboveThree`, **Common** `eq_of_le_of_absNorm_eq`]
- **Visibility**: public
- **Lines**: 391-428
- **Notes**: proof >30 lines. KEY.

### `theorem seven_eq_mul`
- **Type**: `(7:𝓞 K) = (1+thetaInt)(1-thetaInt)`
- **Uses from project**: [`K`, `thetaInt`, `thetaInt_sq`]
- **Visibility**: public
- **Lines**: 431-432

### `theorem span_seven_eq`
- **Type**: `span {7} = span {1+θ} * span {1-θ}` (7 splits, principal factors)
- **Uses from project**: [`thetaInt`, `seven_eq_mul`]
- **Visibility**: public
- **Lines**: 436-438

### `theorem absNorm_span_one_add_theta`
- **Type**: `absNorm (span {1+θ}) = 7`
- **Uses from project**: [`thetaInt`, `intNorm_eq_normForm`]
- **Visibility**: public
- **Lines**: 441-446

### `theorem isPrime_span_one_add_theta`
- **Type**: `(span {1+θ}).IsPrime`
- **Uses from project**: [`thetaInt`, `absNorm_span_one_add_theta`]
- **Visibility**: public
- **Lines**: 448-451

### `theorem absNorm_span_one_sub_theta`
- **Type**: `absNorm (span {1-θ}) = 7`
- **Uses from project**: [`thetaInt`, `intNorm_eq_normForm`]
- **Visibility**: public
- **Lines**: 454-463

### `theorem isPrime_span_one_sub_theta`
- **Type**: `(span {1-θ}).IsPrime`
- **Uses from project**: [`thetaInt`, `absNorm_span_one_sub_theta`]
- **Visibility**: public
- **Lines**: 466-469

### `theorem liesOver_span_one_add_theta / _sub_theta`
- **Type**: lies over `(7:ℤ)`
- **Uses from project**: [`thetaInt`, `isPrime_span_one_add/sub_theta`, `seven_eq_mul`]
- **Visibility**: public
- **Lines**: 472-491

### `theorem inertiaDeg_span_one_add_theta / _sub_theta`
- **Type**: inertia degree over 7 is `1`
- **Uses from project**: [`thetaInt`, `liesOver_span_one_add/sub_theta`, `absNorm_span_one_add/sub_theta`]
- **Visibility**: public
- **Lines**: 494-511

### `def primeAboveFiveSubTwo / primeAboveFiveAddTwo`
- **Type**: `Ideal (𝓞 K) := span {5, thetaInt ∓ 2}`
- **What**: non-principal primes above 5.
- **Uses from project**: [`K`, `thetaInt`]
- **Visibility**: public
- **Lines**: 516-519

### `theorem span_five_eq`
- **Type**: `span {5} = span {5,θ-2} * span {5,θ+2}`
- **Uses from project**: [`thetaInt`, `thetaInt_sq`]
- **Visibility**: public
- **Lines**: 521-548

### `private theorem span_five_theta_sub_two_ne_top / _add_two_ne_top`
- **Type**: `span {5, θ∓2} ≠ ⊤`
- **How**: `mem_span_pair`, `linearIndependent_one_theta`, `5 ∤ 1`.
- **Uses from project**: [`thetaInt`, `exists_eq_smul_one_add_smul_theta`, `linearIndependent_one_theta`, `thetaInt_sq`]
- **Visibility**: private
- **Lines**: 550-603

### `theorem absNorm_primeAboveFiveSubTwo / _AddTwo`
- **Type**: `absNorm primeAboveFive... = 5`
- **How**: divisor of `25`, `≠1` (proper) and `≠25` (via `unit_theta_coeff_not_mem` + `eq_of_le_of_absNorm_eq`).
- **Uses from project**: [`primeAboveFive*`, `absNorm_span_natCast`, `unit_theta_coeff_not_mem`, `thetaInt`, `span_five_theta_*_ne_top`, **Common** `eq_of_le_of_absNorm_eq`]
- **Visibility**: public
- **Lines**: 606-665
- **Notes**: each >30 lines.

### `theorem isPrime_primeAboveFiveSubTwo / _AddTwo`
- **Type**: prime
- **Uses from project**: [`primeAboveFive*`, `absNorm_primeAboveFive*`]
- **Visibility**: public
- **Lines**: 668-677

### `theorem liesOver_primeAboveFiveSubTwo / _AddTwo`
- **Type**: lies over `(5:ℤ)`
- **Uses from project**: [`primeAboveFive*`, `isPrime_primeAboveFive*`, `thetaInt`]
- **Visibility**: public
- **Lines**: 680-695

### `theorem inertiaDeg_primeAboveFiveSubTwo / _AddTwo`
- **Type**: inertia degree 1 over 5
- **Uses from project**: [`primeAboveFive*`, `liesOver_primeAboveFive*`, `absNorm_primeAboveFive*`]
- **Visibility**: public
- **Lines**: 698-715

### `private theorem intNorm_five / intNorm_theta_sub_two`
- **Type**: `norm ℤ 5 = 25`, `norm ℤ (θ-2) = 10`
- **Uses from project**: [`K`, `thetaInt`, `intNorm_eq_normForm`]
- **Visibility**: private
- **Lines**: 717-729

### `theorem not_isPrincipal_primeAboveFive`
- **Type**: `¬ IsPrincipal (span {5, thetaInt - 2})`
- **What**: `(5,θ-2)` non-principal (5 not represented by `x²+6y²`).
- **How**: generator divides 5 (norm 25) and θ-2 (norm 10); `intNorm_ne_five`, `interval_cases`.
- **Uses from project**: [`K`, `span_five_theta_sub_two_ne_top`, `intNorm_five`, `intNorm_theta_sub_two`, `intNorm_nonneg`, `isUnit_iff_intNorm_eq_one`, `intNorm_ne_five`, `thetaInt`]
- **Visibility**: public
- **Lines**: 732-779
- **Notes**: proof >30 lines.

### `private theorem absNorm_span_thirteen_aux`
- **Type**: `absNorm (span {13}) = 169`
- **Uses from project**: [`thetaInt`, `intNorm_eq_normForm`]
- **Visibility**: private
- **Lines**: 781-787

### `theorem isPrime_span_thirteen`
- **Type**: `(span {13}).IsPrime`
- **What**: `13` is inert (`-6` not square mod 13).
- **How**: maximal divisor of `169`; rules out norm-13 prime via `ZMod.ringEquivOfPrime` + `decide` (no root of `t²+6`).
- **Uses from project**: [`K`, `thetaInt`, `thetaInt_sq`, `absNorm_span_thirteen_aux`]
- **Visibility**: public
- **Lines**: 790-837
- **Notes**: proof >30 lines; uses `decide`.

### `theorem absNorm_span_thirteen`
- **Type**: `absNorm (span {13}) = 169`
- **Uses from project**: [`absNorm_span_thirteen_aux`]
- **Visibility**: public
- **Lines**: 839-841

### `theorem liesOver_span_thirteen`
- **Type**: lies over `(13:ℤ)`
- **Uses from project**: [`isPrime_span_thirteen`]
- **Visibility**: public
- **Lines**: 843-849

### `theorem inertiaDeg_span_thirteen`
- **Type**: inertia degree `2`
- **Uses from project**: [`liesOver_span_thirteen`, `absNorm_span_thirteen`]
- **Visibility**: public
- **Lines**: 851-861

### `private theorem mod_twentyfour_of_splits`
- **Type**: `(p prime,≠2,≠3, p splits) → p%24 ∈ {1,5,7,11}`
- **How**: norm factorisation `=p` via `left_eq_prime_of_mul_eq_prime_sq_of_ne_one` (Common); `ZMod.ringEquivOfPrime`, root of `t²+6`, `isSquare_neg_six_iff_mod_twentyfour`.
- **Uses from project**: [`K`, `thetaInt`, `thetaInt_sq`, `absNorm_span_natCast`, `isSquare_neg_six_iff_mod_twentyfour`, **Common** `left_eq_prime_of_mul_eq_prime_sq_of_ne_one`]
- **Visibility**: private
- **Lines**: 863-901
- **Notes**: proof >30 lines.

### `private theorem exists_root_data`
- **Type**: `(p) (hs : -6 = s·s in ZMod p) → ∃ c d k₁ k₂, ...`
- **What**: produce integer representatives + divisibility data for the two roots.
- **How**: `ZMod.natCast_rightInverse`, `intCast_zmod_eq_zero_iff_dvd`, `linear_combination`.
- **Uses from project**: [`K`, `thetaInt`, `thetaInt_sq`]
- **Visibility**: private
- **Lines**: 903-939

### `private theorem absNorm_span_pair_not_one`
- **Type**: `... → absNorm (span {p, θ-c}) ≠ 1`
- **Uses from project**: [`K`, `thetaInt`, `unit_theta_coeff_not_mem`]
- **Visibility**: private
- **Lines**: 941-966

### `private theorem absNorm_span_pair_ne_prime_sq`
- **Type**: `... → absNorm (span {p, θ-c}) ≠ p²`
- **Uses from project**: [`K`, `thetaInt`, `absNorm_span_natCast`, `unit_theta_coeff_not_mem`, **Common** `eq_of_le_of_absNorm_eq`]
- **Visibility**: private
- **Lines**: 968-983

### `private theorem absNorm_span_pair_eq_prime`
- **Type**: `... → absNorm (span {p, θ-c}) = p`
- **How**: `eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq` (Common) + the two helpers above.
- **Uses from project**: [`K`, `thetaInt`, `absNorm_span_natCast`, `absNorm_span_pair_not_one`, `absNorm_span_pair_ne_prime_sq`, **Common** `eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq`]
- **Visibility**: private
- **Lines**: 985-996

### `private theorem root_ne_neg_of_square_neg_six`
- **Type**: `(p prime,≠2,≠3, -6=s·s) → s ≠ -s`
- **How**: else `2s=0 ⇒ s=0 ⇒ p∣6`, contradiction.
- **Uses from project**: []
- **Visibility**: private
- **Lines**: 998-1021

### `private theorem span_pair_ne_of_roots_ne`
- **Type**: distinct roots ⇒ the two prime ideals differ
- **How**: `exists_int_inverse_mod_prime` (Common) yields `1 ∈` ideal if equal.
- **Uses from project**: [`K`, `thetaInt`, **Common** `exists_int_inverse_mod_prime`]
- **Visibility**: private
- **Lines**: 1023-1052

### `private theorem span_pair_mul_eq_span_natCast`
- **Type**: `span {p} = span {p,θ-c} * span {p,θ-d}`
- **Uses from project**: [`K`, `thetaInt`, `absNorm_span_natCast`, **Common** `eq_of_le_of_absNorm_eq`]
- **Visibility**: private
- **Lines**: 1054-1082

### `private theorem splits_of_square_neg_six`
- **Type**: `(p,≠2,≠3, -6 square) → ∃ P Q distinct primes, span {p}=P·Q`
- **How**: assembles `exists_root_data`, `absNorm_span_pair_eq_prime`, `span_pair_ne_of_roots_ne`, `span_pair_mul_eq_span_natCast`.
- **Uses from project**: [`K`, `thetaInt`, `exists_root_data`, `absNorm_span_pair_eq_prime`, `root_ne_neg_of_square_neg_six`, `span_pair_ne_of_roots_ne`, `span_pair_mul_eq_span_natCast`]
- **Visibility**: private
- **Lines**: 1084-1122
- **Notes**: proof >30 lines.

### `theorem splits_iff_mod_twentyfour`
- **Type**: `(p,≠2,≠3) → (p splits into 2 distinct primes) ↔ p%24 ∈ {1,5,7,11}`
- **What**: **splitting law** (main result).
- **How**: forward `mod_twentyfour_of_splits`; backward `isSquare_neg_six_iff_mod_twentyfour` then `splits_of_square_neg_six`.
- **Uses from project**: [`K`, `mod_twentyfour_of_splits`, `isSquare_neg_six_iff_mod_twentyfour`, `splits_of_square_neg_six`]
- **Visibility**: public
- **Lines**: 1126-1136
- **Notes**: MAIN PUBLIC RESULT.

### `private theorem eq_two_or_eq_three_of_prime_dvd_twentyfour`
- **Type**: `(p prime, p∣24) → p=2 ∨ p=3`
- **Uses from project**: []
- **Visibility**: private
- **Lines**: 1138-1146
- **Notes**: GENERIC-looking (number-theoretic, no field data).

### `theorem ramified_iff`
- **Type**: `(p prime) → (∃ prime P, span {p} ≤ P²) ↔ p=2 ∨ p=3`
- **What**: **ramification law**: ramified iff `p ∣ disc = -24`.
- **How**: forward uses `not_isUnramifiedAt_of_...` + `not_map_span_natCast_le_pow_succ_of_...` (Common), `dvd_differentIdeal_iff`, `absNorm_differentIdeal`, `numberField_discr_eq`; backward `span_two_eq`/`span_three_eq`.
- **Uses from project**: [`K`, `absNorm_span_natCast`, `numberField_discr_eq`, `primeAboveTwo/Three`, `isPrime_primeAboveTwo/Three`, `span_two_eq`, `span_three_eq`, `eq_two_or_eq_three_of_prime_dvd_twentyfour`, **Common** `not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow`, `not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ`]
- **Visibility**: public
- **Lines**: 1150-1194
- **Notes**: proof >30 lines. MAIN PUBLIC RESULT.

### `theorem ramificationIdx_span_one_add_theta / _sub_theta / primeAboveFiveSubTwo / _AddTwo / span_thirteen`
- **Type**: ramification index `1` (unramified) for the 7-split, 5-split, 13-inert primes.
- **How**: `ramificationIdx_spec`; would-be `e≥2` contradicts `ramified_iff`.
- **Uses from project**: [respective `span_*`/`primeAbove*`, `isPrime_*`, `ramified_iff`]
- **Visibility**: public
- **Lines**: 1197-1272

### `abbrev sqrtNegSixPolynomialMod`
- **Type**: `(p:ℕ) → (ZMod p)[X] := X²+C 6`
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 1290-1291

### `private theorem sqrtNegSixPolynomialMod_isRoot_iff`
- **Type**: `IsRoot t ↔ t² = (-6:ZMod p)`
- **Uses from project**: [`sqrtNegSixPolynomialMod`]
- **Visibility**: private
- **Lines**: 1293-1301

### `private theorem sqrtNegSixPolynomialMod_natDegree`
- **Type**: `natDegree = 2`
- **Uses from project**: [`sqrtNegSixPolynomialMod`]
- **Visibility**: private
- **Lines**: 1303-1305

### `private theorem sqrtNegSixPolynomialMod_roots_eq_zero_iff_no_root`
- **Type**: `roots = 0 ↔ ¬∃ t, t²=(-6)`
- **Uses from project**: [`sqrtNegSixPolynomialMod`, `sqrtNegSixPolynomialMod_isRoot_iff`, `sqrtNegSixPolynomialMod_natDegree`]
- **Visibility**: private
- **Lines**: 1307-1328

### `private theorem sqrtNegSixPolynomialMod_no_root_iff_inert_mod_twentyfour`
- **Type**: `(p,≠2,≠3) → (¬∃t, t²=-6) ↔ p%24 ∈ {13,17,19,23}`
- **How**: `isSquare_neg_six_iff_mod_twentyfour`, omega.
- **Uses from project**: [`isSquare_neg_six_iff_mod_twentyfour`]
- **Visibility**: private
- **Lines**: 1330-1377
- **Notes**: proof >30 lines. (Kummer-Dedekind inert characterisation; not re-exported publicly.)

### `theorem absNorm_differentIdeal_eq_twentyFour`
- **Type**: `absNorm (differentIdeal ℤ (𝓞 K)) = 24`
- **How**: `NumberField.absNorm_differentIdeal`, `numberField_discr_eq`.
- **Uses from project**: [`K`, `numberField_discr_eq`]
- **Visibility**: public
- **Lines**: 1393-1396

### `theorem prime_dvd_differentIdeal_iff_eq_ramifiedPrime`
- **Type**: `(P prime, ≠⊥) → P ∣ differentIdeal ↔ P = primeAboveTwo ∨ P = primeAboveThree`
- **What**: the different is `(2,θ)(3,θ)` (ramified primes).
- **How**: norm `∣24`, `Nat.absNorm_under_prime`, `eq_two_or_eq_three_of_prime_dvd_twentyfour`, `IsPrime.le_of_pow_le`, `dvd_differentIdeal_iff`.
- **Uses from project**: [`K`, `absNorm_differentIdeal_eq_twentyFour`, `eq_two_or_eq_three_of_prime_dvd_twentyfour`, `primeAboveTwo/Three`, `span_two_eq`, `span_three_eq`, `absNorm_primeAboveTwo/Three`, `isPrime_primeAboveTwo/Three`, `liesOver_primeAboveTwo/Three`, `ramificationIdx_primeAboveTwo/Three`]
- **Visibility**: public
- **Lines**: 1398-1468
- **Notes**: proof >30 lines. MAIN PUBLIC RESULT.

**File Summary (PrimeSplitting.lean)**: ~60 decls (4 defs, 2 abbrevs, ~54 theorems). Heavy use of Common helpers. Key API: `primeAboveTwo`, `primeAboveThree`, `span_two_eq`, `span_three_eq`, `span_theta_eq`, `absNorm_primeAboveTwo/Three`, `isPrime_primeAboveTwo/Three`, `not_isPrincipal_primeAboveTwo`, `ideal_eq_primeAboveTwo/Three_of_absNorm_eq_*`, `absNorm_span_natCast`, `isSquare_neg_six_iff_mod_twentyfour`, `unit_theta_coeff_not_mem`. Main public: `splits_iff_mod_twentyfour`, `ramified_iff`, `prime_dvd_differentIdeal_iff_eq_ramifiedPrime`. No sorry, no set_option. Many proofs >30 lines (listed above). The 5/7/13 splitting lemmas are largely unused downstream (illustrative).

---

## ClassGroup.lean

### `abbrev thetaFractionalIdeal`
- **Type**: `FractionalIdeal (𝓞 K)⁰ K := spanSingleton ... θ`
- **Uses from project**: [`K`, `θ`]
- **Visibility**: public
- **Lines**: 31-32

### `abbrev primeAboveTwoFractionalIdeal / primeAboveThreeFractionalIdeal`
- **Type**: coercions of `primeAboveTwo/Three` to fractional ideals.
- **Uses from project**: [`primeAboveTwo`, `primeAboveThree`, `K`]
- **Visibility**: public
- **Lines**: 34-38

### `theorem theta_mem_fractionalIdeal`
- **Type**: `θ ∈ thetaFractionalIdeal`
- **Uses from project**: [`thetaFractionalIdeal`, `θ`, `K`]
- **Visibility**: public
- **Lines**: 40-42

### `theorem thetaFractionalIdeal_absNorm`
- **Type**: `absNorm thetaFractionalIdeal = |Algebra.norm ℚ θ|`
- **Uses from project**: [`thetaFractionalIdeal`, `θ`]
- **Visibility**: public
- **Lines**: 44-46

### `theorem ramifiedFractionalIdeals_ne_zero`
- **Type**: `primeAboveTwoFractionalIdeal ≠ 0 ∧ primeAboveThreeFractionalIdeal ≠ 0`
- **Uses from project**: [`primeAboveTwoFractionalIdeal`, `primeAboveThreeFractionalIdeal`, `absNorm_primeAboveTwo`, `absNorm_primeAboveThree`]
- **Visibility**: public
- **Lines**: 48-60

### `noncomputable def ramifiedIdealOverTwo`
- **Type**: `(Ideal (𝓞 K))⁰ := ⟨primeAboveTwo, ...⟩`
- **What**: nontrivial class representative.
- **Uses from project**: [`K`, `primeAboveTwo`, `absNorm_primeAboveTwo`]
- **Visibility**: public
- **Lines**: 78-82
- **Notes**: KEY.

### `noncomputable def ramifiedIdealOverThree`
- **Type**: `(Ideal (𝓞 K))⁰ := ⟨primeAboveThree, ...⟩`
- **Uses from project**: [`K`, `primeAboveThree`, `absNorm_primeAboveThree`]
- **Visibility**: public
- **Lines**: 86-90

### `abbrev unitIdealRepresentative`
- **Type**: `(Ideal (𝓞 K))⁰ := ⟨⊤, ...⟩`
- **Uses from project**: [`K`]
- **Visibility**: public
- **Lines**: 93

### `private theorem thetaInt_ne_zero`
- **Type**: `thetaInt ≠ 0`
- **Uses from project**: [`thetaInt`, `θ`, `theta_sq`]
- **Visibility**: private
- **Lines**: 95-100
- **Notes**: GENERIC-looking; could live in RingOfIntegers.

### `private theorem minkowskiBound_lt_four`
- **Type**: Minkowski-bound expression `< 4`
- **What**: `(2/π)√24 ≈ 3.12 < 4`.
- **How**: rewrite places/disc, `Real.sqrt_lt_sqrt`, `Real.pi_gt_three`, nlinarith.
- **Uses from project**: [`K`, `nrRealPlaces_eq_zero`, `degree_eq_two`, `numberField_discr_eq`]
- **Visibility**: private
- **Lines**: 102-123
- **Notes**: proof >20 lines.

### `theorem classGroup_mk0_ramified_ne_one`
- **Type**: `ClassGroup.mk0 ramifiedIdealOverTwo ≠ 1`
- **How**: `mk0_eq_one_iff` ⇒ principal, contradicts `not_isPrincipal_primeAboveTwo`.
- **Uses from project**: [`ramifiedIdealOverTwo`, `not_isPrincipal_primeAboveTwo`]
- **Visibility**: public
- **Lines**: 126-132
- **Notes**: KEY.

### `theorem classGroup_mk0_ramified_sq_eq_one`
- **Type**: `(ClassGroup.mk0 ramifiedIdealOverTwo) ^ 2 = 1`
- **How**: `mk0_eq_mk0_inv_iff` via `(2,θ)²=(2)` (`span_two_eq`); self-inverse.
- **Uses from project**: [`ramifiedIdealOverTwo`, `span_two_eq`]
- **Visibility**: public
- **Lines**: 135-144

### `theorem orderOf_classGroup_mk0_ramified`
- **Type**: `orderOf (ClassGroup.mk0 ramifiedIdealOverTwo) = 2`
- **How**: `orderOf_eq_prime`.
- **Uses from project**: [`ramifiedIdealOverTwo`, `classGroup_mk0_ramified_sq_eq_one`, `classGroup_mk0_ramified_ne_one`]
- **Visibility**: public
- **Lines**: 147-151

### `theorem class_mk0_primeAboveThree_eq_ramified`
- **Type**: `mk0 ramifiedIdealOverThree = mk0 ramifiedIdealOverTwo`
- **How**: both self-inverse / `(θ)=(2,θ)(3,θ)` principal (`span_theta_eq`).
- **Uses from project**: [`ramifiedIdealOverTwo`, `ramifiedIdealOverThree`, `span_two_eq`, `span_theta_eq`, `thetaInt`, `thetaInt_ne_zero`]
- **Visibility**: public
- **Lines**: 154-170

### `private theorem classGroupRepresentatives_aux`
- **Type**: `(C) → C = 1 ∨ C = mk0 ramifiedIdealOverTwo`
- **How**: `exists_ideal_in_class_of_norm_le`, `minkowskiBound_lt_four` ⇒ norm ≤3; `ideal_eq_primeAboveTwo/Three_of_absNorm_eq_*`.
- **Uses from project**: [`K`, `minkowskiBound_lt_four`, `ramifiedIdealOverTwo/Three`, `ideal_eq_primeAboveTwo_of_absNorm_eq_two`, `ideal_eq_primeAboveThree_of_absNorm_eq_three`, `primeAboveTwo/Three`, `class_mk0_primeAboveThree_eq_ramified`]
- **Visibility**: private
- **Lines**: 172-207
- **Notes**: proof >30 lines.

### `theorem classNumber_eq_two`
- **Type**: `NumberField.classNumber K = 2`
- **What**: **class number = 2** (main result).
- **How**: `Nat.card_eq_two_iff` from `1` and `mk0 ramifiedIdealOverTwo`, exhaustiveness `classGroupRepresentatives_aux`.
- **Uses from project**: [`K`, `ramifiedIdealOverTwo`, `classGroup_mk0_ramified_ne_one`, `classGroupRepresentatives_aux`]
- **Visibility**: public
- **Lines**: 209-221
- **Notes**: MAIN PUBLIC RESULT.

### `theorem classGroupStructure`
- **Type**: `Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 2))`
- **What**: **class group ≅ ℤ/2** (main result).
- **How**: `classNumber_eq_two`, `mulEquivOfPrimeCardEq`.
- **Uses from project**: [`K`, `classNumber_eq_two`]
- **Visibility**: public
- **Lines**: 223-229
- **Notes**: MAIN PUBLIC RESULT.

### `theorem classGroup_mk0_ramified_ne`
- **Type**: `mk0 ramifiedIdealOverTwo ≠ mk0 unitIdealRepresentative`
- **Uses from project**: [`ramifiedIdealOverTwo`, `unitIdealRepresentative`, `not_isPrincipal_primeAboveTwo`]
- **Visibility**: public
- **Lines**: 231-240

### `theorem classGroupRepresentatives`
- **Type**: `(C) → C = mk0 unitIdealRepresentative ∨ C = mk0 ramifiedIdealOverTwo`
- **How**: `Nat.card_eq_two_iff'` + `classGroup_mk0_ramified_ne`.
- **Uses from project**: [`K`, `classNumber_eq_two`, `unitIdealRepresentative`, `ramifiedIdealOverTwo`, `classGroup_mk0_ramified_ne`]
- **Visibility**: public
- **Lines**: 242-253

**File Summary (ClassGroup.lean)**: ~18 decls (2 defs, ~13 theorems, 4 abbrevs). Key API: `ramifiedIdealOverTwo`, `classNumber_eq_two`, `classGroup_mk0_ramified_ne_one`. Main public: `classNumber_eq_two`, `classGroupStructure`, `classGroupRepresentatives`. No sorry, no set_option. Proofs >30 lines: `classGroupRepresentatives_aux`. The fractional-ideal abbrevs (`thetaFractionalIdeal`, etc.) are illustrative, unused downstream.

---

## Units.lean

### `abbrev torsionGenerator`
- **Type**: `(𝓞 K)ˣ := -1`
- **Uses from project**: [`K`]
- **Visibility**: public
- **Lines**: 34
- **Notes**: KEY (used in LocalGlobal too).

### `def torsionUnits`
- **Type**: `Set ((𝓞 K)ˣ) := {u | ∃ k : Fin 2, u = torsionGenerator ^ k.val}`
- **Uses from project**: [`K`, `torsionGenerator`]
- **Visibility**: public
- **Lines**: 37

### `theorem torsionUnits_eq`
- **Type**: `{u | IsOfFinOrder u} = torsionUnits`
- **What**: torsion subgroup `= {±1}`.
- **How**: a unit has `x²+6y²=1` ⇒ `(±1,0)` via `isUnit_iff_normForm`; converse `(-1)²=1`.
- **Uses from project**: [`K`, `exists_eq_smul_one_add_smul_theta`, `thetaInt`, `isUnit_iff_normForm`, `torsionGenerator`, `torsionUnits`]
- **Visibility**: public
- **Lines**: 41-68
- **Notes**: KEY; proof >20 lines.

### `theorem torsionOrder_eq_two`
- **Type**: `NumberField.Units.torsionOrder K = 2`
- **How**: `Nat.card_eq_two_iff` from `1`,`-1`; `torsionUnits_eq` for exhaustiveness.
- **Uses from project**: [`K`, `torsionUnits_eq`]
- **Visibility**: public
- **Lines**: 71-96
- **Notes**: proof >20 lines.

### `theorem unitRank_eq_zero`
- **Type**: `NumberField.Units.rank K = 0`
- **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces`, the place counts.
- **Uses from project**: [`K`, `nrRealPlaces_eq_zero`, `nrComplexPlaces_eq_one`]
- **Visibility**: public
- **Lines**: 100-102
- **Notes**: KEY.

### `theorem unit_eq_one_or_neg_one`
- **Type**: `(u : (𝓞 K)ˣ) → u = 1 ∨ u = -1`
- **How**: `exist_unique_eq_mul_prod` + `unitRank_eq_zero` ⇒ torsion; `torsionUnits_eq`.
- **Uses from project**: [`K`, `unitRank_eq_zero`, `torsionUnits_eq`, `torsionGenerator`]
- **Visibility**: public
- **Lines**: 105-123
- **Notes**: KEY.

### `theorem unitGroupStructure`
- **Type**: `Nonempty ((𝓞 K)ˣ ≃* Multiplicative (ZMod 2))`
- **What**: **unit group ≅ ℤ/2** (= μ₂).
- **How**: `Nat.card_eq_two_iff`, `unit_eq_one_or_neg_one`, `mulEquivOfPrimeCardEq`.
- **Uses from project**: [`K`, `unit_eq_one_or_neg_one`]
- **Visibility**: public
- **Lines**: 126-140
- **Notes**: MAIN PUBLIC RESULT.

### `theorem regulator_eq_one`
- **Type**: `NumberField.Units.regulator K = 1`
- **What**: regulator = 1 (empty determinant).
- **How**: `regulator_eq_det'`, `Matrix.det_eq_one_of_card_eq_zero` (rank 0).
- **Uses from project**: [`K`, `unitRank_eq_zero`]
- **Visibility**: public
- **Lines**: 143-158
- **Notes**: MAIN PUBLIC RESULT. (Note: NOT blocked here, unlike the real-quadratic twins.)

**File Summary (Units.lean)**: 8 decls (1 def, 1 abbrev, 6 theorems). Key API: `torsionUnits_eq`, `unitRank_eq_zero`, `unit_eq_one_or_neg_one`, `torsionGenerator`. Main public: `torsionOrder_eq_two`, `unitGroupStructure`, `regulator_eq_one`. No sorry, no set_option, no proof >30 lines.

---

## Euclidean.lean

### `theorem not_isPrincipalIdealRing`
- **Type**: `¬ IsPrincipalIdealRing (𝓞 K)`
- **What**: `ℤ[√-6]` is not a PID.
- **How**: PID would make `primeAboveTwo` principal, contradicts `not_isPrincipal_primeAboveTwo`.
- **Uses from project**: [`K`, `not_isPrincipal_primeAboveTwo`, `primeAboveTwo`]
- **Visibility**: public
- **Lines**: 33-35
- **Notes**: MAIN PUBLIC RESULT (used by UniqueFactorization).

### `theorem not_normEuclidean`
- **Type**: `¬ ∀ a b, b≠0 → ∃ q r, a = b*q+r ∧ |N r| < |N b|`
- **What**: `ℤ[√-6]` is not norm-Euclidean.
- **How**: take `a=θ`, `b=2`: any remainder `r=θ-2q` has norm `(-2x)²+6(1-2y)² ≥ 4 = N(2)`; `nlinarith`.
- **Uses from project**: [`K`, `thetaInt`, `intNorm_eq_normForm`, `exists_eq_smul_one_add_smul_theta`]
- **Visibility**: public
- **Lines**: 38-79
- **Notes**: MAIN PUBLIC RESULT; proof >30 lines.

**File Summary (Euclidean.lean)**: 2 theorems. Both main public results. No sorry, no set_option. `not_normEuclidean` >30 lines.

---

## LocalGlobal.lean

### `def heightOneTwo / heightOneThree`
- **Type**: `HeightOneSpectrum (𝓞 K)` over `primeAboveTwo/Three`.
- **Uses from project**: [`primeAboveTwo/Three`, `isPrime_primeAboveTwo/Three`, `absNorm_primeAboveTwo/Three`, `K`]
- **Visibility**: public
- **Lines**: 35-54

### `abbrev vTwo / vThree`
- **Type**: `NumberField.FinitePlace K := FinitePlace.mk heightOne...`
- **Uses from project**: [`heightOneTwo/Three`, `K`]
- **Visibility**: public
- **Lines**: 56-60

### `example`s (×11)
- ramificationIdx/inertiaDeg of `heightOne*` (lines 62-76), `InfiniteCompletion ≃+* ℂ` (111-114), product formula (128-146), infinite-adele norm/dense (168-174), fundamentalCone measurability (225-231), house positivity (249-256), zeta positivity/def (316-327). These are unnamed `example`s exercising mathlib API against the field; each cites the matching project lemma (`ramificationIdx_primeAboveTwo`, `infinitePlace_isComplex`, `theta_sq`, `torsionGenerator`, etc.).

### `abbrev CompletionAtTwo / CompletionAtThree`
- **Type**: `heightOne....adicCompletion K`
- **Uses from project**: [`heightOneTwo/Three`, `K`]
- **Visibility**: public
- **Lines**: 90-95

### `abbrev InfiniteCompletion`
- **Type**: `(v : InfinitePlace K) → Type := v.Completion`
- **Uses from project**: [`K`]
- **Visibility**: public
- **Lines**: 108-109

### `abbrev SqrtNegSixInfiniteAdeleRing`, `infinitePrincipalAdele_theta`, `infinitePrincipalAdele_torsionGenerator`
- **Type**: infinite adele ring and principal adeles of `θ`, `-1`.
- **Uses from project**: [`K`, `θ`, `torsionGenerator`]
- **Visibility**: public
- **Lines**: 159-166

### `theorem canonicalEmbedding_thetaInt_mem_integerLattice`
- **Type**: `canonicalEmbedding K (algebraMap (𝓞 K) K thetaInt) ∈ integerLattice K`
- **Uses from project**: [`K`, `thetaInt`]
- **Visibility**: public
- **Lines**: 188-191

### `abbrev mixedEmbedding_theta`
- **Type**: `mixedEmbedding.mixedSpace K := mixedEmbedding K θ`
- **Uses from project**: [`K`, `θ`]
- **Visibility**: public
- **Lines**: 207

### `theorem mixedEmbedding_theta_mem_convexBodyLT`
- **Type**: `(f) (hf : ∀ w, w θ < f w) → mixedEmbedding_theta ∈ convexBodyLT K f`
- **How**: unfold convexBodyLT membership; totally complex ⇒ real component vacuous (`infinitePlace_isComplex`), complex via `norm_embedding_eq`.
- **Uses from project**: [`K`, `mixedEmbedding_theta`, `infinitePlace_isComplex`, `θ`]
- **Visibility**: public
- **Lines**: 210-223

### `theorem polarSpace_nonempty`
- **Type**: `Nonempty (mixedEmbedding.polarSpace K)`
- **Uses from project**: [`K`]
- **Visibility**: public
- **Lines**: 233-235

### `theorem house_torsionGenerator`
- **Type**: `NumberField.house (algebraMap (𝓞 K) K (-1)) = 1`
- **Uses from project**: [`K`, `torsionGenerator`]
- **Visibility**: public
- **Lines**: 258-260

### `abbrev SqrtNegSixAdeleRing`, `principalAdele_theta`, `principalAdele_torsionGenerator`
- **Type**: adele ring and principal adeles.
- **Uses from project**: [`K`, `θ`, `torsionGenerator`]
- **Visibility**: public
- **Lines**: 275-282

### `theorem principalAdele_theta_ne_zero`
- **Type**: `principalAdele_theta ≠ 0`
- **Uses from project**: [`principalAdele_theta`, `K`, `θ`, `theta_sq`]
- **Visibility**: public
- **Lines**: 284-290

### `theorem principalAdele_torsionGenerator_is_unit_everywhere`
- **Type**: `∀ v : FinitePlace K, v (algebraMap (𝓞 K) K (-1)) = 1`
- **Uses from project**: [`K`, `torsionGenerator`]
- **Visibility**: public
- **Lines**: 292-296

### `abbrev sqrtNegSixDedekindZeta / sqrtNegSixDedekindZetaResidue`
- **Type**: `dedekindZeta K s` / `dedekindZeta_residue K`
- **Uses from project**: [`K`]
- **Visibility**: public
- **Lines**: 310-314

**File Summary (LocalGlobal.lean)**: ~25 named decls (2 defs, ~6 theorems, ~16 abbrevs) plus 11 unnamed `example`s. Mostly thin wrappers/illustrations of mathlib local-global API specialised to `K`; nothing re-used downstream (terminal file). Key project deps: `primeAboveTwo/Three`, `isPrime_*`, `infinitePlace_isComplex`, `theta_sq`, `torsionGenerator`. No sorry, no set_option, no proof >30 lines.

---

## CMField.lean

### `theorem isCMField`
- **Type**: `NumberField.IsCMField K`
- **How**: `IsTotallyComplex` (from Embeddings) + `IsCMField.ofCMExtension`.
- **Uses from project**: [`K`, `isTotallyComplex`]
- **Visibility**: public
- **Lines**: 26-28
- **Notes**: MAIN PUBLIC RESULT.

### `theorem cmField_isTotallyComplex`
- **Type**: `NumberField.IsTotallyComplex K`
- **How**: `isTotallyComplex`.
- **Uses from project**: [`K`, `isTotallyComplex`]
- **Visibility**: public
- **Lines**: 30-31

### `theorem cmField_quadratic_over_maximalRealSubfield`
- **Type**: `Algebra.IsQuadraticExtension (maximalRealSubfield K) K`
- **How**: `isCMField` + `IsCMField.isQuadraticExtension`.
- **Uses from project**: [`K`, `isCMField`]
- **Visibility**: public
- **Lines**: 33-36

### `theorem cmField_unitsRank_eq_maximalRealSubfield`
- **Type**: `Units.rank (maximalRealSubfield K) = Units.rank K`
- **How**: `isCMField` + `IsCMField.units_rank_eq_units_rank`.
- **Uses from project**: [`K`, `isCMField`]
- **Visibility**: public
- **Lines**: 38-42

**File Summary (CMField.lean)**: 4 theorems. Key API: `isCMField`. No sorry, no set_option, no proof >30 lines.

---

## UniqueFactorization.lean

### `theorem six_eq_neg_theta_sq`
- **Type**: `(6 : 𝓞 K) = -(thetaInt * thetaInt)`
- **What**: `6 = -θ²` (the second factorisation of 6).
- **Uses from project**: [`K`, `thetaInt`, `thetaInt_sq`]
- **Visibility**: public
- **Lines**: 29-31

### `private theorem intNorm_two / intNorm_three / intNorm_thetaInt`
- **Type**: `norm ℤ 2 = 4`, `norm ℤ 3 = 9`, `norm ℤ thetaInt = 6`
- **Uses from project**: [`K`, `intNorm_eq_normForm`, `thetaInt`]
- **Visibility**: private
- **Lines**: 33-52
- **Notes**: `intNorm_two` duplicates an inline `have` in `Euclidean.not_normEuclidean` and in PrimeSplitting.

### `theorem irreducible_two`
- **Type**: `Irreducible (2 : 𝓞 K)`
- **How**: norm 4; factor norms `A·B=4`, exclude `A∈{1,2}` via unit/`intNorm_ne_two`; `interval_cases`.
- **Uses from project**: [`K`, `isUnit_iff_intNorm_eq_one`, `intNorm_two`, `intNorm_nonneg`, `intNorm_ne_two`]
- **Visibility**: public
- **Lines**: 55-91
- **Notes**: proof >30 lines.

### `theorem irreducible_three`
- **Type**: `Irreducible (3 : 𝓞 K)`
- **How**: norm 9; `A·B=9`, exclude `A∈{1,3}`; `interval_cases`.
- **Uses from project**: [`K`, `isUnit_iff_intNorm_eq_one`, `intNorm_three`, `intNorm_nonneg`, `intNorm_ne_three`]
- **Visibility**: public
- **Lines**: 94-135
- **Notes**: proof >30 lines.

### `theorem irreducible_theta`
- **Type**: `Irreducible thetaInt`
- **How**: norm 6; `A·B=6`, exclude `A∈{1,2,3}`; `interval_cases`.
- **Uses from project**: [`K`, `thetaInt`, `isUnit_iff_intNorm_eq_one`, `intNorm_thetaInt`, `intNorm_nonneg`, `intNorm_ne_two`, `intNorm_ne_three`]
- **Visibility**: public
- **Lines**: 139-180
- **Notes**: proof >30 lines.

### `theorem two_not_prime`
- **Type**: `¬ Prime (2 : 𝓞 K)`
- **What**: 2 is irreducible but not prime (`2 ∣ θ² = -6` but `2 ∤ θ`).
- **How**: `2 ∤ θ` since `(2,θ)=(2)` would force norm contradiction (`absNorm_primeAboveTwo` vs `4`); `dvd_or_dvd`.
- **Uses from project**: [`K`, `thetaInt`, `primeAboveTwo`, `absNorm_primeAboveTwo`, `intNorm_eq_normForm`, `thetaInt_sq`]
- **Visibility**: public
- **Lines**: 184-218
- **Notes**: proof >30 lines.

### `theorem not_uniqueFactorizationMonoid`
- **Type**: `¬ UniqueFactorizationMonoid (𝓞 K)`
- **What**: **`ℤ[√-6]` is not a UFD** (main result).
- **How**: UFM + Dedekind ⇒ PID (`IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid`), contradicts `not_isPrincipalIdealRing`.
- **Uses from project**: [`K`, `not_isPrincipalIdealRing`]
- **Visibility**: public
- **Lines**: 221-225
- **Notes**: MAIN PUBLIC RESULT.

**File Summary (UniqueFactorization.lean)**: 8 decls (all theorems; 3 private). Key API: `intNorm_two`. Main public: `not_uniqueFactorizationMonoid` (+ `irreducible_two/three/theta`, `two_not_prime` as witnesses). No sorry, no set_option. Proofs >30 lines: `irreducible_two/three/theta`, `two_not_prime`.

---

## Cross-folder / Common observations

- **Common.lean helpers actually used** by SqrtNegSix: `eq_of_le_of_absNorm_eq`, `eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq`, `left_eq_prime_of_mul_eq_prime_sq_of_ne_one`, `exists_int_inverse_mod_prime`, `not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ`, `not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow` (all in PrimeSplitting). `mulEquivOfPrimeCardEq` is **mathlib**, not Common.
- `torsionPowerHom`, `rankOnePowerHom`, `natAbs_lt_of_abs_ratCast_lt`, `two_le_ramificationIdx_of_...`, `ramificationIdx_ne_one_of_...` from Common are **not** used by SqrtNegSix (used by other twins / real-quadratic regulator work).
