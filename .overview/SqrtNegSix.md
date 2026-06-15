# Declaration Inventory — `XYin/NumberField/FieldExamples/SqrtNegSix/`

Imaginary quadratic field `ℚ(√-6)`, built via `QuadraticAlgebra ℚ (-6) 0` (radical model, generator
`θ` with `θ² = -6`). Signature `(0,1)`; ring of integers `ℤ[√-6]` (maximal order, since `-6 ≡ 2 (mod 4)`);
discriminant `-24`. **The only non-PID case study**: class number `2`, class group `≅ ℤ/2`, *not* a UFD,
*not* norm-Euclidean — the mathematically interesting negative results. Namespace `NumberField.SqrtNegSix`.
Cross-refs to `Common.lean` via `NumberField.FieldExamples`. Import chain:
`Basic → Galois → Embeddings → RingOfIntegers → PrimeSplitting → ClassGroup → Units → Euclidean → LocalGlobal`,
plus special-topic files `CMField` and `UniqueFactorization`. **Sorry-free** (confirmed: zero `sorry`/`admit`).

---

## Basic.lean

### `instance : Fact (∀ r : ℚ, r ^ 2 ≠ (-6 : ℚ) + 0 * r)`
- **Type**: `Fact (∀ r : ℚ, r ^ 2 ≠ (-6 : ℚ) + (0 : ℚ) * r)`
- **What**: Nonsquare hypothesis making `QuadraticAlgebra ℚ (-6) 0` a field (`-6` is not a rational square).
- **How**: `sq_nonneg r` + `nlinarith` (no real square root of a negative).
- **Uses from project**: [] — **Visibility**: public (anonymous instance) — **Lines**: 33-36

### `abbrev K`
- **Type**: `K : Type := QuadraticAlgebra ℚ (-6:ℚ) 0`. **What**: the field `ℚ(√-6)` (radical model). **Uses**: [] — **Lines**: 39

### `abbrev θ`
- **Type**: `θ : K := QuadraticAlgebra.omega`. **What**: distinguished `√-6`. **Uses**: [] — **Lines**: 42 — **Notes**: KEY, pervasive.

### `instance : Field K`
- **How**: `infer_instance` (uses the `Fact` above). **Uses**: [] — **Lines**: 45-46

### `instance : FiniteDimensional ℚ K`
- **How**: `QuadraticAlgebra.basis (-6) 0 |>.finiteDimensional_of_finite`. **Uses**: [] — **Lines**: 49-50

### `instance : NumberField K`
- **How**: `NumberField.of_module_finite ℚ K`. **Uses**: [] — **Lines**: 53-54

### `theorem degree_eq_two`
- **Type**: `Module.finrank ℚ K = 2`. **How**: `Module.finrank_eq_card_basis` on `QuadraticAlgebra.basis` + `Fintype.card_fin`.
- **Uses**: [] — **Visibility**: public — **Lines**: 57-58 — **Notes**: KEY (used in Embeddings, RingOfIntegers, ClassGroup, PrimeSplitting).

### `instance : Algebra.IsQuadraticExtension ℚ K`
- **How**: `degree_eq_two`. **Uses**: [`degree_eq_two`] — **Lines**: 60-61

### `theorem theta_sq`
- **Type**: `θ ^ 2 = -6`. **How**: `sq` + `QuadraticAlgebra.omega_mul_omega_eq_add` + `simp`.
- **Uses**: [] — **Lines**: 64-66 — **Notes**: KEY (the defining relation, used everywhere).

### `abbrev sqrtNegSixPolynomial`
- **Type**: `ℚ[X] := X^2 + C 6` — defining polynomial `X²+6`. **Uses**: [] — **Lines**: 69-70

### `instance : Fact (Irreducible sqrtNegSixPolynomial)`
- **How**: `irreducible_of_degree_le_three_of_not_isRoot` (degree 2, no rational root since `x²+6=0` impossible via `sq_nonneg`+`nlinarith`).
- **Uses**: [] — **Lines**: 72-84

### `abbrev KAdjoinRoot`
- **Type**: `AdjoinRoot sqrtNegSixPolynomial`. Alternate presentation. **Uses**: [] — **Lines**: 87

### `abbrev thetaAdjoinRoot`
- **Type**: `AdjoinRoot.root sqrtNegSixPolynomial`. **Uses**: [] — **Lines**: 90

### `theorem thetaAdjoinRoot_sq`
- **Type**: `thetaAdjoinRoot ^ 2 = (-6 : KAdjoinRoot)`. **How**: `AdjoinRoot.eval₂_root` + `linear_combination`.
- **Uses**: [] — **Lines**: 92-97

### `private theorem sqrtNegSixPolynomial_aeval_theta`
- **Type**: `eval₂ (Algebra.ofId ℚ K) θ sqrtNegSixPolynomial = 0`. **How**: `calc` to `θ²+6` then `theta_sq`. **Uses**: [`theta_sq`] — **Lines**: 99-103

### `private theorem thetaAdjoinRoot_mul_self`
- **Type**: `thetaAdjoinRoot * thetaAdjoinRoot = (-6)•1 + 0•thetaAdjoinRoot`. **How**: `thetaAdjoinRoot_sq` + `simp`. **Uses**: [] — **Lines**: 105-110

### `noncomputable def adjoinRootEquivQuadratic`
- **Type**: `KAdjoinRoot ≃ₐ[ℚ] K`. **What**: equivalence of AdjoinRoot and quadratic-algebra presentations.
- **How**: `AdjoinRoot.liftAlgHom` and `QuadraticAlgebra.lift`; inverses via `algHom_ext` on both sides.
- **Uses**: [`theta`, the two aux lemmas] — **Lines**: 113-136 — **Notes**: proof >20 lines.

### `theorem adjoinRootEquivQuadratic_root`
- **Type**: `adjoinRootEquivQuadratic thetaAdjoinRoot = θ`. **How**: `AdjoinRoot.liftAlgHom_root`. **Uses**: [] — **Lines**: 138-143

**File Summary**: Field setup. Establishes `K = ℚ(√-6)` two ways (quadratic-algebra `θ`, `AdjoinRoot`), proves they
agree, fixes degree 2 and the defining relation `θ²=-6`. The radical model (vs. golden-ratio model of `SqrtFive`)
because `-6 ≡ 2 (mod 4)` ⇒ naive order already maximal. KEY exports: `K`, `θ`, `degree_eq_two`, `theta_sq`.

---

## Galois.lean

### `noncomputable def idAut`
- **Type**: `K ≃ₐ[ℚ] K := AlgEquiv.refl`. **Uses**: [] — **Lines**: 32

### `private noncomputable def conjugationHom`
- **Type**: `K →ₐ[ℚ] K`. **What**: `θ ↦ -θ` via `QuadraticAlgebra.lift ⟨-omega, …⟩`. **How**: relation from `omega_mul_omega_eq_add` + `neg_mul_neg`. **Uses**: [] — **Lines**: 35-39

### `private theorem conjugationHom_omega`
- **Type**: `conjugationHom θ = -θ`. **How**: `change` to component form + `simp`. **Uses**: [] — **Lines**: 41-44

### `private theorem conjugationHom_conjugationHom`
- **Type**: `conjugationHom.comp conjugationHom = AlgHom.id`. **How**: `QuadraticAlgebra.algHom_ext` + `conjugationHom_omega`, `neg_neg`. **Uses**: [] — **Lines**: 46-50

### `noncomputable def conjugation`
- **Type**: `K ≃ₐ[ℚ] K`. **What**: nontrivial conjugation `θ ↦ -θ` (complex conj. under any embedding). **How**: `AlgEquiv.ofAlgHom`. **Uses**: [] — **Lines**: 52-56 — **Notes**: KEY.

### `theorem conjugation_apply_theta`
- **Type**: `conjugation θ = -θ`. **How**: `conjugationHom_omega`. **Uses**: [] — **Lines**: 58-60

### `theorem isGalois`
- **Type**: `IsGalois ℚ K`. **How**: `infer_instance` (separable + normal for quadratic). **Uses**: [] — **Lines**: 62-63

### `theorem aut_eq_or`
- **Type**: `∀ σ, σ = idAut ∨ σ = conjugation`. **What**: only two automorphisms. **How**: `(σθ)²=-6` ⇒ `(σθ-θ)(σθ+θ)=0`; `QuadraticAlgebra.algHom_ext` pins down `σ` by its value on `θ`. **Uses**: [`theta_sq`] — **Lines**: 66-82

### `private theorem conjugation_ne_id`
- **Type**: `conjugation ≠ idAut`. **How**: would give `2θ=0`; rule out via `theta_sq`. **Uses**: [`theta_sq`] — **Lines**: 84-93

### `theorem prod_auts`
- **Type**: `∏ σ, σ z = z * conjugation z`. **How**: `Finset.univ = {idAut, conjugation}` (from `aut_eq_or`), `prod_insert`/`prod_singleton`. **Uses**: [`aut_eq_or`] — **Lines**: 95-107

### `theorem galoisGroupStructure`
- **Type**: `Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2))`. **How**: `Nat.card = 2` (from `aut_eq_or`), `mulEquivOfPrimeCardEq`. **Uses**: [`aut_eq_or`, `conjugation_ne_id`] — **Lines**: 109-118

**File Summary**: Galois theory of the quadratic extension. The single nontrivial automorphism is `conjugation`
(`θ↦-θ`). Proves `IsGalois`, classifies all auts (`aut_eq_or`), Gal group `≅ ℤ/2`. Quadratic so all standard.

---

## Embeddings.lean

### `theorem isTotallyComplex`
- **Type**: `NumberField.IsTotallyComplex K`. **What**: every infinite place is complex. **How**: under a real embedding `z=σθ` satisfies `z²=-6` with `z.im=0`, contradicting `z.re²<0` via `nlinarith`. **Uses**: [`theta_sq`] — **Lines**: 34-48 — **Notes**: KEY (used in CMField, Units, ClassGroup).

### `theorem nrRealPlaces_eq_zero`
- **Type**: `nrRealPlaces K = 0`. **How**: `IsTotallyComplex.nrRealPlaces_eq_zero`. **Uses**: [`isTotallyComplex`] — **Lines**: 50-52 — **Notes**: KEY.

### `theorem nrComplexPlaces_eq_one`
- **Type**: `nrComplexPlaces K = 1`. **How**: `card_add_two_mul_card_eq_rank` + `nrRealPlaces_eq_zero` + `degree_eq_two` + `omega`. **Uses**: [`nrRealPlaces_eq_zero`, `degree_eq_two`] — **Lines**: 54-57 — **Notes**: KEY (signature `(0,1)`).

### `theorem infinitePlace_card_eq_one`
- **Type**: `Fintype.card (InfinitePlace K) = 1`. **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces`. **Uses**: [the two place counts] — **Lines**: 71-74

### `theorem infinitePlace_isComplex`
- **Type**: `∀ v, IsComplex v`. **How**: `isTotallyComplex.isComplex`. **Uses**: [`isTotallyComplex`] — **Lines**: 76-78

### `theorem exists_complexEmbedding_theta_pos`
- **Type**: `∃ σ : K →+* ℂ, σ θ = I·√6`. **How**: `QuadraticAlgebra.lift ⟨I·√6, …⟩`; `(I·√6)²=-6` via `I_mul_I`+`sq_sqrt`. **Uses**: [] — **Lines**: 80-89

### `theorem exists_complexEmbedding_theta_neg`
- **Type**: `∃ σ : K →+* ℂ, σ θ = -I·√6`. **How**: twin of pos, witness `-I·√6`. **Uses**: [] — **Lines**: 91-100

**File Summary**: Archimedean data. Signature `(0,1)`: totally complex, `r₁=0`, `r₂=1`, one infinite place. The
two complex embeddings (`θ↦±I√6`) made explicit. Negative-`d` analogue of `SqrtFive`'s real-places file.

---

## RingOfIntegers.lean

### `theorem theta_integral`
- **Type**: `θ ∈ integralClosure ℤ K`. **How**: root of monic `X²+6` (`monicity!` + `theta_sq`). **Uses**: [`theta_sq`] — **Lines**: 33-37 — **Notes**: KEY.

### `noncomputable def thetaInt`
- **Type**: `𝓞 K := ⟨θ, theta_integral⟩`. **What**: `√-6` in the ring of integers. **Uses**: [`theta_integral`] — **Lines**: 40 — **Notes**: KEY, pervasive in all integral-arithmetic files.

### `theorem thetaInt_sq`
- **Type**: `thetaInt ^ 2 = -6`. **How**: `Subtype.ext` + `theta_sq`. **Uses**: [`theta_sq`] — **Lines**: 43-46 — **Notes**: KEY (used throughout PrimeSplitting/UniqueFactorization).

### `def integralBasisVectors`
- **Type**: `Fin 2 → K := ![1, θ]`. **Uses**: [] — **Lines**: 49

### `local notation 𝓟₂ / 𝓟₃`
- `Submodule.span ℤ {2}` / `{3}` — for Eisenstein-at-`p` statements. **Lines**: 51-52

### `private theorem quadraticBasis_zero` / `_one`
- **Type**: `QuadraticAlgebra.basis (-6) 0` sends `0↦1`, `1↦θ`. **How**: `change`+`simp [basis, ofEquivFun, linearEquivTuple]`. **Uses**: [] — **Lines**: 54-60

### `noncomputable def sqrtNegSixPowerBasis`
- **Type**: `PowerBasis ℚ K` with `gen=θ`, `dim=2`. **How**: `basis_eq_pow` via the two `quadraticBasis_*`. **Uses**: [] — **Lines**: 62-71

### `abbrev sqrtNegSixIntegerPolynomial`
- **Type**: `ℤ[X] := X^2 + C 6`. **Uses**: [] — **Lines**: 74

### `theorem sqrtNegSix_minpoly_rat`
- **Type**: `minpoly ℚ θ = sqrtNegSixPolynomial`. **How**: `minpoly.eq_of_irreducible_of_monic` (Fact instance + `theta_sq` + `monicity!`). **Uses**: [`theta_sq`] — **Lines**: 76-83

### `theorem sqrtNegSix_minpoly_int`
- **Type**: `minpoly ℤ θ = sqrtNegSixIntegerPolynomial`. **How**: `map_injective` + `minpoly.isIntegrallyClosed_eq_field_fractions'` + `sqrtNegSix_minpoly_rat`. **Uses**: [`sqrtNegSix_minpoly_rat`, `theta_integral`] — **Lines**: 86-94

### `theorem sqrtNegSix_minpoly_int_isEisensteinAt_two`
- **Type**: `(minpoly ℤ θ).IsEisensteinAt 𝓟₂`. **How**: `monic_X_pow_add_C.isEisensteinAt_of_mem_of_notMem` (`6∈(2)`, `6∉(2)²=(4)`). **Uses**: [`sqrtNegSix_minpoly_int`] — **Lines**: 96-112 — **Notes**: drives maximality (`2 ∤ disc index`).

### `theorem sqrtNegSix_minpoly_int_isEisensteinAt_three`
- **Type**: `(minpoly ℤ θ).IsEisensteinAt 𝓟₃`. **How**: twin at `3` (`6∈(3)`, `6∉(9)`). **Uses**: [`sqrtNegSix_minpoly_int`] — **Lines**: 114-130

### `private theorem algebraNorm_eq_quadraticNorm`
- **Type**: `Algebra.norm ℚ z = QuadraticAlgebra.norm z`. **How**: `norm_apply` + `det_toLinearMap_eq_norm`. **Uses**: [] — **Lines**: 132-135

### `theorem sqrtNegSixPowerBasis_discr`
- **Type**: `Algebra.discr ℚ sqrtNegSixPowerBasis.basis = -24`. **How**: `discr_powerBasis_eq_norm`; `minpoly' = 2X`, `aeval = 2θ`, `norm(2θ)=24` via the quadratic norm form. **Uses**: [`degree_eq_two`, `sqrtNegSix_minpoly_rat`] — **Lines**: 137-156 — **Notes**: KEY (disc `-24`).

### `private theorem integralClosure_eq_adjoin`
- **Type**: `integralClosure ℤ K = Algebra.adjoin ℤ {θ}`. **What**: maximality of `ℤ[θ]`. **How**: `discr_mul_isIntegral_mem_adjoin` gives `24z ∈ adjoin`; strip `2³` and `3` via `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt` at both Eisenstein primes. **Uses**: [`sqrtNegSixPowerBasis_discr`, both Eisenstein lemmas, `theta_integral`] — **Lines**: 158-196 — **Notes**: KEY proof; the heart of "naive order is maximal".

### `private theorem thetaInt_adjoin_eq_top`
- **Type**: `Algebra.adjoin ℤ {thetaInt} = ⊤`. **How**: pull back `integralClosure_eq_adjoin` through `adjoin_singleton_eq_range_aeval`. **Uses**: [`integralClosure_eq_adjoin`] — **Lines**: 198-214

### `private theorem thetaInt_minpoly`
- **Type**: `minpoly ℤ thetaInt = sqrtNegSixIntegerPolynomial`. **How**: `minpoly.isIntegrallyClosed_eq_field_fractions` + `sqrtNegSix_minpoly_rat`. **Uses**: [`sqrtNegSix_minpoly_rat`] — **Lines**: 216-234

### `private noncomputable def sqrtNegSixExplicitIntegralPowerBasis`
- **Type**: `PowerBasis ℤ (𝓞 K)`. **How**: `PowerBasis.ofAdjoinEqTop'`. **Uses**: [`thetaInt_adjoin_eq_top`] — **Lines**: 236-237

### `private theorem sqrtNegSixExplicitIntegralPowerBasis_dim`
- **Type**: `dim = 2`. **How**: `ofAdjoinEqTop'_dim` + `thetaInt_minpoly` + `natDegree_X_pow_add_C`. **Uses**: [`thetaInt_minpoly`] — **Lines**: 239-243

### `private noncomputable def sqrtNegSixExplicitIntegralBasis`
- **Type**: `Basis (Fin 2) ℤ (𝓞 K)`. **How**: reindex the power basis along `dim=2`. **Uses**: [] — **Lines**: 245-247

### `private theorem sqrtNegSixExplicitIntegralBasis_zero` / `_one`
- **Type**: basis sends `0↦1`, `1↦thetaInt`. **How**: `basis_eq_pow` + `ofAdjoinEqTop'_gen`. **Uses**: [] — **Lines**: 249-267

### `private noncomputable def integralBasisVectorsInt`
- **Type**: `Fin 2 → 𝓞 K := ![1, thetaInt]`. **Uses**: [] — **Lines**: 269

### `private theorem algebraMap_integralBasisVectorsInt`
- **Type**: maps to `integralBasisVectors` in `K`. **How**: `fin_cases`+`simp`. **Uses**: [] — **Lines**: 271-274

### `private noncomputable def ringOfIntegersLinearMap`
- **Type**: `𝓞 K →ₗ[ℤ] K`. **How**: `Algebra.linearMap.restrictScalars`. **Uses**: [] — **Lines**: 276-277

### `private theorem span_integralBasisVectorsInt_eq_top`
- **Type**: `span ℤ (range integralBasisVectorsInt) = ⊤`. **How**: `Basis.span_eq` of the explicit basis. **Uses**: [] — **Lines**: 279-287

### `private theorem sqrtNegSixExplicitIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ … = -24`. **How**: `discr_localizationLocalization` from `ℤ→ℚ`, transfer to `sqrtNegSixPowerBasis_discr` via `Basis.localizationLocalization`. **Uses**: [`sqrtNegSixPowerBasis_discr`] — **Lines**: 289-324 — **Notes**: heavy localization machinery.

### `theorem span_integralBasisVectors_eq`
- **Type**: `span ℤ (range integralBasisVectors) = toSubmodule (integralClosure ℤ K)`. **What**: `1,θ` is an integral basis. **How**: push `span_integralBasisVectorsInt_eq_top` through `ringOfIntegersLinearMap`. **Uses**: [those two lemmas] — **Lines**: 326-347 — **Notes**: docstring contrasts with `ℚ(√5)`.

### `noncomputable def concreteIntegralBasis`
- **Type**: `Basis (Fin 2) ℤ (𝓞 K) := sqrtNegSixExplicitIntegralBasis`. **Uses**: [] — **Lines**: 349-351 — **Notes**: KEY (used in `exists_eq_smul_one_add_smul_theta`).

### `theorem concreteIntegralBasis_apply`
- **Type**: `algebraMap (concreteIntegralBasis i) = integralBasisVectors i`. **How**: `fin_cases`+`simp`. **Uses**: [the basis lemmas] — **Lines**: 353-358

### `theorem exists_eq_smul_one_add_smul_theta`
- **Type**: `∀ z:𝓞 K, ∃ x y:ℤ, z = x•1 + y•thetaInt`. **How**: `concreteIntegralBasis.repr` + `sum_repr`. **Uses**: [`concreteIntegralBasis`] — **Lines**: 360-368 — **Notes**: KEY workhorse — every integral-arithmetic argument reduces to integer coordinates `(x,y)`.

### `theorem linearIndependent_one_theta`
- **Type**: `LinearIndependent ℤ ![1, thetaInt]`. **How**: transport `concreteIntegralBasis.linearIndependent`. **Uses**: [`concreteIntegralBasis`] — **Lines**: 370-386 — **Notes**: KEY (pins ideal-membership computations in PrimeSplitting).

### `theorem span_integralBasisVectors_eq_integralBasis`
- **Type**: span of `1,θ` = span of mathlib's `NumberField.integralBasis K`. **How**: `span_integralBasisVectors_eq` + `mem_span_integralBasis`. **Uses**: [`span_integralBasisVectors_eq`] — **Lines**: 388-402 — **Notes**: equality of lattices, not reindexing.

### `abbrev concreteRingOfIntegers`
- **Type**: `Subalgebra ℤ K := Algebra.adjoin ℤ {θ}`. **What**: the order `ℤ[θ]`. **Uses**: [] — **Lines**: 404-405

### `theorem ringOfIntegers_eq`
- **Type**: `integralClosure ℤ K = concreteRingOfIntegers`. **How**: `integralClosure_eq_adjoin`. **Uses**: [`integralClosure_eq_adjoin`] — **Lines**: 407-410 — **Notes**: `𝓞 K = ℤ[√-6]`.

### `theorem numberField_discr_eq`
- **Type**: `NumberField.discr K = -24`. **How**: `discr_eq_discr K concreteIntegralBasis` + `sqrtNegSixExplicitIntegralBasis_discr`. **Uses**: [`concreteIntegralBasis`, the basis discr] — **Lines**: 412-417 — **Notes**: KEY (used in Minkowski bound, different, ramification).

### `theorem concreteIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ concreteIntegralBasis = -24`. **How**: `sqrtNegSixExplicitIntegralBasis_discr`. **Uses**: [] — **Lines**: 419-422

### `theorem integralBasis_discr`
- **Type**: `Algebra.discr ℚ (NumberField.integralBasis K) = -24`. **How**: `coe_discr` + `numberField_discr_eq`. **Uses**: [`numberField_discr_eq`] — **Lines**: 424-429

### `theorem norm_eq_normForm`
- **Type**: `Algebra.norm ℚ (x•1 + y•θ) = x² + 6y²`. **What**: the (positive-definite) norm form. **How**: `det_toLinearMap_eq_norm` + `QuadraticAlgebra.norm_def`. **Uses**: [] — **Lines**: 444-454 — **Notes**: KEY — positive-definiteness drives ALL negative results (no Pell, units `±1`, unsolvable `=2,3,5`).

### `theorem intNorm_eq_normForm`
- **Type**: `Algebra.norm ℤ (x•1 + y•thetaInt) = x² + 6y²` (`x,y:ℤ`). **How**: `coe_norm_int` cast from `norm_eq_normForm`. **Uses**: [`norm_eq_normForm`] — **Lines**: 456-469 — **Notes**: KEY workhorse for all norm computations.

### `theorem normForm_ne_two`
- **Type**: `x² + 6y² ≠ 2`. **How**: forces `y=0`, `x²=2`, `interval_cases`. **Uses**: [] — **Lines**: 471-479 — **Notes**: KEY — witnesses `(2,θ)` non-principal & `2` irreducible-not-prime.

### `private theorem normForm_ne_three`
- **Type**: `x² + 6y² ≠ 3`. **How**: forces `y=0`, `x²=3`, `interval_cases`. **Uses**: [] — **Lines**: 481-491

### `private theorem normForm_ne_five`
- **Type**: `x² + 6y² ≠ 5`. **How**: forces `y=0`, `x²=5`, `interval_cases`. **Uses**: [] — **Lines**: 493-503 — **Notes**: drives `(5,θ-2)` non-principal.

### `theorem isUnit_iff_normForm`
- **Type**: `IsUnit (x•1 + y•thetaInt) ↔ x²+6y² = 1`. **How**: `isUnit_iff_norm` + `intNorm_eq_normForm`; positive-definite ⇒ no `-1` case. **Uses**: [`intNorm_eq_normForm`] — **Lines**: 505-519 — **Notes**: KEY — only `(±1,0)`, no Pell.

### `theorem intNorm_nonneg`
- **Type**: `0 ≤ Algebra.norm ℤ z`. **How**: reduce to `x²+6y²≥0`. **Uses**: [`exists_eq_smul_one_add_smul_theta`, `intNorm_eq_normForm`] — **Lines**: 521-524 — **Notes**: KEY (norms positive ⇒ many `nlinarith` factor-bounds).

### `theorem isUnit_iff_intNorm_eq_one`
- **Type**: `IsUnit z ↔ Algebra.norm ℤ z = 1`. **How**: reduce to `isUnit_iff_normForm`. **Uses**: [`exists_eq_smul_one_add_smul_theta`] — **Lines**: 526-529 — **Notes**: KEY.

### `theorem intNorm_ne_two` / `intNorm_ne_three` / `intNorm_ne_five`
- **Type**: `Algebra.norm ℤ z ≠ 2 / 3 / 5`. **How**: reduce via coordinates to `normForm_ne_*`. **Uses**: [`exists_eq_smul_one_add_smul_theta`, the `normForm_ne_*`] — **Lines**: 531-547 — **Notes**: KEY — non-attainment of small norms = source of irreducibility & non-principality.

**File Summary**: Ring of integers `𝓞 K = ℤ[√-6]` (maximal order, `-6≡2 mod 4`) with explicit integral basis
`1,θ`, discriminant `-24` (computed via power-basis + localization), and the positive-definite norm form
`x²+6y²`. The norm-form non-attainment lemmas (`≠2,3,5`) and `exists_eq_smul_one_add_smul_theta` /
`linearIndependent_one_theta` are the reusable engine behind every irreducibility, splitting, and
non-principality proof. KEY exports: `thetaInt`, `thetaInt_sq`, `intNorm_eq_normForm`, `numberField_discr_eq`,
`isUnit_iff_*`, `intNorm_ne_*`.

---

## PrimeSplitting.lean

Imports `Common.lean`. Splitting law, Kummer-Dedekind, ramification, different.

### `private theorem absNorm_span_natCast`
- **Type**: `absNorm (span {(p:ℕ):𝓞 K}) = p²`. **How**: `absNorm_span_natCast` + `RingOfIntegers.rank` + `degree_eq_two`. **Uses**: [`degree_eq_two`] — **Lines**: 35-37

### `private theorem unit_theta_coeff_not_mem`
- **Type**: `A + Bθ` with `B=±1` is never in `(p)` for `p≥2`. **How**: coordinates via `exists_eq_smul_one_add_smul_theta`; `linearIndependent_one_theta` gives `p∣1` contradiction. **Uses**: [`exists_eq_smul_one_add_smul_theta`, `linearIndependent_one_theta`] — **Lines**: 40-63 — **Notes**: KEY helper for all "`(p,θ-c)` norm = `p`" lemmas.

### `private theorem isSquare_neg_six_iff_mod_twentyfour`
- **Type**: `IsSquare ((-6:ℤ):ZMod p) ↔ p%24 ∈ {1,5,7,11}`. **How**: `jacobiSym.mod_right`, case-split `p%24`, `nonsquare_iff_jacobiSym_eq_neg_one` / `isSquare_of_jacobiSym_eq_one`. **Uses**: [] — **Lines**: 65-105 — **Notes**: KEY — quadratic-reciprocity core of the splitting law.

### `def primeAboveTwo`
- **Type**: `Ideal (𝓞 K) := span {2, thetaInt}` = `(2,θ)`. **Uses**: [] — **Lines**: 109 — **Notes**: KEY — the non-principal ramified prime, representative of the nontrivial class.

### `def primeAboveThree`
- **Type**: `span {3, thetaInt}` = `(3,θ)`. **Uses**: [] — **Lines**: 112 — **Notes**: KEY — same class as `primeAboveTwo`.

### `theorem span_two_eq`
- **Type**: `(2) = primeAboveTwo²`. **What**: `2` ramifies. **How**: `span_pair_mul_span_pair`, `le_antisymm`, `thetaInt_sq`. **Uses**: [`thetaInt_sq`] — **Lines**: 115-140 — **Notes**: KEY (`(2,θ)²=(2)` ⇒ class² trivial).

### `theorem isPrime_primeAboveTwo`
- **Type**: `primeAboveTwo.IsPrime`. **How**: `isPrime_of_irreducible_absNorm`, `absNorm=2` prime. **Uses**: [`span_two_eq`, `intNorm_eq_normForm`] — **Lines**: 143-155

### `theorem absNorm_primeAboveTwo`
- **Type**: `absNorm primeAboveTwo = 2`. **How**: `absNorm(2)=4`, `span_two_eq` ⇒ `absNorm²=4`, `nlinarith`. **Uses**: [`span_two_eq`, `intNorm_eq_normForm`] — **Lines**: 158-166 — **Notes**: KEY.

### `theorem liesOver_primeAboveTwo`
- **Type**: `primeAboveTwo.LiesOver (span {(2:ℤ)})`. **How**: `liesOver_span_iff` + `2∈(2,θ)`. **Uses**: [`isPrime_primeAboveTwo`] — **Lines**: 169-174

### `theorem inertiaDeg_primeAboveTwo`
- **Type**: `inertiaDeg = 1`. **How**: `absNorm_eq_pow_inertiaDeg'` + `Prime.pow_eq_iff`. **Uses**: [`liesOver_primeAboveTwo`, `absNorm_primeAboveTwo`] — **Lines**: 177-182

### `theorem ramificationIdx_primeAboveTwo`
- **Type**: `ramificationIdx = 2`. **How**: `ramificationIdx_spec` (`(2)≤P²` from `span_two_eq`; `¬(2)≤P³` via norm `8∤4`). **Uses**: [`span_two_eq`, `absNorm_primeAboveTwo`] — **Lines**: 185-205

### `theorem not_isPrincipal_primeAboveTwo`
- **Type**: `¬ Submodule.IsPrincipal primeAboveTwo`. **What**: **THE central negative result** — exhibits the nontrivial ideal class. **How**: a principal generator would have `|norm|=absNorm=2`, but `x²+6y²=2` is unsolvable (`normForm_ne_two`). **Uses**: [`absNorm_primeAboveTwo`, `exists_eq_smul_one_add_smul_theta`, `intNorm_eq_normForm`, `normForm_ne_two`] — **Lines**: 209-224 — **Notes**: KEY — used by `not_isPrincipalIdealRing`, `classGroup_mk0_ramified_ne_one`, `classNumber_eq_two`.

### `theorem span_three_eq`
- **Type**: `(3) = primeAboveThree²`. **How**: twin of `span_two_eq` (`-2·θ²` term). **Uses**: [`thetaInt_sq`] — **Lines**: 227-250

### `theorem isPrime_primeAboveThree`
- **Type**: `primeAboveThree.IsPrime`. **How**: `absNorm=3` prime. **Uses**: [`span_three_eq`, `intNorm_eq_normForm`] — **Lines**: 252-266

### `theorem absNorm_primeAboveThree`
- **Type**: `absNorm primeAboveThree = 3`. **How**: `absNorm(3)=9`, `nlinarith`. **Uses**: [`span_three_eq`, `intNorm_eq_normForm`] — **Lines**: 268-276 — **Notes**: KEY.

### `theorem liesOver_primeAboveThree` / `inertiaDeg_primeAboveThree` / `ramificationIdx_primeAboveThree`
- **Type**: lies over `(3)`; `inertiaDeg=1`; `ramificationIdx=2`. **How**: twins of the `Two` versions. **Uses**: [the `Three` lemmas] — **Lines**: 278-315

### `theorem span_theta_eq`
- **Type**: `(θ) = primeAboveTwo * primeAboveThree`. **What**: the principal ideal `(√-6)` factors as the product of the two ramified primes. **How**: `span_pair_mul_span_pair` + `thetaInt_sq`. **Uses**: [`thetaInt_sq`] — **Lines**: 318-344 — **Notes**: KEY — proves classes of `(2,θ)` and `(3,θ)` are *equal* (their product is principal), so the class group has only one nontrivial element.

### `theorem ideal_eq_primeAboveTwo_of_absNorm_eq_two`
- **Type**: `absNorm I = 2 ⇒ I = primeAboveTwo`. **How**: `2∈I`, `θ∈I` (from `θ²=-6∈I` in `𝓞K/I`), then `eq_of_le_of_absNorm_eq` (Common). **Uses**: [`Common.eq_of_le_of_absNorm_eq`, `absNorm_primeAboveTwo`, `thetaInt_sq`] — **Lines**: 346-383 — **Notes**: KEY — uniqueness of the norm-2 ideal, used in class-group enumeration.

### `theorem ideal_eq_primeAboveThree_of_absNorm_eq_three`
- **Type**: `absNorm I = 3 ⇒ I = primeAboveThree`. **How**: twin. **Uses**: [`Common.eq_of_le_of_absNorm_eq`, `absNorm_primeAboveThree`, `thetaInt_sq`] — **Lines**: 385-422 — **Notes**: KEY.

### `theorem seven_eq_mul`
- **Type**: `7 = (1+θ)(1-θ)`. **How**: `ring_nf`+`thetaInt_sq`. **Uses**: [`thetaInt_sq`] — **Lines**: 424-426

### `theorem span_seven_eq`
- **Type**: `(7) = (1+θ)(1-θ)` (principal factors). **How**: `span_singleton_mul_span_singleton` + `seven_eq_mul`. **Uses**: [`seven_eq_mul`] — **Lines**: 428-432 — **Notes**: `7` splits with *principal* primes (represented by the principal form `1²+6·1²`).

### `theorem absNorm_span_one_add_theta` / `_sub_theta`
- **Type**: `absNorm (1±θ) = 7`. **How**: `absNorm_span_singleton` + `intNorm_eq_normForm 1 (±1)`. **Uses**: [`intNorm_eq_normForm`] — **Lines**: 435-440, 448-457

### `theorem isPrime_span_one_add_theta` / `_sub_theta`
- **Type**: `(1±θ).IsPrime`. **How**: `isPrime_of_irreducible_absNorm` (norm 7). **Uses**: [the absNorm lemmas] — **Lines**: 442-445, 459-463

### `theorem liesOver_span_one_add_theta` / `_sub_theta`
- **Type**: lie over `(7)`. **How**: `7∈(1±θ)` via `seven_eq_mul`. **Uses**: [`seven_eq_mul`] — **Lines**: 466-485

### `theorem inertiaDeg_span_one_add_theta` / `_sub_theta`
- **Type**: `inertiaDeg = 1`. **How**: `absNorm_eq_pow_inertiaDeg'`. **Uses**: [absNorm lemmas] — **Lines**: 488-505

### `def primeAboveFiveSubTwo` / `primeAboveFiveAddTwo`
- **Type**: `span {5, thetaInt∓2}` = `(5,θ-2)` / `(5,θ+2)`. **What**: the *non-principal* primes above the split prime `5`. **Uses**: [] — **Lines**: 510, 513 — **Notes**: subtle — `5` splits yet its prime factors are non-principal (`5 = 2x²+3y²`, the other genus form).

### `theorem span_five_eq`
- **Type**: `(5) = (5,θ-2)(5,θ+2)`. **How**: `span_pair_mul_span_pair` + `thetaInt_sq` (`(θ-2)(θ+2)=θ²-4=-10`). **Uses**: [`thetaInt_sq`] — **Lines**: 515-542

### `private theorem span_five_theta_sub_two_ne_top` / `_add_two_ne_top`
- **Type**: `(5,θ∓2) ≠ ⊤`. **How**: `1∈I` ⇒ coordinates ⇒ `5∣1`, contradiction (`linearIndependent_one_theta`). **Uses**: [`exists_eq_smul_one_add_smul_theta`, `linearIndependent_one_theta`, `thetaInt_sq`] — **Lines**: 544-597

### `theorem absNorm_primeAboveFiveSubTwo` / `_AddTwo`
- **Type**: `absNorm = 5`. **How**: divides `25`, `≠1` (proper), `≠25` (else `θ∓2∈(5)`, ruled out by `unit_theta_coeff_not_mem`); `dvd_prime_pow`+`interval_cases`. **Uses**: [`absNorm_span_natCast`, `Common.eq_of_le_of_absNorm_eq`, `unit_theta_coeff_not_mem`] — **Lines**: 600-659

### `theorem isPrime_primeAboveFiveSubTwo` / `_AddTwo`
- **Type**: `.IsPrime`. **How**: `absNorm=5` prime. **Uses**: [absNorm lemmas] — **Lines**: 662-671

### `theorem liesOver_primeAboveFiveSubTwo` / `_AddTwo`, `inertiaDeg_primeAboveFiveSubTwo` / `_AddTwo`
- **Type**: lie over `(5)`; `inertiaDeg=1`. **How**: standard. **Uses**: [the `Five*` lemmas] — **Lines**: 674-709

### `private theorem intNorm_five` / `intNorm_theta_sub_two`
- **Type**: `norm(5)=25`, `norm(θ-2)=10`. **How**: `intNorm_eq_normForm`. **Uses**: [`intNorm_eq_normForm`] — **Lines**: 711-723

### `theorem not_isPrincipal_primeAboveFive`
- **Type**: `¬ IsPrincipal (5,θ-2)`. **What**: second non-principality witness (the split prime over `5`). **How**: a generator `a` would satisfy `A∣25` and `A∣10`, with `A≠1` (proper), `A≠5` (`intNorm_ne_five`); `interval_cases A`+`omega` exhausts. **Uses**: [`Common`, `intNorm_five`, `intNorm_theta_sub_two`, `intNorm_ne_five`, `isUnit_iff_intNorm_eq_one`, `intNorm_nonneg`] — **Lines**: 726-773 — **Notes**: KEY — concretely confirms class number `> 1` from the splitting of `5`.

### `private theorem absNorm_span_thirteen_aux`
- **Type**: `absNorm (13) = 169`. **How**: `intNorm_eq_normForm 13 0`. **Uses**: [`intNorm_eq_normForm`] — **Lines**: 775-781

### `theorem isPrime_span_thirteen`
- **Type**: `(13).IsPrime`. **What**: `13` is **inert**. **How**: any maximal `M ⊇ (13)` has `absNorm∣169`; `≠1`, `≠13` (else `ZMod 13` would contain a root of `t²+6` — ruled out by `decide`), so `=169`, forcing `M=(13)`. **Uses**: [`absNorm_span_thirteen_aux`, `thetaInt_sq`] — **Lines**: 784-831 — **Notes**: KEY — inertness via "no square root of `-6` mod 13".

### `theorem absNorm_span_thirteen`
- **Type**: `absNorm (13) = 169`. **Uses**: [`absNorm_span_thirteen_aux`] — **Lines**: 833-835

### `theorem liesOver_span_thirteen` / `inertiaDeg_span_thirteen`
- **Type**: lies over `(13)`; `inertiaDeg = 2`. **How**: `pow_right_injective` on `13²=13^f`. **Uses**: [`isPrime_span_thirteen`, `absNorm_span_thirteen`] — **Lines**: 837-855 — **Notes**: inert ⇒ `f=2`.

### `private theorem mod_twentyfour_of_splits`
- **Type**: split (`p%24∉{2,3}`) ⇒ `p%24∈{1,5,7,11}`. **How**: `absNorm P = p` ⇒ `ZMod p ≅ 𝓞K/P` has a root of `t²+6` ⇒ `IsSquare (-6)` ⇒ `isSquare_neg_six_iff_mod_twentyfour`. **Uses**: [`Common.left_eq_prime_of_mul_eq_prime_sq_of_ne_one`, `absNorm_span_natCast`, `thetaInt_sq`, `isSquare_neg_six_iff_mod_twentyfour`] — **Lines**: 857-895

### `private theorem exists_root_data`
- **Type**: from `-6=s²` mod `p`, produces `c,d,k₁,k₂:ℤ` with `(θ-c)(θ-d)=p·(…)`. **How**: `c=s.val`, `d=(-s).val`, `p∣c+d`, `p∣cd-6`; `linear_combination`. **Uses**: [`thetaInt_sq`] — **Lines**: 897-933 — **Notes**: Kummer-Dedekind factorization data.

### `private theorem absNorm_span_pair_not_one`
- **Type**: `(p,θ-c) ≠ ⊤` (given the product relation). **How**: `1∈I` ⇒ `θ-d∈(p)`, ruled out by `unit_theta_coeff_not_mem`. **Uses**: [`unit_theta_coeff_not_mem`] — **Lines**: 935-960

### `private theorem absNorm_span_pair_ne_prime_sq`
- **Type**: `absNorm (p,θ-c) ≠ p²`. **How**: would give `(p,θ-c)=(p)` ⇒ `θ-c∈(p)`, contradiction. **Uses**: [`Common.eq_of_le_of_absNorm_eq`, `absNorm_span_natCast`, `unit_theta_coeff_not_mem`] — **Lines**: 962-977

### `private theorem absNorm_span_pair_eq_prime`
- **Type**: `absNorm (p,θ-c) = p`. **How**: `Common.eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq` (divides `p²`, `≠1`, `≠p²`). **Uses**: [`Common`, the two prior lemmas, `absNorm_span_natCast`] — **Lines**: 979-990

### `private theorem root_ne_neg_of_square_neg_six`
- **Type**: for `p∉{2,3}`, `s ≠ -s`. **How**: `s=-s` ⇒ `2s=0` ⇒ `s=0` ⇒ `p∣6`, contradiction. **Uses**: [] — **Lines**: 992-1015 — **Notes**: distinctness of the two primes over a split `p`.

### `private theorem span_pair_ne_of_roots_ne`
- **Type**: `c≢d mod p` ⇒ `(p,θ-c) ≠ (p,θ-d)`. **How**: `exists_int_inverse_mod_prime` (Common) builds `1∈I`, contradicting norm `p`. **Uses**: [`Common.exists_int_inverse_mod_prime`] — **Lines**: 1017-1046

### `private theorem span_pair_mul_eq_span_natCast`
- **Type**: `(p) = (p,θ-c)(p,θ-d)`. **How**: `≤` directly; norms force equality via `eq_of_le_of_absNorm_eq`. **Uses**: [`Common.eq_of_le_of_absNorm_eq`, `absNorm_span_natCast`] — **Lines**: 1048-1076

### `private theorem splits_of_square_neg_six`
- **Type**: `-6=s²` mod `p` (`p∉{2,3}`) ⇒ `(p)=P·Q`, `P,Q` distinct primes. **How**: assembles `exists_root_data`, the pair-norm lemmas, distinctness, product. **Uses**: [all the private Kummer lemmas above] — **Lines**: 1078-1116

### `theorem splits_iff_mod_twentyfour`
- **Type**: for `p∉{2,3}`: `(p)` splits into two distinct primes ↔ `p%24∈{1,5,7,11}`. **How**: `mod_twentyfour_of_splits` (⇒) and `splits_of_square_neg_six` (⇐). **Uses**: [`isSquare_neg_six_iff_mod_twentyfour`, the two directions] — **Lines**: 1118-1130 — **Notes**: KEY — the full splitting law.

### `private theorem eq_two_or_eq_three_of_prime_dvd_twentyfour`
- **Type**: `p prime ∣ 24 ⇒ p=2 ∨ p=3`. **How**: `24=2³·3`, `Prime.dvd_mul`. **Uses**: [] — **Lines**: 1132-1140

### `theorem ramified_iff`
- **Type**: `(∃ P prime, (p)≤P²) ↔ p∈{2,3}` (`p ∣ disc -24`). **How**: (⇒) `P∣differentIdeal` via `not_isUnramifiedAt_of_…` (Common), `absNorm(different)=24`, so `p∣24`. (⇐) exhibit `primeAboveTwo`/`Three` with `span_two_eq`/`span_three_eq`. **Uses**: [`Common` ramification helpers, `numberField_discr_eq`, `NumberField.absNorm_differentIdeal`, `span_two_eq`, `span_three_eq`] — **Lines**: 1142-1188 — **Notes**: KEY — ramified primes are exactly the divisors of disc `-24`.

### `theorem ramificationIdx_span_one_add_theta` / `_sub_theta`, `ramificationIdx_primeAboveFiveSubTwo` / `_AddTwo`, `ramificationIdx_span_thirteen`
- **Type**: ramification index `1` (the split/inert primes are unramified). **How**: `ramificationIdx_spec`; over-2 case ruled out by `ramified_iff` (`7,5,13∉{2,3}`). **Uses**: [`ramified_iff`, the per-prime data] — **Lines**: 1190-1266

### `abbrev sqrtNegSixPolynomialMod`
- **Type**: `(ZMod p)[X] := X²+C 6`. **What**: reduction of `X²+6` mod `p`. **Uses**: [] — **Lines**: 1284-1285

### `private theorem sqrtNegSixPolynomialMod_isRoot_iff`
- **Type**: `IsRoot t ↔ t² = ((-6:ℤ):ZMod p)`. **How**: `eval`+`linear_combination`. **Uses**: [] — **Lines**: 1287-1295

### `private theorem sqrtNegSixPolynomialMod_natDegree`
- **Type**: `natDegree = 2`. **How**: `simp`. **Uses**: [] — **Lines**: 1297-1299

### `private theorem sqrtNegSixPolynomialMod_roots_eq_zero_iff_no_root`
- **Type**: `roots = 0 ↔ ¬∃ t, t²=-6`. **How**: `mem_roots`/`eq_zero_iff_forall_notMem`. **Uses**: [the isRoot lemma] — **Lines**: 1301-1322

### `private theorem sqrtNegSixPolynomialMod_no_root_iff_inert_mod_twentyfour`
- **Type**: `(¬∃ t, t²=-6) ↔ p%24∈{13,17,19,23}`. **How**: case-split `p%24`, dispatch via `isSquare_neg_six_iff_mod_twentyfour`. **Uses**: [`isSquare_neg_six_iff_mod_twentyfour`] — **Lines**: 1324-1372 — **Notes**: inertness law (Kummer-Dedekind, polynomial-irreducible form).

### `theorem absNorm_differentIdeal_eq_twentyFour`
- **Type**: `absNorm (differentIdeal ℤ (𝓞 K)) = 24`. **How**: `NumberField.absNorm_differentIdeal` + `numberField_discr_eq`. **Uses**: [`numberField_discr_eq`] — **Lines**: 1387-1390

### `theorem prime_dvd_differentIdeal_iff_eq_ramifiedPrime`
- **Type**: `P∣different ↔ P∈{primeAboveTwo, primeAboveThree}`. **How**: (⇒) `absNorm(under P)∣24` ⇒ `under=2 or 3` ⇒ `P=primeAboveTwo/Three` (maximality via `span_*_eq`). (⇐) `dvd_differentIdeal_iff` via `ramificationIdx=2>1`. **Uses**: [`absNorm_differentIdeal_eq_twentyFour`, `eq_two_or_eq_three_…`, `span_two_eq`, `span_three_eq`, `ramificationIdx_primeAbove*`] — **Lines**: 1392-1462 — **Notes**: KEY — the different is supported exactly on the two ramified primes.

**File Summary**: The largest file; the arithmetic core. Establishes splitting behaviour for `ℚ(√-6)`:
`2,3` ramify (`(p)=primeAbove_p²`), `7` splits into *principal* primes `(1±θ)`, `5` splits into
*non-principal* primes `(5,θ∓2)`, `13` is inert; the general law `splits_iff_mod_twentyfour` (split ⇔
`p%24∈{1,5,7,11}` ⇔ `-6` square mod `p`), the inert law (`{13,17,19,23}`), `ramified_iff` (ramified ⇔
`p∈{2,3}`=disc divisors), and the different ideal (norm 24, supported on the ramified primes). The
non-principality witnesses `not_isPrincipal_primeAboveTwo` and `not_isPrincipal_primeAboveFive` live here.
Heavy use of `Common.lean` (`eq_of_le_of_absNorm_eq`, `eq_prime_of_dvd_prime_sq_…`,
`left_eq_prime_of_mul_eq_prime_sq_…`, `exists_int_inverse_mod_prime`, ramification helpers).

---

## ClassGroup.lean

Imports `PrimeSplitting.lean`. The class-group machinery (the headline of this case study).

### `abbrev thetaFractionalIdeal`
- **Type**: `FractionalIdeal (𝓞 K)⁰ K := spanSingleton θ`. **Uses**: [] — **Lines**: 31-32

### `abbrev primeAboveTwoFractionalIdeal` / `primeAboveThreeFractionalIdeal`
- **Type**: coercions of `primeAboveTwo`/`Three` to fractional ideals. **Uses**: [`primeAboveTwo`/`Three`] — **Lines**: 34-38

### `theorem theta_mem_fractionalIdeal`
- **Type**: `θ ∈ thetaFractionalIdeal`. **How**: `mem_spanSingleton_self`. **Uses**: [] — **Lines**: 40-42

### `theorem thetaFractionalIdeal_absNorm`
- **Type**: `absNorm = |Algebra.norm ℚ θ|`. **How**: `simp`. **Uses**: [] — **Lines**: 44-46

### `theorem ramifiedFractionalIdeals_ne_zero`
- **Type**: both ramified fractional ideals `≠ 0`. **How**: `coeIdeal_ne_zero` + `absNorm` nonzero. **Uses**: [`absNorm_primeAboveTwo`/`Three`] — **Lines**: 48-60

### `noncomputable def ramifiedIdealOverTwo`
- **Type**: `(Ideal (𝓞 K))⁰ := ⟨primeAboveTwo, …⟩`. **What**: `(2,θ)` as a nonzero ideal — concrete representative of the nontrivial class. **How**: `absNorm=2≠0`. **Uses**: [`absNorm_primeAboveTwo`] — **Lines**: 76-82 — **Notes**: KEY.

### `noncomputable def ramifiedIdealOverThree`
- **Type**: `⟨primeAboveThree, …⟩`. **What**: `(3,θ)` nonzero ideal (same class as `OverTwo`). **Uses**: [`absNorm_primeAboveThree`] — **Lines**: 84-90

### `abbrev unitIdealRepresentative`
- **Type**: `⟨⊤, …⟩`. **What**: representative of the trivial class. **Uses**: [] — **Lines**: 92-93

### `private theorem thetaInt_ne_zero`
- **Type**: `thetaInt ≠ 0`. **How**: else `θ=0` contradicts `theta_sq`. **Uses**: [`theta_sq`] — **Lines**: 95-100

### `private theorem minkowskiBound_lt_four`
- **Type**: Minkowski bound `< 4`. **How**: `(2/π)√24 < 4` via `√24<5` and `π>3` (`nlinarith`); plugs `nrComplexPlaces=1`, `finrank=2`, disc `-24`. **Uses**: [`nrRealPlaces_eq_zero`, `degree_eq_two`, `numberField_discr_eq`] — **Lines**: 102-123 — **Notes**: KEY — bounds the class-group representatives by norm `≤3`.

### `theorem classGroup_mk0_ramified_ne_one`
- **Type**: `ClassGroup.mk0 ramifiedIdealOverTwo ≠ 1`. **How**: `=1` would force `primeAboveTwo` principal (`mk0_eq_one_iff`), contradicting `not_isPrincipal_primeAboveTwo`. **Uses**: [`not_isPrincipal_primeAboveTwo`] — **Lines**: 125-132 — **Notes**: KEY — the class is nontrivial.

### `theorem classGroup_mk0_ramified_sq_eq_one`
- **Type**: `(ClassGroup.mk0 ramifiedIdealOverTwo)² = 1`. **What**: the nontrivial class has order dividing `2`. **How**: `mk0_eq_mk0_inv_iff` with witness `2` (since `(2,θ)²=(2)` principal ⇒ class is its own inverse). **Uses**: [`span_two_eq`] — **Lines**: 134-144 — **Notes**: KEY — `(2,θ)²` principal ⇒ class² trivial.

### `theorem orderOf_classGroup_mk0_ramified`
- **Type**: `orderOf = 2`. **How**: `orderOf_eq_prime` (sq=1, ≠1). **Uses**: [the two prior] — **Lines**: 146-151 — **Notes**: KEY — the class has order exactly `2`.

### `theorem class_mk0_primeAboveThree_eq_ramified`
- **Type**: class of `(3,θ)` = class of `(2,θ)`. **How**: `(2,θ)` self-inverse and `(2,θ)(3,θ)=(θ)` principal (`span_theta_eq`) ⇒ `(3,θ)` is the inverse of the inverse. **Uses**: [`span_two_eq`, `span_theta_eq`, `thetaInt_ne_zero`] — **Lines**: 153-170 — **Notes**: KEY — both ramified primes give the *same* nontrivial class.

### `private theorem classGroupRepresentatives_aux`
- **Type**: `∀ C, C=1 ∨ C=mk0 ramifiedIdealOverTwo`. **How**: `exists_ideal_in_class_of_norm_le`, `absNorm ≤ 3` (`minkowskiBound_lt_four`); `interval_cases` on norm `1,2,3` using `Ideal.absNorm_eq_one_iff`, `ideal_eq_primeAboveTwo/Three_of_absNorm_eq_*`, `class_mk0_primeAboveThree_eq_ramified`. **Uses**: [`minkowskiBound_lt_four`, the `ideal_eq_*` lemmas, `class_mk0_primeAboveThree_eq_ramified`] — **Lines**: 172-207 — **Notes**: KEY enumeration.

### `theorem classNumber_eq_two`
- **Type**: `NumberField.classNumber K = 2`. **What**: **THE headline result**. **How**: `Nat.card (ClassGroup) = 2` via `card_eq_two_iff` with `{1, mk0 ramifiedIdealOverTwo}`, completeness from `classGroupRepresentatives_aux`, nontriviality from `classGroup_mk0_ramified_ne_one`. **Uses**: [`classGroupRepresentatives_aux`, `classGroup_mk0_ramified_ne_one`] — **Lines**: 209-221 — **Notes**: KEY. Docstring states the full argument (Minkowski bound, primes 2,3, classes coincide & nontrivial via `(2,θ)(3,θ)=(θ)`).

### `theorem classGroupStructure`
- **Type**: `Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 2))`. **How**: `Nat.card=2` + `mulEquivOfPrimeCardEq`. **Uses**: [`classNumber_eq_two`] — **Lines**: 223-229 — **Notes**: KEY — class group `≅ ℤ/2`.

### `theorem classGroup_mk0_ramified_ne`
- **Type**: `mk0 ramifiedIdealOverTwo ≠ mk0 unitIdealRepresentative`. **How**: else `primeAboveTwo` principal, contradiction. **Uses**: [`not_isPrincipal_primeAboveTwo`] — **Lines**: 231-240

### `theorem classGroupRepresentatives`
- **Type**: `∀ C, C = mk0 unitIdealRepresentative ∨ C = mk0 ramifiedIdealOverTwo`. **How**: `Nat.card=2` + `card_eq_two_iff'`. **Uses**: [`classNumber_eq_two`, `classGroup_mk0_ramified_ne`] — **Lines**: 242-253

**File Summary**: The class-group headline. The nontrivial ideal class is exhibited concretely by
`ramifiedIdealOverTwo = (2,θ)`: nontrivial (`not_isPrincipal_primeAboveTwo`), order 2 (`(2,θ)²=(2)`
principal), and equal to the class of `(3,θ)` (because `(2,θ)(3,θ)=(θ)` is principal). The Minkowski
bound `<4` reduces enumeration to norms `1,2,3`, giving exactly two classes ⇒ `classNumber = 2`,
`ClassGroup ≅ ℤ/2`. Uses `ClassGroup.mk0`, `NumberField.classNumber`, `exists_ideal_in_class_of_norm_le`.

---

## Units.lean

Imports `ClassGroup.lean`. Unit group of the imaginary quadratic field.

### `abbrev torsionGenerator`
- **Type**: `(𝓞 K)ˣ := -1`. **What**: torsion generator (`-1`). **Uses**: [] — **Lines**: 33-34 — **Notes**: KEY (referenced in LocalGlobal too).

### `def torsionUnits`
- **Type**: `Set ((𝓞 K)ˣ) := {u | ∃ k:Fin 2, u = torsionGenerator^k.val}`. **What**: `{1,-1}`. **Uses**: [] — **Lines**: 36-37

### `theorem torsionUnits_eq`
- **Type**: `{u | IsOfFinOrder u} = torsionUnits`. **What**: torsion subgroup is exactly `{±1}`. **How**: unit ⇒ `x²+6y²=1` (`isUnit_iff_normForm`) ⇒ `y=0`, `x=±1` (`interval_cases`); conversely `(±1)²=1`. **Uses**: [`exists_eq_smul_one_add_smul_theta`, `isUnit_iff_normForm`] — **Lines**: 39-68 — **Notes**: KEY — no extra roots of unity (disc `≠ -3,-4`).

### `theorem torsionOrder_eq_two`
- **Type**: `NumberField.Units.torsionOrder K = 2`. **How**: `Nat.card (torsion) = 2` via `{1,-1}` distinct (`2≠0` in `K`); completeness from `torsionUnits_eq`. **Uses**: [`torsionUnits_eq`] — **Lines**: 70-96 — **Notes**: KEY — `μ_K = μ₂`.

### `theorem unitRank_eq_zero`
- **Type**: `NumberField.Units.rank K = 0`. **How**: `rank = #places - 1`; `nrRealPlaces=0`, `nrComplexPlaces=1`. **Uses**: [`nrRealPlaces_eq_zero`, `nrComplexPlaces_eq_one`] — **Lines**: 98-102 — **Notes**: KEY — Dirichlet rank `0` (no fundamental units), signature `(0,1)`.

### `theorem unit_eq_one_or_neg_one`
- **Type**: `∀ u:(𝓞 K)ˣ, u=1 ∨ u=-1`. **How**: `exist_unique_eq_mul_prod`; rank `0` ⇒ empty fundamental product ⇒ `u` is torsion ⇒ `torsionUnits_eq`. **Uses**: [`unitRank_eq_zero`, `torsionUnits_eq`] — **Lines**: 104-123 — **Notes**: KEY — finite unit group `{±1}`.

### `theorem unitGroupStructure`
- **Type**: `Nonempty ((𝓞 K)ˣ ≃* Multiplicative (ZMod 2))`. **How**: `Nat.card=2` (from `unit_eq_one_or_neg_one`) + `mulEquivOfPrimeCardEq`. **Uses**: [`unit_eq_one_or_neg_one`] — **Lines**: 125-140 — **Notes**: KEY — `(𝓞 K)ˣ ≅ μ₂`.

### `theorem regulator_eq_one`
- **Type**: `NumberField.Units.regulator K = 1`. **How**: `regulator_eq_det'`; rank `0` ⇒ empty `0×0` determinant `=1` (`det_eq_one_of_card_eq_zero`). **Uses**: [`unitRank_eq_zero`] — **Lines**: 142-158 — **Notes**: regulator trivially `1` (no Artin-bound issue, unlike the real fields).

**File Summary**: Unit group of the imaginary quadratic field. Positive-definite norm form ⇒ no Pell ⇒
unit group is just torsion `{±1} = μ₂`, rank `0`, regulator `1`. Contrast with the real-field case studies
where `isFundamental`/`regulator` are blocked on Artin-type bounds — here everything is fully proved
*because* there are no fundamental units. KEY exports: `torsionGenerator`, `torsionOrder_eq_two`,
`unitRank_eq_zero`, `unit_eq_one_or_neg_one`. (Trailing empty `## Regulator` section, Lines 162-172.)

---

## Euclidean.lean

Imports `Units.lean`. The non-PID / non-Euclidean negative results.

### `theorem not_isPrincipalIdealRing`
- **Type**: `¬ IsPrincipalIdealRing (𝓞 K)`. **What**: `ℤ[√-6]` is **not a PID**. **How**: a PID would make every ideal principal, contradicting `not_isPrincipal_primeAboveTwo` applied to `(2,θ)`. **Uses**: [`not_isPrincipal_primeAboveTwo`, `primeAboveTwo`] — **Lines**: 31-35 — **Notes**: KEY negative result.

### `theorem not_normEuclidean`
- **Type**: `¬ ∀ a b, b≠0 → ∃ q r, a = b*q+r ∧ |norm r| < |norm b|`. **What**: `ℤ[√-6]` is **not norm-Euclidean**. **How**: take `a=thetaInt`, `b=2`: any remainder `r=θ-2q` has coordinates `(-2x, 1-2y)` (odd second coordinate); `norm r = (-2x)²+6(1-2y)² ≥ 6 > 4 = |norm 2|` (`nlinarith`, since `(1-2y)²≥1`), contradicting the Euclidean inequality. **Uses**: [`thetaInt`, `intNorm_eq_normForm`, `exists_eq_smul_one_add_smul_theta`] — **Lines**: 37-79 — **Notes**: KEY negative result — explicit counterexample pair `(θ, 2)`; the property is stated *inline* (not via a mathlib `EuclideanDomain`/`NormEuclidean` typeclass).

**File Summary**: The two negative properties. `not_isPrincipalIdealRing` follows immediately from the
non-principal prime `(2,θ)`. `not_normEuclidean` is an explicit counterexample: dividing `θ` by `2` always
leaves a remainder of norm `≥6`, exceeding `|norm 2|=4`, because the second coordinate of any remainder is
forced odd. The non-Euclidean statement is phrased as a concrete `∀…∃…` over `𝓞 K` rather than a
named typeclass.

---

## UniqueFactorization.lean

Imports `Euclidean.lean`. The not-a-UFD negative result via the classic `6 = 2·3 = (√-6)(-√-6)`.

### `theorem six_eq_neg_theta_sq`
- **Type**: `(6 : 𝓞 K) = -(thetaInt * thetaInt)`. **What**: `6 = -√-6·√-6` — the second factorization of `6`. **How**: `thetaInt_sq` (`θ²=-6`). **Uses**: [`thetaInt_sq`] — **Lines**: 27-31 — **Notes**: KEY — half of the `6 = 2·3 = -θ²` non-unique factorization.

### `private theorem intNorm_two` / `intNorm_three` / `intNorm_thetaInt`
- **Type**: `norm(2)=4`, `norm(3)=9`, `norm(θ)=6`. **How**: `intNorm_eq_normForm`. **Uses**: [`intNorm_eq_normForm`] — **Lines**: 33-52

### `theorem irreducible_two`
- **Type**: `Irreducible (2 : 𝓞 K)`. **How**: not a unit (`norm 4≠1`); any factor norm divides `4`, is `≠1` (non-unit), `≠2` (`intNorm_ne_two`), so one factor has norm `1` ⇒ unit; `interval_cases`+`nlinarith`. **Uses**: [`intNorm_two`, `isUnit_iff_intNorm_eq_one`, `intNorm_ne_two`, `intNorm_nonneg`] — **Lines**: 54-91 — **Notes**: KEY — `2` irreducible (but not prime, below).

### `theorem irreducible_three`
- **Type**: `Irreducible (3 : 𝓞 K)`. **How**: twin (`norm 9`, `≠3` via `intNorm_ne_three`). **Uses**: [`intNorm_three`, `intNorm_ne_three`, …] — **Lines**: 93-135 — **Notes**: KEY.

### `theorem irreducible_theta`
- **Type**: `Irreducible thetaInt`. **How**: `norm 6 = 2·3`; factor norms must avoid `2` and `3` (`intNorm_ne_two/three`), so one is `1` ⇒ unit. **Uses**: [`intNorm_thetaInt`, `intNorm_ne_two`, `intNorm_ne_three`, …] — **Lines**: 137-180 — **Notes**: KEY — `√-6` irreducible, completing the two distinct irreducible factorizations of `6`.

### `theorem two_not_prime`
- **Type**: `¬ Prime (2 : 𝓞 K)`. **What**: `2` irreducible but **not prime**. **How**: `2 ∣ θ·θ = -6` but `2 ∤ θ` (else `θ∈(2)`, but `absNorm(2,θ)=2 ≠ 4=absNorm(2)`, so `(2,θ)≠(2)`); `dvd_or_dvd` fails. **Uses**: [`primeAboveTwo`, `absNorm_primeAboveTwo`, `intNorm_eq_normForm`, `thetaInt_sq`] — **Lines**: 182-218 — **Notes**: KEY — the explicit irreducible-not-prime element, the mechanism of UFD failure.

### `theorem not_uniqueFactorizationMonoid`
- **Type**: `¬ UniqueFactorizationMonoid (𝓞 K)`. **What**: `ℤ[√-6]` is **not a UFD**. **How**: a UFM Dedekind domain would be a PID (`IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid`), contradicting `not_isPrincipalIdealRing`. **Uses**: [`not_isPrincipalIdealRing`] — **Lines**: 220-225 — **Notes**: KEY negative result — stated as `¬ UniqueFactorizationMonoid`, proved cleanly via the Dedekind⇒(UFD⟺PID) bridge. The concrete `6=2·3=-θ²` counterexample (irreducibles `2,3,θ`, `2` not prime) is also fully formalised above as the *constructive* explanation.

**File Summary**: The not-a-UFD result, two ways. (1) Constructively: `6 = 2·3 = -(√-6)²` with `2,3,√-6`
all irreducible (norms `4,9,6`, none equal to a forbidden small norm) and `2` *not prime* (divides `θ²`
but not `θ`) — the textbook failure of unique factorization. (2) Abstractly: `not_uniqueFactorizationMonoid`
via the Dedekind-domain equivalence `UFM ⟺ PID`, reducing to the already-proved `not_isPrincipalIdealRing`.

---

## CMField.lean

Imports `Embeddings.lean`. CM-field structure (special topic).

### `theorem isCMField`
- **Type**: `NumberField.IsCMField K`. **How**: totally complex (`isTotallyComplex`) quadratic over `ℚ` ⇒ `IsCMField.ofCMExtension ℚ K`. **Uses**: [`isTotallyComplex`] — **Lines**: 26-28 — **Notes**: KEY — `ℚ(√-6)` is a CM field (imaginary quadratic).

### `theorem cmField_isTotallyComplex`
- **Type**: `NumberField.IsTotallyComplex K`. **How**: `isTotallyComplex`. **Uses**: [`isTotallyComplex`] — **Lines**: 30-31

### `theorem cmField_quadratic_over_maximalRealSubfield`
- **Type**: `IsQuadraticExtension (maximalRealSubfield K) K`. **How**: `IsCMField.isQuadraticExtension` (max real subfield is `ℚ`). **Uses**: [`isCMField`] — **Lines**: 33-36

### `theorem cmField_unitsRank_eq_maximalRealSubfield`
- **Type**: `Units.rank (maximalRealSubfield K) = Units.rank K`. **How**: `IsCMField.units_rank_eq_units_rank`. **Uses**: [`isCMField`] — **Lines**: 38-42 — **Notes**: both ranks `0` (CM ⇒ same unit rank as max real subfield `ℚ`).

**File Summary**: Records that `ℚ(√-6)` is a CM field (a totally complex quadratic extension of the totally
real `ℚ`). Thin wrapper over mathlib's `NumberField.IsCMField` API: CM structure, quadratic over the
maximal real subfield, and equal unit ranks. Depends only on `isTotallyComplex` from Embeddings.

---

## LocalGlobal.lean

Imports `Euclidean.lean`. Finite/infinite places, completions, product formula, canonical embedding,
adeles, zeta — mostly `example`s exercising mathlib's local-global API on this field.

### `def heightOneTwo` / `heightOneThree`
- **Type**: `HeightOneSpectrum (𝓞 K)` with `asIdeal = primeAboveTwo`/`Three`. **What**: the finite places over `2`/`3`, *represented by the non-principal ramified primes*. **How**: `isPrime_*`, `ne_bot` from nonzero `absNorm`. **Uses**: [`isPrime_primeAboveTwo`/`Three`, `absNorm_primeAboveTwo`/`Three`] — **Lines**: 34-54 — **Notes**: notable — `HeightOneSpectrum` accommodates non-principal primes seamlessly.

### `abbrev vTwo` / `vThree`
- **Type**: `NumberField.FinitePlace K := FinitePlace.mk heightOne*`. **Uses**: [`heightOne*`] — **Lines**: 56-60

### `example` (×4): ramification/inertia of `vTwo`, `vThree`
- ramificationIdx `2` (×2), inertiaDeg `1` (×2). **How**: the `PrimeSplitting` ramification/inertia lemmas. **Uses**: [`ramificationIdx_primeAbove*`, `inertiaDeg_primeAbove*`] — **Lines**: 62-76

### `abbrev CompletionAtTwo` / `CompletionAtThree`
- **Type**: `heightOne*.adicCompletion K`. **Uses**: [`heightOne*`] — **Lines**: 90-94

### `abbrev InfiniteCompletion`
- **Type**: `(v : InfinitePlace K) → v.Completion`. **Uses**: [] — **Lines**: 108-109

### `example`: `Nonempty (InfiniteCompletion v ≃+* ℂ)`
- **How**: `Completion.ringEquivComplexOfIsComplex` + `infinitePlace_isComplex`. **Uses**: [`infinitePlace_isComplex`] — **Lines**: 111-114 — **Notes**: every infinite completion is `ℂ`.

### `example` (×2): product formula for `θ` and for `torsionGenerator`
- `(∏ infinite places)·(∏ finite places) = 1`. **How**: `NumberField.prod_abs_eq_one`. **Uses**: [`theta_sq`, `torsionGenerator`] — **Lines**: 128-146

### `abbrev SqrtNegSixInfiniteAdeleRing`, `infinitePrincipalAdele_theta`, `infinitePrincipalAdele_torsionGenerator`
- infinite adele ring and two principal adeles. **Uses**: [`θ`, `torsionGenerator`] — **Lines**: 159-166

### `example` (×2): infinite-adele norm of `θ`; dense range of `K`
- `‖·‖ = |norm ℚ θ|`; `DenseRange (algebraMap K …)`. **How**: `coe_norm_eq_abs_norm`, `denseRange_algebraMap`. **Uses**: [] — **Lines**: 168-174

### `theorem canonicalEmbedding_thetaInt_mem_integerLattice`
- **Type**: `canonicalEmbedding K (algebraMap thetaInt) ∈ integerLattice K`. **How**: `simp`. **Uses**: [`thetaInt`] — **Lines**: 188-191

### `abbrev mixedEmbedding_theta`
- **Type**: `mixedEmbedding.mixedSpace K := mixedEmbedding K θ`. **Uses**: [`θ`] — **Lines**: 207-208

### `theorem mixedEmbedding_theta_mem_convexBodyLT`
- **Type**: if `∀ w, w θ < f w` then `mixedEmbedding_theta ∈ convexBodyLT K f`. **How**: unfold convex-body membership; only complex places (`infinitePlace_isComplex`), `norm_embedding_eq`. **Uses**: [`infinitePlace_isComplex`] — **Lines**: 210-223

### `example` (×2): measurability of `fundamentalCone`, `normLeOne`
- **How**: `measurableSet_fundamentalCone`, `measurableSet_normLeOne`. **Uses**: [] — **Lines**: 225-231

### `theorem polarSpace_nonempty`
- **Type**: `Nonempty (polarSpace K)`. **How**: `infer_instance`. **Uses**: [] — **Lines**: 233-235

### `example`: `0 < house θ`
- **How**: `one_le_house_of_isIntegral theta_integral`. **Uses**: [`theta_integral`, `theta_sq`] — **Lines**: 249-256

### `theorem house_torsionGenerator`
- **Type**: `house (algebraMap torsionGenerator) = 1`. **How**: `house_intCast (-1)`. **Uses**: [`torsionGenerator`] — **Lines**: 258-260

### `abbrev SqrtNegSixAdeleRing`, `principalAdele_theta`, `principalAdele_torsionGenerator`
- the adele ring `AdeleRing (𝓞 K) K` and two principal adeles. **Uses**: [`θ`, `torsionGenerator`] — **Lines**: 275-282

### `theorem principalAdele_theta_ne_zero`
- **Type**: `principalAdele_theta ≠ 0`. **How**: `AdeleRing.algebraMap_injective` + `theta_sq`. **Uses**: [`theta_sq`] — **Lines**: 284-290

### `theorem principalAdele_torsionGenerator_is_unit_everywhere`
- **Type**: `∀ v finite place, v (algebraMap torsionGenerator) = 1`. **How**: `simp [torsionGenerator]` (`-1` is a unit everywhere). **Uses**: [`torsionGenerator`] — **Lines**: 292-296

### `abbrev sqrtNegSixDedekindZeta`, `sqrtNegSixDedekindZetaResidue`
- `dedekindZeta K s` and its residue. **Uses**: [] — **Lines**: 310-314

### `example` (×2): residue positive; residue class-number formula
- `0 < residue`; residue `= (2^r₁(2π)^r₂ · reg · h)/(w·√|disc|)`. **How**: `dedekindZeta_residue_pos`, `dedekindZeta_residue_def`. **Uses**: [] — **Lines**: 316-326 — **Notes**: the analytic class-number formula instantiated; all ingredients (`reg=1`, `h=2`, `w=2`, `disc=-24`) are proven elsewhere.

**File Summary**: Exercises mathlib's local-global / adelic / analytic API on `ℚ(√-6)`. Notable that the
finite places over the ramified `2,3` are represented by `HeightOneSpectrum` carrying the *non-principal*
prime ideals — the non-PID nature causes no friction here. Mostly `example`s confirming completions are `ℂ`,
product formula, canonical/mixed embeddings, house, adeles, and the Dedekind-zeta residue class-number
formula. Depends on `torsionGenerator`, `theta`/`theta_sq`, and the splitting/ramification data.

---

## Overall

Sorry-free across all 11 files. The case study is the project's unique **non-PID / non-UFD / non-Euclidean**
example, and all three negative results are fully formalised: class number `2` and `ClassGroup ≅ ℤ/2`
(`ClassGroup.lean`), `¬ IsPrincipalIdealRing` and `¬ normEuclidean` (`Euclidean.lean`), `¬ UniqueFactorizationMonoid`
plus the constructive `6 = 2·3 = -(√-6)²` counterexample (`UniqueFactorization.lean`). The whole edifice
rests on the positive-definite norm form `x²+6y²` (no Pell, no fundamental units) and the non-principal
ramified prime `(2,θ)` exhibited via the unsolvability of `x²+6y² = 2`. Unlike the real-field case studies,
nothing is blocked on Artin-type unit bounds — `regulator` and the unit structure are trivial here.
