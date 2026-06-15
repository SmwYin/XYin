# CubeRootThree declaration inventory

Folder: `XYin/NumberField/FieldExamples/CubeRootThree/`
Field: `K = ℚ(∛3) = AdjoinRoot (X³ - 3)`, generator `θ = ∛3`.
Shared helpers live in `XYin/NumberField/FieldExamples/Common.lean` (namespace `NumberField.FieldExamples`).

All declarations are in namespace `NumberField.CubeRootThree` unless noted.

---

## Basic.lean

### `abbrev cubePolynomial`
- **Type**: `cubePolynomial : ℚ[X] := X ^ 3 - C (3 : ℚ)`
- **What**: The defining polynomial `X³ - 3` of `ℚ(∛3)`.
- **How**: Definitional abbrev.
- **Hypotheses**: none
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 31-32
- **Notes**: —

### `instance : Fact (Irreducible cubePolynomial)`
- **Type**: `Fact (Irreducible cubePolynomial)`
- **What**: `X³ - 3` is irreducible over `ℚ`.
- **How**: `X_pow_sub_C_irreducible_of_prime`; reduce to "3 has no rational cube root" via `IsIntegrallyClosed.isIntegral_iff`, then `interval_cases`/`omega` over divisors of 3.
- **Hypotheses**: none
- **Uses from project**: []
- **Visibility**: public (instance)
- **Lines**: 34-50
- **Notes**: —

### `abbrev K`
- **Type**: `K : Type := AdjoinRoot cubePolynomial`
- **What**: The number field `ℚ(∛3)`.
- **Uses from project**: [`cubePolynomial`]
- **Visibility**: public
- **Lines**: 52-53

### `abbrev cubeRootThree`
- **Type**: `cubeRootThree : K := AdjoinRoot.root cubePolynomial`
- **What**: The distinguished root `θ = ∛3`.
- **Uses from project**: [`cubePolynomial`, `K`]
- **Visibility**: public
- **Lines**: 55-56

### `instance : Field K`, `instance : NumberField K`
- **Type**: `Field K`, `NumberField K`
- **What**: Field and number-field structures on `K`.
- **How**: `infer_instance`.
- **Uses from project**: [`K`]
- **Visibility**: public (instances)
- **Lines**: 58-64

### `theorem cubePolynomial_ne_zero`
- **Type**: `cubePolynomial ≠ 0`
- **What**: The defining polynomial is nonzero.
- **How**: `congrArg natDegree` (its degree is 3 ≠ 0). NOTE: this exact one-liner is inlined ~7× elsewhere as `by intro h; simpa using congrArg natDegree h` rather than reusing this lemma.
- **Uses from project**: [`cubePolynomial`]
- **Visibility**: public
- **Lines**: 67-69

### `abbrev cubeRootThreePowerBasis`
- **Type**: `PowerBasis ℚ K := AdjoinRoot.powerBasis cubePolynomial_ne_zero`
- **What**: The power basis `1, θ, θ²`.
- **Uses from project**: [`cubePolynomial_ne_zero`, `K`]
- **Visibility**: public
- **Lines**: 71-73

### `theorem cubeRootThreePowerBasis_gen` (`@[simp]`)
- **Type**: `cubeRootThreePowerBasis.gen = cubeRootThree`
- **How**: `AdjoinRoot.powerBasis_gen`.
- **Uses from project**: [`cubeRootThreePowerBasis`, `cubeRootThree`, `cubePolynomial_ne_zero`]
- **Visibility**: public
- **Lines**: 75-77

### `theorem cubeRootThreePowerBasis_dim`
- **Type**: `cubeRootThreePowerBasis.dim = 3`
- **How**: `AdjoinRoot.powerBasis_dim` + `natDegree_X_pow_sub_C`.
- **Uses from project**: [`cubeRootThreePowerBasis`, `cubePolynomial_ne_zero`]
- **Visibility**: public
- **Lines**: 79-81

### `theorem degree_eq_three`  ★ headline
- **Type**: `Module.finrank ℚ K = 3`
- **What**: `[K : ℚ] = 3`.
- **How**: `PowerBasis.finrank` + `cubeRootThreePowerBasis_dim`.
- **Uses from project**: [`cubeRootThreePowerBasis`, `cubeRootThreePowerBasis_dim`]
- **Visibility**: public
- **Lines**: 83-86

### `theorem cubeRootThree_cube`
- **Type**: `cubeRootThree ^ 3 = 3`
- **What**: `θ³ = 3`.
- **How**: `AdjoinRoot.mk_self` then `linear_combination`. Heavily reused across the folder.
- **Uses from project**: [`cubeRootThree`, `cubePolynomial`]
- **Visibility**: public
- **Lines**: 88-92

### `theorem cubeRootThree_minpoly_rat`
- **Type**: `minpoly ℚ cubeRootThree = cubePolynomial`
- **How**: `AdjoinRoot.minpoly_root` and irreducibility.
- **Uses from project**: [`cubeRootThree`, `cubePolynomial`]
- **Visibility**: public
- **Lines**: 94-99
- **Notes**: appears unused inside this folder (RingOfIntegers/Discriminant re-derive minpoly).

### `theorem adjoin_cubeRootThree_eq_top`
- **Type**: `Algebra.adjoin ℚ {cubeRootThree} = ⊤`
- **How**: `PowerBasis.adjoin_gen_eq_top`.
- **Uses from project**: [`cubeRootThreePowerBasis`, `cubeRootThreePowerBasis_gen`, `cubeRootThree`]
- **Visibility**: public
- **Lines**: 101-104
- **Notes**: appears unused in folder.

**File Summary — Basic.lean**: 5 abbrevs, 7 theorems, 2 instances + 1 Fact-instance. Key API used by 3+: `K`, `cubeRootThree`, `cubePolynomial`, `cubeRootThree_cube`, `degree_eq_three`. Likely unused: `cubeRootThree_minpoly_rat`, `adjoin_cubeRootThree_eq_top`. No sorry, no set_option, no proof >30 lines.

---

## Galois.lean

### `def idAut`
- **Type**: `K ≃ₐ[ℚ] K := AlgEquiv.refl`
- **What**: identity automorphism.
- **Uses from project**: [`K`]
- **Visibility**: public
- **Lines**: 31-32

### `theorem no_primitive_cube_root`
- **Type**: `(z : K) → z ^ 2 + z + 1 ≠ 0`
- **What**: `K` has no primitive cube root of unity.
- **How**: `Φ₃ = X²+X+1` is irreducible (`cyclotomic_prime`, `cyclotomic.irreducible_rat`); a root would force `minpoly` of degree 2 | finrank 3.
- **Uses from project**: [`degree_eq_three`, `K`]
- **Visibility**: public
- **Lines**: 34-49

### `theorem cube_root_one`
- **Type**: `(w : K) → w ^ 3 = 1 → w = 1`
- **How**: factor `w³-1 = (w-1)(w²+w+1)`, second factor nonzero by `no_primitive_cube_root`.
- **Uses from project**: [`no_primitive_cube_root`]
- **Visibility**: public
- **Lines**: 51-56

### `theorem aut_eq_id`
- **Type**: `(σ : K ≃ₐ[ℚ] K) → σ = idAut`
- **What**: every ℚ-automorphism is the identity.
- **How**: `σθ` is a cube root of 3, ratio to `θ` is a cube root of 1 = 1 (`cube_root_one`); then `AdjoinRoot.algHom_ext`.
- **Uses from project**: [`cubeRootThree_cube`, `cube_root_one`, `idAut`, `cubeRootThree`]
- **Visibility**: public
- **Lines**: 58-72

### `theorem not_isGalois`  ★ headline
- **Type**: `¬ IsGalois ℚ K`
- **How**: `IsGalois.card_aut_eq_finrank`: would force `Nat.card aut = 3`, but `aut` is subsingleton (`aut_eq_id`); `omega`.
- **Uses from project**: [`degree_eq_three`, `aut_eq_id`, `idAut`]
- **Visibility**: public
- **Lines**: 74-83

### `theorem galoisGroupStructure`
- **Type**: `Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 1))`
- **How**: `Unique` aut group via `aut_eq_id`, `MulEquiv.ofUnique`.
- **Uses from project**: [`idAut`, `aut_eq_id`]
- **Visibility**: public
- **Lines**: 85-88

### `abbrev galoisClosure`
- **Type**: `Type := cubePolynomial.SplittingField`
- **Uses from project**: [`cubePolynomial`]
- **Visibility**: public
- **Lines**: 90-92

### `theorem isGalois_galoisClosure`
- **Type**: `IsGalois ℚ galoisClosure`
- **How**: `IsGalois.of_separable_splitting_field` + separability of irreducible in char 0.
- **Uses from project**: [`galoisClosure`, `cubePolynomial`]
- **Visibility**: public
- **Lines**: 94-100

### `theorem nonempty_algHom_galoisClosure`
- **Type**: `Nonempty (K →ₐ[ℚ] galoisClosure)`
- **How**: pick a root of `X³-3` in splitting field (`exists_eval_eq_zero`), use `AdjoinRoot.liftAlgHom`.
- **Uses from project**: [`K`, `galoisClosure`, `cubePolynomial`]
- **Visibility**: public
- **Lines**: 102-111

### `theorem galoisClosureGroupStructure`  ★ headline
- **Type**: `Nonempty ((galoisClosure ≃ₐ[ℚ] galoisClosure) ≃* Equiv.Perm (Fin 3))`
- **What**: Galois group of closure is `S₃`.
- **How**: prime-degree irreducible with exactly 2 non-real roots; counts `rootSet ℂ = 3`, `rootSet ℝ = 1` then `Polynomial.Gal.galActionHom_bijective_of_prime_degree`.
- **Uses from project**: [`cubePolynomial`, `galoisClosure`]
- **Visibility**: public
- **Lines**: 113-148
- **Notes**: proof >30 lines (uses `Real.rpow_natCast`, `Odd.strictMono_pow`).

### `theorem finrank_galoisClosure`
- **Type**: `Module.finrank ℚ galoisClosure = 6`
- **How**: Galois ⇒ finrank = |Gal| = |S₃| = 6 via `galoisClosureGroupStructure`, `Fintype.card_perm`.
- **Uses from project**: [`galoisClosure`, `isGalois_galoisClosure`, `galoisClosureGroupStructure`]
- **Visibility**: public
- **Lines**: 150-158

**File Summary — Galois.lean**: 1 def, 8 theorems, 2 abbrevs. Key API (3+): `aut_eq_id`, `idAut`, `galoisClosure`, `degree_eq_three`(imported). Possibly unused downstream: `galoisGroupStructure`, `nonempty_algHom_galoisClosure`, `finrank_galoisClosure`. No sorry/set_option. 1 proof >30 lines (`galoisClosureGroupStructure`).

---

## Embeddings.lean

### `theorem not_totallyReal`
- **Type**: `¬ NumberField.IsTotallyReal K`
- **How**: build a complex root of `X³-3` with nonzero imaginary part (`c₀ζ`), produce embedding `K →+* ℂ` via `AdjoinRoot.lift`; totally-real would force it real (`ComplexEmbedding.isReal_iff`), contradiction.
- **Uses from project**: [`cubePolynomial`, `cubeRootThree`, `K`]
- **Visibility**: public
- **Lines**: 34-68
- **Notes**: proof >30 lines.

### `theorem nrComplexPlaces_eq_one`  ★ headline
- **Type**: `InfinitePlace.nrComplexPlaces K = 1`
- **How**: signature equation `r₁ + 2r₂ = 3` (`card_add_two_mul_card_eq_rank`), `r₂ ≠ 0` from `not_totallyReal`, `omega`.
- **Uses from project**: [`degree_eq_three`, `not_totallyReal`]
- **Visibility**: public
- **Lines**: 70-76

### `theorem nrRealPlaces_eq_one`  ★ headline
- **Type**: `InfinitePlace.nrRealPlaces K = 1`
- **How**: same signature equation + `nrComplexPlaces_eq_one`, `omega`.
- **Uses from project**: [`degree_eq_three`, `nrComplexPlaces_eq_one`]
- **Visibility**: public
- **Lines**: 78-83

### `theorem infinitePlace_card_eq_two`
- **Type**: `Fintype.card (InfinitePlace K) = 2`
- **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces` + the two place counts.
- **Uses from project**: [`nrRealPlaces_eq_one`, `nrComplexPlaces_eq_one`]
- **Visibility**: public
- **Lines**: 97-100

### `theorem infinitePlace_signature`
- **Type**: `nrRealPlaces K = 1 ∧ nrComplexPlaces K = 1`
- **Uses from project**: [`nrRealPlaces_eq_one`, `nrComplexPlaces_eq_one`]
- **Visibility**: public
- **Lines**: 102-105
- **Notes**: unused in folder.

### `theorem exists_realEmbedding_cubeRootThree`
- **Type**: `∃ σ : K →ₐ[ℚ] ℝ, σ cubeRootThree = (3:ℝ)^(1/3)`
- **How**: `AdjoinRoot.liftAlgHom` with the real cube root; `Real.rpow_natCast`/`rpow_mul`.
- **Uses from project**: [`cubePolynomial`, `cubeRootThree`, `K`]
- **Visibility**: public
- **Lines**: 107-117

### `theorem exists_complexEmbedding_cubeRootThree`
- **Type**: `∃ σ : K →+* ℂ, σ cubeRootThree ^ 3 = 3`
- **How**: compose the real embedding with `Complex.ofRealHom`.
- **Uses from project**: [`exists_realEmbedding_cubeRootThree`, `cubeRootThree`]
- **Visibility**: public
- **Lines**: 119-128
- **Notes**: unused in folder.

**File Summary — Embeddings.lean**: 7 theorems. Key API (3+): `nrComplexPlaces_eq_one`, `nrRealPlaces_eq_one`, `not_totallyReal`, `infinitePlace_card_eq_two`, `exists_realEmbedding_cubeRootThree`. Unused: `infinitePlace_signature`, `exists_complexEmbedding_cubeRootThree`. No sorry/set_option. 1 proof >30 lines (`not_totallyReal`). NOTE: `attribute [-instance] DivisionRing.toRatAlgebra` is set in first section.

---

## RingOfIntegers.lean

### `theorem cubeRootThree_integral`
- **Type**: `cubeRootThree ∈ integralClosure ℤ K`
- **How**: root of monic `X³ - C 3`.
- **Uses from project**: [`cubeRootThree`, `cubeRootThree_cube`]
- **Visibility**: public
- **Lines**: 31-38

### `def thetaInt`
- **Type**: `𝓞 K := ⟨cubeRootThree, cubeRootThree_integral⟩`
- **What**: `θ` as an element of `𝓞 K`. Central object reused folder-wide.
- **Uses from project**: [`cubeRootThree`, `cubeRootThree_integral`]
- **Visibility**: public
- **Lines**: 40-41

### `theorem thetaInt_cube`
- **Type**: `thetaInt ^ 3 = 3` (in `𝓞 K`)
- **How**: push through `algebraMap (𝓞 K) K` (`RingOfIntegers.map_mk`), use `cubeRootThree_cube`, injectivity.
- **Uses from project**: [`thetaInt`, `cubeRootThree`, `cubeRootThree_integral`, `cubeRootThree_cube`]
- **Visibility**: public
- **Lines**: 43-49
- **Notes**: heavily reused.

### `def integralBasisVectors`
- **Type**: `Fin 3 → K := ![1, cubeRootThree, cubeRootThree ^ 2]`
- **Uses from project**: [`cubeRootThree`]
- **Visibility**: public
- **Lines**: 51-52

### `theorem mem_adjoin_iff`
- **Type**: `x ∈ Algebra.adjoin ℤ {cubeRootThree} ↔ ∃ a b c : ℤ, x = a•1 + b•θ + c•θ²`
- **How**: `Algebra.adjoin_induction`; multiplication case uses `θ³=3`, `θ⁴=3θ` and `ring`.
- **Uses from project**: [`cubeRootThree`, `cubeRootThree_cube`]
- **Visibility**: public
- **Lines**: 54-88
- **Notes**: proof >30 lines.

### `theorem span_adjoin_eq`
- **Type**: `Subalgebra.toSubmodule (Algebra.adjoin ℤ {θ}) = Submodule.span ℤ (range integralBasisVectors)`
- **How**: double inclusion via `mem_adjoin_iff` and `Submodule.span_induction`.
- **Uses from project**: [`mem_adjoin_iff`, `integralBasisVectors`, `cubeRootThree`]
- **Visibility**: public
- **Lines**: 90-120

### `theorem norm_eq_normForm`
- **Type**: `Algebra.norm ℚ (x•1 + y•θ + z•θ²) = x³ + 3y³ + 9z³ - 9xyz`
- **What**: explicit cubic norm form in the power basis.
- **How**: compute `leftMulMatrix θ = companion matrix`, then `Algebra.norm_eq_matrix_det`, `Matrix.det_fin_three`.
- **Uses from project**: [`cubePolynomial`, `cubeRootThree`, `cubeRootThree_cube`]
- **Visibility**: public
- **Lines**: 122-162
- **Notes**: proof >30 lines. Core reusable engine.

### `theorem discr_powerBasis_eq`
- **Type**: `Algebra.discr ℚ (AdjoinRoot.powerBasis _).basis = -243`
- **How**: `Algebra.discr_powerBasis_eq_norm`, `minpoly` derivative `3X²`, `norm_eq_normForm 0 0 3`.
- **Uses from project**: [`cubePolynomial`, `cubeRootThree`, `degree_eq_three`, `norm_eq_normForm`]
- **Visibility**: public
- **Lines**: 164-190
- **Notes**: proof >30 lines.

### `theorem three_dvd_of_normForm_eq`
- **Type**: `(a b c m : ℤ) → a³+3b³+9c³-9abc = 27m → 3∣a ∧ 3∣b ∧ 3∣c`
- **How**: pure ℤ descent using `Int.prime_three`, `Prime.dvd_of_dvd_pow`, `mul_left_cancel₀`, `linear_combination`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 192-212
- **Notes**: GENERIC-looking ℤ lemma (no field content). proof >10 lines.

### `theorem exists_intCast_norm`
- **Type**: `(z : K) → IsIntegral ℤ z → ∃ m : ℤ, Algebra.norm ℚ z = m`
- **How**: `Algebra.isIntegral_norm` + `IsIntegrallyClosed.isIntegral_iff`.
- **Uses from project**: [`K`]
- **Visibility**: public
- **Lines**: 214-219
- **Notes**: GENERIC (works for any number field).

### `theorem peel`
- **Type**: `(z : K) → IsIntegral ℤ z → 3*z ∈ ℤ[θ] → z ∈ ℤ[θ]`
- **What**: the index-peeling step at p=3.
- **How**: write `3z = a+bθ+cθ²`, norm of `3z` is `27m`, apply `three_dvd_of_normForm_eq` then cancel.
- **Uses from project**: [`mem_adjoin_iff`, `exists_intCast_norm`, `norm_eq_normForm`, `three_dvd_of_normForm_eq`, `degree_eq_three`, `cubeRootThree`]
- **Visibility**: public
- **Lines**: 221-246
- **Notes**: proof >10 lines.

### `theorem integralClosure_eq_adjoin`  ★ headline
- **Type**: `integralClosure ℤ K = Algebra.adjoin ℤ {cubeRootThree}`
- **What**: `𝓞 K = ℤ[θ]` (monogenic).
- **How**: `Algebra.discr_mul_isIntegral_mem_adjoin` puts `243·z ∈ ℤ[θ]`, then 5 rounds of `peel`.
- **Uses from project**: [`cubePolynomial`, `cubeRootThree`, `discr_powerBasis_eq`, `peel`, `cubeRootThree_integral`]
- **Visibility**: public
- **Lines**: 248-287
- **Notes**: proof >30 lines.

### `theorem span_integralBasisVectors_eq`
- **Type**: `Submodule.span ℤ (range integralBasisVectors) = Subalgebra.toSubmodule (integralClosure ℤ K)`
- **Uses from project**: [`integralClosure_eq_adjoin`, `span_adjoin_eq`, `integralBasisVectors`]
- **Visibility**: public
- **Lines**: 289-296

### `def integralBasisVectorsInt`
- **Type**: `Fin 3 → 𝓞 K := ![1, thetaInt, thetaInt ^ 2]`
- **Uses from project**: [`thetaInt`]
- **Visibility**: public
- **Lines**: 298-299

### `def ringOfIntegersLinearMap`
- **Type**: `𝓞 K →ₗ[ℤ] K := (Algebra.linearMap (𝓞 K) K).restrictScalars ℤ`
- **Uses from project**: [`K`]
- **Visibility**: public
- **Lines**: 301-303
- **Notes**: GENERIC (no field content).

### `theorem ringOfIntegersLinearMap_injective`
- **Type**: `Function.Injective ringOfIntegersLinearMap`
- **How**: `FaithfulSMul.algebraMap_injective`.
- **Uses from project**: [`ringOfIntegersLinearMap`]
- **Visibility**: public
- **Lines**: 305-307
- **Notes**: GENERIC.

### `theorem algebraMap_integralBasisVectorsInt`
- **Type**: `(fun i => algebraMap (𝓞 K) K (integralBasisVectorsInt i)) = integralBasisVectors`
- **Uses from project**: [`integralBasisVectorsInt`, `integralBasisVectors`, `thetaInt`, `cubeRootThree`, `cubeRootThree_integral`]
- **Visibility**: public
- **Lines**: 309-315

### `theorem linearIndependent_integralBasisVectorsInt`
- **Type**: `LinearIndependent ℤ integralBasisVectorsInt`
- **How**: ℚ-independence of power basis → `restrict_scalars'` → `of_comp` along the injective `ringOfIntegersLinearMap`.
- **Uses from project**: [`cubePolynomial`, `cubeRootThree`, `integralBasisVectors`, `algebraMap_integralBasisVectorsInt`, `ringOfIntegersLinearMap`]
- **Visibility**: public
- **Lines**: 317-335
- **Notes**: proof >10 lines.

### `theorem span_integralBasisVectorsInt_eq_top`
- **Type**: `Submodule.span ℤ (range integralBasisVectorsInt) = ⊤`
- **How**: map through injective linear map, `span_integralBasisVectors_eq`.
- **Uses from project**: [`ringOfIntegersLinearMap_injective`, `integralBasisVectorsInt`, `integralBasisVectors`, `span_integralBasisVectors_eq`, `algebraMap_integralBasisVectorsInt`, `ringOfIntegersLinearMap`]
- **Visibility**: public
- **Lines**: 337-351

### `def concreteIntegralBasis`  ★ headline
- **Type**: `Basis (Fin 3) ℤ (𝓞 K) := Basis.mk _ _`
- **What**: integral basis `1, θ, θ²` of `𝓞 K`.
- **Uses from project**: [`linearIndependent_integralBasisVectorsInt`, `span_integralBasisVectorsInt_eq_top`]
- **Visibility**: public
- **Lines**: 353-356

### `theorem concreteIntegralBasis_apply`
- **Type**: `algebraMap (𝓞 K) K (concreteIntegralBasis i) = integralBasisVectors i`
- **Uses from project**: [`concreteIntegralBasis`, `integralBasisVectors`, `algebraMap_integralBasisVectorsInt`]
- **Visibility**: public
- **Lines**: 358-362
- **Notes**: unused in folder.

### `theorem span_integralBasisVectors_eq_integralBasis`
- **Type**: `span ℤ (range integralBasisVectors) = span ℤ (range (NumberField.integralBasis K))`
- **How**: both equal `toSubmodule (𝓞 K)` via `mem_span_integralBasis`.
- **Uses from project**: [`span_integralBasisVectors_eq`, `integralBasisVectors`]
- **Visibility**: public
- **Lines**: 364-377

### `abbrev concreteRingOfIntegers`
- **Type**: `Subalgebra ℤ K := Algebra.adjoin ℤ {cubeRootThree}`
- **Uses from project**: [`cubeRootThree`]
- **Visibility**: public
- **Lines**: 379-380

### `theorem ringOfIntegers_eq`  ★ headline
- **Type**: `integralClosure ℤ K = concreteRingOfIntegers`
- **Uses from project**: [`integralClosure_eq_adjoin`, `concreteRingOfIntegers`]
- **Visibility**: public
- **Lines**: 382-385

### `theorem intNorm_eq_normForm`
- **Type**: `Algebra.norm ℤ (x•1 + y•θ + z•θ²) = x³+3y³+9z³-9xyz` (`x,y,z : ℤ`)
- **How**: cast to ℚ via `Algebra.coe_norm_int`, reduce to `norm_eq_normForm`.
- **Uses from project**: [`thetaInt`, `cubeRootThree`, `cubeRootThree_integral`, `norm_eq_normForm`]
- **Visibility**: public
- **Lines**: 400-413
- **Notes**: The workhorse for all PrimeSplitting norm computations.

### `theorem isUnit_iff_normForm`
- **Type**: `IsUnit (x•1+y•θ+z•θ²) ↔ normForm = 1 ∨ normForm = -1`
- **How**: `NumberField.isUnit_iff_norm`, `intNorm_eq_normForm`, `abs_eq`.
- **Uses from project**: [`thetaInt`, `intNorm_eq_normForm`]
- **Visibility**: public
- **Lines**: 415-431
- **Notes**: unused in folder (advertised "cubic Pell equation").

**File Summary — RingOfIntegers.lean**: 8 defs, 17 theorems. Key API (3+): `thetaInt`, `thetaInt_cube`, `norm_eq_normForm`, `intNorm_eq_normForm`, `integralBasisVectors`, `concreteIntegralBasis`, `integralClosure_eq_adjoin`. Unused: `concreteIntegralBasis_apply`, `isUnit_iff_normForm`. No sorry/set_option. Proofs >30 lines: `mem_adjoin_iff`, `norm_eq_normForm`, `integralClosure_eq_adjoin` (and `span_adjoin_eq` near 30). GENERIC candidates: `three_dvd_of_normForm_eq`, `exists_intCast_norm`, `ringOfIntegersLinearMap`(+_injective).

---

## Discriminant.lean

### `theorem numberField_discr_eq`  ★ headline
- **Type**: `NumberField.discr K = -243`
- **How**: change-of-basis to power basis is integral both ways (`Basis.toMatrix`, `mem_span_iff_repr_mem`), `Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral`, then `discr_powerBasis_eq`.
- **Uses from project**: [`cubePolynomial`, `cubeRootThree`, `integralBasisVectors`, `span_integralBasisVectors_eq_integralBasis`, `discr_powerBasis_eq`]
- **Visibility**: public
- **Lines**: 33-71
- **Notes**: proof >30 lines.

### `theorem integralBasis_discr`
- **Type**: `Algebra.discr ℚ (NumberField.integralBasis K) = -243`
- **How**: `NumberField.coe_discr` + `numberField_discr_eq`.
- **Uses from project**: [`numberField_discr_eq`]
- **Visibility**: public
- **Lines**: 73-78
- **Notes**: unused in folder.

**File Summary — Discriminant.lean**: 2 theorems. Key API: `numberField_discr_eq` (used in PrimeSplitting + ClassGroup). Unused: `integralBasis_discr`. No sorry/set_option. 1 proof >30 lines.

---

## PrimeSplitting.lean

(imports `Common.lean`; `open NumberField.FieldExamples`)

### `theorem span_three_eq`
- **Type**: `Ideal.span {(3:𝓞 K)} = Ideal.span {thetaInt} ^ 3`
- **How**: `span_singleton_pow` + `thetaInt_cube`.
- **Uses from project**: [`thetaInt`, `thetaInt_cube`]
- **Visibility**: public · **Lines**: 32-35

### `theorem absNorm_span_theta`
- **Type**: `Ideal.absNorm (span {thetaInt}) = 3`
- **How**: `intNorm_eq_normForm 0 1 0`, `absNorm_span_singleton`.
- **Uses from project**: [`thetaInt`, `intNorm_eq_normForm`]
- **Visibility**: public · **Lines**: 37-42

### `theorem isPrime_span_theta`
- **Type**: `(span {thetaInt}).IsPrime`
- **How**: `Ideal.isPrime_of_irreducible_absNorm` with norm 3 prime.
- **Uses from project**: [`thetaInt`, `absNorm_span_theta`]
- **Visibility**: public · **Lines**: 44-48

### `theorem liesOver_span_theta`
- **Type**: `(span {thetaInt}).LiesOver (span {(3:ℤ)})`
- **Uses from project**: [`thetaInt`, `isPrime_span_theta`, `span_three_eq`]
- **Visibility**: public · **Lines**: 50-58

### `theorem inertiaDeg_span_theta`
- **Type**: `(span {(3:ℤ)}).inertiaDeg (span {thetaInt}) = 1`
- **How**: `Ideal.absNorm_eq_pow_inertiaDeg'` + `absNorm_span_theta`.
- **Uses from project**: [`thetaInt`, `liesOver_span_theta`, `absNorm_span_theta`]
- **Visibility**: public · **Lines**: 60-68

### `theorem ramificationIdx_span_theta`
- **Type**: `(span {(3:ℤ)}).ramificationIdx (span {thetaInt}) = 3`
- **How**: `Ideal.ramificationIdx_spec`; upper bound via absNorm divisibility (81 ∤ 27).
- **Uses from project**: [`thetaInt`, `span_three_eq`, `concreteIntegralBasis`, `absNorm_span_theta`]
- **Visibility**: public · **Lines**: 70-93

### `theorem eq_span_theta_of_three_mem`
- **Type**: `(P : Ideal (𝓞 K)) → P.IsPrime → 3 ∈ P → P = span {thetaInt}`
- **How**: `θ ∈ P` (prime, `θ³=3`); `(θ)` is maximal (`isPrime_span_theta.isMaximal`), `eq_of_le`.
- **Uses from project**: [`thetaInt`, `thetaInt_cube`, `absNorm_span_theta`, `isPrime_span_theta`]
- **Visibility**: public · **Lines**: 95-106

### `theorem two_eq_mul`
- **Type**: `(2:𝓞 K) = (thetaInt - 1)(thetaInt² + thetaInt + 1)`
- **How**: `linear_combination -thetaInt_cube`.
- **Uses from project**: [`thetaInt`, `thetaInt_cube`]
- **Visibility**: public · **Lines**: 108-110

### `theorem span_two_eq`
- **Type**: `span {2} = span {θ-1} * span {θ²+θ+1}`
- **Uses from project**: [`thetaInt`, `two_eq_mul`]
- **Visibility**: public · **Lines**: 112-117

### `theorem absNorm_span_theta_sub_one`
- **Type**: `absNorm (span {θ - 1}) = 2`
- **Uses from project**: [`thetaInt`, `intNorm_eq_normForm`]
- **Visibility**: public · **Lines**: 119-127

### `theorem isPrime_span_theta_sub_one`
- **Type**: `(span {θ - 1}).IsPrime`  (norm 2 prime)
- **Uses from project**: [`thetaInt`, `absNorm_span_theta_sub_one`]
- **Visibility**: public · **Lines**: 129-133

### `theorem absNorm_span_theta_sq_add_theta_add_one`
- **Type**: `absNorm (span {θ²+θ+1}) = 4`
- **Uses from project**: [`thetaInt`, `intNorm_eq_normForm`]
- **Visibility**: public · **Lines**: 135-144

### `theorem absNorm_ne_two_of_quadFactor_mem`
- **Type**: `(P : Ideal) → P.IsMaximal → θ²+θ+1 ∈ P → absNorm P ≠ 2`
- **What**: `X²+X+1` has no root in `𝔽₂`.
- **How**: residue field has 2 elements, every element is 0/1, `t²+t+1≠0` by case-check.
- **Uses from project**: [`thetaInt`]
- **Visibility**: public · **Lines**: 146-182
- **Notes**: proof >30 lines.

### `theorem eq_span_quadFactor_of_mem`
- **Type**: `(P) → P.IsPrime → θ²+θ+1 ∈ P → P = span {θ²+θ+1}`
- **How**: norm of P divides 4, ≠1, ≠2 → =4, force equality (`absNorm_eq_one_iff`).
- **Uses from project**: [`thetaInt`, `absNorm_span_theta_sq_add_theta_add_one`, `absNorm_ne_two_of_quadFactor_mem`]
- **Visibility**: public · **Lines**: 184-213
- **Notes**: proof >10 lines.

### `theorem isPrime_span_theta_sq_add_theta_add_one`
- **Type**: `(span {θ²+θ+1}).IsPrime`
- **Uses from project**: [`thetaInt`, `absNorm_span_theta_sq_add_theta_add_one`, `eq_span_quadFactor_of_mem`]
- **Visibility**: public · **Lines**: 215-226

### `theorem liesOver_span_theta_sub_one`, `theorem liesOver_span_theta_sq_add_theta_add_one`
- **Type**: each `LiesOver (span {(2:ℤ)})`
- **Uses from project**: [`thetaInt`, `isPrime_span_theta_sub_one`/`..sq..`, `two_eq_mul`]
- **Visibility**: public · **Lines**: 228-248

### `theorem inertiaDeg_span_theta_sub_one`, `theorem inertiaDeg_span_theta_sq_add_theta_add_one`
- **Type**: inertia degrees `1` and `2` over `2`.
- **Uses from project**: [`thetaInt`, the corresponding `liesOver`/`absNorm` lemmas]
- **Visibility**: public · **Lines**: 250-270

### `theorem eq_of_two_mem`  ★ (splitting of 2)
- **Type**: `(P) → P.IsPrime → 2 ∈ P → P = span{θ-1} ∨ P = span{θ²+θ+1}`
- **How**: prime contains product `(θ-1)(θ²+θ+1)`, split, use the two uniqueness lemmas.
- **Uses from project**: [`thetaInt`, `two_eq_mul`, `absNorm_span_theta_sub_one`, `isPrime_span_theta_sub_one`, `eq_span_quadFactor_of_mem`]
- **Visibility**: public · **Lines**: 272-289

### `theorem absNorm_span_seven`
- **Type**: `absNorm (span {(7:𝓞 K)}) = 343`
- **Uses from project**: [`thetaInt`, `intNorm_eq_normForm`]
- **Visibility**: public · **Lines**: 291-299

### `theorem absNorm_ne_seven`
- **Type**: `(P) → P.IsMaximal → absNorm P ≠ 7`
- **What**: 3 is not a cube mod 7.
- **How**: residue field ≅ `ZMod 7` (`ZMod.ringEquivOfPrime`), `decide` over all `s : ZMod 7`.
- **Uses from project**: [`thetaInt`, `thetaInt_cube`]
- **Visibility**: public · **Lines**: 301-317

### `theorem isPrime_span_seven`  ★ (7 inert)
- **Type**: `(span {(7:𝓞 K)}).IsPrime`
- **How**: any maximal P above has norm dividing 343, ≠1,7,49 → 343, so equals (7).
- **Uses from project**: [`absNorm_span_seven`, `absNorm_ne_seven`]
- **Visibility**: public · **Lines**: 319-362
- **Notes**: proof >30 lines.

### `theorem liesOver_span_seven`, `inertiaDeg_span_seven`
- **Type**: lies over `(7)`; inertia degree `3`.
- **Uses from project**: [`isPrime_span_seven`, `absNorm_span_seven`, `liesOver_span_seven`]
- **Visibility**: public · **Lines**: 364-382

### `def primeAbove61`
- **Type**: `(r : ℤ) → Ideal (𝓞 K) := span {61, θ - r}`
- **Uses from project**: [`thetaInt`]
- **Visibility**: public · **Lines**: 384-386

### `theorem absNorm_span_theta_sub_four`, `absNorm_span_gen_five`, `absNorm_span_gen_fiftytwo`
- **Type**: norms `61` of `θ-4`, `1+2θ+2θ²`, `2-2θ-θ²`.
- **Uses from project**: [`thetaInt`, `intNorm_eq_normForm`]
- **Visibility**: public · **Lines**: 388-418

### `theorem primeAbove61_four_eq`, `primeAbove61_five_eq`, `primeAbove61_fiftytwo_eq`
- **Type**: each `primeAbove61 r = span {generator}` (principal)
- **How**: `le_antisymm`; membership via `absNorm_mem` and explicit `linear_combination ... thetaInt_cube`.
- **Uses from project**: [`primeAbove61`, `thetaInt`, `thetaInt_cube`, the `absNorm_*` lemmas]
- **Visibility**: public · **Lines**: 420-466

### `theorem span_sixtyOne_eq`  ★ (61 splits completely)
- **Type**: `span {(61:𝓞 K)} = primeAbove61 4 * primeAbove61 5 * primeAbove61 52`
- **How**: rewrite to principal generators, `linear_combination ... thetaInt_cube`.
- **Uses from project**: [`primeAbove61_*_eq`, `thetaInt`, `thetaInt_cube`]
- **Visibility**: public · **Lines**: 468-478

### `theorem isPrime_primeAbove61`, `absNorm_primeAbove61`, `liesOver_primeAbove61`, `inertiaDeg_primeAbove61`
- **Type**: for `r ∈ {4,5,52}`: prime / norm 61 / lies over (61) / inertia degree 1.
- **Uses from project**: [`primeAbove61`, the `primeAbove61_*_eq` and `absNorm_*` lemmas]
- **Visibility**: public · **Lines**: 480-517

### `theorem primeAbove61_pairwise_ne`
- **Type**: the three primes over 61 are pairwise distinct.
- **How**: differences of generators are units mod each prime (explicit `norm_num` Bezout identities).
- **Uses from project**: [`primeAbove61`, `thetaInt`, `isPrime_primeAbove61`]
- **Visibility**: public · **Lines**: 519-555
- **Notes**: proof >30 lines.

### `private theorem adjoin_thetaInt_eq_top`
- **Type**: `Algebra.adjoin ℤ {thetaInt} = ⊤`
- **Uses from project**: [`thetaInt`, `integralBasisVectorsInt`, `span_integralBasisVectorsInt_eq_top`]
- **Visibility**: private · **Lines**: 557-576
- **Notes**: proof >10 lines.

### `private abbrev thetaIntPowerBasis`
- **Type**: `PowerBasis ℤ (𝓞 K)`
- **Uses from project**: [`thetaInt`, `adjoin_thetaInt_eq_top`]
- **Visibility**: private · **Lines**: 578-580

### `private theorem thetaIntPowerBasis_gen`
- **Type**: `thetaIntPowerBasis.gen = thetaInt`
- **Uses from project**: [`thetaIntPowerBasis`, `thetaInt`, `adjoin_thetaInt_eq_top`]
- **Visibility**: private · **Lines**: 582-584

### `private theorem thetaInt_minpoly_eq`
- **Type**: `minpoly ℤ thetaInt = X³ - C 3`
- **How**: `minpoly.isIntegrallyClosed_eq_field_fractions`, `RingOfIntegers.minpoly_coe`, `map_injective`.
- **Uses from project**: [`cubePolynomial`, `cubeRootThree`, `thetaInt`, `cubeRootThree_integral`]
- **Visibility**: private · **Lines**: 586-609
- **Notes**: proof >10 lines.

### `private def residueHom`
- **Type**: `(p : ℕ)(r : ℤ)(hr : (r:ZMod p)³=3) → (𝓞 K) →ₐ[ℤ] ZMod p`
- **How**: `PowerBasis.lift` sending θ ↦ r.
- **Uses from project**: [`thetaIntPowerBasis`, `thetaIntPowerBasis_gen`, `thetaInt_minpoly_eq`]
- **Visibility**: private · **Lines**: 611-616
- **Notes**: GENERIC machinery (mirrors ζ₈/ζ₅ residueHom per memory).

### `private theorem residueHom_thetaInt`
- **Type**: `residueHom p r hr thetaInt = (r : ZMod p)`
- **Uses from project**: [`residueHom`, `thetaIntPowerBasis`, `thetaIntPowerBasis_gen`, `thetaInt`]
- **Visibility**: private · **Lines**: 618-621

### `private theorem ker_residueHom`
- **Type**: `ker (residueHom p r hr).toRingHom = span {p, θ - r}`
- **How**: `PowerBasis.exists_eq_aeval`, `Polynomial.sub_dvd_eval_sub`, `ZMod.intCast_zmod_eq_zero_iff_dvd`.
- **Uses from project**: [`residueHom`, `thetaIntPowerBasis`, `thetaIntPowerBasis_gen`, `residueHom_thetaInt`, `thetaInt`]
- **Visibility**: private · **Lines**: 623-670
- **Notes**: proof >30 lines.

### `private theorem residueHom_surjective`
- **Type**: `Function.Surjective (residueHom p r hr)`
- **Uses from project**: [`residueHom`]
- **Visibility**: private · **Lines**: 672-676

### `private theorem isMaximal_span_pair`
- **Type**: `[Fact p.Prime] → (span {p, θ - r}).IsMaximal`
- **How**: `RingHom.ker_isMaximal_of_surjective` + `ker_residueHom`.
- **Uses from project**: [`ker_residueHom`, `residueHom_surjective`, `thetaInt`]
- **Visibility**: private · **Lines**: 678-682

### `private theorem absNorm_span_pair`
- **Type**: `absNorm (span {p, θ - r}) = p`
- **Uses from project**: [`ker_residueHom`, `residueHom_surjective`, `thetaInt`]
- **Visibility**: private · **Lines**: 684-689

### `theorem exists_degree_one_prime_iff_cube_root_mod_p`  ★ (splitting law)
- **Type**: `(p prime, p≠3) → (∃ residue-degree-1 prime above p) ↔ ∃ r:ZMod p, r³=3`
- **How**: forward via residue field ≅ ZMod p; backward via `isMaximal_span_pair`/`absNorm_span_pair`.
- **Uses from project**: [`thetaInt`, `thetaInt_cube`, `isMaximal_span_pair`, `absNorm_span_pair`]
- **Visibility**: public · **Lines**: 691-721
- **Notes**: proof >30 lines.

### `theorem ramified_iff_eq_three`  ★ (ramification law)
- **Type**: `(p prime) → (∃ P prime, span{p} ≤ P²) ↔ p = 3`
- **How**: ramified ⇒ P ∣ differentIdeal (`dvd_differentIdeal_iff`, `not_isUnramifiedAt_...` from Common), norm ∣ 243 ⇒ p=3; converse via `span_three_eq`.
- **Uses from project**: [Common: `not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow`, `not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ`; local: `concreteIntegralBasis`, `numberField_discr_eq`, `isPrime_span_theta`, `span_three_eq`]
- **Visibility**: public · **Lines**: 723-771
- **Notes**: proof >30 lines.

### `theorem ramificationIdx_span_theta_sub_one`, `..._sq_add_theta_add_one`, `ramificationIdx_span_seven`, `ramificationIdx_primeAbove61`
- **Type**: each ramification index `= 1` (unramified).
- **How**: `ramificationIdx_spec`; non-ramification via `ramified_iff_eq_three` contradiction.
- **Uses from project**: [`thetaInt`, `span_two_eq`, the `isPrime_*` lemmas, `ramified_iff_eq_three`, `primeAbove61`]
- **Visibility**: public · **Lines**: 773-836

### `abbrev cubeRootThreePolynomialMod`
- **Type**: `(p : ℕ) → (ZMod p)[X] := X³ - C 3`
- **Uses from project**: []
- **Visibility**: public · **Lines**: 853-855
- **Notes**: unused.

### `theorem absNorm_differentIdeal_eq_twoHundredFortyThree`
- **Type**: `absNorm (differentIdeal ℤ (𝓞 K)) = 243`
- **How**: `NumberField.absNorm_differentIdeal` + `numberField_discr_eq`.
- **Uses from project**: [`numberField_discr_eq`]
- **Visibility**: public · **Lines**: 871-874

### `theorem prime_dvd_differentIdeal_iff_eq_span_theta`
- **Type**: `(P prime, P≠⊥) → P ∣ differentIdeal ↔ P = span {thetaInt}`
- **How**: norm of P ∣ 243 ⇒ 3 ∈ P ⇒ P=(θ) (`eq_span_theta_of_three_mem`); converse via `ramificationIdx_span_theta`.
- **Uses from project**: [`thetaInt`, `absNorm_differentIdeal_eq_twoHundredFortyThree`, `eq_span_theta_of_three_mem`, `isPrime_span_theta`, `liesOver_span_theta`, `ramificationIdx_span_theta`]
- **Visibility**: public · **Lines**: 876-904
- **Notes**: proof >10 lines.

**File Summary — PrimeSplitting.lean**: ~3 defs/abbrevs + ~50 theorems (many private). Key API (3+): `thetaInt`/`thetaInt_cube`/`intNorm_eq_normForm`(imported), `absNorm_span_theta`, `isPrime_span_theta`, `eq_span_theta_of_three_mem`, `span_three_eq`, `ramified_iff_eq_three`, `primeAbove61`, `residueHom` chain. Unused: `cubeRootThreePolynomialMod`. No sorry. No set_option. Many proofs >30 lines (`absNorm_ne_two_of_quadFactor_mem`, `isPrime_span_seven`, `primeAbove61_pairwise_ne`, `ker_residueHom`, `exists_degree_one_prime_iff_cube_root_mod_p`, `ramified_iff_eq_three`).

---

## ClassGroup.lean

### `abbrev cubeRootThreeFractionalIdeal`, `ramifiedPrimeFractionalIdeal`
- **Type**: `FractionalIdeal (𝓞 K)⁰ K` — `spanSingleton θ` and `(θ)`.
- **Uses from project**: [`cubeRootThree`, `thetaInt`]
- **Visibility**: public · **Lines**: 31-35

### `theorem cubeRootThree_mem_fractionalIdeal`, `cubeRootThreeFractionalIdeal_absNorm`, `ramifiedPrimeFractionalIdeal_ne_zero`
- **Type**: membership / norm / nonzero facts for the fractional ideals.
- **Uses from project**: [`cubeRootThreeFractionalIdeal`, `cubeRootThree`, `ramifiedPrimeFractionalIdeal`, `thetaInt`, `absNorm_span_theta`]
- **Visibility**: public · **Lines**: 37-53
- **Notes**: all three appear unused downstream.

### `theorem sqrt_243_bounds`
- **Type**: `15.58 < √243 ∧ √243 < 15.59`
- **How**: `Real.sq_sqrt`, `nlinarith`. Used in Minkowski bound.
- **Uses from project**: []
- **Visibility**: public · **Lines**: 68-74
- **Notes**: GENERIC numeric helper.

### `theorem classNumber_eq_one`  ★ headline
- **Type**: `NumberField.classNumber K = 1`
- **How**: `classNumber_eq_one_iff` + `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`; Minkowski bound < 5 (`sqrt_243_bounds`, `Real.pi_gt_d2`), `interval_cases p` over 2,3, principal generators from `eq_of_two_mem`/`eq_span_theta_of_three_mem`.
- **Uses from project**: [`nrComplexPlaces_eq_one`, `degree_eq_three`, `numberField_discr_eq`, `sqrt_243_bounds`, `eq_of_two_mem`, `eq_span_theta_of_three_mem`, `thetaInt`]
- **Visibility**: public · **Lines**: 76-117
- **Notes**: proof >30 lines.

### `theorem isPrincipalIdealRing`  ★ headline
- **Type**: `IsPrincipalIdealRing (𝓞 K)`
- **Uses from project**: [`classNumber_eq_one`]
- **Visibility**: public · **Lines**: 119-123

### `theorem uniqueFactorizationMonoid`
- **Type**: `UniqueFactorizationMonoid (𝓞 K)`
- **Uses from project**: [`isPrincipalIdealRing`]
- **Visibility**: public · **Lines**: 125-128

### `theorem classGroupStructure`  ★ headline
- **Type**: `Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1))`
- **Uses from project**: [`classNumber_eq_one`]
- **Visibility**: public · **Lines**: 130-136

### `abbrev unitIdealRepresentative`
- **Type**: `(Ideal (𝓞 K))⁰ := ⟨⊤, _⟩`
- **Uses from project**: []
- **Visibility**: public · **Lines**: 138-139

### `theorem classGroupRepresentative`
- **Type**: `(C : ClassGroup (𝓞 K)) → C = ClassGroup.mk0 unitIdealRepresentative`
- **Uses from project**: [`classNumber_eq_one`, `unitIdealRepresentative`]
- **Visibility**: public · **Lines**: 141-147
- **Notes**: unused downstream.

**File Summary — ClassGroup.lean**: 4 abbrevs, 8 theorems. Key API (3+): `classNumber_eq_one`. Unused: the 3 fractional-ideal lemmas, `classGroupRepresentative`. No sorry/set_option. 1 proof >30 lines (`classNumber_eq_one`). GENERIC: `sqrt_243_bounds` (number-specific but pattern shared across twins).

---

## Units.lean

(`open NumberField.FieldExamples` for `torsionPowerHom`, `rankOnePowerHom`)

### `abbrev torsionGenerator`
- **Type**: `(𝓞 K)ˣ := -1`
- **Uses from project**: []
- **Visibility**: public · **Lines**: 33-34

### `def torsionUnits`
- **Type**: `Set ((𝓞 K)ˣ) := {u | ∃ k : Fin 2, u = torsionGenerator ^ k.val}`
- **Uses from project**: [`torsionGenerator`]
- **Visibility**: public · **Lines**: 36-37

### `theorem torsionUnits_eq`
- **Type**: `{u | IsOfFinOrder u} = torsionUnits`
- **How**: odd finrank ⇒ `torsion_eq_one_or_neg_one_of_odd_finrank`.
- **Uses from project**: [`degree_eq_three`, `torsionUnits`, `torsionGenerator`]
- **Visibility**: public · **Lines**: 39-54

### `theorem torsionOrder_eq_two`  ★ headline
- **Type**: `NumberField.Units.torsionOrder K = 2`
- **How**: `torsionOrder_eq_two_of_odd_finrank`.
- **Uses from project**: [`degree_eq_three`]
- **Visibility**: public · **Lines**: 56-59

### `theorem unitRank_eq_one`  ★ headline
- **Type**: `NumberField.Units.rank K = 1`
- **How**: signature `(1,1)` ⇒ rank = card places − 1.
- **Uses from project**: [`degree_eq_three`, `not_totallyReal`]
- **Visibility**: public · **Lines**: 61-71

### `def fundamentalUnit`  ★ headline
- **Type**: `(𝓞 K)ˣ` with `val = θ²-2`, explicit inverse `2θ²+3θ+4`.
- **How**: `val_inv`/`inv_val` by `linear_combination ... thetaInt_cube`.
- **Uses from project**: [`thetaInt`, `thetaInt_cube`]
- **Visibility**: public · **Lines**: 73-79

### `def fundamentalUnitSystem`
- **Type**: `Fin (rank K) → (𝓞 K)ˣ := fun _ => fundamentalUnit`
- **Uses from project**: [`fundamentalUnit`]
- **Visibility**: public · **Lines**: 81-83

### `theorem fundamentalUnitSystem_isFundamental`  ★ headline (SORRY)
- **Type**: `Subgroup.closure (range fundamentalUnitSystem) ⊔ torsion K = ⊤`
- **What**: `θ²-2` is a genuine fundamental unit.
- **Uses from project**: [`fundamentalUnitSystem`]
- **Visibility**: public · **Lines**: 88-90
- **Notes**: **SORRY** — needs Artin-type unit bound (per memory, the only genuinely blocked class alongside regulator).

### `theorem unit_eq_torsion_mul_fundamentalUnit_zpow`
- **Type**: `(u) → ∃ ζ∈torsion, ∃ n:ℤ, u = ζ·fundamentalUnit^n`
- **How**: `Subgroup.mem_sup` on `fundamentalUnitSystem_isFundamental`, `mem_closure_singleton`.
- **Uses from project**: [`fundamentalUnitSystem`, `fundamentalUnitSystem_isFundamental`, `unitRank_eq_one`, `fundamentalUnit`]
- **Visibility**: public · **Lines**: 92-108
- **Notes**: depends on sorry transitively.

### `theorem exists_eq_torsion_mul_fundSystem_zpow`
- **Type**: `(i₀)(u) → ∃ ζ∈torsion, ∃ n, u = ζ·(fundSystem K i₀)^n`
- **How**: `closure_fundSystem_sup_torsion_eq_top` + subsingleton of `Fin (rank)`.
- **Uses from project**: [`unitRank_eq_one`]
- **Visibility**: public · **Lines**: 110-134
- **Notes**: this is the SORRY-FREE abstract version (uses mathlib fundSystem, not `fundamentalUnit`).

### `theorem fundSystem_zpow_mem_torsion`
- **Type**: `(i₀)(n) → fundSystem K i₀ ^ n ∈ torsion → n = 0`
- **How**: image in free quotient mod torsion is a basis vector (`basisModTorsion`, `repr_self`).
- **Uses from project**: []
- **Visibility**: public · **Lines**: 136-150
- **Notes**: GENERIC (rank-agnostic mechanism).

### `theorem eq_one_or_neg_one_of_mem_torsion`
- **Type**: `ζ ∈ torsion → ζ = 1 ∨ ζ = -1`
- **Uses from project**: [`torsionUnits_eq`]
- **Visibility**: public · **Lines**: 152-161

### `private theorem unitGroupStructure_bijective`
- **Type**: bijectivity of `(torsionPowerHom 2 (-1)).coprod (rankOnePowerHom η)`.
- **How**: injective (kernel trivial via `fundSystem_zpow_mem_torsion` + ZMod 2 case split); surjective via `exists_eq_torsion_mul_fundSystem_zpow`.
- **Uses from project**: [Common: `torsionPowerHom`, `rankOnePowerHom`; local: `fundSystem_zpow_mem_torsion`, `exists_eq_torsion_mul_fundSystem_zpow`, `eq_one_or_neg_one_of_mem_torsion`]
- **Visibility**: private · **Lines**: 163-205
- **Notes**: proof >30 lines.

### `theorem unitGroupStructure`  ★ headline
- **Type**: `Nonempty ((𝓞 K)ˣ ≃* (Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ)))`
- **What**: unit group `≅ μ₂ × ℤ`.
- **How**: `MulEquiv.ofBijective` of the coprod hom, via `unitGroupStructure_bijective`. SORRY-FREE (uses abstract `fundSystem`).
- **Uses from project**: [Common: `torsionPowerHom`, `rankOnePowerHom`; local: `unitRank_eq_one`, `unitGroupStructure_bijective`]
- **Visibility**: public · **Lines**: 207-222

### `theorem regulator_eq`  ★ headline (depends on sorry)
- **Type**: `Units.regulator K = |Real.log ((3:ℝ)^(2/3) - 2)|`
- **How**: pick real embedding, `regOfFamily_div_regulator` + `fundamentalUnitSystem_isFundamental`, `regOfFamily_eq_det`, `Matrix.det_eq_elem_of_subsingleton`.
- **Uses from project**: [`exists_realEmbedding_cubeRootThree`, `thetaInt`, `cubeRootThree_integral`, `fundamentalUnit`, `infinitePlace_card_eq_two`, `unitRank_eq_one`, `fundamentalUnitSystem_isFundamental`]
- **Visibility**: public · **Lines**: 224-297
- **Notes**: proof >30 lines; transitively depends on the `fundamentalUnitSystem_isFundamental` SORRY.

**File Summary — Units.lean**: 4 defs/abbrevs, 10 theorems. Key API (3+): `fundamentalUnit`, `unitRank_eq_one`, `fundamentalUnitSystem_isFundamental`, `torsionUnits_eq`. Sorry: `fundamentalUnitSystem_isFundamental` (and `regulator_eq`/`unit_eq_torsion_mul_fundamentalUnit_zpow` depend on it). No set_option. Proofs >30 lines: `unitGroupStructure_bijective`, `regulator_eq`. GENERIC: `fundSystem_zpow_mem_torsion`, `exists_eq_torsion_mul_fundSystem_zpow`, `unitGroupStructure_bijective` (all rank-1 generic; shared with twins per memory).

---

## Euclidean.lean

### `theorem normEuclidean`  ★ headline (SORRY)
- **Type**: `(a b : 𝓞 K) → b ≠ 0 → ∃ q r, a = b*q+r ∧ (norm r).natAbs < (norm b).natAbs`
- **What**: `ℚ(∛3)` is norm-Euclidean.
- **How**: —
- **Uses from project**: [`K`]
- **Visibility**: public · **Lines**: 34-37
- **Notes**: **SORRY** — needs the covering / division-with-remainder geometric argument (per memory).

**File Summary — Euclidean.lean**: 1 theorem, sorry. No set_option.

---

## LocalGlobal.lean

### `def heightOneThree`, `heightOneTwoLinear`, `heightOneTwoQuadratic`, `heightOneSeven`, `heightOneSixtyOneFour/Five/FiftyTwo`
- **Type**: `HeightOneSpectrum (𝓞 K)` for each finite place.
- **How**: bundle `asIdeal` + isPrime (`isPrime_*`) + ne_bot (`absNorm_*` ≠ 0).
- **Uses from project**: [`thetaInt`, `isPrime_span_theta`/`...sub_one`/`...sq...`/`isPrime_span_seven`/`isPrime_primeAbove61`, corresponding `absNorm_*`, `primeAbove61`]
- **Visibility**: public · **Lines**: 35-109

### `abbrev vThree`
- **Type**: `FinitePlace K := FinitePlace.mk heightOneThree`
- **Uses from project**: [`heightOneThree`]
- **Visibility**: public · **Lines**: 111-112

### (6 `example`s, lines 114-140) ramification/inertia degrees at the height-one primes
- **Uses from project**: [`heightOne*`, `ramificationIdx_span_theta`, `inertiaDeg_*`, `inertiaDeg_primeAbove61`]
- **Notes**: `example`s, not named declarations.

### `abbrev CompletionAtThree`
- **Type**: `Type := heightOneThree.adicCompletion K`
- **Uses from project**: [`heightOneThree`]
- **Visibility**: public · **Lines**: 154-157

### `abbrev InfiniteCompletion`
- **Type**: `(v : InfinitePlace K) → Type := v.Completion`
- **Uses from project**: []
- **Visibility**: public · **Lines**: 170-171
- **Notes**: followed by 2 `example`s for real/complex completions.

### `theorem product_formula_cubeRootThree`
- **Type**: `(∏ w, w θ ^ w.mult) * ∏ᶠ v, v θ = 1`
- **How**: `NumberField.prod_abs_eq_one`.
- **Uses from project**: [`cubeRootThree`, `cubeRootThree_cube`]
- **Visibility**: public · **Lines**: 195-203
- **Notes**: followed by an `example` for the fundamental unit.

### `abbrev CubeRootThreeInfiniteAdeleRing`, `infinitePrincipalAdele_cubeRootThree`, `infinitePrincipalAdele_fundamentalUnit`
- **Type**: `InfiniteAdeleRing K` and principal adeles.
- **Uses from project**: [`K`, `cubeRootThree`, `fundamentalUnit`]
- **Visibility**: public · **Lines**: 230-237
- **Notes**: followed by 2 `example`s (norm, dense range).

### `theorem canonicalEmbedding_thetaInt_mem_integerLattice`
- **Type**: `canonicalEmbedding K (algebraMap (𝓞 K) K thetaInt) ∈ integerLattice K`
- **How**: `simp [integerLattice]`.
- **Uses from project**: [`thetaInt`]
- **Visibility**: public · **Lines**: 259-262

### `abbrev mixedEmbedding_cubeRootThree`
- **Type**: `mixedEmbedding.mixedSpace K := mixedEmbedding K cubeRootThree`
- **Uses from project**: [`cubeRootThree`]
- **Visibility**: public · **Lines**: 278-279
- **Notes**: followed by 3 `example`s (convexBodyLT, measurableSet fundamentalCone/normLeOne).

### `theorem polarSpace_nonempty`
- **Type**: `Nonempty (mixedEmbedding.polarSpace K)`
- **Uses from project**: []
- **Visibility**: public · **Lines**: 295-297

### `theorem house_cubeRootThree_pos`, `house_thetaInt_pos`
- **Type**: `0 < NumberField.house cubeRootThree` (and via `thetaInt`).
- **How**: `one_le_house_of_isIntegral` + `cubeRootThree_integral`.
- **Uses from project**: [`cubeRootThree`, `cubeRootThree_integral`, `cubeRootThree_cube`, `thetaInt`, `house_cubeRootThree_pos`]
- **Visibility**: public · **Lines**: 311-325

### `abbrev CubeRootThreeAdeleRing`, `principalAdele_cubeRootThree`, `principalAdele_fundamentalUnit`
- **Type**: `AdeleRing (𝓞 K) K` and principal adeles.
- **Uses from project**: [`K`, `cubeRootThree`, `fundamentalUnit`]
- **Visibility**: public · **Lines**: 340-347

### `theorem principalAdele_cubeRootThree_ne_zero`
- **Type**: `principalAdele_cubeRootThree ≠ 0`
- **How**: `AdeleRing.algebraMap_injective` + `cubeRootThree_cube`.
- **Uses from project**: [`principalAdele_cubeRootThree`, `cubeRootThree`, `cubeRootThree_cube`]
- **Visibility**: public · **Lines**: 349-355

### `theorem principalAdele_fundamentalUnit_is_unit_everywhere`
- **Type**: `∀ v : FinitePlace K, v (algebraMap (𝓞 K) K fundamentalUnit) = 1`
- **How**: unit ∉ each maximal ideal; `FinitePlace.norm_eq_one_iff_notMem`.
- **Uses from project**: [`fundamentalUnit`]
- **Visibility**: public · **Lines**: 357-367

### `abbrev cubeRootThreeDedekindZeta`, `cubeRootThreeDedekindZetaResidue`
- **Type**: `dedekindZeta K s` and its residue.
- **Uses from project**: [`K`]
- **Visibility**: public · **Lines**: 381-385
- **Notes**: followed by 2 `example`s (residue positive; class-number formula `rfl`).

**File Summary — LocalGlobal.lean**: ~25 abbrevs/defs + 7 theorems + many `example`s. Key API: `heightOneThree`, `fundamentalUnit`, `thetaInt`, `cubeRootThree`. No sorry, no set_option. No proof >30 lines. Mostly thin wrappers tying earlier results to mathlib's place/adele/zeta API; many `example`s serve as compile-checks rather than reusable lemmas.

---

## Cross-folder / Common.lean usage

PrimeSplitting and Units `import`/`open NumberField.FieldExamples` and use from **Common.lean**:
- `torsionPowerHom`, `rankOnePowerHom` (Units)
- `not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ`, `not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow` (PrimeSplitting `ramified_iff_eq_three`)

Common.lean lemmas NOT used by this folder but plausibly should be (smell): `eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq`, `left_eq_prime_of_mul_eq_prime_sq_of_ne_one`, `exists_int_inverse_mod_prime`, `eq_of_le_of_absNorm_eq`, `natAbs_lt_of_abs_ratCast_lt`. This folder re-derives several of these patterns inline (see below).
