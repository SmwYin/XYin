# CyclotomicFive declaration inventory

Folder: `XYin/NumberField/FieldExamples/CyclotomicFive/`
Field: `K = ℚ(ζ₅) = CyclotomicField 5 ℚ`, degree 4, totally complex, disc 125, class number 1.

All declarations live in `namespace NumberField.CyclotomicFive`. Shared helpers come from
`NumberField.FieldExamples` (`Common.lean`): `eq_of_le_of_absNorm_eq`, `torsionPowerHom`,
`rankOnePowerHom`, `not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ`,
`not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow`.

---

## Basic.lean

### `abbrev K`
- **Type**: `K : Type := CyclotomicField 5 ℚ`
- **What**: The fifth cyclotomic field over ℚ.
- **How**: Definitional alias.
- **Hypotheses**: none
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 32
- **Notes**: —

### `instance : IsCyclotomicExtension {5} ℚ K`
- **Type**: `IsCyclotomicExtension {5} ℚ K`
- **What**: Endows K with its cyclotomic-extension structure.
- **How**: `CyclotomicField.isCyclotomicExtension`.
- **Hypotheses**: none
- **Uses from project**: [K]
- **Visibility**: public (instance)
- **Lines**: 35-36
- **Notes**: —

### `abbrev ζ`
- **Type**: `ζ : K := IsCyclotomicExtension.zeta 5 ℚ K`
- **What**: A chosen primitive fifth root of unity.
- **How**: `IsCyclotomicExtension.zeta`.
- **Uses from project**: [K]
- **Visibility**: public
- **Lines**: 39
- **Notes**: —

### `theorem zeta_isPrimitiveRoot`
- **Type**: `IsPrimitiveRoot ζ 5`
- **What**: ζ is a primitive fifth root of unity.
- **How**: `IsCyclotomicExtension.zeta_spec`.
- **Uses from project**: [ζ]
- **Visibility**: public
- **Lines**: 42-43
- **Notes**: Key API (used pervasively across the whole folder).

### `theorem zeta_pow_five`
- **Type**: `ζ ^ 5 = 1`
- **What**: ζ⁵ = 1.
- **How**: `IsPrimitiveRoot.pow_eq_one`.
- **Uses from project**: [zeta_isPrimitiveRoot, ζ]
- **Visibility**: public
- **Lines**: 46-47
- **Notes**: Key API.

### `theorem zeta_sum_eq_zero`
- **Type**: `1 + ζ + ζ^2 + ζ^3 + ζ^4 = 0`
- **What**: Φ₅(ζ) = 0.
- **How**: `IsPrimitiveRoot.geom_sum_eq_zero` + `Finset.sum_range_succ`, `linear_combination`.
- **Uses from project**: [zeta_isPrimitiveRoot, ζ]
- **Visibility**: public
- **Lines**: 51-54
- **Notes**: Key API.

### `abbrev zetaFivePolynomial`
- **Type**: `ℚ[X] := X^4 + X^3 + X^2 + X + C 1`
- **What**: Explicit Φ₅.
- **How**: Definitional.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 65-66
- **Notes**: —

### `instance : Fact (Irreducible zetaFivePolynomial)`
- **Type**: `Fact (Irreducible zetaFivePolynomial)`
- **What**: Φ₅ is irreducible over ℚ.
- **How**: rewrites to `cyclotomic 5 ℚ` via `cyclotomic_prime` then `cyclotomic.irreducible_rat`.
- **Uses from project**: [zetaFivePolynomial]
- **Visibility**: public (instance)
- **Lines**: 68-80
- **Notes**: —

### `abbrev KAdjoinRoot`
- **Type**: `Type := AdjoinRoot zetaFivePolynomial`
- **What**: AdjoinRoot presentation of ℚ(ζ₅).
- **Uses from project**: [zetaFivePolynomial]
- **Visibility**: public
- **Lines**: 83

### `abbrev zetaFiveRoot`
- **Type**: `KAdjoinRoot := AdjoinRoot.root zetaFivePolynomial`
- **What**: Formal primitive root in the AdjoinRoot model.
- **Uses from project**: [zetaFivePolynomial, KAdjoinRoot]
- **Visibility**: public
- **Lines**: 86

### `theorem zetaFiveRoot_relation`
- **Type**: `1 + zetaFiveRoot + … + zetaFiveRoot^4 = 0`
- **What**: Φ₅ vanishes at the formal root.
- **How**: `AdjoinRoot.eval₂_root` + `calc`/`ring`.
- **Uses from project**: [zetaFiveRoot, zetaFivePolynomial]
- **Visibility**: public
- **Lines**: 89-99

### `theorem zetaFivePolynomial_eq_minpoly`
- **Type**: `zetaFivePolynomial = minpoly ℚ ζ`
- **What**: Φ₅ is the minimal polynomial of ζ.
- **How**: `cyclotomic_prime`, `minpoly_eq_cyclotomic_of_irreducible`.
- **Uses from project**: [zetaFivePolynomial, ζ, zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 102-114

### `def zetaMinpolyAdjoinRootPresentation`
- **Type**: `IsAdjoinRoot K (minpoly ℚ ζ)`
- **What**: K is got by adjoining a root of minpoly ℚ ζ.
- **How**: `IsAdjoinRoot.mkOfAdjoinEqTop` + `adjoin_primitive_root_eq_top`.
- **Uses from project**: [K, ζ, zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 117-120

### `noncomputable def adjoinRootEquivCyclotomic`
- **Type**: `KAdjoinRoot ≃ₐ[ℚ] K`
- **What**: ℚ-algebra equivalence AdjoinRoot Φ₅ ≅ K.
- **How**: `AdjoinRoot.algEquivOfEq` composed with `adjoinRootAlgEquiv`.
- **Uses from project**: [KAdjoinRoot, K, zetaFivePolynomial, ζ, zetaFivePolynomial_eq_minpoly, zetaMinpolyAdjoinRootPresentation]
- **Visibility**: public
- **Lines**: 126-129
- **Notes**: Used by Embeddings.

### `theorem adjoinRootEquivCyclotomic_root`
- **Type**: `adjoinRootEquivCyclotomic zetaFiveRoot = ζ`
- **What**: The equivalence sends the formal root to ζ.
- **How**: `AdjoinRoot.algEquivOfEq_root` + simp.
- **Uses from project**: [adjoinRootEquivCyclotomic, zetaFiveRoot, ζ, zetaMinpolyAdjoinRootPresentation, zetaFivePolynomial, zetaFivePolynomial_eq_minpoly]
- **Visibility**: public
- **Lines**: 132-138

### `theorem degree_eq_four`
- **Type**: `Module.finrank ℚ K = 4`
- **What**: [ℚ(ζ₅):ℚ] = φ(5) = 4.
- **How**: `IsCyclotomicExtension.finrank` + `cyclotomic.irreducible_rat`.
- **Uses from project**: [K]
- **Visibility**: public
- **Lines**: 57-59
- **Notes**: HEADLINE (degree). Key API.

**File Summary — Basic.lean**: 17 decls (abbrev/def 8, theorem 7, instance 2). Key API: `ζ`,
`zeta_isPrimitiveRoot`, `zeta_pow_five`, `zeta_sum_eq_zero`, `degree_eq_four`. No sorry, no
set_option, no proof >30 lines.

---

## Galois.lean

### `noncomputable def idAut`
- **Type**: `K ≃ₐ[ℚ] K := AlgEquiv.refl`
- **What**: Identity automorphism.
- **Uses from project**: [K]; **Visibility**: public; **Lines**: 32

### `noncomputable def sigmaTwo / sigmaThree / sigmaFour`
- **Type**: `K ≃ₐ[ℚ] K`
- **What**: Automorphisms ζ ↦ ζ², ζ³, ζ⁴ (σ₄ = complex conjugation).
- **How**: `IsCyclotomicExtension.fromZetaAut` with `pow_of_coprime`.
- **Uses from project**: [zeta_isPrimitiveRoot, K]
- **Visibility**: public; **Lines**: 35-47

### `theorem sigmaTwo_apply_zeta / sigmaThree_apply_zeta / sigmaFour_apply_zeta`
- **Type**: `sigmaN ζ = ζ ^ N`
- **What**: Action of each automorphism on ζ.
- **How**: `fromZetaAut_spec`.
- **Uses from project**: [sigmaN, zeta_isPrimitiveRoot, ζ]
- **Visibility**: public; **Lines**: 50-63

### `private theorem autEq'`
- **Type**: `σ = idAut ∨ σ = sigmaTwo ∨ σ = sigmaThree ∨ σ = sigmaFour`
- **What**: The four automorphisms exhaust the Galois group.
- **How**: `IsPrimitiveRoot.autToPow_spec`, `powerBasis.algHom_ext`, case split on (ZMod 5)ˣ via `decide`.
- **Uses from project**: [idAut, sigmaTwo/Three/Four, zeta_isPrimitiveRoot, *_apply_zeta]
- **Visibility**: private; **Lines**: 65-81

### `theorem isGalois`
- **Type**: `IsGalois ℚ K`
- **What**: ℚ(ζ₅)/ℚ is Galois.
- **How**: `IsCyclotomicExtension.isGalois`.
- **Uses from project**: [K]; **Visibility**: public; **Lines**: 84-85
- **Notes**: HEADLINE.

### `theorem galoisGroupStructure`
- **Type**: `Nonempty ((K ≃ₐ[ℚ] K) ≃* (ZMod 5)ˣ)`
- **What**: Gal ≅ (ℤ/5)ˣ.
- **How**: `IsCyclotomicExtension.autEquivPow`.
- **Uses from project**: [K]; **Visibility**: public; **Lines**: 88-89
- **Notes**: HEADLINE (Galois group).

### `theorem galoisGroup_isCyclic`
- **Type**: `IsCyclic (K ≃ₐ[ℚ] K)`
- **What**: Galois group is cyclic of order 4.
- **How**: transport cyclicity of (ZMod 5)ˣ via `autEquivPow`, `isCyclic_of_surjective`.
- **Uses from project**: [K]; **Visibility**: public; **Lines**: 92-96

### `theorem orderOf_sigmaTwo`
- **Type**: `orderOf sigmaTwo = 4`
- **What**: σ₂ generates the Galois group.
- **How**: transport to (ZMod 5)ˣ via `autEquivPow`/`autToPow_spec`, `orderOf_dvd_prime_pow` analysis, `decide`.
- **Uses from project**: [sigmaTwo, zeta_isPrimitiveRoot, sigmaTwo_apply_zeta, K]
- **Visibility**: public; **Lines**: 99-127
- **Notes**: proof ~29 lines.

### `theorem aut_eq`
- **Type**: `σ = idAut ∨ σ = sigmaTwo ∨ σ = sigmaThree ∨ σ = sigmaFour`
- **What**: Public wrapper around `autEq'`.
- **How**: `autEq'`.
- **Uses from project**: [autEq', idAut, sigmaTwo/Three/Four]
- **Visibility**: public; **Lines**: 130-132

**File Summary — Galois.lean**: 13 decls (def 4, theorem 9, of which 1 private). Key API:
`sigmaTwo_apply_zeta` (and siblings), `isGalois`. No sorry, no set_option. `orderOf_sigmaTwo`
~29 lines. NOTE: `autEq'`/`sigmaN` are *re-derived privately* (`sig2`/`sig3`/`sig4`/`autEq'`)
inside PrimeSplitting.lean — duplication smell.

---

## Embeddings.lean

### `theorem isTotallyComplex`
- **Type**: `NumberField.IsTotallyComplex K`
- **How**: `IsCyclotomicExtension.Rat.isTotallyComplex`.
- **Uses from project**: [K]; **Visibility**: public; **Lines**: 34-35
- **Notes**: HEADLINE; used by CMField, Embeddings.

### `theorem nrRealPlaces_eq_zero`
- **Type**: `InfinitePlace.nrRealPlaces K = 0`
- **How**: `IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero`.
- **Uses from project**: [K]; **Visibility**: public; **Lines**: 37-38
- **Notes**: Key API (Units, ClassGroup).

### `theorem nrComplexPlaces_eq_two`
- **Type**: `InfinitePlace.nrComplexPlaces K = 2`
- **How**: `card_add_two_mul_card_eq_rank`, `degree_eq_four`, omega.
- **Uses from project**: [nrRealPlaces_eq_zero, degree_eq_four, K]
- **Visibility**: public; **Lines**: 40-43
- **Notes**: Key API.

### `theorem infinitePlace_card_eq_two`
- **Type**: `Fintype.card (InfinitePlace K) = 2`
- **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces`.
- **Uses from project**: [nrRealPlaces_eq_zero, nrComplexPlaces_eq_two]
- **Visibility**: public; **Lines**: 57-60

### `theorem infinitePlace_isComplex`
- **Type**: `∀ v, InfinitePlace.IsComplex v`
- **How**: `isTotallyComplex.isComplex`.
- **Uses from project**: [isTotallyComplex]; **Visibility**: public; **Lines**: 62-64
- **Notes**: used by LocalGlobal.

### `theorem exists_complexEmbedding_zeta`
- **Type**: `∃ σ : K →+* ℂ, σ ζ = exp(2πi/5)`
- **What**: There is a complex embedding sending ζ to exp(2πi/5).
- **How**: `Complex.isPrimitiveRoot_exp`, `AdjoinRoot.liftAlgHom` through `adjoinRootEquivCyclotomic.symm`.
- **Uses from project**: [ζ, zetaFivePolynomial, adjoinRootEquivCyclotomic, adjoinRootEquivCyclotomic_root]
- **Visibility**: public; **Lines**: 66-82

**File Summary — Embeddings.lean**: 6 theorems. Key API: `nrRealPlaces_eq_zero`,
`nrComplexPlaces_eq_two`, `isTotallyComplex`. `attribute [-instance] DivisionRing.toRatAlgebra`
locally. No sorry, no proof >30 lines.

---

## RingOfIntegers.lean

### `theorem zeta_integral`
- **Type**: `ζ ∈ integralClosure ℤ K`
- **How**: `IsPrimitiveRoot.isIntegral`.
- **Uses from project**: [ζ, zeta_isPrimitiveRoot]; **Visibility**: public; **Lines**: 32-33
- **Notes**: Key API.

### `noncomputable def zetaInt`
- **Type**: `𝓞 K := ⟨ζ, zeta_integral⟩`
- **What**: ζ as an element of 𝓞 K.
- **Uses from project**: [ζ, zeta_integral]; **Visibility**: public; **Lines**: 36
- **Notes**: Key API — used everywhere downstream.

### `theorem zetaInt_pow_five`
- **Type**: `zetaInt ^ 5 = 1`
- **How**: `Subtype.ext` + `zeta_pow_five`.
- **Uses from project**: [zetaInt, zeta_pow_five]; **Visibility**: public; **Lines**: 39-40
- **Notes**: Key API.

### `theorem zetaInt_sum_eq_zero`
- **Type**: `1 + zetaInt + … + zetaInt^4 = 0`
- **How**: `Subtype.ext` + `zeta_sum_eq_zero`.
- **Uses from project**: [zetaInt, zeta_sum_eq_zero]; **Visibility**: public; **Lines**: 43-44
- **Notes**: Key API (PrimeSplitting, Units).

### `abbrev integralPowerBasis`
- **Type**: `PowerBasis ℤ (𝓞 K) := zeta_isPrimitiveRoot.integralPowerBasis`
- **What**: Mathlib integral power basis 1,ζ,ζ²,ζ³.
- **Uses from project**: [zeta_isPrimitiveRoot]; **Visibility**: public; **Lines**: 47-48

### `theorem integralPowerBasis_gen`
- **Type**: `integralPowerBasis.gen = zeta_isPrimitiveRoot.toInteger`
- **Uses from project**: [integralPowerBasis, zeta_isPrimitiveRoot]; **Lines**: 51-52

### `theorem integralPowerBasis_dim`
- **Type**: `integralPowerBasis.dim = 4`
- **Uses from project**: [integralPowerBasis, zeta_isPrimitiveRoot]; **Lines**: 54-55

### `def integralBasisVectors`
- **Type**: `Fin 4 → K := ![1, ζ, ζ^2, ζ^3]`
- **Uses from project**: [ζ]; **Visibility**: public; **Lines**: 58

### `theorem span_integralBasisVectors_eq`
- **Type**: `Submodule.span ℤ (range integralBasisVectors) = toSubmodule (integralClosure ℤ K)`
- **What**: 1,ζ,ζ²,ζ³ is an integral basis (ℤ-span = 𝓞 K).
- **How**: `mod-by-monic` argument: `degree_modByMonic_lt`, `aeval_eq_sum_range'`,
  `isIntegralClosure_adjoin_singleton`, `adjoin_singleton_eq_range_aeval`.
- **Uses from project**: [integralBasisVectors, ζ, zeta_sum_eq_zero, zeta_integral, zeta_isPrimitiveRoot]
- **Visibility**: public; **Lines**: 62-109
- **Notes**: proof >30 lines (~48). Key supporting result.

### `noncomputable def concreteIntegralBasis`
- **Type**: `Basis (Fin 4) ℤ (𝓞 K)`
- **What**: 1,ζ,ζ²,ζ³ packaged as a genuine ℤ-basis.
- **How**: reindex of `integralPowerBasis.basis`.
- **Uses from project**: [integralPowerBasis, integralPowerBasis_dim]
- **Visibility**: public; **Lines**: 112-113
- **Notes**: Key API (Discriminant, PrimeSplitting finrank computations).

### `theorem concreteIntegralBasis_apply`
- **Type**: `algebraMap (𝓞 K) K (concreteIntegralBasis i) = integralBasisVectors i`
- **How**: `fin_cases` + simp.
- **Uses from project**: [concreteIntegralBasis, integralBasisVectors]; **Lines**: 116-119

### `theorem span_integralBasisVectors_eq_integralBasis`
- **Type**: span equals span of `NumberField.integralBasis K`
- **How**: `mem_span_integralBasis`, `RingHom.mem_range`.
- **Uses from project**: [integralBasisVectors, span_integralBasisVectors_eq]; **Lines**: 124-135

### `abbrev concreteRingOfIntegers`
- **Type**: `Subalgebra ℤ K := Algebra.adjoin ℤ {ζ}`
- **What**: The order ℤ[ζ].
- **Uses from project**: [ζ]; **Lines**: 138

### `theorem isIntegralClosure_adjoin_zeta`
- **Type**: `IsIntegralClosure (adjoin ℤ {ζ}) ℤ K`
- **How**: `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`.
- **Uses from project**: [ζ, zeta_isPrimitiveRoot]; **Lines**: 141-143

### `theorem integralPowerBasis_adjoin_gen_eq_top`
- **Type**: `adjoin ℤ {integralPowerBasis.gen} = ⊤`
- **Uses from project**: [integralPowerBasis]; **Lines**: 146-148

### `theorem ringOfIntegers_eq`
- **Type**: `integralClosure ℤ K = concreteRingOfIntegers`
- **What**: 𝓞 K = ℤ[ζ] (monogenicity).
- **How**: `le_antisymm` via `isIntegralClosure_adjoin_zeta`, `adjoin_le`.
- **Uses from project**: [concreteRingOfIntegers, zeta_integral, isIntegralClosure_adjoin_zeta]
- **Visibility**: public; **Lines**: 151-156
- **Notes**: HEADLINE (ring of integers).

**File Summary — RingOfIntegers.lean**: 16 decls (def/abbrev 6, theorem 10). Key API:
`zetaInt`, `zetaInt_pow_five`, `zetaInt_sum_eq_zero`, `concreteIntegralBasis`,
`integralBasisVectors`. No sorry, no set_option. `span_integralBasisVectors_eq` ~48 lines (>30).

---

## Discriminant.lean

### `theorem numberField_discr_eq`
- **Type**: `NumberField.discr K = 125`
- **What**: disc ℚ(ζ₅) = 5³.
- **How**: `IsCyclotomicExtension.Rat.discr_prime` + norm_num.
- **Uses from project**: [K]; **Visibility**: public; **Lines**: 34-37
- **Notes**: HEADLINE (discriminant). Key API (ClassGroup, PrimeSplitting different).

### `theorem concreteIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ concreteIntegralBasis = 125`
- **How**: `NumberField.discr_eq_discr` + `numberField_discr_eq`.
- **Uses from project**: [concreteIntegralBasis, numberField_discr_eq]; **Lines**: 40-43

### `theorem integralBasis_discr`
- **Type**: `Algebra.discr ℚ (NumberField.integralBasis K) = 125`
- **How**: `NumberField.coe_discr` + `numberField_discr_eq`.
- **Uses from project**: [numberField_discr_eq, K]; **Lines**: 46-50

**File Summary — Discriminant.lean**: 3 theorems. Key API: `numberField_discr_eq`. No sorry,
no set_option, no proof >30 lines.

---

## PrimeSplitting.lean (1353 lines)

### `private theorem gen_eq_zetaInt`
- **Type**: `integralPowerBasis.gen = zetaInt`
- **Uses from project**: [zeta_isPrimitiveRoot, zetaInt]; **Lines**: 35-36

### `private def sig2 / sig3 / sig4` and `private theorem sig2_zeta / sig3_zeta / sig4_zeta`
- **Type**: `K ≃ₐ[ℚ] K` resp. `sigN ζ = ζ^N`
- **What**: PRIVATE re-derivation of the σ₂,σ₃,σ₄ automorphisms (already in Galois.lean as
  `sigmaTwo` etc.) because the public ones live in a later file in the import order.
- **How**: `fromZetaAut` / `fromZetaAut_spec`.
- **Uses from project**: [zeta_isPrimitiveRoot, ζ]; **Lines**: 39-61
- **Notes**: DUPLICATION smell vs Galois.lean.

### `private theorem autEq'`
- **Type**: `σ = 1 ∨ σ = sig2 ∨ σ = sig3 ∨ σ = sig4`
- **What**: PRIVATE copy of Galois `autEq'` (with `1` instead of `idAut`).
- **Uses from project**: [sig2/3/4, sigN_zeta, zeta_isPrimitiveRoot]; **Lines**: 63-78
- **Notes**: DUPLICATION smell.

### `private theorem prod_aut_apply`
- **Type**: `∏ σ, σ x = x * sig2 x * sig3 x * sig4 x`
- **What**: The product over the Galois group is the explicit product of conjugates.
- **How**: distinctness of the four automorphisms via `pow_inj`, `Finset.prod_insert`.
- **Uses from project**: [sig2/3/4, sigN_zeta, zeta_isPrimitiveRoot, autEq']; **Lines**: 81-106
- **Notes**: ~26 lines. Generic-looking (the "product of conjugates = norm" pattern).

### `private theorem intNorm_eq`
- **Type**: from a conjugate-product identity = n, conclude `Algebra.norm ℤ x = n`
- **How**: `Algebra.norm_eq_prod_automorphisms`, `prod_aut_apply`, `Algebra.coe_norm_int`.
- **Uses from project**: [prod_aut_apply, sig2/3/4]; **Lines**: 109-124
- **Notes**: Generic-looking; reused throughout this file for many norm computations.

### `private theorem minpoly_gen_eq`
- **Type**: `minpoly ℤ integralPowerBasis.gen = X^4+X^3+X^2+X+C 1`
- **How**: `minpoly.isIntegrallyClosed_dvd`, monic-degree counting.
- **Uses from project**: [gen_eq_zetaInt, zetaInt_sum_eq_zero, zeta_isPrimitiveRoot]; **Lines**: 126-156
- **Notes**: proof ~30 lines.

### `private def residueHom`
- **Type**: `𝓞 K →ₐ[ℤ] ZMod p` (ζ ↦ r where r is a root of Φ₅ mod p)
- **How**: `integralPowerBasis.lift` with `minpoly_gen_eq`.
- **Uses from project**: [zeta_isPrimitiveRoot, minpoly_gen_eq]; **Lines**: 159-166
- **Notes**: Central Kummer–Dedekind machinery. Generic-looking pattern.

### `private theorem residueHom_zetaInt`
- **Type**: `residueHom p r hr zetaInt = (r : ZMod p)`
- **Uses from project**: [residueHom, gen_eq_zetaInt, zeta_isPrimitiveRoot]; **Lines**: 168-172

### `private theorem ker_residueHom`
- **Type**: `ker residueHom = span {p, zetaInt - r}`
- **How**: `sub_dvd_eval_sub`, `intCast_zmod_eq_zero_iff_dvd`, span membership.
- **Uses from project**: [residueHom, residueHom_zetaInt, zeta_isPrimitiveRoot, zetaInt]; **Lines**: 174-221
- **Notes**: proof >30 lines (~47).

### `private theorem residueHom_surjective`
- **Type**: `Function.Surjective (residueHom p r hr)`
- **How**: `ZMod.intCast_surjective`.
- **Uses from project**: [residueHom]; **Lines**: 223-228

### `private theorem isMaximal_span_pair`
- **Type**: `(span {p, zetaInt - r}).IsMaximal`
- **How**: `RingHom.ker_isMaximal_of_surjective` + `ker_residueHom`.
- **Uses from project**: [ker_residueHom, residueHom, residueHom_surjective]; **Lines**: 230-234
- **Notes**: Key API for splitting proofs (5, 11, generic p).

### `private theorem absNorm_span_pair`
- **Type**: `absNorm (span {p, zetaInt - r}) = p`
- **How**: `quotientKerEquivOfSurjective`, `Nat.card_zmod`.
- **Uses from project**: [ker_residueHom, residueHom, residueHom_surjective]; **Lines**: 236-242
- **Notes**: Key API.

### `theorem norm_one_sub_zeta`
- **Type**: `Algebra.norm ℚ (1 - ζ) = 5`
- **How**: `IsPrimitiveRoot.sub_one_norm_isPrimePow`.
- **Uses from project**: [ζ, zeta_isPrimitiveRoot, degree_eq_four]; **Lines**: 248-260

### `theorem norm_one_add_zeta`
- **Type**: `Algebra.norm ℚ (1 + ζ) = 1`
- **What**: 1+ζ is a cyclotomic unit.
- **How**: factor 1-ζ² = (1-ζ)(1+ζ); `sub_one_norm_isPrimePow` + `norm_one_sub_zeta`.
- **Uses from project**: [ζ, zeta_isPrimitiveRoot, degree_eq_four, norm_one_sub_zeta]; **Lines**: 264-280
- **Notes**: justifies `fundamentalUnit`.

### `def normForm`
- **Type**: `{R} [CommRing R] (a b c d : R) : R` — the explicit quartic norm form
- **What**: N(a+bζ+cζ²+dζ³) as a polynomial in a,b,c,d.
- **Uses from project**: []; **Visibility**: public; **Lines**: 283-293
- **Notes**: Generic over R; field-specific coefficients.

### `private def zetaCoords / normPairA / normPairB / normPairC / zetaPair`
- **Type**: helpers in K / ℚ
- **What**: coordinate element and the half-trace decomposition used to factor the norm form.
- **Uses from project**: [ζ]; **Lines**: 295-307

### `private theorem sig2_zetaCoords / sig3_zetaCoords / sig4_zetaCoords`
- **Type**: action of each σ on a coordinate vector
- **How**: `sigN_zeta` + power reductions (`zeta_pow_five`, `zeta_sum_eq_zero`), `ring`.
- **Uses from project**: [zetaCoords, sigN_zeta, zeta_sum_eq_zero, zeta_pow_five, ζ]; **Lines**: 309-355

### `private theorem zetaCoords_mul_sig4 / sig2_zetaCoords_mul_sig3 / normPair_mul_eq_normForm`
- **What**: assemble the product of the four conjugates into `normForm`.
- **How**: `linear_combination`, `ring_nf`, half-trace `zetaPair² = 1 - zetaPair`.
- **Uses from project**: [zetaCoords, normPairA/B/C, zetaPair, normForm, zeta_*]; **Lines**: 357-409

### `theorem norm_eq_normForm`
- **Type**: `Algebra.norm ℚ (a•1 + b•ζ + c•ζ² + d•ζ³) = normForm a b c d`
- **How**: `norm_eq_prod_automorphisms`, `prod_aut_apply`, the sigN_zetaCoords lemmas.
- **Uses from project**: [zetaCoords, prod_aut_apply, sigN_zetaCoords, zetaCoords_mul_sig4, sig2_zetaCoords_mul_sig3, normPair_mul_eq_normForm, normForm, ζ]; **Lines**: 412-434

### `theorem intNorm_eq_normForm`
- **Type**: `Algebra.norm ℤ (a•1+b•zetaInt+…) = normForm a b c d` (over ℤ)
- **How**: `Algebra.coe_norm_int` + `norm_eq_normForm`.
- **Uses from project**: [zetaInt, ζ, norm_eq_normForm, normForm]; **Lines**: 437-451

### `theorem isUnit_iff_normForm`
- **Type**: `IsUnit (a•1+…) ↔ (normForm a b c d).natAbs = 1`
- **How**: `NumberField.isUnit_iff_norm`, `intNorm_eq_normForm`.
- **Uses from project**: [zetaInt, intNorm_eq_normForm, normForm]; **Lines**: 454-466
- **Notes**: the explicit unit equation.

### `theorem span_five_eq`
- **Type**: `span {5} = span {1 - zetaInt} ^ 4`
- **What**: (5) = (1-ζ)⁴ (total ramification).
- **How**: `span_singleton_eq_span_singleton` + explicit unit via `linear_combination`.
- **Uses from project**: [zetaInt, zetaInt_sum_eq_zero, zetaInt_pow_five]; **Lines**: 470-476
- **Notes**: Key API.

### `private theorem span_one_sub_zetaInt_eq_pair`
- **Type**: `span {1 - zetaInt} = span {5, zetaInt - 1}`
- **Uses from project**: [zetaInt, span_five_eq]; **Lines**: 478-491

### `theorem isPrime_span_one_sub_zeta`
- **Type**: `(span {1 - zetaInt}).IsPrime`
- **How**: `isMaximal_span_pair 5 1` + the pair rewrite; `decide` for root condition.
- **Uses from project**: [zetaInt, span_one_sub_zetaInt_eq_pair, isMaximal_span_pair]; **Lines**: 494-499
- **Notes**: HEADLINE-ish (the prime above 5).

### `theorem absNorm_span_one_sub_zeta`
- **Type**: `absNorm (span {1 - zetaInt}) = 5`
- **Uses from project**: [zetaInt, span_one_sub_zetaInt_eq_pair, absNorm_span_pair]; **Lines**: 502-504

### `theorem liesOver_span_one_sub_zeta`
- **Type**: `(span {1 - zetaInt}).LiesOver (span {5})`
- **Uses from project**: [zetaInt, isPrime_span_one_sub_zeta, span_five_eq]; **Lines**: 507-514

### `theorem inertiaDeg_span_one_sub_zeta`
- **Type**: `inertiaDeg = 1`
- **How**: `absNorm_eq_pow_inertiaDeg'` + `Prime.pow_eq_iff`.
- **Uses from project**: [zetaInt, liesOver_span_one_sub_zeta, absNorm_span_one_sub_zeta]; **Lines**: 517-524

### `theorem ramificationIdx_span_one_sub_zeta`
- **Type**: `ramificationIdx = 4`
- **How**: `ramificationIdx_spec`, `span_five_eq`, absNorm divisibility.
- **Uses from project**: [zetaInt, span_five_eq, absNorm_span_one_sub_zeta, concreteIntegralBasis]; **Lines**: 527-549
- **Notes**: ~23 lines.

### `theorem absNorm_span_two`
- **Type**: `absNorm (span {2}) = 16`
- **How**: `absNorm_span_singleton`, `norm_algebraMap`, finrank=4.
- **Uses from project**: [concreteIntegralBasis]; **Lines**: 552-558

### `private theorem quotient_zeta_ne_one_of_two_mem`
- **Type**: in 𝓞 K / M with 2 ∈ M, `mk M zetaInt ≠ 1`
- **Uses from project**: [zetaInt, zetaInt_sum_eq_zero]; **Lines**: 560-572

### `private theorem absNorm_maximal_over_span_two_eq_sixteen`
- **Type**: any maximal M ⊇ (2) has absNorm 16
- **What**: residue field of any prime over 2 is 𝔽₁₆ (order of ζ is 5 ⇒ f=4).
- **How**: `FiniteField.pow_card`, `orderOf_eq_prime`, `5 ∣ 2^k - 1` ⇒ k=4.
- **Uses from project**: [zetaInt, zetaInt_pow_five, quotient_zeta_ne_one_of_two_mem, absNorm_span_two]; **Lines**: 574-621
- **Notes**: proof >30 lines (~48).

### `theorem isPrime_span_two`
- **Type**: `(span {2}).IsPrime`
- **What**: 2 is inert.
- **How**: maximal M over (2) has norm 16 = norm(2), so M = (2); `eq_of_le_of_absNorm_eq` (Common).
- **Uses from project**: [absNorm_span_two, absNorm_maximal_over_span_two_eq_sixteen, eq_of_le_of_absNorm_eq (Common)]; **Lines**: 624-634
- **Notes**: HEADLINE (2 inert).

### `theorem liesOver_span_two / inertiaDeg_span_two`
- **Type**: `(span {2}).LiesOver (span {2})`; `inertiaDeg = 4`
- **Uses from project**: [isPrime_span_two, absNorm_span_two, liesOver_span_two]; **Lines**: 637-654

### `private theorem nineteen_x_eq / nineteen_y_eq`
- **Type**: factorizations of 19 in 𝓞 K
- **Uses from project**: [zetaInt, zetaInt_pow_five, zetaInt_sum_eq_zero]; **Lines**: 656-662

### `private theorem span_pair_nineteen_left / span_pair_nineteen_right`
- **Type**: `span {19, …} = span {single generator}`
- **Uses from project**: [zetaInt, nineteen_x_eq, nineteen_y_eq]; **Lines**: 664-687

### `private theorem absNorm_span_x / absNorm_span_y`
- **Type**: `absNorm (span {…}) = 361`
- **How**: `intNorm_eq` with explicit conjugate products = 361.
- **Uses from project**: [zetaInt, intNorm_eq, sigN_zeta, ζ, zeta_pow_five, zeta_sum_eq_zero]; **Lines**: 689-751
- **Notes**: each ~30 lines.

### `private theorem absNorm_ne_nineteen`
- **Type**: `∀ P, absNorm P ≠ 19`
- **What**: Φ₅ has no root mod 19, so no prime of norm 19.
- **How**: `ZMod.ringEquivOfPrime`, `decide` over ZMod 19.
- **Uses from project**: [zetaInt, zetaInt_sum_eq_zero]; **Lines**: 754-772

### `private theorem isPrime_of_absNorm_361`
- **Type**: `absNorm (span {g}) = 361 → (span {g}).IsPrime`
- **How**: maximal M ⊇ (g), norm ∈ {1,19,361}, rule out via `absNorm_ne_nineteen`; `eq_of_le_of_absNorm_eq`.
- **Uses from project**: [absNorm_ne_nineteen, eq_of_le_of_absNorm_eq (Common)]; **Lines**: 774-798

### `theorem span_nineteen_eq`
- **Type**: `span {19} = span {19, x} * span {19, y}`
- **What**: 19 splits into two degree-2 primes.
- **Uses from project**: [zetaInt, span_pair_nineteen_left/right, zetaInt_pow_five, zetaInt_sum_eq_zero]; **Lines**: 802-812
- **Notes**: HEADLINE-ish (19 = product of two f=2 primes).

### `theorem isPrime_primesAboveNineteen`
- **Type**: both primes above 19 are prime
- **Uses from project**: [span_pair_nineteen_left/right, isPrime_of_absNorm_361, absNorm_span_x/y]; **Lines**: 815-822

### `private theorem elevenA / elevenB / elevenC`
- **Type**: ζ-identities behind 11 = product of four conjugates
- **Uses from project**: [ζ, zeta_pow_five, zeta_sum_eq_zero]; **Lines**: 824-831

### `private theorem norm_eleven_orbit`
- **Type**: from a conjugate-product identity, `absNorm (span {w}) = 11`
- **How**: `intNorm_eq` + elevenA/B/C.
- **Uses from project**: [intNorm_eq, sigN_zeta, elevenA/B/C, ζ]; **Lines**: 835-846
- **Notes**: shared by the four primes above 11.

### `private theorem absNorm_span_u3 / u4 / u5 / u9`
- **Type**: `absNorm (span {…}) = 11`
- **Uses from project**: [zetaInt, norm_eleven_orbit, sigN_zeta, ζ, zeta_pow_five]; **Lines**: 848-918

### `private theorem span_pair_eleven_three / four / five / nine`
- **Type**: `span {11, zetaInt - r} = span {single generator}`
- **How**: `eq_of_le_of_absNorm_eq`, `absNorm_span_pair`, `decide` root checks.
- **Uses from project**: [zetaInt, eq_of_le_of_absNorm_eq (Common), absNorm_span_uN, absNorm_span_pair]; **Lines**: 920-964

### `theorem span_eleven_eq`
- **Type**: `span {11} = product of four primes (11, ζ - r)`
- **What**: 11 splits completely.
- **Uses from project**: [zetaInt, span_pair_eleven_*, zetaInt_pow_five, zetaInt_sum_eq_zero]; **Lines**: 968-987
- **Notes**: HEADLINE-ish.

### `theorem isPrime_primeAboveEleven`
- **Type**: `(span {11, zetaInt - r}).IsPrime` for r ∈ {3,4,5,9}
- **Uses from project**: [zetaInt, isMaximal_span_pair]; **Lines**: 990-997

### `private theorem one_mod_five_of_splits_completely`
- **Type**: existence of a degree-1 prime ⇒ p ≡ 1 mod 5
- **How**: residue field 𝔽_p contains an order-5 element ⇒ 5 ∣ p-1.
- **Uses from project**: [zetaInt, zetaInt_pow_five, zetaInt_sum_eq_zero]; **Lines**: 999-1044
- **Notes**: proof >30 lines (~46).

### `private theorem splits_completely_of_one_mod_five`
- **Type**: p ≡ 1 mod 5 ⇒ a degree-1 prime exists
- **How**: order-5 generator g^m in (ZMod p)ˣ gives a root of Φ₅; `isMaximal_span_pair`.
- **Uses from project**: [zetaInt, isMaximal_span_pair, absNorm_span_pair]; **Lines**: 1046-1093
- **Notes**: proof >30 lines (~48).

### `theorem splits_completely_iff`
- **Type**: `(∃ degree-1 prime over p) ↔ p % 5 = 1` (p ≠ 5)
- **Uses from project**: [one_mod_five_of_splits_completely, splits_completely_of_one_mod_five]; **Lines**: 1096-1101
- **Notes**: HEADLINE (splitting law).

### `theorem ramified_iff_eq_five`
- **Type**: `(∃ P prime, span {p} ≤ P²) ↔ p = 5`
- **What**: ramification ⇔ p divides disc 125 ⇔ p = 5.
- **How**: different ideal: `not_isUnramifiedAt…`, `dvd_differentIdeal_iff`,
  `absNorm_differentIdeal`, `numberField_discr_eq`. Uses Common helpers.
- **Uses from project**: [zetaInt, concreteIntegralBasis, numberField_discr_eq, span_five_eq, isPrime_span_one_sub_zeta, not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow (Common), not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ (Common)]; **Lines**: 1105-1150
- **Notes**: HEADLINE (ramification). proof >30 lines (~46).

### `theorem ramificationIdx_span_two`
- **Type**: `(span {2}).ramificationIdx (span {2}) = 1`
- **How**: `ramificationIdx_spec` + `ramified_iff_eq_five 2`.
- **Uses from project**: [isPrime_span_two, ramified_iff_eq_five]; **Lines**: 1153-1164

### `abbrev zetaFivePolynomialMod`
- **Type**: `(ZMod p)[X] := X^4+X^3+X^2+X+C 1`
- **Uses from project**: []; **Lines**: 1182-1183

### `private theorem orderOf_unitOfCoprime_five_eq_four_iff`
- **Type**: `orderOf (unitOfCoprime p) = 4 ↔ p % 5 = 2 ∨ p % 5 = 3`
- **How**: case split on p mod 5 with `decide` per residue.
- **Uses from project**: []; **Lines**: 1185-1278
- **Notes**: proof >30 lines (~94). Generic-looking ((ZMod 5)ˣ order arithmetic).

### `private theorem zetaFivePolynomialMod_eq_cyclotomic`
- **Type**: `zetaFivePolynomialMod p = cyclotomic 5 (ZMod p)`
- **Uses from project**: [zetaFivePolynomialMod]; **Lines**: 1280-1285
- **Notes**: appears UNUSED.

### `theorem absNorm_differentIdeal_eq_oneHundredTwentyFive`
- **Type**: `absNorm (differentIdeal ℤ (𝓞 K)) = 125`
- **How**: `NumberField.absNorm_differentIdeal` + `numberField_discr_eq`.
- **Uses from project**: [numberField_discr_eq, K]; **Lines**: 1301-1304

### `theorem prime_dvd_differentIdeal_iff_eq_span_one_sub_zeta`
- **Type**: for prime P ≠ ⊥, `P ∣ differentIdeal ↔ P = span {1 - zetaInt}`
- **How**: norm divides 125 = 5³; `pow_sub_one_dvd_differentIdeal`; `span_five_eq`.
- **Uses from project**: [zetaInt, span_five_eq, absNorm_span_one_sub_zeta, isPrime_span_one_sub_zeta, absNorm_differentIdeal_eq_oneHundredTwentyFive]; **Lines**: 1306-1350
- **Notes**: proof >30 lines (~44).

**File Summary — PrimeSplitting.lean**: ~58 decls (private machinery dominates). Key API:
`zetaInt`-relations, `isMaximal_span_pair`, `absNorm_span_pair`, `intNorm_eq`, `sigN_zeta`,
`eq_of_le_of_absNorm_eq` (Common), `span_five_eq`. Headlines: `splits_completely_iff`,
`ramified_iff_eq_five`, `isPrime_span_two`, `isPrime_span_one_sub_zeta`, `norm_eq_normForm`,
`isUnit_iff_normForm`. Apparently unused: `zetaFivePolynomialMod_eq_cyclotomic`,
`orderOf_unitOfCoprime_five_eq_four_iff` (no in-folder consumer found). No sorry, no set_option.
Many proofs >30 lines (>=8: ker_residueHom, absNorm_maximal_over_span_two_eq_sixteen,
one_mod_five_of_splits_completely, splits_completely_of_one_mod_five, ramified_iff_eq_five,
prime_dvd_differentIdeal_iff_eq_span_one_sub_zeta, orderOf_unitOfCoprime_five_eq_four_iff,
minpoly_gen_eq).

---

## ClassGroup.lean

### `abbrev zetaFractionalIdeal`
- **Type**: `FractionalIdeal (𝓞 K)⁰ K := spanSingleton … ζ`
- **Uses from project**: [ζ]; **Lines**: 31-32

### `abbrev ramifiedPrimeFractionalIdeal`
- **Type**: `(span {1 - zetaInt} : FractionalIdeal …)`
- **Uses from project**: [zetaInt]; **Lines**: 34-35

### `theorem zeta_mem_fractionalIdeal`
- **Type**: `ζ ∈ zetaFractionalIdeal`
- **Uses from project**: [zetaFractionalIdeal, ζ]; **Lines**: 37-39

### `theorem zetaFractionalIdeal_absNorm`
- **Type**: `absNorm zetaFractionalIdeal = |Algebra.norm ℚ ζ|`
- **Uses from project**: [zetaFractionalIdeal, ζ]; **Lines**: 41-43

### `theorem ramifiedPrimeFractionalIdeal_ne_zero`
- **Type**: `ramifiedPrimeFractionalIdeal ≠ 0`
- **How**: `span_singleton_eq_bot`, order-of-ζ contradiction.
- **Uses from project**: [ramifiedPrimeFractionalIdeal, zetaInt, ζ, zeta_isPrimitiveRoot]; **Lines**: 45-56

### `theorem classNumber_eq_one`
- **Type**: `NumberField.classNumber K = 1`
- **What**: ℚ(ζ₅) has class number 1.
- **How**: Minkowski bound < 2 via `…isPrincipalIdealRing_of_isPrincipal_of_pow_le…`, real
  estimate `√125 < 12`, `Real.pi_gt_d2`, `nlinarith`.
- **Uses from project**: [nrComplexPlaces_eq_two, degree_eq_four, numberField_discr_eq, K]; **Lines**: 74-102
- **Notes**: HEADLINE (class number). proof ~28 lines.

### `theorem isPrincipalIdealRing`
- **Type**: `IsPrincipalIdealRing (𝓞 K)`
- **How**: `classNumber_eq_one_iff`.
- **Uses from project**: [classNumber_eq_one]; **Lines**: 105-107
- **Notes**: HEADLINE (PID).

### `theorem uniqueFactorizationMonoid`
- **Type**: `UniqueFactorizationMonoid (𝓞 K)`
- **Uses from project**: [isPrincipalIdealRing]; **Lines**: 110-112

### `theorem classGroupStructure`
- **Type**: `Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1))`
- **How**: subsingleton from card 1, `MulEquiv.ofUnique`.
- **Uses from project**: [classNumber_eq_one]; **Lines**: 115-120
- **Notes**: HEADLINE (class group trivial).

### `abbrev unitIdealRepresentative`
- **Type**: `(Ideal (𝓞 K))⁰ := ⟨⊤, …⟩`
- **Uses from project**: []; **Lines**: 123

### `theorem classGroupRepresentative`
- **Type**: `∀ C, C = ClassGroup.mk0 unitIdealRepresentative`
- **Uses from project**: [classNumber_eq_one, unitIdealRepresentative]; **Lines**: 126-131

**File Summary — ClassGroup.lean**: 11 decls (abbrev 3, theorem 8). Key API: `classNumber_eq_one`.
Headlines: `classNumber_eq_one`, `isPrincipalIdealRing`, `classGroupStructure`. No sorry, no
set_option. `classNumber_eq_one` ~28 lines.

---

## Units.lean

### `noncomputable def torsionGenerator`
- **Type**: `(𝓞 K)ˣ` — the unit -ζ with inverse -ζ⁴
- **Uses from project**: [zetaInt, zetaInt_pow_five]; **Lines**: 35-39
- **Notes**: Key API.

### `def torsionUnits`
- **Type**: `Set ((𝓞 K)ˣ) := {u | ∃ k : Fin 10, u = torsionGenerator ^ k.val}`
- **Uses from project**: [torsionGenerator]; **Lines**: 42

### `private theorem torsionOrder_eq'`
- **Type**: `Units.torsionOrder K = 10`
- **How**: `IsCyclotomicExtension.Rat.torsionOrder_eq`, `if_neg (¬ Even 5)`.
- **Uses from project**: [K]; **Lines**: 45-46

### `private theorem neg_zeta_isPrimitiveRoot`
- **Type**: `IsPrimitiveRoot (-ζ) 10`
- **How**: `orderOf_mul_eq_mul_orderOf_of_coprime`, `orderOf_neg_one`.
- **Uses from project**: [ζ, zeta_isPrimitiveRoot]; **Lines**: 48-58

### `theorem torsionUnits_eq`
- **Type**: `{u | IsOfFinOrder u} = torsionUnits`
- **What**: torsion subgroup = μ₁₀.
- **How**: `rootsOfUnity_eq_torsion`, `eq_pow_of_pow_eq_one` of `neg_zeta_isPrimitiveRoot`.
- **Uses from project**: [torsionGenerator, torsionUnits, torsionOrder_eq', neg_zeta_isPrimitiveRoot, ζ, zeta_pow_five]; **Lines**: 60-84
- **Notes**: proof ~25 lines. Key API.

### `theorem torsionOrder_eq_ten`
- **Type**: `Units.torsionOrder K = 10`
- **Uses from project**: [torsionOrder_eq']; **Lines**: 88-89
- **Notes**: HEADLINE (torsion order).

### `theorem unitRank_eq_one`
- **Type**: `Units.rank K = 1`
- **How**: signature (0,2) ⇒ rank r₁+r₂-1.
- **Uses from project**: [nrRealPlaces_eq_zero, nrComplexPlaces_eq_two]; **Lines**: 93-95
- **Notes**: HEADLINE (Dirichlet rank). Key API.

### `noncomputable def fundamentalUnit`
- **Type**: `(𝓞 K)ˣ` — the cyclotomic unit 1+ζ with inverse -(ζ+ζ³)
- **Uses from project**: [zetaInt, zetaInt_sum_eq_zero]; **Lines**: 99-103
- **Notes**: HEADLINE (fundamental unit). Used by LocalGlobal.

### `noncomputable def fundamentalUnitSystem`
- **Type**: `Fin (Units.rank K) → (𝓞 K)ˣ := fun _ => fundamentalUnit`
- **Uses from project**: [fundamentalUnit]; **Lines**: 106-107

### `private theorem exists_eq_torsion_mul_fundSystem_zpow`
- **Type**: every unit = torsion · (fundSystem i₀)^n
- **How**: `closure_fundSystem_sup_torsion_eq_top`, `Subgroup.mem_sup`, subsingleton index.
- **Uses from project**: [unitRank_eq_one]; **Lines**: 111-133
- **Notes**: Generic rank-1 specialization.

### `private theorem fundSystem_zpow_mem_torsion`
- **Type**: (fundSystem i₀)^n torsion ⇒ n = 0
- **How**: `basisModTorsion`, `QuotientGroup.mk_zpow`, repr injectivity.
- **Uses from project**: []; **Lines**: 136-148

### `private theorem eq_torsionGenerator_pow_of_mem_torsion`
- **Type**: ζ' torsion ⇒ ∃ k : Fin 10, ζ' = torsionGenerator^k
- **Uses from project**: [torsionGenerator, torsionUnits_eq]; **Lines**: 151-156

### `theorem fundamentalUnitSystem_isFundamental`
- **Type**: `closure (range fundamentalUnitSystem) ⊔ torsion K = ⊤`
- **What**: 1+ζ together with μ₁₀ generates 𝓞ˣ.
- **How**: SORRY.
- **Uses from project**: [fundamentalUnitSystem]; **Lines**: 161-163
- **Notes**: **SORRY** — blocked (needs cyclotomic-unit index `[𝓞ˣ : cyclotomic units] = h⁺ = 1`,
  an Artin-type / regulator bound; same blocker class as the sibling ζ₈/ζ₅ studies).

### `theorem unit_eq_torsion_mul_fundamentalUnit_zpow`
- **Type**: every unit = ζ' · fundamentalUnit^n with ζ' torsion
- **How**: from `fundamentalUnitSystem_isFundamental`, `mem_closure_singleton`.
- **Uses from project**: [fundamentalUnitSystem, fundamentalUnit, fundamentalUnitSystem_isFundamental, unitRank_eq_one]; **Lines**: 166-181
- **Notes**: depends on the sorry above.

### `private theorem unitGroupStructure_bijective`
- **Type**: the coprod hom μ₁₀ × ℤ → 𝓞ˣ is bijective
- **How**: `torsionPowerHom`/`rankOnePowerHom` (Common), `fundSystem_zpow_mem_torsion`,
  `eq_torsionGenerator_pow_of_mem_torsion`, `neg_zeta_isPrimitiveRoot.pow_eq_one_iff_dvd`.
- **Uses from project**: [zetaInt, ζ, neg_zeta_isPrimitiveRoot, torsionGenerator, fundSystem_zpow_mem_torsion, exists_eq_torsion_mul_fundSystem_zpow, eq_torsionGenerator_pow_of_mem_torsion, torsionPowerHom (Common), rankOnePowerHom (Common)]; **Lines**: 183-226
- **Notes**: proof >30 lines (~44).

### `theorem unitGroupStructure`
- **Type**: `Nonempty ((𝓞 K)ˣ ≃* Multiplicative (ZMod 10) × Multiplicative (Fin 1 → ℤ))`
- **What**: 𝓞ˣ ≅ μ₁₀ × ℤ.
- **How**: `MulEquiv.ofBijective` + `unitGroupStructure_bijective`.
- **Uses from project**: [ζ, zeta_pow_five, torsionGenerator, torsionPowerHom (Common), rankOnePowerHom (Common), unitGroupStructure_bijective, unitRank_eq_one]; **Lines**: 229-249
- **Notes**: HEADLINE (unit group structure). Relies (transitively, via bijective) on
  `exists_eq_torsion_mul_fundSystem_zpow` (mathlib fundSystem), NOT on the sorry.

### `theorem regulator_eq`
- **Type**: `Units.regulator K = 2 * Real.log ((1 + √5) / 2)`
- **What**: regulator = 2 log φ.
- **How**: SORRY.
- **Uses from project**: [K]; **Lines**: 253-255
- **Notes**: **SORRY** — blocked (requires identifying mathlib's fundamental unit with 1+ζ;
  same Artin/regulator blocker class).

**File Summary — Units.lean**: 17 decls (def 4, theorem 13, of which 6 private). Key API:
`torsionGenerator`, `unitRank_eq_one`, `fundamentalUnit`, `torsionUnits_eq`. Headlines:
`torsionOrder_eq_ten`, `unitRank_eq_one`, `unitGroupStructure`, `fundamentalUnit`. **2 SORRY**:
`fundamentalUnitSystem_isFundamental`, `regulator_eq`. No set_option. `unitGroupStructure_bijective`
~44 lines (>30).

---

## Euclidean.lean

### `theorem normEuclidean`
- **Type**: `∀ a b, b ≠ 0 → ∃ q r, a = b*q+r ∧ |norm r| < |norm b|`
- **What**: ℤ[ζ₅] is norm-Euclidean.
- **How**: SORRY.
- **Uses from project**: []; **Lines**: 32-35
- **Notes**: **SORRY** — blocked (needs a covering/geometry-of-numbers argument for the
  norm-Euclidean inequality; same blocker class flagged in sibling memory notes).

**File Summary — Euclidean.lean**: 1 theorem. 1 SORRY (`normEuclidean`). No set_option.

---

## LocalGlobal.lean

### `def heightOneFive`
- **Type**: `HeightOneSpectrum (𝓞 K)` — the prime (1 - ζ)
- **Uses from project**: [zetaInt, isPrime_span_one_sub_zeta, absNorm_span_one_sub_zeta]; **Lines**: 35-43

### `abbrev vFive`
- **Type**: `FinitePlace K := FinitePlace.mk heightOneFive`
- **Uses from project**: [heightOneFive]; **Lines**: 45-46

### `example` (e=4 / f=1 at heightOneFive)
- **Type**: ramificationIdx = 4 / inertiaDeg = 1 over (5)
- **Uses from project**: [heightOneFive, ramificationIdx_span_one_sub_zeta, inertiaDeg_span_one_sub_zeta]; **Lines**: 48-54
- **Notes**: anonymous `example`s.

### `abbrev CompletionAtFive`
- **Type**: `heightOneFive.adicCompletion K`
- **Uses from project**: [heightOneFive]; **Lines**: 69-70

### `abbrev InfiniteCompletion`
- **Type**: `(v : InfinitePlace K) → Type := v.Completion`
- **Uses from project**: []; **Lines**: 84-85

### `private theorem complexEmbedding_norm_zeta_eq_one`
- **Type**: `‖φ ζ‖ = 1` for any φ : K →+* ℂ
- **How**: `Complex.norm_eq_one_of_pow_eq_one`.
- **Uses from project**: [ζ, zeta_isPrimitiveRoot]; **Lines**: 87-89
- **Notes**: used by `house_zeta`.

### `example` (InfiniteCompletion v ≃+* ℂ)
- **Uses from project**: [InfiniteCompletion, infinitePlace_isComplex]; **Lines**: 91-94

### `theorem infiniteCompletion_zeta_norm`
- **Type**: `‖algebraMap K (InfiniteCompletion v) ζ‖ = 1`
- **How**: `Completion.norm_coe`, `norm_embedding_eq`, `complexEmbedding_norm_zeta_eq_one`.
- **Uses from project**: [InfiniteCompletion, ζ, complexEmbedding_norm_zeta_eq_one]; **Lines**: 96-101

### `private theorem zeta_ne_zero`
- **Type**: `ζ ≠ 0`
- **Uses from project**: [ζ, zeta_isPrimitiveRoot]; **Lines**: 115-119
- **Notes**: used by product-formula example and `principalAdele_zeta_ne_zero`.

### `example` (product formula for ζ / for fundamentalUnit)
- **Uses from project**: [ζ, zeta_ne_zero, fundamentalUnit]; **Lines**: 121-134

### `abbrev CyclotomicFiveInfiniteAdeleRing`, `infinitePrincipalAdele_zeta`, `infinitePrincipalAdele_fundamentalUnit`
- **Type**: infinite adele ring + principal adeles of ζ and the fundamental unit
- **Uses from project**: [ζ, fundamentalUnit]; **Lines**: 148-155

### `example` (‖adele‖ = |norm|, denseRange)
- **Uses from project**: [infinitePrincipalAdele_zeta, ζ]; **Lines**: 157-163

### `theorem canonicalEmbedding_zetaInt_mem_integerLattice`
- **Type**: `canonicalEmbedding K (algebraMap _ K zetaInt) ∈ integerLattice K`
- **Uses from project**: [zetaInt]; **Lines**: 177-182

### `abbrev mixedEmbedding_zeta` + `example`s (convexBodyLT, fundamentalCone, normLeOne)
- **Uses from project**: [ζ]; **Lines**: 198-213

### `theorem polarSpace_nonempty`
- **Type**: `Nonempty (mixedEmbedding.polarSpace K)`
- **Uses from project**: []; **Lines**: 215-217

### `theorem house_zeta`
- **Type**: `NumberField.house ζ = 1`
- **How**: `canonicalEmbedding.norm_le_iff`, `complexEmbedding_norm_zeta_eq_one`, `norm_le_pi_norm`.
- **Uses from project**: [ζ, complexEmbedding_norm_zeta_eq_one]; **Lines**: 231-242

### `example` (0 < house of fundamentalUnit)
- **Uses from project**: [fundamentalUnit]; **Lines**: 244-250

### `abbrev CyclotomicFiveAdeleRing`, `principalAdele_zeta`, `principalAdele_fundamentalUnit`
- **Uses from project**: [ζ, fundamentalUnit]; **Lines**: 265-272

### `theorem principalAdele_zeta_ne_zero`
- **Type**: `principalAdele_zeta ≠ 0`
- **Uses from project**: [principalAdele_zeta, zeta_ne_zero]; **Lines**: 274-276

### `theorem principalAdele_fundamentalUnit_is_unit_everywhere`
- **Type**: `∀ v : FinitePlace K, v (algebraMap _ K fundamentalUnit) = 1`
- **How**: `norm_eq_one_iff_notMem`, prime-ideal argument from the inverse unit.
- **Uses from project**: [fundamentalUnit]; **Lines**: 278-298

### `abbrev cyclotomicFiveDedekindZeta`, `cyclotomicFiveDedekindZetaResidue` + `example`s
- **Type**: Dedekind zeta function/residue + positivity/class-number-formula identity
- **Uses from project**: []; **Lines**: 312-328

**File Summary — LocalGlobal.lean**: ~30 decls (many `example`s and `abbrev`s). Key API:
`complexEmbedding_norm_zeta_eq_one`, `zeta_ne_zero`. Headlines: `house_zeta`,
`infiniteCompletion_zeta_norm`, `principalAdele_fundamentalUnit_is_unit_everywhere`. No sorry,
no set_option, no proof >30 lines.

---

## CMField.lean

### `theorem isCMField`
- **Type**: `NumberField.IsCMField K`
- **How**: `IsCyclotomicExtension.Rat.isCMField`.
- **Uses from project**: [K]; **Lines**: 26-27
- **Notes**: HEADLINE (CM structure).

### `theorem cmField_isTotallyComplex`
- **Type**: `NumberField.IsTotallyComplex K`
- **Uses from project**: [isTotallyComplex]; **Lines**: 29-30

### `theorem cmField_quadratic_over_maximalRealSubfield`
- **Type**: `IsQuadraticExtension (maximalRealSubfield K) K`
- **How**: instance from `IsCMField`.
- **Uses from project**: [isCMField]; **Lines**: 32-35

### `theorem cmField_unitsRank_eq_maximalRealSubfield`
- **Type**: `Units.rank (maximalRealSubfield K) = Units.rank K`
- **How**: `IsCMField.units_rank_eq_units_rank`.
- **Uses from project**: [isCMField]; **Lines**: 37-41

**File Summary — CMField.lean**: 4 theorems. Headline: `isCMField`. No sorry, no set_option.
Imports only Embeddings (parallel branch off the linear chain).

---

## QuadraticSubfield.lean

### `theorem gaussSum_sq`
- **Type**: `(1 + 2ζ + 2ζ⁴)² = 5`
- **What**: the quadratic Gauss sum squares to 5 ⇒ √5 ∈ ℚ(ζ₅).
- **How**: `linear_combination` of `zeta_pow_five`, `zeta_sum_eq_zero`.
- **Uses from project**: [ζ, zeta_pow_five, zeta_sum_eq_zero]; **Lines**: 30-31
- **Notes**: HEADLINE (quadratic subfield). Key API in this file.

### `abbrev sqrtFivePolynomial`
- **Type**: `ℚ[X] := X^2 - C 5`
- **Uses from project**: []; **Lines**: 34

### `instance : Fact (Irreducible sqrtFivePolynomial)`
- **How**: `irreducible_of_degree_le_three_of_not_isRoot`, `5` not a rational square.
- **Uses from project**: [sqrtFivePolynomial]; **Lines**: 36-52

### `abbrev QSqrtFive`
- **Type**: `Type := AdjoinRoot sqrtFivePolynomial`
- **Uses from project**: [sqrtFivePolynomial]; **Lines**: 55

### `abbrev sqrtFiveRoot`
- **Type**: `QSqrtFive := AdjoinRoot.root sqrtFivePolynomial`
- **Uses from project**: [sqrtFivePolynomial, QSqrtFive]; **Lines**: 58

### `theorem sqrtFiveRoot_sq`
- **Type**: `sqrtFiveRoot ^ 2 = 5`
- **How**: `AdjoinRoot.eval₂_root`.
- **Uses from project**: [sqrtFiveRoot, sqrtFivePolynomial]; **Lines**: 61-65

### `abbrev gaussSum`
- **Type**: `K := 1 + 2ζ + 2ζ^4`
- **Uses from project**: [ζ]; **Lines**: 68

### `abbrev sqrtFiveSubfield`
- **Type**: `Subalgebra ℚ K := Algebra.adjoin ℚ {gaussSum}`
- **Uses from project**: [gaussSum]; **Lines**: 71

### `noncomputable def sqrtFiveToCyclotomic`
- **Type**: `QSqrtFive →ₐ[ℚ] K`
- **What**: embedding ℚ(√5) → ℚ(ζ₅), √5 ↦ Gauss sum.
- **How**: `AdjoinRoot.liftAlgHom` using `gaussSum_sq`.
- **Uses from project**: [QSqrtFive, sqrtFivePolynomial, gaussSum, gaussSum_sq]; **Lines**: 74-76

### `noncomputable def sqrtFiveEquivSubfield`
- **Type**: `QSqrtFive ≃ₐ[ℚ] sqrtFiveSubfield`
- **How**: `liftAlgHom` + `AlgEquiv.ofBijective`; surjectivity via `Algebra.adjoin_induction`.
- **Uses from project**: [QSqrtFive, sqrtFiveSubfield, sqrtFivePolynomial, gaussSum, gaussSum_sq, sqrtFiveRoot]; **Lines**: 79-110
- **Notes**: proof >30 lines (~31).

### `theorem sqrtFiveToCyclotomic_root`
- **Type**: `sqrtFiveToCyclotomic sqrtFiveRoot = gaussSum`
- **Uses from project**: [sqrtFiveToCyclotomic, sqrtFiveRoot, sqrtFivePolynomial, gaussSum]; **Lines**: 113-114

### `theorem sqrtFiveEquivSubfield_root`
- **Type**: `(sqrtFiveEquivSubfield sqrtFiveRoot : K) = gaussSum`
- **Uses from project**: [sqrtFiveEquivSubfield, sqrtFiveRoot, sqrtFivePolynomial, gaussSum]; **Lines**: 117-122

### `theorem sqrtFiveToCyclotomic_injective`
- **Type**: `Function.Injective sqrtFiveToCyclotomic`
- **Uses from project**: [sqrtFiveToCyclotomic]; **Lines**: 125-126

**File Summary — QuadraticSubfield.lean**: 13 decls (abbrev/def 8, theorem 4, instance 1).
Headlines: `gaussSum_sq` (√5 ∈ K, ℚ(√5) the quadratic subfield), `sqrtFiveToCyclotomic`.
No sorry, no set_option. `sqrtFiveEquivSubfield` ~31 lines. Imports only Galois (parallel branch).

---

## Cross-folder notes

- Common.lean helpers used here: `eq_of_le_of_absNorm_eq`, `torsionPowerHom`, `rankOnePowerHom`,
  `not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ`,
  `not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow`.
- PrimeSplitting re-derives `sig2/sig3/sig4/autEq'` privately, duplicating Galois.lean (import
  ordering: Galois's public `sigmaTwo` is not visible because PrimeSplitting imports Discriminant,
  which does import Galois transitively — so this duplication is avoidable).
</content>
