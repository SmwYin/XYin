# CyclotomicThree — Declaration Inventory

Folder: `XYin/NumberField/FieldExamples/CyclotomicThree/`
Field: `K = CyclotomicField 3 ℚ = ℚ(ζ₃) = ℚ(√-3)` (imaginary quadratic, disc −3, class number 1, Eisenstein integers).
Shared helpers live in `XYin/NumberField/FieldExamples/Common.lean` (namespace `NumberField.FieldExamples`).

All declarations are in namespace `NumberField.CyclotomicThree` unless noted. Every file opens a `noncomputable section`.

---

## Basic.lean

### `abbrev K`
- **Type**: `K : Type := CyclotomicField 3 ℚ`
- **What**: The running example field, the 3rd cyclotomic field ℚ(ζ₃).
- **How**: Definitional abbreviation of `CyclotomicField 3 ℚ`.
- **Hypotheses**: none
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 33
- **Notes**: —

### `instance : IsCyclotomicExtension {3} ℚ K`
- **Type**: `IsCyclotomicExtension {3} ℚ K`
- **What**: Records that `K` is the cyclotomic extension for `{3}`.
- **How**: `CyclotomicField.isCyclotomicExtension 3 ℚ`.
- **Hypotheses**: none
- **Uses from project**: []
- **Visibility**: public (instance)
- **Lines**: 35-36

### `abbrev ζ`
- **Type**: `ζ : K := IsCyclotomicExtension.zeta 3 ℚ K`
- **What**: A chosen primitive cube root of unity.
- **How**: mathlib's `zeta`.
- **Hypotheses**: none
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 39

### `theorem zeta_isPrimitiveRoot`
- **Type**: `IsPrimitiveRoot ζ 3`
- **What**: `ζ` is a primitive cube root of unity.
- **How**: `IsCyclotomicExtension.zeta_spec`.
- **Hypotheses**: none
- **Uses from project**: [ζ]
- **Visibility**: public
- **Lines**: 41-42
- **Notes**: Workhorse — used by 3+ across nearly every file.

### `theorem zeta_sq_add_zeta_add_one_eq_zero`
- **Type**: `ζ ^ 2 + ζ + 1 = 0`
- **What**: Defining quadratic relation Φ₃(ζ)=0.
- **How**: `zeta_isPrimitiveRoot.isRoot_cyclotomic`.
- **Hypotheses**: none
- **Uses from project**: [zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 45-46

### `theorem adjoin_zeta_eq_top`
- **Type**: `Algebra.adjoin ℚ ({ζ} : Set K) = ⊤`
- **What**: `K` is generated over ℚ by `ζ`.
- **How**: `IsCyclotomicExtension.adjoin_primitive_root_eq_top`.
- **Uses from project**: [zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 49-50

### `theorem degree_eq_two`
- **Type**: `Module.finrank ℚ K = 2`
- **What**: ℚ(ζ₃) is quadratic since φ(3)=2.
- **How**: `IsCyclotomicExtension.Rat.finrank` + `Nat.totient_prime`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 53-55

### `instance : Algebra.IsQuadraticExtension ℚ K`
- **Type**: `Algebra.IsQuadraticExtension ℚ K`
- **What**: K/ℚ is a quadratic extension.
- **How**: field `finrank_eq_two' := degree_eq_two`.
- **Uses from project**: [degree_eq_two]
- **Visibility**: public (instance)
- **Lines**: 57-58

### `abbrev zetaThreePolynomial`
- **Type**: `ℚ[X] := X ^ 2 + X + 1`
- **What**: The polynomial Φ₃ used to present K as an AdjoinRoot.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 65

### `instance : Fact (Irreducible zetaThreePolynomial)`
- **Type**: `Fact (Irreducible zetaThreePolynomial)`
- **What**: Φ₃ = X²+X+1 is irreducible over ℚ.
- **How**: rewrite to `cyclotomic_three` then `cyclotomic.irreducible_rat`.
- **Uses from project**: [zetaThreePolynomial]
- **Visibility**: public (instance)
- **Lines**: 67-70

### `abbrev KAdjoinRoot`
- **Type**: `Type := AdjoinRoot zetaThreePolynomial`
- **What**: AdjoinRoot presentation of ℚ(ζ₃).
- **Uses from project**: [zetaThreePolynomial]
- **Visibility**: public
- **Lines**: 73

### `theorem zetaThreePolynomial_eq_minpoly`
- **Type**: `zetaThreePolynomial = minpoly ℚ ζ`
- **What**: X²+X+1 is the minimal polynomial of ζ.
- **How**: `cyclotomic_three`, `minpoly_eq_cyclotomic_of_irreducible`.
- **Uses from project**: [zetaThreePolynomial, ζ, zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 76-80

### `def zetaMinpolyAdjoinRootPresentation`
- **Type**: `IsAdjoinRoot K (minpoly ℚ ζ)`
- **What**: K is an AdjoinRoot of minpoly(ζ).
- **How**: `IsAdjoinRoot.mkOfAdjoinEqTop` with integrality + `adjoin_primitive_root_eq_top`.
- **Uses from project**: [ζ, zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 83-86

### `abbrev adjoinRootEquivCyclotomic`
- **Type**: `KAdjoinRoot ≃ₐ[ℚ] K`
- **What**: AlgEquiv between the AdjoinRoot model and the cyclotomic field.
- **How**: `AdjoinRoot.algEquivOfEq` composed with `adjoinRootAlgEquiv`.
- **Uses from project**: [zetaThreePolynomial, ζ, zetaThreePolynomial_eq_minpoly, zetaMinpolyAdjoinRootPresentation]
- **Visibility**: public
- **Lines**: 93-96
- **Notes**: Used by Embeddings.

### `theorem adjoinRootEquivCyclotomic_root`
- **Type**: `adjoinRootEquivCyclotomic (AdjoinRoot.root zetaThreePolynomial) = ζ`
- **What**: The equivalence carries the formal root to ζ.
- **How**: `AdjoinRoot.algEquivOfEq_root` + simp.
- **Uses from project**: [adjoinRootEquivCyclotomic, zetaThreePolynomial, ζ, zetaMinpolyAdjoinRootPresentation]
- **Visibility**: public
- **Lines**: 99-105

### `theorem two_mul_zeta_add_one_sq`
- **Type**: `(2 * ζ + 1) ^ 2 = (-3 : K)`
- **What**: 2ζ+1 is a square root of −3 in K (the ℚ(√-3) identification).
- **How**: `calc` + `ring`, using zeta relation.
- **Uses from project**: [ζ, zeta_sq_add_zeta_add_one_eq_zero]
- **Visibility**: public
- **Lines**: 108-112

### `abbrev sqrtNegThreePolynomial`
- **Type**: `ℚ[X] := X ^ 2 + 3`
- **What**: Polynomial presenting ℚ(√-3).
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 115

### `instance : Fact (Irreducible sqrtNegThreePolynomial)`
- **Type**: `Fact (Irreducible sqrtNegThreePolynomial)`
- **What**: X²+3 irreducible over ℚ.
- **How**: `irreducible_of_degree_le_three_of_not_isRoot` + positivity (`nlinarith`).
- **Uses from project**: [sqrtNegThreePolynomial]
- **Visibility**: public (instance)
- **Lines**: 117-127

### `abbrev QSqrtNegThree`
- **Type**: `Type := AdjoinRoot sqrtNegThreePolynomial`
- **What**: ℚ(√-3) as an AdjoinRoot.
- **Uses from project**: [sqrtNegThreePolynomial]
- **Visibility**: public
- **Lines**: 130

### `abbrev sqrtNegThreeRoot`
- **Type**: `QSqrtNegThree := AdjoinRoot.root sqrtNegThreePolynomial`
- **What**: Formal √-3.
- **Uses from project**: [sqrtNegThreePolynomial]
- **Visibility**: public
- **Lines**: 133

### `abbrev zetaThreeRoot`
- **Type**: `KAdjoinRoot := AdjoinRoot.root zetaThreePolynomial`
- **What**: Formal primitive root in the X²+X+1 model.
- **Uses from project**: [zetaThreePolynomial]
- **Visibility**: public
- **Lines**: 136

### `theorem sqrtNegThreeRoot_sq`
- **Type**: `sqrtNegThreeRoot ^ 2 = (-3 : QSqrtNegThree)`
- **How**: `AdjoinRoot.eval₂_root` + ring.
- **Uses from project**: [sqrtNegThreeRoot, sqrtNegThreePolynomial]
- **Visibility**: public
- **Lines**: 138-144

### `theorem zetaThreeRoot_relation`
- **Type**: `zetaThreeRoot ^ 2 + zetaThreeRoot + 1 = 0`
- **How**: `AdjoinRoot.eval₂_root`.
- **Uses from project**: [zetaThreeRoot, zetaThreePolynomial]
- **Visibility**: public
- **Lines**: 146-148

### `def sqrtNegThreeToZetaThree`
- **Type**: `QSqrtNegThree →ₐ[ℚ] KAdjoinRoot`
- **What**: Sends √-3 ↦ 2ζ+1.
- **How**: `AdjoinRoot.liftAlgHom` with relation check via ring + `zetaThreeRoot_relation`.
- **Uses from project**: [sqrtNegThreePolynomial, KAdjoinRoot, zetaThreeRoot, zetaThreeRoot_relation]
- **Visibility**: public
- **Lines**: 151-159

### `theorem sqrtNegThreeToZetaThree_root` `@[simp]`
- **Type**: `sqrtNegThreeToZetaThree sqrtNegThreeRoot = 2 * zetaThreeRoot + 1`
- **How**: `AdjoinRoot.liftAlgHom_root`.
- **Uses from project**: [sqrtNegThreeToZetaThree, sqrtNegThreeRoot, zetaThreeRoot]
- **Visibility**: public
- **Lines**: 161-166

### `def zetaThreeToSqrtNegThree`
- **Type**: `KAdjoinRoot →ₐ[ℚ] QSqrtNegThree`
- **What**: Inverse map sending ζ ↦ (√-3 − 1)/2.
- **How**: `AdjoinRoot.liftAlgHom`, relation via `sqrtNegThreeRoot_sq`.
- **Uses from project**: [zetaThreePolynomial, QSqrtNegThree, sqrtNegThreeRoot, sqrtNegThreeRoot_sq]
- **Visibility**: public
- **Lines**: 169-178

### `theorem zetaThreeToSqrtNegThree_root` `@[simp]`
- **Type**: `zetaThreeToSqrtNegThree zetaThreeRoot = (sqrtNegThreeRoot - 1) / 2`
- **How**: `AdjoinRoot.liftAlgHom_root`.
- **Uses from project**: [zetaThreeToSqrtNegThree, zetaThreeRoot, sqrtNegThreeRoot]
- **Visibility**: public
- **Lines**: 180-185

### `def sqrtNegThreeEquivZetaThree`
- **Type**: `QSqrtNegThree ≃ₐ[ℚ] KAdjoinRoot`
- **What**: The two AdjoinRoot models are isomorphic.
- **How**: structure with `invFun`; both inverse directions via `AdjoinRoot.algHom_ext` + ring/ring_nf.
- **Uses from project**: [sqrtNegThreeToZetaThree, zetaThreeToSqrtNegThree, sqrtNegThreeRoot, zetaThreeRoot, *_root lemmas]
- **Visibility**: public
- **Lines**: 188-216
- **Notes**: proof ~29 lines.

### `theorem sqrtNegThreeEquivZetaThree_root` `@[simp]`
- **Type**: `sqrtNegThreeEquivZetaThree sqrtNegThreeRoot = 2 * zetaThreeRoot + 1`
- **How**: `sqrtNegThreeToZetaThree_root`.
- **Uses from project**: [sqrtNegThreeEquivZetaThree, sqrtNegThreeRoot, zetaThreeRoot, sqrtNegThreeToZetaThree_root]
- **Visibility**: public
- **Lines**: 218-221

### `def sqrtNegThreeEquivCyclotomic`
- **Type**: `QSqrtNegThree ≃ₐ[ℚ] K`
- **What**: ℚ(√-3) AdjoinRoot model ≅ cyclotomic K.
- **How**: compose `sqrtNegThreeEquivZetaThree.trans adjoinRootEquivCyclotomic`.
- **Uses from project**: [sqrtNegThreeEquivZetaThree, adjoinRootEquivCyclotomic]
- **Visibility**: public
- **Lines**: 224-225

### `theorem sqrtNegThreeEquivCyclotomic_root`
- **Type**: `sqrtNegThreeEquivCyclotomic sqrtNegThreeRoot = 2 * ζ + 1`
- **How**: `AlgEquiv.trans_apply`, `sqrtNegThreeEquivZetaThree_root`, `adjoinRootEquivCyclotomic_root`.
- **Uses from project**: [sqrtNegThreeEquivCyclotomic, sqrtNegThreeRoot, ζ, sqrtNegThreeEquivZetaThree_root, adjoinRootEquivCyclotomic_root]
- **Visibility**: public
- **Lines**: 227-231

### `instance : Fact (∀ r : ℚ, r ^ 2 ≠ (-3 : ℚ) + (0 : ℚ) * r)`
- **Type**: `Fact (∀ r : ℚ, r ^ 2 ≠ -3 + 0 * r)`
- **What**: −3 has no rational square root (needed by `QuadraticAlgebra ℚ (-3) 0`).
- **How**: `sq_nonneg` + `nlinarith`.
- **Uses from project**: []
- **Visibility**: public (instance)
- **Lines**: 233-237

### `abbrev QSqrtNegThreeQuadratic`
- **Type**: `Type := QuadraticAlgebra ℚ (-3 : ℚ) 0`
- **What**: ℚ[√-3] via the radical quadratic-algebra construction.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 240

### `abbrev sqrtNegThreeQuadraticRoot`
- **Type**: `QSqrtNegThreeQuadratic := QuadraticAlgebra.omega`
- **What**: Distinguished √-3 in the quadratic-algebra model.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 243

### `theorem sqrtNegThreeQuadraticRoot_sq`
- **Type**: `sqrtNegThreeQuadraticRoot ^ 2 = (-3 : QSqrtNegThreeQuadratic)`
- **How**: `QuadraticAlgebra.omega_mul_omega_eq_add` + simp.
- **Uses from project**: [sqrtNegThreeQuadraticRoot]
- **Visibility**: public
- **Lines**: 245-248

### `private def sqrtNegThreeQuadraticEquivAdjoinRoot`
- **Type**: `QSqrtNegThreeQuadratic ≃ₐ[ℚ] QSqrtNegThree`
- **What**: The quadratic-algebra model ≅ AdjoinRoot model.
- **How**: `QuadraticAlgebra.lift` and `AdjoinRoot.liftAlgHom`, glued by `AlgEquiv.ofAlgHom` with `algHom_ext` on both rings.
- **Uses from project**: [QSqrtNegThreeQuadratic, sqrtNegThreeRoot, sqrtNegThreeRoot_sq, sqrtNegThreePolynomial, sqrtNegThreeQuadraticRoot, sqrtNegThreeQuadraticRoot_sq]
- **Visibility**: private
- **Lines**: 250-285
- **Notes**: proof >30 lines.

### `private theorem sqrtNegThreeQuadraticEquivAdjoinRoot_root`
- **Type**: `sqrtNegThreeQuadraticEquivAdjoinRoot sqrtNegThreeQuadraticRoot = sqrtNegThreeRoot`
- **How**: unfold to omega.re/im • basis + simp.
- **Uses from project**: [sqrtNegThreeQuadraticEquivAdjoinRoot, sqrtNegThreeQuadraticRoot, sqrtNegThreeRoot]
- **Visibility**: private
- **Lines**: 287-292

### `def sqrtNegThreeQuadraticEquivCyclotomic`
- **Type**: `QSqrtNegThreeQuadratic ≃ₐ[ℚ] K`
- **What**: Quadratic-algebra model ≅ cyclotomic K.
- **How**: compose private equiv with `sqrtNegThreeEquivCyclotomic`.
- **Uses from project**: [sqrtNegThreeQuadraticEquivAdjoinRoot, sqrtNegThreeEquivCyclotomic]
- **Visibility**: public
- **Lines**: 295-297

### `theorem sqrtNegThreeQuadraticEquivCyclotomic_root`
- **Type**: `sqrtNegThreeQuadraticEquivCyclotomic sqrtNegThreeQuadraticRoot = 2 * ζ + 1`
- **How**: `AlgEquiv.trans_apply` + the two root lemmas.
- **Uses from project**: [sqrtNegThreeQuadraticEquivCyclotomic, sqrtNegThreeQuadraticRoot, ζ, sqrtNegThreeQuadraticEquivAdjoinRoot_root, sqrtNegThreeEquivCyclotomic_root]
- **Visibility**: public
- **Lines**: 299-302

### File Summary — Basic.lean
- Total decls: 33 (abbrevs 12, defs 5, theorems 12, instances 4).
- Key API (3+ uses): `zeta_isPrimitiveRoot`, `ζ`, `zetaThreePolynomial`, `adjoinRootEquivCyclotomic`, `sqrtNegThreeEquivCyclotomic`.
- Unused (no in-folder consumer): the entire `√-3` / `QuadraticAlgebra` identification chain (`sqrtNegThree*`, `QSqrtNegThree*`, the two private equivs) is demonstration-only; only `adjoinRootEquivCyclotomic`/`adjoinRootEquivCyclotomic_root` feed Embeddings.
- sorry: none. set_option: none. proofs >30 lines: `sqrtNegThreeQuadraticEquivAdjoinRoot` (≈36), `sqrtNegThreeEquivZetaThree` (≈29).

---

## Galois.lean

### `theorem isGalois`
- **Type**: `IsGalois ℚ K`
- **What**: ℚ(ζ₃)/ℚ is Galois.
- **How**: `IsCyclotomicExtension.isGalois`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 33-34
- **Notes**: used as `haveI` in Galois.

### `abbrev galEquivZMod`
- **Type**: `Gal(K / ℚ) ≃* (ZMod 3)ˣ`
- **What**: Identifies the Galois group with (ℤ/3)ˣ via cyclotomic character.
- **How**: `IsCyclotomicExtension.Rat.galEquivZMod`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 40-41

### `theorem galEquivZMod_apply_zeta`
- **Type**: `(σ : Gal(K/ℚ)) : σ ζ = ζ ^ (galEquivZMod σ).val.val`
- **What**: The character records the exponent on ζ.
- **How**: `galEquivZMod_apply_of_pow_eq` + `pow_eq_one`.
- **Uses from project**: [galEquivZMod, ζ, zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 44-46

### `theorem galoisGroupStructure`
- **Type**: `Nonempty (Gal(K/ℚ) ≃* Multiplicative (ZMod 2))`
- **What**: Gal ≅ ℤ/2, generated by complex conjugation.
- **How**: card = 2 via `IsGalois.card_aut_eq_finrank` + totient; then `mulEquivOfPrimeCardEq`.
- **Uses from project**: [isGalois]
- **Visibility**: public
- **Lines**: 50-59

### File Summary — Galois.lean
- Total decls: 4 (theorems 3, abbrev 1).
- Key API: `isGalois` (reused in Embeddings/PrimeSplitting via `IsCyclotomicExtension.isGalois` directly, plus here).
- Unused: `galEquivZMod_apply_zeta`, `galoisGroupStructure` are terminal results.
- sorry/set_option/long proofs: none.

---

## Embeddings.lean

### `theorem nrRealPlaces_eq_zero`
- **Type**: `InfinitePlace.nrRealPlaces K = 0`
- **How**: `IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 34-35

### `theorem isTotallyComplex`
- **Type**: `IsTotallyComplex K`
- **How**: `IsCyclotomicExtension.Rat.isTotallyComplex`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 37-38
- **Notes**: reused by Embeddings + CMField.

### `theorem nrComplexPlaces_eq_one`
- **Type**: `InfinitePlace.nrComplexPlaces K = 1`
- **How**: `nrComplexPlaces_eq_totient_div_two` + `Nat.totient_prime`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 40-42

### `theorem infinitePlace_card_eq_one`
- **Type**: `Fintype.card (InfinitePlace K) = 1`
- **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces` + the two place counts.
- **Uses from project**: [nrRealPlaces_eq_zero, nrComplexPlaces_eq_one]
- **Visibility**: public
- **Lines**: 56-59

### `theorem infinitePlace_isComplex`
- **Type**: `(v : InfinitePlace K) : InfinitePlace.IsComplex v`
- **How**: `isTotallyComplex.isComplex`.
- **Uses from project**: [isTotallyComplex]
- **Visibility**: public
- **Lines**: 61-63
- **Notes**: reused in LocalGlobal.

### `theorem exists_complexEmbedding_zeta`
- **Type**: `∃ σ : K →+* ℂ, σ ζ = Complex.exp (2 π I / 3)`
- **What**: There is a complex embedding sending ζ to the standard primitive root.
- **How**: `Complex.isPrimitiveRoot_exp`, `AdjoinRoot.liftAlgHom` through `adjoinRootEquivCyclotomic.symm`.
- **Uses from project**: [zetaThreePolynomial, ζ, adjoinRootEquivCyclotomic, adjoinRootEquivCyclotomic_root]
- **Visibility**: public
- **Lines**: 65-78

### File Summary — Embeddings.lean
- Total decls: 6 (theorems 6).
- Key API: `isTotallyComplex`, `infinitePlace_isComplex`, `nrRealPlaces_eq_zero`/`nrComplexPlaces_eq_one` (used by Units, LocalGlobal).
- Note: `attribute [-instance] DivisionRing.toRatAlgebra` set in first section.
- sorry/set_option/long proofs: none (`attribute` directive present).

---

## RingOfIntegers.lean

### `def zetaInt`
- **Type**: `𝓞 K := zeta_isPrimitiveRoot.toInteger`
- **What**: ζ as an algebraic integer in 𝓞 K.
- **Uses from project**: [zeta_isPrimitiveRoot]
- **Visibility**: public (noncomputable def)
- **Lines**: 33
- **Notes**: Workhorse used in 5+ files.

### `abbrev integralPowerBasis`
- **Type**: `PowerBasis ℤ (𝓞 K)`
- **What**: Integral power basis from the primitive root.
- **Uses from project**: [zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 39-40

### `theorem integralPowerBasis_gen`
- **Type**: `integralPowerBasis.gen = zeta_isPrimitiveRoot.toInteger`
- **How**: simp.
- **Uses from project**: [integralPowerBasis, zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 43-44

### `theorem integralPowerBasis_dim`
- **Type**: `integralPowerBasis.dim = 2`
- **How**: simp + `Nat.totient_prime`.
- **Uses from project**: [integralPowerBasis]
- **Visibility**: public
- **Lines**: 46-47

### `abbrev zetaExplicitIntegralBasis`
- **Type**: `Basis (Fin 2) ℤ (𝓞 K)`
- **What**: Explicit basis [1, ζ] of 𝓞 K.
- **How**: reindex of the power-basis basis via `finCongr integralPowerBasis_dim`.
- **Uses from project**: [integralPowerBasis, integralPowerBasis_dim]
- **Visibility**: public
- **Lines**: 50-51
- **Notes**: heavily reused (Discriminant, PrimeSplitting finrank facts).

### `theorem zetaExplicitIntegralBasis_zero`
- **Type**: `zetaExplicitIntegralBasis 0 = 1`
- **How**: `Basis.reindex_apply`, `basis_eq_pow`, `rfl` coercion.
- **Uses from project**: [zetaExplicitIntegralBasis, integralPowerBasis, integralPowerBasis_dim]
- **Visibility**: public
- **Lines**: 53-61

### `theorem zetaExplicitIntegralBasis_one`
- **Type**: `zetaExplicitIntegralBasis 1 = zeta_isPrimitiveRoot.toInteger`
- **How**: same as above with index 1.
- **Uses from project**: [zetaExplicitIntegralBasis, integralPowerBasis, integralPowerBasis_dim, zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 63-71

### `theorem cyclotomicRing_isIntegralClosure`
- **Type**: `IsIntegralClosure (CyclotomicRing 3 ℤ ℚ) ℤ K`
- **How**: `IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 74-75

### `theorem isIntegralClosure_adjoin_zeta`
- **Type**: `IsIntegralClosure (Algebra.adjoin ℤ {ζ}) ℤ K`
- **How**: `isIntegralClosure_adjoin_singleton`.
- **Uses from project**: [ζ, zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 82-84

### `theorem integralPowerBasis_adjoin_gen_eq_top`
- **Type**: `Algebra.adjoin ℤ {integralPowerBasis.gen} = ⊤`
- **How**: `PowerBasis.adjoin_gen_eq_top`.
- **Uses from project**: [integralPowerBasis]
- **Visibility**: public
- **Lines**: 90-92

### File Summary — RingOfIntegers.lean
- Total decls: 10 (defs 1, abbrevs 2, theorems 7).
- Key API: `zetaInt`, `zetaExplicitIntegralBasis`, `integralPowerBasis`(+ `_dim`).
- Unused (terminal): `cyclotomicRing_isIntegralClosure`, `isIntegralClosure_adjoin_zeta`, `integralPowerBasis_adjoin_gen_eq_top`, basis-component lemmas.
- sorry/set_option/long proofs: none.

---

## Discriminant.lean

### `theorem numberField_discr_eq`
- **Type**: `NumberField.discr K = -3`
- **What**: The field discriminant is −3 (smallest |disc| quadratic field).
- **How**: `IsCyclotomicExtension.Rat.discr_prime` + norm_num.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 35-37
- **Notes**: used in PrimeSplitting (different ideal) — key API.

### `theorem zetaExplicitIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ zetaExplicitIntegralBasis = (-3 : ℤ)`
- **How**: `NumberField.discr_eq_discr` then `discr_prime`.
- **Uses from project**: [zetaExplicitIntegralBasis]
- **Visibility**: public
- **Lines**: 39-46

### `theorem integralBasis_discr`
- **Type**: `Algebra.discr ℚ (NumberField.integralBasis K) = (-3 : ℚ)`
- **How**: `NumberField.coe_discr` + `discr_prime`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 53-58
- **Notes**: used by the two `example`s below.

### `example` (change-of-basis discriminant scaling)
- **Type**: `Algebra.discr ℚ (Matrix.mulVec (P.map …) (integralBasis K)) = P.det^2 * Algebra.discr ℚ (integralBasis K)`
- **How**: `Algebra.discr_of_matrix_mulVec`.
- **Uses from project**: []
- **Visibility**: example (anonymous)
- **Lines**: 66-70

### `example` (unimodular change preserves −3)
- **Type**: under `P.det = ±1`, discriminant = −3.
- **How**: previous formula + `integralBasis_discr` + simp.
- **Uses from project**: [integralBasis_discr]
- **Visibility**: example
- **Lines**: 73-83

### File Summary — Discriminant.lean
- Total decls: 5 (theorems 3, examples 2).
- Key API: `numberField_discr_eq` (used in PrimeSplitting `ramified_iff_eq_three` and different-ideal).
- Unused: `zetaExplicitIntegralBasis_discr`, the two examples (illustrative).
- sorry/set_option/long proofs: none.

---

## PrimeSplitting.lean

Section `PrivateMachinery` (lines 34-217) — generic ℤ[ζ]→ZMod p reduction machinery, mirrors CubeRootThree.

### `private theorem zeta_pow_three`
- **Type**: `ζ ^ 3 = 1`
- **How**: `pow_eq_one`.
- **Uses from project**: [ζ, zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 36-37
- **Notes**: duplicated as private in Units.lean too.

### `private theorem gen_eq_zetaInt`
- **Type**: `zeta_isPrimitiveRoot.integralPowerBasis.gen = zetaInt`
- **How**: `integralPowerBasis_gen` + rfl.
- **Uses from project**: [zeta_isPrimitiveRoot, zetaInt]
- **Visibility**: private
- **Lines**: 39-41

### `private theorem zetaInt_pow_three`
- **Type**: `zetaInt ^ 3 = 1`
- **How**: `toInteger_cube_eq_one`.
- **Uses from project**: [zetaInt, zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 43-44

### `private theorem zetaInt_relation`
- **Type**: `zetaInt ^ 2 + zetaInt + 1 = 0`
- **How**: `ext` + `isRoot_cyclotomic`.
- **Uses from project**: [zetaInt, zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 46-48

### `private def sig2`
- **Type**: `K ≃ₐ[ℚ] K`
- **What**: The nontrivial automorphism ζ ↦ ζ² (complex conjugation).
- **How**: `IsCyclotomicExtension.fromZetaAut` (pow_of_coprime 2).
- **Uses from project**: [zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 50-52

### `private theorem sig2_zeta`
- **Type**: `sig2 ζ = ζ ^ 2`
- **How**: `fromZetaAut_spec`.
- **Uses from project**: [sig2, ζ, zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 54-56

### `private theorem autEq'`
- **Type**: `(σ : K ≃ₐ[ℚ] K) : σ = 1 ∨ σ = sig2`
- **What**: Only two automorphisms.
- **How**: `autToPow_spec`, `powerBasis.algHom_ext`, casework on (ZMod 3)ˣ via decide.
- **Uses from project**: [sig2, ζ, zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 58-70

### `private theorem prod_aut_apply`
- **Type**: `∏ σ, σ x = x * sig2 x`
- **How**: enumerate univ = {1, sig2} via `autEq'`, `Finset.prod_pair`.
- **Uses from project**: [sig2, autEq', ζ, zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 72-84

### `private theorem intNorm_eq`
- **Type**: from `x·σx = n` conclude `Algebra.norm ℤ x = n`
- **How**: `norm_eq_prod_automorphisms`, `prod_aut_apply`, `Algebra.coe_norm_int`.
- **Uses from project**: [sig2, prod_aut_apply]
- **Visibility**: private
- **Lines**: 86-100
- **Notes**: appears unused in file (norm forms computed via `norm_eq_normForm`).

### `private theorem minpoly_gen_eq`
- **Type**: `minpoly ℤ integralPowerBasis.gen = X² + X + C 1`
- **How**: `isIntegrallyClosed_dvd`, degree comparison, `eq_one_of_monic_natDegree_zero`.
- **Uses from project**: [gen_eq_zetaInt, zetaInt_relation, zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 102-130
- **Notes**: proof ~28 lines.

### `private def residueHom`
- **Type**: `(p r, hr) → 𝓞 K →ₐ[ℤ] ZMod p` (with `r²+r+1=0` mod p)
- **What**: Reduction homomorphism sending ζ ↦ r.
- **How**: `integralPowerBasis.lift` using `minpoly_gen_eq`.
- **Uses from project**: [zeta_isPrimitiveRoot, minpoly_gen_eq]
- **Visibility**: private
- **Lines**: 132-139
- **Notes**: STRUCTURAL TWIN of CubeRootThree.residueHom (cube vs quadratic relation).

### `private theorem residueHom_zetaInt`
- **Type**: `residueHom p r hr zetaInt = (r : ZMod p)`
- **How**: `lift_gen`.
- **Uses from project**: [residueHom, gen_eq_zetaInt, zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 141-145

### `private theorem ker_residueHom`
- **Type**: `RingHom.ker (residueHom …) = Ideal.span {p, ζ − r}`
- **What**: Kernel of reduction is the prime pair ideal.
- **How**: `le_antisymm`; `sub_dvd_eval_sub`, `Ideal.mem_span_singleton`, `intCast_zmod_eq_zero_iff_dvd`.
- **Uses from project**: [residueHom, residueHom_zetaInt, gen_eq_zetaInt, zetaInt, zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 147-195
- **Notes**: proof >30 lines. STRUCTURAL TWIN of CubeRootThree.ker_residueHom.

### `private theorem residueHom_surjective`
- **Type**: `Function.Surjective (residueHom …)`
- **How**: `ZMod.intCast_surjective`.
- **Uses from project**: [residueHom]
- **Visibility**: private
- **Lines**: 197-202

### `private theorem isMaximal_span_pair`
- **Type**: `(Ideal.span {p, ζ − r}).IsMaximal`
- **How**: `ker_residueHom` + `RingHom.ker_isMaximal_of_surjective`.
- **Uses from project**: [ker_residueHom, residueHom_surjective]
- **Visibility**: private
- **Lines**: 204-208

### `private theorem absNorm_span_pair`
- **Type**: `Ideal.absNorm (Ideal.span {p, ζ − r}) = p`
- **How**: `ker_residueHom`, `cardQuot_apply`, `Nat.card_zmod`.
- **Uses from project**: [ker_residueHom, residueHom_surjective]
- **Visibility**: private
- **Lines**: 210-216
- **Notes**: TWIN of CubeRootThree.absNorm_span_pair.

### `theorem norm_eq_normForm`
- **Type**: `(x y : ℚ) : Algebra.norm ℚ (x • 1 + y • ζ) = x² − xy + y²`
- **What**: The norm form (principal binary quadratic form of disc −3).
- **How**: `norm_eq_prod_automorphisms`, `prod_aut_apply`, `sig2_zeta`, `linear_combination` with zeta relation.
- **Uses from project**: [ζ, prod_aut_apply, sig2_zeta, zeta_isPrimitiveRoot, zeta_pow_three]
- **Visibility**: public
- **Lines**: 221-229
- **Notes**: key API (Euclidean, intNorm).

### `theorem intNorm_eq_normForm`
- **Type**: `(x y : ℤ) : Algebra.norm ℤ (x • 1 + y • zetaInt) = x² − xy + y²`
- **How**: `Algebra.coe_norm_int`, push to K, `norm_eq_normForm`.
- **Uses from project**: [zetaInt, norm_eq_normForm]
- **Visibility**: public
- **Lines**: 233-243
- **Notes**: key API.

### `theorem isUnit_iff_normForm`
- **Type**: `(x y : ℤ) : IsUnit (x • 1 + y • zetaInt) ↔ x² − xy + y² = 1`
- **What**: Unit equation for ℤ[ζ].
- **How**: `NumberField.isUnit_iff_norm`, `intNorm_eq_normForm`, `abs_eq`, nonnegativity via nlinarith.
- **Uses from project**: [zetaInt, intNorm_eq_normForm]
- **Visibility**: public
- **Lines**: 247-260

### `theorem norm_one_sub_zeta`
- **Type**: `Algebra.norm ℚ (1 - ζ) = 3`
- **How**: `norm_eq_normForm (1, -1)`.
- **Uses from project**: [ζ, norm_eq_normForm]
- **Visibility**: public
- **Lines**: 262-266

### `theorem norm_one_add_zeta`
- **Type**: `Algebra.norm ℚ (1 + ζ) = 1`
- **How**: `norm_eq_normForm (1, 1)`.
- **Uses from project**: [ζ, norm_eq_normForm]
- **Visibility**: public
- **Lines**: 268-272

### `theorem zetaInt_sub_one_prime`
- **Type**: `Prime (zetaInt - 1 : 𝓞 K)`
- **How**: `zeta_sub_one_prime'`.
- **Uses from project**: [zetaInt, zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 273-276

### `theorem zetaInt_sub_one_dvd_three`
- **Type**: `(zetaInt - 1) ∣ (3 : 𝓞 K)`
- **How**: `toInteger_sub_one_dvd_prime'`.
- **Uses from project**: [zetaInt, zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 278-281

### `theorem span_three_eq`
- **Type**: `Ideal.span {3} = Ideal.span {zetaInt - 1} ^ 2`
- **What**: 3 totally ramifies: (3)=(ζ−1)².
- **How**: `span_singleton_pow`, `span_singleton_eq_span_singleton`, `linear_combination` with zeta relation.
- **Uses from project**: [zetaInt, zetaInt_pow_three, zetaInt_relation]
- **Visibility**: public
- **Lines**: 285-292
- **Notes**: key API (used 6+ times).

### `private theorem span_zetaInt_sub_one_eq_pair`
- **Type**: `Ideal.span {zetaInt - 1} = Ideal.span {(3:ℕ), ζ − 1}`
- **How**: `le_antisymm`, `mem_span_pair`, `span_three_eq`, `pow_le_self`.
- **Uses from project**: [zetaInt, span_three_eq]
- **Visibility**: private
- **Lines**: 294-304

### `theorem absNorm_span_zetaInt_sub_one`
- **Type**: `Ideal.absNorm (Ideal.span {zetaInt - 1}) = 3`
- **How**: rewrite to pair, `absNorm_span_pair 3 1`.
- **Uses from project**: [zetaInt, span_zetaInt_sub_one_eq_pair, absNorm_span_pair]
- **Visibility**: public
- **Lines**: 306-311

### `theorem isPrime_span_zetaInt_sub_one`
- **Type**: `(Ideal.span {zetaInt - 1}).IsPrime`
- **How**: pair rewrite + `isMaximal_span_pair`.
- **Uses from project**: [zetaInt, span_zetaInt_sub_one_eq_pair, isMaximal_span_pair]
- **Visibility**: public
- **Lines**: 313-318
- **Notes**: used in LocalGlobal + different ideal.

### `theorem liesOver_span_zetaInt_sub_one`
- **Type**: `(Ideal.span {zetaInt - 1}).LiesOver (Ideal.span {(3:ℤ)})`
- **How**: `liesOver_span_iff`, `span_three_eq`, `pow_le_self`.
- **Uses from project**: [zetaInt, isPrime_span_zetaInt_sub_one, span_three_eq]
- **Visibility**: public
- **Lines**: 321-328

### `theorem inertiaDeg_span_zetaInt_sub_one`
- **Type**: `(Ideal.span {(3:ℤ)}).inertiaDeg (Ideal.span {zetaInt-1}) = 1`
- **How**: `absNorm_eq_pow_inertiaDeg'` + `absNorm_span_zetaInt_sub_one`.
- **Uses from project**: [zetaInt, liesOver_span_zetaInt_sub_one, absNorm_span_zetaInt_sub_one]
- **Visibility**: public
- **Lines**: 330-338

### `theorem ramificationIdx_span_zetaInt_sub_one`
- **Type**: `(Ideal.span {(3:ℤ)}).ramificationIdx (Ideal.span {zetaInt-1}) = 2`
- **How**: `ramificationIdx_spec`; `span_three_eq` for ≤, norm-3-vs-9 contradiction for the strict bound.
- **Uses from project**: [zetaInt, span_three_eq, absNorm_span_zetaInt_sub_one, zetaExplicitIntegralBasis]
- **Visibility**: public
- **Lines**: 341-363
- **Notes**: proof ~23 lines.

### `theorem absNorm_span_two`
- **Type**: `Ideal.absNorm (Ideal.span {(2:𝓞 K)}) = 4`
- **How**: `absNorm_span_singleton`, `norm_algebraMap`, finrank 2.
- **Uses from project**: [zetaExplicitIntegralBasis]
- **Visibility**: public
- **Lines**: 366-372

### `private theorem quotient_zeta_ne_one_of_two_mem`
- **Type**: in maximal `M` containing 2, `Quotient.mk M zetaInt ≠ 1`
- **How**: from zeta relation mod M and 2≡0, derive 1=0.
- **Uses from project**: [zetaInt, zetaInt_relation]
- **Visibility**: private
- **Lines**: 374-386

### `private theorem absNorm_maximal_over_span_two_eq_four`
- **Type**: maximal `M ⊇ (2)` ⇒ `absNorm M = 4`
- **What**: 2 is inert: order of ζ mod M is 3, so residue field is 𝔽₄.
- **How**: `FiniteField.pow_card`, `orderOf_eq_prime`, `3 ∣ 2^k−1` interval_cases.
- **Uses from project**: [zetaInt, zetaInt_pow_three, quotient_zeta_ne_one_of_two_mem]
- **Visibility**: private
- **Lines**: 388-434
- **Notes**: proof >30 lines.

### `theorem isPrime_span_two`
- **Type**: `(Ideal.span {(2:𝓞 K)}).IsPrime`
- **What**: 2 is inert.
- **How**: maximal extension + `absNorm_maximal_over_span_two_eq_four` + `eq_of_le_of_absNorm_eq` (Common).
- **Uses from project**: [absNorm_span_two, absNorm_maximal_over_span_two_eq_four, Common.eq_of_le_of_absNorm_eq]
- **Visibility**: public
- **Lines**: 437-447

### `theorem liesOver_span_two`
- **Type**: `(Ideal.span {(2:𝓞 K)}).LiesOver (Ideal.span {(2:ℤ)})`
- **Uses from project**: [isPrime_span_two]
- **Visibility**: public
- **Lines**: 449-454

### `theorem inertiaDeg_span_two`
- **Type**: `inertiaDeg = 2`
- **How**: `absNorm_eq_pow_inertiaDeg'`, `absNorm_span_two`, `pow_right_injective`.
- **Uses from project**: [liesOver_span_two, absNorm_span_two]
- **Visibility**: public
- **Lines**: 456-464

### `private theorem seven_eq_mul`
- **Type**: `(7 : 𝓞 K) = (3 + zetaInt)(3 + zetaInt²)`
- **How**: `linear_combination` with zeta relations.
- **Uses from project**: [zetaInt, zetaInt_pow_three, zetaInt_relation]
- **Visibility**: private
- **Lines**: 466-467

### `theorem span_seven_eq`
- **Type**: `Ideal.span {7} = Ideal.span {3+ζ} * Ideal.span {3+ζ²}`
- **What**: 7 splits.
- **Uses from project**: [zetaInt, seven_eq_mul]
- **Visibility**: public
- **Lines**: 471-473

### `theorem absNorm_span_seven_factor`
- **Type**: `Ideal.absNorm (Ideal.span {3+zetaInt}) = 7`
- **How**: `intNorm_eq_normForm 3 1` + `absNorm_span_singleton`.
- **Uses from project**: [zetaInt, intNorm_eq_normForm]
- **Visibility**: public
- **Lines**: 475-480

### `theorem isPrime_span_seven_factor`
- **Type**: `(Ideal.span {3+zetaInt}).IsPrime`
- **How**: `isPrime_of_irreducible_absNorm` + norm 7 prime.
- **Uses from project**: [zetaInt, absNorm_span_seven_factor]
- **Visibility**: public
- **Lines**: 482-486

### `theorem liesOver_span_seven_factor`
- **Type**: `LiesOver (Ideal.span {(7:ℤ)})`
- **Uses from project**: [zetaInt, isPrime_span_seven_factor, seven_eq_mul]
- **Visibility**: public
- **Lines**: 488-496

### `theorem inertiaDeg_span_seven_factor`
- **Type**: `inertiaDeg = 1`
- **Uses from project**: [zetaInt, liesOver_span_seven_factor, absNorm_span_seven_factor]
- **Visibility**: public
- **Lines**: 498-506

### `theorem ramified_iff_eq_three`
- **Type**: `(p prime) : (∃ P prime, span{p} ≤ P²) ↔ p = 3`
- **What**: A prime ramifies iff p=3 (divides disc).
- **How**: norm/different-ideal argument: `not_isUnramifiedAt_…` (Common), `dvd_differentIdeal_iff`, `absNorm_differentIdeal`, `numberField_discr_eq`.
- **Uses from project**: [zetaExplicitIntegralBasis, numberField_discr_eq, isPrime_span_zetaInt_sub_one, span_three_eq, Common.not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow, Common.not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ]
- **Visibility**: public
- **Lines**: 510-555
- **Notes**: proof >30 lines. Key API (used by ramificationIdx + splits lemmas).

### `theorem ramificationIdx_span_two`
- **Type**: `ramificationIdx = 1` (2 unramified)
- **How**: `ramificationIdx_spec` + `ramified_iff_eq_three 2`.
- **Uses from project**: [isPrime_span_two, ramified_iff_eq_three]
- **Visibility**: public
- **Lines**: 558-569

### `theorem ramificationIdx_span_seven_factor`
- **Type**: `ramificationIdx = 1`
- **How**: `ramificationIdx_spec`, `span_seven_eq`, `ramified_iff_eq_three 7`.
- **Uses from project**: [zetaInt, span_seven_eq, isPrime_span_seven_factor, ramified_iff_eq_three]
- **Visibility**: public
- **Lines**: 572-585

### `private theorem absNorm_span_natCast`
- **Type**: `Ideal.absNorm (Ideal.span {(p:𝓞 K)}) = p²`
- **Uses from project**: [zetaExplicitIntegralBasis]
- **Visibility**: private
- **Lines**: 587-595
- **Notes**: generic; could be derived from finrank — candidate to share.

### `private theorem one_mod_three_of_prime_norm`
- **Type**: `(p≠3): (∃ P norm p) → p % 3 = 1`
- **How**: residue field 𝔽_p has a primitive cube root, so 3 ∣ p−1.
- **Uses from project**: [zetaInt, zetaInt_pow_three, zetaInt_relation]
- **Visibility**: private
- **Lines**: 597-644
- **Notes**: proof >30 lines.

### `private theorem exists_prime_norm_of_one_mod_three`
- **Type**: `p % 3 = 1 → ∃ P prime, span{p}≤P, norm P = p`
- **How**: cyclic generator of (ZMod p)ˣ gives order-3 element r; build pair ideal via `isMaximal_span_pair`/`absNorm_span_pair`.
- **Uses from project**: [zetaInt, isMaximal_span_pair, absNorm_span_pair]
- **Visibility**: private
- **Lines**: 646-691
- **Notes**: proof >30 lines.

### `private theorem exists_prime_norm_iff_one_mod_three`
- **Type**: iff version of the previous two.
- **Uses from project**: [one_mod_three_of_prime_norm, exists_prime_norm_of_one_mod_three]
- **Visibility**: private
- **Lines**: 693-698

### `private theorem one_mod_three_of_splits`
- **Type**: split into 2 distinct primes ⇒ p % 3 = 1
- **How**: norm multiplicativity, `left_eq_prime_of_mul_eq_prime_sq_of_ne_one` (Common), iff lemma.
- **Uses from project**: [absNorm_span_natCast, exists_prime_norm_iff_one_mod_three, Common.left_eq_prime_of_mul_eq_prime_sq_of_ne_one]
- **Visibility**: private
- **Lines**: 700-720

### `private theorem splits_of_one_mod_three`
- **Type**: p % 3 = 1 ⇒ splits into 2 distinct primes
- **How**: from prime of norm p, factor span{p}=P·Q; distinctness via `ramified_iff_eq_three`.
- **Uses from project**: [absNorm_span_natCast, exists_prime_norm_iff_one_mod_three, ramified_iff_eq_three]
- **Visibility**: private
- **Lines**: 722-747

### `theorem splits_iff_one_mod_three`
- **Type**: `(p≠3): splits ↔ p % 3 = 1`
- **What**: Quadratic/cyclotomic splitting law for ℚ(ζ₃).
- **How**: combine the two private directions.
- **Uses from project**: [one_mod_three_of_splits, splits_of_one_mod_three]
- **Visibility**: public
- **Lines**: 752-757
- **Notes**: headline result of file.

### Kummer-Dedekind section (lines 761-831)

### `abbrev zetaThreePolynomialMod`
- **Type**: `(p : ℕ) : (ZMod p)[X] := X² + X + C 1`
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 775-776

### `private theorem not_dvd_three_of_prime_ne_three`
- **Type**: `(p prime, p≠3): ¬ p ∣ 3`
- **Uses from project**: []
- **Visibility**: private
- **Lines**: 778-784

### `private theorem zetaThreePolynomialMod_eq_cyclotomic`
- **Type**: `zetaThreePolynomialMod p = cyclotomic 3 (ZMod p)`
- **Uses from project**: [zetaThreePolynomialMod]
- **Visibility**: private
- **Lines**: 786-789

### `private theorem orderOf_unitOfCoprime_eq_two_of_mod_three_eq_two`
- **Type**: `p % 3 = 2 ⇒ orderOf (unitOfCoprime p) = 2`
- **How**: `orderOf_eq_prime`, ZMod cast manipulation.
- **Uses from project**: [not_dvd_three_of_prime_ne_three]
- **Visibility**: private
- **Lines**: 791-814

### `private theorem orderOf_unitOfCoprime_eq_one_of_mod_three_eq_one`
- **Type**: `p % 3 = 1 ⇒ orderOf (unitOfCoprime p) = 1`
- **Uses from project**: [not_dvd_three_of_prime_ne_three]
- **Visibility**: private
- **Lines**: 816-829
- **Notes**: These four Kummer-Dedekind helpers appear UNUSED (no consumer in folder) — dead section.

### Different section (lines 833-915)

### `private theorem span_zetaInt_sub_one_dvd_differentIdeal`
- **Type**: `Ideal.span {zetaInt - 1} ∣ differentIdeal ℤ (𝓞 K)`
- **How**: `dvd_differentIdeal_iff` + Common ramification lemmas; (3)=(ζ−1)² and norm computations.
- **Uses from project**: [zetaInt, isPrime_span_zetaInt_sub_one, span_three_eq, zetaInt_sub_one_prime, zetaExplicitIntegralBasis, absNorm_span_zetaInt_sub_one, Common.not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow, Common.not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ]
- **Visibility**: private
- **Lines**: 845-880
- **Notes**: proof >30 lines.

### `theorem absNorm_differentIdeal_eq_three`
- **Type**: `Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = 3`
- **How**: `NumberField.absNorm_differentIdeal` + `numberField_discr_eq`.
- **Uses from project**: [numberField_discr_eq]
- **Visibility**: public
- **Lines**: 882-885

### `theorem prime_dvd_differentIdeal_iff_eq_span_zeta_sub_one`
- **Type**: `(P prime ≠ ⊥): P ∣ different ↔ P = Ideal.span {zetaInt - 1}`
- **What**: The unique prime dividing the different is the ramified prime over 3.
- **How**: norm divides 3 ⇒ norm = 3 ⇒ lies over 3; `eq_span_zeta_sub_one_of_liesOver'`.
- **Uses from project**: [zetaInt, absNorm_differentIdeal_eq_three, zeta_isPrimitiveRoot, span_zetaInt_sub_one_dvd_differentIdeal]
- **Visibility**: public
- **Lines**: 887-913
- **Notes**: proof >30 lines.

### File Summary — PrimeSplitting.lean
- Total decls: 47 (theorems ~42, defs 2: `sig2`, `residueHom`, abbrev 1: `zetaThreePolynomialMod`; ~24 private).
- Key API (3+): `zeta_pow_three`, `zetaInt_pow_three`, `zetaInt_relation`, `prod_aut_apply`, `sig2_zeta`, `norm_eq_normForm`, `intNorm_eq_normForm`, `span_three_eq`, `absNorm_span_zetaInt_sub_one`, `isPrime_span_zetaInt_sub_one`, `ramified_iff_eq_three`, `isMaximal_span_pair`/`absNorm_span_pair`, `numberField_discr_eq`.
- Public headline results: `splits_iff_one_mod_three`, `ramified_iff_eq_three`, `prime_dvd_differentIdeal_iff_eq_span_zeta_sub_one`, all the splitting/inertia/ramification per-prime facts (2 inert, 3 ramified, 7 split).
- Unused: `intNorm_eq` (private, never used), the four Kummer-Dedekind helpers (lines 786-829).
- sorry: none. set_option: none.
- proofs >30 lines: `ker_residueHom`, `absNorm_maximal_over_span_two_eq_four`, `ramified_iff_eq_three`, `one_mod_three_of_prime_norm`, `exists_prime_norm_of_one_mod_three`, `span_zetaInt_sub_one_dvd_differentIdeal`, `prime_dvd_differentIdeal_iff_eq_span_zeta_sub_one`.

---

## ClassGroup.lean

### `abbrev zetaFractionalIdeal`
- **Type**: `FractionalIdeal (𝓞 K)⁰ K := spanSingleton _ ζ`
- **Uses from project**: [ζ]
- **Visibility**: public
- **Lines**: 31-32

### `abbrev ramifiedPrimeFractionalIdeal`
- **Type**: `FractionalIdeal (𝓞 K)⁰ K := (Ideal.span {zetaInt - 1} : …)`
- **Uses from project**: [zetaInt]
- **Visibility**: public
- **Lines**: 34-35

### `theorem zeta_mem_fractionalIdeal`
- **Type**: `ζ ∈ zetaFractionalIdeal`
- **How**: `FractionalIdeal.mem_spanSingleton_self`.
- **Uses from project**: [zetaFractionalIdeal, ζ]
- **Visibility**: public
- **Lines**: 37-39

### `theorem zetaFractionalIdeal_absNorm`
- **Type**: `FractionalIdeal.absNorm zetaFractionalIdeal = |Algebra.norm ℚ ζ|`
- **How**: `absNorm_span_singleton`.
- **Uses from project**: [zetaFractionalIdeal, ζ]
- **Visibility**: public
- **Lines**: 41-43

### `theorem ramifiedPrimeFractionalIdeal_ne_zero`
- **Type**: `ramifiedPrimeFractionalIdeal ≠ 0`
- **How**: `coeIdeal_ne_zero` + `span_zeta_sub_one_ne_bot`.
- **Uses from project**: [ramifiedPrimeFractionalIdeal, ζ, zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 45-53

### `theorem isPrincipalIdealRing`
- **Type**: `IsPrincipalIdealRing (𝓞 K)`
- **What**: 𝓞 K is a PID (class number one).
- **How**: `IsCyclotomicExtension.Rat.three_pid`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 72-73
- **Notes**: feeds UFM + Euclidean.

### `theorem uniqueFactorizationMonoid`
- **Type**: `UniqueFactorizationMonoid (𝓞 K)`
- **How**: PID ⇒ UFM (`infer_instance`).
- **Uses from project**: [isPrincipalIdealRing]
- **Visibility**: public
- **Lines**: 75-78

### `theorem classNumber_eq_one`
- **Type**: `NumberField.classNumber K = 1`
- **How**: `classNumber_eq_one_iff` + `three_pid`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 80-82
- **Notes**: used by classGroupStructure/representative.

### `theorem classGroupStructure`
- **Type**: `Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1))`
- **How**: card 1 ⇒ subsingleton ⇒ `MulEquiv.ofUnique`.
- **Uses from project**: [classNumber_eq_one]
- **Visibility**: public
- **Lines**: 85-90

### `abbrev unitIdealRepresentative`
- **Type**: `(Ideal (𝓞 K))⁰ := ⟨⊤, _⟩`
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 93

### `theorem classGroupRepresentative`
- **Type**: `(C : ClassGroup (𝓞 K)) : C = ClassGroup.mk0 unitIdealRepresentative`
- **How**: subsingleton.
- **Uses from project**: [classNumber_eq_one, unitIdealRepresentative]
- **Visibility**: public
- **Lines**: 96-101

### File Summary — ClassGroup.lean
- Total decls: 11 (abbrevs 3, theorems 8).
- Key API: `isPrincipalIdealRing`, `classNumber_eq_one`.
- Unused (terminal/illustrative): fractional ideal block, `classGroupStructure`, `classGroupRepresentative`.
- sorry/set_option/long proofs: none.

---

## Units.lean

### `private theorem zeta_pow_three`
- **Type**: `ζ ^ 3 = 1`
- **Uses from project**: [ζ, zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 34-35
- **Notes**: DUPLICATE of the private `zeta_pow_three` in PrimeSplitting.

### `abbrev etaUnit`
- **Type**: `(𝓞 K)ˣ`
- **What**: The unit corresponding to ζ.
- **How**: `toInteger_isPrimitiveRoot.isUnit`.
- **Uses from project**: [zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 38-39
- **Notes**: used in LocalGlobal.

### `theorem unit_mem_unitsList`
- **Type**: `(u : (𝓞 K)ˣ) : u ∈ [1,-1,η,-η,η²,-η²]`
- **How**: `IsCyclotomicExtension.Rat.Three.Units.mem`.
- **Uses from project**: [etaUnit, zeta_isPrimitiveRoot]
- **Visibility**: public
- **Lines**: 45-47

### `theorem unit_eq_one_or_neg_one_or_eta`
- **Type**: case split of the six units.
- **Uses from project**: [unit_mem_unitsList, etaUnit]
- **Visibility**: public
- **Lines**: 50-53

### `theorem torsionOrder_eq_six`
- **Type**: `Units.torsionOrder K = 6`
- **How**: `IsCyclotomicExtension.Rat.torsionOrder_eq` + norm_num.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 56-58
- **Notes**: used by unitGroupStructure.

### `theorem unitRank_eq_zero`
- **Type**: `Units.rank K = 0`
- **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces` + totient.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 62-67

### `theorem unitGroupStructure`
- **Type**: `Nonempty ((𝓞 K)ˣ ≃* Multiplicative (ZMod 6))`
- **What**: Unit group ≅ μ₆.
- **How**: every unit torsion (fin_cases on the six), `IsCyclic`, card 6, `mulEquivOfCyclicCardEq`.
- **Uses from project**: [unit_mem_unitsList, zeta_pow_three, torsionOrder_eq_six]
- **Visibility**: public
- **Lines**: 71-111
- **Notes**: proof >30 lines.

### `theorem regulator_eq_one`
- **Type**: `Units.regulator K = 1`
- **How**: `regulator_eq_det'`, rank 0 ⇒ `Matrix.det_eq_one_of_card_eq_zero`.
- **Uses from project**: [unitRank_eq_zero]
- **Visibility**: public
- **Lines**: 115-127
- **Notes**: NOT blocked here (rank 0) — contrast with sibling fields where regulator is sorried.

### File Summary — Units.lean
- Total decls: 8 (abbrev 1, theorems 7; 1 private).
- Key API: `etaUnit`, `unit_mem_unitsList`, `torsionOrder_eq_six`, `unitRank_eq_zero`.
- Public headline: `unitGroupStructure`, `regulator_eq_one`, `torsionOrder_eq_six`.
- The trailing `Regulator` section (lines 131-141) is empty.
- sorry: none. set_option: none. proofs >30 lines: `unitGroupStructure`.

---

## Euclidean.lean

### `private theorem abs_norm_int_lt_of_remainder_eq`
- **Type**: from remainder formula + |form| ≤ 3/4 conclude `|N(r)| < |N(b)|`.
- **How**: `Algebra.coe_norm_int`, `norm_eq_normForm`, `abs_mul`, `mul_le_mul_of_nonneg_left`, linarith.
- **Uses from project**: [ζ, norm_eq_normForm]
- **Visibility**: private
- **Lines**: 33-53

### `private theorem exists_coords`
- **Type**: `(x : K) : ∃ a b : ℚ, x = a • 1 + b • ζ`
- **How**: power basis `exists_eq_aeval`, `eq_X_add_C_of_natDegree_le_one`.
- **Uses from project**: [zeta_isPrimitiveRoot, ζ, zetaThreePolynomial, zetaThreePolynomial_eq_minpoly]
- **Visibility**: private
- **Lines**: 55-70

### `theorem normEuclidean`
- **Type**: `(a b, b≠0): ∃ q r, a = b*q + r ∧ |N r|.natAbs < |N b|.natAbs`
- **What**: ℤ[ζ₃] (Eisenstein integers) is norm-Euclidean.
- **How**: nearest-integer rounding of coords; bound the form by 3/4 via `abs_sub_round` + nlinarith; `abs_norm_int_lt_of_remainder_eq`, `natAbs_lt_of_abs_ratCast_lt` (Common).
- **Uses from project**: [zetaInt, ζ, exists_coords, abs_norm_int_lt_of_remainder_eq, norm_eq_normForm, Common.natAbs_lt_of_abs_ratCast_lt]
- **Visibility**: public
- **Lines**: 75-112
- **Notes**: proof >30 lines. Headline result; here it IS proven (no sorry), unlike some siblings.

### File Summary — Euclidean.lean
- Total decls: 3 (theorems 3; 2 private).
- Key API: `normEuclidean` (terminal).
- sorry: none. set_option: none. proofs >30 lines: `normEuclidean`.

---

## LocalGlobal.lean

### `def heightOneThree`
- **Type**: `HeightOneSpectrum (𝓞 K)`
- **What**: The finite place over 3 = ramified prime (ζ−1).
- **How**: record with `isPrime_span_zetaInt_sub_one`, ne_bot via norm 3.
- **Uses from project**: [zetaInt, isPrime_span_zetaInt_sub_one, absNorm_span_zetaInt_sub_one]
- **Visibility**: public
- **Lines**: 35-42

### `abbrev vThree`
- **Type**: `FinitePlace K := FinitePlace.mk heightOneThree`
- **Uses from project**: [heightOneThree]
- **Visibility**: public
- **Lines**: 44-45

### `example` (ramificationIdx of heightOneThree = 2)
- **Uses from project**: [heightOneThree, ramificationIdx_span_zetaInt_sub_one]
- **Visibility**: example
- **Lines**: 47-49

### `example` (inertiaDeg of heightOneThree = 1)
- **Uses from project**: [heightOneThree, inertiaDeg_span_zetaInt_sub_one]
- **Visibility**: example
- **Lines**: 51-53

### `abbrev CompletionAtThree`
- **Type**: `Type := heightOneThree.adicCompletion K`
- **Uses from project**: [heightOneThree]
- **Visibility**: public
- **Lines**: 68-70

### `abbrev InfiniteCompletion`
- **Type**: `(v : InfinitePlace K) : Type := v.Completion`
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 83-84

### `private theorem complexEmbedding_norm_zeta_eq_one`
- **Type**: `(φ : K →+* ℂ) : ‖φ ζ‖ = 1`
- **How**: `Complex.norm_eq_one_of_pow_eq_one`.
- **Uses from project**: [ζ, zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 86-88
- **Notes**: reused by house_zeta + infiniteCompletion_zeta_norm.

### `example` (InfiniteCompletion v ≃+* ℂ)
- **Uses from project**: [InfiniteCompletion, infinitePlace_isComplex]
- **Visibility**: example
- **Lines**: 90-93

### `theorem infiniteCompletion_zeta_norm`
- **Type**: `‖algebraMap K (InfiniteCompletion v) ζ‖ = 1`
- **How**: `Completion.norm_coe`, `norm_embedding_eq`, `complexEmbedding_norm_zeta_eq_one`.
- **Uses from project**: [InfiniteCompletion, ζ, complexEmbedding_norm_zeta_eq_one]
- **Visibility**: public
- **Lines**: 95-100

### `private theorem zeta_ne_zero`
- **Type**: `ζ ≠ 0`
- **Uses from project**: [ζ, zeta_isPrimitiveRoot]
- **Visibility**: private
- **Lines**: 114-118
- **Notes**: reused by principalAdele_zeta_ne_zero.

### `example` (product formula for ζ)
- **Uses from project**: [ζ, zeta_ne_zero]
- **Visibility**: example
- **Lines**: 120-123

### `example` (product formula for etaUnit)
- **Uses from project**: [etaUnit]
- **Visibility**: example
- **Lines**: 125-134

### `abbrev CyclotomicThreeInfiniteAdeleRing`
- **Type**: `Type := NumberField.InfiniteAdeleRing K`
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 148-149

### `abbrev infinitePrincipalAdele_zeta`
- **Type**: `CyclotomicThreeInfiniteAdeleRing`
- **Uses from project**: [CyclotomicThreeInfiniteAdeleRing, ζ]
- **Visibility**: public
- **Lines**: 151-152

### `abbrev infinitePrincipalAdele_etaUnit`
- **Type**: `CyclotomicThreeInfiniteAdeleRing`
- **Uses from project**: [CyclotomicThreeInfiniteAdeleRing, etaUnit]
- **Visibility**: public
- **Lines**: 154-155

### `example` (infinite-adele norm of ζ)
- **Uses from project**: [infinitePrincipalAdele_zeta, ζ]
- **Visibility**: example
- **Lines**: 157-159

### `example` (DenseRange algebraMap)
- **Uses from project**: [CyclotomicThreeInfiniteAdeleRing]
- **Visibility**: example
- **Lines**: 161-163

### `theorem canonicalEmbedding_zetaInt_mem_integerLattice`
- **Type**: `canonicalEmbedding K (algebraMap … zetaInt) ∈ integerLattice K`
- **Uses from project**: [zetaInt]
- **Visibility**: public
- **Lines**: 177-182

### `abbrev mixedEmbedding_zeta`
- **Type**: `mixedEmbedding.mixedSpace K := mixedEmbedding K ζ`
- **Uses from project**: [ζ]
- **Visibility**: public
- **Lines**: 198-199

### `example` (convexBodyLT membership)
- **Uses from project**: [mixedEmbedding_zeta, ζ]
- **Visibility**: example
- **Lines**: 201-205

### `example` (measurableSet fundamentalCone)
- **Uses from project**: []
- **Visibility**: example
- **Lines**: 207-209

### `example` (measurableSet normLeOne)
- **Uses from project**: []
- **Visibility**: example
- **Lines**: 211-213

### `theorem polarSpace_nonempty`
- **Type**: `Nonempty (mixedEmbedding.polarSpace K)`
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 215-217

### `theorem house_zeta`
- **Type**: `NumberField.house ζ = 1`
- **How**: `le_antisymm`; `canonicalEmbedding.norm_le_iff` and `complexEmbedding_norm_zeta_eq_one`.
- **Uses from project**: [ζ, complexEmbedding_norm_zeta_eq_one]
- **Visibility**: public
- **Lines**: 231-242

### `theorem house_etaUnit`
- **Type**: `NumberField.house (algebraMap … etaUnit) = 1`
- **How**: simp reduce to `house_zeta`.
- **Uses from project**: [etaUnit, zetaInt, house_zeta]
- **Visibility**: public
- **Lines**: 244-246

### `abbrev CyclotomicThreeAdeleRing`
- **Type**: `Type := NumberField.AdeleRing (𝓞 K) K`
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 261-262

### `abbrev principalAdele_zeta`
- **Type**: `CyclotomicThreeAdeleRing`
- **Uses from project**: [CyclotomicThreeAdeleRing, ζ]
- **Visibility**: public
- **Lines**: 264-265

### `abbrev principalAdele_etaUnit`
- **Type**: `CyclotomicThreeAdeleRing`
- **Uses from project**: [CyclotomicThreeAdeleRing, etaUnit]
- **Visibility**: public
- **Lines**: 267-268

### `theorem principalAdele_zeta_ne_zero`
- **Type**: `principalAdele_zeta ≠ 0`
- **How**: `AdeleRing.algebraMap_injective` + `zeta_ne_zero`.
- **Uses from project**: [principalAdele_zeta, zeta_ne_zero]
- **Visibility**: public
- **Lines**: 270-272

### `theorem principalAdele_etaUnit_is_unit_everywhere`
- **Type**: `∀ v : FinitePlace K, v (algebraMap … etaUnit) = 1`
- **How**: `norm_embedding_eq`, `norm_eq_one_iff_notMem`, unit not in maximal ideal.
- **Uses from project**: [etaUnit]
- **Visibility**: public
- **Lines**: 274-293

### `abbrev cyclotomicThreeDedekindZeta`
- **Type**: `(s : ℂ) : ℂ := dedekindZeta K s`
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 307-308

### `abbrev cyclotomicThreeDedekindZetaResidue`
- **Type**: `ℝ := dedekindZeta_residue K`
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 310-311

### `example` (residue > 0)
- **Uses from project**: [cyclotomicThreeDedekindZetaResidue]
- **Visibility**: example
- **Lines**: 313-315

### `example` (class number formula residue)
- **Uses from project**: [cyclotomicThreeDedekindZetaResidue]
- **Visibility**: example
- **Lines**: 317-323

### File Summary — LocalGlobal.lean
- Total decls: ~37 (many abbrevs/examples; theorems ~11, defs 1, abbrevs ~14, examples ~11).
- Key API: `heightOneThree`, `complexEmbedding_norm_zeta_eq_one`, `zeta_ne_zero`.
- Public headlines: `infiniteCompletion_zeta_norm`, `house_zeta`/`house_etaUnit`, `principalAdele_zeta_ne_zero`, `principalAdele_etaUnit_is_unit_everywhere`, product/class-number-formula `example`s.
- sorry: none. set_option: none. proofs >30 lines: none.

---

## CMField.lean

### `theorem isCMField`
- **Type**: `NumberField.IsCMField K`
- **What**: ℚ(ζ₃) is a CM field.
- **How**: `IsCyclotomicExtension.Rat.isCMField`.
- **Uses from project**: []
- **Visibility**: public
- **Lines**: 26-27

### `theorem cmField_isTotallyComplex`
- **Type**: `NumberField.IsTotallyComplex K`
- **How**: `isTotallyComplex` (Embeddings).
- **Uses from project**: [isTotallyComplex]
- **Visibility**: public
- **Lines**: 29-30

### `theorem cmField_quadratic_over_maximalRealSubfield`
- **Type**: `Algebra.IsQuadraticExtension (maximalRealSubfield K) K`
- **How**: from `IsCMField` instance + infer_instance.
- **Uses from project**: [isCMField]
- **Visibility**: public
- **Lines**: 32-35

### `theorem cmField_unitsRank_eq_maximalRealSubfield`
- **Type**: `Units.rank (maximalRealSubfield K) = Units.rank K`
- **How**: `IsCMField.units_rank_eq_units_rank`.
- **Uses from project**: [isCMField]
- **Visibility**: public
- **Lines**: 37-41

### File Summary — CMField.lean
- Total decls: 4 (theorems 4).
- Key API: `isCMField`.
- Note: imports Embeddings only (off the main linear chain — a special-topic leaf file).
- sorry/set_option/long proofs: none.

---

## Cross-file notes

- **Duplicate**: private `zeta_pow_three` defined identically in both PrimeSplitting.lean (36-37) and Units.lean (34-35).
- **Common.lean helpers used here**: `eq_of_le_of_absNorm_eq`, `natAbs_lt_of_abs_ratCast_lt`, `left_eq_prime_of_mul_eq_prime_sq_of_ne_one`, `not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow`, `not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ`. NOT used: `exists_int_inverse_mod_prime`, `torsionPowerHom`, `rankOnePowerHom`, `two_le_ramificationIdx_…`/`ramificationIdx_ne_one_…` (consumed indirectly), `eq_prime_of_dvd_prime_sq_…`.
- **CubeRootThree twin**: the entire `PrivateMachinery` block (`residueHom`, `residueHom_zetaInt`, `ker_residueHom`, `residueHom_surjective`, `isMaximal_span_pair`, `absNorm_span_pair`, `minpoly_gen_eq`, `gen_eq_zetaInt`) is the structural twin of CubeRootThree's same-named private decls — same proof skeleton, differing only by the defining relation (`r²+r+1=0` mod p here vs `r³=3` there). `ramified_iff_eq_three`, `absNorm_span_natCast`, `span_three_eq`, `cubeRootThreePolynomialMod`↔`zetaThreePolynomialMod`, and the different-ideal `prime_dvd_differentIdeal_iff_…` are all near-identical in shape.
