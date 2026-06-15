# CyclotomicThree (`ℚ(ζ₃) = ℚ(√-3)`) — Declaration Inventory

Folder: `XYin/NumberField/FieldExamples/CyclotomicThree/`
Field: `K = CyclotomicField 3 ℚ`, the third cyclotomic field = `ℚ(√-3)`, built via
`IsCyclotomicExtension {3} ℚ K`; generator `ζ` a primitive cube root with `Φ₃ = X²+X+1`
(`ζ²+ζ+1 = 0`). Degree 2, signature `(0,1)`, ring of integers `ℤ[ζ]` (Eisenstein integers),
disc `-3`, class number 1, unit group `μ₆` (rank 0, regulator 1), norm-Euclidean, CM field.
Twin of `CubeRootThree` (`ℚ(∛3)`): there the cubic relation `r³=3` drives everything; here the
quadratic cyclotomic relation `r²+r+1=0` plays the analogous structural role.
All declarations in `namespace NumberField.CyclotomicThree` unless noted. Shared helpers from
`XYin/NumberField/FieldExamples/Common.lean` (`namespace NumberField.FieldExamples`).
**Sorry-free**: confirmed (grep clean). Rank-0 units, so no Artin-bound blockers (unlike ζ₅/ζ₈).
Reduction-mod-p / Kummer-Dedekind machinery uses **Common's ResidueHom** (`isMaximal_span_gen_sub`,
`absNorm_span_gen_sub`) rather than bespoke residue maps; only thin local wrappers remain.

---

## Basic.lean

Establishes the cyclotomic model `K = CyclotomicField 3 ℚ`, degree 2, and a web of `AlgEquiv`s
identifying it with three other presentations of the same field: `AdjoinRoot (X²+X+1)`,
`AdjoinRoot (X²+3) = ℚ(√-3)`, and `QuadraticAlgebra ℚ (-3) 0`.

### `abbrev K`
- **Type**: `K : Type := CyclotomicField 3 ℚ`
- **What**: The third cyclotomic field = `ℚ(√-3)`.
- **How**: Direct abbrev.
- **Uses from project**: []
- **Visibility**: public — **Lines**: 33

### `instance : IsCyclotomicExtension {3} ℚ K`
- **What**: The cyclotomic-extension structure. — **How**: `CyclotomicField.isCyclotomicExtension 3 ℚ`.
- **Uses from project**: [`K`] — **Visibility**: public (instance) — **Lines**: 35-36

### `abbrev ζ`
- **Type**: `ζ : K := IsCyclotomicExtension.zeta 3 ℚ K`
- **What**: Chosen primitive cube root of unity. — **How**: mathlib `IsCyclotomicExtension.zeta`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 39

### `theorem zeta_isPrimitiveRoot`
- **Type**: `IsPrimitiveRoot ζ 3` — **How**: `IsCyclotomicExtension.zeta_spec`.
- **Uses from project**: [`ζ`] — **Visibility**: public — **Lines**: 41-42 — heavily reused.

### `theorem zeta_sq_add_zeta_add_one_eq_zero`
- **Type**: `ζ ^ 2 + ζ + 1 = 0` — the defining quadratic relation (`Φ₃(ζ)=0`).
- **How**: `IsPrimitiveRoot.isRoot_cyclotomic` + `simpa`. The cyclotomic analogue of `cubeRootThree_cube`.
- **Uses from project**: [`zeta_isPrimitiveRoot`] — **Visibility**: public — **Lines**: 45-46

### `theorem adjoin_zeta_eq_top`
- **Type**: `Algebra.adjoin ℚ {ζ} = ⊤` — **How**: `IsCyclotomicExtension.adjoin_primitive_root_eq_top`.
- **Uses from project**: [`zeta_isPrimitiveRoot`] — **Visibility**: public — **Lines**: 49-50

### `theorem degree_eq_two`  ★ headline
- **Type**: `Module.finrank ℚ K = 2` — `[K:ℚ] = φ(3) = 2`.
- **How**: `IsCyclotomicExtension.Rat.finrank` + `Nat.totient_prime`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 53-55

### `instance : Algebra.IsQuadraticExtension ℚ K`
- **What**: Records degree 2 as a typeclass. — **How**: `degree_eq_two`.
- **Uses from project**: [`degree_eq_two`] — **Visibility**: public (instance) — **Lines**: 57-58

### `abbrev zetaThreePolynomial`
- **Type**: `ℚ[X] := X ^ 2 + X + 1` — `Φ₃`.
- **Uses from project**: [] — **Visibility**: public — **Lines**: 65

### `instance : Fact (Irreducible zetaThreePolynomial)`
- **How**: rewrite as `cyclotomic 3 ℚ`, then `cyclotomic.irreducible_rat`.
- **Uses from project**: [`zetaThreePolynomial`] — **Visibility**: public (instance) — **Lines**: 67-70

### `abbrev KAdjoinRoot`
- **Type**: `AdjoinRoot zetaThreePolynomial` — the `AdjoinRoot (X²+X+1)` model.
- **Uses from project**: [`zetaThreePolynomial`] — **Visibility**: public — **Lines**: 73

### `theorem zetaThreePolynomial_eq_minpoly`
- **Type**: `zetaThreePolynomial = minpoly ℚ ζ`
- **How**: rewrite as `cyclotomic 3 ℚ`, `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible`.
- **Uses from project**: [`zetaThreePolynomial`, `ζ`] — **Visibility**: public — **Lines**: 76-80

### `def zetaMinpolyAdjoinRootPresentation`
- **Type**: `IsAdjoinRoot K (minpoly ℚ ζ)` — **How**: `IsAdjoinRoot.mkOfAdjoinEqTop` from integrality + `adjoin = ⊤`.
- **Uses from project**: [`ζ`, `zeta_isPrimitiveRoot`] — **Visibility**: public — **Lines**: 83-86

### `abbrev adjoinRootEquivCyclotomic`
- **Type**: `KAdjoinRoot ≃ₐ[ℚ] K` — identifies the `AdjoinRoot Φ₃` model with the cyclotomic one.
- **How**: `AdjoinRoot.algEquivOfEq` (Φ₃ = minpoly) ∘ `IsAdjoinRoot.adjoinRootAlgEquiv`.
- **Uses from project**: [`zetaThreePolynomial_eq_minpoly`, `zetaMinpolyAdjoinRootPresentation`]
- **Visibility**: public — **Lines**: 93-96 — used in `Embeddings.exists_complexEmbedding_zeta`.

### `theorem adjoinRootEquivCyclotomic_root`
- **Type**: `adjoinRootEquivCyclotomic (AdjoinRoot.root …) = ζ` — **How**: `AdjoinRoot.algEquivOfEq_root` + `simp`.
- **Uses from project**: [`adjoinRootEquivCyclotomic`] — **Visibility**: public — **Lines**: 99-105

### `theorem two_mul_zeta_add_one_sq`
- **Type**: `(2*ζ + 1)^2 = -3` — exhibits `2ζ+1 = √-3`.
- **How**: `calc` collapsing `4(ζ²+ζ+1) - 3` via the relation. — **Uses from project**: [`zeta_sq_add_zeta_add_one_eq_zero`]
- **Visibility**: public — **Lines**: 108-112

### `abbrev sqrtNegThreePolynomial`
- **Type**: `ℚ[X] := X ^ 2 + 3`. — **Uses from project**: [] — **Visibility**: public — **Lines**: 115

### `instance : Fact (Irreducible sqrtNegThreePolynomial)`
- **How**: `irreducible_of_degree_le_three_of_not_isRoot`; no rational root since `x²+3 > 0` (`nlinarith`).
- **Uses from project**: [`sqrtNegThreePolynomial`] — **Visibility**: public (instance) — **Lines**: 117-127

### `abbrev QSqrtNegThree`, `abbrev sqrtNegThreeRoot`, `abbrev zetaThreeRoot`
- **Types**: `AdjoinRoot (X²+3)`; its root; the root of `AdjoinRoot (X²+X+1)`.
- **Uses from project**: [`sqrtNegThreePolynomial`/`zetaThreePolynomial`] — **Visibility**: public — **Lines**: 130-136

### `theorem sqrtNegThreeRoot_sq`
- **Type**: `sqrtNegThreeRoot ^ 2 = -3` — **How**: `AdjoinRoot.eval₂_root` + `calc`.
- **Uses from project**: [`sqrtNegThreeRoot`] — **Visibility**: public — **Lines**: 138-144

### `theorem zetaThreeRoot_relation`
- **Type**: `zetaThreeRoot ^ 2 + zetaThreeRoot + 1 = 0` — **How**: `AdjoinRoot.eval₂_root`.
- **Uses from project**: [`zetaThreeRoot`] — **Visibility**: public — **Lines**: 146-148

### `def sqrtNegThreeToZetaThree` / `theorem …_root`
- **Type**: `QSqrtNegThree →ₐ[ℚ] KAdjoinRoot`, sending `√-3 ↦ 2ζ+1`.
- **How**: `AdjoinRoot.liftAlgHom`; relation check `(2ζ+1)²+3 = 4(ζ²+ζ+1) = 0`. `_root` is `@[simp]`.
- **Uses from project**: [`zetaThreeRoot_relation`, `zetaThreeRoot`] — **Visibility**: public — **Lines**: 151-166

### `def zetaThreeToSqrtNegThree` / `theorem …_root`
- **Type**: `KAdjoinRoot →ₐ[ℚ] QSqrtNegThree`, sending `ζ ↦ (√-3 - 1)/2`.
- **How**: `AdjoinRoot.liftAlgHom`; relation check via `(√-3)²=-3`. `_root` is `@[simp]`.
- **Uses from project**: [`sqrtNegThreeRoot_sq`, `sqrtNegThreeRoot`] — **Visibility**: public — **Lines**: 169-185

### `def sqrtNegThreeEquivZetaThree` / `theorem …_root`
- **Type**: `QSqrtNegThree ≃ₐ[ℚ] KAdjoinRoot` — the two `AdjoinRoot` models are the same field.
- **How**: bundle the two maps; `left_inv`/`right_inv` via `AdjoinRoot.algHom_ext` + `ring`. `_root` `@[simp]`.
- **Uses from project**: [`sqrtNegThreeToZetaThree`, `zetaThreeToSqrtNegThree`, their `_root` lemmas]
- **Visibility**: public — **Lines**: 188-221

### `def sqrtNegThreeEquivCyclotomic` / `theorem …_root`
- **Type**: `QSqrtNegThree ≃ₐ[ℚ] K`, root `↦ 2ζ+1` — `ℚ(√-3)`-AdjoinRoot model **is** the cyclotomic field.
- **How**: `sqrtNegThreeEquivZetaThree.trans adjoinRootEquivCyclotomic`.
- **Uses from project**: [`sqrtNegThreeEquivZetaThree`, `adjoinRootEquivCyclotomic`] — **Visibility**: public — **Lines**: 224-231

### `instance : Fact (∀ r : ℚ, r ^ 2 ≠ -3 + 0 * r)`
- **What**: nondegeneracy hypothesis for `QuadraticAlgebra ℚ (-3) 0`. — **How**: `nlinarith` (`r²≥0`).
- **Uses from project**: [] — **Visibility**: public (instance) — **Lines**: 233-237

### `abbrev QSqrtNegThreeQuadratic`, `abbrev sqrtNegThreeQuadraticRoot`
- **Types**: `QuadraticAlgebra ℚ (-3) 0`; its `QuadraticAlgebra.omega`.
- **Uses from project**: [] — **Visibility**: public — **Lines**: 240-243

### `theorem sqrtNegThreeQuadraticRoot_sq`
- **Type**: `sqrtNegThreeQuadraticRoot ^ 2 = -3` — **How**: `QuadraticAlgebra.omega_mul_omega_eq_add` + `simp`.
- **Uses from project**: [`sqrtNegThreeQuadraticRoot`] — **Visibility**: public — **Lines**: 245-248

### `def sqrtNegThreeQuadraticEquivAdjoinRoot` / `theorem …_root`
- **Type**: `QSqrtNegThreeQuadratic ≃ₐ[ℚ] QSqrtNegThree` — **How**: `QuadraticAlgebra.lift` ↔ `AdjoinRoot.liftAlgHom`,
  glued by `AlgEquiv.ofAlgHom`; `algHom_ext` on both sides. Both **private**.
- **Uses from project**: [`sqrtNegThreeRoot_sq`, `sqrtNegThreeQuadraticRoot_sq`] — **Visibility**: private — **Lines**: 250-292

### `def sqrtNegThreeQuadraticEquivCyclotomic` / `theorem …_root`
- **Type**: `QSqrtNegThreeQuadratic ≃ₐ[ℚ] K`, root `↦ 2ζ+1` — radical-quadratic-algebra model **is** the cyclotomic field.
- **How**: trans of the previous two equivs.
- **Uses from project**: [`sqrtNegThreeQuadraticEquivAdjoinRoot`, `sqrtNegThreeEquivCyclotomic`] — **Visibility**: public — **Lines**: 295-302

**File Summary — Basic.lean**: the cyclotomic core (`K`, `ζ`, `degree_eq_two`, `zeta_…_eq_zero`)
plus a four-way model-equivalence bridge (`AdjoinRoot Φ₃`, `AdjoinRoot (X²+3)`, `QuadraticAlgebra`,
cyclotomic). Key reused: `ζ`, `zeta_isPrimitiveRoot`, `zeta_sq_add_zeta_add_one_eq_zero`,
`degree_eq_two`, `adjoinRootEquivCyclotomic`. The quadratic-algebra and `√-3` equivalences are
largely self-contained bridges (mostly unused downstream — downstream uses `ζ` directly).
No sorry. Longest proof: `sqrtNegThreeEquivZetaThree` (~34 lines).

---

## Galois.lean

### `theorem isGalois`
- **Type**: `IsGalois ℚ K` — **How**: `IsCyclotomicExtension.isGalois`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 33-34

### `abbrev galEquivZMod`
- **Type**: `Gal(K/ℚ) ≃* (ZMod 3)ˣ` — cyclotomic Galois theory identification.
- **How**: `IsCyclotomicExtension.Rat.galEquivZMod 3 K`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 40-41

### `theorem galEquivZMod_apply_zeta`
- **Type**: `σ ζ = ζ ^ (galEquivZMod σ).val.val` — cyclotomic character.
- **How**: `IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq`.
- **Uses from project**: [`galEquivZMod`, `zeta_isPrimitiveRoot`] — **Visibility**: public — **Lines**: 44-46

### `theorem galoisGroupStructure`  ★ headline
- **Type**: `Nonempty (Gal(K/ℚ) ≃* Multiplicative (ZMod 2))` — Gal cyclic of order 2 (`(ℤ/3)ˣ ≅ ℤ/2`).
- **How**: card via `IsGalois.card_aut_eq_finrank` + `finrank` + `totient_prime`; `mulEquivOfPrimeCardEq`.
- **Uses from project**: [`isGalois`, `K`] — **Visibility**: public — **Lines**: 50-59

**File Summary — Galois.lean**: 4 decls. Galois group `≅ (ℤ/3)ˣ ≅ ℤ/2` (conjugation `ζ↦ζ²`).
Unlike `CubeRootThree` (non-Galois, S₃ closure), this field is its own Galois closure. No sorry.

---

## Embeddings.lean

### `theorem nrRealPlaces_eq_zero`
- **Type**: `InfinitePlace.nrRealPlaces K = 0` — **How**: `IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 34-35

### `theorem isTotallyComplex`
- **Type**: `IsTotallyComplex K` — **How**: `IsCyclotomicExtension.Rat.isTotallyComplex`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 37-38 — note `attribute [-instance] DivisionRing.toRatAlgebra` in effect for this section.

### `theorem nrComplexPlaces_eq_one`
- **Type**: `InfinitePlace.nrComplexPlaces K = 1` — **How**: `…nrComplexPlaces_eq_totient_div_two` + `totient_prime`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 40-42

### `theorem infinitePlace_card_eq_one`
- **Type**: `Fintype.card (InfinitePlace K) = 1` — **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces` + above.
- **Uses from project**: [`nrRealPlaces_eq_zero`, `nrComplexPlaces_eq_one`] — **Visibility**: public — **Lines**: 56-59

### `theorem infinitePlace_isComplex`
- **Type**: `∀ v, IsComplex v` — **How**: `isTotallyComplex.isComplex`.
- **Uses from project**: [`isTotallyComplex`] — **Visibility**: public — **Lines**: 61-63

### `theorem exists_complexEmbedding_zeta`
- **Type**: `∃ σ : K →+* ℂ, σ ζ = exp(2πi/3)` — exhibits an explicit complex embedding.
- **How**: `Complex.isPrimitiveRoot_exp`; lift via `AdjoinRoot.liftAlgHom` composed with
  `adjoinRootEquivCyclotomic.symm`.
- **Uses from project**: [`zetaThreePolynomial`, `adjoinRootEquivCyclotomic`, `adjoinRootEquivCyclotomic_root`]
- **Visibility**: public — **Lines**: 65-78

**File Summary — Embeddings.lean**: 6 decls. Signature `(0,1)` (totally complex, one complex place),
plus an explicit `ζ ↦ exp(2πi/3)` embedding built through the `AdjoinRoot` bridge. No sorry.

---

## RingOfIntegers.lean

### `def zetaInt`
- **Type**: `𝓞 K := zeta_isPrimitiveRoot.toInteger` — `ζ` as an algebraic integer. Pervasive downstream.
- **Uses from project**: [`zeta_isPrimitiveRoot`] — **Visibility**: public — **Lines**: 33

### `theorem zeta_pow_three`
- **Type**: `ζ ^ 3 = 1` — **How**: `IsPrimitiveRoot.pow_eq_one`.
- **Uses from project**: [`zeta_isPrimitiveRoot`] — **Visibility**: public — **Lines**: 36-37 — reused in norm/unit computations.

### `abbrev integralPowerBasis`
- **Type**: `PowerBasis ℤ (𝓞 K) := zeta_isPrimitiveRoot.integralPowerBasis`
- **What**: explicit integral power basis from a primitive root (cyclotomic-specific).
- **Uses from project**: [`zeta_isPrimitiveRoot`] — **Visibility**: public — **Lines**: 43-44

### `theorem integralPowerBasis_gen`, `theorem integralPowerBasis_dim`
- **Types**: `gen = zeta_isPrimitiveRoot.toInteger`; `dim = 2`.
- **How**: `simp [integralPowerBasis]`; `+ totient_prime`.
- **Uses from project**: [`integralPowerBasis`] — **Visibility**: public — **Lines**: 47-51

### `abbrev zetaExplicitIntegralBasis`
- **Type**: `Basis (Fin 2) ℤ (𝓞 K)` — the explicit integral basis `[1, ζ]`.
- **How**: reindex `integralPowerBasis.basis` along `finCongr integralPowerBasis_dim`.
- **Uses from project**: [`integralPowerBasis`, `integralPowerBasis_dim`] — **Visibility**: public — **Lines**: 54-55 — heavily reused (finrank = 2 throughout).

### `theorem zetaExplicitIntegralBasis_zero`, `theorem zetaExplicitIntegralBasis_one`
- **Types**: `basis 0 = 1`; `basis 1 = zeta_isPrimitiveRoot.toInteger`.
- **How**: `Basis.reindex_apply` + `basis_eq_pow` + the `Fin`-coe computations.
- **Uses from project**: [`zetaExplicitIntegralBasis`, `integralPowerBasis`] — **Visibility**: public — **Lines**: 57-75

### `theorem cyclotomicRing_isIntegralClosure`
- **Type**: `IsIntegralClosure (CyclotomicRing 3 ℤ ℚ) ℤ K` — **How**: `…Rat.cyclotomicRing_isIntegralClosure`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 77-79

### `theorem isIntegralClosure_adjoin_zeta`
- **Type**: `IsIntegralClosure (Algebra.adjoin ℤ {ζ}) ℤ K` — i.e. `ℤ[ζ] = 𝓞 K`.
- **How**: `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`.
- **Uses from project**: [`zeta_isPrimitiveRoot`] — **Visibility**: public — **Lines**: 86-88

### `theorem integralPowerBasis_adjoin_gen_eq_top`
- **Type**: `Algebra.adjoin ℤ {integralPowerBasis.gen} = ⊤` — **How**: `PowerBasis.adjoin_gen_eq_top`.
- **Uses from project**: [`integralPowerBasis`] — **Visibility**: public — **Lines**: 94-96

**File Summary — RingOfIntegers.lean**: 10 decls. Ring of integers `= ℤ[ζ]` via the cyclotomic
`integralPowerBasis`; explicit `[1,ζ]` basis. The `IsPrimitiveRoot.integralPowerBasis` machinery
makes the integral basis essentially free here (contrast CubeRootThree which derives it laboriously).
No sorry.

---

## Discriminant.lean

### `theorem numberField_discr_eq`  ★ headline
- **Type**: `NumberField.discr K = -3` — **How**: `IsCyclotomicExtension.Rat.discr_prime 3 K` + `norm_num`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 35-37 — used in `PrimeSplitting` (different ideal / ramification).

### `theorem zetaExplicitIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ zetaExplicitIntegralBasis = -3` — **How**: `NumberField.discr_eq_discr` ▸ `discr_prime`.
- **Uses from project**: [`zetaExplicitIntegralBasis`] — **Visibility**: public — **Lines**: 39-46

### `theorem integralBasis_discr`
- **Type**: `Algebra.discr ℚ (integralBasis K) = -3` — **How**: `NumberField.coe_discr` bridge from the ℤ-disc.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 53-58

### `example` (×2)
- **What**: change-of-basis discriminant law: `discr(P • b) = det(P)² · discr(b)`; unimodular `det=±1`
  preserves `-3`. **How**: `Algebra.discr_of_matrix_mulVec` + `integralBasis_discr`.
- **Uses from project**: [`integralBasis_discr`] — **Visibility**: examples (no name) — **Lines**: 66-83

**File Summary — Discriminant.lean**: disc `= -3` (smallest absolute disc among quadratic fields),
three named theorems + two illustrative `example`s on unimodular change-of-basis invariance. No sorry.

---

## PrimeSplitting.lean

Largest file. A `PrivateMachinery` section sets up the integral minimal polynomial and the two
automorphisms, then derives ramification at 3, inertness at 2, splitting at 7, and the general
congruence splitting law `p splits ⟺ p ≡ 1 (mod 3)`. **Uses Common's ResidueHom** API
(`isMaximal_span_gen_sub`, `absNorm_span_gen_sub`) via thin local wrappers — no bespoke residue map.

### `private theorem gen_eq_zetaInt`, `zetaInt_pow_three`, `zetaInt_relation`
- **Types**: `integralPowerBasis.gen = zetaInt`; `zetaInt^3 = 1`; `zetaInt²+zetaInt+1 = 0`.
- **How**: `integralPowerBasis_gen`/`rfl`; `toInteger_cube_eq_one`; `isRoot_cyclotomic` + `ext`.
- **Uses from project**: [`integralPowerBasis_gen`, `zetaInt`, `zeta_isPrimitiveRoot`] — **Visibility**: private — **Lines**: 36-45

### `private def sig2` / `private theorem sig2_zeta`
- **Type**: `K ≃ₐ[ℚ] K`, the nontrivial automorphism `ζ ↦ ζ²` (conjugation).
- **How**: `IsCyclotomicExtension.fromZetaAut` from `pow_of_coprime 2`; spec via `fromZetaAut_spec`.
- **Uses from project**: [`zeta_isPrimitiveRoot`] — **Visibility**: private — **Lines**: 47-53

### `private theorem autEq'`
- **Type**: `∀ σ, σ = 1 ∨ σ = sig2` — the only two automorphisms.
- **How**: `decide` on `(ZMod 3)ˣ` values via `autToPow_spec`; extensionality through the power basis.
- **Uses from project**: [`sig2`, `sig2_zeta`, `zeta_isPrimitiveRoot`] — **Visibility**: private — **Lines**: 55-67

### `private theorem prod_aut_apply`
- **Type**: `∏ σ, σ x = x * sig2 x` — product over Galois group of size 2.
- **How**: `univ = {1, sig2}`, `Finset.prod_pair`. — **Uses from project**: [`autEq'`, `sig2`, `sig2_zeta`, `zeta_isPrimitiveRoot`]
- **Visibility**: private — **Lines**: 69-81

### `private theorem minpoly_gen_eq`
- **Type**: `minpoly ℤ integralPowerBasis.gen = X²+X+C 1` — integral minimal polynomial.
- **How**: `minpoly.isIntegrallyClosed_dvd` (divides X²+X+1 via `zetaInt_relation`) + monic-degree-2 argument
  forcing the cofactor to be 1.
- **Uses from project**: [`gen_eq_zetaInt`, `zetaInt_relation`, `integralPowerBasis_dim`] — **Visibility**: private — **Lines**: 83-111

### `private theorem isMaximal_span_pair`, `private theorem absNorm_span_pair`
- **Types**: for `r²+r+1≡0 (mod p)`: `(span {p, ζ-r}).IsMaximal`; `absNorm = p`.
- **How**: thin wrappers over **Common's** `isMaximal_span_gen_sub` / `absNorm_span_gen_sub` (Kummer-Dedekind
  ResidueHom), feeding `minpoly_gen_eq`.
- **Uses from project**: [`gen_eq_zetaInt`, `minpoly_gen_eq`, `isMaximal_span_gen_sub`, `absNorm_span_gen_sub`]
- **Visibility**: private — **Lines**: 113-127

### `theorem norm_eq_normForm`  ★ key
- **Type**: `Algebra.norm ℚ (x•1 + y•ζ) = x² - xy + y²` — the principal binary quadratic form of disc `-3`.
- **How**: `norm_eq_prod_automorphisms` + `prod_aut_apply` + `linear_combination` against the cyclotomic relation.
- **Uses from project**: [`prod_aut_apply`, `sig2_zeta`, `zeta_pow_three`] — **Visibility**: public — **Lines**: 130-140

### `theorem intNorm_eq_normForm`
- **Type**: `Algebra.norm ℤ (x•1 + y•zetaInt) = x² - xy + y²` (`x,y ∈ ℤ`).
- **How**: `Algebra.coe_norm_int` cast bridge to `norm_eq_normForm`.
- **Uses from project**: [`zetaInt`, `norm_eq_normForm`] — **Visibility**: public — **Lines**: 142-154

### `theorem isUnit_iff_normForm`  ★
- **Type**: `IsUnit (x•1 + y•zetaInt) ↔ x²-xy+y² = 1` — the unit equation (6 solutions = `±1,±ζ,±ζ²`).
- **How**: `NumberField.isUnit_iff_norm` + `intNorm_eq_normForm`; rules out `-1` via positivity (`nlinarith`/`omega`).
- **Uses from project**: [`intNorm_eq_normForm`, `zetaInt`] — **Visibility**: public — **Lines**: 156-171

### `theorem norm_one_sub_zeta`, `theorem norm_one_add_zeta`
- **Types**: `norm ℚ (1-ζ) = 3`; `norm ℚ (1+ζ) = 1`. — **How**: specialise `norm_eq_normForm`.
- **Uses from project**: [`norm_eq_normForm`] — **Visibility**: public — **Lines**: 173-183

### `theorem zetaInt_sub_one_prime`
- **Type**: `Prime (zetaInt - 1)` — **How**: `IsPrimitiveRoot.zeta_sub_one_prime'`.
- **Uses from project**: [`zetaInt`] — **Visibility**: public — **Lines**: 184-187

### `theorem zetaInt_sub_one_dvd_three`
- **Type**: `(zetaInt - 1) ∣ 3` — **How**: `toInteger_sub_one_dvd_prime'`.
- **Uses from project**: [`zetaInt`] — **Visibility**: public — **Lines**: 189-192

### `theorem span_three_eq`  ★ ramification
- **Type**: `span {3} = span {zetaInt - 1} ^ 2` — `3` is totally ramified `(3)=(ζ-1)²`.
- **How**: `span_singleton_pow` + `span_singleton_eq_span_singleton`; explicit unit via `zetaInt_relation`/`pow_three`.
- **Uses from project**: [`zetaInt_pow_three`, `zetaInt_relation`, `zetaInt`] — **Visibility**: public — **Lines**: 194-203

### `private theorem span_zetaInt_sub_one_eq_pair`
- **Type**: `span {zetaInt-1} = span {(3:ℕ), zetaInt-(1:ℤ)}` — bridges to the Common pair form.
- **How**: `le_antisymm` via `mem_span_pair` and `span_three_eq`.
- **Uses from project**: [`span_three_eq`, `zetaInt`] — **Visibility**: private — **Lines**: 205-215

### `theorem absNorm_span_zetaInt_sub_one`
- **Type**: `absNorm (span {zetaInt-1}) = 3` (residue degree `f=1`).
- **How**: `decide` the mod-3 root, `span_zetaInt_sub_one_eq_pair`, `absNorm_span_pair`.
- **Uses from project**: [`span_zetaInt_sub_one_eq_pair`, `absNorm_span_pair`] — **Visibility**: public — **Lines**: 217-222

### `theorem isPrime_span_zetaInt_sub_one`
- **Type**: `(span {zetaInt-1}).IsPrime` — the unique prime over 3.
- **How**: `isMaximal_span_pair 3 1`.isPrime. — **Uses from project**: [`span_zetaInt_sub_one_eq_pair`, `isMaximal_span_pair`]
- **Visibility**: public — **Lines**: 224-229

### `theorem liesOver_span_zetaInt_sub_one`, `inertiaDeg_span_zetaInt_sub_one`, `ramificationIdx_span_zetaInt_sub_one`
- **Types**: `(ζ-1)` lies over `(3)`; `f=1`; `e=2`.
- **How**: `liesOver_span_iff` + `span_three_eq`; `absNorm_eq_pow_inertiaDeg'`; `ramificationIdx_spec` with a
  norm-9-vs-27 divisibility contradiction.
- **Uses from project**: [`isPrime_span_zetaInt_sub_one`, `span_three_eq`, `absNorm_span_zetaInt_sub_one`,
  `zetaExplicitIntegralBasis`] — **Visibility**: public — **Lines**: 231-274

### `theorem absNorm_span_two`
- **Type**: `absNorm (span {2}) = 4` — `2` inert, residue degree 2.
- **How**: `absNorm_span_singleton` + `norm_algebraMap` + `finrank = 2`.
- **Uses from project**: [`zetaExplicitIntegralBasis`] — **Visibility**: public — **Lines**: 276-283

### `private theorem quotient_zeta_ne_one_of_two_mem`, `absNorm_maximal_over_span_two_eq_four`
- **Types**: in a maximal `M ∋ 2`, `mk M zetaInt ≠ 1`; and `absNorm M = 4`.
- **How**: finite-field order argument: `ω = mk zetaInt` has order 3, so `3 ∣ 2^k - 1`, forcing `k=2`.
- **Uses from project**: [`zetaInt_relation`, `zetaInt_pow_three`, `absNorm_span_two`, `zetaInt`] — **Visibility**: private — **Lines**: 285-344

### `theorem isPrime_span_two`  ★ inert
- **Type**: `(span {2}).IsPrime` — `2` is inert (`Φ₃` irreducible mod 2).
- **How**: take maximal `M ⊇ (2)`, show `absNorm M = 4 = absNorm (2)`, then `eq_of_le_of_absNorm_eq` (Common).
- **Uses from project**: [`absNorm_span_two`, `absNorm_maximal_over_span_two_eq_four`, `eq_of_le_of_absNorm_eq`]
- **Visibility**: public — **Lines**: 346-358

### `theorem liesOver_span_two`, `inertiaDeg_span_two`
- **Types**: `(2)` lies over `(2)`; `f=2`. — **How**: `liesOver_span_iff`; `absNorm_eq_pow_inertiaDeg'` + `pow_right_injective`.
- **Uses from project**: [`isPrime_span_two`, `absNorm_span_two`] — **Visibility**: public — **Lines**: 360-375

### `private theorem seven_eq_mul`
- **Type**: `(7:𝓞 K) = (3+zetaInt)(3+zetaInt²)` — **How**: `linear_combination` with `pow_three`/relation.
- **Uses from project**: [`zetaInt_pow_three`, `zetaInt_relation`] — **Visibility**: private — **Lines**: 377-378

### `theorem span_seven_eq`  ★ split
- **Type**: `span {7} = span {3+ζ} * span {3+ζ²}` — `7 ≡ 1 (mod 3)` splits.
- **How**: `span_singleton_mul_span_singleton` + `seven_eq_mul`.
- **Uses from project**: [`seven_eq_mul`, `zetaInt`] — **Visibility**: public — **Lines**: 380-384

### `theorem absNorm_span_seven_factor`, `isPrime_span_seven_factor`, `liesOver_span_seven_factor`, `inertiaDeg_span_seven_factor`
- **Types**: `absNorm (3+ζ) = 7`; prime; lies over `(7)`; `f=1`.
- **How**: `intNorm_eq_normForm 3 1`; `isPrime_of_irreducible_absNorm`; `liesOver_span_iff`; `absNorm_eq_pow_inertiaDeg'`.
- **Uses from project**: [`intNorm_eq_normForm`, `seven_eq_mul`, `zetaInt`] — **Visibility**: public — **Lines**: 386-417

### `theorem ramified_iff_eq_three`  ★ ramification law
- **Type**: `(∃ P prime, span{p} ≤ P²) ↔ p = 3` — ramifies iff `p | disc = -3`.
- **How**: forward via different ideal: `dvd_differentIdeal_iff` from unramifiedness failure (Common's
  `not_map_span_natCast_le_pow_succ…` / `not_isUnramifiedAt_of_…`), then `absNorm_differentIdeal = |disc| = 3`;
  backward `span_three_eq`.
- **Uses from project**: [`numberField_discr_eq`, `span_three_eq`, `isPrime_span_zetaInt_sub_one`,
  Common ramification helpers, `zetaExplicitIntegralBasis`] — **Visibility**: public — **Lines**: 419-466

### `theorem ramificationIdx_span_two`, `ramificationIdx_span_seven_factor`
- **Types**: `e=1` at `(2)`; `e=1` at `(3+ζ)` over 7 — both unramified.
- **How**: `ramificationIdx_spec` + `ramified_iff_eq_three` contradiction.
- **Uses from project**: [`isPrime_span_two`/`isPrime_span_seven_factor`, `ramified_iff_eq_three`, `span_seven_eq`]
- **Visibility**: public — **Lines**: 468-496

### `private theorem absNorm_span_natCast`
- **Type**: `absNorm (span {(p:𝓞 K)}) = p²` — **How**: `absNorm_span_natCast` + `RingOfIntegers.rank` + `degree_eq_two`.
- **Uses from project**: [`degree_eq_two`] — **Visibility**: private — **Lines**: 498-500

### `private theorem one_mod_three_of_prime_norm`, `exists_prime_norm_of_one_mod_three`, `exists_prime_norm_iff_one_mod_three`
- **Types**: existence of a norm-`p` prime over `p` ⟺ `p ≡ 1 (mod 3)`.
- **How**: forward — `ZMod.ringEquivOfPrime`, `mk zetaInt` gives an order-3 element of `(ZMod p)ˣ` so `3 ∣ p-1`;
  backward — generator `g` of cyclic `(ZMod p)ˣ`, `g^m` of order 3 is a mod-`p` root of `X²+X+1`, feed
  `isMaximal_span_pair`/`absNorm_span_pair`.
- **Uses from project**: [`zetaInt_pow_three`, `zetaInt_relation`, `isMaximal_span_pair`, `absNorm_span_pair`, `zetaInt`]
- **Visibility**: private — **Lines**: 502-603

### `private theorem one_mod_three_of_splits`, `splits_of_one_mod_three`
- **Types**: the two directions of the splitting law in product form.
- **How**: `map_mul absNorm` + `absNorm_span_natCast`; Common's `left_eq_prime_of_mul_eq_prime_sq…`;
  distinctness via `ramified_iff_eq_three`.
- **Uses from project**: [`absNorm_span_natCast`, `exists_prime_norm_iff_one_mod_three`,
  `left_eq_prime_of_mul_eq_prime_sq_of_ne_one`, `ramified_iff_eq_three`] — **Visibility**: private — **Lines**: 605-652

### `theorem splits_iff_one_mod_three`  ★ headline splitting law
- **Type**: for `p ≠ 3` prime: `(∃ P≠Q primes, span{p}=P*Q) ↔ p ≡ 1 (mod 3)`.
- **How**: combine the two private directions.
- **Uses from project**: [`one_mod_three_of_splits`, `splits_of_one_mod_three`] — **Visibility**: public — **Lines**: 654-662

### `private theorem span_zetaInt_sub_one_dvd_differentIdeal`
- **Type**: `span {zetaInt-1} ∣ differentIdeal ℤ (𝓞 K)` — **How**: `dvd_differentIdeal_iff` from ramification at 3,
  Common's `not_map_span_natCast…`/`not_isUnramifiedAt…`.
- **Uses from project**: [`isPrime_span_zetaInt_sub_one`, `span_three_eq`, `zetaInt_sub_one_prime`,
  `absNorm_span_zetaInt_sub_one`, Common helpers] — **Visibility**: private — **Lines**: 678-714

### `theorem absNorm_differentIdeal_eq_three`
- **Type**: `absNorm (differentIdeal ℤ (𝓞 K)) = 3` — **How**: `NumberField.absNorm_differentIdeal` + `numberField_discr_eq`.
- **Uses from project**: [`numberField_discr_eq`] — **Visibility**: public — **Lines**: 715-718

### `theorem prime_dvd_differentIdeal_iff_eq_span_zeta_sub_one`
- **Type**: for prime `P ≠ ⊥`: `P ∣ different ↔ P = span {zetaInt-1}`.
- **How**: norm divides 3 ⇒ norm = 3 ⇒ `3 ∈ P`, lies over `(3)`, then
  `IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'`; converse from the dvd lemma.
- **Uses from project**: [`absNorm_differentIdeal_eq_three`, `span_zetaInt_sub_one_dvd_differentIdeal`, `zetaInt`]
- **Visibility**: public — **Lines**: 720-746

**File Summary — PrimeSplitting.lean**: the arithmetic heart. Full local picture: `3` totally
ramified `(ζ-1)²` (`e=2,f=1`), `2` inert (`f=2`), `7` split (two `f=1` primes), the congruence law
`p splits ⟺ p ≡ 1 mod 3` (cyclotomic class-field-theory shadow), and the different ideal `(ζ-1)` of
norm 3. **Uses Common's ResidueHom** (`isMaximal_span_gen_sub`, `absNorm_span_gen_sub`) plus the
generic ramification helpers — only thin `…_span_pair` wrappers are local. No sorry.

---

## ClassGroup.lean

### `abbrev zetaFractionalIdeal`, `ramifiedPrimeFractionalIdeal`
- **Types**: `spanSingleton ζ`; `span {zetaInt-1}` as fractional ideals.
- **Uses from project**: [`ζ`, `zetaInt`] — **Visibility**: public — **Lines**: 31-35

### `theorem zeta_mem_fractionalIdeal`, `zetaFractionalIdeal_absNorm`
- **Types**: `ζ ∈ zetaFractionalIdeal`; `absNorm = |Algebra.norm ℚ ζ|`.
- **How**: `mem_spanSingleton_self`; `absNorm_span_singleton`.
- **Uses from project**: [`zetaFractionalIdeal`, `ζ`] — **Visibility**: public — **Lines**: 37-43

### `theorem ramifiedPrimeFractionalIdeal_ne_zero`
- **Type**: `ramifiedPrimeFractionalIdeal ≠ 0` — **How**: `coeIdeal_ne_zero` + `…Rat.span_zeta_sub_one_ne_bot`
  (with `3^(0+1)` reshaping).
- **Uses from project**: [`ramifiedPrimeFractionalIdeal`, `zeta_isPrimitiveRoot`] — **Visibility**: public — **Lines**: 45-53

### `theorem isPrincipalIdealRing`  ★
- **Type**: `IsPrincipalIdealRing (𝓞 K)` — **How**: `IsCyclotomicExtension.Rat.three_pid K`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 72-73

### `theorem uniqueFactorizationMonoid`
- **Type**: `UniqueFactorizationMonoid (𝓞 K)` — **How**: `infer_instance` from PID.
- **Uses from project**: [`isPrincipalIdealRing`] — **Visibility**: public — **Lines**: 75-78

### `theorem classNumber_eq_one`  ★ headline
- **Type**: `NumberField.classNumber K = 1` — **How**: `classNumber_eq_one_iff.mpr (…Rat.three_pid K)`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 80-82

### `theorem classGroupStructure`
- **Type**: `Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1))` — class group trivial.
- **How**: `Nat.card = 1` ⇒ `Subsingleton`/`Unique` ⇒ `MulEquiv.ofUnique`.
- **Uses from project**: [`classNumber_eq_one`] — **Visibility**: public — **Lines**: 84-90

### `abbrev unitIdealRepresentative` / `theorem classGroupRepresentative`
- **Types**: `⟨⊤, _⟩ : (Ideal (𝓞 K))⁰`; every class `= ClassGroup.mk0 unitIdealRepresentative`.
- **How**: `Subsingleton.elim`. — **Uses from project**: [`classNumber_eq_one`, `unitIdealRepresentative`]
- **Visibility**: public — **Lines**: 92-101

**File Summary — ClassGroup.lean**: 9 decls. Class number 1 from `…Rat.three_pid`; PID ⇒ UFD;
class group trivial `≅ ZMod 1`. All invariants are direct mathlib applications. No sorry.

---

## Units.lean

### `abbrev etaUnit`
- **Type**: `(𝓞 K)ˣ` — `ζ` as a unit. — **How**: `toInteger_isPrimitiveRoot.isUnit (decide).unit`.
- **Uses from project**: [`zeta_isPrimitiveRoot`] — **Visibility**: public — **Lines**: 35-36

### `theorem unit_mem_unitsList`, `unit_eq_one_or_neg_one_or_eta`
- **Types**: every unit is among `[1,-1,η,-η,η²,-η²]`; the disjunction form.
- **How**: `IsCyclotomicExtension.Rat.Three.Units.mem`.
- **Uses from project**: [`etaUnit`, `zeta_isPrimitiveRoot`] — **Visibility**: public — **Lines**: 42-50

### `theorem torsionOrder_eq_six`
- **Type**: `Units.torsionOrder K = 6` — **How**: `IsCyclotomicExtension.Rat.torsionOrder_eq` + `norm_num`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 52-54

### `theorem unitRank_eq_zero`  ★
- **Type**: `Units.rank K = 0` — signature `(0,1)` ⇒ `r₁+r₂-1 = 0`.
- **How**: unfold `rank`, `card_eq_nrRealPlaces_add_nrComplexPlaces` + the cyclotomic place counts.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 57-64

### `theorem unitGroupStructure`  ★ headline
- **Type**: `Nonempty ((𝓞 K)ˣ ≃* Multiplicative (ZMod 6))` — units `≅ μ₆`.
- **How**: every unit is torsion (`fin_cases` over the 6-element list, each `IsOfFinOrder`); `(𝓞 K)ˣ` cyclic;
  `Nat.card = 6` via `torsionOrder_eq_six`; `mulEquivOfCyclicCardEq`.
- **Uses from project**: [`unit_mem_unitsList`, `zeta_pow_three`, `torsionOrder_eq_six`] — **Visibility**: public — **Lines**: 66-108

### `theorem regulator_eq_one`  ★
- **Type**: `Units.regulator K = 1` — rank-0 ⇒ trivial (empty) log-lattice determinant.
- **How**: `Units.regulator_eq_det'`; the index type `{w ≠ w₀}` has card 0 (from `unitRank_eq_zero` via
  `equivFinRank`), so `Matrix.det_eq_one_of_card_eq_zero` gives det = 1.
- **Uses from project**: [`unitRank_eq_zero`] — **Visibility**: public — **Lines**: 110-124

**File Summary — Units.lean**: 7 decls. Unit group `= μ₆` (rank 0), torsion order 6, regulator 1
(obtained from the *empty* `0×0` determinant, not a deep computation — contrast the
`isFundamental`/`regulator` blockers in the higher cyclotomic / real cases). The trailing empty
`Regulator` section is a structural placeholder. No sorry — **no Artin-bound blockers** (rank 0).

---

## CMField.lean

Special-topic file (imports `Embeddings`). The CM structure of `ℚ(ζ₃)`.

### `theorem isCMField`  ★
- **Type**: `NumberField.IsCMField K` — **How**: `IsCyclotomicExtension.Rat.isCMField K (S := {3})` with witness `⟨3,…⟩`.
- **Uses from project**: [`K`] — **Visibility**: public — **Lines**: 26-27

### `theorem cmField_isTotallyComplex`
- **Type**: `IsTotallyComplex K` — **How**: `isTotallyComplex` (Embeddings).
- **Uses from project**: [`isTotallyComplex`] — **Visibility**: public — **Lines**: 29-30

### `theorem cmField_quadratic_over_maximalRealSubfield`
- **Type**: `IsQuadraticExtension (maximalRealSubfield K) K` — here `maximalRealSubfield = ℚ`.
- **How**: `IsCMField` ⇒ `infer_instance`. — **Uses from project**: [`isCMField`] — **Visibility**: public — **Lines**: 32-35

### `theorem cmField_unitsRank_eq_maximalRealSubfield`
- **Type**: `Units.rank (maximalRealSubfield K) = Units.rank K` — CM rank-equality (both 0).
- **How**: `IsCMField.units_rank_eq_units_rank`. — **Uses from project**: [`isCMField`] — **Visibility**: public — **Lines**: 37-41

**File Summary — CMField.lean**: 4 decls. `ℚ(ζ₃)` is a CM field with totally real subfield `ℚ`
and matching unit rank (0). No sorry.

---

## Euclidean.lean

### `private theorem abs_norm_int_lt_of_remainder_eq`
- **Type**: given the remainder decomposition and the fractional-form bound `≤ 3/4`,
  `|N(r)| < |N(b)|` (over ℚ). — **How**: Common's `abs_intNorm_lt_of_abs_norm_le` with `3/4 < 1`, after
  `norm_eq_normForm`.
- **Uses from project**: [`abs_intNorm_lt_of_abs_norm_le`, `norm_eq_normForm`] — **Visibility**: private — **Lines**: 33-48

### `private theorem exists_coords`
- **Type**: `∀ x : K, ∃ a b : ℚ, x = a•1 + b•ζ` — coordinates in the `1,ζ` basis.
- **How**: `IsPrimitiveRoot.powerBasis.exists_eq_aeval`; degree `≤ 1` so `eq_X_add_C_of_natDegree_le_one`.
- **Uses from project**: [`zeta_isPrimitiveRoot`, `zetaThreePolynomial_eq_minpoly`] — **Visibility**: private — **Lines**: 50-65

### `theorem normEuclidean`  ★ headline
- **Type**: `∀ a b, b ≠ 0 → ∃ q r, a = b*q + r ∧ |N r| < |N b|` (natAbs) — `ℤ[ζ₃]` is norm-Euclidean.
- **How**: divide in `K`, take nearest-integer coords (`round`), bound the quadratic-form remainder
  `|s² - st + t²| ≤ 3/4` (`nlinarith` with `sq_nonneg (s±t)`); then `abs_norm_int_lt_…` +
  `natAbs_lt_of_abs_ratCast_lt` (Common). Strengthens `isPrincipalIdealRing`.
- **Uses from project**: [`exists_coords`, `zetaInt`, `abs_norm_int_lt_of_remainder_eq`,
  `natAbs_lt_of_abs_ratCast_lt`] — **Visibility**: public — **Lines**: 67-107

**File Summary — Euclidean.lean**: 3 decls. The Eisenstein integers are norm-Euclidean via the
nearest-integer / `3/4`-bound argument on the principal form `x²-xy+y²`. The covering-style bound is
*direct* here (no covering-argument blocker, unlike CubeRootThree's `normEuclidean`). No sorry.

---

## LocalGlobal.lean

Capstone: finite/infinite places, completions, product formula, canonical & mixed embedding geometry,
house, adeles, Dedekind zeta. Mix of named theorems and illustrative `example`s.

### `def heightOneThree` / `abbrev vThree`
- **Types**: `HeightOneSpectrum (𝓞 K)` at `span {zetaInt-1}`; `FinitePlace.mk` of it.
- **How**: `isPrime_span_zetaInt_sub_one`; `ne_bot` from `absNorm = 3 ≠ 0`.
- **Uses from project**: [`isPrime_span_zetaInt_sub_one`, `absNorm_span_zetaInt_sub_one`, `zetaInt`]
- **Visibility**: public — **Lines**: 35-45

### `example` (×2 over heightOneThree)
- **What**: `e=2`, `f=1` for the place over 3. **How**: `ramificationIdx_span_zetaInt_sub_one` / `inertiaDeg_…`.
- **Uses from project**: [those + `heightOneThree`] — **Lines**: 47-53

### `abbrev CompletionAtThree`, `abbrev InfiniteCompletion`
- **Types**: `heightOneThree.adicCompletion K`; `v.Completion`.
- **Uses from project**: [`heightOneThree`] — **Visibility**: public — **Lines**: 68-84

### `private theorem complexEmbedding_norm_zeta_eq_one`
- **Type**: `‖φ ζ‖ = 1` for any `φ : K →+* ℂ` — **How**: `Complex.norm_eq_one_of_pow_eq_one` (`ζ³=1`).
- **Uses from project**: [`zeta_isPrimitiveRoot`] — **Visibility**: private — **Lines**: 86-88

### `example` + `theorem infiniteCompletion_zeta_norm`
- **Types**: `InfiniteCompletion v ≃+* ℂ`; `‖algebraMap K _ ζ‖ = 1`.
- **How**: `Completion.ringEquivComplexOfIsComplex`; `Completion.norm_coe` + `norm_embedding_eq` + above.
- **Uses from project**: [`infinitePlace_isComplex`, `complexEmbedding_norm_zeta_eq_one`] — **Visibility**: public — **Lines**: 90-100

### `private theorem zeta_ne_zero` + product-formula `example`s (×2)
- **What**: `ζ ≠ 0`; product formula `∏_w · ∏_v = 1` for `ζ` and for `etaUnit`.
- **How**: `NumberField.prod_abs_eq_one`.
- **Uses from project**: [`zeta_isPrimitiveRoot`, `etaUnit`] — **Visibility**: private / examples — **Lines**: 114-134

### `abbrev CyclotomicThreeInfiniteAdeleRing`, `infinitePrincipalAdele_zeta`, `…_etaUnit` + `example`s
- **What**: infinite adele ring; principal adeles of `ζ`/`etaUnit`; norm formula + dense range.
- **How**: `InfiniteAdeleRing.coe_norm_eq_abs_norm`; `denseRange_algebraMap`.
- **Uses from project**: [`ζ`, `etaUnit`] — **Visibility**: public/examples — **Lines**: 148-163

### `theorem canonicalEmbedding_zetaInt_mem_integerLattice`
- **Type**: `canonicalEmbedding K (algebraMap zetaInt) ∈ integerLattice K` — **How**: exhibit preimage `zetaInt`.
- **Uses from project**: [`zetaInt`] — **Visibility**: public — **Lines**: 177-182

### `abbrev mixedEmbedding_zeta` + geometry `example`s + `theorem polarSpace_nonempty`
- **What**: mixed embedding of `ζ`; convex-body membership; measurability of `fundamentalCone`/`normLeOne`;
  `Nonempty (polarSpace K)`.
- **How**: `convexBodyLT_mem`; `measurableSet_fundamentalCone`/`…normLeOne`; `infer_instance`.
- **Uses from project**: [`ζ`] — **Visibility**: public/examples — **Lines**: 198-217

### `theorem house_zeta`, `house_etaUnit`
- **Types**: `house ζ = 1`; `house etaUnit = 1`.
- **How**: `le_antisymm` via `canonicalEmbedding.norm_le_iff` and `‖φ ζ‖ = 1` at each embedding; `etaUnit` by `simpa`.
- **Uses from project**: [`complexEmbedding_norm_zeta_eq_one`, `etaUnit`, `zetaInt`] — **Visibility**: public — **Lines**: 231-246

### `abbrev CyclotomicThreeAdeleRing`, `principalAdele_zeta`, `…_etaUnit`
- **Types**: full adele ring and principal adeles.
- **Uses from project**: [`ζ`, `etaUnit`] — **Visibility**: public — **Lines**: 261-268

### `theorem principalAdele_zeta_ne_zero`
- **Type**: `principalAdele_zeta ≠ 0` — **How**: `AdeleRing.algebraMap_injective` + `zeta_ne_zero`.
- **Uses from project**: [`zeta_ne_zero`] — **Visibility**: public — **Lines**: 270-272

### `theorem principalAdele_etaUnit_is_unit_everywhere`
- **Type**: `∀ v finite, v (etaUnit) = 1` — a unit has trivial valuation at every finite place.
- **How**: `norm_embedding_eq` + `norm_eq_one_iff_notMem`; `etaUnit·etaUnit⁻¹=1 ∉ maximal ideal`.
- **Uses from project**: [`etaUnit`] — **Visibility**: public — **Lines**: 274-293

### `abbrev cyclotomicThreeDedekindZeta`, `…Residue` + `example`s
- **What**: Dedekind zeta function and its residue; positivity; the class-number-formula residue identity.
- **How**: `dedekindZeta_residue_pos`; `dedekindZeta_residue_def` (involves regulator, classNumber,
  torsionOrder, discr — all computed in earlier files).
- **Uses from project**: [`K`] — **Visibility**: public/examples — **Lines**: 307-323

**File Summary — LocalGlobal.lean**: capstone tying together places, completions, adeles, geometry of
numbers, house, and the analytic class number formula residue. Mostly applications of mathlib's
local-global API specialised to `ζ`/`etaUnit`; the named theorems are reusable, the `example`s are
illustrative checkpoints. No sorry.

---

## Folder-level notes

- **Sorry-free**: confirmed across all 11 files (grep clean). Rank-0 units mean there is **no**
  `isFundamental`/`regulator` Artin-bound blocker (the obstruction present in `CyclotomicFive`/`Eight`/
  `CubeRootThree`); `regulator_eq_one` falls out of an empty determinant.
- **Common usage**: PrimeSplitting uses Common's ResidueHom (`isMaximal_span_gen_sub`,
  `absNorm_span_gen_sub`) and ramification helpers (`not_map_span_natCast_le_pow_succ…`,
  `not_isUnramifiedAt_of_…`), plus `left_eq_prime_of_mul_eq_prime_sq_of_ne_one`,
  `eq_of_le_of_absNorm_eq`. Euclidean uses `abs_intNorm_lt_of_abs_norm_le`,
  `natAbs_lt_of_abs_ratCast_lt`. **No local re-derivation of reduction-mod-p machinery.**
- **Twin of `CubeRootThree`**: same role-structure, different driving relation — `r²+r+1=0`
  (cyclotomic/quadratic) here vs `r³=3` (radical/cubic) there. The cyclotomic model gives degree,
  Galois, ring of integers, units, CM, and the congruence splitting law *for free* via
  `IsCyclotomicExtension.Rat.*`; CubeRootThree must build the analogous facts by hand and remains
  non-Galois with S₃ closure and rank-1 units (hence its blockers).
