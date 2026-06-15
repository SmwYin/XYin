# CyclotomicEight (`ℚ(ζ₈)`) — Declaration Inventory

Field: `ℚ(ζ₈)`, the eighth cyclotomic field, modelled as `K := CyclotomicField 8 ℚ` via
`IsCyclotomicExtension {8} ℚ K`. Degree `φ(8) = 4`, signature `(0,2)` (totally complex, CM),
ring of integers `ℤ[ζ₈]` (monogenic), discriminant `256 = 2⁸`, class number `1`. The Galois
group is `(ℤ/8)ˣ`, the **non-cyclic** Klein four-group `ℤ/2 × ℤ/2` (smallest non-cyclic Galois
group over `ℚ`); every automorphism is an involution. CM field with three quadratic subfields
`ℚ(√2), ℚ(i), ℚ(√−2)`. Unit group `μ₈ × ℤ` (rank 1), fundamental unit `1 + √2`.
This is the **twin of CyclotomicFive** (`ℚ(ζ₅)`, cyclic Galois group); the route map (fromZetaAut
automorphisms, residueHom Kummer–Dedekind, `torsionPowerHom`/`rankOnePowerHom` unit structure)
is shared. **2 sorries** (down from 3): `fundamentalUnitSystem_isFundamental` (Units.lean — `1+√2`
is fundamental, the cyclotomic-unit index `h⁺=1` obstruction) and `normEuclidean` (Euclidean.lean,
geometry-of-numbers covering argument). The former `regulator_eq` sorry is now **closed**: its body
is complete via mathlib's `regOfFamily_eq_det` (as in SqrtTwo/SqrtFive/CyclotomicFive), so it depends
only transitively on `isFundamental`. The regulator value was never the API gap — the genuine
obstruction is certifying `1+√2` as the fundamental unit (cyclotomic-unit / real-subfield theory).

All declarations live in `namespace NumberField.CyclotomicEight` unless noted.
Shared helpers referenced from `XYin/NumberField/FieldExamples/Common.lean`
(`namespace NumberField.FieldExamples`).

---

## Basic.lean

### `abbrev K`
- **Type**: `K : Type := CyclotomicField 8 ℚ`
- **What**: The eighth cyclotomic field over `ℚ`.
- **How**: Direct abbreviation of `CyclotomicField 8 ℚ`.
- **Uses from project**: []
- **Visibility**: public; **Lines**: 32

### `instance IsCyclotomicExtension {8} ℚ K`
- **Type**: `IsCyclotomicExtension {8} ℚ K`
- **What**: Endows `K` with the cyclotomic-extension structure.
- **How**: `CyclotomicField.isCyclotomicExtension 8 ℚ`.
- **Uses from project**: [`K`]
- **Visibility**: public; **Lines**: 35-36

### `abbrev ζ`
- **Type**: `ζ : K := IsCyclotomicExtension.zeta 8 ℚ K`
- **What**: A chosen primitive eighth root of unity.
- **How**: Mathlib's canonical `IsCyclotomicExtension.zeta`.
- **Uses from project**: [`K`]
- **Visibility**: public; **Lines**: 39

### `theorem zeta_isPrimitiveRoot`
- **Type**: `IsPrimitiveRoot ζ 8`
- **What**: `ζ` is a primitive eighth root of unity.
- **How**: `IsCyclotomicExtension.zeta_spec`.
- **Uses from project**: [`ζ`]
- **Visibility**: public; **Lines**: 42-43

### `theorem zeta_pow_eight`
- **Type**: `ζ ^ 8 = 1`
- **How**: `IsPrimitiveRoot.pow_eq_one`.
- **Uses from project**: [`zeta_isPrimitiveRoot`]
- **Visibility**: public; **Lines**: 46-47

### `theorem zeta_pow_four`
- **Type**: `ζ ^ 4 = -1`
- **What**: Vanishing of `Φ₈` at `ζ`: `ζ⁴ = −1`. **Heavily used (every `linear_combination`).**
- **How**: `(zeta_isPrimitiveRoot.pow (8 = 4*2)).eq_neg_one_of_two_right`.
- **Uses from project**: [`zeta_isPrimitiveRoot`]
- **Visibility**: public; **Lines**: 50-51

### `theorem degree_eq_four`
- **Type**: `Module.finrank ℚ K = 4`
- **What**: `[ℚ(ζ₈):ℚ] = φ(8) = 4`.
- **How**: `IsCyclotomicExtension.finrank` + `cyclotomic.irreducible_rat`.
- **Uses from project**: [`K`]
- **Visibility**: public; **Lines**: 54-56

### `abbrev zetaEightPolynomial`
- **Type**: `Polynomial ℚ := X ^ 4 + C 1`
- **What**: The defining polynomial `X⁴ + 1`.
- **Uses from project**: []
- **Visibility**: public; **Lines**: 59

### `theorem cyclotomic_eight_rat` *(private)*
- **Type**: `Polynomial.cyclotomic 8 ℚ = zetaEightPolynomial`
- **What**: `Φ₈ = X⁴ + 1` over `ℚ`.
- **How**: Two `cyclotomic_expand_eq_cyclotomic` steps (2→4→8) from `cyclotomic_two`, then `expand_X`/`ring`.
- **Uses from project**: [`zetaEightPolynomial`]
- **Visibility**: private; **Lines**: 61-72

### `instance Fact (Irreducible zetaEightPolynomial)`
- **Type**: `Fact (Irreducible zetaEightPolynomial)`
- **What**: `X⁴ + 1` is irreducible over `ℚ`.
- **How**: rewrite to `Φ₈` via `cyclotomic_eight_rat`, then `cyclotomic.irreducible_rat`.
- **Uses from project**: [`zetaEightPolynomial`, `cyclotomic_eight_rat`]
- **Visibility**: public; **Lines**: 74-77

### `abbrev KAdjoinRoot`
- **Type**: `Type := AdjoinRoot zetaEightPolynomial`
- **What**: The field presented as `ℚ[X]/(X⁴+1)`.
- **Uses from project**: [`zetaEightPolynomial`]
- **Visibility**: public; **Lines**: 80

### `abbrev zetaEightRoot`
- **Type**: `KAdjoinRoot := AdjoinRoot.root zetaEightPolynomial`
- **What**: The formal root generator in the `AdjoinRoot` model.
- **Uses from project**: [`zetaEightPolynomial`, `KAdjoinRoot`]
- **Visibility**: public; **Lines**: 83

### `theorem zetaEightRoot_pow_four`
- **Type**: `zetaEightRoot ^ 4 = (-1 : KAdjoinRoot)`
- **How**: `AdjoinRoot.eval₂_root` gives `root⁴+1=0`; `calc`/`ring`.
- **Uses from project**: [`zetaEightRoot`, `zetaEightPolynomial`]
- **Visibility**: public; **Lines**: 85-91

### `theorem zetaEightPolynomial_eq_minpoly`
- **Type**: `zetaEightPolynomial = minpoly ℚ ζ`
- **How**: `cyclotomic_eight_rat` + `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible`.
- **Uses from project**: [`zetaEightPolynomial`, `cyclotomic_eight_rat`, `zeta_isPrimitiveRoot`]
- **Visibility**: public; **Lines**: 93-97

### `def zetaMinpolyAdjoinRootPresentation`
- **Type**: `IsAdjoinRoot K (minpoly ℚ ζ)`
- **How**: `IsAdjoinRoot.mkOfAdjoinEqTop` + `adjoin_primitive_root_eq_top`.
- **Uses from project**: [`K`, `ζ`, `zeta_isPrimitiveRoot`]
- **Visibility**: public; **Lines**: 100-103

### `def adjoinRootEquivCyclotomic`
- **Type**: `KAdjoinRoot ≃ₐ[ℚ] K`
- **What**: Equivalence between the `AdjoinRoot` model and `CyclotomicField`.
- **How**: `AdjoinRoot.algEquivOfEq` (poly equality) composed with `adjoinRootAlgEquiv`.
- **Uses from project**: [`KAdjoinRoot`, `K`, `zetaEightPolynomial_eq_minpoly`, `zetaMinpolyAdjoinRootPresentation`]
- **Visibility**: public; **Lines**: 106-109

### `theorem adjoinRootEquivCyclotomic_root`
- **Type**: `adjoinRootEquivCyclotomic zetaEightRoot = ζ`
- **How**: `AdjoinRoot.algEquivOfEq_root` + `simp`.
- **Uses from project**: [`adjoinRootEquivCyclotomic`, `zetaEightRoot`, `ζ`, `zetaMinpolyAdjoinRootPresentation`, `zetaEightPolynomial_eq_minpoly`]
- **Visibility**: public; **Lines**: 111-117

**File Summary — Basic.lean**: 17 decls (5 abbrevs / 2 defs / 9 theorems-instances). Key API (3+): `ζ`, `zeta_isPrimitiveRoot`, `zeta_pow_four`, `zeta_pow_eight`, `K`, `degree_eq_four`, `zetaEightPolynomial`, `adjoinRootEquivCyclotomic`. No sorry, no set_option, no proof >30 lines.

---

## Galois.lean

### `def idAut`
- **Type**: `K ≃ₐ[ℚ] K := AlgEquiv.refl`
- **What**: Identity automorphism.
- **Uses from project**: [`K`]
- **Visibility**: public; **Lines**: 32

### `def sigmaThree` / `def sigmaFive` / `def sigmaSeven`
- **Type**: `K ≃ₐ[ℚ] K` each
- **What**: The three nontrivial automorphisms `ζ ↦ ζ³ / ζ⁵ / ζ⁷` (fixing `ℚ(√−2) / ℚ(i) / ℚ(√2)` resp.; `sigmaSeven` is complex conjugation).
- **How**: `IsCyclotomicExtension.fromZetaAut` of `zeta_isPrimitiveRoot.pow_of_coprime k`.
- **Uses from project**: [`zeta_isPrimitiveRoot`]
- **Visibility**: public; **Lines**: 35-48

### `theorem sigmaThree_apply_zeta` / `sigmaFive_apply_zeta` / `sigmaSeven_apply_zeta`
- **Type**: `sigmaK ζ = ζ ^ k` (k = 3,5,7)
- **How**: `IsCyclotomicExtension.fromZetaAut_spec`.
- **Uses from project**: [`sigmaThree`/`sigmaFive`/`sigmaSeven`, `zeta_isPrimitiveRoot`]
- **Visibility**: public; **Lines**: 51-63

### `theorem isGalois`
- **Type**: `IsGalois ℚ K`
- **How**: `IsCyclotomicExtension.isGalois`.
- **Uses from project**: [`K`]
- **Visibility**: public; **Lines**: 66-67

### `theorem galoisGroupStructure`
- **Type**: `Nonempty ((K ≃ₐ[ℚ] K) ≃* (ZMod 8)ˣ)`
- **What**: Galois group ≅ `(ℤ/8)ˣ` (cyclotomic character).
- **How**: `IsCyclotomicExtension.autEquivPow`.
- **Uses from project**: [`K`]
- **Visibility**: public; **Lines**: 69-71

### `theorem galoisGroup_klein`
- **Type**: `Nonempty ((K ≃ₐ[ℚ] K) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))`
- **What**: The Galois group is the Klein four-group.
- **How**: `autEquivPow` transports the involution property; establishes `Nat.card = 4` (`card_aut_eq_finrank`) and `Monoid.exponent = 2` to land `IsKleinFour` on both sides, then `IsKleinFour.nonempty_mulEquiv`; `decide` on `(ZMod 8)ˣ`.
- **Uses from project**: [`K`, `isGalois`, `degree_eq_four`]
- **Visibility**: public; **Lines**: 74-110; **Notes**: proof >30 lines.

### `theorem aut_sq_eq_one`
- **Type**: `(σ : K ≃ₐ[ℚ] K) → σ * σ = 1`
- **What**: Every automorphism is an involution (key non-cyclic witness).
- **How**: `autEquivPow` injectivity + `decide` that `t*t=1` in `(ZMod 8)ˣ`.
- **Uses from project**: [`K`]
- **Visibility**: public; **Lines**: 112-119

### `theorem galoisGroup_not_isCyclic`
- **Type**: `¬ IsCyclic (K ≃ₐ[ℚ] K)`
- **What**: The Galois group is not cyclic (smallest non-cyclic Galois group over `ℚ`).
- **How**: A generator would have order 4 (`card_aut_eq_finrank`), contradicting `aut_sq_eq_one`.
- **Uses from project**: [`K`, `isGalois`, `degree_eq_four`, `aut_sq_eq_one`]
- **Visibility**: public; **Lines**: 121-130

### `theorem aut_eq`
- **Type**: `σ = idAut ∨ σ = sigmaThree ∨ σ = sigmaFive ∨ σ = sigmaSeven`
- **What**: The four displayed automorphisms exhaust the Galois group.
- **How**: `autToPow_spec` + `decide` on `(ZMod 8)ˣ.val ∈ {1,3,5,7}`; `powerBasis.algHom_ext` to pin maps by their value on `ζ`.
- **Uses from project**: [`K`, `idAut`, `sigmaThree`, `sigmaFive`, `sigmaSeven`, `zeta_isPrimitiveRoot`, `sigma*_apply_zeta`]
- **Visibility**: public; **Lines**: 132-149

**File Summary — Galois.lean**: 13 decls (4 defs / 9 theorems). Key API (3+): `sigmaThree`/`Five`/`Seven` (+ `_apply_zeta`), `isGalois`, `degree_eq_four` (imported), `zeta_isPrimitiveRoot`. No sorry, no set_option. Proofs >30 lines: `galoisGroup_klein`.
Smell: `idAut`/`sigmaThree`/`sigmaFive`/`sigmaSeven` + `aut_eq` are re-implemented privately as `sig3/sig5/sig7`/`autEq'` in PrimeSplitting.lean (duplication across the import barrier — those are needed for the norm-via-conjugates computation but never imported back).

---

## Embeddings.lean

### `theorem isTotallyComplex`
- **Type**: `NumberField.IsTotallyComplex K`
- **How**: `IsCyclotomicExtension.Rat.isTotallyComplex`.
- **Uses from project**: [`K`]; **Visibility**: public; **Lines**: 34-35

### `theorem nrRealPlaces_eq_zero`
- **Type**: `InfinitePlace.nrRealPlaces K = 0`
- **How**: `IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero`.
- **Uses from project**: [`K`]; **Visibility**: public; **Lines**: 37-38

### `theorem nrComplexPlaces_eq_two`
- **Type**: `InfinitePlace.nrComplexPlaces K = 2`
- **How**: `card_add_two_mul_card_eq_rank` + `nrRealPlaces_eq_zero`, `degree_eq_four`, `omega`.
- **Uses from project**: [`K`, `nrRealPlaces_eq_zero`, `degree_eq_four`]; **Visibility**: public; **Lines**: 40-43

### `theorem infinitePlace_card_eq_two`
- **Type**: `Fintype.card (InfinitePlace K) = 2`
- **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces` + the two place counts.
- **Uses from project**: [`K`, `nrRealPlaces_eq_zero`, `nrComplexPlaces_eq_two`]; **Visibility**: public; **Lines**: 57-60

### `theorem infinitePlace_isComplex`
- **Type**: `(v : InfinitePlace K) → IsComplex v`
- **How**: `isTotallyComplex.isComplex`.
- **Uses from project**: [`K`, `isTotallyComplex`]; **Visibility**: public; **Lines**: 62-64

### `theorem exists_complexEmbedding_zeta`
- **Type**: `∃ σ : K →+* ℂ, σ ζ = Complex.exp (2πi/8)`
- **What**: There is a complex embedding sending `ζ` to the standard primitive root.
- **How**: `Complex.isPrimitiveRoot_exp` gives ξ a root of `X⁴+1`; lift via `AdjoinRoot.liftAlgHom ∘ adjoinRootEquivCyclotomic.symm`; `adjoinRootEquivCyclotomic_root`.
- **Uses from project**: [`K`, `ζ`, `zetaEightPolynomial`, `adjoinRootEquivCyclotomic`, `adjoinRootEquivCyclotomic_root`]; **Visibility**: public; **Lines**: 66-83

**File Summary — Embeddings.lean**: 6 theorems. Key API (3+): `isTotallyComplex`, `nrRealPlaces_eq_zero`, `nrComplexPlaces_eq_two`, `infinitePlace_isComplex`. `attribute [-instance] DivisionRing.toRatAlgebra` at top (line 26). No sorry, no set_option, no proof >30 lines.

---

## RingOfIntegers.lean

### `theorem zeta_integral`
- **Type**: `ζ ∈ integralClosure ℤ K`
- **How**: `IsPrimitiveRoot.isIntegral`.
- **Uses from project**: [`ζ`, `K`, `zeta_isPrimitiveRoot`]; **Visibility**: public; **Lines**: 32-33

### `def zetaInt`
- **Type**: `𝓞 K := ⟨ζ, zeta_integral⟩`
- **What**: `ζ` viewed in the ring of integers. **Heavily used across the entire folder.**
- **Uses from project**: [`ζ`, `zeta_integral`]; **Visibility**: public; **Lines**: 36

### `theorem zetaInt_pow_four`
- **Type**: `zetaInt ^ 4 = -1`
- **How**: `Subtype.ext` + `push_cast` + `zeta_pow_four`. **The workhorse of all `linear_combination` proofs in PrimeSplitting/Units.**
- **Uses from project**: [`zetaInt`, `zeta_pow_four`]; **Visibility**: public; **Lines**: 39-40

### `abbrev integralPowerBasis`
- **Type**: `PowerBasis ℤ (𝓞 K) := zeta_isPrimitiveRoot.integralPowerBasis`
- **What**: Mathlib's integral power basis `1, ζ, ζ², ζ³`.
- **Uses from project**: [`zeta_isPrimitiveRoot`]; **Visibility**: public; **Lines**: 43-44

### `theorem integralPowerBasis_gen`
- **Type**: `integralPowerBasis.gen = zeta_isPrimitiveRoot.toInteger`
- **Uses from project**: [`integralPowerBasis`, `zeta_isPrimitiveRoot`]; **Visibility**: public; **Lines**: 47-48

### `theorem integralPowerBasis_dim`
- **Type**: `integralPowerBasis.dim = 4`
- **Uses from project**: [`integralPowerBasis`, `zeta_isPrimitiveRoot`]; **Visibility**: public; **Lines**: 50-51

### `def integralBasisVectors`
- **Type**: `Fin 4 → K := ![1, ζ, ζ², ζ³]`
- **Uses from project**: [`ζ`]; **Visibility**: public; **Lines**: 54

### `theorem span_integralBasisVectors_eq`
- **Type**: `Submodule.span ℤ (range integralBasisVectors) = Subalgebra.toSubmodule (integralClosure ℤ K)`
- **What**: `1, ζ, ζ², ζ³` spans the ring of integers as a `ℤ`-lattice.
- **How**: `le_antisymm`; reverse inclusion via `isIntegralClosure_adjoin_singleton`, `adjoin_singleton_eq_range_aeval`, `modByMonic` reduction (degree <4), `aeval_eq_sum_range'`.
- **Uses from project**: [`integralBasisVectors`, `zeta_integral`, `zeta_isPrimitiveRoot`, `zeta_pow_four`]; **Visibility**: public; **Lines**: 58-95; **Notes**: proof >30 lines.

### `def concreteIntegralBasis`
- **Type**: `Basis (Fin 4) ℤ (𝓞 K)`
- **What**: `1, ζ, ζ², ζ³` packaged as a genuine basis. **Used in Discriminant + PrimeSplitting (finrank computations).**
- **How**: `integralPowerBasis.basis.reindex (finCongr integralPowerBasis_dim)`.
- **Uses from project**: [`integralPowerBasis`, `integralPowerBasis_dim`]; **Visibility**: public; **Lines**: 98-99

### `theorem concreteIntegralBasis_apply`
- **Type**: `algebraMap (𝓞 K) K (concreteIntegralBasis i) = integralBasisVectors i`
- **How**: `fin_cases` + `simp`.
- **Uses from project**: [`concreteIntegralBasis`, `integralBasisVectors`]; **Visibility**: public; **Lines**: 102-105

### `theorem span_integralBasisVectors_eq_integralBasis`
- **Type**: `span ℤ (range integralBasisVectors) = span ℤ (range (NumberField.integralBasis K))`
- **What**: The displayed basis spans the same lattice as mathlib's integral basis (equality of lattices, not a reindexing).
- **How**: `span_integralBasisVectors_eq` + `mem_span_integralBasis` both directions.
- **Uses from project**: [`integralBasisVectors`, `span_integralBasisVectors_eq`]; **Visibility**: public; **Lines**: 107-121

### `abbrev concreteRingOfIntegers`
- **Type**: `Subalgebra ℤ K := Algebra.adjoin ℤ {ζ}`
- **Uses from project**: [`ζ`]; **Visibility**: public; **Lines**: 124

### `theorem isIntegralClosure_adjoin_zeta`
- **Type**: `IsIntegralClosure (Algebra.adjoin ℤ {ζ}) ℤ K`
- **How**: `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`.
- **Uses from project**: [`ζ`, `zeta_isPrimitiveRoot`]; **Visibility**: public; **Lines**: 127-129

### `theorem integralPowerBasis_adjoin_gen_eq_top`
- **Type**: `Algebra.adjoin ℤ {integralPowerBasis.gen} = ⊤`
- **How**: `PowerBasis.adjoin_gen_eq_top`.
- **Uses from project**: [`integralPowerBasis`]; **Visibility**: public; **Lines**: 131-134

### `theorem ringOfIntegers_eq`
- **Type**: `integralClosure ℤ K = concreteRingOfIntegers`
- **What**: `𝓞 K = ℤ[ζ]` (monogenicity).
- **How**: `le_antisymm` via `isIntegralClosure_adjoin_zeta` + `adjoin_le`.
- **Uses from project**: [`concreteRingOfIntegers`, `zeta_integral`, `isIntegralClosure_adjoin_zeta`]; **Visibility**: public; **Lines**: 136-142

**File Summary — RingOfIntegers.lean**: 15 decls (4 defs/abbrevs + `integralBasisVectors`/`concreteIntegralBasis` defs / 11 theorems-abbrevs). Key API (3+): `zetaInt`, `zetaInt_pow_four`, `concreteIntegralBasis`, `integralPowerBasis`, `zeta_integral`. No sorry, no set_option. Proofs >30 lines: `span_integralBasisVectors_eq`.

---

## Discriminant.lean

### `theorem numberField_discr_eq`
- **Type**: `NumberField.discr K = (256 : ℤ)`
- **What**: `disc(ℚ(ζ₈)) = 256 = 2⁸`. **Used in ClassGroup (Minkowski bound), PrimeSplitting (different/ramification), LocalGlobal.**
- **How**: rewrite `{8}` to `{2^3}`, `IsCyclotomicExtension.Rat.discr_prime_pow 2 3` + `totient`/`norm_num`.
- **Uses from project**: [`K`]; **Visibility**: public; **Lines**: 33-39

### `theorem concreteIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ concreteIntegralBasis = 256`
- **How**: `NumberField.discr_eq_discr` + `numberField_discr_eq`.
- **Uses from project**: [`concreteIntegralBasis`, `numberField_discr_eq`]; **Visibility**: public; **Lines**: 42-45

### `theorem integralBasis_discr`
- **Type**: `Algebra.discr ℚ (NumberField.integralBasis K) = (256 : ℚ)`
- **How**: `NumberField.coe_discr` + `numberField_discr_eq`.
- **Uses from project**: [`numberField_discr_eq`]; **Visibility**: public; **Lines**: 47-52

**File Summary — Discriminant.lean**: 3 theorems. Key API: `numberField_discr_eq`. No sorry/set_option/long proofs.

---

## Subfields.lean

(Imports Discriminant; imported by PrimeSplitting. This is how the three quadratic subfields are
exhibited: not as `Subfield`/`IntermediateField` objects but via explicit generators of the three
real/imaginary quadratic algebras inside `K`, each pinned by a defining quadratic relation. These
match the three index-2 subgroups of the Klein-four Galois group.)

### `theorem sqrt_two_sq`
- **Type**: `(ζ + ζ ^ 7) ^ 2 = 2`
- **What**: `√2 = ζ + ζ⁻¹` lives in `ℚ(ζ₈)` (generator of `ℚ(√2)`, the maximal real subfield).
- **How**: `linear_combination (…) * zeta_pow_four`.
- **Uses from project**: [`ζ`, `zeta_pow_four`]; **Visibility**: public; **Lines**: 28-29

### `theorem i_sq`
- **Type**: `(ζ ^ 2) ^ 2 = -1`
- **What**: `i = ζ²` (generator of `ℚ(i)`).
- **How**: `linear_combination zeta_pow_four`.
- **Uses from project**: [`ζ`, `zeta_pow_four`]; **Visibility**: public; **Lines**: 31-33

### `theorem sqrt_neg_two_sq`
- **Type**: `(ζ - ζ ^ 7) ^ 2 = -2`
- **What**: `√−2 = ζ − ζ⁻¹` (generator of `ℚ(√−2)`); together with the above exhibits all three quadratic subfields `ℚ(√2), ℚ(i), ℚ(√−2)`.
- **How**: `linear_combination (…) * zeta_pow_four`.
- **Uses from project**: [`ζ`, `zeta_pow_four`]; **Visibility**: public; **Lines**: 35-39

**File Summary — Subfields.lean**: 3 theorems, all public. No sorry/set_option/long proofs. No `Subfield`/`IntermediateField` lattice objects are built — the subfields are witnessed only by their generators' minimal relations.

---

## PrimeSplitting.lean (1045 lines)

Imports Discriminant, **Common**, Subfields, and `Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization`.

### `theorem gen_eq_zetaInt` *(private)*
- **Type**: `zeta_isPrimitiveRoot.integralPowerBasis.gen = zetaInt`
- **How**: `integralPowerBasis_gen` + `rfl`.
- **Uses from project**: [`zeta_isPrimitiveRoot`, `zetaInt`]; **Visibility**: private; **Lines**: 34-35
- **Note**: re-declared identically in ClassGroup.lean.

### `def sig3` / `sig5` / `sig7` *(private)*
- **Type**: `K ≃ₐ[ℚ] K` each
- **What**: Private copies of `sigmaThree/Five/Seven`, needed locally for the norm-via-conjugates machinery (`prod_aut_apply`).
- **How**: `fromZetaAut` of `pow_of_coprime`.
- **Uses from project**: [`zeta_isPrimitiveRoot`]; **Visibility**: private; **Lines**: 38-48
- **Note**: duplicates the public `Galois.sigma*` (Galois.lean is not imported here).

### `theorem sig3_zeta` / `sig5_zeta` / `sig7_zeta` *(private)*
- **Type**: `sigK ζ = ζ ^ k`
- **How**: `fromZetaAut_spec`.
- **Uses from project**: [`sig3`/`sig5`/`sig7`, `zeta_isPrimitiveRoot`]; **Visibility**: private; **Lines**: 50-60

### `theorem autEq'` *(private)*
- **Type**: `σ = 1 ∨ σ = sig3 ∨ σ = sig5 ∨ σ = sig7`
- **What**: Private duplicate of `Galois.aut_eq` (using `1` for identity).
- **How**: `autToPow_spec` + `decide` + `powerBasis.algHom_ext`.
- **Uses from project**: [`sig3/5/7`, `sig*_zeta`, `zeta_isPrimitiveRoot`]; **Visibility**: private; **Lines**: 62-77

### `theorem prod_aut_apply` *(private)*
- **Type**: `∏ σ, σ x = x * sig3 x * sig5 x * sig7 x`
- **What**: The product over the four Galois conjugates.
- **How**: distinctness via `pow_inj`, `Finset.univ = {1,sig3,sig5,sig7}`, `prod_insert`/`prod_pair`/`ring`.
- **Uses from project**: [`autEq'`, `sig*_zeta`, `zeta_isPrimitiveRoot`]; **Visibility**: private; **Lines**: 79-105; **Notes**: >30 lines.

### `theorem intNorm_eq` *(private)*
- **Type**: `(x : 𝓞 K) → (conjugate product = (n:K)) → Algebra.norm ℤ x = n`
- **How**: `norm_eq_prod_automorphisms`, `prod_aut_apply`, `Algebra.coe_norm_int`.
- **Uses from project**: [`prod_aut_apply`, `sig3/5/7`]; **Visibility**: private; **Lines**: 107-123

### `def normForm`
- **Type**: `{R}[CommRing R] (a b c d : R) → R := (a²−c²+2bd)² + (2ac−b²+d²)²`
- **What**: Explicit norm form of `a+bζ+cζ²+dζ³`. **Used by Units.lean (unit equation).**
- **Uses from project**: []; **Visibility**: public; **Lines**: 126-127

### `def zetaCoords` *(private)*
- **Type**: `(a b c d : ℚ) → K := a + bζ + cζ² + dζ³`
- **Uses from project**: [`ζ`]; **Visibility**: private; **Lines**: 129-130

### `theorem sig3_zetaCoords` / `sig5_zetaCoords` / `sig7_zetaCoords` *(private)*
- **Type**: explicit images of `zetaCoords a b c d` under each automorphism.
- **How**: `map_*`, `sig*_zeta`, reduce powers ζ⁵…ζ²¹ via `linear_combination ... zeta_pow_four/eight`, `ring_nf`.
- **Uses from project**: [`zetaCoords`, `sig*_zeta`, `ζ`, `zeta_pow_four`, `zeta_pow_eight`]; **Visibility**: private; **Lines**: 132-184

### `theorem zetaCoords_mul_sig5` / `sig3_zetaCoords_mul_sig7` *(private)*
- **Type**: product identities collapsing to `(a²−c²+2bd) ± (2ac−b²+d²)ζ²`.
- **How**: `ring_nf` + `zeta_pow_four`, `ζ⁶ = −ζ²`.
- **Uses from project**: [`zetaCoords`, `ζ`, `zeta_pow_four`]; **Visibility**: private; **Lines**: 186-202

### `theorem norm_eq_normForm`
- **Type**: `Algebra.norm ℚ (a•1+b•ζ+c•ζ²+d•ζ³) = normForm a b c d`
- **How**: rewrite to `zetaCoords`, `norm_eq_prod_automorphisms`, the four conjugate formulas, then the two product identities.
- **Uses from project**: [`normForm`, `zetaCoords`, `sig*_zetaCoords`, `zetaCoords_mul_sig5`, `sig3_zetaCoords_mul_sig7`, `ζ`, `zeta_pow_four`]; **Visibility**: public; **Lines**: 204-231; **Notes**: >30 lines.

### `theorem intNorm_eq_normForm`
- **Type**: `Algebra.norm ℤ (a•1+b•zetaInt+c•zetaInt²+d•zetaInt³) = normForm a b c d`
- **How**: `Algebra.coe_norm_int` + `norm_eq_normForm`.
- **Uses from project**: [`zetaInt`, `normForm`, `norm_eq_normForm`]; **Visibility**: public; **Lines**: 233-248

### `theorem isUnit_iff_normForm`
- **Type**: `IsUnit (a•1+...+d•zetaInt³) ↔ (normForm a b c d).natAbs = 1`
- **What**: Unit equation for `ℤ[ζ₈]`.
- **How**: `NumberField.isUnit_iff_norm`, `RingOfIntegers.coe_norm`, `intNorm_eq_normForm`.
- **Uses from project**: [`zetaInt`, `intNorm_eq_normForm`, `normForm`]; **Visibility**: public; **Lines**: 250-263

### `theorem cyclotomic_eight_int` *(private)*
- **Type**: `Polynomial.cyclotomic 8 ℤ = X ^ 4 + 1`
- **How**: same 2→4→8 expand argument as `cyclotomic_eight_rat`, over `ℤ`.
- **Uses from project**: []; **Visibility**: private; **Lines**: 265-274
- **Note**: duplicate-structure of `Basic.cyclotomic_eight_rat`.

### `theorem minpoly_gen_eq` *(private)*
- **Type**: `minpoly ℤ (integralPowerBasis.gen) = X ^ 4 + 1`
- **How**: `isIntegrallyClosed_dvd` + degree/monic arguments, `eq_one_of_monic_natDegree_zero`.
- **Uses from project**: [`zeta_isPrimitiveRoot`, `gen_eq_zetaInt`, `zetaInt_pow_four`]; **Visibility**: private; **Lines**: 276-299; **Note**: duplicated in ClassGroup.lean.

### `theorem isMaximal_span_pair` *(private)*
- **Type**: `(p : ℕ)[Fact p.Prime](r : ℤ)((r:ZMod p)⁴ = −1) → (Ideal.span {p, zetaInt − r}).IsMaximal`
- **What**: The prime `(p, ζ−r)` is maximal whenever `r` is a fourth root of `−1 mod p`.
- **How**: `← gen_eq_zetaInt` then **`Common.isMaximal_span_gen_sub`** (the generic Kummer–Dedekind ResidueHom from Common), with `minpoly_gen_eq`.
- **Uses from project**: [`gen_eq_zetaInt`, `minpoly_gen_eq`, `zeta_isPrimitiveRoot`, Common: `isMaximal_span_gen_sub`]; **Visibility**: private; **Lines**: 302-308
- **Note**: **NOW USES Common** — the bespoke `residueHom`/`ker_residueHom`/`residueHom_surjective` stack previously here has been removed in favour of the generic helper.

### `theorem absNorm_span_pair` *(private)*
- **Type**: `Ideal.absNorm (Ideal.span {p, zetaInt − r}) = p`
- **How**: `← gen_eq_zetaInt` then **`Common.absNorm_span_gen_sub`**, with `minpoly_gen_eq`.
- **Uses from project**: [`gen_eq_zetaInt`, `minpoly_gen_eq`, `zeta_isPrimitiveRoot`, Common: `absNorm_span_gen_sub`]; **Visibility**: private; **Lines**: 310-315
- **Note**: **NOW USES Common.**

### `theorem span_two_eq`
- **Type**: `Ideal.span {(2:𝓞 K)} = Ideal.span {1 - zetaInt} ^ 4`
- **What**: `(2) = (1−ζ)⁴`, total ramification at 2 (e=4). **Used pervasively (LiesOver, ramification, classNumber, different).**
- **How**: `span_singleton_pow` + `span_singleton_eq_span_singleton` with explicit unit + `linear_combination ... zetaInt_pow_four`.
- **Uses from project**: [`zetaInt`, `zetaInt_pow_four`]; **Visibility**: public; **Lines**: 317-326

### `theorem span_one_sub_zetaInt_eq_pair` *(private)*
- **Type**: `Ideal.span {1 - zetaInt} = Ideal.span {(2:ℕ), zetaInt - 1}`
- **Uses from project**: [`zetaInt`, `span_two_eq`]; **Visibility**: private; **Lines**: 328-341; **Note**: duplicated in ClassGroup.lean.

### `theorem isPrime_span_one_sub_zeta`
- **Type**: `(Ideal.span {1 - zetaInt}).IsPrime`
- **What**: `(1−ζ)` is prime (unique prime over 2). **Used in ClassGroup, LocalGlobal, different.**
- **How**: `span_one_sub_zetaInt_eq_pair` + `(isMaximal_span_pair 2 1).isPrime`.
- **Uses from project**: [`span_one_sub_zetaInt_eq_pair`, `isMaximal_span_pair`]; **Visibility**: public; **Lines**: 343-346

### `theorem absNorm_span_one_sub_zeta`
- **Type**: `Ideal.absNorm (Ideal.span {1 - zetaInt}) = 2`
- **How**: `span_one_sub_zetaInt_eq_pair` + `absNorm_span_pair 2 1`.
- **Uses from project**: [`span_one_sub_zetaInt_eq_pair`, `absNorm_span_pair`]; **Visibility**: public; **Lines**: 348-351

### `theorem liesOver_span_one_sub_zeta`
- **Type**: `(Ideal.span {1 - zetaInt}).LiesOver (Ideal.span {(2:ℤ)})`
- **How**: `liesOver_span_iff` + `span_two_eq` + `pow_le_self`.
- **Uses from project**: [`isPrime_span_one_sub_zeta`, `span_two_eq`]; **Visibility**: public; **Lines**: 353-361

### `theorem inertiaDeg_span_one_sub_zeta`
- **Type**: `(Ideal.span {(2:ℤ)}).inertiaDeg (Ideal.span {1 - zetaInt}) = 1`
- **How**: `absNorm_eq_pow_inertiaDeg'` + `absNorm_span_one_sub_zeta` + `Nat.Prime.pow_eq_iff`.
- **Uses from project**: [`liesOver_span_one_sub_zeta`, `absNorm_span_one_sub_zeta`]; **Visibility**: public; **Lines**: 363-371

### `theorem ramificationIdx_span_one_sub_zeta`
- **Type**: `(Ideal.span {(2:ℤ)}).ramificationIdx (Ideal.span {1 - zetaInt}) = 4`
- **How**: `ramificationIdx_spec`: `≤` via `span_two_eq`; `>` ruled out by `absNorm` (32 ∤ 16, using finrank=4 via `concreteIntegralBasis`).
- **Uses from project**: [`span_two_eq`, `absNorm_span_one_sub_zeta`, `concreteIntegralBasis`]; **Visibility**: public; **Lines**: 373-396; **Notes**: >30 lines.

### `theorem span_pair_three_left` / `span_pair_three_right` *(private)*
- **Type**: `Ideal.span {3, zetaInt²+zetaInt+2} = Ideal.span {zetaInt²+zetaInt−1}` (and right twin).
- **How**: `mem_span_singleton`, explicit witnesses, `linear_combination ... zetaInt_pow_four`.
- **Uses from project**: [`zetaInt`, `zetaInt_pow_four`]; **Visibility**: private; **Lines**: 398-426

### `theorem span_three_eq`
- **Type**: `Ideal.span {(3:𝓞 K)} = (3, ζ²+ζ+2)*(3, ζ²+2ζ+2)`
- **What**: 3 splits into two degree-2 primes (`Φ₈ ≡ (X²+X+2)(X²+2X+2) mod 3`).
- **How**: rewrite to principal singletons + `span_singleton_mul` + explicit unit.
- **Uses from project**: [`span_pair_three_left/right`, `zetaInt_pow_four`]; **Visibility**: public; **Lines**: 428-440

### `theorem absNorm_ne_three` *(private)*
- **Type**: `(P : Ideal (𝓞 K)) → Ideal.absNorm P ≠ 3`
- **What**: No prime with residue field `𝔽₃` (X⁴+1 has no root mod 3).
- **How**: from card 3 build `ZMod.ringEquivOfPrime`, transport `zetaInt⁴ = −1`, `decide`.
- **Uses from project**: [`zetaInt`, `zetaInt_pow_four`]; **Visibility**: private; **Lines**: 442-457

### `theorem isPrime_of_absNorm_nine` *(private)*
- **Type**: `Ideal.absNorm (span {g}) = 9 → (span {g}).IsPrime`
- **How**: take maximal `M ≥`; `absNorm M ∣ 9`, exclude 1 and 3 (`absNorm_ne_three`), so 9; cofactor norm 1.
- **Uses from project**: [`absNorm_ne_three`]; **Visibility**: private; **Lines**: 459-483; **Note**: could use `Common.eq_of_le_of_absNorm_eq`/`eq_prime_of_dvd_prime_sq...`.

### `theorem absNorm_span_g1` / `absNorm_span_g2` *(private)*
- **Type**: `Ideal.absNorm (span {zetaInt²±zetaInt−1}) = 9`
- **How**: `intNorm_eq` with conjugate formulas (`sig3/5/7_zeta`), `linear_combination ... zeta_pow_four`.
- **Uses from project**: [`intNorm_eq`, `sig3/5/7_zeta`, `zetaInt`, `zeta_pow_four`, `ζ`]; **Visibility**: private; **Lines**: 485-527

### `theorem isPrime_primesAboveThree`
- **Type**: both primes above 3 are prime.
- **Uses from project**: [`span_pair_three_left/right`, `isPrime_of_absNorm_nine`, `absNorm_span_g1/g2`]; **Visibility**: public; **Lines**: 529-537

### `theorem absNorm_primeAboveThreeLeft` / `absNorm_primeAboveThreeRight`
- **Type**: each prime above 3 has norm 9.
- **Uses from project**: [`span_pair_three_left/right`, `absNorm_span_g1/g2`]; **Visibility**: public; **Lines**: 539-549

### `theorem seventeen_mem_span_two/eight/nine/fifteen` *(private)*
- **Type**: `(17:𝓞 K) ∈ Ideal.span {zetaInt^k − 2}` for k=1,3,7,5.
- **How**: `mem_span_singleton` + explicit cofactor + big `linear_combination ... zetaInt_pow_four`.
- **Uses from project**: [`zetaInt`, `zetaInt_pow_four`]; **Visibility**: private; **Lines**: 551-577

### `theorem span_pair_seventeen_two/eight/nine/fifteen` *(private)*
- **Type**: `Ideal.span {17, zetaInt − r} = Ideal.span {zetaInt^k − 2}`
- **Uses from project**: [`zetaInt`, `seventeen_mem_span_*`, `zetaInt_pow_four`]; **Visibility**: private; **Lines**: 579-620

### `theorem span_seventeen_eq`
- **Type**: `Ideal.span {(17:𝓞 K)} = ∏ (17, zetaInt − r)` for r∈{2,8,9,15}
- **What**: 17 splits completely (17 ≡ 1 mod 8; roots of X⁴+1 mod 17 are the order-8 elements).
- **How**: rewrite each pair to a principal singleton, multiply, explicit product = 17.
- **Uses from project**: [`span_pair_seventeen_*`, `zetaInt_pow_four`]; **Visibility**: public; **Lines**: 622-635

### `theorem isPrime_primeAboveSeventeen`
- **Type**: `(r ∈ {2,8,9,15}) → (Ideal.span {17, zetaInt − r}).IsPrime`
- **How**: `decide` on `(r:ZMod 17)⁴ = −1` + `(isMaximal_span_pair 17).isPrime`.
- **Uses from project**: [`isMaximal_span_pair`]; **Visibility**: public; **Lines**: 637-644

### `theorem fintype_card_le_prime_sq_of_pow_prime_sq_fixed` *(private)*
- **Type**: `{F}[CommRing F][IsDomain F][Fintype F] (hp : p.Prime) (∀ x, x^(p²)=x) → Fintype.card F ≤ p²`
- **What**: Generic: a finite domain where `x^(p²)=x` has ≤ p² elements.
- **How**: roots of `X^(p²) − X` ⊇ univ; `card_roots'`.
- **Uses from project**: []; **Visibility**: private; **Lines**: 646-673; **Note**: **field-independent → candidate for Common/mathlib.**

### `theorem not_isPrime_span_two_natCast` *(private)*
- **Type**: `¬ (Ideal.span {((2:ℕ):𝓞 K)}).IsPrime`
- **How**: `span_two_eq` + `mem_of_pow_mem` + `absNorm` contradiction.
- **Uses from project**: [`span_two_eq`, `absNorm_span_one_sub_zeta`]; **Visibility**: private; **Lines**: 675-687

### `theorem quotient_pow_prime_sq_eq_self_of_isPrime_span_natCast_ne_two` *(private)*
- **Type**: `(p ≠ 2 prime, span {p} prime) → ∀ x : 𝓞 K ⧸ span{p}, x^(p²) = x`
- **How**: residue field has char p, `p² ≡ 1 (mod 8)`, frobenius² fixes ζ; `aeval_algHom_apply`.
- **Uses from project**: [`zeta_isPrimitiveRoot`, `gen_eq_zetaInt`, `zetaInt`, `zetaInt_pow_four`]; **Visibility**: private; **Lines**: 689-737; **Notes**: >30 lines.

### `theorem not_isPrime_span_natCast_of_ne_two` *(private)*
- **Type**: `(p prime, p ≠ 2) → ¬ (Ideal.span {p}).IsPrime`
- **How**: residue field would have p⁴ elements but `x^(p²)=x` bounds it by p² < p⁴.
- **Uses from project**: [`concreteIntegralBasis`, `quotient_pow_prime_sq_eq_self_...`, `fintype_card_le_prime_sq_of_pow_prime_sq_fixed`]; **Visibility**: private; **Lines**: 739-767

### `theorem no_inert_prime`
- **Type**: `(p : ℕ)(hp : p.Prime) → ¬ (Ideal.span {(p:𝓞 K)}).IsPrime`
- **What**: **No rational prime is inert** (hallmark of non-cyclic abelian extensions: every residue degree ≤ exponent 2 < 4).
- **How**: case split p=2/≠2 to the two private lemmas.
- **Uses from project**: [`not_isPrime_span_two_natCast`, `not_isPrime_span_natCast_of_ne_two`]; **Visibility**: public; **Lines**: 769-778

### `theorem orderOf_mk0_eq_eight_of_pow_four_eq_neg_one` *(private)*
- **Type**: `[Fact p.Prime] (p≠2) (s≠0) (s⁴ = −1) → orderOf (Units.mk0 s) = 8`
- **How**: order ∣ 8, not ∣ 4 (since s⁴ = −1 ≠ 1), so = 8.
- **Uses from project**: []; **Visibility**: private; **Lines**: 780-810; **Note**: **field-independent → candidate for Common.**

### `theorem unit_val_pow_four_eq_neg_one_of_orderOf_eq_eight` *(private)*
- **Type**: `[Fact p.Prime] (orderOf u = 8) → (u:ZMod p)⁴ = −1`
- **How**: `u⁴` squares to 1 but ≠ 1, so = −1.
- **Uses from project**: []; **Visibility**: private; **Lines**: 812-833; **Note**: **field-independent → candidate for Common.**

### `theorem one_mod_eight_of_splits_completely` *(private)*
- **Type**: `(p ≠ 2 prime) → (∃ P prime, ⊇span{p}, norm p) → p % 8 = 1`
- **How**: residue field 𝔽_p, `Units.mk0 s` has order 8, so `8 ∣ p−1`.
- **Uses from project**: [`zetaInt`, `zetaInt_pow_four`, `orderOf_mk0_eq_eight_of_pow_four_eq_neg_one`]; **Visibility**: private; **Lines**: 835-865

### `theorem splits_completely_of_one_mod_eight` *(private)*
- **Type**: `(p prime) → p % 8 = 1 → ∃ P prime ⊇ span{p}, norm p`
- **How**: cyclic `(ℤ/p)ˣ` generator `g`, `g^m` has order 8, build prime `(p, ζ−r)` via `isMaximal_span_pair`.
- **Uses from project**: [`zetaInt`, `unit_val_pow_four_eq_neg_one_of_orderOf_eq_eight`, `isMaximal_span_pair`, `absNorm_span_pair`]; **Visibility**: private; **Lines**: 867-898; **Notes**: >30 lines.

### `theorem splits_completely_iff`
- **Type**: `(p prime, p≠2) → (∃ P prime ⊇span{p}, norm p) ↔ p % 8 = 1`
- **What**: **Splitting law**: p splits completely iff `p ≡ 1 (mod 8)`.
- **Uses from project**: [`one_mod_eight_of_splits_completely`, `splits_completely_of_one_mod_eight`]; **Visibility**: public; **Lines**: 900-906

### `theorem ramified_iff_eq_two`
- **Type**: `(p prime) → (∃ P prime, span{p} ≤ P²) ↔ p = 2`
- **What**: **Ramification law**: only 2 ramifies (p | disc 256).
- **How**: different ideal route: `dvd_differentIdeal_iff`, `absNorm_differentIdeal`, `numberField_discr_eq`, plus `Common.not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ` and `Common.not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow`.
- **Uses from project**: [`concreteIntegralBasis`, `numberField_discr_eq`, `isPrime_span_one_sub_zeta`, `span_two_eq`, `zetaInt`, Common: `not_isUnramifiedAt_...`, `not_map_span_natCast_le_pow_succ_...`]; **Visibility**: public; **Lines**: 908-956; **Notes**: >30 lines.

### `abbrev zetaEightPolynomialMod`
- **Type**: `(p : ℕ) → (ZMod p)[X] := X^4 + C 1`
- **Uses from project**: []; **Visibility**: public; **Lines**: 973-974

### `theorem zetaEightPolynomialMod_eq_cyclotomic` *(private)*
- **Type**: `zetaEightPolynomialMod p = cyclotomic 8 (ZMod p)`
- **How**: map `cyclotomic_eight_int` via `Int.castRingHom`, `map_cyclotomic_int`.
- **Uses from project**: [`zetaEightPolynomialMod`, `cyclotomic_eight_int`]; **Visibility**: private; **Lines**: 976-980

### `theorem absNorm_differentIdeal_eq_twoHundredFiftySix`
- **Type**: `Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = 256`
- **How**: `absNorm_differentIdeal` + `numberField_discr_eq`.
- **Uses from project**: [`numberField_discr_eq`]; **Visibility**: public; **Lines**: 996-999

### `theorem prime_dvd_differentIdeal_iff_eq_span_one_sub_zeta`
- **Type**: `(P prime, P≠⊥) → (P ∣ differentIdeal ℤ (𝓞 K) ↔ P = Ideal.span {1 - zetaInt})`
- **What**: The different is supported only at `(1−ζ)`.
- **How**: forward via `absNorm` dvd 2⁸ + `mem_of_pow_mem` + maximality; reverse via `pow_sub_one_dvd_differentIdeal`.
- **Uses from project**: [`zetaInt`, `absNorm_differentIdeal_eq_twoHundredFiftySix`, `span_two_eq`, `span_one_sub_zetaInt_eq_pair`, `isMaximal_span_pair`]; **Visibility**: public; **Lines**: 1001-1042; **Notes**: >30 lines.

**File Summary — PrimeSplitting.lean**: ~45 decls (defs: `sig3/5/7`, `normForm`, `zetaCoords`; 2 abbrevs; many private theorems). Key API (3+): `zetaInt`, `zetaInt_pow_four`, `intNorm_eq`, `sig*_zeta`, `span_two_eq`, `isMaximal_span_pair`/`absNorm_span_pair` (now thin wrappers over **Common** ResidueHom), `numberField_discr_eq`, `concreteIntegralBasis`, Common helpers. Headline public results: `span_two_eq`, `isPrime/absNorm/inertiaDeg/ramificationIdx_span_one_sub_zeta`, `span_three_eq`, `span_seventeen_eq`, `no_inert_prime`, `splits_completely_iff`, `ramified_iff_eq_two`, `norm_eq_normForm`, `isUnit_iff_normForm`, `prime_dvd_differentIdeal_iff...`. Several proofs >30 lines (see notes). No sorry, no set_option. **DUPLICATION NOTE: this file now uses Common's ResidueHom helpers (`isMaximal_span_gen_sub`, `absNorm_span_gen_sub`) and no longer carries the bespoke `residueHom`/`ker_residueHom`/`residueHom_surjective` stack** — that migration was NOT done in ClassGroup.lean (see below).

---

## ClassGroup.lean

Imports PrimeSplitting. Two sections: fractional ideals, then class group.

### `abbrev zetaFractionalIdeal`
- **Type**: `FractionalIdeal (𝓞 K)⁰ K := spanSingleton _ ζ`
- **Uses from project**: [`ζ`]; **Visibility**: public; **Lines**: 31-32

### `abbrev ramifiedPrimeFractionalIdeal`
- **Type**: `FractionalIdeal (𝓞 K)⁰ K := (Ideal.span {1 - zetaInt} : ...)`
- **Uses from project**: [`zetaInt`]; **Visibility**: public; **Lines**: 34-35

### `theorem zeta_mem_fractionalIdeal`
- **Type**: `ζ ∈ zetaFractionalIdeal`
- **How**: `mem_spanSingleton_self`.
- **Uses from project**: [`zetaFractionalIdeal`, `ζ`]; **Visibility**: public; **Lines**: 37-39

### `theorem zetaFractionalIdeal_absNorm`
- **Type**: `FractionalIdeal.absNorm zetaFractionalIdeal = |Algebra.norm ℚ ζ|`
- **How**: `absNorm_span_singleton`.
- **Uses from project**: [`zetaFractionalIdeal`, `ζ`]; **Visibility**: public; **Lines**: 41-43

### `theorem ramifiedPrimeFractionalIdeal_ne_zero`
- **Type**: `ramifiedPrimeFractionalIdeal ≠ 0`
- **How**: `coeIdeal_ne_zero` + `span_singleton_eq_bot` ⇒ ζ = 1 ⇒ order 1 vs 8 contradiction.
- **Uses from project**: [`ramifiedPrimeFractionalIdeal`, `zetaInt`, `ζ`, `zeta_isPrimitiveRoot`]; **Visibility**: public; **Lines**: 45-56

### `theorem gen_eq_zetaInt` *(private)*
- **Type**: `zeta_isPrimitiveRoot.integralPowerBasis.gen = zetaInt`
- **Uses from project**: [`zeta_isPrimitiveRoot`, `zetaInt`]; **Visibility**: private; **Lines**: 72-74; **Note**: verbatim copy of PrimeSplitting's `gen_eq_zetaInt`.

### `theorem minpoly_gen_eq` *(private)*
- **Type**: `minpoly ℤ (integralPowerBasis.gen) = X ^ 4 + 1`
- **Uses from project**: [`zeta_isPrimitiveRoot`, `gen_eq_zetaInt`, `zetaInt_pow_four`]; **Visibility**: private; **Lines**: 76-99; **Note**: verbatim copy of PrimeSplitting's `minpoly_gen_eq`.

### `def residueHom` *(private)*
- **Type**: `(p : ℕ)(r : ℤ)(hr : (r:ZMod p)⁴ = −1) → 𝓞 K →ₐ[ℤ] ZMod p`
- **What**: Reduction `ζ ↦ r` mod `p`.
- **How**: `integralPowerBasis.lift` with `minpoly_gen_eq`.
- **Uses from project**: [`zeta_isPrimitiveRoot`, `minpoly_gen_eq`]; **Visibility**: private; **Lines**: 101-104
- **Note**: **bespoke ResidueHom — NOT migrated to Common.** Duplicates `Common.genResidueHom`.

### `theorem residueHom_zetaInt` *(private)*
- **Type**: `residueHom p r hr zetaInt = (r : ZMod p)`
- **Uses from project**: [`residueHom`, `gen_eq_zetaInt`, `minpoly_gen_eq`, `zeta_isPrimitiveRoot`, `zetaInt`]; **Visibility**: private; **Lines**: 106-110

### `theorem ker_residueHom` *(private)*
- **Type**: `RingHom.ker (residueHom p r hr).toRingHom = Ideal.span {p, zetaInt − r}`
- **How**: division `q(ζ)−q(r) ∈ (ζ−r)` via `sub_dvd_eval_sub`; `intCast_zmod_eq_zero_iff_dvd`; both inclusions.
- **Uses from project**: [`residueHom`, `residueHom_zetaInt`, `zeta_isPrimitiveRoot`, `gen_eq_zetaInt`, `zetaInt`]; **Visibility**: private; **Lines**: 112-159; **Notes**: >30 lines; duplicates `Common.ker_genResidueHom`.

### `theorem residueHom_surjective` *(private)*
- **Type**: `Function.Surjective (residueHom p r hr)`
- **Uses from project**: [`residueHom`]; **Visibility**: private; **Lines**: 161-165

### `theorem isMaximal_span_pair` *(private)*
- **Type**: `[Fact p.Prime] → (Ideal.span {p, zetaInt − r}).IsMaximal`
- **How**: `← ker_residueHom` + `ker_isMaximal_of_surjective`.
- **Uses from project**: [`ker_residueHom`, `residueHom_surjective`]; **Visibility**: private; **Lines**: 167-171

### `theorem span_one_sub_zetaInt_eq_pair` *(private)*
- **Type**: `Ideal.span {1 - zetaInt} = Ideal.span {(2:ℕ), zetaInt - 1}`
- **Uses from project**: [`zetaInt`, `span_two_eq`]; **Visibility**: private; **Lines**: 173-186; **Note**: verbatim copy of PrimeSplitting's.

### `theorem eq_span_one_sub_of_two_mem` *(private)*
- **Type**: `(P prime, 2 ∈ P) → P = Ideal.span {1 - zetaInt}`
- **How**: `(1−ζ)⁴ ∈ P`, `mem_of_pow_mem`, maximality (local `isMaximal_span_pair`).
- **Uses from project**: [`zetaInt`, `span_two_eq`, `span_one_sub_zetaInt_eq_pair`, `isMaximal_span_pair`]; **Visibility**: private; **Lines**: 190-201

### `theorem classNumber_eq_one`
- **Type**: `NumberField.classNumber K = 1`
- **What**: **Class number 1.**
- **How**: `classNumber_eq_one_iff` + `isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`; Minkowski bound `(4/π)²·4!/4⁴·√256 ≈ 2.4 < 3` via `Nat.floor_lt`, `pi_gt_d2`, `nlinarith`; only p=2 remains, principal `(1−ζ)`.
- **Uses from project**: [`nrComplexPlaces_eq_two`, `degree_eq_four`, `numberField_discr_eq`, `eq_span_one_sub_of_two_mem`, `zetaInt`]; **Visibility**: public; **Lines**: 203-240; **Notes**: >30 lines.

### `theorem isPrincipalIdealRing`
- **Type**: `IsPrincipalIdealRing (𝓞 K)`
- **How**: `← classNumber_eq_one_iff` + `classNumber_eq_one`.
- **Uses from project**: [`classNumber_eq_one`]; **Visibility**: public; **Lines**: 242-245

### `theorem uniqueFactorizationMonoid`
- **Type**: `UniqueFactorizationMonoid (𝓞 K)`
- **How**: PIR ⇒ UFM (`infer_instance`).
- **Uses from project**: [`isPrincipalIdealRing`]; **Visibility**: public; **Lines**: 247-250

### `theorem classGroupStructure`
- **Type**: `Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1))`
- **How**: card 1 ⇒ `Unique` ⇒ `MulEquiv.ofUnique`.
- **Uses from project**: [`classNumber_eq_one`]; **Visibility**: public; **Lines**: 252-258

### `abbrev unitIdealRepresentative`
- **Type**: `(Ideal (𝓞 K))⁰ := ⟨⊤, _⟩`
- **Uses from project**: []; **Visibility**: public; **Lines**: 260-261

### `theorem classGroupRepresentative`
- **Type**: `(C : ClassGroup (𝓞 K)) → C = ClassGroup.mk0 unitIdealRepresentative`
- **How**: `Subsingleton.elim`.
- **Uses from project**: [`classNumber_eq_one`, `unitIdealRepresentative`]; **Visibility**: public; **Lines**: 263-269

**File Summary — ClassGroup.lean**: ~17 decls. Key API (3+): `classNumber_eq_one`, `zetaInt`, plus the re-declared private residue-hom stack. Headline: `classNumber_eq_one`, `isPrincipalIdealRing`, `uniqueFactorizationMonoid`, `classGroupStructure`. Proofs >30 lines: `classNumber_eq_one`, `ker_residueHom`. No sorry, no set_option. **Major smell (STILL PRESENT): lines 72-186 carry a full bespoke private residueHom stack** (`gen_eq_zetaInt`, `minpoly_gen_eq`, `residueHom`, `residueHom_zetaInt`, `ker_residueHom`, `residueHom_surjective`, `isMaximal_span_pair`, `span_one_sub_zetaInt_eq_pair`). This is the SAME machinery `Common` now provides (`genResidueHom`, `ker_genResidueHom`, `isMaximal_span_gen_sub`, `absNorm_span_gen_sub`) and which **PrimeSplitting.lean has already migrated to use**. ClassGroup needs only `isMaximal_span_pair 2 1`, so it could be replaced by a one-line call to `Common.isMaximal_span_gen_sub` exactly as PrimeSplitting does. ~115 lines removable.

---

## Units.lean

Imports ClassGroup; `open NumberField.FieldExamples` (for Common's `torsionPowerHom`/`rankOnePowerHom`).

### `def torsionGenerator`
- **Type**: `(𝓞 K)ˣ` with `val = zetaInt`, `inv = zetaInt^7`
- **What**: A torsion generator (ζ). **Used in unit-group structure.**
- **How**: `linear_combination (zetaInt⁴−1) * zetaInt_pow_four` for val_inv/inv_val.
- **Uses from project**: [`zetaInt`, `zetaInt_pow_four`]; **Visibility**: public; **Lines**: 35-39

### `def torsionUnits`
- **Type**: `Set (𝓞 K)ˣ := {u | ∃ k : Fin 8, u = torsionGenerator ^ k.val}`
- **Uses from project**: [`torsionGenerator`]; **Visibility**: public; **Lines**: 42

### `theorem torsionOrder_eq'` *(private)*
- **Type**: `NumberField.Units.torsionOrder K = 8`
- **How**: `IsCyclotomicExtension.Rat.torsionOrder_eq`.
- **Uses from project**: []; **Visibility**: private; **Lines**: 46-48

### `theorem torsionUnits_eq`
- **Type**: `{u | IsOfFinOrder u} = torsionUnits`
- **What**: Torsion subgroup = μ₈ = `{ζ^k}` (note `−1 = ζ⁴` already a power of ζ, unlike ℚ(ζ₅)).
- **How**: `rootsOfUnity_eq_torsion`, `torsionOrder_eq'`, `eq_pow_of_pow_eq_one`.
- **Uses from project**: [`torsionGenerator`, `torsionUnits`, `torsionOrder_eq'`, `zeta_isPrimitiveRoot`, `ζ`, `zeta_pow_eight`]; **Visibility**: public; **Lines**: 50-72

### `theorem torsionOrder_eq_eight`
- **Type**: `NumberField.Units.torsionOrder K = 8`
- **Uses from project**: [`torsionOrder_eq'`]; **Visibility**: public; **Lines**: 74-76

### `theorem unitRank_eq_one`
- **Type**: `NumberField.Units.rank K = 1`
- **How**: signature `(0,2)` ⇒ rank = r₁+r₂−1 = 1 (`card_eq_nrRealPlaces_add_nrComplexPlaces`).
- **Uses from project**: [`nrRealPlaces_eq_zero`, `nrComplexPlaces_eq_two`]; **Visibility**: public; **Lines**: 78-82

### `def fundamentalUnit`
- **Type**: `(𝓞 K)ˣ` with `val = 1 + zetaInt + zetaInt^7`, `inv = zetaInt + zetaInt^7 − 1`
- **What**: `1 + √2`, the fundamental unit (the fundamental unit of the real subfield ℚ(√2)). **Used in LocalGlobal.**
- **How**: `linear_combination (…) * zetaInt_pow_four`.
- **Uses from project**: [`zetaInt`, `zetaInt_pow_four`]; **Visibility**: public; **Lines**: 86-94

### `def fundamentalUnitSystem`
- **Type**: `Fin (rank K) → (𝓞 K)ˣ := fun _ => fundamentalUnit`
- **Uses from project**: [`fundamentalUnit`]; **Visibility**: public; **Lines**: 97-98

### `theorem exists_eq_torsion_mul_fundSystem_zpow` *(private)*
- **Type**: `(i₀)(u) → ∃ ζ' ∈ torsion, ∃ n, u = ζ' * fundSystem K i₀ ^ n`
- **How**: rank 1 ⇒ subsingleton index; `closure_fundSystem_sup_torsion_eq_top`, `mem_sup`, `mem_closure_singleton`.
- **Uses from project**: [`unitRank_eq_one`]; **Visibility**: private; **Lines**: 102-124

### `theorem fundSystem_zpow_mem_torsion` *(private)*
- **Type**: `fundSystem K i₀ ^ n ∈ torsion → n = 0`
- **How**: image in `basisModTorsion` repr is a basis vector.
- **Uses from project**: []; **Visibility**: private; **Lines**: 126-140

### `theorem eq_torsionGenerator_pow_of_mem_torsion` *(private)*
- **Type**: `ζ' ∈ torsion → ∃ k : Fin 8, ζ' = torsionGenerator ^ k.val`
- **How**: `torsionUnits_eq`.
- **Uses from project**: [`torsionGenerator`, `torsionUnits_eq`]; **Visibility**: private; **Lines**: 142-148

### `theorem fundamentalUnitSystem_isFundamental`  ⚠️ SORRY
- **Type**: `Subgroup.closure (range fundamentalUnitSystem) ⊔ torsion K = ⊤`
- **What**: `{1+√2}` together with μ₈ generates all units.
- **Uses from project**: [`fundamentalUnitSystem`]; **Visibility**: public; **Lines**: 152-154; **Notes**: **SORRY** (isFundamental — blocked, Artin-type unit-index bound; need that `1+√2` is a fundamental unit, i.e. generates the free part — no mathlib API computes the cyclotomic-unit index / fundamental-unit-of-real-subfield).

### `theorem unit_eq_torsion_mul_fundamentalUnit_zpow`
- **Type**: `(u) → ∃ ζ' ∈ torsion, ∃ n, u = ζ' * fundamentalUnit ^ n`
- **What**: every unit is `ζ^j (1+√2)ⁿ`.
- **How**: `fundamentalUnitSystem_isFundamental` + `mem_sup`/`mem_closure_singleton`.
- **Uses from project**: [`fundamentalUnitSystem`, `fundamentalUnit`, `fundamentalUnitSystem_isFundamental`, `unitRank_eq_one`]; **Visibility**: public; **Lines**: 156-172; **Note**: depends on the sorry'd lemma.

### `theorem unitGroupStructure_bijective` *(private)*
- **Type**: `(i₀)(η = fundSystem K i₀)(htg8)(htg_tor) → Bijective ((torsionPowerHom 8 torsionGenerator htg8).coprod (rankOnePowerHom η))`
- **How**: injectivity via `fundSystem_zpow_mem_torsion` + `pow_eq_one_iff_dvd`; surjectivity via `exists_eq_torsion_mul_fundSystem_zpow` + `eq_torsionGenerator_pow_of_mem_torsion`.
- **Uses from project**: [`torsionGenerator`, `zetaInt`, `ζ`, `zeta_isPrimitiveRoot`, `fundSystem_zpow_mem_torsion`, `exists_eq_torsion_mul_fundSystem_zpow`, `eq_torsionGenerator_pow_of_mem_torsion`, Common: `torsionPowerHom`, `rankOnePowerHom`]; **Visibility**: private; **Lines**: 174-217; **Notes**: >30 lines.

### `theorem unitGroupStructure`
- **Type**: `Nonempty ((𝓞 K)ˣ ≃* (Multiplicative (ZMod 8) × Multiplicative (Fin 1 → ℤ)))`
- **What**: **Unit group ≅ μ₈ × ℤ.** (Crucially proved **independently of the sorry** via `fundSystem`/`closure_fundSystem_sup_torsion_eq_top`, NOT via `fundamentalUnit`.)
- **How**: `MulEquiv.ofBijective` of the coprod hom via `unitGroupStructure_bijective`.
- **Uses from project**: [`torsionGenerator`, `unitRank_eq_one`, `zeta_pow_eight`, `unitGroupStructure_bijective`, Common: `torsionPowerHom`, `rankOnePowerHom`]; **Visibility**: public; **Lines**: 219-238

### `theorem regulator_eq`  ◑ body proved, depends on the `isFundamental` sorry
- **Type**: `NumberField.Units.regulator K = 2 * Real.log (1 + Real.sqrt 2)`
- **What**: **Regulator = 2·log(1+√2) ≈ 1.7627** (complex place weight 2, `|1+ζ+ζ⁷| = 1+√2`).
- **Uses from project**: [`fundamentalUnitSystem_isFundamental`, `unitRank_eq_one`]; **Visibility**: public; **Lines**: 242-310; **Notes**: proof body now **complete** via mathlib's `regOfFamily_div_regulator` → `regOfFamily_eq_det` → `Matrix.det_eq_elem_of_subsingleton` (same route as SqrtTwo/SqrtFive). It is no longer its own sorry, but it *calls* `fundamentalUnitSystem_isFundamental`, so holds only modulo that. The regulator value was never an API gap.

(The trailing `Regulator` section is an empty namespace re-open — no declarations.)

**File Summary — Units.lean**: ~16 decls (4 defs / 12 theorems). Key API (3+): `torsionGenerator`, `fundamentalUnit`, `unitRank_eq_one`, `zetaInt`, `regOfFamily_eq_det`, Common `torsionPowerHom`/`rankOnePowerHom`. Headline: `torsionOrder_eq_eight`, `unitRank_eq_one`, `unitGroupStructure` (sorry-free), `regulator_eq` (body complete, downstream of the sorry), `fundamentalUnitSystem_isFundamental`. **1 genuine sorry** (`fundamentalUnitSystem_isFundamental`); `unit_eq_torsion_mul_fundamentalUnit_zpow` and `regulator_eq` depend on it. Proofs >30 lines: `unitGroupStructure_bijective`, `regulator_eq`. No set_option.

---

## Euclidean.lean

Imports Units.

### `theorem normEuclidean`  ⚠️ SORRY
- **Type**: `(a b : 𝓞 K)(hb : b ≠ 0) → ∃ q r, a = b*q+r ∧ (norm ℤ r).natAbs < (norm ℤ b).natAbs`
- **What**: `ℚ(ζ₈)` is norm-Euclidean.
- **Uses from project**: []; **Visibility**: public; **Lines**: 32-35; **Notes**: **SORRY** (needs a geometry-of-numbers covering argument: every point of `K` is within norm-`<1` of a lattice point of `ℤ[ζ₈]`; no mathlib API for the covering radius of the cyclotomic lattice).

**File Summary — Euclidean.lean**: 1 theorem, public, **1 sorry**. No set_option.

---

## CMField.lean

Imports Embeddings (special-topic; not on the main import chain into Units).

### `theorem isCMField`
- **Type**: `NumberField.IsCMField K`
- **What**: `ℚ(ζ₈)` is a CM field.
- **How**: `IsCyclotomicExtension.Rat.isCMField` with witness `⟨8, …⟩`.
- **Uses from project**: [`K`]; **Visibility**: public; **Lines**: 26-27

### `theorem cmField_isTotallyComplex`
- **Type**: `NumberField.IsTotallyComplex K`
- **How**: re-export of `isTotallyComplex`.
- **Uses from project**: [`isTotallyComplex`]; **Visibility**: public; **Lines**: 29-30

### `theorem cmField_quadratic_over_maximalRealSubfield`
- **Type**: `Algebra.IsQuadraticExtension (NumberField.maximalRealSubfield K) K`
- **What**: `K` is quadratic over its maximal real subfield `ℚ(√2)` (defining property of a CM field).
- **How**: from `isCMField` instance, `infer_instance`.
- **Uses from project**: [`isCMField`]; **Visibility**: public; **Lines**: 32-35

### `theorem cmField_unitsRank_eq_maximalRealSubfield`
- **Type**: `Units.rank (NumberField.maximalRealSubfield K) = Units.rank K`
- **What**: unit rank equal to that of the real subfield (the Dirichlet/CM unit-index statement; both are 1).
- **How**: `IsCMField.units_rank_eq_units_rank`.
- **Uses from project**: [`isCMField`]; **Visibility**: public; **Lines**: 37-41

**File Summary — CMField.lean**: 4 theorems, all public. Headline: `isCMField`, `cmField_quadratic_over_maximalRealSubfield`, `cmField_unitsRank_eq_maximalRealSubfield`. No sorry/set_option/long proofs. CM structure formalised via mathlib's `NumberField.IsCMField` and `NumberField.maximalRealSubfield`.

---

## LocalGlobal.lean

Imports Euclidean (hence the whole chain). Many small named theorems plus ~12 `example`s exercising adele/zeta/canonical-embedding API.

### `def heightOneTwo`
- **Type**: `HeightOneSpectrum (𝓞 K)` with `asIdeal = span {1 - zetaInt}`
- **What**: The finite place over 2 (totally ramified prime `(1−ζ)`).
- **Uses from project**: [`zetaInt`, `isPrime_span_one_sub_zeta`, `absNorm_span_one_sub_zeta`]; **Visibility**: public; **Lines**: 35-43

### `def heightOneThreeLeft` / `heightOneThreeRight`
- **Type**: `HeightOneSpectrum (𝓞 K)` for the two primes over 3.
- **Uses from project**: [`zetaInt`, `isPrime_primesAboveThree`]; **Visibility**: public; **Lines**: 46-67

### `abbrev vTwo`
- **Type**: `NumberField.FinitePlace K := FinitePlace.mk heightOneTwo`
- **Uses from project**: [`heightOneTwo`]; **Visibility**: public; **Lines**: 69-70

### (two unnamed `example`s) ramification/inertia of `heightOneTwo` — Lines 72-78
- **Uses from project**: [`heightOneTwo`, `ramificationIdx_span_one_sub_zeta`, `inertiaDeg_span_one_sub_zeta`]

### `theorem vThreeLeft_inertiaDeg` / `vThreeRight_inertiaDeg`
- **Type**: `(span {(3:ℤ)}).inertiaDeg heightOneThree*.asIdeal = 2`
- **How**: `liesOver_span_iff` + `absNorm_eq_pow_inertiaDeg'` + `absNorm_primeAboveThree*` + `Nat.pow_right_injective`.
- **Uses from project**: [`heightOneThreeLeft/Right`, `absNorm_primeAboveThreeLeft/Right`, `zetaInt`]; **Visibility**: public; **Lines**: 80-112

### `abbrev CompletionAtTwo`
- **Type**: `heightOneTwo.adicCompletion K`
- **Uses from project**: [`heightOneTwo`]; **Visibility**: public; **Lines**: 127-128

### `abbrev InfiniteCompletion`
- **Type**: `(v : InfinitePlace K) → Type := v.Completion`
- **Uses from project**: []; **Visibility**: public; **Lines**: 142-143

### `theorem complexEmbedding_norm_zeta_eq_one` *(private)*
- **Type**: `(φ : K →+* ℂ) → ‖φ ζ‖ = 1`
- **How**: `Complex.norm_eq_one_of_pow_eq_one` (φζ⁸ = 1).
- **Uses from project**: [`ζ`, `zeta_isPrimitiveRoot`]; **Visibility**: private; **Lines**: 145-147

### (unnamed `example`) InfiniteCompletion ≃+* ℂ — Lines 149-152
- **Uses from project**: [`InfiniteCompletion`, `infinitePlace_isComplex`]

### `theorem infiniteCompletion_zeta_norm`
- **Type**: `‖algebraMap K (InfiniteCompletion v) ζ‖ = 1`
- **How**: `Completion.norm_coe`, `norm_embedding_eq`, `complexEmbedding_norm_zeta_eq_one`.
- **Uses from project**: [`InfiniteCompletion`, `ζ`, `complexEmbedding_norm_zeta_eq_one`]; **Visibility**: public; **Lines**: 154-159

### `theorem zeta_ne_zero` *(private)*
- **Type**: `ζ ≠ 0`
- **How**: ζ⁸ = 1 contradicts 0.
- **Uses from project**: [`ζ`, `zeta_isPrimitiveRoot`]; **Visibility**: private; **Lines**: 173-177

### (two unnamed `example`s) product formula for ζ and fundamentalUnit — Lines 179-192
- **Uses from project**: [`ζ`, `zeta_ne_zero`, `fundamentalUnit`]

### `abbrev CyclotomicEightInfiniteAdeleRing`, `infinitePrincipalAdele_zeta`, `infinitePrincipalAdele_fundamentalUnit`
- **Type**: infinite adele ring + two principal adeles.
- **Uses from project**: [`ζ`, `fundamentalUnit`]; **Visibility**: public; **Lines**: 206-213
- (plus two unnamed `example`s: norm = |norm ℚ ζ|, denseRange — Lines 215-221)

### `theorem canonicalEmbedding_zetaInt_mem_integerLattice`
- **Type**: `canonicalEmbedding K (algebraMap (𝓞 K) K zetaInt) ∈ integerLattice K`
- **Uses from project**: [`zetaInt`]; **Visibility**: public; **Lines**: 235-240

### `abbrev mixedEmbedding_zeta`
- **Type**: `mixedEmbedding.mixedSpace K := mixedEmbedding K ζ`
- **Uses from project**: [`ζ`]; **Visibility**: public; **Lines**: 256-257
- (plus unnamed `example`s: convexBodyLT/fundamentalCone/normLeOne — Lines 259-271)

### `theorem polarSpace_nonempty`
- **Type**: `Nonempty (mixedEmbedding.polarSpace K)`
- **Uses from project**: []; **Visibility**: public; **Lines**: 273-275

### `theorem house_zeta`
- **Type**: `NumberField.house ζ = 1`
- **How**: `le_antisymm` via `canonicalEmbedding.norm_le_iff` + `complexEmbedding_norm_zeta_eq_one`.
- **Uses from project**: [`ζ`, `complexEmbedding_norm_zeta_eq_one`]; **Visibility**: public; **Lines**: 289-300
- (plus unnamed `example`: house of fundamentalUnit > 0 — Lines 302-308)

### `abbrev CyclotomicEightAdeleRing`, `principalAdele_zeta`, `principalAdele_fundamentalUnit`
- **Type**: adele ring + two principal adeles.
- **Uses from project**: [`ζ`, `fundamentalUnit`]; **Visibility**: public; **Lines**: 323-330

### `theorem principalAdele_zeta_ne_zero`
- **Type**: `principalAdele_zeta ≠ 0`
- **How**: `AdeleRing.algebraMap_injective` + `zeta_ne_zero`.
- **Uses from project**: [`principalAdele_zeta`, `zeta_ne_zero`]; **Visibility**: public; **Lines**: 332-334

### `theorem principalAdele_fundamentalUnit_is_unit_everywhere`
- **Type**: `∀ v : FinitePlace K, v (algebraMap (𝓞 K) K fundamentalUnit) = 1`
- **How**: `norm_eq_one_iff_notMem`; a unit can't lie in a maximal ideal.
- **Uses from project**: [`fundamentalUnit`]; **Visibility**: public; **Lines**: 336-356

### `abbrev cyclotomicEightDedekindZeta`, `cyclotomicEightDedekindZetaResidue`
- **Type**: Dedekind zeta function + residue.
- **Uses from project**: []; **Visibility**: public; **Lines**: 370-374
- (plus unnamed `example`s: residue > 0, and the class-number-formula identity `dedekindZeta_residue_def` linking regulator/classNumber/torsionOrder/discr — Lines 376-386)

**File Summary — LocalGlobal.lean**: ~25 named decls + ~12 `example`s. Key API (3+): `zetaInt`, `ζ`, `fundamentalUnit`, `complexEmbedding_norm_zeta_eq_one`, the height-one-spectrum places. Headline: place definitions (`heightOneTwo/ThreeLeft/ThreeRight`), `vThree*_inertiaDeg`, `house_zeta`, `infiniteCompletion_zeta_norm`, class-number-formula `example`. No sorry, no set_option, no proof >30 lines.

---

# Global notes / cross-cutting smells

1. **Residue-hom stack: partial migration.** PrimeSplitting.lean **now uses Common's** generic Kummer–Dedekind ResidueHom (`isMaximal_span_gen_sub`, `absNorm_span_gen_sub`) and has dropped its own `residueHom`/`ker_residueHom`/`residueHom_surjective`. **ClassGroup.lean was NOT migrated** — it still carries the full bespoke private stack (`gen_eq_zetaInt`, `minpoly_gen_eq`, `residueHom`, `residueHom_zetaInt`, `ker_residueHom`, `residueHom_surjective`, `isMaximal_span_pair`, `span_one_sub_zetaInt_eq_pair`, lines 72-186, ~115 lines). It needs only `isMaximal_span_pair 2 1`; replace with one call to `Common.isMaximal_span_gen_sub` (as PrimeSplitting does). This is the single largest cleanup available.
2. **Galois automorphisms duplicated.** `sigmaThree/Five/Seven` + `aut_eq` (public, Galois.lean) are re-implemented privately as `sig3/sig5/sig7` + `autEq'` in PrimeSplitting.lean (Galois.lean is not imported there; the conjugates are needed for the norm-form computation).
3. **Cyclotomic-polynomial computation duplicated.** `cyclotomic_eight_rat` (Basic, over ℚ) vs `cyclotomic_eight_int` (PrimeSplitting, over ℤ) — identical 2→4→8 expand structure; could be one parametric lemma over a commutative ring.
4. **Generic finite-field/order lemmas** (`fintype_card_le_prime_sq_of_pow_prime_sq_fixed`, `orderOf_mk0_eq_eight_of_pow_four_eq_neg_one`, `unit_val_pow_four_eq_neg_one_of_orderOf_eq_eight`) are field-independent and belong in Common/mathlib.
5. `isPrime_of_absNorm_nine` re-derives reasoning already packaged in `Common.eq_of_le_of_absNorm_eq` / `eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq`.
6. **2 genuine sorries** (down from 3): `Units.fundamentalUnitSystem_isFundamental` and `Euclidean.normEuclidean`.
   - `fundamentalUnitSystem_isFundamental` — certify `1+√2` fundamental. The obstruction is the cyclotomic-unit index `[𝓞ˣ : C] = h⁺ = 1`, where `h⁺` is the class number of the maximal real subfield `K⁺ = ℚ(ζ+ζ⁻¹) = ℚ(√2)` and `C` is the subgroup of cyclotomic units; `h⁺(ℚ(√2)) = 1` makes `1+√2` fundamental. Mathlib has **no** `cyclotomicUnit` / index API; the totally-complex field offers no real embedding for a SqrtFive-style window-reduction. **This is the one sorry worth answering with new reusable API** (a `cyclotomicUnit` library would close it for every cyclotomic field at once).
   - `normEuclidean` — geometry-of-numbers covering bound; **primarily intrinsic mathematical difficulty**, not an API request.
   - `Units.regulator_eq`'s body is now complete via mathlib's `regOfFamily_eq_det` (the regulator value was never an API gap) but depends transitively on `isFundamental`. `unitGroupStructure` remains sorry-free via `fundSystem`.
