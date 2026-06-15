# CyclotomicFive declaration inventory

Folder: `XYin/NumberField/FieldExamples/CyclotomicFive/`.
Field `K = ℚ(ζ₅) = CyclotomicField 5 ℚ`, modelled via `IsCyclotomicExtension {5} ℚ K` with
generator `ζ = IsCyclotomicExtension.zeta 5 ℚ K`. Degree `φ(5) = 4`, signature `(0,2)` (totally
complex), ring of integers `ℤ[ζ]` (monogenic), discriminant `125 = 5³`, class number `1`, unit
group `μ₁₀ × ℤ` (Dirichlet rank `1`, fundamental unit `1 + ζ`). CM field: complex conjugation is
`σ₄ : ζ ↦ ζ⁴`, real subfield `ℚ(√5)` realised via the quadratic Gauss sum `1 + 2ζ + 2ζ⁴` (whose
square is `5`). Direct port/twin of `CyclotomicEight` (ζ₈) — same route map (`fromZetaAut`,
`autEquivPow`, `torsionPowerHom`/`rankOnePowerHom`, Common `genResidueHom` Kummer–Dedekind). Two
extra special-topic files `CMField.lean`, `QuadraticSubfield.lean`. **2 sorries** (down from 3):
`fundamentalUnitSystem_isFundamental` (Units.lean — `1+ζ` is fundamental, the cyclotomic-unit index
`h⁺=1` obstruction) and `normEuclidean` (Euclidean.lean, covering argument). The former
`regulator_eq` sorry is now **closed**: its proof body is complete (via mathlib's `regOfFamily_eq_det`,
exactly as in SqrtTwo/SqrtFive), so the *only* remaining unit-side blocker is `isFundamental`, on
which `regulator_eq` still depends transitively. The "regulator value" was never the API gap; the
genuine obstruction is the cyclotomic-unit theory needed to certify `1+ζ` as fundamental.

Namespace `NumberField.CyclotomicFive` throughout. Shared helpers come from
`NumberField.FieldExamples` (`Common.lean`): `eq_of_le_of_absNorm_eq`, `torsionPowerHom`,
`rankOnePowerHom`, `not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ`,
`not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow`, and the generic Kummer–Dedekind
`ResidueHom` section (`genResidueHom`, `isMaximal_span_gen_sub`, `absNorm_span_gen_sub`).

Import DAG (core): `Basic → Galois → Embeddings → RingOfIntegers → Discriminant →
PrimeSplitting → ClassGroup → Units → Euclidean → LocalGlobal`; off-spine specials
`CMField` (← Embeddings), `QuadraticSubfield` (← Galois).

---

## Basic.lean

### `abbrev K`
- **Type**: `Type`
- **What**: `CyclotomicField 5 ℚ`, the field `ℚ(ζ₅)`.
- **How**: definitional alias.
- **Uses from project**: []
- **Visibility**: public — **Lines**: 32

### `instance : IsCyclotomicExtension {5} ℚ K`
- **Type**: instance
- **What**: cyclotomic-extension structure on `K`.
- **How**: `CyclotomicField.isCyclotomicExtension 5 ℚ`.
- **Uses from project**: []
- **Visibility**: instance — **Lines**: 35–36

### `abbrev ζ`
- **Type**: `K`
- **What**: chosen primitive fifth root of unity.
- **How**: `IsCyclotomicExtension.zeta 5 ℚ K`.
- **Uses from project**: []
- **Visibility**: public — **Lines**: 39

### `theorem zeta_isPrimitiveRoot`
- **Type**: `IsPrimitiveRoot ζ 5`
- **What**: `ζ` is a primitive 5th root.
- **How**: `IsCyclotomicExtension.zeta_spec`.
- **Uses from project**: [ζ]
- **Visibility**: public — **Lines**: 42–43

### `theorem zeta_pow_five`
- **Type**: `ζ ^ 5 = 1`
- **What**: order-5 relation.
- **How**: `zeta_isPrimitiveRoot.pow_eq_one`.
- **Uses from project**: [zeta_isPrimitiveRoot]
- **Visibility**: public — **Lines**: 46–47

### `theorem zeta_sum_eq_zero`
- **Type**: `1 + ζ + ζ² + ζ³ + ζ⁴ = 0`
- **What**: cyclotomic relation `Φ₅(ζ) = 0`.
- **How**: `geom_sum_eq_zero` + `Finset.sum_range_succ` unfold + `linear_combination`.
- **Uses from project**: [zeta_isPrimitiveRoot]
- **Visibility**: public — **Lines**: 51–54

### `theorem degree_eq_four`
- **Type**: `Module.finrank ℚ K = 4`
- **What**: `[K:ℚ] = φ(5) = 4`.
- **How**: `IsCyclotomicExtension.finrank` with `cyclotomic.irreducible_rat`.
- **Uses from project**: []
- **Visibility**: public — **Lines**: 57–59

### `abbrev zetaFivePolynomial`
- **Type**: `ℚ[X]`
- **What**: `X⁴ + X³ + X² + X + 1 = Φ₅`.
- **How**: literal.
- **Uses from project**: []
- **Visibility**: public — **Lines**: 65–66

### `instance : Fact (Irreducible zetaFivePolynomial)`
- **Type**: instance
- **What**: `Φ₅` irreducible over ℚ.
- **How**: rewrite to `cyclotomic 5 ℚ` via `cyclotomic_prime`, then `cyclotomic.irreducible_rat`.
- **Uses from project**: [zetaFivePolynomial]
- **Visibility**: instance — **Lines**: 68–80

### `abbrev KAdjoinRoot`
- **Type**: `Type` = `AdjoinRoot zetaFivePolynomial`
- **What**: `AdjoinRoot Φ₅` presentation of the field.
- **Uses from project**: [zetaFivePolynomial]
- **Visibility**: public — **Lines**: 83

### `abbrev zetaFiveRoot`
- **Type**: `KAdjoinRoot`
- **What**: formal root `AdjoinRoot.root Φ₅`.
- **Uses from project**: [zetaFivePolynomial]
- **Visibility**: public — **Lines**: 86

### `theorem zetaFiveRoot_relation`
- **Type**: `1 + r + r² + r³ + r⁴ = 0` in `KAdjoinRoot`
- **What**: cyclotomic relation in `AdjoinRoot` model.
- **How**: `AdjoinRoot.eval₂_root` + `ring`.
- **Uses from project**: [zetaFiveRoot]
- **Visibility**: public — **Lines**: 89–99

### `theorem zetaFivePolynomial_eq_minpoly`
- **Type**: `zetaFivePolynomial = minpoly ℚ ζ`
- **What**: `Φ₅` is the minimal polynomial of `ζ`.
- **How**: `minpoly_eq_cyclotomic_of_irreducible`.
- **Uses from project**: [ζ]
- **Visibility**: public — **Lines**: 102–114

### `def zetaMinpolyAdjoinRootPresentation`
- **Type**: `IsAdjoinRoot K (minpoly ℚ ζ)`
- **What**: `K` is `AdjoinRoot (minpoly ℚ ζ)`.
- **How**: `IsAdjoinRoot.mkOfAdjoinEqTop` + `adjoin_primitive_root_eq_top`.
- **Uses from project**: [zeta_isPrimitiveRoot]
- **Visibility**: public — **Lines**: 117–120

### `def adjoinRootEquivCyclotomic`
- **Type**: `KAdjoinRoot ≃ₐ[ℚ] K`
- **What**: `AdjoinRoot Φ₅ ≅ ℚ(ζ₅)` as ℚ-algebras.
- **How**: `AdjoinRoot.algEquivOfEq` (Φ₅ = minpoly) ∘ `adjoinRootAlgEquiv`.
- **Uses from project**: [zetaFivePolynomial_eq_minpoly, zetaMinpolyAdjoinRootPresentation]
- **Visibility**: public — **Lines**: 126–129

### `theorem adjoinRootEquivCyclotomic_root`
- **Type**: `adjoinRootEquivCyclotomic zetaFiveRoot = ζ`
- **What**: transport of the formal root.
- **How**: `AdjoinRoot.algEquivOfEq_root` + simp.
- **Uses from project**: [adjoinRootEquivCyclotomic]
- **Visibility**: public — **Lines**: 132–138

**File Summary**: Field setup. Two equivalent presentations (`IsCyclotomicExtension` and
`AdjoinRoot Φ₅`) with the explicit isomorphism used downstream for complex embeddings; degree 4,
`Φ₅ = minpoly ℚ ζ`. Sorry-free.

---

## Galois.lean

### `def idAut`
- **Type**: `K ≃ₐ[ℚ] K` — identity (`AlgEquiv.refl`). **Lines**: 32. Public. Uses: [].

### `def sigmaTwo`, `sigmaThree`, `sigmaFour`
- **Type**: `K ≃ₐ[ℚ] K`
- **What**: the automorphisms `ζ ↦ ζ²`, `ζ ↦ ζ³`, `ζ ↦ ζ⁴`; `σ₄` is complex conjugation.
- **How**: `IsCyclotomicExtension.fromZetaAut` on `zeta_isPrimitiveRoot.pow_of_coprime k`.
- **Uses from project**: [zeta_isPrimitiveRoot]
- **Visibility**: public — **Lines**: 35–47

### `theorem sigmaTwo_apply_zeta`, `sigmaThree_apply_zeta`, `sigmaFour_apply_zeta`
- **Type**: `σₖ ζ = ζ^k`
- **What**: action spec. `σ₄ ζ = ζ⁴ = ζ⁻¹` (conj; fixed field = `ℚ(ζ+ζ⁻¹) = ℚ(√5)`).
- **How**: `IsCyclotomicExtension.fromZetaAut_spec`.
- **Uses from project**: [zeta_isPrimitiveRoot]
- **Visibility**: public — **Lines**: 50–63

### `private theorem autEq'`
- **Type**: `∀ σ, σ = id ∨ σ = σ₂ ∨ σ = σ₃ ∨ σ = σ₄`
- **What**: exhaustive list of the 4 automorphisms.
- **How**: `autToPow_spec`, `(t:ZMod 5).val ∈ {1,2,3,4}` by `decide`, power-basis `algHom_ext`.
- **Uses from project**: [zeta_isPrimitiveRoot, sigma*_apply_zeta]
- **Visibility**: private — **Lines**: 65–81

### `theorem isGalois`
- **Type**: `IsGalois ℚ K`. **How**: `IsCyclotomicExtension.isGalois`. Public. **Lines**: 84–85. Uses: [].

### `theorem galoisGroupStructure`
- **Type**: `Nonempty ((K ≃ₐ[ℚ] K) ≃* (ZMod 5)ˣ)`
- **What**: Galois group is the cyclotomic character group `(ℤ/5)ˣ`.
- **How**: `IsCyclotomicExtension.autEquivPow`.
- **Uses from project**: []
- **Visibility**: public — **Lines**: 88–89

### `theorem galoisGroup_isCyclic`
- **Type**: `IsCyclic (K ≃ₐ[ℚ] K)`
- **What**: Galois group cyclic of order 4 (2 is a primitive root mod 5).
- **How**: surjective image of `autEquivPow.symm`.
- **Uses from project**: []
- **Visibility**: public — **Lines**: 92–96

### `theorem orderOf_sigmaTwo`
- **Type**: `orderOf sigmaTwo = 4`
- **What**: `σ₂` generates the Galois group.
- **How**: transport via `autEquivPow` to `⟨2,3⟩ ∈ (ZMod 5)ˣ`, `decide` powers, `Nat.dvd_prime_pow`.
- **Uses from project**: [zeta_isPrimitiveRoot, sigmaTwo_apply_zeta]
- **Visibility**: public — **Lines**: 99–127

### `theorem aut_eq`
- **Type**: public wrapper of `autEq'`. **Lines**: 130–132. Uses: [autEq'].

**File Summary**: Full Galois description: 4 explicit automorphisms via `fromZetaAut`, group
`≅ (ℤ/5)ˣ ≅ ℤ/4` cyclic, generator `σ₂` of order 4, exhaustive classification. Sorry-free.

---

## Embeddings.lean

### `theorem isTotallyComplex`
- **Type**: `NumberField.IsTotallyComplex K`. **How**: `IsCyclotomicExtension.Rat.isTotallyComplex`. Public. **Lines**: 34–35. Uses: [].

### `theorem nrRealPlaces_eq_zero`
- **Type**: `nrRealPlaces K = 0`. **How**: `IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero`. Public. **Lines**: 37–38. Uses: [].

### `theorem nrComplexPlaces_eq_two`
- **Type**: `nrComplexPlaces K = 2`
- **What**: signature `(0,2)`.
- **How**: `card_add_two_mul_card_eq_rank` + `degree_eq_four` + omega.
- **Uses from project**: [nrRealPlaces_eq_zero, degree_eq_four]
- **Visibility**: public — **Lines**: 40–43

### `theorem infinitePlace_card_eq_two`
- **Type**: `Fintype.card (InfinitePlace K) = 2`. **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces`. Public. **Lines**: 57–60. Uses: [nrRealPlaces_eq_zero, nrComplexPlaces_eq_two].

### `theorem infinitePlace_isComplex`
- **Type**: `∀ v, v.IsComplex`. **How**: `isTotallyComplex.isComplex`. Public. **Lines**: 62–64. Uses: [isTotallyComplex].

### `theorem exists_complexEmbedding_zeta`
- **Type**: `∃ σ : K →+* ℂ, σ ζ = exp(2πi/5)`
- **What**: explicit complex embedding hitting the standard 5th root.
- **How**: `Complex.isPrimitiveRoot_exp`, `AdjoinRoot.liftAlgHom` of `Φ₅`, transported through
  `adjoinRootEquivCyclotomic.symm`.
- **Uses from project**: [zetaFivePolynomial, adjoinRootEquivCyclotomic, adjoinRootEquivCyclotomic_root]
- **Visibility**: public — **Lines**: 66–82

**File Summary**: Signature `(0,2)`, two complex places, totally complex, plus a concrete
complex embedding `ζ ↦ e^{2πi/5}` built through the `AdjoinRoot` model. Sorry-free.

---

## RingOfIntegers.lean

### `theorem zeta_integral`
- **Type**: `ζ ∈ integralClosure ℤ K`. **How**: `IsPrimitiveRoot.isIntegral`. Public. **Lines**: 32–33. Uses: [zeta_isPrimitiveRoot].

### `def zetaInt`
- **Type**: `𝓞 K` = `⟨ζ, zeta_integral⟩`. The integral form of `ζ`. Public. **Lines**: 36. Uses: [zeta_integral].

### `theorem zetaInt_pow_five`
- **Type**: `zetaInt ^ 5 = 1`. **How**: `Subtype.ext` + `zeta_pow_five`. Public. **Lines**: 39–40. Uses: [zetaInt, zeta_pow_five].

### `theorem zetaInt_sum_eq_zero`
- **Type**: `1 + zetaInt + … + zetaInt⁴ = 0`. **How**: `Subtype.ext` + `zeta_sum_eq_zero`. Public. **Lines**: 43–44. Uses: [zetaInt, zeta_sum_eq_zero].

### `abbrev integralPowerBasis`
- **Type**: `PowerBasis ℤ (𝓞 K)` = `zeta_isPrimitiveRoot.integralPowerBasis` (`1,ζ,ζ²,ζ³`). Public. **Lines**: 47–48. Uses: [zeta_isPrimitiveRoot].

### `theorem integralPowerBasis_gen`
- **Type**: `gen = zeta_isPrimitiveRoot.toInteger`. **How**: simp. Public. **Lines**: 51–52. Uses: [].

### `theorem integralPowerBasis_dim`
- **Type**: `dim = 4`. **How**: `integralPowerBasis_dim`. Public. **Lines**: 54–55. Uses: [].

### `def integralBasisVectors`
- **Type**: `Fin 4 → K` = `![1, ζ, ζ², ζ³]`. Public. **Lines**: 58. Uses: [ζ].

### `theorem span_integralBasisVectors_eq`
- **Type**: `Submodule.span ℤ (range vectors) = Subalgebra.toSubmodule (integralClosure ℤ K)`
- **What**: `1,ζ,ζ²,ζ³` spans `𝓞 K` as a ℤ-lattice.
- **How**: monogenicity (`isIntegralClosure_adjoin_singleton`), `modByMonic` reduction against
  monic `Φ₅` over ℤ, `aeval_eq_sum_range'` to land in the span.
- **Uses from project**: [zeta_integral, zeta_sum_eq_zero, zeta_isPrimitiveRoot]
- **Visibility**: public — **Lines**: 62–109

### `def concreteIntegralBasis`
- **Type**: `Basis (Fin 4) ℤ (𝓞 K)` — reindexed `integralPowerBasis.basis`. Public. **Lines**: 112–113. Uses: [integralPowerBasis_dim].

### `theorem concreteIntegralBasis_apply`
- **Type**: `algebraMap (concreteIntegralBasis i) = integralBasisVectors i`. **How**: `fin_cases` + simp. Public. **Lines**: 116–119. Uses: [concreteIntegralBasis, integralBasisVectors].

### `theorem span_integralBasisVectors_eq_integralBasis`
- **Type**: `span ℤ (range vectors) = span ℤ (range (NumberField.integralBasis K))`
- **What**: displayed basis and mathlib's integral basis span the same lattice.
- **How**: reduce both to `integralClosure` via `mem_span_integralBasis`.
- **Uses from project**: [span_integralBasisVectors_eq]
- **Visibility**: public — **Lines**: 124–135

### `abbrev concreteRingOfIntegers`
- **Type**: `Subalgebra ℤ K` = `Algebra.adjoin ℤ {ζ}` = `ℤ[ζ]`. Public. **Lines**: 138. Uses: [ζ].

### `theorem isIntegralClosure_adjoin_zeta`
- **Type**: `IsIntegralClosure (adjoin ℤ {ζ}) ℤ K`. **How**: `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`. Public. **Lines**: 141–143. Uses: [zeta_isPrimitiveRoot].

### `theorem integralPowerBasis_adjoin_gen_eq_top`
- **Type**: `adjoin ℤ {gen} = ⊤`. **How**: `PowerBasis.adjoin_gen_eq_top`. Public. **Lines**: 146–148. Uses: [].

### `theorem ringOfIntegers_eq`
- **Type**: `integralClosure ℤ K = concreteRingOfIntegers`
- **What**: `𝓞 K = ℤ[ζ]` (monogenic).
- **How**: antisymm via `isIntegralClosure_adjoin_zeta`.
- **Uses from project**: [isIntegralClosure_adjoin_zeta]
- **Visibility**: public — **Lines**: 151–156

**File Summary**: Ring of integers `= ℤ[ζ]`, integral basis `1,ζ,ζ²,ζ³`, lattice-equality with
mathlib's `integralBasis`. Sorry-free; foundation for Discriminant + PrimeSplitting.

---

## Discriminant.lean

### `theorem numberField_discr_eq`
- **Type**: `NumberField.discr K = 125`
- **What**: discriminant `= 5³` (odd-prime cyclotomic formula `(-1)^((p-1)/2) p^(p-2)`).
- **How**: `IsCyclotomicExtension.Rat.discr_prime 5` + `norm_num`.
- **Uses from project**: []
- **Visibility**: public — **Lines**: 34–37

### `theorem concreteIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ concreteIntegralBasis = 125`. **How**: `discr_eq_discr` + `numberField_discr_eq`. Public. **Lines**: 40–43. Uses: [concreteIntegralBasis, numberField_discr_eq].

### `theorem integralBasis_discr`
- **Type**: `Algebra.discr ℚ (integralBasis K) = 125`. **How**: `coe_discr` + `numberField_discr_eq`. Public. **Lines**: 46–50. Uses: [numberField_discr_eq].

**File Summary**: Discriminant `125` three ways (field invariant, concrete basis, mathlib basis).
Sorry-free.

---

## PrimeSplitting.lean

The longest file (1166 lines). Opens with a `PrivateMachinery` section duplicating Galois data
(re-declared so it is available earlier on the spine: PrimeSplitting imports Discriminant, not
Galois) and norm-via-conjugates infrastructure; then norm forms, the totally-ramified prime over
5, inert 2, split 19, totally-split 11, the splitting/ramification laws, and the different.

### `private` (section `PrivateMachinery`, Lines 33–179)
- `gen_eq_zetaInt` : `integralPowerBasis.gen = zetaInt`. Uses [zeta_isPrimitiveRoot].
- `sig2`,`sig3`,`sig4` : private copies of `σ₂,σ₃,σ₄` via `fromZetaAut`. Uses [zeta_isPrimitiveRoot].
- `sig2_zeta`,`sig3_zeta`,`sig4_zeta` : action specs via `fromZetaAut_spec`.
- `autEq'` : the 4-automorphism classification (local copy). Uses [sig*_zeta].
- `prod_aut_apply (x)` : `∏ σ, σ x = x·σ₂x·σ₃x·σ₄x`; enumerates `univ = {1,σ₂,σ₃,σ₄}`.
- `intNorm_eq (x,n)` : compute `Algebra.norm ℤ x` from the conjugate product equalling `n`; via
  `Algebra.norm_eq_prod_automorphisms` + `coe_norm_int`.
- `minpoly_gen_eq` : `minpoly ℤ gen = X⁴+X³+X²+X+1`; `minpoly.isIntegrallyClosed_dvd` + degree/monic.
- `isMaximal_span_pair (p,r,hr)` : `(p, ζ - r)` maximal when `r` is a root of `Φ₅ mod p` —
  thin wrapper over Common `isMaximal_span_gen_sub`. **Uses Common ResidueHom.**
- `absNorm_span_pair (p,r,hr)` : `absNorm (p, ζ - r) = p` — wrapper over Common
  `absNorm_span_gen_sub`. **Uses Common ResidueHom.**

### `theorem norm_one_sub_zeta`
- **Type**: `Algebra.norm ℚ (1 - ζ) = 5`
- **What**: generator of the prime above 5 has norm `Φ₅(1) = 5`.
- **How**: `sub_one_norm_isPrimePow` + degree-4 norm of `-1`.
- **Uses from project**: [zeta_isPrimitiveRoot, degree_eq_four]
- **Visibility**: public — **Lines**: 181–195

### `theorem norm_one_add_zeta`
- **Type**: `Algebra.norm ℚ (1 + ζ) = 1`
- **What**: `1 + ζ` is a *cyclotomic unit* (`Φ₅(-1) = 1`).
- **How**: `1 - ζ² = (1-ζ)(1+ζ)`, norm of `1-ζ²` is 5, divide by `norm_one_sub_zeta`.
- **Uses from project**: [zeta_isPrimitiveRoot, degree_eq_four, norm_one_sub_zeta]
- **Visibility**: public — **Lines**: 197–215

### `def normForm {R} (a b c d)`
- **Type**: `R` — explicit quartic form `N(a + bζ + cζ² + dζ³)` in the integral basis. Public. **Lines**: 218–228. Uses: [].

### `private` norm-form helpers (Lines 230–344)
- `zetaCoords`,`normPairA/B/C`,`zetaPair` : building blocks (`ζ²+ζ³` satisfies `zetaPair² = 1 - zetaPair`).
- `sig2_zetaCoords`,`sig3_zetaCoords`,`sig4_zetaCoords` : conjugates of `a+bζ+cζ²+dζ³`.
- `zetaCoords_mul_sig4`, `sig2_zetaCoords_mul_sig3` : the two quadratic factors of the conjugate
  product expressed via `normPair*` + `zetaPair`.
- `normPair_mul_eq_normForm` : product of the two factors `= algebraMap (normForm a b c d)`.

### `theorem norm_eq_normForm (a b c d : ℚ)`
- **Type**: `Algebra.norm ℚ (a•1 + b•ζ + c•ζ² + d•ζ³) = normForm a b c d`
- **How**: `norm_eq_prod_automorphisms` + `prod_aut_apply`, then the `normPair` factorisation.
- **Uses from project**: [PrivateMachinery, normForm, zeta helpers]
- **Visibility**: public — **Lines**: 347–369

### `theorem intNorm_eq_normForm (a b c d : ℤ)`
- **Type**: integral version `Algebra.norm ℤ (…) = normForm a b c d`. **How**: `coe_norm_int` cast from `norm_eq_normForm`. Public. **Lines**: 372–386. Uses: [norm_eq_normForm, zetaInt].

### `theorem isUnit_iff_normForm (a b c d : ℤ)`
- **Type**: `IsUnit (a•1+b•ζ+c•ζ²+d•ζ³) ↔ (normForm a b c d).natAbs = 1`
- **What**: unit equation in the integral basis.
- **How**: `NumberField.isUnit_iff_norm` + `intNorm_eq_normForm`.
- **Uses from project**: [intNorm_eq_normForm]
- **Visibility**: public — **Lines**: 389–401

### `theorem span_five_eq`
- **Type**: `Ideal.span {5} = Ideal.span {1 - zetaInt} ^ 4`
- **What**: 5 is totally ramified, `(5) = (1-ζ)⁴`, `e = 4 = [K:ℚ]`.
- **How**: `span_singleton_eq_span_singleton` with explicit unit, `linear_combination`.
- **Uses from project**: [zetaInt_sum_eq_zero, zetaInt_pow_five]
- **Visibility**: public — **Lines**: 405–411

### `private span_one_sub_zetaInt_eq_pair`
- `Ideal.span {1 - zetaInt} = Ideal.span {(5:𝓞K), zetaInt - 1}`; bridges to the Kummer pair form. **Lines**: 413–426.

### `theorem isPrime_span_one_sub_zeta`
- **Type**: `(span {1 - zetaInt}).IsPrime`
- **What**: `(1-ζ)` is the unique prime over 5.
- **How**: `isMaximal_span_pair 5 1` (root of `Φ₅ mod 5` is 1). **Uses Common ResidueHom (via wrapper).**
- **Uses from project**: [isMaximal_span_pair, span_one_sub_zetaInt_eq_pair]
- **Visibility**: public — **Lines**: 429–434

### `theorem absNorm_span_one_sub_zeta`
- **Type**: `absNorm (span {1-zetaInt}) = 5` (residue degree `f = 1`). **How**: `absNorm_span_pair 5 1`. Public. **Lines**: 437–439. Uses: [absNorm_span_pair].

### `theorem liesOver_span_one_sub_zeta`
- **Type**: `(span {1-zetaInt}).LiesOver (span {(5:ℤ)})`. **How**: `liesOver_span_iff` + `span_five_eq`. Public. **Lines**: 442–449. Uses: [isPrime_span_one_sub_zeta, span_five_eq].

### `theorem inertiaDeg_span_one_sub_zeta`
- **Type**: `inertiaDeg = 1`. **How**: `absNorm_eq_pow_inertiaDeg'` + `absNorm_span_one_sub_zeta`. Public. **Lines**: 452–459. Uses: [liesOver…, absNorm…].

### `theorem ramificationIdx_span_one_sub_zeta`
- **Type**: `ramificationIdx = 4`. **How**: `ramificationIdx_spec`; lower bound from `span_five_eq`, upper from absNorm of `P⁵ ∤ (5)`. Public. **Lines**: 462–484. Uses: [span_five_eq, absNorm_span_one_sub_zeta, concreteIntegralBasis].

### `theorem absNorm_span_two`
- **Type**: `absNorm (span {2}) = 16` (`f = 4`). **How**: `absNorm_span_singleton` + `norm_algebraMap` + `finrank = 4`. Public. **Lines**: 487–493. Uses: [concreteIntegralBasis].

### `private quotient_zeta_ne_one_of_two_mem`, `absNorm_maximal_over_span_two_eq_sixteen`
- Order-5 argument in the residue field: `ζ̄ ≠ 1`, residue field `𝔽_{2^k}` with `5 ∣ 2^k - 1`
  forces `k = 4`. **Lines**: 495–556. Uses: [zetaInt_sum_eq_zero, zetaInt_pow_five].

### `theorem isPrime_span_two`
- **Type**: `(span {2}).IsPrime`
- **What**: 2 is inert (`ord_{(ℤ/5)ˣ}(2) = 4`, `Φ₅` irreducible mod 2).
- **How**: maximal `M ⊇ (2)` has norm 16 = norm(2), so `M = (2)`; Common `eq_of_le_of_absNorm_eq`.
- **Uses from project**: [absNorm_span_two, eq_of_le_of_absNorm_eq]
- **Visibility**: public — **Lines**: 559–569

### `theorem liesOver_span_two`, `inertiaDeg_span_two`, `ramificationIdx_span_two`
- 2 lies over (2); `inertiaDeg = 4`; `ramificationIdx = 1` (unramified, via `ramified_iff_eq_five 2`).
- **Lines**: 572–589; 1088–1100. Uses: [isPrime_span_two, absNorm_span_two, ramified_iff_eq_five].

### `private` 19-machinery (Lines 591–733)
- `nineteen_x_eq`,`nineteen_y_eq` : factor 19 into two conjugate-pair products.
- `span_pair_nineteen_left/right` : identify Kummer pairs `(19, ζ²+5ζ+1)`, `(19, ζ²+15ζ+1)` with
  principal `(ζ²+5ζ+1)`, `(ζ²−4ζ+1)`.
- `absNorm_span_x`,`absNorm_span_y` : both have norm 361 = 19² (via `intNorm_eq` conjugate product).
- `absNorm_ne_nineteen (P)` : no prime of norm 19 (`Φ₅` has no root mod 19, `decide` over `ZMod 19`).
- `isPrime_of_absNorm_361` : norm-361 principal ideal is prime (the 19-factor isn't norm 1 or 19).

### `theorem span_nineteen_eq`
- **Type**: `span {19} = (19, ζ²+5ζ+1)·(19, ζ²+15ζ+1)`
- **What**: 19 splits into two degree-2 primes (`19 ≡ -1 mod 5`, order 2).
- **Uses from project**: [span_pair_nineteen_*, zetaInt relations]
- **Visibility**: public — **Lines**: 737–747

### `theorem isPrime_primesAboveNineteen`
- **Type**: both factors of norm 361 are prime. **How**: `isPrime_of_absNorm_361`. Public. **Lines**: 750–757. Uses: [span_pair_nineteen_*, absNorm_span_x/y].

### `private` 11-machinery (Lines 759–899)
- `elevenA`,`elevenB`,`elevenC` : the conjugate orbit `{ζ²+ζ−1, ζ⁴+ζ²−1, ζ³+ζ−1, ζ⁴+ζ³−1}` has product 11.
- `norm_eleven_orbit (w)` : norm 11 from the conjugate product.
- `absNorm_span_u3/u4/u5/u9` : the four generators each of norm 11.
- `span_pair_eleven_{three,four,five,nine}` : Kummer pairs `(11, ζ - r)`, `r ∈ {3,4,5,9}` (roots of
  `Φ₅ mod 11`), each principal of norm 11; via `eq_of_le_of_absNorm_eq` + `absNorm_span_pair`.

### `theorem span_eleven_eq`
- **Type**: `span {11} = ∏ (11, ζ - r)`, `r ∈ {3,4,5,9}`
- **What**: 11 splits completely (`11 ≡ 1 mod 5`).
- **Uses from project**: [span_pair_eleven_*, zetaInt relations]
- **Visibility**: public — **Lines**: 903–922

### `theorem isPrime_primeAboveEleven (r, hr)`
- **Type**: `(11, ζ - r).IsPrime` for `r ∈ {3,4,5,9}`. **How**: `isMaximal_span_pair 11 r` + `decide`. Public. **Lines**: 925–932. Uses: [isMaximal_span_pair].

### `private one_mod_five_of_splits_completely`, `splits_completely_of_one_mod_five`
- The two directions of the splitting law: a degree-1 prime forces `ζ̄` to have order 5 in `𝔽_p`,
  so `5 ∣ p−1`; conversely build a root of `Φ₅` from a generator of `(ZMod p)ˣ`. **Lines**: 934–1028.

### `theorem splits_completely_iff (p, hp, hp5)`
- **Type**: `(∃ degree-1 prime over p) ↔ p % 5 = 1`
- **What**: the splitting law for `ℚ(ζ₅)` (decomposition determined by `p mod 5`).
- **Uses from project**: [one_mod_five_…, splits_completely_…]
- **Visibility**: public — **Lines**: 1031–1036

### `theorem ramified_iff_eq_five (p, hp)`
- **Type**: `(∃ P prime, span {p} ≤ P²) ↔ p = 5`
- **What**: 5 is the only ramified prime (the prime divisors of `disc = 125`).
- **How**: forward via `differentIdeal`, `dvd_differentIdeal_iff`, `absNorm_differentIdeal = 125`;
  uses Common `not_isUnramifiedAt_of_…` + `not_map_span_natCast_le_pow_succ_…`; reverse via `span_five_eq`.
- **Uses from project**: [concreteIntegralBasis, numberField_discr_eq, span_five_eq,
  isPrime_span_one_sub_zeta, Common unramified lemmas]
- **Visibility**: public — **Lines**: 1040–1085

### `theorem absNorm_differentIdeal_eq_oneHundredTwentyFive`
- **Type**: `absNorm (differentIdeal ℤ (𝓞 K)) = 125`. **How**: `NumberField.absNorm_differentIdeal` + `numberField_discr_eq`. Public. **Lines**: 1115–1118. Uses: [numberField_discr_eq].

### `theorem prime_dvd_differentIdeal_iff_eq_span_one_sub_zeta (P, _, _)`
- **Type**: `P ∣ differentIdeal ↔ P = span {1 - zetaInt}`
- **What**: only the ramified prime `(1-ζ)` divides the different.
- **How**: forward by norm-divides-125 ⇒ contains 5 ⇒ contains `(1-ζ)`; reverse via
  `pow_sub_one_dvd_differentIdeal` (`e = 4`).
- **Uses from project**: [absNorm_differentIdeal…, span_five_eq, absNorm_span_one_sub_zeta,
  isPrime_span_one_sub_zeta]
- **Visibility**: public — **Lines**: 1120–1164

**File Summary**: Complete splitting analysis: totally ramified 5 (`(5)=(1-ζ)⁴`, `e=4,f=1`), inert
2 (`f=4`), split 19 (two `f=2`), totally split 11 (four `f=1`), the `p mod 5` splitting law,
`ramified ⇔ p=5`, and the different supported at `(1-ζ)`. Heavy reliance on the Common
Kummer–Dedekind `ResidueHom` (`isMaximal_span_gen_sub`/`absNorm_span_gen_sub` via the
`*_span_pair` wrappers) and `eq_of_le_of_absNorm_eq`. Sorry-free.

---

## ClassGroup.lean

### `abbrev zetaFractionalIdeal`
- `FractionalIdeal (𝓞 K)⁰ K` = `spanSingleton ζ`. Public. **Lines**: 31. Uses: [ζ].

### `abbrev ramifiedPrimeFractionalIdeal`
- the fractional ideal `(1 - zetaInt)`. Public. **Lines**: 34–35. Uses: [zetaInt].

### `theorem zeta_mem_fractionalIdeal`
- `ζ ∈ zetaFractionalIdeal`. **How**: `mem_spanSingleton_self`. Public. **Lines**: 37–39. Uses: [].

### `theorem zetaFractionalIdeal_absNorm`
- `absNorm = |Algebra.norm ℚ ζ|`. **How**: `absNorm_span_singleton`. Public. **Lines**: 41–43. Uses: [].

### `theorem ramifiedPrimeFractionalIdeal_ne_zero`
- nonzero, from `ζ ≠ 1` (order 5). Public. **Lines**: 45–56. Uses: [zetaInt, zeta_isPrimitiveRoot].

### `theorem classNumber_eq_one`
- **Type**: `NumberField.classNumber K = 1`
- **What**: class number 1 (Minkowski bound `≈ 1.7 < 2`).
- **How**: `classNumber_eq_one_iff` →
  `isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`; bound the
  Minkowski floor `< 2` via `nrComplexPlaces=2`, `disc=125`, `√125 < 12`, `π > 3.14`, `nlinarith`.
- **Uses from project**: [nrComplexPlaces_eq_two, degree_eq_four, numberField_discr_eq]
- **Visibility**: public — **Lines**: 74–102

### `theorem isPrincipalIdealRing`
- `IsPrincipalIdealRing (𝓞 K)`. **How**: `classNumber_eq_one_iff`. Public. **Lines**: 105–107. Uses: [classNumber_eq_one].

### `theorem uniqueFactorizationMonoid`
- `UniqueFactorizationMonoid (𝓞 K)`. **How**: PID ⇒ UFD instance. Public. **Lines**: 110–112. Uses: [isPrincipalIdealRing].

### `theorem classGroupStructure`
- `Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1))`. **How**: trivial group via `Nat.card = 1`. Public. **Lines**: 115–120. Uses: [classNumber_eq_one].

### `abbrev unitIdealRepresentative`, `theorem classGroupRepresentative`
- the trivial class representative `⊤`; every class equals it (`Subsingleton.elim`). Public. **Lines**: 123–131. Uses: [classNumber_eq_one].

**File Summary**: Class number 1 via Minkowski bound `< 2`; PID/UFD; trivial class group. The
Minkowski floor computation is the only nontrivial proof. Sorry-free.

---

## Units.lean

### `def torsionGenerator`
- **Type**: `(𝓞 K)ˣ` — `-ζ` with inverse `-ζ⁴` (`(-ζ)(-ζ⁴) = ζ⁵ = 1`); primitive 10th root. Public. **Lines**: 35–39. Uses: [zetaInt, zetaInt_pow_five].

### `def torsionUnits`
- `{u | ∃ k : Fin 10, u = torsionGenerator^k}` = `μ₁₀`. Public. **Lines**: 42. Uses: [torsionGenerator].

### `private torsionOrder_eq'`, `theorem torsionOrder_eq_ten`
- `torsionOrder K = 10`. **How**: `IsCyclotomicExtension.Rat.torsionOrder_eq` (5 odd ⇒ 2·5). Public. **Lines**: 45–46, 88–89. Uses: [].

### `private neg_zeta_isPrimitiveRoot`
- `IsPrimitiveRoot (-ζ) 10`. **How**: `orderOf_mul` of coprime orders 2 and 5. **Lines**: 48–58. Uses: [zeta_isPrimitiveRoot].

### `theorem torsionUnits_eq`
- **Type**: `{u | IsOfFinOrder u} = torsionUnits`
- **What**: the torsion subgroup is exactly `μ₁₀ = {±ζ^j}`.
- **How**: `rootsOfUnity_eq_torsion` + `torsionOrder = 10`; `eq_pow_of_pow_eq_one` of `-ζ`.
- **Uses from project**: [torsionGenerator, neg_zeta_isPrimitiveRoot, torsionOrder_eq']
- **Visibility**: public — **Lines**: 60–84

### `theorem unitRank_eq_one`
- **Type**: `NumberField.Units.rank K = 1`. **What**: `r₁+r₂-1 = 1`. **How**: `nrRealPlaces=0`, `nrComplexPlaces=2`. Public. **Lines**: 93–95. Uses: [nrRealPlaces_eq_zero, nrComplexPlaces_eq_two].

### `def fundamentalUnit`
- **Type**: `(𝓞 K)ˣ` — the cyclotomic unit `1 + ζ`, inverse `-(ζ + ζ³)`
  (`(1+ζ)(ζ+ζ³) = ζ+ζ²+ζ³+ζ⁴ = -1`). Public. **Lines**: 99–103. Uses: [zetaInt, zetaInt_sum_eq_zero].

### `def fundamentalUnitSystem`
- **Type**: `Fin (rank K) → (𝓞 K)ˣ` — the single-element system `fun _ => 1 + ζ`. Public. **Lines**: 106–107. Uses: [fundamentalUnit].

### `private exists_eq_torsion_mul_fundSystem_zpow`
- mathlib's `fundSystem K i₀` + torsion generate everything (rank-1 specialisation of
  `closure_fundSystem_sup_torsion_eq_top`). **Lines**: 111–133. Uses: [unitRank_eq_one].

### `private fundSystem_zpow_mem_torsion`
- a power of `fundSystem K i₀` is torsion only for exponent 0 (via `basisModTorsion`). **Lines**: 136–148. Uses: [].

### `private eq_torsionGenerator_pow_of_mem_torsion`
- every torsion unit is `(-ζ)^k` (from `torsionUnits_eq`). **Lines**: 151–156. Uses: [torsionUnits_eq].

### `theorem fundamentalUnitSystem_isFundamental`  ⚠️ SORRY
- **Type**: `closure (range fundamentalUnitSystem) ⊔ torsion K = ⊤`
- **What**: `1 + ζ` together with `μ₁₀` generates *all* units of `ℤ[ζ]`.
- **How**: SORRIED. This is the cyclotomic-unit index statement
  `[𝓞ˣ : ⟨μ, cyclotomic units⟩] = h⁺ = 1` for `ℚ(ζ₅)`. Blocked: identifying the *explicit* unit
  `1 + ζ` with mathlib's *abstract* `fundSystem K 0` needs the index of the cyclotomic-unit
  group, which mathlib does not provide. (`unit_eq_torsion_mul_…` and `unitGroupStructure` proceed
  *assuming* this lemma, but the abstract structure is proved independently from `fundSystem`.)
- **Uses from project**: [fundamentalUnitSystem]
- **Visibility**: public — **Lines**: 161–163

### `theorem unit_eq_torsion_mul_fundamentalUnit_zpow (u)`
- **Type**: `∃ ζ' ∈ torsion, ∃ n, u = ζ' · (1+ζ)^n` (every unit is `±ζ^j (1+ζ)^n`). **How**: `mem_sup` of `fundamentalUnitSystem_isFundamental`. Public. **Lines**: 166–181. Uses: [fundamentalUnitSystem_isFundamental, fundamentalUnit] — *downstream of the sorry*.

### `private unitGroupStructure_bijective`
- the coproduct of `torsionPowerHom 10 (-ζ)` and `rankOnePowerHom η` is bijective; injectivity from
  `fundSystem_zpow_mem_torsion` + order of `-ζ`, surjectivity from `exists_eq_torsion_mul_fundSystem_zpow`.
  **Uses Common `torsionPowerHom`,`rankOnePowerHom`.** **Lines**: 183–226. Uses: [zetaInt, neg_zeta_isPrimitiveRoot, fundSystem_zpow_mem_torsion, eq_torsionGenerator_pow_of_mem_torsion].

### `theorem unitGroupStructure`
- **Type**: `Nonempty ((𝓞 K)ˣ ≃* Multiplicative (ZMod 10) × Multiplicative (Fin 1 → ℤ))`
- **What**: the unit group `≅ μ₁₀ × ℤ` abstractly.
- **How**: `MulEquiv.ofBijective` of the coprod hom (built on `fundSystem`, *not* on
  `fundamentalUnit` — independent of the sorry).
- **Uses from project**: [torsionPowerHom, rankOnePowerHom, unitRank_eq_one, unitGroupStructure_bijective]
- **Visibility**: public — **Lines**: 229–249

### `theorem regulator_eq`  ◑ body proved, depends on the `isFundamental` sorry
- **Type**: `NumberField.Units.regulator K = 2 · log((1 + √5)/2)`
- **What**: regulator `= 2 log φ ≈ 0.962` (`φ = (1+√5)/2 = |1+ζ|` at one complex place).
- **How**: the proof body is now **complete** — `fundamentalUnitSystem_isFundamental` (index 1) ⇒
  `regOfFamily_div_regulator` ⇒ `regulator = regOfFamily`, then `regOfFamily_eq_det` +
  `Matrix.det_eq_elem_of_subsingleton` evaluate the rank-1 determinant with the archimedean value
  `|1+ζ|_v = φ`. It is **not** its own sorry any more, but it *calls* the still-sorried
  `fundamentalUnitSystem_isFundamental`, so it is true only modulo that. The regulator-value step
  itself uses only mature mathlib API.
- **Uses from project**: [`fundamentalUnitSystem_isFundamental`, `unitRank_eq_one`]
- **Visibility**: public — **Lines**: 253–311

**File Summary**: Torsion `= μ₁₀` (generator `-ζ`), rank 1, fundamental unit `1+ζ`, abstract
structure `μ₁₀ × ℤ` (proved, via Common power-homs and `fundSystem`). **One genuine sorry**:
`fundamentalUnitSystem_isFundamental` (identify `1+ζ` with mathlib's abstract fundamental unit — the
cyclotomic-unit index `h⁺=1`). `regulator_eq`'s body is now complete (mature `regOfFamily_eq_det`
route) but depends transitively on that sorry. The genuine obstruction is the absence of
cyclotomic-units API in mathlib — and, unlike the real-quadratic case (SqrtFive), there is no real
embedding to run a window-reduction, so this is a deeper, partly-intrinsic difficulty.

---

## Euclidean.lean

### `theorem normEuclidean (a b, hb)`  ⚠️ SORRY
- **Type**: `∃ q r, a = b·q + r ∧ |N r| < |N b|`
- **What**: `ℤ[ζ₅]` is norm-Euclidean.
- **How**: SORRIED. Requires the standard covering argument (every element of `K` is within
  norm-`< 1` of a lattice point of `ℤ[ζ]` under the canonical embedding) — no mathlib API for
  norm-Euclideanity of cyclotomic rings; needs a geometry-of-numbers covering estimate.
- **Uses from project**: []
- **Visibility**: public — **Lines**: 32–35

**File Summary**: Single sorried statement (norm-Euclidean), blocked on a covering argument.

---

## LocalGlobal.lean

### `def heightOneFive`
- **Type**: `HeightOneSpectrum (𝓞 K)` — the ramified prime `(1 - ζ)` as a height-one point.
  **How**: `asIdeal = span {1-zetaInt}`, prime/`ne_bot` from PrimeSplitting. Public. **Lines**: 35–43. Uses: [isPrime_span_one_sub_zeta, absNorm_span_one_sub_zeta].

### `abbrev vFive`
- `FinitePlace K` from `heightOneFive`. Public. **Lines**: 45–46. Uses: [heightOneFive].

### `example` (e=4, f=1 over 5)
- `ramificationIdx = 4` and `inertiaDeg = 1`. **Lines**: 48–54. Uses: [ramificationIdx_span_one_sub_zeta, inertiaDeg_span_one_sub_zeta].

### `abbrev CompletionAtFive`, `InfiniteCompletion`
- `heightOneFive.adicCompletion K`; `v.Completion`. Public. **Lines**: 69–70, 84–85. Uses: [heightOneFive].

### `private complexEmbedding_norm_zeta_eq_one`, `theorem infiniteCompletion_zeta_norm`
- `‖φ ζ‖ = 1` for any `φ : K →+* ℂ` (root of unity) and at any infinite completion. **Lines**: 87–101. Uses: [zeta_isPrimitiveRoot, infinitePlace_isComplex].

### `example` (∼ℂ at each place)
- `Nonempty (InfiniteCompletion v ≃+* ℂ)`. **Lines**: 91–94. Uses: [infinitePlace_isComplex].

### `private zeta_ne_zero`, product-formula `example`s
- `∏_v |ζ|_v = 1` and same for `fundamentalUnit`. **Lines**: 115–134. Uses: [zeta_isPrimitiveRoot, fundamentalUnit].

### infinite-adele block
- `CyclotomicFiveInfiniteAdeleRing`, `infinitePrincipalAdele_zeta/_fundamentalUnit`, `example`s
  (norm = `|N ζ|`, dense range). **Lines**: 148–163. Uses: [ζ, fundamentalUnit].

### `theorem canonicalEmbedding_zetaInt_mem_integerLattice`
- `ζ ∈ integerLattice`. **How**: range membership. Public. **Lines**: 177–182. Uses: [zetaInt].

### canonical-embedding geometry block
- `mixedEmbedding_zeta`; `example`s for `convexBodyLT`, measurable fundamental cone / `normLeOne`;
  `polarSpace_nonempty`. **Lines**: 198–217. Uses: [ζ].

### `theorem house_zeta`
- **Type**: `NumberField.house ζ = 1`. **What**: house of a root of unity is 1. **How**: `norm_le_iff` (all conjugates norm 1) + lower bound. Public. **Lines**: 231–242. Uses: [complexEmbedding_norm_zeta_eq_one].

### `example` (house of fundamental unit > 0)
- via `one_le_house_of_isIntegral`. **Lines**: 244–250. Uses: [fundamentalUnit].

### adele block
- `CyclotomicFiveAdeleRing`, `principalAdele_zeta/_fundamentalUnit`,
  `principalAdele_zeta_ne_zero`, `principalAdele_fundamentalUnit_is_unit_everywhere`
  (the fundamental unit has `v(u)=1` at every finite place). **Lines**: 265–298. Uses: [ζ, fundamentalUnit, zeta_ne_zero].

### Dedekind zeta block
- `cyclotomicFiveDedekindZeta`, `…Residue`; `example`s for residue positivity and the analytic
  class number formula `residue = (2^r₁ (2π)^r₂ · Reg · h)/(w·√|disc|)`. **Lines**: 312–328. Uses: [].

**File Summary**: Local-global package: ramified finite place over 5, completions (`≅ℂ`,
adic), product formula, infinite/finite adele rings, canonical & mixed embeddings + convex-body
geometry, house, and the Dedekind zeta residue / class number formula. All wrappers over mathlib
local-global API. Sorry-free.

---

## CMField.lean  (special topic)

### `theorem isCMField`
- **Type**: `NumberField.IsCMField K`
- **What**: `ℚ(ζ₅)` is a CM field.
- **How**: `IsCyclotomicExtension.Rat.isCMField K` with witness `5` (odd, `> 2`). **Uses mathlib's
  `NumberField.IsCMField` class directly.**
- **Uses from project**: []
- **Visibility**: public — **Lines**: 26–27

### `theorem cmField_isTotallyComplex`
- `IsTotallyComplex K` (restatement). **How**: `isTotallyComplex`. Public. **Lines**: 29–30. Uses: [isTotallyComplex].

### `theorem cmField_quadratic_over_maximalRealSubfield`
- **Type**: `Algebra.IsQuadraticExtension (maximalRealSubfield K) K`
- **What**: `K` is quadratic over its maximal real subfield `K⁺ = ℚ(√5)`.
- **How**: `infer_instance` given `IsCMField K` (mathlib instance). **Uses `maximalRealSubfield`.**
- **Uses from project**: [isCMField]
- **Visibility**: public — **Lines**: 32–35

### `theorem cmField_unitsRank_eq_maximalRealSubfield`
- **Type**: `Units.rank (maximalRealSubfield K) = Units.rank K`
- **What**: the unit-rank equality for CM fields (`rank K⁺ = rank K`, here both 1).
- **How**: `NumberField.IsCMField.units_rank_eq_units_rank`.
- **Uses from project**: [isCMField]
- **Visibility**: public — **Lines**: 37–41

**File Summary**: CM structure entirely via mathlib's `NumberField.IsCMField` /
`maximalRealSubfield` API (`IsCyclotomicExtension.Rat.isCMField`): CM, quadratic over the real
subfield, equal unit ranks. No bespoke CM definition. Sorry-free.

---

## QuadraticSubfield.lean  (special topic)

### `theorem gaussSum_sq`
- **Type**: `(1 + 2ζ + 2ζ⁴)² = 5`
- **What**: the quadratic Gauss sum for 5 squares to 5 ⇒ `√5 ∈ ℚ(ζ₅)`; `ℚ(√5)` is the unique
  quadratic subfield (index-2 subgroup of the cyclic Galois group; Kronecker–Weber in miniature).
- **How**: `linear_combination` of `zeta_pow_five` + `zeta_sum_eq_zero`.
- **Uses from project**: [zeta_pow_five, zeta_sum_eq_zero]
- **Visibility**: public — **Lines**: 30–31

### `abbrev sqrtFivePolynomial`
- `X² - 5`. Public. **Lines**: 34. Uses: [].

### `instance : Fact (Irreducible sqrtFivePolynomial)`
- `X²-5` irreducible (degree ≤ 3, no rational root since 5 isn't a square). **Lines**: 36–52. Uses: [].

### `abbrev QSqrtFive`, `sqrtFiveRoot`, `theorem sqrtFiveRoot_sq`
- `AdjoinRoot (X²-5) = ℚ(√5)`; formal `√5`; `√5² = 5`. Public. **Lines**: 55–65. Uses: [].

### `abbrev gaussSum`
- `1 + 2ζ + 2ζ⁴ : K`, the distinguished square root of 5 inside `ℚ(ζ₅)`. Public. **Lines**: 68. Uses: [ζ].

### `abbrev sqrtFiveSubfield`
- `Subalgebra ℚ K` = `Algebra.adjoin ℚ {gaussSum}` — the quadratic subfield. Public. **Lines**: 71. Uses: [gaussSum].

### `def sqrtFiveToCyclotomic`
- **Type**: `QSqrtFive →ₐ[ℚ] K`
- **What**: the embedding `ℚ(√5) ↪ ℚ(ζ₅)`, `√5 ↦ gaussSum`.
- **How**: `AdjoinRoot.liftAlgHom` of `Algebra.ofId ℚ K` using `gaussSum_sq`.
- **Uses from project**: [gaussSum, gaussSum_sq]
- **Visibility**: public — **Lines**: 74–76

### `def sqrtFiveEquivSubfield`
- **Type**: `QSqrtFive ≃ₐ[ℚ] sqrtFiveSubfield`
- **What**: `ℚ(√5) ≅` the generated subfield.
- **How**: `AlgEquiv.ofBijective` of the corestricted lift; surjectivity by `Algebra.adjoin_induction`
  over the single generator `gaussSum`.
- **Uses from project**: [gaussSum, gaussSum_sq, sqrtFiveSubfield]
- **Visibility**: public — **Lines**: 79–110

### `theorem sqrtFiveToCyclotomic_root`, `sqrtFiveEquivSubfield_root`
- the formal `√5` maps to `gaussSum` (under the embedding and under the equiv). **How**:
  `AdjoinRoot.liftAlgHom_root`. Public. **Lines**: 113–122. Uses: [gaussSum].

### `theorem sqrtFiveToCyclotomic_injective`
- `Function.Injective sqrtFiveToCyclotomic` (field hom). Public. **Lines**: 125–126. Uses: [sqrtFiveToCyclotomic].

**File Summary**: Realises the real quadratic subfield `ℚ(√5) ⊂ ℚ(ζ₅)` through the quadratic
Gauss sum `1 + 2ζ + 2ζ⁴` (whose square is 5). The subfield is `Algebra.adjoin ℚ {gaussSum}`, shown
equivalent to the standalone `AdjoinRoot (X²-5)` model via an explicit `liftAlgHom` +
`adjoin_induction`. No mathlib Gauss-sum or quadratic-subfield API — the embedding is hand-built
from `AdjoinRoot.liftAlgHom`. Sorry-free.

---

## Sorry ledger (2 genuine; `regulator_eq` body now complete but downstream of #1)

1. **`Units.fundamentalUnitSystem_isFundamental`** — `1 + ζ` + `μ₁₀` generate `𝓞ˣ`. Blocked: needs
   the cyclotomic-unit index `[𝓞ˣ : C] = h⁺ = 1`, where `h⁺` is the class number of the maximal real
   subfield `K⁺ = ℚ(ζ+ζ⁻¹) = ℚ(√5)` and `C` is the subgroup of cyclotomic units (`1+ζ`, …); the
   classical index theorem `[𝓞ˣ : C] = h⁺` (Washington Ch. 8) then says `1+ζ` is fundamental exactly
   because `h⁺(ℚ(√5)) = 1`. Mathlib has **no** `cyclotomicUnit` def or index theory. **Mixed cause** —
   a genuinely hard theorem (intrinsic) *and* an API gap: unlike the real-quadratic SqrtFive, the
   totally-complex field has no real embedding to run a window-reduction, so a reusable
   cyclotomic-units library is the natural (missing) tool. **This is the one sorry worth answering
   with new reusable API.**
2. **`Euclidean.normEuclidean`** — `ℤ[ζ₅]` norm-Euclidean. Blocked: geometry-of-numbers covering
   argument; no mathlib norm-Euclidean / covering API. Primarily intrinsic mathematical content.

*(Formerly listed: `Units.regulator_eq`. Its proof body is now complete via the mature
`regOfFamily_eq_det` route — the regulator value was never an API gap — but it still calls #1, so it
holds only modulo `isFundamental`.)*
