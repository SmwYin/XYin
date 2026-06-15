# Declaration Inventory — `XYin/NumberField/FieldExamples/SqrtFive/`

Real quadratic field `ℚ(√5)`, built via `QuadraticAlgebra ℚ 1 1` (the **golden-ratio model**, generator
`φ` with `φ² = φ + 1`). Twin of `SqrtTwo` (which uses the radical model `QuadraticAlgebra ℚ 2 0`).
Namespace `NumberField.SqrtFive` throughout. Every file: `noncomputable section`,
`attribute [-instance] DivisionRing.toRatAlgebra`, same open scopes.

All cross-references to `Common.lean` use namespace `NumberField.FieldExamples`.

---

## Basic.lean

### `instance : Fact (∀ r : ℚ, r ^ 2 ≠ 1 + 1 * r)`
- **Type**: `Fact (∀ r : ℚ, r ^ 2 ≠ (1 : ℚ) + (1 : ℚ) * r)`
- **What**: Provides the `QuadraticAlgebra ℚ 1 1` field instance hypothesis (no rational root of `X²-X-1`).
- **How**: From a root one builds `IsSquare (5:ℚ)` via `isSquare_iff_exists_sq` with witness `2r-1`, then `norm_num`/`nlinarith`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Visibility**: public (anonymous instance) — **Lines**: 34-41
- **Notes**: none.

### `abbrev K`
- **Type**: `K : Type := QuadraticAlgebra ℚ (1:ℚ) (1:ℚ)`
- **What**: The field `ℚ(√5)` as the golden-ratio quadratic algebra.
- **How**: definitional.
- **Uses from project**: [] — **Visibility**: public — **Lines**: 44

### `instance : FiniteDimensional ℚ K`
- **What**: `K` is finite-dimensional over `ℚ`. **How**: from `QuadraticAlgebra.basis` finiteness.
- **Uses from project**: [] — **Lines**: 46-47

### `instance : NumberField K`
- **What**: `K` is a number field. **How**: `NumberField.of_module_finite`.
- **Uses from project**: [] — **Lines**: 49-50

### `theorem degree_eq_two`
- **Type**: `Module.finrank ℚ K = 2`
- **What**: `[ℚ(√5):ℚ] = 2`. **How**: `Module.finrank_eq_card_basis` on `QuadraticAlgebra.basis` + `Fintype.card_fin`.
- **Uses from project**: [] — **Visibility**: public — **Lines**: 52-55
- **Notes**: KEY (used in Embeddings, ClassGroup, Units).

### `instance : Algebra.IsQuadraticExtension ℚ K`
- **What**: registers quadratic extension. **How**: `degree_eq_two`. **Uses**: [`degree_eq_two`] — **Lines**: 57-59

### `abbrev goldenRoot`
- **Type**: `goldenRoot : K := QuadraticAlgebra.omega`
- **What**: the generator `φ = (1+√5)/2`. **Uses**: [] — **Lines**: 62
- **Notes**: KEY — referenced pervasively in every file.

### `theorem goldenRoot_sq`
- **Type**: `goldenRoot ^ 2 = goldenRoot + 1`
- **What**: `φ² = φ + 1`. **How**: `change` to component form `⟨0,1⟩`, `ext`/`simp [pow_two]`.
- **Uses**: [`goldenRoot`] — **Lines**: 64-66 — **Notes**: KEY (used everywhere).

### `abbrev goldenPolynomial`
- **Type**: `ℚ[X] := C 1 * X^2 + C (-1) * X + C (-1)` — the minimal polynomial `X²-X-1`. **Uses**: [] — **Lines**: 69-70

### `instance : Fact (Irreducible goldenPolynomial)`
- **How**: `Polynomial.X_pow_sub_X_sub_one_irreducible_rat`. **Uses**: [`goldenPolynomial`] — **Lines**: 72-76

### `abbrev KAdjoinRoot`
- **Type**: `AdjoinRoot goldenPolynomial`. Alternate presentation. **Uses**: [`goldenPolynomial`] — **Lines**: 79

### `abbrev goldenAdjoinRoot`
- **Type**: `AdjoinRoot.root goldenPolynomial`. **Uses**: [`goldenPolynomial`] — **Lines**: 82

### `theorem goldenAdjoinRoot_sq`
- **Type**: `goldenAdjoinRoot ^ 2 = goldenAdjoinRoot + 1`. **How**: `AdjoinRoot.eval₂_root` + `linear_combination`.
- **Uses**: [`goldenAdjoinRoot`,`goldenPolynomial`] — **Lines**: 84-88

### `def goldenAdjoinRootEquivGolden`
- **Type**: `KAdjoinRoot ≃ₐ[ℚ] K`
- **What**: equivalence between AdjoinRoot and quadratic-algebra presentation.
- **How**: `AdjoinRoot.liftAlgHom` and `QuadraticAlgebra.lift`; inverses via `AdjoinRoot.algHom_ext`/`QuadraticAlgebra.algHom_ext`.
- **Uses**: [`goldenRoot`,`goldenRoot_sq`,`goldenPolynomial`,`goldenAdjoinRoot`,`goldenAdjoinRoot_sq`] — **Lines**: 91-113
- **Notes**: proof >20 lines.

### `theorem goldenAdjoinRootEquivGolden_root`
- **Type**: `goldenAdjoinRootEquivGolden goldenAdjoinRoot = goldenRoot`. **How**: `simp`. **Uses**: [the equiv, `goldenAdjoinRoot`,`goldenRoot`] — **Lines**: 115-117

### `abbrev sqrtFiveRoot`
- **Type**: `sqrtFiveRoot : K := 2 * goldenRoot - 1` — `√5 = 2φ-1`. **Uses**: [`goldenRoot`] — **Lines**: 120
- **Notes**: KEY (used in Galois, PrimeSplitting, ClassGroup, LocalGlobal).

### `theorem sqrtFiveRoot_sq`
- **Type**: `sqrtFiveRoot ^ 2 = (5:K)`. **How**: `calc` expand + `goldenRoot_sq`. **Uses**: [`sqrtFiveRoot`,`goldenRoot_sq`] — **Lines**: 122-126
- **Notes**: KEY — used in PrimeSplitting, ClassGroup, LocalGlobal repeatedly.

### `theorem goldenRoot_eq_half_sqrtFiveRoot_add_one`
- **Type**: `goldenRoot = (sqrtFiveRoot + 1)/2`. **How**: `field_simp`/`ring`. **Uses**: [`sqrtFiveRoot`] — **Lines**: 128-132

### `theorem goldenRoot_isIntegral`
- **Type**: `IsIntegral ℤ goldenRoot`. **How**: witness `X²-X-1`, `monicity`, `goldenRoot_sq`. **Uses**: [`goldenRoot_sq`] — **Lines**: 134-138
- **Notes**: KEY (RingOfIntegers, LocalGlobal).

### `instance : Fact (∀ r : ℚ, r ^ 2 ≠ 5 + 0 * r)`
- **What**: field instance for the radical model `QuadraticAlgebra ℚ 5 0`. **How**: same `IsSquare 5` contradiction. **Uses**: [] — **Lines**: 140-147

### `abbrev RadicalModel` / `sqrtFiveRadicalRoot` / `sqrtFive` / `goldenRadicalRoot`
- **Types**: `RadicalModel := QuadraticAlgebra ℚ 5 0`; `sqrtFiveRadicalRoot := omega`; `sqrtFive := sqrtFiveRadicalRoot`; `goldenRadicalRoot := (1+sqrtFive)/2`.
- **What**: the alternative `√5`-presentation and its elements. **Uses**: chain — **Lines**: 150-167

### `theorem sqrtFiveRadicalRoot_sq` / `sqrtFive_sq` / `goldenRadicalRoot_sq`
- **Types**: `sqrtFiveRadicalRoot^2 = 5`; `sqrtFive^2 = 5`; `goldenRadicalRoot^2 = goldenRadicalRoot + 1`.
- **How**: component `ext`; aliasing; `field_simp`/`linear_combination`. **Uses**: each other — **Lines**: 155-173

### `abbrev sqrtFivePolynomial` / `RadicalAdjoinRoot` / `sqrtFiveAdjoinRoot`
- **Types**: `X²-C 5`; `AdjoinRoot sqrtFivePolynomial`; `AdjoinRoot.root …`. **Uses**: chain — **Lines**: 176-183

### `theorem sqrtFiveAdjoinRoot_sq`
- **Type**: `sqrtFiveAdjoinRoot^2 = 5`. **How**: `AdjoinRoot.eval₂_root` + `linear_combination`. **Uses**: [`sqrtFiveAdjoinRoot`,`sqrtFivePolynomial`] — **Lines**: 185-190

### `private def sqrtFiveAdjoinRootToRadical` / `theorem …_root`
- **Type**: `RadicalAdjoinRoot →ₐ[ℚ] RadicalModel`; root identity.
- **How**: `AdjoinRoot.liftAlgHom`; `AdjoinRoot.liftAlgHom_root`. **Uses**: [`sqrtFivePolynomial`,`sqrtFive`,`sqrtFive_sq`,`sqrtFiveAdjoinRoot`] — **Lines**: 192-202 — **Visibility**: private

### `private def sqrtFiveRadicalToAdjoinRoot` / `theorem …_root`
- **Type**: `RadicalModel →ₐ[ℚ] RadicalAdjoinRoot`; root identity.
- **How**: `QuadraticAlgebra.lift`; component computation. **Uses**: [`sqrtFiveAdjoinRoot`,`sqrtFiveAdjoinRoot_sq`,`sqrtFive`,`sqrtFiveRadicalRoot`] — **Lines**: 204-214 — **Visibility**: private

### `def sqrtFiveRadicalEquivAdjoinRoot` / `theorem …_root`
- **Type**: `RadicalModel ≃ₐ[ℚ] RadicalAdjoinRoot`; sends `sqrtFive ↦ sqrtFiveAdjoinRoot`.
- **How**: package the two AlgHoms; inverses via `QuadraticAlgebra.algHom_ext`/`AdjoinRoot.algHom_ext`.
- **Uses**: [`sqrtFiveAdjoinRootToRadical(_root)`,`sqrtFiveRadicalToAdjoinRoot(_root)`,`sqrtFive`,`sqrtFiveAdjoinRoot`] — **Lines**: 217-244 — **Notes**: proof >20 lines.

### `def sqrtFiveRadicalToGolden` / `@[simp] theorem …_root`
- **Type**: `RadicalModel →ₐ[ℚ] K`; sends radical root to `sqrtFiveRoot`.
- **How**: `QuadraticAlgebra.lift` with proof `sqrtFiveRoot²=5`. **Uses**: [`sqrtFiveRoot`,`sqrtFiveRoot_sq`,`sqrtFiveRadicalRoot`] — **Lines**: 247-255

### `def goldenToSqrtFiveRadical` / `@[simp] theorem …_root`
- **Type**: `K →ₐ[ℚ] RadicalModel`; sends `goldenRoot ↦ (radicalRoot+1)/2`.
- **How**: `QuadraticAlgebra.lift`; `calc` quadratic identity using `sqrtFiveRadicalRoot_sq`. **Uses**: [`sqrtFiveRadicalRoot(_sq)`,`goldenRoot`] — **Lines**: 258-271

### `def sqrtFiveRadicalEquivGolden` / `theorem …_root` / `theorem …_symm_root`
- **Type**: `RadicalModel ≃ₐ[ℚ] K`. **What**: identifies radical and golden presentations.
- **How**: `QuadraticAlgebra.algHom_ext` on both composites, using `goldenRoot_eq_half_sqrtFiveRoot_add_one`. **Uses**: [`sqrtFiveRadicalToGolden(_root)`,`goldenToSqrtFiveRadical(_root)`,`sqrtFiveRoot`,`goldenRoot_eq_half_sqrtFiveRoot_add_one`,`sqrtFiveRadicalRoot`] — **Lines**: 274-309 — **Notes**: proof >25 lines.

### `def sqrtFiveAdjoinRootEquivGolden` / `theorem …_root`
- **Type**: `RadicalAdjoinRoot ≃ₐ[ℚ] K`. **How**: trans of the two equivs. **Uses**: [`sqrtFiveRadicalEquivAdjoinRoot(_root)`,`sqrtFiveRadicalEquivGolden(_root)`,`sqrtFive`,`sqrtFiveAdjoinRoot`,`sqrtFiveRoot`] — **Lines**: 312-321

**File Summary — Basic.lean**: ~38 decls (abbrevs/defs ~24, theorems ~12, instances 4).
Key API (3+): `goldenRoot`, `goldenRoot_sq`, `sqrtFiveRoot`, `sqrtFiveRoot_sq`, `goldenRoot_isIntegral`, `degree_eq_two`, `K`. No sorry. No `set_option`. Proofs >30 lines: none individually but several 20-27 line equiv constructions. The whole radical-model / AdjoinRoot apparatus (`RadicalModel`, `sqrtFive*`, four equivs) is presentation plumbing only used internally — largely "unused downstream" (only the golden model is used in later files).

---

## Galois.lean

### `private def conjHom` / `private theorem conjHom_root` / `private theorem conjHom_comp`
- **Type**: `K →ₐ[ℚ] K` sending `φ ↦ 1-φ`; `conjHom goldenRoot = 1-goldenRoot`; `conjHom.comp conjHom = id`.
- **How**: `QuadraticAlgebra.lift` (verifying `(1-φ)²=(1-φ)+1`); involution via `QuadraticAlgebra.algHom_ext`.
- **Uses**: [`goldenRoot`,`goldenRoot_sq`] — **Lines**: 34-49 — **Visibility**: private

### `def conjugation`
- **Type**: `K ≃ₐ[ℚ] K`. **What**: the nontrivial automorphism. **How**: package `conjHom` with itself as inverse.
- **Uses**: [`conjHom`,`conjHom_comp`] — **Lines**: 51-55 — **Notes**: KEY.

### `private theorem conjugation_root`
- **Type**: `conjugation goldenRoot = 1-goldenRoot`. **Uses**: [`conjHom_root`] — **Lines**: 57-58 — **Visibility**: private

### `def idAut`
- **Type**: `K ≃ₐ[ℚ] K := AlgEquiv.refl`. **Uses**: [] — **Lines**: 60

### `theorem conjugation_apply_goldenRoot`
- **Type**: `conjugation goldenRoot = 1-goldenRoot`. **Uses**: [`conjugation_root`] — **Lines**: 63-64

### `theorem conjugation_apply_sqrtFiveRoot`
- **Type**: `conjugation sqrtFiveRoot = -sqrtFiveRoot`. **How**: rewrite via `sqrtFiveRoot` def + `conjugation_apply_goldenRoot`. **Uses**: [`sqrtFiveRoot`,`conjugation_apply_goldenRoot`] — **Lines**: 66-69

### `theorem exists_conj`
- **Type**: `∃ σ : K≃ₐ[ℚ]K, σ goldenRoot = 1-goldenRoot`. **Uses**: [`conjugation`,`conjugation_root`] — **Lines**: 71-75

### `theorem aut_apply_goldenRoot`
- **Type**: `σ goldenRoot = goldenRoot ∨ σ goldenRoot = 1-goldenRoot`.
- **How**: `σφ` satisfies same quadratic, factor `(σφ-φ)(σφ-(1-φ))=0` via `linear_combination`, `mul_eq_zero`. **Uses**: [`goldenRoot_sq`] — **Lines**: 79-88

### `theorem aut_eq_or`
- **Type**: `σ = idAut ∨ σ = conjugation`. **How**: extensionality via `QuadraticAlgebra.algHom_ext` + `aut_apply_goldenRoot`. **Uses**: [`idAut`,`conjugation`,`conjugation_root`,`aut_apply_goldenRoot`] — **Lines**: 90-100

### `theorem isGalois`
- **Type**: `IsGalois ℚ K`. **How**: `infer_instance`. **Uses**: [] — **Lines**: 102-105

### `theorem galoisGroupStructure`
- **Type**: `Nonempty ((K≃ₐ[ℚ]K) ≃* Multiplicative (ZMod 2))`.
- **What**: Galois group is cyclic of order 2. **How**: `Nat.card = 2` via `Nat.card_eq_two_iff` + `aut_eq_or`, then `mulEquivOfPrimeCardEq`/`Nat.card_zmod`.
- **Uses**: [`conjugation`,`idAut`,`conjugation_root`,`aut_eq_or`,`goldenRoot`] — **Lines**: 109-126 — **Notes**: proof >15 lines.

**File Summary — Galois.lean**: 12 decls (defs 3, theorems 8 + 1 instance-like). Key API (3+): `conjugation`, `idAut`, `conjugation_apply_goldenRoot`. No sorry/set_option. >30-line proofs: none.

---

## Embeddings.lean

### `private theorem ringHom_ext_golden`
- **Type**: `{f g : K →+* ℂ} (h : f goldenRoot = g goldenRoot) → f = g`.
- **What**: ring homs `K→ℂ` agreeing on `φ` are equal. **How**: `QuadraticAlgebra.mk_eq_add_smul_omega`, `eq_ratCast` on the rational part. **Uses**: [`goldenRoot`] — **Lines**: 34-45 — **Visibility**: private
- **Notes**: generic-looking — could be a shared `QuadraticAlgebra` ext lemma.

### `theorem isTotallyReal`
- **Type**: `NumberField.IsTotallyReal K`.
- **How**: each embedding is real: conjugate root satisfies same quadratic, factor; rule out `re=1/2` branch via `nlinarith [sq_nonneg z.im]`. Uses `ComplexEmbedding.conjugate_coe_eq`, `ringHom_ext_golden`.
- **Uses**: [`ringHom_ext_golden`,`goldenRoot`,`goldenRoot_sq`] — **Lines**: 47-70 — **Notes**: proof >20 lines. KEY.

### `theorem nrRealPlaces_eq_two`
- **Type**: `InfinitePlace.nrRealPlaces K = 2`. **How**: `IsTotallyReal.nrComplexPlaces_eq_zero`, `card_add_two_mul_card_eq_rank`, `degree_eq_two`, `omega`. **Uses**: [`isTotallyReal`,`degree_eq_two`] — **Lines**: 72-77 — **Notes**: KEY (Units, LocalGlobal).

### `theorem nrComplexPlaces_eq_zero`
- **Type**: `InfinitePlace.nrComplexPlaces K = 0`. **How**: `IsTotallyReal.nrComplexPlaces_eq_zero`. **Uses**: [`isTotallyReal`] — **Lines**: 79-81 — **Notes**: KEY.

### `theorem infinitePlace_card_eq_two`
- **Type**: `Fintype.card (InfinitePlace K) = 2`. **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces` + the two counts. **Uses**: [`nrRealPlaces_eq_two`,`nrComplexPlaces_eq_zero`] — **Lines**: 96-99

### `theorem infinitePlace_isReal`
- **Type**: `(v : InfinitePlace K) → IsReal v`. **How**: `isTotallyReal.isReal`. **Uses**: [`isTotallyReal`] — **Lines**: 101-103 — **Notes**: used in LocalGlobal.

### `theorem exists_realEmbedding_goldenRatio`
- **Type**: `∃ σ : K →ₐ[ℚ] ℝ, σ goldenRoot = (1+√5)/2`. **How**: `QuadraticAlgebra.lift` with `Real.mul_self_sqrt`/`nlinarith`. **Uses**: [`goldenRoot`] — **Lines**: 105-113 — **Notes**: used in LocalGlobal.house.

### `theorem exists_realEmbedding_conjugateGoldenRatio`
- **Type**: `∃ σ, σ goldenRoot = (1-√5)/2`. **How**: same with `(1-√5)/2`. **Uses**: [`goldenRoot`] — **Lines**: 115-123

**File Summary — Embeddings.lean**: 8 decls (theorems 8, 1 private). Key API (3+): `isTotallyReal`. No sorry/set_option. >30-line proofs: none (isTotallyReal ~24). `ringHom_ext_golden` is a generic helper.

---

## RingOfIntegers.lean

### `abbrev GoldenOrder` / `abbrev goldenInteger`
- **Types**: `QuadraticAlgebra ℤ 1 1`; `goldenInteger := omega`. The concrete order `ℤ[φ]`. **Uses**: [] — **Lines**: 38-41 — **Notes**: KEY.

### `theorem goldenInteger_sq`
- **Type**: `goldenInteger^2 = goldenInteger + 1`. **How**: component `ext`. **Uses**: [`goldenInteger`] — **Lines**: 43-45

### `theorem goldenInteger_isIntegral`
- **Type**: `IsIntegral ℤ goldenInteger`. **How**: `X²-X-1`, `monicity`. **Uses**: [`goldenInteger_sq`] — **Lines**: 47-51

### `instance : Algebra.IsIntegral ℤ GoldenOrder`
- **How**: each `⟨a,b⟩` = `algebraMap a + b•goldenInteger`, both integral. **Uses**: [`goldenInteger_isIntegral`] — **Lines**: 53-59

### `def goldenOrderToField`
- **Type**: `GoldenOrder →+* K`. **What**: embeds `ℤ[φ]` into `ℚ(√5)`. **How**: coordinatewise cast; ring-hom axioms by `ext`/`simp`. **Uses**: [] — **Lines**: 62-70 — **Notes**: KEY.

### `instance : Algebra GoldenOrder K` / `instance : IsScalarTower ℤ GoldenOrder K`
- **How**: `toAlgebra`; `IsScalarTower.of_algebraMap_eq`. **Uses**: [`goldenOrderToField`] — **Lines**: 72-76

### `theorem goldenOrderToField_injective`
- **Type**: `Function.Injective goldenOrderToField`. **How**: coordinatewise `exact_mod_cast`. **Uses**: [`goldenOrderToField`] — **Lines**: 78-86

### `abbrev goldenPowerBasis`
- **Type**: `PowerBasis ℚ K` with gen `goldenRoot`, dim 2. **Uses**: [`goldenRoot`,`QuadraticAlgebra.basis`] — **Lines**: 88-94 — **Notes**: KEY.

### `theorem adjoin_goldenRoot_eq_top`
- **Type**: `Algebra.adjoin ℚ {goldenRoot} = ⊤`. **How**: `goldenPowerBasis.adjoin_gen_eq_top`. **Uses**: [`goldenPowerBasis`,`goldenRoot`] — **Lines**: 96-98 — **Notes**: used in PrimeSplitting.

### `theorem goldenPowerBasis_basis_zero` / `…_basis_one`
- **Types**: basis 0 = 1; basis 1 = goldenRoot. **How**: component `ext`. **Uses**: [`goldenPowerBasis`,`goldenRoot`] — **Lines**: 100-106

### `theorem golden_trace_eq`
- **Type**: `Algebra.trace ℚ K x = 2*x.re + x.im`. **How**: `trace_eq_matrix_trace`, `leftMulMatrix_eq_repr_mul`, `Matrix.trace_fin_two`. **Uses**: [] — **Lines**: 108-114 — **Notes**: KEY (used in discr, five_dvd).

### `theorem golden_norm_eq`
- **Type**: `Algebra.norm ℚ x = x.re² + x.re*x.im - x.im²`. **How**: `norm_eq_matrix_det`, `Matrix.det_fin_two`. **Uses**: [] — **Lines**: 116-122 — **Notes**: KEY.

### `theorem goldenPowerBasis_discr`
- **Type**: `Algebra.discr ℚ goldenPowerBasis.basis = 5`. **How**: trace matrix `!![2,1;1,3]` via `golden_trace_eq` on the 4 entries, `Matrix.det_fin_two_of`. **Uses**: [`goldenPowerBasis(_basis_zero/_one)`,`golden_trace_eq`,`goldenRoot`] — **Lines**: 124-155 — **Notes**: proof >30 lines.

### `theorem five_dvd_coords_of_trace_norm`
- **Type**: `(2m+n=5T) → (m²+mn-n²=25N) → 5∣m ∧ 5∣n`. **How**: substitute `n`, show `m²=5(...)`, `Prime.dvd_of_dvd_pow`, then `5∣n`. **Uses**: [] — **Lines**: 157-173 — **Notes**: generic-ish number lemma.

### `theorem int_eq_of_rat_div_five_eq` / `int_eq_of_rat_div_twentyFive_eq`
- **Types**: `(a:ℚ)/5 = b → a = 5b`; same /25. **How**: `norm_num`/`linear_combination`/`exact_mod_cast`. **Uses**: [] — **Lines**: 175-188 — **Notes**: generic arithmetic helpers (could move to Common).

### `private theorem five_dvd_coords_of_integral`
- **Type**: integral `x` with `m=5x.re, n=5x.im` ⇒ `5∣m ∧ 5∣n`.
- **How**: integrality of trace/norm (`Algebra.isIntegral_trace/_norm`, `exists_int_iff_exists_rat`), then `five_dvd_coords_of_trace_norm`. **Uses**: [`golden_trace_eq`,`golden_norm_eq`,`int_eq_of_rat_div_five_eq`,`int_eq_of_rat_div_twentyFive_eq`,`five_dvd_coords_of_trace_norm`] — **Lines**: 190-215 — **Visibility**: private — **Notes**: proof >20 lines.

### `theorem integral_mem_goldenOrderToField_range`
- **Type**: `IsIntegral ℤ x → ∃ y : GoldenOrder, algebraMap y = x`.
- **What**: every algebraic integer lies in `ℤ[φ]`.
- **How**: `Algebra.discr_mul_isIntegral_mem_adjoin` gives `5•x ∈ ℤ[φ]`, then divisibility of coords (`five_dvd_coords_of_integral`) to remove the 5. **Uses**: [`goldenPowerBasis(_discr)`,`goldenRoot_isIntegral`,`goldenOrderToField`,`goldenInteger`,`five_dvd_coords_of_integral`] — **Lines**: 217-251 — **Notes**: KEY; proof >30 lines.

### `instance : IsIntegralClosure GoldenOrder ℤ K`
- **How**: `goldenOrderToField_injective` + `integral_mem_goldenOrderToField_range`. **Uses**: those + `Algebra.IsIntegral.isIntegral` — **Lines**: 253-259 — **Notes**: KEY.

### `def integralBasisVectors`
- **Type**: `Fin 2 → K := ![1, goldenRoot]`. **Uses**: [`goldenRoot`] — **Lines**: 262

### `theorem span_integralBasisVectors_eq`
- **Type**: `span ℤ (range integralBasisVectors) = Subalgebra.toSubmodule (integralClosure ℤ K)`.
- **How**: `le_antisymm`; reverse uses `integral_mem_goldenOrderToField_range` + coordinate decomposition. **Uses**: [`integralBasisVectors`,`goldenRoot(_isIntegral)`,`integral_mem_goldenOrderToField_range`,`goldenOrderToField`] — **Lines**: 264-284 — **Notes**: proof >15 lines.

### `abbrev concreteRingOfIntegers`
- **Type**: `Subalgebra ℤ K := Algebra.adjoin ℤ {goldenRoot}`. **Uses**: [`goldenRoot`] — **Lines**: 287-288 — **Notes**: KEY.

### `theorem ringOfIntegers_eq`
- **Type**: `integralClosure ℤ K = concreteRingOfIntegers`. **How**: `le_antisymm`, `integral_mem_goldenOrderToField_range`, `QuadraticAlgebra.mk_eq_add_smul_omega`. **Uses**: [`concreteRingOfIntegers`,`integral_mem_goldenOrderToField_range`,`goldenRoot`] — **Lines**: 290-304 — **Notes**: KEY (PrimeSplitting); proof >15 lines.

### `theorem span_integralBasisVectors_eq_integralBasis`
- **Type**: span of `[1,φ]` = span of mathlib `integralBasis K`. **How**: `mem_span_integralBasis`, `RingHom.mem_range`. **Uses**: [`integralBasisVectors`,`span_integralBasisVectors_eq`] — **Lines**: 306-320

### `theorem adjoin_sqrtFive_ne_integralClosure`
- **Type**: `Algebra.adjoin ℤ {sqrtFiveRoot} ≠ integralClosure ℤ K`.
- **What**: `ℤ[√5]` is not the maximal order. **How**: builds the sub-`Subalgebra` `{re=a, im=2b}` containing `ℤ[√5]`, shows `φ` has odd `im`, contradiction `2b=1`. **Uses**: [`sqrtFiveRoot`,`goldenRoot`] — **Lines**: 322-362 — **Notes**: proof >30 lines.

### `abbrev sqrtFiveExplicitIntegralBasis`
- **Type**: `Basis (Fin 2) ℤ GoldenOrder := QuadraticAlgebra.basis 1 1`. **Uses**: [] — **Lines**: 365-366 — **Notes**: KEY.

### `theorem sqrtFiveExplicitIntegralBasis_zero` / `…_one`
- **Types**: basis 0 = 1; basis 1 = goldenInteger. **How**: component `ext`. **Uses**: [`goldenInteger`] — **Lines**: 369-378

### `theorem goldenOrderToField_basis_zero` / `…_one`
- **Types**: `goldenOrderToField (basis 0) = 1`; `(basis 1) = goldenRoot`. **Uses**: [`goldenOrderToField`,`sqrtFiveExplicitIntegralBasis_zero/_one`,`goldenRoot`] — **Lines**: 380-388

### `def goldenOrderEquivRingOfIntegers`
- **Type**: `GoldenOrder ≃ₐ[ℤ] 𝓞 K := IsIntegralClosure.equiv …`. **Uses**: [`GoldenOrder` instances] — **Lines**: 390-392 — **Notes**: KEY.

### `def concreteIntegralBasis`
- **Type**: `Basis (Fin 2) ℤ (𝓞 K)`. **What**: `[1,φ]` transported into `𝓞 K`. **How**: `sqrtFiveExplicitIntegralBasis.map equiv`. **Uses**: [`sqrtFiveExplicitIntegralBasis`,`goldenOrderEquivRingOfIntegers`] — **Lines**: 394-396 — **Notes**: KEY (PrimeSplitting, discr).

### `theorem concreteIntegralBasis_basis_zero` / `…_basis_one`
- **Types**: `algebraMap (basis 0) = 1`; `(basis 1) = goldenRoot`. **How**: `IsIntegralClosure.algebraMap_equiv`. **Uses**: [`concreteIntegralBasis`,`goldenOrderEquivRingOfIntegers`,`sqrtFiveExplicitIntegralBasis_…`,`goldenOrderToField_basis_…`,`goldenRoot`] — **Lines**: 398-412

### `theorem concreteIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ concreteIntegralBasis = 5`.
- **How**: `Algebra.discr_localizationLocalization` + `Module.Basis.localizationLocalization` to reduce to `goldenPowerBasis_discr`. **Uses**: [`concreteIntegralBasis(_basis_zero/_one)`,`goldenPowerBasis(_basis_zero/_one)(_discr)`] — **Lines**: 414-452 — **Notes**: proof >30 lines; heavy localization machinery.

### `theorem numberField_discr_eq`
- **Type**: `NumberField.discr K = 5`. **How**: `discr_eq_discr K concreteIntegralBasis` + `concreteIntegralBasis_discr`. **Uses**: [`concreteIntegralBasis(_discr)`] — **Lines**: 454-459 — **Notes**: KEY (PrimeSplitting ×, ClassGroup, Units).

### `theorem integralBasis_discr`
- **Type**: `Algebra.discr ℚ (integralBasis K) = 5`. **How**: `NumberField.coe_discr` + `numberField_discr_eq`. **Uses**: [`numberField_discr_eq`] — **Lines**: 461-467 — **Notes**: `attribute [local instance] DivisionRing.toRatAlgebra in`.

### `def goldenIntO`
- **Type**: `𝓞 K := ⟨goldenRoot, goldenRoot_isIntegral⟩`. **What**: `φ` in the abstract `𝓞 K`. **Uses**: [`goldenRoot(_isIntegral)`] — **Lines**: 484 — **Notes**: KEY — pervasive in PrimeSplitting/Units/Euclidean/LocalGlobal.

### `theorem norm_eq_normForm`
- **Type**: `Algebra.norm ℚ (x•1 + y•goldenRoot) = x²+xy-y²`. **How**: `golden_norm_eq` + `norm_num`. **Uses**: [`golden_norm_eq`,`goldenRoot`] — **Lines**: 486-491 — **Notes**: KEY; near-identical name to SqrtTwo's `norm_eq_normForm`.

### `theorem intNorm_eq_normForm`
- **Type**: `Algebra.norm ℤ (x•1 + y•goldenIntO) = x²+xy-y²` (`x,y:ℤ`). **How**: `Algebra.coe_norm_int`, cast to `K`, `norm_eq_normForm`. **Uses**: [`goldenIntO`,`norm_eq_normForm`,`goldenRoot`] — **Lines**: 493-507 — **Notes**: KEY — workhorse of all PrimeSplitting norm computations; twin of SqrtTwo's.

### `theorem isUnit_iff_normForm`
- **Type**: `IsUnit (x•1 + y•goldenIntO) ↔ x²+xy-y² = ±1`. **How**: `isUnit_iff_norm`, `intNorm_eq_normForm`, `abs_eq`. **Uses**: [`goldenIntO`,`intNorm_eq_normForm`] — **Lines**: 509-525 — **Notes**: twin of SqrtTwo's `isUnit_iff_normForm`.

**File Summary — RingOfIntegers.lean**: ~37 decls (defs/abbrevs ~14, theorems ~21, instances 4). Key API (3+): `goldenIntO`, `intNorm_eq_normForm`, `goldenPowerBasis`, `concreteIntegralBasis`, `numberField_discr_eq`, `golden_trace_eq`, `golden_norm_eq`, `integral_mem_goldenOrderToField_range`, `ringOfIntegers_eq`. No sorry/set_option. >30-line proofs: `goldenPowerBasis_discr`, `integral_mem_goldenOrderToField_range`, `adjoin_sqrtFive_ne_integralClosure`, `concreteIntegralBasis_discr`. Generic helpers: `int_eq_of_rat_div_five_eq`, `int_eq_of_rat_div_twentyFive_eq`, `five_dvd_coords_of_trace_norm`.

---

## Discriminant.lean

Empty body — namespace only, no declarations (content folded into RingOfIntegers).
**File Summary**: 0 decls.

---

## PrimeSplitting.lean  (1191 lines; imports `Common.lean`)

### `def sqrtFiveIntO`
- **Type**: `𝓞 K := 2*goldenIntO - 1`. **What**: `√5` in `𝓞 K`. **Uses**: [`goldenIntO`] — **Lines**: 37 — **Notes**: KEY (ClassGroup, LocalGlobal, Different).

### `theorem span_five_eq`
- **Type**: `Ideal.span {5} = Ideal.span {sqrtFiveIntO}^2`. **What**: 5 totally ramifies. **How**: `span_singleton_pow` + `sqrtFiveRoot_sq`. **Uses**: [`sqrtFiveIntO`,`goldenIntO`,`sqrtFiveRoot_sq`] — **Lines**: 41-47 — **Notes**: KEY.

### `theorem absNorm_span_sqrtFiveIntO`
- **Type**: `absNorm (span {sqrtFiveIntO}) = 5`. **How**: `intNorm_eq_normForm (-1) 2`, `absNorm_span_singleton`. **Uses**: [`sqrtFiveIntO`,`goldenIntO`,`intNorm_eq_normForm`] — **Lines**: 50-59 — **Notes**: KEY.

### `theorem isPrime_span_sqrtFiveIntO`
- **Type**: `(span {sqrtFiveIntO}).IsPrime`. **How**: `isPrime_of_irreducible_absNorm` + Nat.Prime 5. **Uses**: [`absNorm_span_sqrtFiveIntO`] — **Lines**: 62-65 — **Notes**: KEY (ClassGroup? no — LocalGlobal, Different).

### `theorem liesOver_span_sqrtFiveIntO`
- **Type**: lies over `(5:ℤ)`. **How**: `liesOver_span_iff` + `sqrtFiveRoot_sq`. **Uses**: [`isPrime_span_sqrtFiveIntO`,`sqrtFiveIntO`,`goldenIntO`,`sqrtFiveRoot_sq`] — **Lines**: 68-79

### `theorem inertiaDeg_span_sqrtFiveIntO`
- **Type**: `inertiaDeg (5) (√5) = 1`. **How**: `absNorm_eq_pow_inertiaDeg'`, `Nat.Prime.pow_eq_iff`. **Uses**: [`liesOver_span_sqrtFiveIntO`,`absNorm_span_sqrtFiveIntO`] — **Lines**: 82-89 — **Notes**: used in LocalGlobal.

### `theorem ramificationIdx_span_sqrtFiveIntO`
- **Type**: `ramificationIdx (5) (√5) = 2`. **How**: `ramificationIdx_spec`; upper bound via norm `125 ∤ 25`. **Uses**: [`span_five_eq`,`absNorm_span_sqrtFiveIntO`,`intNorm_eq_normForm`,`goldenIntO`] — **Lines**: 92-115 — **Notes**: proof >20 lines; used in LocalGlobal.

### `private theorem goldenIntO_sq`
- **Type**: `goldenIntO^2 = goldenIntO + 1`. **How**: `Subtype.ext` + `goldenRoot_sq`. **Uses**: [`goldenIntO`,`goldenRoot_sq`] — **Lines**: 117-118 — **Visibility**: private — **Notes**: DUPLICATE — also defined privately in Units.lean (lines 36-37). Could be a single public lemma.

### `private theorem absNorm_ne_two` / `absNorm_ne_three`
- **Types**: no ideal of `𝓞 K` has norm 2 (resp. 3).
- **How**: residue field `ZMod p`, lift `φ` to root of `t²=t+1` in `ZMod 2`/`3`, `decide`. **Uses**: [`goldenIntO_sq`] — **Lines**: 119-155 — **Visibility**: private — **Notes**: structurally identical pair (only the prime differs); each ~18 lines.

### `theorem isPrime_span_two`
- **Type**: `(span {2}).IsPrime` (2 inert). **How**: norm 4, take maximal `M≥(2)`, rule out norms 1,2 via `absNorm_ne_two`, `eq_of_le_of_absNorm_eq`. **Uses**: [`intNorm_eq_normForm`,`goldenIntO`,`absNorm_ne_two`, Common `eq_of_le_of_absNorm_eq`] — **Lines**: 159-190 — **Notes**: proof >30 lines.

### `theorem absNorm_span_two` / `liesOver_span_two` / `inertiaDeg_span_two`
- **Types**: norm 4; lies over (2); inertiaDeg 2. **How**: `intNorm_eq_normForm`; `liesOver_span_iff`; `absNorm_eq_pow_inertiaDeg'`+`Nat.pow_right_injective`. **Uses**: [`intNorm_eq_normForm`,`goldenIntO`,`isPrime_span_two`,`liesOver_span_two`,`absNorm_span_two`] — **Lines**: 192-220

### `theorem isPrime_span_three`
- **Type**: `(span {3}).IsPrime` (3 inert). **How**: identical to `isPrime_span_two` with norm 9 / `absNorm_ne_three`. **Uses**: [`intNorm_eq_normForm`,`goldenIntO`,`absNorm_ne_three`, Common `eq_of_le_of_absNorm_eq`] — **Lines**: 224-255 — **Notes**: proof >30 lines; structural twin of `isPrime_span_two`.

### `theorem absNorm_span_three` / `liesOver_span_three` / `inertiaDeg_span_three`
- **Types/How**: as for 2, norm 9, inertiaDeg 2. **Uses**: [`intNorm_eq_normForm`,`goldenIntO`,`isPrime_span_three`,`liesOver_span_three`,`absNorm_span_three`] — **Lines**: 257-285

### `theorem eleven_eq_mul`
- **Type**: `(11:𝓞 K) = (3+φ)(4-φ)`. **How**: `Subtype.ext`, expand, `goldenRoot_sq`. **Uses**: [`goldenIntO`,`goldenRoot_sq`] — **Lines**: 287-293

### `theorem span_eleven_eq`
- **Type**: `span {11} = span {3+φ} * span {4-φ}`. **How**: `span_singleton_mul_span_singleton` + `eleven_eq_mul`. **Uses**: [`goldenIntO`,`eleven_eq_mul`] — **Lines**: 297-300

### `theorem absNorm_span_three_add_golden` / `isPrime_span_three_add_golden`
- **Types**: norm 11; prime. **How**: `intNorm_eq_normForm 3 1`; `isPrime_of_irreducible_absNorm`. **Uses**: [`intNorm_eq_normForm`,`goldenIntO`,`absNorm_span_three_add_golden`] — **Lines**: 303-317

### `theorem absNorm_span_four_sub_golden` / `isPrime_span_four_sub_golden`
- **Types**: norm 11; prime. **How**: `intNorm_eq_normForm 4 (-1)`. **Uses**: [`intNorm_eq_normForm`,`goldenIntO`,`absNorm_span_four_sub_golden`] — **Lines**: 319-336

### `theorem liesOver_span_three_add_golden` / `liesOver_span_four_sub_golden`
- **Types**: each lies over (11). **How**: `liesOver_span_iff` + `eleven_eq_mul`. **Uses**: [`isPrime_…`,`goldenIntO`,`eleven_eq_mul`] — **Lines**: 338-358

### `theorem inertiaDeg_span_three_add_golden` / `inertiaDeg_span_four_sub_golden`
- **Types**: inertiaDeg 1 over 11. **How**: `absNorm_eq_pow_inertiaDeg'`+`Nat.Prime.pow_eq_iff`. **Uses**: [`liesOver_…`,`absNorm_…`] — **Lines**: 360-378

### `theorem primesAboveEleven_ne`
- **Type**: `span {3+φ} ≠ span {4-φ}`. **How**: assuming equal, derive `√5, 5, 11, 1 ∈ span{3+φ}` ⇒ top, contradict norm 11. **Uses**: [`goldenIntO`,`sqrtFiveIntO`,`sqrtFiveRoot_sq`,`eleven_eq_mul`,`absNorm_span_three_add_golden`] — **Lines**: 380-409 — **Notes**: proof >25 lines.

### `private theorem absNorm_span_natCast`
- **Type**: `absNorm (span {(p:ℕ):𝓞 K}) = p²` for `p:ℕ`. **How**: `intNorm_eq_normForm p 0`, `Int.natAbs_pow`. **Uses**: [`intNorm_eq_normForm`,`goldenIntO`] — **Lines**: 411-419 — **Visibility**: private — **Notes**: KEY in the general splitting law; generic.

### `private theorem concreteIntegralBasis_zero_eq_one` / `…_one_eq_goldenIntO`
- **Types**: `concreteIntegralBasis 0 = 1`; `1 = goldenIntO`. **How**: `Subtype.ext`. **Uses**: [`concreteIntegralBasis(_basis_zero/_one)`,`goldenIntO`] — **Lines**: 421-429 — **Visibility**: private

### `private theorem li_one_golden`
- **Type**: `LinearIndependent ℤ ![1, goldenIntO]`. **How**: transport from `concreteIntegralBasis.linearIndependent`. **Uses**: [`goldenIntO`,`concreteIntegralBasis(_…)`] — **Lines**: 431-440 — **Visibility**: private

### `private theorem exists_o5_coords`
- **Type**: `∀ z:𝓞 K, ∃ A B:ℤ, z = A•1 + B•goldenIntO`. **How**: `concreteIntegralBasis.repr`/`sum_repr`. **Uses**: [`goldenIntO`,`concreteIntegralBasis(_…)`] — **Lines**: 442-450 — **Visibility**: private

### `private theorem unit_golden_coeff_not_mem`
- **Type**: `A + B·φ` with `B=±1` not in `span {p}` for `p≥2`. **How**: decompose membership, `li_one_golden`, `Int.le_of_dvd`. **Uses**: [`goldenIntO`,`exists_o5_coords`,`li_one_golden`] — **Lines**: 452-476 — **Visibility**: private — **Notes**: proof >20 lines.

### `theorem ramified_iff_eq_five`
- **Type**: `(∃P prime, span{p} ≤ P²) ↔ p = 5` for prime `p`.
- **What**: `p` ramifies iff `p=5` (divides discriminant). **How**: forward uses `not_isUnramifiedAt_…` + different-ideal divisibility (`dvd_differentIdeal_iff`, `absNorm_differentIdeal`, `numberField_discr_eq`); backward uses `span_five_eq`. **Uses**: [`absNorm_span_natCast`, Common (`not_map_span_natCast_le_pow_succ_…`, `not_isUnramifiedAt_of_map_span_natCast_le_sq_…`), `numberField_discr_eq`,`isPrime_span_sqrtFiveIntO`,`span_five_eq`,`sqrtFiveIntO`] — **Lines**: 478-522 — **Notes**: proof >40 lines. KEY public result.

### `theorem ramificationIdx_span_two` / `…_three` / `…_three_add_golden` / `…_four_sub_golden`
- **Types**: each unramified (ramIdx 1). **How**: `ramificationIdx_spec`; upper bound by reducing to `ramified_iff_eq_five` (≠5). **Uses**: [`isPrime_span_…`,`ramified_iff_eq_five`,`span_eleven_eq`] — **Lines**: 524-586

### `private theorem golden_sub_mem_span_natCast_of_one_mem_span_pair`
- **Type**: technical — if `1 ∈ span{p, φ-c}` and `(φ-c)(φ-c')=p·(…)` then `φ-c' ∈ span{p}`. **How**: `mem_span_pair`, `linear_combination`. **Uses**: [`goldenIntO`] — **Lines**: 588-608 — **Visibility**: private

### `private theorem absNorm_span_prime_golden_sub_of_mul`
- **Type**: `absNorm (span {p, φ-c}) = p` given the product factorization. **How**: rule out norm 1 (via prev + `unit_golden_coeff_not_mem`) and norm p² (via `eq_of_le_of_absNorm_eq`+`unit_golden_coeff_not_mem`), then Common `eq_prime_of_dvd_prime_sq_…`. **Uses**: [`goldenIntO`,`golden_sub_mem_span_natCast_of_one_mem_span_pair`,`unit_golden_coeff_not_mem`,`absNorm_span_natCast`, Common `eq_of_le_of_absNorm_eq`,`eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq`] — **Lines**: 610-655 — **Visibility**: private — **Notes**: proof >40 lines.

### `private theorem exists_golden_root_of_absNorm_eq_prime`
- **Type**: `absNorm P = p ⇒ ∃ t:ZMod p, t²=t+1`. **How**: residue field `≃ ZMod p` (`ZMod.ringEquivOfPrime`), lift `φ`. **Uses**: [`goldenIntO`,`goldenIntO_sq`] — **Lines**: 657-675 — **Visibility**: private

### `private theorem isSquare_five_of_absNorm_eq_prime`
- **Type**: `absNorm P = p ⇒ IsSquare ((5:ℕ):ZMod p)`. **How**: from root `t`, `2t-1` squares to 5. **Uses**: [`exists_golden_root_of_absNorm_eq_prime`] — **Lines**: 677-683 — **Visibility**: private

### `private theorem pm_one_mod_five_of_splits`
- **Type**: split ⇒ `p%5 ∈ {1,4}`. **How**: norms multiply to `p²`, one factor norm `p`, `isSquare_five_…`, quadratic reciprocity `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`, case on `p%5` with `decide` non-residues. **Uses**: [`absNorm_span_natCast`, Common `left_eq_prime_of_mul_eq_prime_sq_of_ne_one`,`isSquare_five_of_absNorm_eq_prime`,`exists_golden_root_of_absNorm_eq_prime`] — **Lines**: 685-730 — **Visibility**: private — **Notes**: proof >40 lines.

### `private theorem exists_golden_root_of_pm_one_mod_five`
- **Type**: `p%5∈{1,4} ⇒ ∃ t:ZMod p, t²=t+1`. **How**: reciprocity gives `IsSquare 5`, set `t=(1+s)/2`. **Uses**: [] — **Lines**: 732-772 — **Visibility**: private — **Notes**: proof >30 lines.

### `private theorem golden_root_ne_one_sub_of_prime_ne_five`
- **Type**: root `t` of `t²=t+1` satisfies `t ≠ 1-t` when `p≠5`. **How**: else `2t=1`, derive `5≡0`. **Uses**: [] — **Lines**: 774-789 — **Visibility**: private

### `private theorem span_prime_golden_sub_ne_of_root`
- **Type**: the two primes `span{p,φ-c}`, `span{p,φ-c'}` are distinct. **How**: inverse mod p (Common `exists_int_inverse_mod_prime`), derive `1∈P`. **Uses**: [`goldenIntO`,`golden_root_ne_one_sub_of_prime_ne_five`, Common `exists_int_inverse_mod_prime`] — **Lines**: 791-836 — **Visibility**: private — **Notes**: proof >40 lines.

### `private theorem span_natCast_eq_mul_span_golden_sub_of_mul`
- **Type**: `span{p} = span{p,φ-c} * span{p,φ-c'}`. **How**: `≤` by `mul_le`+product identity, then `eq_of_le_of_absNorm_eq` on norms `p²`. **Uses**: [`goldenIntO`,`absNorm_span_natCast`, Common `eq_of_le_of_absNorm_eq`] — **Lines**: 838-878 — **Visibility**: private — **Notes**: proof >30 lines.

### `private theorem exists_golden_split_data`
- **Type**: from a root `t` produce integers `c,c',k₁,k₂` with the product factorization. **How**: `ZMod.natCast_rightInverse`, divisibility lifts, `linear_combination goldenIntO_sq`. **Uses**: [`goldenIntO`,`goldenIntO_sq`] — **Lines**: 880-918 — **Visibility**: private — **Notes**: proof >30 lines.

### `private theorem splits_of_pm_one_mod_five`
- **Type**: `p%5∈{1,4} ⇒ ∃ distinct primes P,Q, span{p}=P*Q`. **How**: assemble previous private lemmas. **Uses**: [`goldenIntO`,`exists_golden_root_of_pm_one_mod_five`,`exists_golden_split_data`,`absNorm_span_prime_golden_sub_of_mul`,`span_prime_golden_sub_ne_of_root`,`span_natCast_eq_mul_span_golden_sub_of_mul`] — **Lines**: 920-962 — **Visibility**: private — **Notes**: proof >40 lines.

### `theorem splits_iff_pm_one_mod_five`
- **Type**: for prime `p≠5`: `(∃ distinct primes P,Q with span{p}=P*Q) ↔ p%5∈{1,4}`.
- **What**: quadratic splitting law. **How**: combine `pm_one_mod_five_of_splits` and `splits_of_pm_one_mod_five`. **Uses**: those two — **Lines**: 964-973 — **Notes**: KEY public result.

### `abbrev goldenPolynomialMod`
- **Type**: `(ZMod p)[X] := X²-X-C 1`. **Uses**: [] — **Lines**: 990-991

### `private theorem goldenPolynomialMod_isRoot_iff` / `…_natDegree` / `…_roots_eq_zero_iff_no_root` / `…_no_root_iff_two_or_three_mod_five`
- **Types**: root iff `t²=t+1`; natDegree 2; roots empty iff no solution; no root iff `p%5∈{2,3}`.
- **How**: `Polynomial.natDegree_quadratic`, `mem_roots`, reuse `exists_golden_root_of_pm_one_mod_five` and reciprocity. **Uses**: [`goldenPolynomialMod`,`exists_golden_root_of_pm_one_mod_five`] — **Lines**: 993-1075 — **Visibility**: private — **Notes**: Kummer-Dedekind support; last one proof >30 lines.

### `private theorem goldenIntO_adjoin_eq_top`
- **Type**: `Algebra.adjoin ℤ {goldenIntO} = ⊤`. **How**: pull back from `concreteRingOfIntegers`/`ringOfIntegers_eq` via `aeval`. **Uses**: [`goldenIntO`,`concreteRingOfIntegers`,`ringOfIntegers_eq`,`goldenRoot`] — **Lines**: 1091-1110 — **Visibility**: private — **Notes**: proof >15 lines.

### `private theorem goldenIntO_minpoly`
- **Type**: `minpoly ℤ goldenIntO = X²-X-1`. **How**: `minpoly.isIntegrallyClosed_eq_field_fractions`, map injectivity, `X_pow_sub_X_sub_one_irreducible_rat`. **Uses**: [`goldenIntO`,`goldenRoot(_sq)`] — **Lines**: 1112-1140 — **Visibility**: private — **Notes**: proof >25 lines.

### `theorem differentIdeal_eq_span_sqrtFive`
- **Type**: `differentIdeal ℤ (𝓞 K) = span {sqrtFiveIntO}`. **How**: `conductor_eq_top_of_adjoin_eq_top`, `conductor_mul_differentIdeal`, `aeval` of derivative `2X-1`. **Uses**: [`goldenIntO_adjoin_eq_top`,`goldenIntO_minpoly`,`goldenIntO`,`adjoin_goldenRoot_eq_top`,`sqrtFiveIntO`] — **Lines**: 1142-1161 — **Notes**: KEY; proof >15 lines.

### `theorem absNorm_differentIdeal_eq_five`
- **Type**: `absNorm (differentIdeal ℤ (𝓞 K)) = 5`. **How**: `NumberField.absNorm_differentIdeal` + `numberField_discr_eq`. **Uses**: [`numberField_discr_eq`] — **Lines**: 1163-1166

### `theorem prime_dvd_differentIdeal_iff_eq_span_sqrtFive`
- **Type**: nonzero prime `P ∣ differentIdeal ↔ P = span {sqrtFiveIntO}`. **How**: maximality of `span{sqrtFiveIntO}` (`isMaximal`), `differentIdeal_eq_span_sqrtFive`. **Uses**: [`differentIdeal_eq_span_sqrtFive`,`sqrtFiveIntO`,`sqrtFiveRoot_sq`,`isPrime_span_sqrtFiveIntO`] — **Lines**: 1168-1188 — **Notes**: proof >15 lines.

**File Summary — PrimeSplitting.lean**: ~50 decls (defs/abbrevs 3, theorems ~47, ~22 private). Key API (3+, internal): `goldenIntO_sq`, `absNorm_span_natCast`, `intNorm_eq_normForm` (imported), `exists_golden_root_of_pm_one_mod_five`, `numberField_discr_eq` (imported), `sqrtFiveIntO`. Public results: `span_five_eq`, `ramified_iff_eq_five`, `splits_iff_pm_one_mod_five`, `differentIdeal_eq_span_sqrtFive`, all the per-prime split/inert facts. No sorry. No set_option. >30-line proofs: `isPrime_span_two`, `isPrime_span_three`, `ramified_iff_eq_five`, `absNorm_span_prime_golden_sub_of_mul`, `pm_one_mod_five_of_splits`, `exists_golden_root_of_pm_one_mod_five`, `span_prime_golden_sub_ne_of_root`, `span_natCast_eq_mul_span_golden_sub_of_mul`, `exists_golden_split_data`, `splits_of_pm_one_mod_five`, `goldenPolynomialMod_no_root_iff_…`, `goldenIntO_minpoly`. Heavy reliance on Common.lean.

---

## ClassGroup.lean

### `abbrev goldenRootFractionalIdeal` / `ramifiedPrimeFractionalIdeal`
- **Types**: `spanSingleton goldenRoot`; coe of `span {sqrtFiveIntO}`. **Uses**: [`goldenRoot`,`sqrtFiveIntO`] — **Lines**: 33-37

### `theorem goldenRoot_mem_fractionalIdeal`
- **Type**: `goldenRoot ∈ goldenRootFractionalIdeal`. **How**: `mem_spanSingleton_self`. **Uses**: [`goldenRootFractionalIdeal`,`goldenRoot`] — **Lines**: 39-41

### `theorem goldenRootFractionalIdeal_absNorm`
- **Type**: `absNorm = |Algebra.norm ℚ goldenRoot|`. **How**: `simp`. **Uses**: [`goldenRootFractionalIdeal`,`goldenRoot`] — **Lines**: 43-45

### `theorem ramifiedPrimeFractionalIdeal_ne_zero`
- **Type**: `≠ 0`. **How**: `coeIdeal_ne_zero` + `span_singleton_eq_bot`, `sqrtFiveRoot_sq`. **Uses**: [`ramifiedPrimeFractionalIdeal`,`sqrtFiveIntO`,`sqrtFiveRoot_sq`] — **Lines**: 47-58

### `theorem classNumber_eq_one`
- **Type**: `NumberField.classNumber K = 1`.
- **What**: class number 1 via Minkowski bound `√5/2 < 2`. **How**: `classNumber_eq_one_iff` + `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_…`; bound the Minkowski floor `< 2` with `Real.sqrt 5 < 3`, then `interval_cases`. **Uses**: [`nrComplexPlaces_eq_zero`,`degree_eq_two`,`numberField_discr_eq`] — **Lines**: 76-105 — **Notes**: KEY; proof >25 lines.

### `theorem isPrincipalIdealRing`
- **Type**: `IsPrincipalIdealRing (𝓞 K)`. **How**: `classNumber_eq_one_iff`. **Uses**: [`classNumber_eq_one`] — **Lines**: 107-111 — **Notes**: KEY.

### `theorem uniqueFactorizationMonoid`
- **Type**: `UniqueFactorizationMonoid (𝓞 K)`. **How**: PID ⇒ UFM. **Uses**: [`isPrincipalIdealRing`] — **Lines**: 113-116

### `theorem classGroupStructure`
- **Type**: `Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1))`. **How**: card 1 ⇒ subsingleton ⇒ `MulEquiv.ofUnique`. **Uses**: [`classNumber_eq_one`] — **Lines**: 118-125

### `abbrev unitIdealRepresentative`
- **Type**: `(Ideal (𝓞 K))⁰ := ⟨⊤, …⟩`. **Uses**: [] — **Lines**: 128-129

### `theorem classGroupRepresentative`
- **Type**: `∀ C, C = ClassGroup.mk0 unitIdealRepresentative`. **How**: subsingleton. **Uses**: [`unitIdealRepresentative`,`classNumber_eq_one`] — **Lines**: 131-137

**File Summary — ClassGroup.lean**: 10 decls (abbrevs 3, theorems 7). Key API (3+): `classNumber_eq_one`. No sorry/set_option. >30-line proofs: none (classNumber ~28). The fractional-ideal decls (33-58) are unused downstream.

---

## Units.lean

### `private theorem goldenIntO_sq`
- **Type**: `goldenIntO^2 = goldenIntO + 1`. **Uses**: [`goldenIntO`,`goldenRoot_sq`] — **Lines**: 36-37 — **Visibility**: private — **Notes**: DUPLICATE of the private one in PrimeSplitting.lean.

### `def fundamentalUnit`
- **Type**: `(𝓞 K)ˣ` with `val=goldenIntO`, `inv=goldenIntO-1`. **What**: fundamental unit `φ`. **How**: `goldenIntO_sq`/`ring`. **Uses**: [`goldenIntO`,`goldenIntO_sq`] — **Lines**: 41-51 — **Notes**: KEY (LocalGlobal).

### `abbrev torsionGenerator`
- **Type**: `(𝓞 K)ˣ := -1`. **Uses**: [] — **Lines**: 54

### `def torsionUnits`
- **Type**: `Set ((𝓞 K)ˣ) := {u | ∃ k:Fin 2, u = torsionGenerator^k.val}` = `{1,-1}`. **Uses**: [`torsionGenerator`] — **Lines**: 57

### `private def realEmb`
- **Type**: `K →ₐ[ℚ] ℝ`. **What**: real embedding sending `φ ↦ (1+√5)/2`. **How**: `QuadraticAlgebra.lift`, `Real.mul_self_sqrt`. **Uses**: [] — **Lines**: 59-65 — **Visibility**: private — **Notes**: same construction as `exists_realEmbedding_goldenRatio` in Embeddings.

### `theorem torsionUnits_eq`
- **Type**: `{u | IsOfFinOrder u} = torsionUnits`. **How**: finite-order unit ⇒ `|e(x)|=1` (real embedding) ⇒ `±1`; uses `IsFractionRing.injective`, `pow_lt_one₀`/`one_lt_pow₀`. **Uses**: [`realEmb`,`torsionUnits`,`torsionGenerator`] — **Lines**: 68-114 — **Notes**: KEY; proof >40 lines.

### `theorem torsionOrder_eq_two`
- **Type**: `Units.torsionOrder K = 2`. **How**: `Nat.card (torsion K) = 2` via `Nat.card_eq_two_iff` and `torsionUnits_eq`. **Uses**: [`torsionUnits_eq`] — **Lines**: 116-144 — **Notes**: KEY; proof >25 lines.

### `theorem unitRank_eq_one`
- **Type**: `Units.rank K = 1`. **How**: rank `= card places - 1`, `nrRealPlaces_eq_two`/`nrComplexPlaces_eq_zero`. **Uses**: [`nrRealPlaces_eq_two`,`nrComplexPlaces_eq_zero`] — **Lines**: 146-150 — **Notes**: KEY.

### `def fundamentalUnitSystem`
- **Type**: `Fin (Units.rank K) → (𝓞 K)ˣ := fun _ => fundamentalUnit`. **Uses**: [`fundamentalUnit`] — **Lines**: 153-154

### `theorem intNorm_goldenInt`
- **Type**: `Algebra.norm ℤ goldenIntO = -1`. **How**: `intNorm_eq_normForm 0 1`. **Uses**: [`goldenIntO`,`intNorm_eq_normForm`] — **Lines**: 156-159 — **Notes**: KEY (the norm is `-1`, so `φ` has norm `-1`).

### `private theorem normFundamentalUnit_map` / `normNegOneUnit_map`
- **Types**: `Units.map (norm) fundamentalUnit = -1`; `…(-1) = 1`. **How**: `Units.ext` + `intNorm_goldenInt`/`intNorm_eq_normForm (-1) 0`. **Uses**: [`fundamentalUnit`,`goldenIntO`,`intNorm_goldenInt`,`intNorm_eq_normForm`] — **Lines**: 161-177 — **Visibility**: private

### `private theorem even_of_negOneUnit_zpow_eq_one`
- **Type**: `(-1:ℤˣ)^n = 1 → ∃k, n=2k`. **How**: parity, `Odd.neg_one_zpow`. **Uses**: [] — **Lines**: 179-189 — **Visibility**: private — **Notes**: generic.

### `private theorem normFundamentalUnit_zpow_map` / `normNegFundamentalUnit_zpow_map`
- **Types**: norm of `φⁿ` (resp `-(φⁿ)`) `= (-1)ⁿ`. **How**: `map_zpow`. **Uses**: [`fundamentalUnit`,`normFundamentalUnit_map`,`normNegOneUnit_map`] — **Lines**: 191-203 — **Visibility**: private

### `theorem exists_eq_torsion_mul_fundSystem_zpow`
- **Type**: any unit `u = ζ * fundSystem K i₀ ^ n`, `ζ` torsion. **How**: `closure_fundSystem_sup_torsion_eq_top`, `Subgroup.mem_sup`, subsingleton of `Fin (rank)`. **Uses**: [`unitRank_eq_one`] — **Lines**: 207-229 — **Notes**: proof >20 lines.

### `theorem fundSystem_zpow_mem_torsion`
- **Type**: `fundSystem K i₀ ^ n` torsion ⇒ `n=0`. **How**: quotient by torsion is free, `basisModTorsion.repr`. **Uses**: [] — **Lines**: 231-248 — **Notes**: proof >15 lines.

### `theorem eq_one_or_neg_one_of_mem_torsion`
- **Type**: `ζ ∈ torsion ⇒ ζ = 1 ∨ ζ = -1`. **How**: `torsionUnits_eq`. **Uses**: [`torsionUnits_eq`] — **Lines**: 250-259

### `theorem fundamentalUnit_generates`  ⚠ SORRY
- **Type**: `∀ u:(𝓞 K)ˣ, ∃ n, u = φⁿ ∨ u = -(φⁿ)`.
- **What**: every unit is a signed power of `φ`. **How**: SORRY. **Uses**: [`fundamentalUnit`] — **Lines**: 261-269 — **Visibility**: public
- **Notes**: **SORRY** — blocked: no bridge from the Fibonacci/Pell-±4 equation `x²+xy-y²=±1` (half-integral order `ℤ[(1+√5)/2]`) to the displayed `φ`. SqrtTwo solves the analogue via `Zsqrtd`/`Pell.Solution₁`. This sorry is the load-bearing assumption beneath the rest of the unit-group results.

### `theorem fundamentalUnitSystem_isFundamental`
- **Type**: `closure (range fundamentalUnitSystem) ⊔ torsion K = ⊤`. **How**: `fundamentalUnit_generates` + membership bookkeeping. **Uses**: [`fundamentalUnit`,`fundamentalUnitSystem`,`unitRank_eq_one`,`fundamentalUnit_generates`] — **Lines**: 271-293 — **Notes**: depends transitively on the sorry.

### `theorem unit_eq_torsion_mul_fundamentalUnit_zpow`
- **Type**: `u = ζ * φⁿ`, ζ torsion. **How**: `fundamentalUnit_generates`. **Uses**: [`fundamentalUnit`,`fundamentalUnit_generates`] — **Lines**: 295-304 — **Notes**: depends on sorry.

### `theorem normOneUnit_generated_by_fundamentalUnit_sq`
- **Type**: norm-1 units `= ±φ^(2n)`. **How**: `fundamentalUnit_generates` + `even_of_negOneUnit_zpow_eq_one`. **Uses**: [`fundamentalUnit`,`fundamentalUnit_generates`,`normFundamentalUnit_zpow_map`,`normNegFundamentalUnit_zpow_map`,`even_of_negOneUnit_zpow_eq_one`] — **Lines**: 306-324 — **Notes**: depends on sorry.

### `theorem regulator_eq`  ⚠ SORRY
- **Type**: `Units.regulator K = Real.log ((1+√5)/2)`.
- **What**: the regulator is `log φ`. **How**: SORRY. **Uses**: [] — **Lines**: 326-332 — **Visibility**: public
- **Notes**: **SORRY** — intentionally the final theorem; needs the analytic statement that `φ` is fundamental (Artin-type unit bound), unproved in the project.

### `private theorem unitGroupStructure_bijective`
- **Type**: the coproduct map `(torsionPowerHom 2 (-1)).coprod (rankOnePowerHom η)` is bijective.
- **How**: injectivity via `fundSystem_zpow_mem_torsion`; surjectivity via `exists_eq_torsion_mul_fundSystem_zpow` + `eq_one_or_neg_one_of_mem_torsion`. **Uses**: [`fundSystem_zpow_mem_torsion`,`exists_eq_torsion_mul_fundSystem_zpow`,`eq_one_or_neg_one_of_mem_torsion`, Common `torsionPowerHom`,`rankOnePowerHom`] — **Lines**: 334-378 — **Visibility**: private — **Notes**: proof >40 lines.

### `theorem unitGroupStructure`
- **Type**: `Nonempty ((𝓞 K)ˣ ≃* Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ))`.
- **What**: unit group `≅ μ₂ × ℤ`. **How**: `MulEquiv.ofBijective` of `unitGroupStructure_bijective`. **Uses**: [`unitRank_eq_one`,`unitGroupStructure_bijective`, Common `torsionPowerHom`,`rankOnePowerHom`] — **Lines**: 380-397 — **Notes**: KEY public result; proof >15 lines. Independent of the sorry (uses mathlib's abstract fundSystem, not `fundamentalUnit_generates`).

**File Summary — Units.lean**: ~22 decls (defs/abbrevs 4, theorems ~17, 1 private def). Key API (3+): `fundamentalUnit`, `torsionUnits_eq`, `unitRank_eq_one`, `fundamentalUnit_generates`, `goldenIntO_sq`. **SORRY ×2**: `fundamentalUnit_generates`, `regulator_eq`. No set_option. >30-line proofs: `torsionUnits_eq`, `unitGroupStructure_bijective`. The "Regulator" section at the end is empty.

---

## Euclidean.lean

### `private theorem abs_norm_int_lt_of_remainder_eq`
- **Type**: given remainder identity and `|norm-form of fractional part| ≤ 3/4` and `0 < |norm bK|`, then `|norm r| < |norm b|`.
- **How**: `Algebra.coe_norm_int`, `norm_eq_normForm`, `abs_mul`, `mul_le_mul_of_nonneg_left`, `linarith`. **Uses**: [`norm_eq_normForm`,`goldenRoot`] — **Lines**: 35-57 — **Visibility**: private — **Notes**: twin of SqrtTwo's `abs_norm_int_lt_of_remainder_eq` (its version has extra `e` arg for the `2` shift).

### `theorem normEuclidean`
- **Type**: `∀ a b, b≠0 → ∃ q r, a = b*q + r ∧ (norm r).natAbs < (norm b).natAbs`.
- **What**: `ℤ[φ]` is norm-Euclidean. **How**: round real/imag coords of `a/b`; the fractional-part norm form `|s²+st-t²| ≤ 3/4` (from `|s|,|t| ≤ 1/2`, `nlinarith`), then `abs_norm_int_lt_of_remainder_eq` + Common `natAbs_lt_of_abs_ratCast_lt`. **Uses**: [`goldenIntO`,`goldenRoot`,`norm_eq_normForm` (via helper),`abs_norm_int_lt_of_remainder_eq`, Common `natAbs_lt_of_abs_ratCast_lt`] — **Lines**: 59-100 — **Notes**: KEY public result; proof >30 lines. (3/4 bound is specific to disc-5 form; SqrtTwo uses a 1/2-style bound.)

**File Summary — Euclidean.lean**: 2 decls (1 private helper + `normEuclidean`). Key API: `normEuclidean`. No sorry/set_option. >30-line proofs: `normEuclidean`. The helper is a generic norm-shrinking lemma; near-identical to SqrtTwo.

---

## LocalGlobal.lean

### `def heightOneFive`
- **Type**: `HeightOneSpectrum (𝓞 K)` = the ramified prime `(√5)`. **How**: fields via `isPrime_span_sqrtFiveIntO` and nonzero via `sqrtFiveRoot_sq`. **Uses**: [`sqrtFiveIntO`,`isPrime_span_sqrtFiveIntO`,`sqrtFiveRoot_sq`,`goldenRoot`] — **Lines**: 37-50

### `abbrev vFive`
- **Type**: `FinitePlace K := FinitePlace.mk heightOneFive`. **Uses**: [`heightOneFive`] — **Lines**: 53-54

### two `example`s (ramIdx 2, inertiaDeg 1 at `heightOneFive`)
- **Uses**: [`ramificationIdx_span_sqrtFiveIntO`,`inertiaDeg_span_sqrtFiveIntO`,`heightOneFive`] — **Lines**: 56-62

### `abbrev CompletionAtFive`
- **Type**: `heightOneFive.adicCompletion K`. **Uses**: [`heightOneFive`] — **Lines**: 77-79

### `abbrev InfiniteCompletion` + `example` (`≃+* ℝ`)
- **Type**: `(v) → v.Completion`; example uses `ringEquivRealOfIsReal (infinitePlace_isReal v)`. **Uses**: [`infinitePlace_isReal`] — **Lines**: 92-97

### two product-formula `example`s (for `goldenRoot`, `fundamentalUnit`)
- **How**: `NumberField.prod_abs_eq_one` (nonzero via `goldenRoot_sq` / `Units.ne_zero`). **Uses**: [`goldenRoot(_sq)`,`fundamentalUnit`] — **Lines**: 111-128

### `abbrev SqrtFiveInfiniteAdeleRing` / `infinitePrincipalAdele_goldenRoot` / `…_fundamentalUnit` + 2 `example`s
- **Types**: infinite adele ring abbrevs; examples = norm equality and dense range. **Uses**: [`goldenRoot`,`fundamentalUnit`] — **Lines**: 142-157

### `theorem canonicalEmbedding_goldenIntO_mem_integerLattice`
- **Type**: `canonicalEmbedding K (algebraMap goldenIntO) ∈ integerLattice K`. **How**: `simp`. **Uses**: [`goldenIntO`] — **Lines**: 171-174

### `abbrev mixedEmbedding_goldenRoot`
- **Type**: `mixedSpace K`. **Uses**: [`goldenRoot`] — **Lines**: 190-191

### `theorem mixedEmbedding_goldenRoot_mem_convexBodyLT`
- **Type**: membership in `convexBodyLT K f` under coordinate bounds. **How**: unfold prod/pi memberships; all places real via `infinitePlace_isReal`. **Uses**: [`mixedEmbedding_goldenRoot`,`goldenRoot`,`infinitePlace_isReal`] — **Lines**: 193-208 — **Notes**: proof >15 lines.

### two `example`s (measurable fundamentalCone, normLeOne) + `theorem polarSpace_nonempty`
- **How**: mathlib lemmas / `infer_instance`. **Uses**: [] — **Lines**: 210-219

### `example` (`0 < house goldenRoot`) + `theorem house_fundamentalUnit`
- **Type**: `house (algebraMap fundamentalUnit) = (1+√5)/2`.
- **How**: each embedding sends `φ` to `(1±√5)/2`; bound conjugate norm `≤ (1+√5)/2`; lower bound from `exists_realEmbedding_goldenRatio`; `canonicalEmbedding.norm_le_iff`, `norm_le_pi_norm`. **Uses**: [`goldenRoot(_sq)(_isIntegral)`,`fundamentalUnit`,`exists_realEmbedding_goldenRatio`] — **Lines**: 234-296 — **Notes**: proof >40 lines.

### `abbrev SqrtFiveAdeleRing` / `principalAdele_goldenRoot` / `…_fundamentalUnit`
- **Types**: full adele ring abbrevs. **Uses**: [`goldenRoot`,`fundamentalUnit`] — **Lines**: 310-317

### `theorem principalAdele_goldenRoot_ne_zero`
- **Type**: `≠ 0`. **How**: `AdeleRing.algebraMap_injective` + `goldenRoot_sq`. **Uses**: [`principalAdele_goldenRoot`,`goldenRoot(_sq)`] — **Lines**: 319-325

### `theorem principalAdele_fundamentalUnit_is_unit_everywhere`
- **Type**: `∀ v finite place, v(fundamentalUnit) = 1`. **How**: `norm_eq_one_iff_notMem`; unit inverse forces `1 ∈ maximalIdeal`, contradiction. **Uses**: [`fundamentalUnit`] — **Lines**: 327-346 — **Notes**: proof >15 lines.

### `abbrev sqrtFiveDedekindZeta` / `sqrtFiveDedekindZetaResidue` + 2 `example`s
- **Types**: zeta abbrevs; examples: residue positive, residue formula (involves `regulator`, `classNumber`, `torsionOrder`, `discr`). **Uses**: [] — **Lines**: 360-376

**File Summary — LocalGlobal.lean**: ~30 decls (mostly abbrevs + `example`s; ~7 named theorems). Key API: `heightOneFive`, `house_fundamentalUnit`. No sorry/set_option. >30-line proofs: `house_fundamentalUnit`. Many `example`s are smoke-tests of mathlib API rather than reusable lemmas.

---

## Cross-file notes

- **Duplicate**: `private theorem goldenIntO_sq` appears identically in PrimeSplitting.lean (117-118) and Units.lean (36-37). Should be a single public lemma in RingOfIntegers.lean.
- **Generic helpers that could move to Common.lean / mathlib**:
  - `ringHom_ext_golden` (Embeddings) — `QuadraticAlgebra` ring-hom extensionality on the generator.
  - `int_eq_of_rat_div_five_eq`, `int_eq_of_rat_div_twentyFive_eq` (RingOfIntegers) — pure ℤ/ℚ arithmetic.
  - `five_dvd_coords_of_trace_norm` (RingOfIntegers) — generic divisibility-from-trace/norm shape.
  - `even_of_negOneUnit_zpow_eq_one` (Units) — `(-1:ℤˣ)^n=1 → Even n`; fully generic.
  - `absNorm_ne_two` / `absNorm_ne_three` (PrimeSplitting) — could be one parametrized lemma.
  - `abs_norm_int_lt_of_remainder_eq` (Euclidean) — already a twin in SqrtTwo; candidate for a shared real-quadratic Euclidean helper.
- **Twin with SqrtTwo** (near-identical names/roles): `K`, `degree_eq_two`, `isTotallyReal`, `nrRealPlaces_eq_two`, `nrComplexPlaces_eq_zero`, `norm_eq_normForm`, `intNorm_eq_normForm`, `isUnit_iff_normForm`, `integralBasis_discr`, `abs_norm_int_lt_of_remainder_eq`, `normEuclidean`, `unitGroupStructure`, the whole prime-splitting / local-global scaffolding. The mathematical content differs (golden vs radical model; disc 5 vs 8; norm form `x²+xy-y²` vs `x²-2y²`; 5 ramified+`±1 mod 5` splitting vs 2 ramified). SqrtTwo additionally completes the `fundamentalUnit_generates` analogue via `Pell.Solution₁`/`Zsqrtd`, which is exactly the SqrtFive sorry.
