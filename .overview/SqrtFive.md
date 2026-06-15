# SqrtFive declaration inventory

Folder: `XYin/NumberField/FieldExamples/SqrtFive/`
Field: real quadratic `ℚ(√5)`, built via `QuadraticAlgebra ℚ 1 1` (golden-ratio model, generator
`φ` with `φ² = φ + 1`). Ring of integers `ℤ[φ] = ℤ[(1+√5)/2]`, disc `5` (smallest of any real
quadratic field). Twin of SqrtTwo (`QuadraticAlgebra ℚ 2 0`); SqrtFive additionally carries a
`RadicalModel = QuadraticAlgebra ℚ 5 0` (generator `√5`) and an `AdjoinRoot (X²-5)` presentation,
plus the golden `AdjoinRoot (X²-X-1)` presentation, all proved equivalent.
Namespace throughout: `NumberField.SqrtFive`. Files open `QuadraticAlgebra`, `NumberField`,
`Module`, `Polynomial` (and `NumberField.FieldExamples` = Common where relevant). All core files
are `noncomputable section` and remove `DivisionRing.toRatAlgebra`.
Cross-reference — `Common.lean` API used: `eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq`,
`left_eq_prime_of_mul_eq_prime_sq_of_ne_one`, `exists_int_inverse_mod_prime`,
`eq_of_le_of_absNorm_eq`, `natAbs_lt_of_abs_ratCast_lt`, `torsionPowerHom`, `rankOnePowerHom`,
`abs_intNorm_lt_of_abs_norm_le`, `not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ`,
`not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow`.
**Sorry-free** (as of the 2026-06-15 update). The two former Units.lean sorries are now **closed**.
`fundamentalUnit_generates` is proved by a self-contained **real-embedding window-reduction**
argument: every unit maps under `reEmb : ℚ(√5) → ℝ` (sending `φ ↦ Φ = (1+√5)/2`); a power of `φ`
reduces it into the window `[1, Φ)`; and the norm form `x²+xy−y² = ±1` (`isUnit_iff_normForm`) forces
the only unit there to be `1`. This is the standard textbook proof, formalised faithfully — it does
**not** use the `Zsqrtd`/`Pell` `x²−5y²=1` machinery (which only covers the index-2 suborder
`ℤ[√5]`), and needs **no missing API**. `regulator_eq` then follows from mature mathlib API
(`regOfFamily_div_regulator` → `regOfFamily_eq_det` → `Matrix.det_eq_elem_of_subsingleton`). SqrtFive
is the proof that, for a real quadratic field, "this explicit unit is fundamental" is a matter of
*intrinsic mathematical work*, not API immaturity.

---

## Basic.lean

### `instance Fact (∀ r : ℚ, r² ≠ 1 + 1·r)`
- **Type**: `Fact (∀ r : ℚ, r ^ 2 ≠ (1 : ℚ) + (1 : ℚ) * r)`
- **What**: `X²-X-1` has no rational root; data instance feeding `QuadraticAlgebra` that the field is genuinely degree 2.
- **How**: from `r²=r+1` build `IsSquare (5:ℚ)` via `2r-1`, contradiction by `norm_num`.
- **Uses from project**: [] — **Visibility**: public (instance) — **Lines**: 34-41

### `abbrev K`
- **Type**: `K : Type := QuadraticAlgebra ℚ (1:ℚ) (1:ℚ)` — **What**: the field `ℚ(√5)`. — **How**: definitional. — **Uses**: [] — public — **Lines**: 44

### `instance FiniteDimensional ℚ K`
- **How**: `QuadraticAlgebra.basis (1) (1) |>.finiteDimensional_of_finite`. — **Uses**: [] — public — **Lines**: 46-47

### `instance NumberField K`
- **How**: `NumberField.of_module_finite ℚ K`. — **Uses**: [] — public — **Lines**: 49-50

### `theorem degree_eq_two`
- **Type**: `Module.finrank ℚ K = 2` — **How**: `finrank_eq_card_basis` + `Fintype.card_fin`.
- **Uses**: [] — public — **Lines**: 52-55 — **Notes**: heavily-used API (≈10 references across folder).

### `instance Algebra.IsQuadraticExtension ℚ K`
- **How**: `finrank_eq_two' := degree_eq_two`. — **Uses**: [degree_eq_two] — public — **Lines**: 57-59

### `abbrev goldenRoot`
- **Type**: `goldenRoot : K := QuadraticAlgebra.omega` — **What**: distinguished `φ`. — **Uses**: [] — public — **Lines**: 62
- **Notes**: THE central generator (≈40 references across folder).

### `theorem goldenRoot_sq`
- **Type**: `goldenRoot ^ 2 = goldenRoot + 1` — **How**: `change` to `⟨0,1⟩`, `ext`/`simp [pow_two]`.
- **Uses**: [goldenRoot] — public — **Lines**: 64-66 — **Notes**: most-used identity in folder.

### `abbrev goldenPolynomial`
- **Type**: `ℚ[X] := C 1·X² + C(-1)·X + C(-1)` — **What**: defining poly `X²-X-1`. — **Uses**: [] — public — **Lines**: 69-70

### `instance Fact (Irreducible goldenPolynomial)`
- **How**: `Polynomial.X_pow_sub_X_sub_one_irreducible_rat (n:=2)` + `simpa`. — **Uses**: [goldenPolynomial] — public — **Lines**: 72-76

### `abbrev KAdjoinRoot`
- **Type**: `:= AdjoinRoot goldenPolynomial` — AdjoinRoot presentation. — **Uses**: [goldenPolynomial] — public — **Lines**: 79

### `abbrev goldenAdjoinRoot`
- **Type**: `KAdjoinRoot := AdjoinRoot.root goldenPolynomial` — **Uses**: [goldenPolynomial] — public — **Lines**: 82

### `theorem goldenAdjoinRoot_sq`
- **Type**: `goldenAdjoinRoot ^ 2 = goldenAdjoinRoot + 1` — **How**: `AdjoinRoot.eval₂_root` + `linear_combination`. — **Uses**: [goldenAdjoinRoot, goldenPolynomial] — public — **Lines**: 84-88

### `def goldenAdjoinRootEquivGolden`
- **Type**: `KAdjoinRoot ≃ₐ[ℚ] K` — **What**: AdjoinRoot ≅ QuadraticAlgebra model. **How**: fwd `AdjoinRoot.liftAlgHom`, back `QuadraticAlgebra.lift`; `algHom_ext`+`DFunLike.congr_fun`.
- **Uses**: [goldenPolynomial, goldenRoot, goldenRoot_sq, goldenAdjoinRoot, goldenAdjoinRoot_sq] — public — **Lines**: 91-113 — **Notes**: proof ≈23 lines.

### `theorem goldenAdjoinRootEquivGolden_root`
- **Type**: `... goldenAdjoinRoot = goldenRoot` — **How**: simp. — **Uses**: [goldenAdjoinRootEquivGolden, goldenAdjoinRoot, goldenRoot] — public — **Lines**: 115-117

### `abbrev sqrtFiveRoot`
- **Type**: `K := 2 * goldenRoot - 1` — **What**: `√5 = 2φ - 1`. — **Uses**: [goldenRoot] — public — **Lines**: 120
- **Notes**: key API (used 6+ times incl. ramification, conjugation).

### `theorem sqrtFiveRoot_sq`
- **Type**: `sqrtFiveRoot ^ 2 = (5 : K)` — **How**: `calc` expand + `goldenRoot_sq` + `ring`. — **Uses**: [sqrtFiveRoot, goldenRoot_sq] — public — **Lines**: 122-126 — **Notes**: reused throughout PrimeSplitting/ClassGroup/LocalGlobal.

### `theorem goldenRoot_eq_half_sqrtFiveRoot_add_one`
- **Type**: `goldenRoot = (sqrtFiveRoot + 1) / 2` — **How**: `field_simp`/`ring`. — **Uses**: [sqrtFiveRoot] — public — **Lines**: 128-132

### `theorem goldenRoot_isIntegral`
- **Type**: `IsIntegral ℤ goldenRoot` — **How**: witness `X²-X-1`, `monicity`, `simp [goldenRoot_sq]`. — **Uses**: [goldenRoot_sq] — public — **Lines**: 134-138 — **Notes**: key API (used 8+ times).

### `instance Fact (∀ r : ℚ, r² ≠ 5 + 0·r)`
- **What**: `5` not a rational square (for `RadicalModel`). **How**: `IsSquare (5:ℚ)`, `norm_num`. — **Uses**: [] — public — **Lines**: 140-147

### `abbrev RadicalModel`
- **Type**: `:= QuadraticAlgebra ℚ (5:ℚ) 0` — **What**: `√5`-generator presentation. — **Uses**: [] — public — **Lines**: 150

### `abbrev sqrtFiveRadicalRoot` / `theorem sqrtFiveRadicalRoot_sq`
- `RadicalModel := QuadraticAlgebra.omega`; `^2 = 5`. **How**: `change`/`ext`/`simp`. — **Uses**: [] — public — **Lines**: 153 / 155-158

### `abbrev sqrtFive` / `theorem sqrtFive_sq`
- `RadicalModel := sqrtFiveRadicalRoot`; `^2 = 5`. — **Uses**: [sqrtFiveRadicalRoot(_sq)] — public — **Lines**: 161 / 163-164

### `abbrev goldenRadicalRoot` / `theorem goldenRadicalRoot_sq`
- `(1+√5)/2` in radical model; `^2 = ·+1`. **How**: `field_simp`+`linear_combination sqrtFive_sq`. — **Uses**: [sqrtFive_sq] — public — **Lines**: 167 / 169-173

### `abbrev sqrtFivePolynomial`
- **Type**: `ℚ[X] := X² - C 5` — defining poly of `√5`. — **Uses**: [] — public — **Lines**: 176-177

### `abbrev RadicalAdjoinRoot` / `abbrev sqrtFiveAdjoinRoot` / `theorem sqrtFiveAdjoinRoot_sq`
- `:= AdjoinRoot sqrtFivePolynomial`; root; `root²=5` via `AdjoinRoot.eval₂_root`. — **Uses**: [sqrtFivePolynomial] — public — **Lines**: 180 / 183 / 185-190

### `private def sqrtFiveAdjoinRootToRadical` / `private theorem sqrtFiveAdjoinRootToRadical_root`
- `RadicalAdjoinRoot →ₐ[ℚ] RadicalModel` (`√5↦√5`); `AdjoinRoot.liftAlgHom`(_root). — **Uses**: [sqrtFivePolynomial, sqrtFive(_sq), sqrtFiveAdjoinRoot] — private — **Lines**: 192-197 / 199-202

### `private def sqrtFiveRadicalToAdjoinRoot` / `private theorem sqrtFiveRadicalToAdjoinRoot_root`
- `RadicalModel →ₐ[ℚ] RadicalAdjoinRoot`; `QuadraticAlgebra.lift`. — **Uses**: [sqrtFiveAdjoinRoot(_sq), sqrtFive…] — private — **Lines**: 204-207 / 209-214

### `def sqrtFiveRadicalEquivAdjoinRoot` / `theorem sqrtFiveRadicalEquivAdjoinRoot_root`
- `RadicalModel ≃ₐ[ℚ] RadicalAdjoinRoot`; assembles fwd/back, `algHom_ext`+`DFunLike`. — **Uses**: [the four maps + `_root` lemmas] — public — **Lines**: 217-240 / 242-244 — **Notes**: proof ≈24 lines.

### `def sqrtFiveRadicalToGolden` / `theorem sqrtFiveRadicalToGolden_root` (@[simp])
- `RadicalModel →ₐ[ℚ] K` (`√5↦2φ-1`); `QuadraticAlgebra.lift` w/ `sqrtFiveRoot_sq`. — **Uses**: [sqrtFiveRoot(_sq), sqrtFiveRadicalRoot] — public — **Lines**: 247-250 / 252-255

### `def goldenToSqrtFiveRadical` / `theorem goldenToSqrtFiveRadical_root` (@[simp])
- `K →ₐ[ℚ] RadicalModel` (`φ↦(√5+1)/2`); `QuadraticAlgebra.lift`, relation via `calc`+`sqrtFiveRadicalRoot_sq`. — **Uses**: [sqrtFiveRadicalRoot(_sq), goldenRoot] — public — **Lines**: 258-266 / 268-271

### `def sqrtFiveRadicalEquivGolden` / `_root` / `_symm_root`
- `RadicalModel ≃ₐ[ℚ] K` + apply/symm-apply lemmas. **How**: fwd/back homs, `algHom_ext`+`DFunLike`, `goldenRoot_eq_half_sqrtFiveRoot_add_one`. — **Uses**: [sqrtFiveRadicalToGolden, goldenToSqrtFiveRadical, …] — public — **Lines**: 274-301 / 303-305 / 307-309 — **Notes**: proof ≈28 lines.

### `def sqrtFiveAdjoinRootEquivGolden` / `theorem sqrtFiveAdjoinRootEquivGolden_root`
- `RadicalAdjoinRoot ≃ₐ[ℚ] K := …EquivAdjoinRoot.symm.trans …EquivGolden`; `_root` via `AlgEquiv.trans_apply`. — **Uses**: [sqrtFiveRadicalEquivAdjoinRoot, sqrtFiveRadicalEquivGolden, sqrtFiveAdjoinRoot, sqrtFive…] — public — **Lines**: 312-313 / 315-321

**File Summary (Basic.lean)**: ~33 decls (3 Fact/2 plain instances, ~9 defs, ~14 theorems, ~12
abbrevs). Key API (3+ uses): `goldenRoot`, `goldenRoot_sq`, `sqrtFiveRoot`, `sqrtFiveRoot_sq`,
`goldenRoot_isIntegral`, `degree_eq_two`. The entire `RadicalModel`/`RadicalAdjoinRoot`
equivalence block (lines 150-321) is self-contained presentation machinery, **never referenced by
any sibling file** (the field is used via the `QuadraticAlgebra ℚ 1 1` golden model directly). No
sorry, no set_option. Longest proofs ≈28 lines (`sqrtFiveRadicalEquivGolden`),
≈24 (`sqrtFiveRadicalEquivAdjoinRoot`), ≈23 (`goldenAdjoinRootEquivGolden`).

---

## Galois.lean

### `private def conjHom`
- **Type**: `K →ₐ[ℚ] K` (`φ ↦ 1 - φ`) — **How**: `QuadraticAlgebra.lift` with `(1-φ)²=1-2φ+φ²`, `goldenRoot_sq`. — **Uses**: [goldenRoot, goldenRoot_sq] — private — **Lines**: 34-40

### `private theorem conjHom_root` / `private theorem conjHom_comp`
- `conjHom φ = 1-φ`; `conjHom.comp conjHom = id` via `QuadraticAlgebra.algHom_ext`. — **Uses**: [conjHom, goldenRoot] — private — **Lines**: 42-43 / 45-49

### `def conjugation`
- **Type**: `K ≃ₐ[ℚ] K` — involutive conjugation. **How**: `invFun := conjHom`, `left/right_inv` from `conjHom_comp`. — **Uses**: [conjHom, conjHom_comp] — public — **Lines**: 51-55 — **Notes**: key API across Galois/Embeddings.

### `private theorem conjugation_root`
- `conjugation φ = 1-φ := conjHom_root`. — **Uses**: [conjugation, conjHom_root] — private — **Lines**: 57-58

### `def idAut`
- **Type**: `K ≃ₐ[ℚ] K := AlgEquiv.refl`. — **Uses**: [] — public — **Lines**: 60

### `theorem conjugation_apply_goldenRoot`
- `conjugation φ = 1 - φ` (public restatement). — **Uses**: [conjugation_root] — public — **Lines**: 62-64

### `theorem conjugation_apply_sqrtFiveRoot`
- `conjugation (√5) = -√5` — **How**: `map_sub`/`map_mul` + `conjugation_apply_goldenRoot` + `ring`. — **Uses**: [sqrtFiveRoot, conjugation, conjugation_apply_goldenRoot] — public — **Lines**: 66-69

### `theorem exists_conj`
- `∃ σ : K ≃ₐ[ℚ] K, σ φ = 1-φ` — **How**: `⟨conjugation, conjugation_root⟩`. — **Uses**: [conjugation, conjugation_root, goldenRoot] — public — **Lines**: 71-75

### `theorem aut_apply_goldenRoot`
- **Type**: `(σ) → σφ = φ ∨ σφ = 1-φ` — **What**: classifies action on generator. **How**: `σφ` satisfies `x²=x+1`; factor `(σφ-φ)(σφ-(1-φ))=0` by `linear_combination`. — **Uses**: [goldenRoot_sq] — public — **Lines**: 77-88

### `theorem aut_eq_or`
- **Type**: `(σ) → σ = idAut ∨ σ = conjugation` — **How**: `QuadraticAlgebra.algHom_ext` ⇒ determined by image of `φ`; case-split `aut_apply_goldenRoot`. — **Uses**: [idAut, conjugation, conjugation_root, aut_apply_goldenRoot] — public — **Lines**: 90-100

### `theorem isGalois`
- `IsGalois ℚ K` — **How**: `infer_instance` (quadratic char-0 ⇒ Galois). — **Uses**: [] — public — **Lines**: 102-105

### `theorem galoisGroupStructure`
- **Type**: `Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2))` — **How**: `conjugation ≠ idAut` (else `2φ=1`, check `im`); `Nat.card_eq_two_iff` from `aut_eq_or`; `mulEquivOfPrimeCardEq` + `Nat.card_zmod`. — **Uses**: [conjugation, idAut, conjugation_root, goldenRoot, aut_eq_or] — public — **Lines**: 107-126 — **Notes**: proof ≈18 lines; **differs from SqrtTwo** which routes through `zmodAddEquivOfGenerator`/`AddEquiv.toMultiplicativeLeft` (shared infra) — here a direct `mulEquivOfPrimeCardEq`.

**File Summary (Galois.lean)**: 13 decls (2 defs + `idAut`, ~8 theorems, conjHom internals).
Key API (3+ uses): `conjugation`, `conjugation_apply_goldenRoot`, `aut_eq_or`. Public results:
`isGalois`, `galoisGroupStructure`, `exists_conj`. No sorry/set_option. No proof >30 lines (longest
`galoisGroupStructure` ≈18). `conjugation` double-uses `conjHom_comp` in both `left_inv`/`right_inv`
(mild duplication, identical to SqrtTwo).

---

## Embeddings.lean

### `private theorem ringHom_ext_golden`
- **Type**: `{f g : K →+* ℂ} (h : f φ = g φ) → f = g` — **What**: ring homs to ℂ determined by image of `φ`. **How**: `QuadraticAlgebra.mk_eq_add_smul_omega`, `eq_ratCast` on ℚ-part. — **Uses**: [goldenRoot] — private — **Lines**: 34-45 — **Notes**: GENERIC; a quadratic-algebra `ringHom_ext` candidate for Common (twin of SqrtTwo's `ringHom_ext_sqrtTwo`).

### `theorem isTotallyReal`
- **Type**: `NumberField.IsTotallyReal K` — **How**: each embedding fixes `φ` under conjugation (factor `(z̄-z)(z̄+z-1)=0`); exclude `re=1/2` branch by `nlinarith [sq_nonneg z.im]`. — **Uses**: [goldenRoot_sq, ringHom_ext_golden] — public — **Lines**: 47-70 — **Notes**: proof ≈24 lines; the `re=1/2` exclusion is the golden-ratio analogue of SqrtTwo's `re=0`.

### `theorem nrRealPlaces_eq_two`
- `InfinitePlace.nrRealPlaces K = 2` — **How**: `IsTotallyReal.nrComplexPlaces_eq_zero` + `card_add_two_mul_card_eq_rank` + `degree_eq_two`, `omega`. — **Uses**: [isTotallyReal, degree_eq_two] — public — **Lines**: 72-77 — **Notes**: used in Embeddings/Units/ClassGroup.

### `theorem nrComplexPlaces_eq_zero`
- `= 0` — **How**: `IsTotallyReal.nrComplexPlaces_eq_zero`. — **Uses**: [isTotallyReal] — public — **Lines**: 79-81 — **Notes**: used 3+ times.

### `theorem infinitePlace_card_eq_two`
- `Fintype.card (InfinitePlace K) = 2` — **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces` + the two counts. — **Uses**: [nrRealPlaces_eq_two, nrComplexPlaces_eq_zero] — public — **Lines**: 96-99

### `theorem infinitePlace_isReal`
- `(v) → IsReal v` — **How**: `isTotallyReal.isReal`. — **Uses**: [isTotallyReal] — public — **Lines**: 101-103 — **Notes**: used in LocalGlobal.

### `theorem exists_realEmbedding_goldenRatio` / `theorem exists_realEmbedding_conjugateGoldenRatio`
- `∃ σ : K →ₐ[ℚ] ℝ, σφ = (1±√5)/2` — **How**: `QuadraticAlgebra.lift` with the relation checked via `Real.mul_self_sqrt`, `nlinarith`. — **Uses**: [goldenRoot] — public — **Lines**: 105-113 / 115-123 — **Notes**: `_goldenRatio` reused in `house_fundamentalUnit`.

**File Summary (Embeddings.lean)**: 8 decls (1 private generic + 7 public). Key API:
`isTotallyReal`, `nrComplexPlaces_eq_zero`, `nrRealPlaces_eq_two`, `infinitePlace_isReal`,
`exists_realEmbedding_goldenRatio`. No sorry/set_option. `isTotallyReal` ≈24 lines. Split into two
`noncomputable section`s (signature counts / embeddings). `ringHom_ext_golden` is reusable infra.

---

## RingOfIntegers.lean

### `abbrev GoldenOrder`
- **Type**: `:= QuadraticAlgebra ℤ (1:ℤ) (1:ℤ)` — **What**: concrete `ℤ[φ]` model (`a+bφ`, `a b : ℤ`). — **Uses**: [] — public — **Lines**: 38 — **Notes**: key API.

### `abbrev goldenInteger` / `theorem goldenInteger_sq`
- `GoldenOrder := QuadraticAlgebra.omega`; `^2 = ·+1`. — **Uses**: [] — public — **Lines**: 41 / 43-45

### `theorem goldenInteger_isIntegral`
- `IsIntegral ℤ goldenInteger` — **How**: witness `X²-X-1`, `monicity`. — **Uses**: [goldenInteger_sq] — public — **Lines**: 47-51

### `instance Algebra.IsIntegral ℤ GoldenOrder`
- **How**: each `⟨a,b⟩ = algebraMap a + b•φ`, both integral. — **Uses**: [goldenInteger_isIntegral] — public — **Lines**: 53-59

### `def goldenOrderToField`
- **Type**: `GoldenOrder →+* K` (`⟨a,b⟩ ↦ ⟨a,b⟩` over ℚ) — **How**: explicit `RingHom` w/ `ext`/`simp`. — **Uses**: [] — public — **Lines**: 62-70 — **Notes**: key API.

### `instance Algebra GoldenOrder K` / `instance IsScalarTower ℤ GoldenOrder K`
- via `goldenOrderToField.toAlgebra`; tower by `of_algebraMap_eq`. — **Uses**: [goldenOrderToField] — public — **Lines**: 72-76

### `theorem goldenOrderToField_injective`
- `Injective goldenOrderToField` — **How**: compare `re`/`im`, `exact_mod_cast`. — **Uses**: [goldenOrderToField] — public — **Lines**: 78-86

### `abbrev goldenPowerBasis`
- **Type**: `PowerBasis ℚ K` (gen `φ`, dim 2, basis = `QuadraticAlgebra.basis`). — **Uses**: [goldenRoot] — public — **Lines**: 88-94 — **Notes**: key API (used 8+ times: discr, adjoin, basis lemmas).

### `theorem adjoin_goldenRoot_eq_top`
- `Algebra.adjoin ℚ {φ} = ⊤` — **How**: `PowerBasis.adjoin_gen_eq_top`. — **Uses**: [goldenPowerBasis, goldenRoot] — public — **Lines**: 96-98 — **Notes**: used in Different section.

### `theorem goldenPowerBasis_basis_zero` / `_one`
- `basis 0 = 1`, `basis 1 = φ` — **How**: `change`+`ext`/`simp`. — **Uses**: [goldenRoot] — public — **Lines**: 100-102 / 104-106 — **Notes**: each used 3+ times.

### `theorem golden_trace_eq`
- **Type**: `Algebra.trace ℚ K x = 2·x.re + x.im` — **How**: `trace_eq_matrix_trace`, `leftMulMatrix_eq_repr_mul`, `Matrix.trace_fin_two`. — **Uses**: [] — public — **Lines**: 108-114 — **Notes**: used in discr + integrality.

### `theorem golden_norm_eq`
- **Type**: `Algebra.norm ℚ x = x.re² + x.re·x.im - x.im²` — **How**: `norm_eq_matrix_det`, `Matrix.det_fin_two`. — **Uses**: [] — public — **Lines**: 116-122 — **Notes**: the norm form; used in `norm_eq_normForm`, integrality, Euclidean.

### `theorem goldenPowerBasis_discr`
- **Type**: `Algebra.discr ℚ goldenPowerBasis.basis = 5` — **How**: traceMatrix `!![2,1;1,3]` (entrywise via `golden_trace_eq`), `det_fin_two_of`. — **Uses**: [goldenPowerBasis_basis_zero/one, golden_trace_eq, goldenRoot] — public — **Lines**: 124-155 — **Notes**: proof ≈31 lines (>30); core disc computation.

### `theorem five_dvd_coords_of_trace_norm`
- `2m+n=5T ∧ m²+mn-n²=25N → 5∣m ∧ 5∣n` — **How**: substitute `n=5T-2m`, `m²=5·…` ⇒ `5∣m²`, `Prime 5`; then `5∣n`. — **Uses**: [] — public — **Lines**: 157-173

### `theorem int_eq_of_rat_div_five_eq` / `int_eq_of_rat_div_twentyFive_eq`
- `(a/5 = b in ℚ) → a = 5b` (and `/25`). **How**: `norm_num`/`linear_combination`/`exact_mod_cast`. — **Uses**: [] — public — **Lines**: 175-180 / 182-188

### `private theorem five_dvd_coords_of_integral`
- For integral `x` with `m=5x.re,n=5x.im`: `5∣m ∧ 5∣n` — **How**: `trace`/`norm` of `x` are integers, push to `five_dvd_coords_of_trace_norm`. — **Uses**: [golden_trace_eq, golden_norm_eq, int_eq lemmas, five_dvd_coords_of_trace_norm] — private — **Lines**: 190-215

### `theorem integral_mem_goldenOrderToField_range`
- **Type**: integral `x` ⇒ `∃ y : GoldenOrder, algebraMap y = x` — **How**: `discr·x ∈ adjoin` (`Algebra.discr_mul_isIntegral_mem_adjoin`, disc 5), divisibility of coords by 5 cancels the `5•`. — **Uses**: [goldenPowerBasis(_discr), goldenRoot_isIntegral, goldenOrderToField, goldenInteger, five_dvd_coords_of_integral] — public — **Lines**: 217-251 — **Notes**: proof ≈35 lines (>30); the integrality crux (golden half-integral subtlety).

### `instance IsIntegralClosure GoldenOrder ℤ K`
- **How**: `algebraMap_injective` + `isIntegral_iff` both directions. — **Uses**: [goldenOrderToField_injective, integral_mem_goldenOrderToField_range] — public — **Lines**: 253-259

### `def integralBasisVectors` / `theorem span_integralBasisVectors_eq`
- `Fin 2 → K := ![1, φ]`; their ℤ-span = `Subalgebra.toSubmodule (integralClosure ℤ K)`. **How**: `le_antisymm`; for `≥` decompose via `integral_mem_goldenOrderToField_range`. — **Uses**: [goldenRoot(_isIntegral), goldenOrderToField, integral_mem_goldenOrderToField_range] — public — **Lines**: 262 / 264-284

### `abbrev concreteRingOfIntegers`
- `:= Algebra.adjoin ℤ {goldenRoot}` — the order `ℤ[φ]`. — **Uses**: [goldenRoot] — public — **Lines**: 287-288 — **Notes**: used in Different.

### `theorem ringOfIntegers_eq`
- **Type**: `integralClosure ℤ K = concreteRingOfIntegers` — **How**: `le_antisymm`; integral ⇒ in adjoin via `mk_eq_add_smul_omega`, `intCast_mem`/`zsmul_mem`. — **Uses**: [integral_mem_goldenOrderToField_range, goldenRoot, concreteRingOfIntegers] — public — **Lines**: 290-304 — **Notes**: key result; used in `goldenIntO_adjoin_eq_top`.

### `theorem span_integralBasisVectors_eq_integralBasis`
- `[1,φ]` span = `NumberField.integralBasis K` span. **How**: `mem_span_integralBasis`, `RingHom.mem_range`. — **Uses**: [span_integralBasisVectors_eq, integralBasisVectors] — public — **Lines**: 306-320

### `theorem adjoin_sqrtFive_ne_integralClosure`
- **Type**: `Algebra.adjoin ℤ {√5} ≠ integralClosure ℤ K` — **What**: `ℤ[√5] ⊊ ℤ[φ]` (index 2). **How**: build subalgebra `S = {re∈ℤ, im∈2ℤ}` (with explicit `mul_mem` using `φ²=φ+1`), `√5=-1+2φ ∈ S`, but `φ∉S` (im=1 not even). — **Uses**: [sqrtFiveRoot, goldenRoot, goldenRoot_isIntegral] — public — **Lines**: 322-362 — **Notes**: proof ≈40 lines; the distinctive `5≡1 mod 4` fact (no SqrtTwo analogue — there `ℤ[√2]` IS the maximal order).

### `abbrev sqrtFiveExplicitIntegralBasis` / `_zero` / `_one`
- `Basis (Fin 2) ℤ GoldenOrder := QuadraticAlgebra.basis 1 1`; vectors `1`, `goldenInteger`. — **Uses**: [goldenInteger] — public — **Lines**: 365-366 / 369-372 / 375-378

### `theorem goldenOrderToField_basis_zero` / `_one`
- `goldenOrderToField (basis i) = 1 / φ`. — **Uses**: [sqrtFiveExplicitIntegralBasis_zero/one, goldenOrderToField] — public — **Lines**: 380-383 / 385-388

### `def goldenOrderEquivRingOfIntegers`
- **Type**: `GoldenOrder ≃ₐ[ℤ] 𝓞 K := IsIntegralClosure.equiv …`. — **Uses**: [IsIntegralClosure instance] — public — **Lines**: 391-392 — **Notes**: key API.

### `def concreteIntegralBasis` + `_basis_zero`/`_one`
- `Basis (Fin 2) ℤ (𝓞 K)` = explicit basis mapped via the equiv; `algebraMap (·) = 1 / φ`. **How**: `IsIntegralClosure.algebraMap_equiv`. — **Uses**: [sqrtFiveExplicitIntegralBasis, goldenOrderEquivRingOfIntegers, goldenOrderToField_basis_*] — public — **Lines**: 395-396 / 399-404 / 407-412 — **Notes**: key API across PrimeSplitting.

### `theorem concreteIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ concreteIntegralBasis = 5` — **How**: `Algebra.discr_localizationLocalization` (𝓞 K → ℚ⊗) + `Module.Basis.localizationLocalization`, transfer to `goldenPowerBasis_discr`. — **Uses**: [concreteIntegralBasis(_basis_*), goldenPowerBasis_basis_*, goldenPowerBasis_discr] — public — **Lines**: 414-452 — **Notes**: proof ≈38 lines (>30); heaviest localization argument in folder.

### `theorem numberField_discr_eq`
- **Type**: `NumberField.discr K = 5` — **How**: `discr_eq_discr K concreteIntegralBasis` + `concreteIntegralBasis_discr`. — **Uses**: [concreteIntegralBasis(_discr)] — public — **Lines**: 454-459 — **Notes**: used in PrimeSplitting (different/ramification) and ClassGroup (Minkowski).

### `theorem integralBasis_discr`
- `Algebra.discr ℚ (NumberField.integralBasis K) = 5` (with local `DivisionRing.toRatAlgebra`). **How**: `NumberField.coe_discr` + `numberField_discr_eq`. — **Uses**: [numberField_discr_eq] — public — **Lines**: 461-467 — **Notes**: only `attribute [local instance]` in file.

### `def goldenIntO` / `theorem goldenIntO_sq`
- `𝓞 K := ⟨goldenRoot, goldenRoot_isIntegral⟩`; `^2 = ·+1`. **How**: `Subtype.ext`/`push_cast`. — **Uses**: [goldenRoot(_isIntegral, _sq)] — public — **Lines**: 484 / 487-488 — **Notes**: THE generator of `𝓞 K` (≈40 references across PrimeSplitting/ClassGroup/Units).

### `theorem norm_eq_normForm`
- **Type**: `Algebra.norm ℚ (x•1 + y•φ) = x² + xy - y²` — **How**: `golden_norm_eq` + `re/im_add`. — **Uses**: [golden_norm_eq, goldenRoot] — public — **Lines**: 490-495 — **Notes**: used in Euclidean.

### `theorem intNorm_eq_normForm`
- **Type**: integral version `Algebra.norm ℤ (x•1 + y•φ) = x² + xy - y²` (`x y : ℤ`) — **How**: push to ℚ via `Algebra.coe_norm_int`, `norm_eq_normForm`. — **Uses**: [goldenIntO, norm_eq_normForm] — public — **Lines**: 497-511 — **Notes**: workhorse of PrimeSplitting (≈12 uses computing ideal norms).

### `theorem isUnit_iff_normForm`
- **Type**: `IsUnit (x•1+y•φ) ↔ x²+xy-y² = ±1` — **What**: Pell-type unit equation. **How**: `isUnit_iff_norm`, `intNorm_eq_normForm`, `abs_eq`. — **Uses**: [goldenIntO, intNorm_eq_normForm] — public — **Lines**: 513-528 — **Notes**: this norm-form criterion is exactly the engine `minimality`/`reduction` use to prove `fundamentalUnit_generates` (now proved).

**File Summary (RingOfIntegers.lean)**: ~40 decls. Key API (3+ uses): `goldenIntO`,
`goldenIntO_sq`, `intNorm_eq_normForm`, `concreteIntegralBasis(_basis_*)`, `goldenPowerBasis`,
`golden_trace_eq`, `golden_norm_eq`, `numberField_discr_eq`, `goldenOrderEquivRingOfIntegers`. No
sorry. One `attribute [local instance] DivisionRing.toRatAlgebra` (line 461). Proofs >30 lines:
`adjoin_sqrtFive_ne_integralClosure` (~40), `concreteIntegralBasis_discr` (~38),
`integral_mem_goldenOrderToField_range` (~35), `goldenPowerBasis_discr` (~31). The
`adjoin_sqrtFive_ne_integralClosure` result is SqrtFive-specific (half-integral maximal order).

---

## PrimeSplitting.lean

### `def sqrtFiveIntO`
- **Type**: `𝓞 K := 2 * goldenIntO - 1` — `√5` in `𝓞 K`. — **Uses**: [goldenIntO] — public — **Lines**: 37 — **Notes**: key API; the ramified prime generator.

### `theorem span_five_eq`
- **Type**: `Ideal.span {5} = Ideal.span {√5} ^ 2` — **What**: `5` totally ramifies. **How**: `span_singleton_pow`, `(2φ-1)²=5` via `sqrtFiveRoot_sq`. — **Uses**: [sqrtFiveIntO, sqrtFiveRoot_sq] — public — **Lines**: 41-47

### `theorem absNorm_span_sqrtFiveIntO`
- `Ideal.absNorm (span {√5}) = 5` — **How**: `√5 = -1+2φ`, `intNorm_eq_normForm (-1) 2`, `absNorm_span_singleton`. — **Uses**: [sqrtFiveIntO, intNorm_eq_normForm, goldenIntO] — public — **Lines**: 49-59 — **Notes**: used 3+ times.

### `theorem isPrime_span_sqrtFiveIntO`
- `(√5).IsPrime` — **How**: `isPrime_of_irreducible_absNorm` + `Nat.Prime 5`. — **Uses**: [absNorm_span_sqrtFiveIntO] — public — **Lines**: 61-65 — **Notes**: used in LocalGlobal/ClassGroup/Different.

### `theorem liesOver_span_sqrtFiveIntO` / `inertiaDeg_span_sqrtFiveIntO` / `ramificationIdx_span_sqrtFiveIntO`
- `(√5)` lies over `(5)`; `f=1`; `e=2`. **How**: `liesOver_span_iff`; `absNorm_eq_pow_inertiaDeg'`; `ramificationIdx_spec` with norm 5/125/25 divisibility. — **Uses**: [isPrime/absNorm/span_five_eq, intNorm_eq_normForm] — public — **Lines**: 67-79 / 81-89 / 91-115

### `private theorem absNorm_ne_two` / `absNorm_ne_three`
- No ideal of `𝓞 K` has norm 2 or 3. **How**: residue field `≅ ZMod 2/3`, `φ` would solve `t²=t+1`, `decide`. — **Uses**: [goldenIntO_sq] — private — **Lines**: 117-134 / 136-153 — **Notes**: drive inertness of `(2)`,`(3)`.

### `theorem isPrime_span_two`
- `(2).IsPrime` — **What**: `2` inert. **How**: `absNorm = 4`, any maximal `M ⊇ (2)` has norm ∣4, ≠1,≠2 ⇒ =4 ⇒ `M=(2)`. **Uses**: [absNorm_ne_two, eq_of_le_of_absNorm_eq, intNorm_eq_normForm] — public — **Lines**: 155-188

### `theorem absNorm_span_two` / `liesOver_span_two` / `inertiaDeg_span_two`
- norm 4; lies over `(2)`; `f=2`. **How**: `intNorm_eq_normForm 2 0`; `liesOver_span_iff`; `absNorm_eq_pow_inertiaDeg'` + `pow_right_injective`. — **Uses**: [isPrime_span_two, intNorm_eq_normForm] — public — **Lines**: 190-198 / 200-206 / 208-218

### `theorem isPrime_span_three` + `absNorm`/`liesOver`/`inertiaDeg_span_three`
- `3` inert (norm 9, `f=2`). **How**: analogous to `(2)` (`5` not a square mod 3). **Uses**: [absNorm_ne_three, eq_of_le_of_absNorm_eq, intNorm_eq_normForm] — public — **Lines**: 220-253 / 255-263 / 265-271 / 273-283

### `theorem eleven_eq_mul`
- `(11 : 𝓞 K) = (3+φ)(4-φ)` — **How**: `Subtype.ext`, expand, `goldenRoot_sq`. — **Uses**: [goldenIntO, goldenRoot_sq] — public — **Lines**: 285-291 — **Notes**: the split-prime example.

### `theorem span_eleven_eq` + `absNorm`/`isPrime`/`liesOver`/`inertiaDeg` for `(3+φ)`,`(4-φ)`
- `(11) = (3+φ)(4-φ)`, each prime of norm 11, `f=1`, lies over `(11)`. **How**: `span_singleton_mul`, `intNorm_eq_normForm 3 1` / `4 (-1)`, `isPrime_of_irreducible_absNorm`. — **Uses**: [eleven_eq_mul, intNorm_eq_normForm] — public — **Lines**: 295-356 (spread)

### `theorem primesAboveEleven_ne`
- `(3+φ) ≠ (4-φ)` — **How**: else both contain their difference `√5`, then `5`, then `11`, then `1` ⇒ contradiction with norm 11. — **Uses**: [sqrtFiveIntO, sqrtFiveRoot_sq, eleven_eq_mul, absNorm_span_three_add_golden] — public — **Lines**: 378-407

### `private theorem absNorm_span_natCast`
- `Ideal.absNorm (span {(p:𝓞 K)}) = p²` — **How**: `absNorm_span_natCast` (mathlib) + `RingOfIntegers.rank` + `degree_eq_two`. — **Uses**: [degree_eq_two] — private — **Lines**: 409-411 — **Notes**: used 4+ times (norm of inert/ramified rational primes); reusable infra.

### `private theorem concreteIntegralBasis_zero_eq_one` / `_one_eq_goldenIntO` / `li_one_golden` / `exists_o5_coords`
- `[1,φ]` is the ℤ-basis of `𝓞 K`: coordinate extraction lemmas. **How**: `Subtype.ext`, `Fintype.linearIndependent_iff`, `concreteIntegralBasis.repr`. — **Uses**: [concreteIntegralBasis(_basis_*), goldenIntO] — private — **Lines**: 413-442

### `private theorem unit_golden_coeff_not_mem`
- `A + B·φ` with `B=±1` is never in `(p)` for `p≥2`. **How**: `mem_span_singleton`, coords via `li_one_golden`, `p∣1`⇒contra. — **Uses**: [goldenIntO, exists_o5_coords, li_one_golden] — private — **Lines**: 444-468 — **Notes**: drives norm-`p` ⇒ prime arguments.

### `theorem ramified_iff_eq_five`
- **Type**: `(∃ P prime, (p) ≤ P²) ↔ p = 5` — **What**: ramification ⇔ `p ∣ disc = 5`. **How**: (⇒) `not_isUnramifiedAt_…` ⇒ `P ∣ differentIdeal`, `absNorm P ∣ 5`, so `p=5`; (⇐) use `span_five_eq`. — **Uses (incl. Common)**: [absNorm_span_natCast, not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ, not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow, numberField_discr_eq, absNorm_differentIdeal, sqrtFiveIntO, span_five_eq, isPrime_span_sqrtFiveIntO] — public — **Lines**: 470-514 — **Notes**: proof ≈45 lines (>30); central ramification law.

### `theorem ramificationIdx_span_two` / `_three` / `_three_add_golden` / `_four_sub_golden`
- inert/split primes are unramified (`e=1`). **How**: `ramificationIdx_spec`; the `>` direction reduces to `ramified_iff_eq_five` giving `p=5` contradiction. — **Uses**: [ramified_iff_eq_five, isPrime_span_*, span_eleven_eq] — public — **Lines**: 516-578

### `private theorem golden_sub_mem_span_natCast_of_one_mem_span_pair`
- Lattice computation supporting norm-`p` of `(p, φ-c)`. **How**: `mem_span_pair`, `mem_span_singleton`, `linear_combination`. — **Uses**: [goldenIntO] — private — **Lines**: 580-600

### `private theorem absNorm_span_prime_golden_sub_of_mul`
- `(p, φ-c)` has norm `p` given the product factorization. **How**: norm ∣ p², ≠1 (`unit_golden_coeff_not_mem`), ≠p² (`eq_of_le_of_absNorm_eq`), `eq_prime_of_dvd_prime_sq_…`. — **Uses (incl. Common)**: [absNorm_span_natCast, unit_golden_coeff_not_mem, eq_of_le_of_absNorm_eq, eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq, golden_sub_mem_span_natCast_of_one_mem_span_pair, goldenIntO] — private — **Lines**: 602-647

### `private theorem exists_golden_root_of_absNorm_eq_prime`
- norm-`p` prime ⇒ `∃ t : ZMod p, t²=t+1`. **How**: residue field `≅ ZMod p`, image of `φ`. — **Uses**: [goldenIntO_sq] — private — **Lines**: 649-667

### `private theorem isSquare_five_of_absNorm_eq_prime`
- ⇒ `IsSquare ((5:ℕ):ZMod p)` via `2t-1`. — **Uses**: [exists_golden_root_of_absNorm_eq_prime] — private — **Lines**: 669-675

### `private theorem pm_one_mod_five_of_splits`
- `p` splits ⇒ `p%5 ∈ {1,4}`. **How**: norm-`p` factor + `isSquare_five`, quadratic reciprocity `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`, exclude `2,3` mod 5 by `decide`. — **Uses (incl. Common)**: [left_eq_prime_of_mul_eq_prime_sq_of_ne_one, absNorm_span_natCast, exists_golden_root_of_absNorm_eq_prime, isSquare_five_of_absNorm_eq_prime] — private — **Lines**: 677-722

### `private theorem exists_golden_root_of_pm_one_mod_five`
- `p%5∈{1,4}` ⇒ `∃ t, t²=t+1`. **How**: reciprocity gives `5` square mod `p`, set `t=(1+s)/2`, clear `4`. — **Uses**: [] — private — **Lines**: 724-764

### `private theorem golden_root_ne_one_sub_of_prime_ne_five`
- For `p≠5`: `t ≠ 1-t`. **How**: else `2t=1`, derive `5≡0 mod p` ⇒ contradiction. — **Uses**: [] — private — **Lines**: 766-781

### `private theorem span_prime_golden_sub_ne_of_root`
- The two primes `(p,φ-c)`,`(p,φ-c')` are distinct. **How**: inverse of `c-c'` mod p (`exists_int_inverse_mod_prime`), else `1 ∈ P`. — **Uses (incl. Common)**: [exists_int_inverse_mod_prime, golden_root_ne_one_sub_of_prime_ne_five, goldenIntO] — private — **Lines**: 783-828

### `private theorem span_natCast_eq_mul_span_golden_sub_of_mul`
- `(p) = (p,φ-c)·(p,φ-c')`. **How**: `mul_le` + `mem_span_pair`/`linear_combination`, `eq_of_le_of_absNorm_eq` with norm `p²`. — **Uses (incl. Common)**: [eq_of_le_of_absNorm_eq, absNorm_span_natCast] — private — **Lines**: 830-870

### `private theorem exists_golden_split_data`
- From a root `t` produce integer data `c,c',k₁,k₂` with the product identity. **How**: `ZMod.natCast_rightInverse`, divisibilities `p∣1-c-c'`,`p∣1+cc'`, `linear_combination`. — **Uses**: [goldenIntO(_sq)] — private — **Lines**: 872-910

### `private theorem splits_of_pm_one_mod_five`
- `p%5∈{1,4}` ⇒ splits into two distinct primes. **How**: assemble all the above. — **Uses**: [exists_golden_root_of_pm_one_mod_five, exists_golden_split_data, absNorm_span_prime_golden_sub_of_mul, span_prime_golden_sub_ne_of_root, span_natCast_eq_mul_span_golden_sub_of_mul] — private — **Lines**: 912-954

### `theorem splits_iff_pm_one_mod_five`
- **Type**: for `p≠5`, splits ↔ `p%5 ∈ {1,4}` — **What**: the quadratic splitting law (reciprocity). **How**: combines the two private directions. — **Uses**: [pm_one_mod_five_of_splits, splits_of_pm_one_mod_five] — public — **Lines**: 956-964 — **Notes**: headline splitting theorem.

### Kummer-Dedekind section (`goldenPolynomialMod` etc.)
- `abbrev goldenPolynomialMod p := X²-X-C 1`; `_isRoot_iff` (root ↔ `t²=t+1`); `_natDegree`=2 (`natDegree_quadratic`); `_roots_eq_zero_iff_no_root`; `_no_root_iff_two_or_three_mod_five` (`p%5∈{2,3}`, reciprocity + `decide`). — **Uses**: [exists_golden_root_of_pm_one_mod_five] — abbrev public / theorems private — **Lines**: 982-1066

### Different section
- `private goldenIntO_adjoin_eq_top` (`adjoin ℤ {φ} = ⊤`; from `ringOfIntegers_eq`, `aeval`); `private goldenIntO_minpoly` (`= X²-X-1`; `minpoly.isIntegrallyClosed_eq_field_fractions` + `X_pow_sub_X_sub_one_irreducible_rat`); `differentIdeal_eq_span_sqrtFive` (`𝔡 = (√5)`; `conductor_mul_differentIdeal`, `aeval (derivative minpoly) = 2φ-1`); `absNorm_differentIdeal_eq_five` (=5; `absNorm_differentIdeal` + disc); `prime_dvd_differentIdeal_iff_eq_span_sqrtFive` (`P ∣ 𝔡 ↔ P=(√5)`). — **Uses**: [ringOfIntegers_eq, adjoin_goldenRoot_eq_top, concreteRingOfIntegers, goldenRoot_sq, goldenIntO, sqrtFiveIntO, sqrtFiveRoot_sq, numberField_discr_eq, isPrime_span_sqrtFiveIntO] — public/private — **Lines**: 1083-1182 — **Notes**: `goldenIntO_minpoly` proof ≈30 lines.

**File Summary (PrimeSplitting.lean)**: ~50 decls (largest file, 1183 lines, 4 `noncomputable
section`s: Prime Splitting / Kummer-Dedekind / Different). Key API (3+ uses): `intNorm_eq_normForm`
(≈12), `goldenIntO(_sq)`, `sqrtFiveIntO`, `absNorm_span_natCast`, `eq_of_le_of_absNorm_eq` (Common),
`absNorm_eq_pow_inertiaDeg'`, `ramified_iff_eq_five`, `exists_golden_root_of_pm_one_mod_five`. Uses
Common: `eq_of_le_of_absNorm_eq`, `eq_prime_of_dvd_prime_sq_…`,
`left_eq_prime_of_mul_eq_prime_sq_…`, `exists_int_inverse_mod_prime`, plus the two ramification
helpers. No sorry/set_option. Proofs >30 lines: `ramified_iff_eq_five` (~45),
`span_prime_golden_sub_ne_of_root` (~45), `exists_golden_root_of_pm_one_mod_five` (~40),
`span_natCast_eq_mul_span_golden_sub_of_mul` (~40), `exists_golden_split_data` (~38),
`absNorm_span_prime_golden_sub_of_mul` (~45), `goldenIntO_minpoly` (~30). `absNorm_span_natCast`
reusable infra. `goldenPolynomialMod` block is Kummer-Dedekind sugar largely independent of the
splitting proof (which is done directly via norms).

---

## ClassGroup.lean

### `abbrev goldenRootFractionalIdeal` / `ramifiedPrimeFractionalIdeal`
- `FractionalIdeal (𝓞 K)⁰ K`: `spanSingleton φ`; coe of `(√5)`. — **Uses**: [goldenRoot, sqrtFiveIntO] — public — **Lines**: 33-34 / 36-37

### `theorem goldenRoot_mem_fractionalIdeal` / `goldenRootFractionalIdeal_absNorm`
- `φ ∈ …`; `absNorm = |Algebra.norm ℚ φ|`. **How**: `mem_spanSingleton_self`; `simp`. — **Uses**: [goldenRootFractionalIdeal, goldenRoot] — public — **Lines**: 39-41 / 43-45

### `theorem ramifiedPrimeFractionalIdeal_ne_zero`
- `≠ 0` — **How**: `coeIdeal_ne_zero`; `(√5)=0` ⇒ `5=0`. — **Uses**: [sqrtFiveIntO, sqrtFiveRoot_sq, goldenRoot] — public — **Lines**: 47-58

### `theorem classNumber_eq_one`
- **Type**: `NumberField.classNumber K = 1` — **What**: trivial class group. **How**: `classNumber_eq_one_iff` + `isPrincipalIdealRing_of_…_mem_Icc`; Minkowski bound `√5/2 < 2` so `⌊bound⌋ < 2`, no primes in `Icc 2 1`. **Uses**: [nrComplexPlaces_eq_zero, degree_eq_two, numberField_discr_eq] — public — **Lines**: 76-105 — **Notes**: proof ≈30 lines; the Minkowski-bound class-number-one argument (disc 5 is what makes the bound `<2`).

### `theorem isPrincipalIdealRing`
- `IsPrincipalIdealRing (𝓞 K)` — **How**: `← classNumber_eq_one_iff`. — **Uses**: [classNumber_eq_one] — public — **Lines**: 107-111

### `theorem uniqueFactorizationMonoid`
- `UniqueFactorizationMonoid (𝓞 K)` — **How**: PID ⇒ UFM, `infer_instance`. — **Uses**: [isPrincipalIdealRing] — public — **Lines**: 113-116

### `theorem classGroupStructure`
- **Type**: `Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1))` — **How**: `Nat.card = 1` ⇒ `Subsingleton`/`Unique` ⇒ `MulEquiv.ofUnique`. — **Uses**: [classNumber_eq_one] — public — **Lines**: 118-125 — **Notes**: trivial-group `Nonempty (… ≃* Multiplicative (ZMod 1))` encoding (twin pattern; unnatural — see report).

### `abbrev unitIdealRepresentative` / `theorem classGroupRepresentative`
- `(⊤ : Ideal …)` as `(Ideal …)⁰`; every class = `mk0 ⊤`. **How**: `Subsingleton.elim`. — **Uses**: [classNumber_eq_one] — public — **Lines**: 128-129 / 132-137

**File Summary (ClassGroup.lean)**: 10 decls (2 sections). Key API: `classNumber_eq_one` (drives
all the rest). Uses RingOfIntegers/Embeddings API: `numberField_discr_eq`, `degree_eq_two`,
`nrComplexPlaces_eq_zero`, `sqrtFiveIntO`. No sorry/set_option. `classNumber_eq_one` ≈30 lines
(longest). The fractional-ideal decls (33-58) are demonstrative, unused by sibling files.

---

## Units.lean

### `def fundamentalUnit`
- **Type**: `(𝓞 K)ˣ` (`val = φ`, `inv = φ-1`) — **What**: the fundamental unit `φ`. **How**: `val_inv`/`inv_val` from `goldenIntO_sq` (`φ(φ-1)=φ²-φ=1`). — **Uses**: [goldenIntO(_sq)] — public — **Lines**: 38-48 — **Notes**: key API across Units/LocalGlobal.

### `abbrev torsionGenerator` / `def torsionUnits`
- `(𝓞 K)ˣ := -1`; `{u | ∃ k:Fin 2, u = (-1)^k}`. — **Uses**: [] — public — **Lines**: 51 / 54

### `private def realEmb`
- `K →ₐ[ℚ] ℝ` (`φ ↦ (1+√5)/2`) — **How**: `QuadraticAlgebra.lift`, `Real.mul_self_sqrt`. — **Uses**: [] — private — **Lines**: 56-62 — **Notes**: same construction as `exists_realEmbedding_goldenRatio`.

### `theorem torsionUnits_eq`
- **Type**: `{u | IsOfFinOrder u} = torsionUnits` — **What**: torsion `= {±1}`. **How**: real embedding `e`; finite-order ⇒ `|e x|=1` ⇒ `e x=±1` ⇒ `x=±1` (injectivity). — **Uses**: [realEmb, torsionUnits, goldenRoot] — public — **Lines**: 64-111 — **Notes**: proof ≈47 lines (>30). The "totally real ⇒ roots of unity `±1`" argument.

### `theorem torsionOrder_eq_two`
- `Units.torsionOrder K = 2` — **How**: `Nat.card (torsion) = 2` via `card_eq_two_iff` (`±1`, distinct since `2≠0` in K), `torsionUnits_eq` for surjectivity. — **Uses**: [torsionUnits_eq] — public — **Lines**: 113-141

### `theorem unitRank_eq_one`
- `Units.rank K = 1` — **How**: `rank = #places - 1`, `nrRealPlaces=2`, `nrComplexPlaces=0`. — **Uses**: [nrRealPlaces_eq_two, nrComplexPlaces_eq_zero] — public — **Lines**: 143-147 — **Notes**: used 5+ times.

### `def fundamentalUnitSystem`
- `Fin (Units.rank K) → (𝓞 K)ˣ := fun _ => fundamentalUnit`. — **Uses**: [fundamentalUnit] — public — **Lines**: 149-151

### `theorem intNorm_goldenInt`
- `Algebra.norm ℤ goldenIntO = -1` — **How**: `intNorm_eq_normForm 0 1` (`0²+0-1²=-1`). — **Uses**: [intNorm_eq_normForm, goldenIntO] — public — **Lines**: 153-156 — **Notes**: `N(φ)=-1` is why `φ` (not `φ²`) is fundamental.

### `private theorem normFundamentalUnit_map` / `normNegOneUnit_map` / `even_of_negOneUnit_zpow_eq_one` / `normFundamentalUnit_zpow_map` / `normNegFundamentalUnit_zpow_map`
- `N(φ)=-1` and `N(-1)=1` as `ℤˣ`-maps; `(-1)^n=1 ⇒ n` even; the `zpow` versions. **How**: `Units.ext`, `map_zpow`, `Odd.neg_one_zpow`. — **Uses**: [fundamentalUnit, intNorm_goldenInt, intNorm_eq_normForm, goldenIntO] — private — **Lines**: 158-200

### `theorem exists_eq_torsion_mul_fundSystem_zpow`
- mathlib `fundSystem K i₀` + torsion generate `(𝓞 K)ˣ`. **How**: `closure_fundSystem_sup_torsion_eq_top`, `mem_sup`, `range fundSystem = {fundSystem i₀}` (subsingleton via rank 1), `mem_closure_singleton`. — **Uses**: [unitRank_eq_one] — public — **Lines**: 204-226 — **Notes**: bridges abstract `fundSystem` to a single generator.

### `theorem fundSystem_zpow_mem_torsion`
- `fundSystem^n ∈ torsion ⇒ n=0`. **How**: image in `(𝓞 K)ˣ/torsion` via `basisModTorsion`, `repr_self`. — **Uses**: [] — public — **Lines**: 228-245

### `theorem eq_one_or_neg_one_of_mem_torsion`
- torsion `ζ` ⇒ `ζ=±1`. **How**: `torsionUnits_eq` + `fin_cases`. — **Uses**: [torsionUnits_eq] — public — **Lines**: 247-256

### `theorem fundamentalUnit_generates`  ✅ proved
- **Type**: `(u) → ∃ n, u = φ^n ∨ u = -(φ^n)` — **What**: every unit is `±φⁿ`. **How**: a
  **real-embedding window-reduction** (≈35 lines of supporting `private` lemmas: `reEmb`, `fhom`,
  `exists_coords`, `minimality`, `reduction`, `pos_case`). Send units to ℝ via `reEmb : φ ↦ Φ`;
  `exists_mem_Ico_zpow` reduces any positive-image unit into `[1, Φ)` by a power of `φ`; `minimality`
  uses the norm form `x²+xy−y² = ±1` (`isUnit_iff_normForm`) + bounds on the conjugate to force the
  reduced unit to `1`; sign handled by `fhom_neg`. — **Uses**: [fundamentalUnit, isUnit_iff_normForm,
  exists_realEmbedding_goldenRatio] — public — **Lines**: 430-440 (helpers 258-428)
- **NOT an API gap**: this is the faithful formalisation of the standard "φ is fundamental" proof for
  a real quadratic field, using only mature mathlib API. It deliberately bypasses `Zsqrtd`/`Pell`
  (which only covers the index-2 suborder `ℤ[√5]`, not the half-integral maximal order `ℤ[(1+√5)/2]`).
  The difficulty was *intrinsic mathematics*, now discharged.

### `theorem fundamentalUnitSystem_isFundamental`  ✅ proved
- `closure (range fundamentalUnitSystem) ⊔ torsion = ⊤`. **How**: `fundamentalUnit_generates` + `mem_sup`. — **Uses**: [fundamentalUnitSystem, fundamentalUnit, fundamentalUnit_generates] — public — **Lines**: 444-464.

### `theorem unit_eq_torsion_mul_fundamentalUnit_zpow`  ✅ proved
- `u = ζ · φ^n`, `ζ` torsion. **How**: `fundamentalUnit_generates`. — **Uses**: [fundamentalUnit_generates, fundamentalUnit] — public — **Lines**: 467-475.

### `theorem normOneUnit_generated_by_fundamentalUnit_sq`  ✅ proved
- norm-1 unit `= ±φ^(2n)`. **How**: `fundamentalUnit_generates` + `even_of_negOneUnit_zpow_eq_one` via the norm map. — **Uses**: [fundamentalUnit_generates, normFundamentalUnit_zpow_map, normNegFundamentalUnit_zpow_map, even_of_negOneUnit_zpow_eq_one] — public — **Lines**: 478-495.

### `theorem regulator_eq`  ✅ proved
- **Type**: `Units.regulator K = Real.log ((1+√5)/2)` — **What**: regulator `= log φ ≈ 0.4812` (smallest of any real quadratic field). **How**: choose the real place `wR` (`exists_realEmbedding_goldenRatio`); `fundamentalUnitSystem_isFundamental` gives index 1, so `regOfFamily_div_regulator` ⇒ `regulator = regOfFamily`; `regOfFamily_eq_det` + `Matrix.det_eq_elem_of_subsingleton` evaluate the rank-1 `1×1` matrix to `|log(wR φ)| = log Φ`. — **Uses**: [fundamentalUnitSystem_isFundamental, unitRank_eq_one, infinitePlace_card_eq_two, exists_realEmbedding_goldenRatio] — public — **Lines**: 500-562
- **NOT an API gap**: the regulator-value step is mature mathlib (`regOfFamily_eq_det`); it only sat downstream of `fundamentalUnit_generates`.

### `private theorem unitGroupStructure_bijective`
- The coprod hom `(ZMod 2 torsion) ⊕ (rank-1 ℤ)` → `(𝓞 K)ˣ` is bijective. **How**: injective via `fundSystem_zpow_mem_torsion` + `-1` order 2; surjective via `exists_eq_torsion_mul_fundSystem_zpow` + `eq_one_or_neg_one_of_mem_torsion`. — **Uses (incl. Common)**: [torsionPowerHom, rankOnePowerHom, fundSystem_zpow_mem_torsion, exists_eq_torsion_mul_fundSystem_zpow, eq_one_or_neg_one_of_mem_torsion] — private — **Lines**: 331-375 — **Notes**: proof ≈45 lines (>30); does NOT use the sorry (routes through mathlib `fundSystem`).

### `theorem unitGroupStructure`
- **Type**: `Nonempty ((𝓞 K)ˣ ≃* (Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ)))` — **What**: `(𝓞 K)ˣ ≅ μ₂ × ℤ`. **How**: assemble `torsionPowerHom`/`rankOnePowerHom` coprod, `MulEquiv.ofBijective`. — **Uses (incl. Common)**: [torsionPowerHom, rankOnePowerHom, unitGroupStructure_bijective, unitRank_eq_one] — public — **Lines**: 377-394 — **Notes**: sorry-FREE; the abstract structure theorem routes through mathlib `fundSystem`. (The *explicit* generator identification, once a separate blocker, is now also proved — see `fundamentalUnit_generates`.)

**File Summary (Units.lean)**: ~28 decls (incl. the `reEmb`/`fhom`/`minimality`/`reduction`/
`pos_case` window-reduction toolkit). **0 sorries** — both former sorries (`fundamentalUnit_generates`,
`regulator_eq`) are now proved, and the three downstream results
(`fundamentalUnitSystem_isFundamental`, `unit_eq_torsion_mul_fundamentalUnit_zpow`,
`normOneUnit_generated_by_fundamentalUnit_sq`) along with them. Key API: `fundamentalUnit`,
`unitRank_eq_one`, `torsionUnits_eq`, `isUnit_iff_normForm`, `regOfFamily_eq_det`,
`exists_eq_torsion_mul_fundSystem_zpow`, `fundSystem_zpow_mem_torsion`,
`eq_one_or_neg_one_of_mem_torsion`. Uses Common: `torsionPowerHom`, `rankOnePowerHom`. No set_option.
Proofs >30 lines: `torsionUnits_eq` (~47), `unitGroupStructure_bijective` (~45), the
`fundamentalUnit_generates` window-reduction block. NB: the *abstract* unit group
(`unitGroupStructure ≅ μ₂ × ℤ`) routes through mathlib `fundSystem` and was always sorry-free; the
new work supplies the *explicit* `±φⁿ` description and regulator value by following the standard
mathematics (no API gap).

---

## Euclidean.lean

### `private theorem abs_norm_int_lt_of_remainder_eq`
- **Type**: division-with-remainder norm bound: if `r = b·(frac)` and the golden norm form of the fractional part `≤ 3/4`, then `|N(r)| < |N(b)|`. **How**: `Common.abs_intNorm_lt_of_abs_norm_le` with `3/4 < 1`, rewriting the norm via `norm_eq_normForm`. — **Uses (incl. Common)**: [abs_intNorm_lt_of_abs_norm_le, norm_eq_normForm, goldenRoot] — private — **Lines**: 35-50

### `theorem normEuclidean`
- **Type**: `(a b)(hb : b≠0) → ∃ q r, a = b·q + r ∧ |N r|.natAbs < |N b|.natAbs` — **What**: `ℤ[φ]` is norm-Euclidean. **How**: take `q` by rounding the `(re, im)` coordinates of `a/b` in the `1,φ` basis; the fractional parts `(s,t)` satisfy `|s²+st-t²| ≤ 3/4` (the golden norm form on `[-1/2,1/2]²`, shown by `nlinarith` from `abs_sub_round`), then apply the bound lemma. — **Uses (incl. Common)**: [goldenRoot, goldenIntO, norm_eq_normForm, abs_norm_int_lt_of_remainder_eq, natAbs_lt_of_abs_ratCast_lt] — public — **Lines**: 52-93 — **Notes**: proof ≈40 lines (>30). The `3/4` bound is sharp-enough for the golden form (cf. SqrtTwo's `1/2` for `x²-2y²`); the rounding/`nlinarith` packaging is the same shape as SqrtTwo's `normEuclidean`.

**File Summary (Euclidean.lean)**: 2 decls. Uses Common: `abs_intNorm_lt_of_abs_norm_le`,
`natAbs_lt_of_abs_ratCast_lt`. No sorry/set_option. `normEuclidean` ≈40 lines.
`abs_norm_int_lt_of_remainder_eq` is the SqrtFive twin of SqrtTwo's helper (golden norm form vs
`x²-2y²`).

---

## LocalGlobal.lean

### `def heightOneFive`
- **Type**: `HeightOneSpectrum (𝓞 K)` (asIdeal `(√5)`) — the finite place over `5`. **How**: `isPrime_span_sqrtFiveIntO`, `ne_bot` from `(√5)=0 ⇒ 5=0`. — **Uses**: [sqrtFiveIntO, isPrime_span_sqrtFiveIntO, sqrtFiveRoot_sq, goldenRoot] — public — **Lines**: 37-50

### `abbrev vFive`
- `FinitePlace K := FinitePlace.mk heightOneFive`. — **Uses**: [heightOneFive] — public — **Lines**: 53-54

### `example`s (ramification/inertia at 5)
- `ramificationIdx … heightOneFive = 2`, `inertiaDeg … = 1`. **How**: the PrimeSplitting lemmas. — **Uses**: [ramificationIdx_span_sqrtFiveIntO, inertiaDeg_span_sqrtFiveIntO] — anonymous — **Lines**: 56-62

### `abbrev CompletionAtFive`
- `:= heightOneFive.adicCompletion K`. — **Uses**: [heightOneFive] — public — **Lines**: 77-78

### `abbrev InfiniteCompletion` + `example`
- `v.Completion`; each `≅+* ℝ` (`ringEquivRealOfIsReal`, `infinitePlace_isReal`). — **Uses**: [infinitePlace_isReal] — public/anon — **Lines**: 92-93 / 95-97

### `example`s (product formula)
- `(∏_w w(φ)^mult)·(∏ᶠ_v v(φ)) = 1` for `φ` and for `fundamentalUnit`. **How**: `NumberField.prod_abs_eq_one` (nonzero from `φ²=φ+1` / `Units.ne_zero`). — **Uses**: [goldenRoot(_sq), fundamentalUnit] — anonymous — **Lines**: 111-128

### `abbrev SqrtFiveInfiniteAdeleRing` + `infinitePrincipalAdele_goldenRoot`/`_fundamentalUnit` + `example`s
- `InfiniteAdeleRing K` and principal-adele images; norm = `|N φ|`; dense range. **How**: `coe_norm_eq_abs_norm`, `denseRange_algebraMap`. — **Uses**: [goldenRoot, fundamentalUnit] — public/anon — **Lines**: 142-157

### `theorem canonicalEmbedding_goldenIntO_mem_integerLattice`
- `canonicalEmbedding K φ ∈ integerLattice K` — **How**: `simp [integerLattice]`. — **Uses**: [goldenIntO] — public — **Lines**: 171-174

### `abbrev mixedEmbedding_goldenRoot` / `theorem mixedEmbedding_goldenRoot_mem_convexBodyLT`
- `mixedEmbedding K φ`; membership in `convexBodyLT K f` when `w(φ) < f w` ∀w. **How**: `Set.mem_prod`/`mem_pi`, totally-real reduces complex coordinates (`infinitePlace_isReal`). — **Uses**: [goldenRoot, infinitePlace_isReal] — public — **Lines**: 190-191 / 193-208

### `example`s (fundamental cone) + `theorem polarSpace_nonempty`
- `MeasurableSet (fundamentalCone K)`, `(normLeOne K)`; `Nonempty (polarSpace K)`. **How**: mathlib lemmas / `infer_instance`. — **Uses**: [] — anon/public — **Lines**: 210-220

### `example` (house of φ > 0) / `theorem house_fundamentalUnit`
- `0 < house φ` (`one_le_house_of_isIntegral`); `house φ = (1+√5)/2` — **What**: archimedean size of the fundamental unit. **How**: every embedding sends `φ` to `(1±√5)/2` (`sq_eq_sq_iff_eq_or_eq_neg`); the conjugate `(1-√5)/2` has smaller norm; `le_antisymm` via `canonicalEmbedding.norm_le_iff` and `exists_realEmbedding_goldenRatio`. — **Uses**: [goldenRoot(_sq, _isIntegral), fundamentalUnit, exists_realEmbedding_goldenRatio] — public — **Lines**: 234-241 / 243-296 — **Notes**: proof ≈53 lines (>30); the only place a quantitative archimedean value of `φ` is computed.

### `abbrev SqrtFiveAdeleRing` + principal adeles + `theorem principalAdele_goldenRoot_ne_zero` / `principalAdele_fundamentalUnit_is_unit_everywhere`
- `AdeleRing (𝓞 K) K`; `φ`-adele `≠0`; fundamental unit has `v(·)=1` at every finite place. **How**: `AdeleRing.algebraMap_injective`; `norm_eq_one_iff_notMem` (if `φ ∈ 𝔪` then `1 ∈ 𝔪` via the inverse). — **Uses**: [goldenRoot(_sq), fundamentalUnit] — public — **Lines**: 310-346 — **Notes**: `principalAdele_fundamentalUnit_is_unit_everywhere` ≈20 lines.

### `abbrev sqrtFiveDedekindZeta` / `sqrtFiveDedekindZetaResidue` + `example`s
- `dedekindZeta K s`; residue; residue `> 0`; class-number-formula residue identity. **How**: `dedekindZeta_residue_pos`, `dedekindZeta_residue_def`. — **Uses**: [] — public/anon — **Lines**: 360-377 — **Notes**: residue identity references `regulator K`/`classNumber K`/`torsionOrder K`/`discr K` but is just the mathlib formula (does not re-prove them, so independent of the sorries).

**File Summary (LocalGlobal.lean)**: ~30 decls (~10 named theorems, ~12 abbrevs/defs, ~10 anonymous
`example`s; 9 `noncomputable section`s by topic). Key API: `heightOneFive`, `goldenRoot`,
`fundamentalUnit`, `infinitePlace_isReal`, `exists_realEmbedding_goldenRatio`,
`isPrime_span_sqrtFiveIntO`, `sqrtFiveRoot_sq`. Public results: place data, completions, infinite
completion ≅ ℝ, product formula, house of φ / fundamental unit, mixed-embedding/convex-body
membership, adele non-vanishing, Dedekind zeta residue + class-number formula. No sorry/set_option.
Proofs >30 lines: `house_fundamentalUnit` (~53). Many `example`s are demonstrative (not reusable
API).

---

## Cross-file observations

- **SqrtTwo twins (QuadraticAlgebra setup, near-identical)**: `K`, `degree_eq_two`,
  `IsQuadraticExtension`, AdjoinRoot↔QuadraticAlgebra equivalence block, the whole Units machinery
  (`torsionUnits_eq`, `torsionOrder_eq_two`, `unitRank_eq_one`,
  `exists_eq_torsion_mul_fundSystem_zpow`, `fundSystem_zpow_mem_torsion`,
  `eq_one_or_neg_one_of_mem_torsion`, `unitGroupStructure(_bijective)`,
  `fundamentalUnit_generates`+`regulator_eq`, now proved in both twins by different routes — SqrtTwo
  via `Pell`, SqrtFive via the real-embedding window-reduction), `normEuclidean`, the PrimeSplitting /
  ClassGroup / LocalGlobal scaffolding. Differences: generator (golden `φ=(1+√5)/2` vs `√2`),
  constants (disc 5 vs 8; norm form `x²+xy-y²` vs `x²-2y²`; ramified prime 5 vs 2; split criterion
  `p%5∈{1,4}` vs `p%8∈{1,7}`), and the golden-ratio intermediary (`goldenRoot` is the generator,
  `sqrtFiveRoot=2φ-1` derived).
- **EXTRA in SqrtFive (not in SqrtTwo's analogous slot)**: `RadicalModel`/`RadicalAdjoinRoot`
  presentations + all their equivalences (Basic 150-321), and `adjoin_sqrtFive_ne_integralClosure`
  (`ℤ[√5] ⊊ ℤ[φ]`, the genuinely-`5≡1 mod 4` fact; SqrtTwo has no such proper-suborder result).
  SqrtTwo's EXTRA `KUnitModel` (`1+√2`) block has no SqrtFive counterpart.
- **Generic helpers worth promoting to Common**: `ringHom_ext_golden` (Embeddings, twin of
  `ringHom_ext_sqrtTwo`), `abs_norm_int_lt_of_remainder_eq` (Euclidean), `absNorm_span_natCast`
  (PrimeSplitting).
- **Sorry blast radius**: none — the folder is now **sorry-free**. The former blockers
  `fundamentalUnit_generates` (explicit `±φⁿ`) and `regulator_eq` are proved, and the three
  results that depended on the former follow. The lesson for the project-wide API assessment: this
  "explicit fundamental unit" obstruction was *intrinsic mathematical difficulty*, not API
  immaturity — a faithful formalisation of the textbook real-embedding argument closed it with
  existing mathlib API.
