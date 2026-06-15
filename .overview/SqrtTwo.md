# SqrtTwo declaration inventory

Folder: `XYin/NumberField/FieldExamples/SqrtTwo/`
Field: real quadratic `ℚ(√2)`, built via `QuadraticAlgebra ℚ 2 0`.
Twin of SqrtFive (golden-ratio model). SqrtTwo additionally carries a second `AdjoinRoot`
presentation `KUnitModel = AdjoinRoot (X²-2X-1)` (root `1+√2`).

Namespace throughout: `NumberField.SqrtTwo`. Files open
`QuadraticAlgebra`, `NumberField`, `Module`, `Polynomial`, and (where relevant)
`NumberField.FieldExamples` (Common). All files are `noncomputable section` and remove the
`DivisionRing.toRatAlgebra` instance (the core files).

Cross-reference: `Common.lean` API used = `eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq`,
`eq_of_le_of_absNorm_eq`, `natAbs_lt_of_abs_ratCast_lt`, `torsionPowerHom`, `rankOnePowerHom`,
`not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ`,
`not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow`. Galois uses
`zmodAddEquivOfGenerator`, `AddEquiv.toMultiplicativeLeft` (also Common/shared infra).

---

## Basic.lean

### `instance Fact (∀ r : ℚ, r^2 ≠ 2 + 0*r)`
- **Type**: `Fact (∀ r : ℚ, r ^ 2 ≠ (2 : ℚ) + (0 : ℚ) * r)`
- **What**: `2` is not a rational square; the data instance feeding `QuadraticAlgebra` that the field is genuinely degree 2.
- **How**: assumes `r^2 = 2`, builds `IsSquare (2:ℚ)`, contradiction via `norm_num`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Visibility**: public (instance)
- **Lines**: 39-46

### `abbrev K`
- **Type**: `K : Type := QuadraticAlgebra ℚ (2 : ℚ) 0`
- **What**: the field `ℚ(√2)`.
- **How**: definitional.
- **Uses from project**: []
- **Visibility**: public — **Lines**: 49

### `instance NumberField K`
- **Type**: `NumberField K`
- **What**: `K` is a number field.
- **How**: `NumberField.of_module_finite ℚ K`.
- **Uses from project**: [] — **Visibility**: public — **Lines**: 51-52

### `abbrev sqrtTwoRoot`
- **Type**: `sqrtTwoRoot : K := QuadraticAlgebra.omega`
- **What**: distinguished `√2`. — **How**: definitional.
- **Uses from project**: [] — **Visibility**: public — **Lines**: 55

### `theorem sqrtTwoRoot_sq`
- **Type**: `sqrtTwoRoot ^ 2 = (2 : K)`
- **What**: `√2² = 2`. **How**: `QuadraticAlgebra.omega_mul_omega_eq_add`, `ext`/`norm_num`.
- **Uses from project**: [sqrtTwoRoot] — **Visibility**: public — **Lines**: 57-59
- **Notes**: heavily-used API (≈30 references across folder).

### `abbrev sqrtTwoPolynomial`
- **Type**: `ℚ[X] := X ^ 2 - C (2 : ℚ)` — **What**: defining poly. **How**: definitional.
- **Uses from project**: [] — **Visibility**: public — **Lines**: 62

### `instance Fact (Irreducible sqrtTwoPolynomial)`
- **What**: `X²-2` irreducible over ℚ. **How**: `Polynomial.irreducible_of_degree_le_three_of_not_isRoot` + `natDegree_X_pow_sub_C` + "2 not a square".
- **Uses from project**: [sqrtTwoPolynomial] — **Visibility**: public — **Lines**: 64-80

### `abbrev KAdjoinRoot`
- **Type**: `:= AdjoinRoot sqrtTwoPolynomial` — **What**: AdjoinRoot presentation. — **Uses**: [sqrtTwoPolynomial] — public — **Lines**: 83

### `abbrev sqrtTwoAdjoinRoot`
- **Type**: `KAdjoinRoot := AdjoinRoot.root sqrtTwoPolynomial` — **Uses**: [sqrtTwoPolynomial] — public — **Lines**: 86

### `theorem sqrtTwoAdjoinRoot_sq`
- **Type**: `sqrtTwoAdjoinRoot ^ 2 = (2 : KAdjoinRoot)` — **How**: `AdjoinRoot.eval₂_root` + `calc`.
- **Uses**: [sqrtTwoAdjoinRoot, sqrtTwoPolynomial] — public — **Lines**: 88-94

### `def sqrtTwoAdjoinRootToQuadratic`
- **Type**: `KAdjoinRoot →ₐ[ℚ] K` — **What**: AdjoinRoot→QuadraticAlgebra iso half. **How**: `AdjoinRoot.liftAlgHom`, relation `sqrtTwoRoot_sq`.
- **Uses**: [sqrtTwoPolynomial, sqrtTwoRoot, sqrtTwoRoot_sq] — public — **Lines**: 96-102

### `theorem sqrtTwoAdjoinRootToQuadratic_root` (@[simp])
- **Type**: `... sqrtTwoAdjoinRoot = sqrtTwoRoot` — **How**: `AdjoinRoot.liftAlgHom_root`.
- **Uses**: [sqrtTwoAdjoinRootToQuadratic, sqrtTwoAdjoinRoot, sqrtTwoPolynomial, sqrtTwoRoot] — public — **Lines**: 104-108

### `def sqrtTwoQuadraticToAdjoinRoot`
- **Type**: `K →ₐ[ℚ] KAdjoinRoot` — **How**: `QuadraticAlgebra.lift` with `sqrtTwoAdjoinRoot_sq`.
- **Uses**: [sqrtTwoAdjoinRoot, sqrtTwoAdjoinRoot_sq] — public — **Lines**: 110-113

### `theorem sqrtTwoQuadraticToAdjoinRoot_root` (@[simp])
- **Type**: `... sqrtTwoRoot = sqrtTwoAdjoinRoot` — **How**: simp.
- **Uses**: [sqrtTwoQuadraticToAdjoinRoot, sqrtTwoRoot, sqrtTwoAdjoinRoot] — public — **Lines**: 115-118

### `def sqrtTwoAdjoinRootEquivQuadratic`
- **Type**: `KAdjoinRoot ≃ₐ[ℚ] K` — **What**: equivalence of the two presentations. **How**: assembles fwd/back hom; `AdjoinRoot.algHom_ext`/`QuadraticAlgebra.algHom_ext` + `DFunLike.congr_fun`.
- **Uses**: [sqrtTwoAdjoinRootToQuadratic, sqrtTwoQuadraticToAdjoinRoot, sqrtTwoAdjoinRoot, sqrtTwoRoot, *_root lemmas] — public — **Lines**: 120-140

### `abbrev sqrtTwoAdjoinRootPowerBasis`
- **Type**: `PowerBasis ℚ KAdjoinRoot` — power basis `1,√2`. — **How**: `AdjoinRoot.powerBasis`.
- **Uses**: [sqrtTwoPolynomial] — public — **Lines**: 143-145

### `abbrev sqrtTwoPowerBasis`
- **Type**: `PowerBasis ℚ K := sqrtTwoAdjoinRootPowerBasis.map sqrtTwoAdjoinRootEquivQuadratic`
- **Uses**: [sqrtTwoAdjoinRootPowerBasis, sqrtTwoAdjoinRootEquivQuadratic] — public — **Lines**: 147-148
- **Notes**: key API (used 8+ times: finrank, discr, basis).

### `theorem sqrtTwoPowerBasis_gen` (@[simp])
- **Type**: `sqrtTwoPowerBasis.gen = sqrtTwoRoot` — **How**: `sqrtTwoAdjoinRootToQuadratic_root`.
- **Uses**: [sqrtTwoPowerBasis, sqrtTwoAdjoinRoot, sqrtTwoRoot, sqrtTwoAdjoinRootToQuadratic_root] — public — **Lines**: 150-153

### `theorem adjoin_sqrtTwoRoot_eq_top`
- **Type**: `Algebra.adjoin ℚ {sqrtTwoRoot} = ⊤` — **How**: `PowerBasis.adjoin_gen_eq_top`.
- **Uses**: [sqrtTwoPowerBasis_gen, sqrtTwoPowerBasis, sqrtTwoRoot] — public — **Lines**: 156-158

### `theorem sqrtTwoPowerBasis_dim`
- **Type**: `sqrtTwoPowerBasis.dim = 2` — **How**: `natDegree_X_pow_sub_C`.
- **Uses**: [sqrtTwoPowerBasis, sqrtTwoPolynomial] — public — **Lines**: 160-163
- **Notes**: key API (used 6+ times).

### `theorem degree_eq_two`
- **Type**: `Module.finrank ℚ K = 2` — **How**: `PowerBasis.finrank` + `sqrtTwoPowerBasis_dim`.
- **Uses**: [sqrtTwoPowerBasis, sqrtTwoPowerBasis_dim] — public — **Lines**: 165-168

### `instance Algebra.IsQuadraticExtension ℚ K`
- **What**: K/ℚ quadratic. **How**: `finrank_eq_two' := degree_eq_two`.
- **Uses**: [degree_eq_two] — public — **Lines**: 170-171

### `abbrev sqrtTwoUnitPolynomial`
- **Type**: `ℚ[X] := C 1 * X^2 + C(-2)*X + C(-1)` — defining poly of `1+√2`.
- **Uses**: [] — public — **Lines**: 177-178
- **Notes**: EXTRA vs SqrtFive (second/unit presentation).

### `instance Fact (Irreducible sqrtTwoUnitPolynomial)`
- **How**: `irreducible_of_degree_le_three_of_not_isRoot` + `natDegree_quadratic` + "2 not a square".
- **Uses**: [sqrtTwoUnitPolynomial] — public — **Lines**: 180-192 — **Notes**: EXTRA.

### `abbrev KUnitModel`
- **Type**: `:= AdjoinRoot sqrtTwoUnitPolynomial` — the `1+√2` model. — **Uses**: [sqrtTwoUnitPolynomial] — public — **Lines**: 195 — **Notes**: EXTRA.

### `abbrev sqrtTwoUnitRoot`
- **Type**: `KUnitModel := AdjoinRoot.root sqrtTwoUnitPolynomial` — **Uses**: [sqrtTwoUnitPolynomial] — public — **Lines**: 198 — **Notes**: EXTRA.

### `theorem sqrtTwoUnitRoot_relation`
- **Type**: `sqrtTwoUnitRoot^2 - 2*sqrtTwoUnitRoot - 1 = 0` — **How**: `AdjoinRoot.eval₂_root`.
- **Uses**: [sqrtTwoUnitRoot, sqrtTwoUnitPolynomial] — public — **Lines**: 200-203 — **Notes**: EXTRA.

### `def sqrtTwoToUnitModel`
- **Type**: `K →ₐ[ℚ] KUnitModel` (`√2 ↦ β-1`) — **How**: `QuadraticAlgebra.lift`, relation via `linear_combination`.
- **Uses**: [sqrtTwoUnitRoot, sqrtTwoUnitRoot_relation] — public — **Lines**: 206-217 — **Notes**: EXTRA.

### `theorem sqrtTwoToUnitModel_root` (@[simp])
- **Type**: `sqrtTwoToUnitModel sqrtTwoRoot = sqrtTwoUnitRoot - 1` — **Uses**: [sqrtTwoToUnitModel, sqrtTwoRoot, sqrtTwoUnitRoot] — public — **Lines**: 219-222 — **Notes**: EXTRA.

### `def unitModelToSqrtTwo`
- **Type**: `KUnitModel →ₐ[ℚ] K` (`β ↦ √2+1`) — **How**: `AdjoinRoot.liftAlgHom`, relation via `sqrtTwoRoot_sq`.
- **Uses**: [sqrtTwoUnitPolynomial, sqrtTwoRoot, sqrtTwoRoot_sq] — public — **Lines**: 225-233 — **Notes**: EXTRA.

### `theorem unitModelToSqrtTwo_root` (@[simp])
- **Type**: `unitModelToSqrtTwo sqrtTwoUnitRoot = sqrtTwoRoot + 1` — **How**: `AdjoinRoot.liftAlgHom_root`.
- **Uses**: [unitModelToSqrtTwo, sqrtTwoUnitRoot, sqrtTwoUnitPolynomial, sqrtTwoRoot] — public — **Lines**: 235-240 — **Notes**: EXTRA.

### `def sqrtTwoEquivUnitModel`
- **Type**: `K ≃ₐ[ℚ] KUnitModel` — **How**: fwd/back hom + algHom_ext + `DFunLike`.
- **Uses**: [sqrtTwoToUnitModel, unitModelToSqrtTwo, sqrtTwoRoot, sqrtTwoUnitRoot, *_root] — public — **Lines**: 243-266 — **Notes**: EXTRA, never used elsewhere in folder.

### `theorem sqrtTwoEquivUnitModel_root`
- **Type**: `sqrtTwoEquivUnitModel sqrtTwoRoot = sqrtTwoUnitRoot - 1` — **How**: `sqrtTwoToUnitModel_root`.
- **Uses**: [sqrtTwoEquivUnitModel, sqrtTwoRoot, sqrtTwoUnitRoot, sqrtTwoToUnitModel_root] — public — **Lines**: 268-270 — **Notes**: EXTRA, unused.

**File Summary (Basic.lean)**: ~30 decls (3 instances, ~7 defs, ~10 theorems, ~10 abbrevs).
Key API (3+ uses): `sqrtTwoRoot`, `sqrtTwoRoot_sq`, `sqrtTwoPolynomial`, `sqrtTwoPowerBasis`,
`sqrtTwoPowerBasis_dim`, `sqrtTwoPowerBasis_gen`, `sqrtTwoAdjoinRootEquivQuadratic`.
Unused outside file: the entire `KUnitModel` block (lines 177-270) — second presentation, never
referenced by any sibling file. No sorry, no set_option, no >30-line proof (longest ≈24).

---

## Galois.lean

### `def sqrtTwoConjHom`
- **Type**: `K →ₐ[ℚ] K` (`√2 ↦ -√2`) — **How**: `QuadraticAlgebra.lift` with `neg_sq`, `sqrtTwoRoot_sq`.
- **Uses**: [sqrtTwoRoot, sqrtTwoRoot_sq] — public — **Lines**: 35-38

### `theorem sqrtTwoConjHom_root` (@[simp])
- **Type**: `sqrtTwoConjHom sqrtTwoRoot = -sqrtTwoRoot` — **How**: simp.
- **Uses**: [sqrtTwoConjHom, sqrtTwoRoot] — public — **Lines**: 40-42

### `def sqrtTwoConj`
- **Type**: `K ≃ₐ[ℚ] K` — involutive conjugation. **How**: invFun = self; `QuadraticAlgebra.algHom_ext`.
- **Uses**: [sqrtTwoConjHom, sqrtTwoRoot, sqrtTwoConjHom_root] — public — **Lines**: 45-63

### `theorem sqrtTwoConj_root`
- **Type**: `sqrtTwoConj sqrtTwoRoot = -sqrtTwoRoot` — **Uses**: [sqrtTwoConj, sqrtTwoConjHom_root, sqrtTwoRoot] — public — **Lines**: 65-67

### `theorem isGalois`
- **Type**: `IsGalois ℚ K` — **How**: `infer_instance` (quadratic ⇒ Galois). — **Uses**: [] — public — **Lines**: 69-71

### `theorem sqrtTwo_gal_eq_id_or_conj`
- **Type**: `(σ : Gal(K/ℚ)) → σ = 1 ∨ σ = sqrtTwoConj` — **What**: classifies the 2 automorphisms. **How**: `σ√2` squares to 2, factor `(σ√2-√2)(σ√2+√2)=0`, `QuadraticAlgebra.algHom_ext`.
- **Uses**: [sqrtTwoRoot, sqrtTwoRoot_sq, sqrtTwoConj, sqrtTwoConjHom_root] — public — **Lines**: 73-100 — **Notes**: proof 28 lines.

### `private theorem sqrtTwoConj_ne_one`
- **Type**: `sqrtTwoConj ≠ 1` — **How**: else `-√2=√2 ⇒ √2=0 ⇒ 2=0`. — **Uses**: [sqrtTwoConj, sqrtTwoConjHom_root, sqrtTwoRoot, sqrtTwoRoot_sq] — private — **Lines**: 102-121

### `theorem gal_natCard_eq_two`
- **Type**: `Nat.card Gal(K/ℚ) = 2` — **How**: `Nat.card_eq_two_iff` + classification.
- **Uses**: [sqrtTwoConj, sqrtTwoConj_ne_one, sqrtTwo_gal_eq_id_or_conj] — public — **Lines**: 123-128

### `private abbrev CyclicTwo`
- **Type**: `Multiplicative (ZMod 2)` — **Uses**: [] — private — **Lines**: 131

### `private theorem sqrtTwoGal_additive_generator`
- **Type**: conjugation generates `Additive Gal(K/ℚ)` — **How**: case split via `sqrtTwo_gal_eq_id_or_conj`, `zmultiples`.
- **Uses**: [sqrtTwo_gal_eq_id_or_conj, sqrtTwoConj] — private — **Lines**: 134-142

### `private noncomputable abbrev cyclicTwoEquivSqrtTwoGal`
- **Type**: `CyclicTwo ≃* Gal(K/ℚ)` — **How**: `AddEquiv.toMultiplicativeLeft` + `zmodAddEquivOfGenerator`.
- **Uses (incl. shared infra)**: [sqrtTwoGal_additive_generator, gal_natCard_eq_two, sqrtTwoConj] — private — **Lines**: 148-150

### `private noncomputable abbrev sqrtTwoGalEquivCyclicTwo`
- **Type**: `Gal(K/ℚ) ≃* CyclicTwo := cyclicTwoEquivSqrtTwoGal.symm` — **Uses**: [cyclicTwoEquivSqrtTwoGal] — private — **Lines**: 153-154

### `theorem galoisGroupStructure`
- **Type**: `Nonempty (Gal(K/ℚ) ≃* Multiplicative (ZMod 2))` — **How**: wraps the iso.
- **Uses**: [sqrtTwoGalEquivCyclicTwo] — public — **Lines**: 158-159

**File Summary (Galois.lean)**: 13 decls (2 defs, ~7 theorems, 4 abbrevs). Key API: `sqrtTwoConj`,
`sqrtTwoConjHom_root`, `sqrtTwo_gal_eq_id_or_conj`, `gal_natCard_eq_two`. Public results:
`isGalois`, `galoisGroupStructure`. No sorry/set_option; one proof at 28 lines
(`sqrtTwo_gal_eq_id_or_conj`). `sqrtTwoConj` double-derives the same `hcomp` in both `left_inv`
and `right_inv` (mild duplication).

---

## Embeddings.lean

### `private theorem ringHom_ext_sqrtTwo`
- **Type**: `{f g : K →+* ℂ} (h : f √2 = g √2) → f = g` — **What**: ring homs to ℂ are determined by image of `√2`. **How**: `QuadraticAlgebra.mk_eq_add_smul_omega`, `eq_ratCast` on `ℚ`-part.
- **Uses**: [sqrtTwoRoot] — private — **Lines**: 34-45
- **Notes**: GENERIC-looking; a quadratic-algebra `ringHom_ext` candidate for Common.

### `theorem isTotallyReal`
- **Type**: `NumberField.IsTotallyReal K` — **How**: each embedding fixes `√2` under conjugation; factor `(z̄-z)(z̄+z)=0`, exclude `re=0` by `nlinarith [sq_nonneg z.im]`.
- **Uses**: [ringHom_ext_sqrtTwo, sqrtTwoRoot, sqrtTwoRoot_sq] — public — **Lines**: 47-73 — **Notes**: 27-line proof.

### `theorem nrComplexPlaces_eq_zero`
- **Type**: `InfinitePlace.nrComplexPlaces K = 0` — **How**: `IsTotallyReal.nrComplexPlaces_eq_zero`.
- **Uses**: [isTotallyReal] — public — **Lines**: 75-79

### `theorem nrRealPlaces_eq_two`
- **Type**: `InfinitePlace.nrRealPlaces K = 2` — **How**: `card_add_two_mul_card_eq_rank` + finrank 2 + `omega`.
- **Uses**: [sqrtTwoPowerBasis, sqrtTwoPowerBasis_dim, nrComplexPlaces_eq_zero] — public — **Lines**: 81-90
- **Notes**: key API (used in ClassGroup, Units).

### `theorem exists_realEmbedding_pos`
- **Type**: `∃ σ : K →ₐ[ℚ] ℝ, σ √2 = Real.sqrt 2` — **How**: `QuadraticAlgebra.lift` with `Real.mul_self_sqrt`.
- **Uses**: [sqrtTwoRoot] — public — **Lines**: 107-114

### `theorem exists_realEmbedding_neg`
- **Type**: `∃ σ : K →ₐ[ℚ] ℝ, σ √2 = -Real.sqrt 2` — analog. — **Uses**: [sqrtTwoRoot] — public — **Lines**: 116-123

### `theorem realEmbedding_root_eq_pos_or_neg`
- **Type**: `(σ : K →ₐ[ℚ] ℝ) → σ√2 = √2 ∨ σ√2 = -√2` — **How**: `sq_eq_sq_iff_eq_or_eq_neg`.
- **Uses**: [sqrtTwoRoot, sqrtTwoRoot_sq] — public — **Lines**: 125-134

### `theorem infinitePlace_card_eq_two`
- **Type**: `Fintype.card (InfinitePlace K) = 2` — **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces`.
- **Uses**: [nrRealPlaces_eq_two, nrComplexPlaces_eq_zero] — public — **Lines**: 137-140

### `theorem infinitePlace_isReal`
- **Type**: `(v) → InfinitePlace.IsReal v` — **How**: `IsTotallyReal.isReal`.
- **Uses**: [isTotallyReal] — public — **Lines**: 142-146

### `theorem infinitePlace_apply_sqrtTwoRoot`
- **Type**: `(v) → v √2 = Real.sqrt 2` — **How**: `norm_embedding_eq`, square argument, `sq_eq_sq_iff`.
- **Uses**: [sqrtTwoRoot, sqrtTwoRoot_sq] — public — **Lines**: 148-169 — **Notes**: key API (LocalGlobal).

**File Summary (Embeddings.lean)**: 10 decls (all theorems; 1 private). Key API:
`isTotallyReal`, `nrRealPlaces_eq_two`, `nrComplexPlaces_eq_zero`, `infinitePlace_isReal`,
`infinitePlace_apply_sqrtTwoRoot`. No sorry/set_option. `isTotallyReal` 27 lines.
`ringHom_ext_sqrtTwo` is a generic helper.

---

## Discriminant.lean

Empty placeholder: only `noncomputable section` + empty namespace. **0 declarations.** All
discriminant content lives in RingOfIntegers.lean.

---

## RingOfIntegers.lean

### `theorem sqrtTwoRoot_isIntegral`
- **Type**: `IsIntegral ℤ sqrtTwoRoot` — **How**: witness `X²-C 2`, `monic_X_pow_sub_C`.
- **Uses**: [sqrtTwoRoot, sqrtTwoRoot_sq] — public — **Lines**: 34-37 — **Notes**: key API.

### `abbrev sqrtTwoInteger`
- **Type**: `𝓞 K := ⟨sqrtTwoRoot, sqrtTwoRoot_isIntegral⟩` — **What**: `√2` as algebraic integer.
- **Uses**: [sqrtTwoRoot, sqrtTwoRoot_isIntegral] — public — **Lines**: 40-41 — **Notes**: most-used integral element (40+ refs).

### `local notation 𝓟₂`
- `Submodule.span ℤ {(2:ℤ)}` — **Lines**: 43.

### `abbrev sqrtTwoIntegerPolynomial`
- **Type**: `ℤ[X] := X^2 - C 2` — **Uses**: [] — public — **Lines**: 46.

### `theorem sqrtTwo_minpoly_rat`
- **Type**: `minpoly ℚ √2 = sqrtTwoPolynomial` — **How**: transport via `sqrtTwoAdjoinRootEquivQuadratic`, `minpoly.algEquiv_eq`, `AdjoinRoot.minpoly_root`.
- **Uses**: [sqrtTwoAdjoinRootToQuadratic_root, sqrtTwoAdjoinRootEquivQuadratic, sqrtTwoAdjoinRoot, sqrtTwoPolynomial] — public — **Lines**: 49-57.

### `theorem sqrtTwo_minpoly_int`
- **Type**: `minpoly ℤ √2 = sqrtTwoIntegerPolynomial` — **How**: `map_injective` + `minpoly.isIntegrallyClosed_eq_field_fractions'` + `sqrtTwo_minpoly_rat`.
- **Uses**: [sqrtTwoRoot_isIntegral, sqrtTwo_minpoly_rat, sqrtTwoIntegerPolynomial] — public — **Lines**: 60-67.

### `theorem sqrtTwo_minpoly_int_isEisenstein`
- **Type**: `(minpoly ℤ √2).IsEisensteinAt 𝓟₂` — **How**: `monic_X_pow_sub_C.isEisensteinAt_of_mem_of_notMem`.
- **Uses**: [sqrtTwo_minpoly_int] — public — **Lines**: 69-82.

### `theorem sqrtTwoPowerBasis_discr`
- **Type**: `Algebra.discr ℚ sqrtTwoPowerBasis.basis = 8` — **How**: `discr_powerBasis_eq_norm`, `norm_gen_eq_coeff_zero_minpoly`, `Algebra.norm_algebraMap`.
- **Uses**: [sqrtTwoPowerBasis, sqrtTwoPolynomial, sqrtTwoPowerBasis_gen, sqrtTwoRoot, sqrtTwo_minpoly_rat] — public — **Lines**: 84-106 — **Notes**: 22-line proof.

### `theorem sqrtTwo_integral_mem_adjoin`
- **Type**: `(z hz : IsIntegral ℤ z) → z ∈ Algebra.adjoin ℤ {√2}` — **What**: every integer lies in `ℤ[√2]`. **How**: `discr_mul_isIntegral_mem_adjoin` (gives `8•z`), strip `2³` via `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt`.
- **Uses**: [sqrtTwoPowerBasis, sqrtTwoPowerBasis_gen, sqrtTwoRoot, sqrtTwoPowerBasis_discr, sqrtTwo_minpoly_int_isEisenstein] — public — **Lines**: 108-133 — **Notes**: 25 lines; core ring-of-integers argument.

### `theorem isIntegralClosure_adjoin_sqrtTwoRoot`
- **Type**: `IsIntegralClosure (Algebra.adjoin ℤ {√2}) ℤ K` — **How**: builds the two-part structure; uses `sqrtTwo_integral_mem_adjoin`, `Algebra.IsIntegral.adjoin`.
- **Uses**: [sqrtTwoRoot, sqrtTwo_integral_mem_adjoin, sqrtTwoRoot_isIntegral] — public — **Lines**: 139-157.

### `theorem sqrtTwoInteger_adjoin_eq_top`
- **Type**: `Algebra.adjoin ℤ {sqrtTwoInteger} = ⊤` — **What**: 𝓞K generated by √2 over ℤ. **How**: lift field-level adjoin via `adjoin_singleton_eq_range_aeval`.
- **Uses**: [sqrtTwoInteger, sqrtTwoRoot, sqrtTwo_integral_mem_adjoin] — public — **Lines**: 159-178 — **Notes**: key API (PrimeSplitting, Units).

### `theorem sqrtTwoInteger_minpoly`
- **Type**: `minpoly ℤ sqrtTwoInteger = sqrtTwoIntegerPolynomial` — **How**: `minpoly.isIntegrallyClosed_eq_field_fractions` (explicit instance args) + `sqrtTwo_minpoly_rat`.
- **Uses**: [sqrtTwoInteger, sqrtTwoRoot, sqrtTwo_minpoly_rat, sqrtTwoIntegerPolynomial] — public — **Lines**: 180-202 — **Notes**: 23 lines; verbose `@minpoly...` instance call.

### `abbrev sqrtTwoExplicitIntegralPowerBasis`
- **Type**: `PowerBasis ℤ (𝓞 K)` — **How**: `PowerBasis.ofAdjoinEqTop'`.
- **Uses**: [sqrtTwoInteger, sqrtTwoInteger_adjoin_eq_top] — public — **Lines**: 208-211.

### `theorem sqrtTwoExplicitIntegralPowerBasis_dim`
- **Type**: `... .dim = 2` — **How**: `ofAdjoinEqTop'_dim`, `sqrtTwoInteger_minpoly`, `natDegree_X_pow_sub_C`.
- **Uses**: [sqrtTwoExplicitIntegralPowerBasis, sqrtTwoInteger_minpoly, sqrtTwoIntegerPolynomial] — public — **Lines**: 213-218.

### `abbrev sqrtTwoExplicitIntegralBasis`
- **Type**: `Basis (Fin 2) ℤ (𝓞 K)` — basis `[1,√2]`. **How**: reindex power basis.
- **Uses**: [sqrtTwoExplicitIntegralPowerBasis, sqrtTwoExplicitIntegralPowerBasis_dim] — public — **Lines**: 220-223 — **Notes**: key API (PrimeSplitting, Units).

### `theorem sqrtTwoExplicitIntegralBasis_zero`
- **Type**: `sqrtTwoExplicitIntegralBasis 0 = 1` — **How**: `basis_eq_pow`, `pow_zero`.
- **Uses**: [sqrtTwoExplicitIntegralBasis, sqrtTwoExplicitIntegralPowerBasis, sqrtTwoExplicitIntegralPowerBasis_dim] — public — **Lines**: 225-234.

### `theorem sqrtTwoExplicitIntegralBasis_one`
- **Type**: `sqrtTwoExplicitIntegralBasis 1 = sqrtTwoInteger` — analog. — **Uses**: [same + sqrtTwoInteger] — public — **Lines**: 236-245.

### `theorem sqrtTwoInteger_sq`
- **Type**: `sqrtTwoInteger ^ 2 = (2 : 𝓞 K)` — **How**: `Subtype.ext` + `sqrtTwoRoot_sq`.
- **Uses**: [sqrtTwoInteger, sqrtTwoRoot, sqrtTwoRoot_sq] — public — **Lines**: 247-250 — **Notes**: key API (PrimeSplitting; 12+ refs).

### `theorem sqrtTwoExplicitIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ sqrtTwoExplicitIntegralBasis = 8` — **How**: descend to ℚ via `Algebra.discr_localizationLocalization` + `Module.Basis.localizationLocalization`, identify with `sqrtTwoPowerBasis.basis`, use `sqrtTwoPowerBasis_discr`.
- **Uses**: [sqrtTwoExplicitIntegralBasis, sqrtTwoPowerBasis, sqrtTwoPowerBasis_dim, sqrtTwoExplicitIntegralBasis_zero/_one, sqrtTwoRoot, sqrtTwoPowerBasis_gen, sqrtTwoPowerBasis_discr] — public — **Lines**: 252-299 — **Notes**: `set_option linter.flexible false`; proof ~47 lines, heaviest in file.

### `theorem sqrtTwo_numberField_discr`
- **Type**: `NumberField.discr K = 8` — **How**: `discr_eq_discr` + basis discriminant.
- **Uses**: [sqrtTwoExplicitIntegralBasis, sqrtTwoExplicitIntegralBasis_discr] — public — **Lines**: 301-304 — **Notes**: key public result; used in ClassGroup, PrimeSplitting.

### `theorem integralBasis_discr`
- **Type**: `Algebra.discr ℚ (integralBasis K) = 8` — **How**: `NumberField.coe_discr` + above.
- **Uses**: [sqrtTwo_numberField_discr] — public — **Lines**: 306-311 — **Notes**: `attribute [local instance] DivisionRing.toRatAlgebra`.

### `example` (discr under matrix mulVec)
- **Lines**: 313-317 — `Algebra.discr_of_matrix_mulVec`. Anonymous, no name. **Uses**: [sqrtTwoPowerBasis].

### `example` (det ±1 keeps discr 8)
- **Lines**: 319-334 — **Uses**: [sqrtTwoPowerBasis, sqrtTwoPowerBasis_discr]. Anonymous.

### `theorem sqrtTwoInteger_dvd_two`
- **Type**: `sqrtTwoInteger ∣ (2 : 𝓞 K)` — **How**: from `sqrtTwoInteger_sq`. — **Uses**: [sqrtTwoInteger, sqrtTwoInteger_sq] — public — **Lines**: 336-342.

### `theorem norm_eq_normForm`
- **Type**: `Algebra.norm ℚ x = x.re^2 - 2*x.im^2` — **What**: norm form (binary quadratic form disc 8). **How**: `QuadraticAlgebra.det_toLinearMap_eq_norm`, `QuadraticAlgebra.norm_def`.
- **Uses**: [] — public — **Lines**: 358-366 — **Notes**: key API (Euclidean, norm-form chain).

### `theorem intNorm_eq_normForm`
- **Type**: `(x y : ℤ) → Algebra.norm ℤ (x•1 + y•√2) = x^2 - 2*y^2` — **How**: `Algebra.coe_norm_int` to push to ℚ, `norm_eq_normForm`, cast back.
- **Uses**: [sqrtTwoInteger, sqrtTwoRoot, norm_eq_normForm] — public — **Lines**: 368-386 — **Notes**: heavily-used API (PrimeSplitting norm computations, 10+ refs).

### `theorem isUnit_iff_normForm`
- **Type**: `IsUnit (x•1 + y•√2) ↔ x²-2y² = 1 ∨ = -1` — **What**: Pell unit criterion. **How**: `NumberField.isUnit_iff_norm`, `intNorm_eq_normForm`, `abs_eq`.
- **Uses**: [sqrtTwoInteger, intNorm_eq_normForm] — public — **Lines**: 388-402.

**File Summary (RingOfIntegers.lean)**: ~27 decls (~17 theorems, 5 abbrevs, 2 anonymous examples,
1 notation). Key API (3+): `sqrtTwoInteger`, `sqrtTwoInteger_sq`, `sqrtTwoExplicitIntegralBasis`
(+ `_zero/_one`), `sqrtTwo_numberField_discr`, `sqrtTwoInteger_adjoin_eq_top`,
`intNorm_eq_normForm`, `norm_eq_normForm`, `sqrtTwoInteger_minpoly`. Public results: ring of
integers = ℤ[√2] (`sqrtTwoInteger_adjoin_eq_top`), discriminant 8 (`sqrtTwo_numberField_discr`),
integral basis. One `set_option linter.flexible false`. Proofs >30 lines:
`sqrtTwoExplicitIntegralBasis_discr` (~47). The two `example`s are unused demonstrations.

---

## ClassGroup.lean

### `abbrev sqrtTwoRootFractionalIdeal`
- **Type**: `FractionalIdeal (𝓞 K)⁰ K := spanSingleton ... sqrtTwoRoot` — **Uses**: [sqrtTwoRoot] — public — **Lines**: 36-37 — **Notes**: only used by `sqrtTwoRoot_mem_fractionalIdeal`/`_absNorm`.

### `abbrev ramifiedPrimeFractionalIdeal`
- **Type**: fractional ideal `(√2)` — **Uses**: [sqrtTwoInteger] — public — **Lines**: 40-41 — **Notes**: used only by its `_ne_zero` lemma; otherwise unused.

### `theorem sqrtTwoRoot_mem_fractionalIdeal`
- **Type**: `√2 ∈ sqrtTwoRootFractionalIdeal` — **How**: `mem_spanSingleton`. — **Uses**: [sqrtTwoRoot, sqrtTwoRootFractionalIdeal] — public — **Lines**: 43-46 — **Notes**: unused elsewhere.

### `theorem sqrtTwoRootFractionalIdeal_absNorm`
- **Type**: `absNorm = |Algebra.norm ℚ √2|` — **How**: `absNorm_span_singleton`. — **Uses**: [sqrtTwoRootFractionalIdeal, sqrtTwoRoot] — public — **Lines**: 48-50 — **Notes**: unused elsewhere.

### `theorem ramifiedPrimeFractionalIdeal_ne_zero`
- **Type**: `ramifiedPrimeFractionalIdeal ≠ 0` — **How**: `coeIdeal_ne_zero` + `absNorm_span_sqrtTwoInteger`.
- **Uses**: [ramifiedPrimeFractionalIdeal, absNorm_span_sqrtTwoInteger] — public — **Lines**: 52-59 — **Notes**: forward ref to PrimeSplitting (`absNorm_span_sqrtTwoInteger`).

### `theorem isPrincipalIdealRing`
- **Type**: `IsPrincipalIdealRing (𝓞 K)` — **What**: class number 1 ring content. **How**: `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` + Minkowski bound estimate (`Real.pi_gt_three`, `nlinarith`).
- **Uses**: [sqrtTwo_numberField_discr, sqrtTwoPowerBasis, sqrtTwoPowerBasis_dim] — public — **Lines**: 79-94 — **Notes**: key API; 16 lines.

### `theorem uniqueFactorizationMonoid`
- **Type**: `UniqueFactorizationMonoid (𝓞 K)` — **How**: from PID. — **Uses**: [isPrincipalIdealRing] — public — **Lines**: 96-99.

### `theorem classNumber_eq_one`
- **Type**: `NumberField.classNumber K = 1` — **How**: `classNumber_eq_one_iff.mpr isPrincipalIdealRing`.
- **Uses**: [isPrincipalIdealRing] — public — **Lines**: 101-104.

### `theorem classGroupStructure`
- **Type**: `Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1))` — **How**: `Subsingleton` from card 1 + `MulEquiv.ofBijective`.
- **Uses**: [classNumber_eq_one] — public — **Lines**: 106-118.

### `abbrev unitIdealRepresentative`
- **Type**: `(Ideal (𝓞 K))⁰ := ⟨⊤, _⟩` — **Uses**: [] — public — **Lines**: 121.

### `theorem classGroupRepresentative`
- **Type**: `(C) → C = ClassGroup.mk0 unitIdealRepresentative` — **How**: `Subsingleton.elim`.
- **Uses**: [classNumber_eq_one, unitIdealRepresentative] — public — **Lines**: 123-131.

**File Summary (ClassGroup.lean)**: 11 decls (6 theorems, ~3 abbrevs). Key API: `isPrincipalIdealRing`
(used 3+ — uniqueFactorizationMonoid, classNumber, etc.). Public: `classNumber_eq_one`,
`classGroupStructure`, `isPrincipalIdealRing`, `uniqueFactorizationMonoid`. No sorry/set_option;
no >30-line proof. The fractional-ideal block (lines 36-50) is largely demonstrative/unused.

---

## PrimeSplitting.lean

### `theorem span_two_eq`
- **Type**: `Ideal.span {2} = Ideal.span {√2}^2` — **What**: 2 totally ramified. **How**: `span_singleton_pow` + `sqrtTwoInteger_sq`.
- **Uses**: [sqrtTwoInteger, sqrtTwoInteger_sq] — public — **Lines**: 38-39.

### `theorem absNorm_span_sqrtTwoInteger`
- **Type**: `absNorm (span {√2}) = 2` — **How**: `intNorm_eq_normForm 0 1`, `absNorm_span_singleton`.
- **Uses**: [intNorm_eq_normForm, sqrtTwoInteger] — public — **Lines**: 40-47 — **Notes**: key API (ClassGroup, LocalGlobal, different).

### `theorem isPrime_span_sqrtTwoInteger`
- **Type**: `(span {√2}).IsPrime` — **How**: `isPrime_of_irreducible_absNorm` (norm 2 prime). — **Uses**: [absNorm_span_sqrtTwoInteger, sqrtTwoInteger] — public — **Lines**: 49-54 — **Notes**: key API (LocalGlobal vTwo).

### `theorem liesOver_span_sqrtTwoInteger`
- **Type**: `(span {√2}).LiesOver (span {2:ℤ})` — **How**: `liesOver_span_iff`. — **Uses**: [isPrime_span_sqrtTwoInteger, sqrtTwoInteger, sqrtTwoInteger_sq] — public — **Lines**: 56-65.

### `theorem inertiaDeg_span_sqrtTwoInteger`
- **Type**: inertia deg = 1 — **How**: `absNorm_eq_pow_inertiaDeg'`, `Nat.Prime.pow_eq_iff`. — **Uses**: [liesOver_span_sqrtTwoInteger, absNorm_span_sqrtTwoInteger, sqrtTwoInteger] — public — **Lines**: 67-75.

### `theorem ramificationIdx_span_sqrtTwoInteger`
- **Type**: ram idx = 2 — **How**: `ramificationIdx_spec` + norm-divisibility (`absNorm_dvd_absNorm_of_le`).
- **Uses**: [sqrtTwoInteger, span_two_eq, intNorm_eq_normForm, absNorm_span_sqrtTwoInteger] — public — **Lines**: 77-98.

### `theorem span_seven_eq`
- **Type**: `span {7} = span {3+√2} * span {3-√2}` — **How**: `(3+√2)(3-√2)=9-2=7` via `sqrtTwoInteger_sq`. — **Uses**: [sqrtTwoInteger, sqrtTwoInteger_sq] — public — **Lines**: 100-110.

### `theorem absNorm_span_three_add_sqrtTwo` / `_sub_sqrtTwo`
- **Type**: norm `=7` each — **How**: `intNorm_eq_normForm 3 ±1`. — **Uses**: [intNorm_eq_normForm, sqrtTwoInteger] — public — **Lines**: 112-118 / 127-138.

### `theorem isPrime_span_three_add_sqrtTwo` / `_sub_sqrtTwo`
- **Type**: each prime — **How**: `isPrime_of_irreducible_absNorm` (norm 7). — **Uses**: [absNorm_span_three_add/sub_sqrtTwo, sqrtTwoInteger] — public — **Lines**: 120-125 / 140-145 — **Notes**: key API (LocalGlobal vSeven±).

### `theorem liesOver_span_three_add_sqrtTwo` / `_sub_sqrtTwo`
- **Type**: lies over `(7)` — **How**: `liesOver_span_iff`. — **Uses**: [isPrime_span_three_add/sub_sqrtTwo, sqrtTwoInteger, sqrtTwoInteger_sq] — public — **Lines**: 147-169.

### `theorem inertiaDeg_span_three_add_sqrtTwo` / `_sub_sqrtTwo`
- **Type**: inertia deg 1 — **How**: `absNorm_eq_pow_inertiaDeg'`. — **Uses**: [liesOver_*, absNorm_span_three_add/sub_sqrtTwo] — public — **Lines**: 171-189.

### `private theorem absNorm_ne_three`
- **Type**: `(P) → absNorm P ≠ 3` — **What**: no prime with residue field 𝔽₃ (X²-2 has no root mod 3). **How**: `ZMod.ringEquivOfPrime`, then `decide` over `ZMod 3`.
- **Uses**: [sqrtTwoInteger, sqrtTwoInteger_sq] — private — **Lines**: 190-207.

### `theorem isPrime_span_three`
- **Type**: `(span {3:𝓞K}).IsPrime` — **What**: 3 inert. **How**: norm 9; rule out maximal sub-ideals of norm 1 and 3 (`absNorm_ne_three`), force norm 9, `eq_of_le_of_absNorm_eq` (Common).
- **Uses**: [intNorm_eq_normForm, sqrtTwoInteger, absNorm_ne_three, eq_of_le_of_absNorm_eq] — public — **Lines**: 209-242 — **Notes**: 33-line proof; key API (vThree).

### `theorem absNorm_span_three`
- **Type**: `absNorm (span {3}) = 9` — **How**: `intNorm_eq_normForm 3 0`. — **Uses**: [intNorm_eq_normForm, sqrtTwoInteger] — public — **Lines**: 244-249.

### `theorem liesOver_span_three` / `inertiaDeg_span_three` / `ramificationIdx_span_three`
- inert prime (3): lies over (3), inertia deg 2, ram idx 1. **How**: `liesOver_span_iff`; `absNorm_eq_pow_inertiaDeg'` + `Nat.pow_right_injective`; `ramificationIdx_spec` + `ramified_iff_eq_two`.
- **Uses**: [isPrime_span_three, absNorm_span_three, liesOver_span_three, ramified_iff_eq_two] — public — **Lines**: 251-266 / 403-415.

### `private theorem absNorm_span_natCast`
- **Type**: `(p:ℕ) → absNorm (span {(p:𝓞K)}) = p^2` — **How**: `intNorm_eq_normForm p 0`. — **Uses**: [intNorm_eq_normForm, sqrtTwoInteger] — private — **Lines**: 268-277 — **Notes**: generic helper, reused 5× in file.

### `private theorem li_one_sqrtTwo`
- **Type**: `LinearIndependent ℤ ![1, √2]` — **How**: reduce to `sqrtTwoExplicitIntegralBasis.linearIndependent`. — **Uses**: [sqrtTwoInteger, sqrtTwoExplicitIntegralBasis(+_zero/_one)] — private — **Lines**: 279-287.

### `private theorem exists_o2_coords`
- **Type**: `(z) → ∃ A B : ℤ, z = A•1 + B•√2` — **How**: basis `repr`. — **Uses**: [sqrtTwoInteger, sqrtTwoExplicitIntegralBasis(+_zero/_one)] — private — **Lines**: 289-297.

### `private theorem unit_sqrtTwo_coeff_not_mem`
- **Type**: `A+B√2` with `B=±1` ∉ `(p)` for `p≥2` — **How**: coordinates + `li_one_sqrtTwo`, `p ∣ 1` contradiction. — **Uses**: [sqrtTwoInteger, exists_o2_coords, li_one_sqrtTwo] — private — **Lines**: 299-323.

### `theorem ramified_iff_eq_two`
- **Type**: `(p prime) → (∃P prime, span{p} ≤ P²) ↔ p = 2` — **What**: ramified ⟺ p=2 ⟺ p∣disc 8. **How**: different ideal: `dvd_differentIdeal_iff`, `not_isUnramifiedAt_of_...` and `not_map_span_natCast_le_pow_succ_of_...` (Common), `absNorm_differentIdeal`, disc 8.
- **Uses**: [absNorm_span_natCast, not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow, not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ, sqrtTwo_numberField_discr, isPrime_span_sqrtTwoInteger, span_two_eq] — public — **Lines**: 325-369 — **Notes**: 44-line proof; central splitting result; reused by ramificationIdx lemmas + split law.

### `theorem ramificationIdx_span_three_add_sqrtTwo` / `_sub_sqrtTwo`
- ram idx 1 for the (7)-primes — **How**: `ramificationIdx_spec` + `span_seven_eq` + `ramified_iff_eq_two 7`. — **Uses**: [span_seven_eq, isPrime_span_three_add/sub_sqrtTwo, ramified_iff_eq_two] — public — **Lines**: 371-401.

### `private theorem absNorm_span_prime_sqrtTwo_sub_of_mul`
- **Type**: from `(√2-c)(√2+c)=p·k`, `absNorm (span {p, √2-c}) = p` — **How**: show ≠1 and ≠p² (using `unit_sqrtTwo_coeff_not_mem`, `eq_of_le_of_absNorm_eq`), then `eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq` (Common).
- **Uses**: [sqrtTwoInteger, absNorm_span_natCast, unit_sqrtTwo_coeff_not_mem, eq_of_le_of_absNorm_eq, eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq] — private — **Lines**: 417-462 — **Notes**: 45-line proof.

### `private theorem pm_one_mod_eight_of_prime_norm`
- **Type**: existence of norm-p prime ⇒ `p % 8 ∈ {1,7}` — **How**: residue field 𝔽_p, `ZMod.exists_sq_eq_two_iff` (second supplement of QR). — **Uses**: [sqrtTwoInteger, sqrtTwoInteger_sq] — private — **Lines**: 464-486.

### `private theorem exists_prime_norm_of_pm_one_mod_eight`
- **Type**: converse — build prime `(p, √2-c)` from a sqrt of 2 mod p. **How**: `ZMod.exists_sq_eq_two_iff`, `absNorm_span_prime_sqrtTwo_sub_of_mul`.
- **Uses**: [sqrtTwoInteger, sqrtTwoInteger_sq, absNorm_span_prime_sqrtTwo_sub_of_mul] — private — **Lines**: 488-526 — **Notes**: 38-line proof.

### `theorem exists_prime_norm_iff_pm_one_mod_eight`
- **Type**: norm-p prime ⟺ `p%8 ∈ {1,7}` — **How**: combines previous two. — **Uses**: [pm_one_mod_eight_of_prime_norm, exists_prime_norm_of_pm_one_mod_eight] — public — **Lines**: 528-533.

### `private theorem pm_one_mod_eight_of_splits` / `splits_of_pm_one_mod_eight`
- split ⟺ congruence direction-by-direction. **How**: norm bookkeeping (`absNorm_span_natCast`), `ramified_iff_eq_two` to ensure distinctness. — **Uses**: [absNorm_span_natCast, exists_prime_norm_iff_pm_one_mod_eight, ramified_iff_eq_two] — private — **Lines**: 535-594.

### `theorem splits_iff_pm_one_mod_eight`
- **Type**: odd `p` splits into two distinct primes ⟺ `p%8 ∈ {1,7}` — **How**: combines the two halves. — **Uses**: [pm_one_mod_eight_of_splits, splits_of_pm_one_mod_eight] — public — **Lines**: 596-604 — **Notes**: main splitting law.

### `abbrev sqrtTwoPolynomialMod`
- **Type**: `(p) → (ZMod p)[X] := X^2 - C 2` — **Uses**: [] — public — **Lines**: 622-623.

### `theorem sqrtTwoInteger_exponent_eq_one`
- **Type**: `RingOfIntegers.exponent sqrtTwoInteger = 1` — **How**: `exponent_eq_one_iff` + `sqrtTwoInteger_adjoin_eq_top`. — **Uses**: [sqrtTwoInteger, sqrtTwoInteger_adjoin_eq_top] — public — **Lines**: 627-630.

### `theorem sqrtTwoInteger_exponent_not_dvd`
- **Type**: `[Fact p.Prime] → ¬ p ∣ exponent √2` — **Uses**: [sqrtTwoInteger, sqrtTwoInteger_exponent_eq_one] — public — **Lines**: 632-636.

### `theorem sqrtTwo_kummerDedekind_inertiaDeg` / `_ramificationIdx`
- Kummer-Dedekind reads inertia deg = `natDegree` and ram idx = `multiplicity` of a mod-p factor. **How**: `primesOverSpanEquivMonicFactorsMod` machinery (`inertiaDeg_..._symm_apply'`, `ramificationIdx_..._symm_apply'`).
- **Uses**: [sqrtTwoInteger, sqrtTwoInteger_exponent_not_dvd, sqrtTwoInteger_minpoly, sqrtTwoIntegerPolynomial, sqrtTwoPolynomialMod] — public — **Lines**: 638-663.

### `theorem sqrtTwoPolynomialMod_two` / `_seven_factor` / `_three_irreducible`
- mod-2: `X²`; mod-7: `(X-3)(X+3)`; mod-3: irreducible. **How**: `ZMod.natCast_self`; `ring_nf` + `C 2 = (C 3)²`; `irreducible_of_degree_le_three_of_not_isRoot` + `fin_cases`/`decide`.
- **Uses**: [sqrtTwoPolynomialMod] — public — **Lines**: 665-700.

### `theorem exists_root_mod_iff_exists_prime_norm`
- **Type**: `∃ c, c² = 2 mod p ⟺ ∃ norm-p prime` — **How**: `ZMod.exists_sq_eq_two_iff` + `exists_prime_norm_iff_pm_one_mod_eight`. — **Uses**: [exists_prime_norm_iff_pm_one_mod_eight] — public — **Lines**: 702-715.

### `theorem differentIdeal_eq_span_two_mul_sqrtTwo`
- **Type**: `differentIdeal ℤ (𝓞 K) = span {2√2}` — **How**: `conductor_eq_top_of_adjoin_eq_top` + `conductor_mul_differentIdeal`; different = `(minpoly')(√2) = 2√2`.
- **Uses**: [sqrtTwoInteger, sqrtTwoInteger_adjoin_eq_top, adjoin_sqrtTwoRoot_eq_top, sqrtTwoInteger_minpoly, sqrtTwoIntegerPolynomial] — public — **Lines**: 730-751 — **Notes**: 22 lines.

### `theorem differentIdeal_eq_span_sqrtTwoInteger_pow_three`
- **Type**: `differentIdeal = span {√2}^3` — **How**: `√2³ = 2√2` via `sqrtTwoInteger_sq`. — **Uses**: [differentIdeal_eq_span_two_mul_sqrtTwo, sqrtTwoInteger, sqrtTwoInteger_sq] — public — **Lines**: 753-761.

### `theorem absNorm_differentIdeal_eq_eight`
- **Type**: `absNorm (differentIdeal) = 8` — **How**: cube of (√2)-norm 2. — **Uses**: [differentIdeal_eq_span_sqrtTwoInteger_pow_three, absNorm_span_sqrtTwoInteger] — public — **Lines**: 763-767.

### `theorem prime_dvd_differentIdeal_iff_eq_span_sqrtTwo`
- **Type**: `(P prime ≠⊥) → P ∣ differentIdeal ↔ P = span {√2}` — **How**: `IsPrime.le_of_pow_le`, maximality of `(√2)`. — **Uses**: [differentIdeal_eq_span_sqrtTwoInteger_pow_three, sqrtTwoInteger, sqrtTwoRoot, sqrtTwoRoot_sq, isPrime_span_sqrtTwoInteger] — public — **Lines**: 769-794 — **Notes**: ~25 lines.

**File Summary (PrimeSplitting.lean)**: ~40 decls (~33 theorems incl. 9 private, ~2 abbrevs).
Key API (3+): `absNorm_span_sqrtTwoInteger`, `sqrtTwoInteger_sq` (imported), `intNorm_eq_normForm`
(imported), `absNorm_span_natCast`, `unit_sqrtTwo_coeff_not_mem`, `ramified_iff_eq_two`,
`exists_prime_norm_iff_pm_one_mod_eight`, the `isPrime_span_*`/`absNorm_span_*` (consumed by
LocalGlobal). Public main results: `ramified_iff_eq_two`, `splits_iff_pm_one_mod_eight`,
different ideal `= (√2)³` / norm 8, full split/inert/ramified data for 2,3,7. No sorry/set_option.
Proofs >30 lines: `ramified_iff_eq_two` (~44), `absNorm_span_prime_sqrtTwo_sub_of_mul` (~45),
`exists_prime_norm_of_pm_one_mod_eight` (~38), `isPrime_span_three` (~33).

---

## Units.lean

### `abbrev ZSqrtTwo`
- **Type**: `Zsqrtd (2 : ℤ)` — mathlib Pell `ℤ[√2]`. — **Uses**: [] — public — **Lines**: 42.

### `abbrev zsqrtTwoToRingOfIntegers`
- **Type**: `ZSqrtTwo →+* 𝓞 K` (`√2↦√2`) — **How**: `Zsqrtd.lift` with `sqrtTwoInteger_sq`. — **Uses**: [sqrtTwoInteger, sqrtTwoInteger_sq] — public — **Lines**: 45-46.

### `theorem zsqrtTwoToRingOfIntegers_apply`
- **Type**: `⟨a,b⟩ ↦ a + b√2` — **Uses**: [zsqrtTwoToRingOfIntegers, sqrtTwoInteger] — public — **Lines**: 48-51.

### `theorem two_not_int_square`
- **Type**: `∀ n:ℤ, 2 ≠ n*n` — **How**: `IsSquare`+`norm_num`. — **Uses**: [] — public — **Lines**: 53-56 — **Notes**: GENERIC; candidate for Common.

### `theorem zsqrtTwoToRingOfIntegers_injective` / `_surjective`
- bijectivity of the model map. **How**: `Zsqrtd.lift_injective` (+ `two_not_int_square`); surj via basis `repr`. — **Uses**: [zsqrtTwoToRingOfIntegers(+_apply), sqrtTwoInteger, sqrtTwoInteger_sq, two_not_int_square, sqrtTwoExplicitIntegralBasis(+_zero/_one), sqrtTwoExplicitIntegralPowerBasis(+_dim)] — public — **Lines**: 58-84.

### `abbrev zsqrtTwoEquivRingOfIntegers`
- **Type**: `ZSqrtTwo ≃+* 𝓞 K` — **How**: `RingEquiv.ofBijective`. — **Uses**: [zsqrtTwoToRingOfIntegers(+inj/surj)] — public — **Lines**: 87-89 — **Notes**: key bridge to Pell.

### `abbrev sqrtTwoFundamentalUnit`
- **Type**: `(𝓞 K)ˣ` val `√2+1`, inv `√2-1` — **What**: fundamental unit `1+√2`. **How**: `val_inv/inv_val` via `sqrtTwoRoot_sq`.
- **Uses**: [sqrtTwoInteger, sqrtTwoRoot, sqrtTwoRoot_sq] — public — **Lines**: 91-104 — **Notes**: key public object (LocalGlobal, regulator, house, adeles).

### `abbrev zsqrtTwoFundamentalUnit`
- **Type**: `ZSqrtTwoˣ` val `⟨1,1⟩`, inv `⟨-1,1⟩` — **Uses**: [] — public — **Lines**: 107-113.

### `theorem zsqrtTwoFundamentalUnit_norm`
- **Type**: `Zsqrtd.norm = -1` — **How**: `norm_num`. — **Uses**: [zsqrtTwoFundamentalUnit] — public — **Lines**: 115-117.

### `theorem zsqrtTwoEquivRingOfIntegers_fundamentalUnit`
- **Type**: `Units.mapEquiv ... zsqrtTwoFundamentalUnit = sqrtTwoFundamentalUnit` — **How**: `Units.ext`. — **Uses**: [zsqrtTwoEquivRingOfIntegers, zsqrtTwoToRingOfIntegers_apply, zsqrtTwoFundamentalUnit, sqrtTwoFundamentalUnit, sqrtTwoInteger] — public — **Lines**: 119-126.

### `theorem zsqrtTwoEquivRingOfIntegers_unitsMap_neg`
- **Type**: `mapEquiv (-v) = -(mapEquiv v)` — **How**: `map_neg`. — **Uses**: [zsqrtTwoEquivRingOfIntegers] — public — **Lines**: 128-134 — **Notes**: GENERIC (mapEquiv commutes with neg).

### `theorem sqrtTwoFundamentalUnit_sq`
- **Type**: `(1+√2)² = 3+2√2` — **How**: `Subtype.ext`+`sqrtTwoRoot_sq`. — **Uses**: [sqrtTwoFundamentalUnit, sqrtTwoInteger, sqrtTwoRoot, sqrtTwoRoot_sq] — public — **Lines**: 141-148.

### `abbrev pellTwoFundamentalSolution`
- **Type**: `Pell.Solution₁ 2 := mk 3 2 _` — **Uses**: [] — public — **Lines**: 151-152.

### `theorem pellTwoFundamentalSolution_isFundamental`
- **Type**: `Pell.IsFundamental pellTwoFundamentalSolution` — **What**: 3+2√2 is the fundamental norm-1 Pell solution. **How**: minimality via `omega`/`nlinarith` on `b.x<3`. — **Uses**: [pellTwoFundamentalSolution] — public — **Lines**: 159-173.

### `theorem pellTwoFundamentalSolution_generates_normOnePell`
- **Type**: every Pell sol = `±F^n` — **How**: `IsFundamental.eq_zpow_or_neg_zpow`. — **Uses**: [pellTwoFundamentalSolution_isFundamental, pellTwoFundamentalSolution] — public — **Lines**: 175-180.

### `theorem zsqrtTwoFundamentalUnit_sq_toPell`
- **Type**: `Unitary.toUnits pellSol = zF²` — **How**: `ext`+`norm_num`. — **Uses**: [pellTwoFundamentalSolution, zsqrtTwoFundamentalUnit] — public — **Lines**: 182-186.

### `theorem zsqrtTwo_normOneUnit_generated_by_square`
- **Type**: norm-1 ZSqrtTwo unit = `±zF^(2n)` — **How**: pass to `Pell.Solution₁`, `Unitary.toUnits.map_zpow`, `zsqrtTwoFundamentalUnit_sq_toPell`. — **Uses**: [zsqrtTwoFundamentalUnit, pellTwoFundamentalSolution(+_generates), zsqrtTwoFundamentalUnit_sq_toPell] — public — **Lines**: 188-226 — **Notes**: 38-line proof.

### `theorem zsqrtTwo_units_generated_by_fundamental`
- **Type**: every ZSqrtTwo unit = `±zF^n` — **How**: norm is ±1 (`Int.isUnit_eq_one_or`); multiply by zF to reduce norm-(-1) case. — **Uses**: [zsqrtTwoFundamentalUnit(+_norm), zsqrtTwo_normOneUnit_generated_by_square] — public — **Lines**: 228-265 — **Notes**: 37-line proof.

### `theorem sqrtTwoFundamentalUnit_generates_unitGroup`
- **Type**: every `(𝓞 K)ˣ` = `±(1+√2)^n` — **What**: complete unit-group generation. **How**: transport via `zsqrtTwoEquivRingOfIntegers`. — **Uses**: [zsqrtTwoEquivRingOfIntegers, zsqrtTwo_units_generated_by_fundamental, zsqrtTwoFundamentalUnit, zsqrtTwoEquivRingOfIntegers_fundamentalUnit, zsqrtTwoEquivRingOfIntegers_unitsMap_neg, sqrtTwoFundamentalUnit] — public — **Lines**: 267-292 — **Notes**: key result.

### `theorem sqrtTwoFundamentalUnit_isFundamental`
- **Type**: `(1+√2)²=3+2√2 ∧ ∀ Pell sol = ±F^n` — **How**: pairs the two facts. — **Uses**: [sqrtTwoFundamentalUnit_sq, pellTwoFundamentalSolution_generates_normOnePell, sqrtTwoFundamentalUnit, sqrtTwoInteger] — public — **Lines**: 299-306.

### `private theorem sqrtTwo_torsion_eq_one_or_neg_one`
- **Type**: `(x : torsion K) → x = ±1` — **How**: totally real ⇒ no primitive root of order >2 (`InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt`), interval_cases on order. — **Uses**: [nrRealPlaces_eq_two] — private — **Lines**: 310-334 — **Notes**: 25 lines; reused by torsionOrder + iff lemma.

### `theorem torsionOrder_eq_two`
- **Type**: `Units.torsionOrder K = 2` — **How**: `Finset.card_eq_two` with `{1,-1}` + classification. — **Uses**: [sqrtTwo_torsion_eq_one_or_neg_one] — public — **Lines**: 336-341 — **Notes**: TWIN of SqrtFive `torsionOrder_eq_two`.

### `theorem unitRank_eq_one`
- **Type**: `Units.rank K = 1` — **How**: `(2,0)` signature ⇒ rank 1. — **Uses**: [nrRealPlaces_eq_two, nrComplexPlaces_eq_zero] — public — **Lines**: 343-348 — **Notes**: TWIN of SqrtFive.

### `private theorem exists_eq_torsion_mul_fundSystem_zpow`
- **Type**: `(i₀ u) → ∃ ζ ∈ torsion, ∃ n, u = ζ·fundSystem^n` — **How**: `closure_fundSystem_sup_torsion_eq_top`, `Subgroup.mem_sup`, rank-1 ⇒ subsingleton fundSystem index. — **Uses**: [unitRank_eq_one] — private — **Lines**: 350-373 — **Notes**: TWIN of SqrtFive (same name).

### `private theorem fundSystem_zpow_mem_torsion`
- **Type**: `fundSystem^n ∈ torsion ⇒ n=0` — **How**: project to `(𝓞K)ˣ/torsion`, `basisModTorsion.repr`. — **Uses**: [] (uses unitRank only indirectly) — private — **Lines**: 375-389 — **Notes**: TWIN of SqrtFive.

### `private theorem eq_one_or_neg_one_of_mem_torsion`
- **Type**: `ζ ∈ torsion ⇒ ζ = ±1` — **How**: wraps `sqrtTwo_torsion_eq_one_or_neg_one`. — **Uses**: [sqrtTwo_torsion_eq_one_or_neg_one] — private — **Lines**: 391-395 — **Notes**: TWIN of SqrtFive.

### `theorem mem_torsion_iff_eq_one_or_neg_one`
- **Type**: `u ∈ torsion K ↔ u = ±1` — **How**: both directions. — **Uses**: [eq_one_or_neg_one_of_mem_torsion] — public — **Lines**: 397-404 — **Notes**: used by LocalGlobal fundamental-cone lemma.

### `theorem regulator_eq`  ⚠ SORRY
- **Type**: `Units.regulator K = Real.log (1 + Real.sqrt 2)` — **What**: regulator = log of fundamental unit. **How**: `sorry`. — **Uses**: [] — public — **Lines**: 406-409 — **Notes**: **SORRY**. Blocked (Artin/fundamental-unit covolume identification), same blocker as all 8 twins.

### `private theorem unitGroupStructure_bijective`
- **Type**: bijectivity of `torsionPowerHom 2 (-1) ⊕ rankOnePowerHom η` (Common helpers). **How**: injectivity via `fundSystem_zpow_mem_torsion`/`ZMod 2` casework; surjectivity via `exists_eq_torsion_mul_fundSystem_zpow`.
- **Uses**: [torsionPowerHom, rankOnePowerHom, fundSystem_zpow_mem_torsion, exists_eq_torsion_mul_fundSystem_zpow, eq_one_or_neg_one_of_mem_torsion] — private — **Lines**: 411-453 — **Notes**: ~43 lines; TWIN of SqrtFive.

### `theorem unitGroupStructure`
- **Type**: `Nonempty ((𝓞 K)ˣ ≃* Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ))` — **What**: unit group `≅ μ₂ × ℤ`. **How**: `MulEquiv.ofBijective` on coprod, bijectivity from above. — **Uses**: [unitRank_eq_one, torsionPowerHom, rankOnePowerHom, unitGroupStructure_bijective] — public — **Lines**: 455-471 — **Notes**: key public result; TWIN of SqrtFive.

**File Summary (Units.lean)**: ~28 decls (~20 theorems incl. 6 private, ~7 abbrevs). Key API:
`sqrtTwoFundamentalUnit`, `zsqrtTwoEquivRingOfIntegers`, `sqrtTwo_torsion_eq_one_or_neg_one`,
`unitRank_eq_one`, `mem_torsion_iff_eq_one_or_neg_one`. Public results: `torsionOrder_eq_two`,
`unitRank_eq_one`, `sqrtTwoFundamentalUnit_generates_unitGroup`,
`sqrtTwoFundamentalUnit_isFundamental`, `unitGroupStructure`, `regulator_eq` (sorry).
**1 SORRY** (`regulator_eq`). No set_option. Proofs >30 lines:
`zsqrtTwo_normOneUnit_generated_by_square` (~38), `zsqrtTwo_units_generated_by_fundamental` (~37),
`unitGroupStructure_bijective` (~43). The empty `## Regulator` section at end has 0 decls.
NOTE: lines 350-471 (torsion/rank/unitGroup machinery) are near-verbatim twins of SqrtFive Units.

---

## Euclidean.lean

### `private theorem abs_norm_int_lt_of_remainder_eq`
- **Type**: given `r = b·e` and `|N(e)| = |frac form| ≤ 1/2` and `0<|N(b)|`, conclude `|N r| < |N b|`. — **What**: the arithmetic core of the Euclidean division bound. **How**: `Algebra.coe_norm_int`, `abs_mul`, `mul_le_mul_of_nonneg_left`, `linarith`.
- **Uses**: [] — private — **Lines**: 35-55 — **Notes**: GENERIC-looking; quadratic-field Euclidean helper candidate for Common.

### `theorem normEuclidean`
- **Type**: `(a b : 𝓞 K) (hb : b ≠ 0) → ∃ q r, a = b·q + r ∧ (N r).natAbs < (N b).natAbs` — **What**: ℚ(√2) is norm-Euclidean. **How**: round real/im coords of `a/b`, remainder norm form `|u'²-2v'²| ≤ 1/2` via `abs_sub_round` + `nlinarith`, then `abs_norm_int_lt_of_remainder_eq` and `natAbs_lt_of_abs_ratCast_lt` (Common).
- **Uses**: [sqrtTwoInteger, sqrtTwoRoot, norm_eq_normForm, abs_norm_int_lt_of_remainder_eq, natAbs_lt_of_abs_ratCast_lt] — public — **Lines**: 57-107 — **Notes**: ~50-line proof; central Euclidean result. TWIN of SqrtFive `normEuclidean` (different constant `2` vs `5`/golden form).

**File Summary (Euclidean.lean)**: 2 decls (1 private helper, 1 public theorem). Key public result:
`normEuclidean`. No sorry/set_option. `normEuclidean` proof ~50 lines. The helper
`abs_norm_int_lt_of_remainder_eq` is generic enough to share with SqrtFive.

---

## LocalGlobal.lean

### `def vTwo` / `vThree` / `vSevenPlus` / `vSevenMinus`
- **Type**: `HeightOneSpectrum (𝓞 K)` for `(√2)`, `(3)`, `(3+√2)`, `(3-√2)`. **How**: package ideal + `isPrime_span_*` + `ne_bot` (from `absNorm_span_*`).
- **Uses**: [isPrime_span_sqrtTwoInteger/three/three_add/three_sub, absNorm_span_sqrtTwoInteger/three/three_add/three_sub, sqrtTwoInteger] — public — **Lines**: 37-74 — **Notes**: each used by its FinitePlace + Completion + examples.

### `abbrev finitePlaceTwo` / `Three` / `SevenPlus` / `SevenMinus`
- **Type**: `NumberField.FinitePlace K := FinitePlace.mk v…` — **Uses**: [vTwo/vThree/vSevenPlus/vSevenMinus] — public — **Lines**: 77-90. `finitePlaceTwo` used in `finite_support_sqrtTwoRoot_only_vTwo`.

### `example`s (8×, lines 92-122)
- ramification/inertia data for `vTwo/vThree/vSeven±` — **How**: cite the PrimeSplitting lemmas. **Uses**: [ramificationIdx_*, inertiaDeg_*, vTwo/vThree/vSeven±] — anonymous.

### `abbrev CompletionAtTwo` / `Three` / `SevenPlus` / `SevenMinus`
- **Type**: `v….adicCompletion K` — **Uses**: [vTwo/vThree/vSeven±] — public — **Lines**: 139-152.

### `example`s (lines 155-168)
- ram idx 2 at 2; inertia 2 at 3; inertia 1 at both 7. — **Uses**: [ramificationIdx_span_sqrtTwoInteger, inertiaDeg_span_three(+_add/_sub_sqrtTwo), vTwo/vThree/vSeven±] — anonymous.

### `abbrev InfiniteCompletion`
- **Type**: `(v : InfinitePlace K) → Type := v.Completion` — **Uses**: [] — public — **Lines**: 185-186.

### `example` (infinite completion ≅ ℝ)
- **How**: `Completion.ringEquivRealOfIsReal (infinitePlace_isReal v)`. **Uses**: [InfiniteCompletion, infinitePlace_isReal] — anonymous — **Lines**: 189-191.

### `theorem infiniteCompletion_sqrtTwoRoot_norm`
- **Type**: `‖algebraMap K (InfiniteCompletion v) √2‖ = √2` — **How**: `Completion.norm_coe` + `infinitePlace_apply_sqrtTwoRoot`. — **Uses**: [InfiniteCompletion, sqrtTwoRoot, infinitePlace_apply_sqrtTwoRoot] — public — **Lines**: 194-199.

### `theorem infinitePlace_sum_inertiaDeg_eq_two`
- **Type**: `(v : InfinitePlace ℚ) → ∑ w ∈ v.placesOver K, v.inertiaDeg w = 2` — **How**: `sum_inertiaDeg_eq_finrank` + `degree_eq_two`. — **Uses**: [degree_eq_two] — public — **Lines**: 201-207.

### `example` (product formula for √2)
- **How**: `NumberField.prod_abs_eq_one` (√2≠0). **Uses**: [sqrtTwoRoot, sqrtTwoRoot_sq] — anonymous — **Lines**: 225-233.

### `example` (product formula for 1+√2)
- **How**: `prod_abs_eq_one`. **Uses**: [sqrtTwoFundamentalUnit] — anonymous — **Lines**: 236-245.

### `theorem finite_support_sqrtTwoRoot_only_vTwo`
- **Type**: `(v ≠ finitePlaceTwo) → v √2 = 1` — **What**: finite contribution of √2 sits only at vTwo. **How**: `norm_eq_one_iff_notMem`; maximal ideal containing `(√2)` must equal vTwo (`IsMaximal.eq_of_le`). — **Uses**: [sqrtTwoRoot, sqrtTwoInteger, finitePlaceTwo, vTwo] — public — **Lines**: 248-265 — **Notes**: ~18 lines.

### `abbrev SqrtTwoInfiniteAdeleRing` / `infinitePrincipalAdele_sqrtTwoRoot` / `_fundamentalUnit`
- infinite adele ring + two principal adeles. **Uses**: [sqrtTwoRoot, sqrtTwoFundamentalUnit] — public — **Lines**: 282-292.

### `example`s (lines 294-306)
- norm of principal infinite adeles = `|N|`; dense range. — **Uses**: [infinitePrincipalAdele_sqrtTwoRoot/_fundamentalUnit, SqrtTwoInfiniteAdeleRing, sqrtTwoRoot, sqrtTwoFundamentalUnit] — anonymous.

### `private theorem complexEmbedding_norm_sqrtTwoRoot`
- **Type**: `(φ : K →+* ℂ) → ‖φ √2‖ = √2` — **How**: `infinitePlace_apply_sqrtTwoRoot (mk φ)`. — **Uses**: [sqrtTwoRoot, infinitePlace_apply_sqrtTwoRoot] — private — **Lines**: 322-324.

### `theorem canonicalEmbedding_norm_sqrtTwoRoot`
- **Type**: `‖canonicalEmbedding K √2‖ = √2` — **How**: `le_antisymm` via `canonicalEmbedding.norm_le_iff` and `norm_le_pi_norm`. — **Uses**: [sqrtTwoRoot, complexEmbedding_norm_sqrtTwoRoot] — public — **Lines**: 327-337.

### `theorem canonicalEmbedding_sqrtTwoInteger_mem_integerLattice`
- **Type**: `canonicalEmbedding K √2 ∈ integerLattice K` — **How**: exhibit preimage. — **Uses**: [sqrtTwoInteger] — public — **Lines**: 339-345.

### `theorem canonicalEmbedding_fundamentalUnit_coordinates`
- **Type**: `∃ σ τ, σ(1+√2) = 1+√2 ∧ τ(1+√2) = 1-√2` — **How**: `exists_realEmbedding_pos/_neg` composed with `ofRealHom`. — **Uses**: [exists_realEmbedding_pos, exists_realEmbedding_neg, sqrtTwoFundamentalUnit, sqrtTwoRoot] — public — **Lines**: 347-362.

### `abbrev mixedEmbedding_sqrtTwoRoot`
- **Type**: `mixedSpace K := mixedEmbedding K √2` — **Uses**: [sqrtTwoRoot] — public — **Lines**: 379-380.

### `example`s (lines 382-394)
- `convexBodyLT_mem`; `measurableSet_fundamentalCone`; `measurableSet_normLeOne`. — **Uses**: [mixedEmbedding_sqrtTwoRoot, sqrtTwoRoot] — anonymous.

### `theorem polarSpace_nonempty`
- **Type**: `Nonempty (polarSpace K)` — `infer_instance`. — **Uses**: [] — public — **Lines**: 396-398.

### `theorem unit_smul_mem_fundamentalCone_iff_eq_one_or_neg_one`
- **Type**: `u • x ∈ fundamentalCone ↔ u = ±1` — **How**: `fundamentalCone.unit_smul_mem_iff_mem_torsion` + `mem_torsion_iff_eq_one_or_neg_one`. — **Uses**: [mem_torsion_iff_eq_one_or_neg_one] — public — **Lines**: 402-408.

### `theorem house_sqrtTwoRoot`
- **Type**: `house √2 = √2` — **How**: `house` + `canonicalEmbedding_norm_sqrtTwoRoot`. — **Uses**: [sqrtTwoRoot, canonicalEmbedding_norm_sqrtTwoRoot] — public — **Lines**: 425-427.

### `theorem house_sqrtTwoInteger`
- **Type**: `house (algebraMap √2) = √2` — **Uses**: [sqrtTwoInteger, house_sqrtTwoRoot] — public — **Lines**: 429-432.

### `theorem house_sqrtTwoFundamentalUnit`
- **Type**: `house (1+√2) = 1+√2` — **How**: `le_antisymm` (`norm_le_iff` + triangle; lower bound from real embedding `σ`). — **Uses**: [sqrtTwoFundamentalUnit, sqrtTwoRoot, infinitePlace_apply_sqrtTwoRoot, canonicalEmbedding_fundamentalUnit_coordinates] — public — **Lines**: 434-457 — **Notes**: ~23 lines.

### `abbrev SqrtTwoAdeleRing` / `principalAdele_sqrtTwoRoot` / `_fundamentalUnit`
- full adele ring + principal adeles. **Uses**: [sqrtTwoRoot, sqrtTwoFundamentalUnit] — public — **Lines**: 474-483.

### `theorem principalAdele_sqrtTwoRoot_ne_zero`
- **Type**: `principalAdele_sqrtTwoRoot ≠ 0` — **How**: `AdeleRing.algebraMap_injective`. — **Uses**: [principalAdele_sqrtTwoRoot, sqrtTwoRoot, sqrtTwoRoot_sq] — public — **Lines**: 486-494.

### `theorem principalAdele_fundamentalUnit_is_unit_everywhere`
- **Type**: `∀ v : FinitePlace K, v(1+√2) = 1` — **How**: `norm_eq_one_iff_notMem`; if `(1+√2) ∈ 𝔪` then `1 ∈ 𝔪` (via inverse). — **Uses**: [sqrtTwoFundamentalUnit, sqrtTwoInteger, sqrtTwoRoot, sqrtTwoRoot_sq] — public — **Lines**: 497-524 — **Notes**: ~27 lines.

### `abbrev sqrtTwoDedekindZeta` / `sqrtTwoDedekindZetaResidue`
- Dedekind zeta + residue. **Uses**: [] — public — **Lines**: 541-546.

### `example`s (lines 548-558)
- residue positivity; class-number-formula residue identity. — **Uses**: [sqrtTwoDedekindZetaResidue] — anonymous.

**File Summary (LocalGlobal.lean)**: ~45 decls (~16 named theorems, ~15 abbrevs/defs, ~14
anonymous `example`s). Key API: `vTwo/vThree/vSeven±`, `finitePlaceTwo`,
`canonicalEmbedding_norm_sqrtTwoRoot`, `canonicalEmbedding_fundamentalUnit_coordinates`,
`mem_torsion_iff_eq_one_or_neg_one` (imported). Public results: place data, completions, infinite
completion ≅ ℝ, product formula, house of √2 / 1+√2, adele non-vanishing, Dedekind zeta residue.
No sorry/set_option. No proof >30 lines (longest ≈27). Many `example`s are demonstrative (not
reusable API).

---

## Cross-file observations

- **SqrtFive twins (QuadraticAlgebra setup, near-identical)**: `K`, `degree_eq_two`,
  `IsQuadraticExtension` instance, the AdjoinRoot↔QuadraticAlgebra equivalence block, the entire
  Units machinery (`torsionOrder_eq_two`, `unitRank_eq_one`,
  `exists_eq_torsion_mul_fundSystem_zpow`, `fundSystem_zpow_mem_torsion`,
  `eq_one_or_neg_one_of_mem_torsion`, `mem_torsion_iff_eq_one_or_neg_one`,
  `unitGroupStructure(_bijective)`, `regulator_eq` sorry), `normEuclidean`, all the
  PrimeSplitting/LocalGlobal scaffolding. Differences: generator (`√2` vs golden `(1+√5)/2`),
  constants (disc 8 vs 5; norm form `x²-2y²` vs golden form), and SqrtFive's golden-ratio
  intermediary model.
- **EXTRA in SqrtTwo (not in SqrtFive)**: the whole `KUnitModel` second presentation
  (`sqrtTwoUnitPolynomial`, `KUnitModel`, `sqrtTwoUnitRoot`, `sqrtTwoUnitRoot_relation`,
  `sqrtTwoToUnitModel`, `unitModelToSqrtTwo`, `sqrtTwoEquivUnitModel`, `_root` lemmas) —
  Basic.lean lines 173-270. Self-contained, unused by any sibling file.
- **Generic helpers worth promoting**: `ringHom_ext_sqrtTwo` (Embeddings),
  `abs_norm_int_lt_of_remainder_eq` (Euclidean), `two_not_int_square` (Units),
  `zsqrtTwoEquivRingOfIntegers_unitsMap_neg` (Units), `absNorm_span_natCast` (PrimeSplitting).
