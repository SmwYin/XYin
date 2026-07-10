# Declaration Inventory — `XYin/NumberField/FieldExamples/SqrtTwo/`

Real quadratic field `ℚ(√2)`, built via `QuadraticAlgebra ℚ 2 0` (the **radical model**, generator
`√2` with `√2² = 2`). Twin of `SqrtFive` (which uses the golden-ratio model `QuadraticAlgebra ℚ 1 1`).
The decisive difference: ring of integers is `ℤ[√2]` (monogenic at the *square root*, disc `8 = 2³`),
and the **fundamental unit `1+√2` is proved outright via mathlib's `Zsqrtd`/`Pell.Solution₁` API** —
so `unitGroupStructure` (`μ₂ × ℤ`) is fully formalised; `regulator_eq` is now also **proved**, making
the folder **sorry-free**.
Namespace `NumberField.SqrtTwo` throughout. Every file: `noncomputable section`,
`attribute [-instance] DivisionRing.toRatAlgebra`, same open scopes.

All cross-references to `Common.lean` use namespace `NumberField.FieldExamples`. Common API actually
used here: `eq_of_le_of_absNorm_eq`, `eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq`,
`not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ`,
`not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow`, `abs_intNorm_lt_of_abs_norm_le`,
`natAbs_lt_of_abs_ratCast_lt`, `torsionPowerHom`, `rankOnePowerHom`.

**Sorry-free.** The former lone sorry `regulator_eq` (`Units.regulator K = log(1+√2)`) is now
**closed**, via mathlib's `regOfFamily_div_regulator` → `regOfFamily_eq_det` →
`Matrix.det_eq_elem_of_subsingleton`. This is the diagnostic case that corrects an earlier
mis-reading: the "regulator = log(fundamental unit)" step is **mature mathlib API**, not a missing
bridge — it only needed the fundamental unit (already certified here via Pell). The regulator was
never an API gap; it was simply downstream of fundamentality.

---

## Basic.lean

### `instance : Fact (∀ r : ℚ, r ^ 2 ≠ 2 + 0 * r)`
- **Type**: `Fact (∀ r : ℚ, r ^ 2 ≠ (2 : ℚ) + (0 : ℚ) * r)`.
- **What**: the `QuadraticAlgebra ℚ 2 0` field-instance hypothesis (`2` has no rational square root).
- **How**: from a root build `IsSquare (2:ℚ)` via `isSquare_iff_exists_sq` + `nlinarith`, then `norm_num`.
- **Uses from project**: [] — **Visibility**: public (anon instance) — **Lines**: 39-46

### `abbrev K`
- **Type**: `K : Type := QuadraticAlgebra ℚ (2:ℚ) 0`. **What**: `ℚ(√2)` as a quadratic algebra. **How**: defn.
- **Uses**: [] — **Visibility**: public — **Lines**: 49

### `instance : NumberField K`
- **What**: `K` is a number field. **How**: `NumberField.of_module_finite`. **Uses**: [] — **Lines**: 51-52

### `abbrev sqrtTwoRoot`
- **Type**: `sqrtTwoRoot : K := QuadraticAlgebra.omega`. **What**: the generator `√2`. **Uses**: [] — **Lines**: 55
- **Notes**: KEY — referenced pervasively in every file.

### `theorem sqrtTwoRoot_sq`
- **Type**: `sqrtTwoRoot ^ 2 = (2 : K)`. **How**: `pow_two` + `QuadraticAlgebra.omega_mul_omega_eq_add`, `ext`/`norm_num`.
- **Uses**: [`sqrtTwoRoot`] — **Lines**: 57-59 — **Notes**: KEY (used everywhere).

### `abbrev sqrtTwoPolynomial`
- **Type**: `ℚ[X] := X^2 - C 2` — the minimal polynomial. **Uses**: [] — **Lines**: 62

### `instance : Fact (Irreducible sqrtTwoPolynomial)`
- **How**: `irreducible_of_degree_le_three_of_not_isRoot`; root would give `IsSquare 2`. **Uses**: [`sqrtTwoPolynomial`] — **Lines**: 64-80

### `abbrev KAdjoinRoot` / `abbrev sqrtTwoAdjoinRoot`
- **Types**: `AdjoinRoot sqrtTwoPolynomial`; `AdjoinRoot.root …`. Alternate presentation. **Uses**: [`sqrtTwoPolynomial`] — **Lines**: 83, 86

### `theorem sqrtTwoAdjoinRoot_sq`
- **Type**: `sqrtTwoAdjoinRoot^2 = 2`. **How**: `AdjoinRoot.eval₂_root` + `calc`. **Uses**: [`sqrtTwoAdjoinRoot`,`sqrtTwoPolynomial`] — **Lines**: 88-94

### `def sqrtTwoAdjoinRootToQuadratic` / `@[simp] theorem …_root`
- **Type**: `KAdjoinRoot →ₐ[ℚ] K`; root identity. **How**: `AdjoinRoot.liftAlgHom`; `AdjoinRoot.liftAlgHom_root`.
- **Uses**: [`sqrtTwoPolynomial`,`sqrtTwoRoot`,`sqrtTwoRoot_sq`,`sqrtTwoAdjoinRoot`] — **Lines**: 96-108

### `def sqrtTwoQuadraticToAdjoinRoot` / `@[simp] theorem …_root`
- **Type**: `K →ₐ[ℚ] KAdjoinRoot`; root identity. **How**: `QuadraticAlgebra.lift`. **Uses**: [`sqrtTwoAdjoinRoot(_sq)`,`sqrtTwoRoot`] — **Lines**: 110-118

### `def sqrtTwoAdjoinRootEquivQuadratic`
- **Type**: `KAdjoinRoot ≃ₐ[ℚ] K`. **What**: AdjoinRoot ≅ quadratic-algebra presentation. **How**: package the two AlgHoms; inverses via `AdjoinRoot.algHom_ext`/`QuadraticAlgebra.algHom_ext`.
- **Uses**: [`sqrtTwoAdjoinRootToQuadratic(_root)`,`sqrtTwoQuadraticToAdjoinRoot(_root)`] — **Lines**: 120-140 — **Notes**: KEY (used in RingOfIntegers minpoly); proof ~20 lines.

### `abbrev sqrtTwoAdjoinRootPowerBasis` / `abbrev sqrtTwoPowerBasis`
- **Types**: `PowerBasis ℚ KAdjoinRoot` from `AdjoinRoot.powerBasis`; mapped to `PowerBasis ℚ K`. **Uses**: [`sqrtTwoPolynomial`,`sqrtTwoAdjoinRootEquivQuadratic`] — **Lines**: 143-148 — **Notes**: KEY.

### `@[simp] theorem sqrtTwoPowerBasis_gen`
- **Type**: `sqrtTwoPowerBasis.gen = sqrtTwoRoot`. **How**: `sqrtTwoAdjoinRootToQuadratic_root`. **Uses**: [`sqrtTwoPowerBasis`,…] — **Lines**: 150-153

### `theorem adjoin_sqrtTwoRoot_eq_top`
- **Type**: `Algebra.adjoin ℚ {sqrtTwoRoot} = ⊤`. **How**: `PowerBasis.adjoin_gen_eq_top`. **Uses**: [`sqrtTwoPowerBasis(_gen)`] — **Lines**: 156-158 — **Notes**: used in PrimeSplitting (Different).

### `theorem sqrtTwoPowerBasis_dim`
- **Type**: `sqrtTwoPowerBasis.dim = 2`. **How**: `natDegree_X_pow_sub_C`. **Uses**: [`sqrtTwoPowerBasis`,`sqrtTwoPolynomial`] — **Lines**: 160-163 — **Notes**: KEY.

### `theorem degree_eq_two`
- **Type**: `Module.finrank ℚ K = 2`. **How**: `PowerBasis.finrank` + `sqrtTwoPowerBasis_dim`. **Uses**: [`sqrtTwoPowerBasis(_dim)`] — **Lines**: 165-168 — **Notes**: KEY (Embeddings, PrimeSplitting, LocalGlobal).

### `instance : Algebra.IsQuadraticExtension ℚ K`
- **How**: `degree_eq_two`. **Uses**: [`degree_eq_two`] — **Lines**: 170-171

### `abbrev sqrtTwoUnitPolynomial`
- **Type**: `ℚ[X] := C 1 * X² + C(-2) * X + C(-1)` — the minimal polynomial `X²-2X-1` of `1+√2`. **Uses**: [] — **Lines**: 177-178

### `instance : Fact (Irreducible sqrtTwoUnitPolynomial)`
- **How**: `irreducible_of_degree_le_three_of_not_isRoot`; root would give `IsSquare 2` (witness `x-1`). **Uses**: [`sqrtTwoUnitPolynomial`] — **Lines**: 180-192

### `abbrev KUnitModel` / `abbrev sqrtTwoUnitRoot`
- **Types**: `AdjoinRoot sqrtTwoUnitPolynomial`; `AdjoinRoot.root …` (a root of `X²-2X-1`, i.e. `1+√2`). **Uses**: [`sqrtTwoUnitPolynomial`] — **Lines**: 195, 198

### `theorem sqrtTwoUnitRoot_relation`
- **Type**: `sqrtTwoUnitRoot² - 2·sqrtTwoUnitRoot - 1 = 0`. **How**: `AdjoinRoot.eval₂_root`. **Uses**: [`sqrtTwoUnitRoot`,`sqrtTwoUnitPolynomial`] — **Lines**: 200-203

### `def sqrtTwoToUnitModel` / `@[simp] theorem …_root`
- **Type**: `K →ₐ[ℚ] KUnitModel` sending `√2 ↦ β-1`. **How**: `QuadraticAlgebra.lift`, `calc`+`linear_combination sqrtTwoUnitRoot_relation`. **Uses**: [`sqrtTwoUnitRoot(_relation)`,`sqrtTwoRoot`] — **Lines**: 206-222

### `def unitModelToSqrtTwo` / `@[simp] theorem …_root`
- **Type**: `KUnitModel →ₐ[ℚ] K` sending `β ↦ √2+1`. **How**: `AdjoinRoot.liftAlgHom`. **Uses**: [`sqrtTwoUnitPolynomial`,`sqrtTwoRoot(_sq)`,`sqrtTwoUnitRoot`] — **Lines**: 225-240

### `def sqrtTwoEquivUnitModel` / `theorem …_root`
- **Type**: `K ≃ₐ[ℚ] KUnitModel`. **What**: the two AdjoinRoot presentations are equivalent. **How**: package AlgHoms; inverses via `QuadraticAlgebra.algHom_ext`/`AdjoinRoot.algHom_ext`. **Uses**: [`sqrtTwoToUnitModel(_root)`,`unitModelToSqrtTwo(_root)`,`sqrtTwoRoot`] — **Lines**: 243-270 — **Notes**: proof >25 lines.

**File Summary — Basic.lean**: ~23 decls (abbrevs/defs ~14, theorems ~7, instances 3). Key API (3+): `sqrtTwoRoot`, `sqrtTwoRoot_sq`, `sqrtTwoPowerBasis`, `degree_eq_two`. No sorry/set_option. >30-line proofs: none (several ~20-27 line equiv constructions). The entire `KUnitModel`/`sqrtTwoUnit*` apparatus (the `1+√2` presentation) is presentation plumbing — **unused downstream**; the `KAdjoinRoot` chain is used only in RingOfIntegers (`sqrtTwo_minpoly_rat`).

---

## Galois.lean

### `def sqrtTwoConjHom` / `@[simp] theorem sqrtTwoConjHom_root`
- **Type**: `K →ₐ[ℚ] K` sending `√2 ↦ -√2`; `sqrtTwoConjHom sqrtTwoRoot = -sqrtTwoRoot`.
- **How**: `QuadraticAlgebra.lift` (verifying `(-√2)²=2`). **Uses**: [`sqrtTwoRoot(_sq)`] — **Lines**: 34-42

### `def sqrtTwoConj`
- **Type**: `K ≃ₐ[ℚ] K`. **What**: the nontrivial conjugation automorphism. **How**: package `sqrtTwoConjHom` as its own inverse (involution via `QuadraticAlgebra.algHom_ext`).
- **Uses**: [`sqrtTwoConjHom(_root)`] — **Lines**: 44-63 — **Notes**: KEY.

### `theorem sqrtTwoConj_root`
- **Type**: `sqrtTwoConj sqrtTwoRoot = -sqrtTwoRoot`. **How**: `sqrtTwoConjHom_root`. **Uses**: [`sqrtTwoConjHom_root`] — **Lines**: 65-67

### `theorem isGalois`
- **Type**: `IsGalois ℚ K`. **How**: `infer_instance` (quadratic extensions are Galois). **Uses**: [] — **Lines**: 69-71

### `theorem sqrtTwo_gal_eq_id_or_conj`
- **Type**: `(σ : Gal(K/ℚ)) → σ = 1 ∨ σ = sqrtTwoConj`. **How**: `σ√2` satisfies `X²=2`, factor `(σ√2-√2)(σ√2+√2)=0`, `mul_eq_zero`, extensionality via `QuadraticAlgebra.algHom_ext`.
- **Uses**: [`sqrtTwoRoot(_sq)`,`sqrtTwoConj(Hom_root)`] — **Lines**: 73-100 — **Notes**: proof >25 lines.

### `private theorem sqrtTwoConj_ne_one`
- **Type**: `sqrtTwoConj ≠ 1`. **How**: else `-√2=√2 ⇒ 2·√2=0 ⇒ √2=0 ⇒ 2=0`, contradiction. **Uses**: [`sqrtTwoConjHom_root`,`sqrtTwoRoot(_sq)`] — **Lines**: 102-121 — **Visibility**: private

### `theorem gal_natCard_eq_two`
- **Type**: `Nat.card (Gal(K/ℚ)) = 2`. **How**: `Nat.card_eq_two_iff` with witnesses `1`,`sqrtTwoConj` + `sqrtTwo_gal_eq_id_or_conj`. **Uses**: [`sqrtTwoConj(_ne_one)`,`sqrtTwo_gal_eq_id_or_conj`] — **Lines**: 123-128 — **Notes**: KEY.

### `private abbrev CyclicTwo`
- **Type**: `Multiplicative (ZMod 2)`. **Uses**: [] — **Lines**: 131 — **Visibility**: private

### `private theorem sqrtTwoGal_additive_generator`
- **Type**: every `σ ∈ AddSubgroup.zmultiples (ofMul sqrtTwoConj)`. **How**: case on `sqrtTwo_gal_eq_id_or_conj`. **Uses**: [`sqrtTwo_gal_eq_id_or_conj`,`sqrtTwoConj`] — **Lines**: 134-142 — **Visibility**: private

### `private abbrev cyclicTwoEquivSqrtTwoGal` / `sqrtTwoGalEquivCyclicTwo`
- **Types**: `CyclicTwo ≃* Gal(K/ℚ)` (via `zmodAddEquivOfGenerator`+`AddEquiv.toMultiplicativeLeft`); its `.symm`. **Uses**: [`sqrtTwoGal_additive_generator`,`gal_natCard_eq_two`] — **Lines**: 148-154 — **Visibility**: private

### `theorem galoisGroupStructure`
- **Type**: `Nonempty (Gal(K/ℚ) ≃* Multiplicative (ZMod 2))`. **What**: Galois group is cyclic of order 2. **How**: `⟨sqrtTwoGalEquivCyclicTwo⟩`. **Uses**: [`sqrtTwoGalEquivCyclicTwo`] — **Lines**: 156-159

**File Summary — Galois.lean**: 12 decls (defs 2, abbrevs 3, theorems 6 + 1 instance-like). Key API (3+): `sqrtTwoConj`, `sqrtTwoConjHom_root`, `sqrtTwo_gal_eq_id_or_conj`. No sorry/set_option. >30-line proofs: none.

---

## Embeddings.lean

### `private theorem ringHom_ext_sqrtTwo`
- **Type**: `{f g : K →+* ℂ} (h : f sqrtTwoRoot = g sqrtTwoRoot) → f = g`. **What**: ring homs `K→ℂ` agreeing on `√2` are equal.
- **How**: `QuadraticAlgebra.mk_eq_add_smul_omega`, `eq_ratCast` on rational part. **Uses**: [`sqrtTwoRoot`] — **Lines**: 34-45 — **Visibility**: private — **Notes**: generic — could be a shared `QuadraticAlgebra` ext lemma.

### `theorem isTotallyReal`
- **Type**: `NumberField.IsTotallyReal K`. **How**: each embedding is real — conjugate root satisfies `X²=2`, factor, rule out `re=0` branch via `nlinarith [sq_nonneg z.im]`. Uses `ComplexEmbedding.conjugate_coe_eq`, `ringHom_ext_sqrtTwo`.
- **Uses**: [`ringHom_ext_sqrtTwo`,`sqrtTwoRoot(_sq)`] — **Lines**: 47-73 — **Notes**: KEY; proof >20 lines.

### `theorem nrComplexPlaces_eq_zero`
- **Type**: `InfinitePlace.nrComplexPlaces K = 0`. **How**: `IsTotallyReal.nrComplexPlaces_eq_zero`. **Uses**: [`isTotallyReal`] — **Lines**: 75-79 — **Notes**: KEY (ClassGroup, Units, LocalGlobal).

### `theorem nrRealPlaces_eq_two`
- **Type**: `InfinitePlace.nrRealPlaces K = 2`. **How**: `card_add_two_mul_card_eq_rank`, `nrComplexPlaces_eq_zero`, `finrank=2`, `omega`. **Uses**: [`nrComplexPlaces_eq_zero`,`sqrtTwoPowerBasis(_dim)`] — **Lines**: 81-90 — **Notes**: KEY (Units, LocalGlobal).

### `theorem exists_realEmbedding_pos` / `exists_realEmbedding_neg`
- **Types**: `∃ σ : K →ₐ[ℚ] ℝ, σ sqrtTwoRoot = ±Real.sqrt 2`. **How**: `QuadraticAlgebra.lift` with `Real.mul_self_sqrt`. **Uses**: [`sqrtTwoRoot`] — **Lines**: 108-123 — **Notes**: used in LocalGlobal (house, canonical coords).

### `theorem realEmbedding_root_eq_pos_or_neg`
- **Type**: `(σ : K →ₐ[ℚ] ℝ) → σ sqrtTwoRoot = √2 ∨ = -√2`. **How**: `sq_eq_sq_iff_eq_or_eq_neg`. **Uses**: [`sqrtTwoRoot(_sq)`] — **Lines**: 125-134

### `theorem infinitePlace_card_eq_two`
- **Type**: `Fintype.card (InfinitePlace K) = 2`. **How**: `card_eq_nrRealPlaces_add_nrComplexPlaces` + counts. **Uses**: [`nrRealPlaces_eq_two`,`nrComplexPlaces_eq_zero`] — **Lines**: 137-140

### `theorem infinitePlace_isReal`
- **Type**: `(v : InfinitePlace K) → IsReal v`. **How**: `IsTotallyReal.isReal`. **Uses**: [`isTotallyReal`] — **Lines**: 142-146 — **Notes**: used in LocalGlobal.

### `theorem infinitePlace_apply_sqrtTwoRoot`
- **Type**: `(v : InfinitePlace K) → v sqrtTwoRoot = Real.sqrt 2`. **How**: `norm_embedding_eq`, embedding-square is `2=√2²`, `sq_eq_sq_iff_eq_or_eq_neg`, both branches give `√2`. **Uses**: [`sqrtTwoRoot(_sq)`] — **Lines**: 148-169 — **Notes**: KEY (LocalGlobal house/canonical/completion); proof >20 lines.

**File Summary — Embeddings.lean**: 9 decls (theorems 9, 1 private). Two `noncomputable section`s in one file (signature block + embeddings block). Key API (3+): `isTotallyReal`, `sqrtTwoRoot_sq`, `nrComplexPlaces_eq_zero`. No sorry/set_option. >30-line proofs: none (`isTotallyReal` ~26). `ringHom_ext_sqrtTwo` is a generic helper.

---

## RingOfIntegers.lean

### `theorem sqrtTwoRoot_isIntegral`
- **Type**: `IsIntegral ℤ sqrtTwoRoot`. **How**: witness `X²-C 2`, `monic_X_pow_sub_C`, `sqrtTwoRoot_sq`. **Uses**: [`sqrtTwoRoot_sq`] — **Lines**: 34-37 — **Notes**: KEY.

### `abbrev sqrtTwoInteger`
- **Type**: `𝓞 K := ⟨sqrtTwoRoot, sqrtTwoRoot_isIntegral⟩`. **What**: `√2` in `𝓞 K`. **Uses**: [`sqrtTwoRoot(_isIntegral)`] — **Lines**: 40-41 — **Notes**: KEY — pervasive in every later file.

### `local notation "𝓟₂"` / `abbrev sqrtTwoIntegerPolynomial`
- `𝓟₂ := span ℤ {2}`; `sqrtTwoIntegerPolynomial := X²-C 2` over `ℤ`. **Uses**: [] — **Lines**: 43, 46

### `theorem sqrtTwo_minpoly_rat`
- **Type**: `minpoly ℚ sqrtTwoRoot = sqrtTwoPolynomial`. **How**: transport along `sqrtTwoAdjoinRootEquivQuadratic` via `minpoly.algEquiv_eq` + `AdjoinRoot.minpoly_root`. **Uses**: [`sqrtTwoAdjoinRootToQuadratic_root`,`sqrtTwoAdjoinRootEquivQuadratic`,`sqrtTwoPolynomial`] — **Lines**: 49-57 — **Notes**: KEY.

### `theorem sqrtTwo_minpoly_int`
- **Type**: `minpoly ℤ sqrtTwoRoot = sqrtTwoIntegerPolynomial`. **How**: `map_injective` + `minpoly.isIntegrallyClosed_eq_field_fractions'` + `sqrtTwo_minpoly_rat`. **Uses**: [`sqrtTwoRoot_isIntegral`,`sqrtTwo_minpoly_rat`,`sqrtTwoIntegerPolynomial`] — **Lines**: 60-67

### `theorem sqrtTwo_minpoly_int_isEisenstein`
- **Type**: `(minpoly ℤ sqrtTwoRoot).IsEisensteinAt 𝓟₂`. **What**: `X²-2` is Eisenstein at `2`. **How**: `monic.isEisensteinAt_of_mem_of_notMem`, membership via `Ideal.mem_span_singleton`. **Uses**: [`sqrtTwo_minpoly_int`] — **Lines**: 70-82 — **Notes**: KEY — the engine of integral-closure (no discriminant covering argument).

### `theorem sqrtTwoPowerBasis_discr`
- **Type**: `Algebra.discr ℚ sqrtTwoPowerBasis.basis = 8`. **How**: `discr_powerBasis_eq_norm`; compute `norm(1+1)=4`, `norm(√2)=-2` via `PowerBasis.norm_gen_eq_coeff_zero_minpoly`, `simp`+`norm_num`. **Uses**: [`sqrtTwoPowerBasis(_gen)`,`sqrtTwoRoot`,`sqrtTwoPolynomial`,`sqrtTwo_minpoly_rat`] — **Lines**: 85-106 — **Notes**: proof >20 lines.

### `theorem sqrtTwo_integral_mem_adjoin`
- **Type**: `IsIntegral ℤ z → z ∈ Algebra.adjoin ℤ {sqrtTwoRoot}`. **What**: every algebraic integer lies in `ℤ[√2]`.
- **How**: `Algebra.discr_mul_isIntegral_mem_adjoin` gives `8•z ∈ ℤ[√2]`, then `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt` (Eisenstein theorem at `p=2,n=3`) removes the `2³`. **Uses**: [`sqrtTwoPowerBasis(_gen/_discr)`,`sqrtTwoRoot_isIntegral`,`sqrtTwo_minpoly_int_isEisenstein`] — **Lines**: 108-133 — **Notes**: KEY; proof >20 lines. Cleaner than SqrtFive's discriminant-coordinate-divisibility route.

### `theorem isIntegralClosure_adjoin_sqrtTwoRoot`
- **Type**: `IsIntegralClosure (Algebra.adjoin ℤ {sqrtTwoRoot}) ℤ K`. **How**: injectivity (`Subtype.ext`) + `sqrtTwo_integral_mem_adjoin`; reverse via `Algebra.IsIntegral.adjoin`. **Uses**: [`sqrtTwo_integral_mem_adjoin`,`sqrtTwoRoot_isIntegral`] — **Lines**: 139-157 — **Notes**: KEY.

### `theorem sqrtTwoInteger_adjoin_eq_top`
- **Type**: `Algebra.adjoin ℤ {sqrtTwoInteger} = ⊤`. **How**: `le_antisymm`; pull each `x∈𝓞 K` back via `sqrtTwo_integral_mem_adjoin` + `adjoin_singleton_eq_range_aeval`. **Uses**: [`sqrtTwoInteger`,`sqrtTwo_integral_mem_adjoin`] — **Lines**: 160-178 — **Notes**: KEY (PrimeSplitting Kummer-Dedekind + Different).

### `theorem sqrtTwoInteger_minpoly`
- **Type**: `minpoly ℤ sqrtTwoInteger = sqrtTwoIntegerPolynomial`. **How**: `minpoly.isIntegrallyClosed_eq_field_fractions` (fully explicit `@`-application), `map_injective`, reduce to `sqrtTwo_minpoly_rat`. **Uses**: [`sqrtTwoInteger`,`sqrtTwo_minpoly_rat`,`sqrtTwoIntegerPolynomial`,`sqrtTwoRoot`] — **Lines**: 181-202 — **Notes**: KEY (PrimeSplitting KD/Different); proof >15 lines.

### `abbrev sqrtTwoExplicitIntegralPowerBasis`
- **Type**: `PowerBasis ℤ (𝓞 K) := PowerBasis.ofAdjoinEqTop' …`. **Uses**: [`sqrtTwoInteger(_adjoin_eq_top)`] — **Lines**: 208-211 — **Notes**: KEY.

### `theorem sqrtTwoExplicitIntegralPowerBasis_dim`
- **Type**: `dim = 2`. **How**: `ofAdjoinEqTop'_dim` + `sqrtTwoInteger_minpoly` + `natDegree_X_pow_sub_C`. **Uses**: [those] — **Lines**: 213-218

### `abbrev sqrtTwoExplicitIntegralBasis`
- **Type**: `Basis (Fin 2) ℤ (𝓞 K)` = `[1,√2]` (reindexed power basis). **Uses**: [`sqrtTwoExplicitIntegralPowerBasis(_dim)`] — **Lines**: 221-223 — **Notes**: KEY (PrimeSplitting, Units).

### `theorem sqrtTwoExplicitIntegralBasis_zero` / `…_one`
- **Types**: basis 0 = 1; basis 1 = sqrtTwoInteger. **How**: `Basis.reindex_apply` + `basis_eq_pow`. **Uses**: [`sqrtTwoExplicitIntegralBasis`,`sqrtTwoInteger`] — **Lines**: 226-245

### `theorem sqrtTwoInteger_sq`
- **Type**: `sqrtTwoInteger ^ 2 = (2 : 𝓞 K)`. **How**: `Subtype.ext` + `sqrtTwoRoot_sq`. **Uses**: [`sqrtTwoInteger`,`sqrtTwoRoot_sq`] — **Lines**: 247-250 — **Notes**: KEY — workhorse of all PrimeSplitting/Units factorisation/norm steps.

### `theorem sqrtTwoExplicitIntegralBasis_discr`
- **Type**: `Algebra.discr ℤ sqrtTwoExplicitIntegralBasis = 8`. **How**: `Algebra.discr_localizationLocalization` + `Module.Basis.localizationLocalization` to reduce to `sqrtTwoPowerBasis_discr` via `discr_reindex`. **Uses**: [`sqrtTwoExplicitIntegralBasis(_zero/_one)`,`sqrtTwoPowerBasis(_gen/_dim/_discr)`,`sqrtTwoRoot`] — **Lines**: 252-299 — **Notes**: `set_option linter.flexible false in`; proof >40 lines; heavy localization machinery.

### `theorem sqrtTwo_numberField_discr`
- **Type**: `NumberField.discr K = 8`. **How**: `discr_eq_discr K …` + `sqrtTwoExplicitIntegralBasis_discr`. **Uses**: [`sqrtTwoExplicitIntegralBasis(_discr)`] — **Lines**: 301-304 — **Notes**: KEY (PrimeSplitting `ramified_iff_eq_two`/Different, ClassGroup).

### `theorem integralBasis_discr`
- **Type**: `Algebra.discr ℚ (integralBasis K) = 8`. **How**: `NumberField.coe_discr` + `sqrtTwo_numberField_discr`. **Uses**: [`sqrtTwo_numberField_discr`] — **Lines**: 306-311 — **Notes**: `attribute [local instance] DivisionRing.toRatAlgebra in`.

### `example` (×2)
- **Types**: discr-of-`mulVec` `= det²·discr`; and `=8` when `det=±1` (change-of-basis invariance of disc). **How**: `Algebra.discr_of_matrix_mulVec` + `sqrtTwoPowerBasis_discr`. **Uses**: [`sqrtTwoPowerBasis(_discr)`] — **Lines**: 313-334 — **Notes**: smoke-tests, not named lemmas.

### `theorem sqrtTwoInteger_dvd_two`
- **Type**: `sqrtTwoInteger ∣ (2 : 𝓞 K)`. **How**: witness `sqrtTwoInteger`, `sqrtTwoInteger_sq`. **Uses**: [`sqrtTwoInteger(_sq)`] — **Lines**: 336-342 — **Notes**: ramification flavour (`(√2)²=2`).

### `theorem norm_eq_normForm`
- **Type**: `Algebra.norm ℚ x = x.re² - 2·x.im²`. **What**: norm form = principal form of disc `8`. **How**: `Algebra.norm_apply`, `QuadraticAlgebra.det_toLinearMap_eq_norm`, `QuadraticAlgebra.norm_def`, `ring`. **Uses**: [] — **Lines**: 361-366 — **Notes**: KEY.

### `theorem intNorm_eq_normForm`
- **Type**: `Algebra.norm ℤ (x•1 + y•sqrtTwoInteger) = x² - 2y²` (`x,y:ℤ`). **How**: `Algebra.coe_norm_int`, cast to `K`, `norm_eq_normForm`. **Uses**: [`sqrtTwoInteger`,`norm_eq_normForm`,`sqrtTwoRoot`] — **Lines**: 370-386 — **Notes**: KEY — workhorse of all PrimeSplitting norm computations; twin of SqrtFive's.

### `theorem isUnit_iff_normForm`
- **Type**: `IsUnit (x•1 + y•sqrtTwoInteger) ↔ x²-2y² = ±1`. **What**: the Pell-equation unit criterion. **How**: `isUnit_iff_norm`, `intNorm_eq_normForm`, `abs_eq`. **Uses**: [`sqrtTwoInteger`,`intNorm_eq_normForm`] — **Lines**: 391-402 — **Notes**: docstring links to `sqrtTwoFundamentalUnit_generates_unitGroup` (the full Pell solution).

**File Summary — RingOfIntegers.lean**: ~26 decls (defs/abbrevs ~7, theorems ~17 + 2 examples). Two `noncomputable section`s (ring-of-integers + norm form). Key API (3+): `sqrtTwoInteger`, `sqrtTwoInteger_sq`, `intNorm_eq_normForm`, `sqrtTwoPowerBasis_discr`, `sqrtTwo_minpoly_rat`, `sqrtTwo_integral_mem_adjoin`, `sqrtTwo_numberField_discr`, `sqrtTwoExplicitIntegralBasis(_zero/_one)`. **One `set_option linter.flexible false`** (`sqrtTwoExplicitIntegralBasis_discr`). No sorry. >30-line proofs: `sqrtTwoExplicitIntegralBasis_discr` (localization). The integral-closure route is the **Eisenstein theorem** (`X²-2` Eisenstein at `2`) — mathematically cleaner than SqrtFive's coordinate-divisibility route.

---

## Discriminant.lean

Not present as a standalone file in this folder (the linear-import header mentions it, but discriminant content lives in RingOfIntegers.lean: `sqrtTwoPowerBasis_discr`, `sqrtTwoExplicitIntegralBasis_discr`, `sqrtTwo_numberField_discr`, `integralBasis_discr`). **0 decls.**

---

## PrimeSplitting.lean  (791 lines; imports `Common.lean`)

### `theorem span_two_eq`
- **Type**: `span {2} = span {sqrtTwoInteger}²`. **What**: 2 totally ramifies, `(2)=(√2)²`. **How**: `span_singleton_pow` + `sqrtTwoInteger_sq`. **Uses**: [`sqrtTwoInteger(_sq)`] — **Lines**: 38-39 — **Notes**: KEY.

### `theorem absNorm_span_sqrtTwoInteger`
- **Type**: `absNorm (span {sqrtTwoInteger}) = 2`. **How**: `intNorm_eq_normForm 0 1` (`= -2`, abs `2`), `absNorm_span_singleton`. **Uses**: [`intNorm_eq_normForm`,`sqrtTwoInteger`] — **Lines**: 41-47 — **Notes**: KEY.

### `theorem isPrime_span_sqrtTwoInteger`
- **Type**: `(span {sqrtTwoInteger}).IsPrime`. **How**: `isPrime_of_irreducible_absNorm` + `Nat.prime_two`. **Uses**: [`absNorm_span_sqrtTwoInteger`] — **Lines**: 49-54 — **Notes**: KEY (ClassGroup, LocalGlobal, Different).

### `theorem liesOver_span_sqrtTwoInteger` / `inertiaDeg_span_sqrtTwoInteger` / `ramificationIdx_span_sqrtTwoInteger`
- **Types**: lies over `(2)`; `f=1`; `e=2`. **How**: `liesOver_span_iff`; `absNorm_eq_pow_inertiaDeg'`+`Nat.Prime.pow_eq_iff`; `ramificationIdx_spec` with norm upper bound `8∤4` for the cube. **Uses**: [`isPrime_/absNorm_/span_two_eq`,`sqrtTwoInteger(_sq)`,`intNorm_eq_normForm`] — **Lines**: 56-98 — **Notes**: used in LocalGlobal.

### `theorem span_seven_eq`
- **Type**: `span {7} = span {3+√2} * span {3-√2}`. **What**: 7 splits. **How**: `span_singleton_mul_span_singleton` + `(3+√2)(3-√2)=9-√2²=7`. **Uses**: [`sqrtTwoInteger(_sq)`] — **Lines**: 100-110

### `theorem absNorm_span_three_add_sqrtTwo` / `isPrime_…` / `absNorm_span_three_sub_sqrtTwo` / `isPrime_…`
- **Types**: each norm 7; each prime. **How**: `intNorm_eq_normForm 3 (±1)` (`=7`); `isPrime_of_irreducible_absNorm`. **Uses**: [`intNorm_eq_normForm`,`sqrtTwoInteger`,`absNorm_…`] — **Lines**: 112-145

### `theorem liesOver_span_three_add_sqrtTwo` / `…_sub_…`
- **Types**: each lies over `(7)`. **How**: `liesOver_span_iff` + product `=7`. **Uses**: [`isPrime_…`,`sqrtTwoInteger(_sq)`] — **Lines**: 147-169

### `theorem inertiaDeg_span_three_add_sqrtTwo` / `…_sub_…`
- **Types**: each `f=1` over 7. **How**: `absNorm_eq_pow_inertiaDeg'`+`Nat.Prime.pow_eq_iff`. **Uses**: [`liesOver_…`,`absNorm_…`] — **Lines**: 171-189

### `private theorem absNorm_ne_three`
- **Type**: no ideal of `𝓞 K` has norm 3. **How**: residue field `≃ ZMod 3` (`ZMod.ringEquivOfPrime`), lift `√2` to root of `t²=2` in `ZMod 3`, `revert t; decide` (no solution). **Uses**: [`sqrtTwoInteger(_sq)`] — **Lines**: 191-207 — **Visibility**: private

### `theorem isPrime_span_three`
- **Type**: `(span {3}).IsPrime` (3 inert). **What**: `2` is a non-residue mod `3`. **How**: norm 9, take maximal `M≥(3)`, rule out norms 1,3 (`absNorm_ne_three`), `eq_of_le_of_absNorm_eq`. **Uses**: [`intNorm_eq_normForm`,`sqrtTwoInteger`,`absNorm_ne_three`, Common `eq_of_le_of_absNorm_eq`] — **Lines**: 209-242 — **Notes**: proof >30 lines.

### `theorem absNorm_span_three` / `liesOver_span_three` / `inertiaDeg_span_three`
- **Types**: norm 9; lies over (3); `f=2`. **How**: `intNorm_eq_normForm 3 0`; `liesOver_span_iff`; `absNorm_eq_pow_inertiaDeg'`+`Nat.pow_right_injective`. **Uses**: [`intNorm_eq_normForm`,`isPrime_span_three`,`liesOver_span_three`,`absNorm_span_three`] — **Lines**: 244-266

### `private theorem absNorm_span_natCast`
- **Type**: `absNorm (span {(p:ℕ):𝓞 K}) = p²`. **How**: `Ideal.absNorm_span_natCast`, `RingOfIntegers.rank`, `degree_eq_two`. **Uses**: [`degree_eq_two`] — **Lines**: 268-271 — **Visibility**: private — **Notes**: KEY in the general splitting law; generic.

### `private theorem li_one_sqrtTwo`
- **Type**: `LinearIndependent ℤ ![1, sqrtTwoInteger]`. **How**: transport from `sqrtTwoExplicitIntegralBasis.linearIndependent`. **Uses**: [`sqrtTwoExplicitIntegralBasis(_zero/_one)`,`sqrtTwoInteger`] — **Lines**: 273-281 — **Visibility**: private

### `private theorem exists_o2_coords`
- **Type**: `∀ z:𝓞 K, ∃ A B:ℤ, z = A•1 + B•sqrtTwoInteger`. **How**: `repr`/`sum_repr` of the explicit basis. **Uses**: [`sqrtTwoExplicitIntegralBasis(_…)`,`sqrtTwoInteger`] — **Lines**: 283-291 — **Visibility**: private

### `private theorem unit_sqrtTwo_coeff_not_mem`
- **Type**: `A + B√2` with `B=±1` not in `span {p}` for `p≥2`. **How**: decompose membership, `li_one_sqrtTwo`, `Int.le_of_dvd`. **Uses**: [`sqrtTwoInteger`,`exists_o2_coords`,`li_one_sqrtTwo`] — **Lines**: 293-317 — **Visibility**: private — **Notes**: proof >20 lines.

### `theorem ramified_iff_eq_two`
- **Type**: prime `p` ramifies (`∃P, span{p}≤P²`) ↔ `p=2`. **What**: `p` ramifies iff divides disc `8`. **How**: forward via `not_isUnramifiedAt_…` + different-ideal divisibility (`dvd_differentIdeal_iff`, `absNorm_differentIdeal`, `sqrtTwo_numberField_discr`); backward via `span_two_eq`. **Uses**: [`absNorm_span_natCast`, Common (`not_map_span_natCast_le_pow_succ_…`, `not_isUnramifiedAt_…`), `sqrtTwo_numberField_discr`,`isPrime_span_sqrtTwoInteger`,`span_two_eq`,`sqrtTwoInteger`] — **Lines**: 319-363 — **Notes**: proof >40 lines. KEY public result.

### `theorem ramificationIdx_span_three_add_sqrtTwo` / `…_sub_…` / `ramificationIdx_span_three`
- **Types**: each unramified (`e=1`). **How**: `ramificationIdx_spec`; upper bound by reducing to `ramified_iff_eq_two` (`p≠2`). **Uses**: [`isPrime_…`,`ramified_iff_eq_two`,`span_seven_eq`] — **Lines**: 365-409

### `private theorem absNorm_span_prime_sqrtTwo_sub_of_mul`
- **Type**: `absNorm (span {p, √2-c}) = p` given `(√2-c)(√2+c)=p·k`. **How**: rule out norm 1 (`mem_span_pair`+`unit_sqrtTwo_coeff_not_mem`) and norm p² (`eq_of_le_of_absNorm_eq`+`unit_sqrtTwo_coeff_not_mem`), then Common `eq_prime_of_dvd_prime_sq_…`. **Uses**: [`sqrtTwoInteger`,`unit_sqrtTwo_coeff_not_mem`,`absNorm_span_natCast`, Common `eq_of_le_of_absNorm_eq`,`eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq`] — **Lines**: 411-456 — **Visibility**: private — **Notes**: proof >40 lines.

### `private theorem pm_one_mod_eight_of_prime_norm`
- **Type**: `(∃ P prime, span{p}≤P, absNorm P = p) → p%8∈{1,7}` (`p≠2`). **How**: residue field `≃ ZMod p`, lift `√2` to `t` with `t²=2`, `IsSquare (2:ZMod p)`, then `ZMod.exists_sq_eq_two_iff` (second supplement to QR). **Uses**: [`sqrtTwoInteger(_sq)`] — **Lines**: 458-480 — **Visibility**: private

### `private theorem exists_prime_norm_of_pm_one_mod_eight`
- **Type**: `p%8∈{1,7} → ∃ P prime of norm p above p` (`p≠2`). **How**: `ZMod.exists_sq_eq_two_iff` gives `c` with `c²≡2`, build `span {p, √2-c}`, factorization `(√2-c)(√2+c)=p·k`, `absNorm_span_prime_sqrtTwo_sub_of_mul` + `isPrime_of_irreducible_absNorm`. **Uses**: [`sqrtTwoInteger(_sq)`,`absNorm_span_prime_sqrtTwo_sub_of_mul`] — **Lines**: 482-520 — **Visibility**: private — **Notes**: proof >30 lines.

### `theorem exists_prime_norm_iff_pm_one_mod_eight`
- **Type**: `(∃ P prime of norm p above p) ↔ p%8∈{1,7}` (`p≠2`). **How**: combine the two private lemmas. **Uses**: those — **Lines**: 522-527 — **Notes**: public intermediate.

### `private theorem pm_one_mod_eight_of_splits`
- **Type**: split ⇒ `p%8∈{1,7}` (`p≠2`). **How**: norms multiply to `p²`, one factor norm `p`, reduce to `exists_prime_norm_iff_…`. **Uses**: [`absNorm_span_natCast`,`exists_prime_norm_iff_pm_one_mod_eight`] — **Lines**: 529-561 — **Visibility**: private — **Notes**: proof >30 lines.

### `private theorem splits_of_pm_one_mod_eight`
- **Type**: `p%8∈{1,7} ⇒ ∃ distinct primes P,Q, span{p}=P*Q` (`p≠2`). **How**: get norm-`p` prime `P`, `dvd_iff_le` gives complement `Q`, norms force `absNorm Q = p`, `P≠Q` via `ramified_iff_eq_two`. **Uses**: [`exists_prime_norm_iff_pm_one_mod_eight`,`absNorm_span_natCast`,`ramified_iff_eq_two`] — **Lines**: 563-588 — **Visibility**: private — **Notes**: proof >25 lines.

### `theorem splits_iff_pm_one_mod_eight`
- **Type**: for prime `p≠2`: `(∃ distinct primes P,Q, span{p}=P*Q) ↔ p%8∈{1,7}`. **What**: the quadratic splitting law (`(2/p)=1 ⇔ p≡±1 mod 8`, second supplement). **How**: combine the two private lemmas. **Uses**: those — **Lines**: 590-598 — **Notes**: KEY public result.

### `abbrev sqrtTwoPolynomialMod`
- **Type**: `(ZMod p)[X] := X² - C 2`. **Uses**: [] — **Lines**: 616-617

### `theorem sqrtTwoInteger_exponent_eq_one`
- **Type**: `RingOfIntegers.exponent sqrtTwoInteger = 1`. **What**: `√2` generates the full `𝓞 K`, so KD has no conductor primes. **How**: `exponent_eq_one_iff` + `sqrtTwoInteger_adjoin_eq_top`. **Uses**: [`sqrtTwoInteger_adjoin_eq_top`] — **Lines**: 619-624

### `theorem sqrtTwoInteger_exponent_not_dvd`
- **Type**: `¬ p ∣ exponent sqrtTwoInteger`. **How**: `sqrtTwoInteger_exponent_eq_one` + `not_dvd_one`. **Uses**: [`sqrtTwoInteger_exponent_eq_one`] — **Lines**: 626-630

### `theorem sqrtTwo_kummerDedekind_inertiaDeg` / `…_ramificationIdx`
- **Types**: KD identifies `f` with `natDegree` (resp. `e` with `multiplicity`) of a mod-`p` factor. **How**: `Ideal.inertiaDeg_/ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'` + `sqrtTwoInteger_minpoly`. **Uses**: [`sqrtTwoInteger(_exponent_not_dvd/_minpoly)`,`sqrtTwoPolynomialMod`,`sqrtTwoIntegerPolynomial`] — **Lines**: 632-657

### `theorem sqrtTwoPolynomialMod_two`
- **Type**: `sqrtTwoPolynomialMod 2 = X²`. **What**: KD double root at `2` (ramification). **How**: `(2:ZMod 2)=0`, `simp`. **Uses**: [`sqrtTwoPolynomialMod`] — **Lines**: 659-665

### `theorem sqrtTwoPolynomialMod_seven_factor`
- **Type**: `sqrtTwoPolynomialMod 7 = (X-3)(X+3)`. **What**: KD two roots `±3` (splitting). **How**: `ring_nf` + `2=3²` in `ZMod 7`. **Uses**: [`sqrtTwoPolynomialMod`] — **Lines**: 667-676

### `theorem sqrtTwoPolynomialMod_three_irreducible`
- **Type**: `Irreducible (sqrtTwoPolynomialMod 3)`. **What**: KD irreducible at `3` (inert). **How**: `irreducible_of_degree_le_three_of_not_isRoot` + `fin_cases x` over `ZMod 3`, `decide`. **Uses**: [`sqrtTwoPolynomialMod`] — **Lines**: 678-694

### `theorem exists_root_mod_iff_exists_prime_norm`
- **Type**: `(∃ c:ZMod p, c²=2) ↔ ∃ norm-p prime above p` (`p≠2`). **What**: KD root condition = the norm-`p` prime condition. **How**: `calc` through `p%8∈{1,7}` (`ZMod.exists_sq_eq_two_iff`) + `exists_prime_norm_iff_pm_one_mod_eight`. **Uses**: [`exists_prime_norm_iff_pm_one_mod_eight`] — **Lines**: 696-708

### `theorem differentIdeal_eq_span_two_mul_sqrtTwo`
- **Type**: `differentIdeal ℤ (𝓞 K) = span {2·√2}`. **How**: `conductor_eq_top_of_adjoin_eq_top`, `conductor_mul_differentIdeal`, `aeval` of derivative `2X` of `X²-2`. **Uses**: [`sqrtTwoInteger(_adjoin_eq_top/_minpoly)`,`adjoin_sqrtTwoRoot_eq_top`,`sqrtTwoIntegerPolynomial`] — **Lines**: 724-745 — **Notes**: KEY; proof >15 lines.

### `theorem differentIdeal_eq_span_sqrtTwoInteger_pow_three`
- **Type**: `differentIdeal = span {sqrtTwoInteger}³`. **What**: different is `(√2)³` (matches disc `2³`). **How**: rewrite `2·√2 = √2³` via `sqrtTwoInteger_sq`. **Uses**: [`differentIdeal_eq_span_two_mul_sqrtTwo`,`sqrtTwoInteger_sq`] — **Lines**: 747-755 — **Notes**: KEY.

### `theorem absNorm_differentIdeal_eq_eight`
- **Type**: `absNorm (differentIdeal) = 8`. **How**: `differentIdeal_eq_span_sqrtTwoInteger_pow_three`, `map_pow`, `absNorm_span_sqrtTwoInteger`. **Uses**: [those] — **Lines**: 757-761

### `theorem prime_dvd_differentIdeal_iff_eq_span_sqrtTwo`
- **Type**: nonzero prime `P ∣ differentIdeal ↔ P = span {sqrtTwoInteger}`. **How**: `IsPrime.le_of_pow_le`, maximality (`isPrime_span_sqrtTwoInteger.isMaximal`), `differentIdeal_eq_…_pow_three`. **Uses**: [`differentIdeal_eq_span_sqrtTwoInteger_pow_three`,`sqrtTwoInteger`,`sqrtTwoRoot_sq`,`isPrime_span_sqrtTwoInteger`] — **Lines**: 763-788 — **Notes**: proof >20 lines.

**File Summary — PrimeSplitting.lean**: ~36 decls (defs/abbrevs 2, theorems ~34, ~7 private). Three `noncomputable section`s (Prime Splitting / Kummer-Dedekind / Different). Key API (3+, internal): `intNorm_eq_normForm` (imported), `sqrtTwoInteger_sq` (imported), `absNorm_span_natCast`, `ZMod.exists_sq_eq_two_iff`, `exists_prime_norm_iff_pm_one_mod_eight`, `sqrtTwo_numberField_discr` (imported). Public results: `span_two_eq`, `ramified_iff_eq_two`, `splits_iff_pm_one_mod_eight`, all per-prime split/inert/ramified facts, full Kummer-Dedekind dictionary, `differentIdeal_eq_span_*`. No sorry/set_option. >30-line proofs: `isPrime_span_three`, `ramified_iff_eq_two`, `absNorm_span_prime_sqrtTwo_sub_of_mul`, `exists_prime_norm_of_pm_one_mod_eight`, `pm_one_mod_eight_of_splits`. Heavy reliance on Common.lean. **Note**: leaner than SqrtFive's splitting law — `ZMod.exists_sq_eq_two_iff` (second supplement) does in one lemma what SqrtFive does by hand for `5` via reciprocity.

---

## ClassGroup.lean

### `abbrev sqrtTwoRootFractionalIdeal` / `ramifiedPrimeFractionalIdeal`
- **Types**: `spanSingleton sqrtTwoRoot`; coe of `span {sqrtTwoInteger}`. **Uses**: [`sqrtTwoRoot`,`sqrtTwoInteger`] — **Lines**: 36-41

### `theorem sqrtTwoRoot_mem_fractionalIdeal`
- **Type**: `sqrtTwoRoot ∈ sqrtTwoRootFractionalIdeal`. **How**: `mem_spanSingleton` (witness 1). **Uses**: [`sqrtTwoRootFractionalIdeal`,`sqrtTwoRoot`] — **Lines**: 43-46

### `theorem sqrtTwoRootFractionalIdeal_absNorm`
- **Type**: `absNorm = |Algebra.norm ℚ sqrtTwoRoot|`. **How**: `FractionalIdeal.absNorm_span_singleton`. **Uses**: [`sqrtTwoRootFractionalIdeal`,`sqrtTwoRoot`] — **Lines**: 48-50

### `theorem ramifiedPrimeFractionalIdeal_ne_zero`
- **Type**: `≠ 0`. **How**: `coeIdeal_ne_zero` + `absNorm_span_sqrtTwoInteger` (norm 2 ≠ 0). **Uses**: [`ramifiedPrimeFractionalIdeal`,`sqrtTwoInteger`,`absNorm_span_sqrtTwoInteger`] — **Lines**: 52-59

### `theorem isPrincipalIdealRing`
- **Type**: `IsPrincipalIdealRing (𝓞 K)`. **What**: ring-theoretic content of class number 1. **How**: `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`; bound `|disc|=8` (Minkowski bound `½√8 ≈ 1.41 < 2`), case-split `nrComplexPlaces ≤ 1`, `nlinarith [Real.pi_gt_three]`. **Uses**: [`sqrtTwo_numberField_discr`,`sqrtTwoPowerBasis(_dim)`] — **Lines**: 79-94 — **Notes**: KEY; small-discriminant PIR criterion.

### `theorem uniqueFactorizationMonoid`
- **Type**: `UniqueFactorizationMonoid (𝓞 K)`. **How**: PID ⇒ UFM (`infer_instance`). **Uses**: [`isPrincipalIdealRing`] — **Lines**: 96-99

### `theorem classNumber_eq_one`
- **Type**: `NumberField.classNumber K = 1`. **How**: `classNumber_eq_one_iff.mpr isPrincipalIdealRing`. **Uses**: [`isPrincipalIdealRing`] — **Lines**: 101-104 — **Notes**: KEY.

### `theorem classGroupStructure`
- **Type**: `Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1))`. **How**: card 1 ⇒ `Subsingleton` ⇒ `MulEquiv.ofBijective` of the trivial hom. **Uses**: [`classNumber_eq_one`] — **Lines**: 106-118

### `abbrev unitIdealRepresentative`
- **Type**: `(Ideal (𝓞 K))⁰ := ⟨⊤, …⟩`. **Uses**: [] — **Lines**: 120-121

### `theorem classGroupRepresentative`
- **Type**: `∀ C, C = ClassGroup.mk0 unitIdealRepresentative`. **How**: `Subsingleton.elim`. **Uses**: [`unitIdealRepresentative`,`classNumber_eq_one`] — **Lines**: 123-131

**File Summary — ClassGroup.lean**: 10 decls (abbrevs 3, theorems 7). Two `noncomputable section`s. Key API (3+): `isPrincipalIdealRing`/`classNumber_eq_one`, `sqrtTwo_numberField_discr`. No sorry/set_option. >30-line proofs: none. **Note**: order differs from SqrtFive — here `isPrincipalIdealRing` is the primitive (via `isPrincipalIdealRing_of_abs_discr_lt`) and `classNumber_eq_one` follows. The fractional-ideal decls (36-59) are unused downstream.

---

## Units.lean  (486 lines)

### `abbrev ZSqrtTwo` / `abbrev zsqrtTwoToRingOfIntegers`
- **Types**: `Zsqrtd (2:ℤ)` (mathlib's concrete `ℤ[√2]`); `Zsqrtd.lift ⟨sqrtTwoInteger,…⟩ : ZSqrtTwo →+* 𝓞 K`. **Uses**: [`sqrtTwoInteger(_sq)`] — **Lines**: 42-46 — **Notes**: KEY — the Pell bridge; the whole reason SqrtTwo's fundamental unit is proved.

### `theorem zsqrtTwoToRingOfIntegers_apply`
- **Type**: `zsqrtTwoToRingOfIntegers ⟨a,b⟩ = a + b·√2`. **How**: `simp`. **Uses**: [`zsqrtTwoToRingOfIntegers`] — **Lines**: 48-51

### `theorem two_not_int_square`
- **Type**: `∀ n:ℤ, 2 ≠ n*n`. **How**: `IsSquare 2` + `norm_num`. **Uses**: [] — **Lines**: 53-56

### `theorem zsqrtTwoToRingOfIntegers_injective` / `…_surjective`
- **Types**: injective (`Zsqrtd.lift_injective` + `two_not_int_square`); surjective (decompose target on `sqrtTwoExplicitIntegralBasis`). **Uses**: [`sqrtTwoInteger(_sq)`,`two_not_int_square`,`sqrtTwoExplicitIntegral*`] — **Lines**: 58-84

### `abbrev zsqrtTwoEquivRingOfIntegers`
- **Type**: `ZSqrtTwo ≃+* 𝓞 K := RingEquiv.ofBijective …`. **Uses**: [`zsqrtTwoToRingOfIntegers(_injective/_surjective)`] — **Lines**: 86-89 — **Notes**: KEY.

### `abbrev sqrtTwoFundamentalUnit`
- **Type**: `(𝓞 K)ˣ` with `val = sqrtTwoInteger+1`, `inv = sqrtTwoInteger-1`. **What**: the fundamental unit `1+√2`. **How**: `Subtype.ext` + `(√2+1)(√2-1)=√2²-1=1`. **Uses**: [`sqrtTwoInteger`,`sqrtTwoRoot_sq`] — **Lines**: 91-104 — **Notes**: KEY (LocalGlobal house/adele/product).

### `abbrev zsqrtTwoFundamentalUnit`
- **Type**: `ZSqrtTwoˣ` with `val=⟨1,1⟩`, `inv=⟨-1,1⟩`. **What**: `1+√2` in the `Zsqrtd` model. **Uses**: [] — **Lines**: 106-113

### `theorem zsqrtTwoFundamentalUnit_norm`
- **Type**: `Zsqrtd.norm ⟨1,1⟩ = -1`. **How**: `norm_num [Zsqrtd.norm]`. **Uses**: [`zsqrtTwoFundamentalUnit`] — **Lines**: 115-117 — **Notes**: KEY — norm `-1` (so the *square* is the norm-one Pell solution).

### `theorem zsqrtTwoEquivRingOfIntegers_fundamentalUnit`
- **Type**: `Units.mapEquiv … zsqrtTwoFundamentalUnit = sqrtTwoFundamentalUnit`. **How**: `Units.ext` + `zsqrtTwoToRingOfIntegers_apply`. **Uses**: [both fundamental units, the equiv] — **Lines**: 119-126

### `theorem zsqrtTwoEquivRingOfIntegers_unitsMap_neg`
- **Type**: `mapEquiv (-v) = -(mapEquiv v)`. **How**: `Units.ext` + `map_neg`. **Uses**: [`zsqrtTwoEquivRingOfIntegers`] — **Lines**: 128-134

### `theorem sqrtTwoFundamentalUnit_sq`
- **Type**: `((1+√2)² : 𝓞 K) = 3 + 2√2`. **How**: `Subtype.ext`, expand, `sqrtTwoRoot_sq`. **Uses**: [`sqrtTwoFundamentalUnit`,`sqrtTwoInteger`,`sqrtTwoRoot_sq`] — **Lines**: 136-148

### `abbrev pellTwoFundamentalSolution`
- **Type**: `Pell.Solution₁ (2:ℤ) := Solution₁.mk 3 2 _`. **What**: `3+2√2`, the fundamental norm-one Pell solution of `x²-2y²=1`. **Uses**: [] — **Lines**: 150-152 — **Notes**: KEY.

### `theorem pellTwoFundamentalSolution_isFundamental`
- **Type**: `Pell.IsFundamental pellTwoFundamentalSolution`. **How**: `Pell.IsFundamental` triple — positivity + minimality of `x`-coord (rule out `x=2` via `2y²=3`, `omega`). **Uses**: [`pellTwoFundamentalSolution`] — **Lines**: 159-173 — **Notes**: KEY — the load-bearing Pell minimality fact.

### `theorem pellTwoFundamentalSolution_generates_normOnePell`
- **Type**: `∀ a:Solution₁ 2, ∃ n, a = pell^n ∨ a = -pell^n`. **How**: `IsFundamental.eq_zpow_or_neg_zpow`. **Uses**: [`pellTwoFundamentalSolution(_isFundamental)`] — **Lines**: 175-180 — **Notes**: KEY — mathlib gives the entire norm-one solution group directly.

### `theorem zsqrtTwoFundamentalUnit_sq_toPell`
- **Type**: `Unitary.toUnits pellTwoFundamentalSolution = zsqrtTwoFundamentalUnit²`. **How**: `ext` + `norm_num`. **Uses**: [`pellTwoFundamentalSolution`,`zsqrtTwoFundamentalUnit`] — **Lines**: 182-186

### `theorem zsqrtTwo_normOneUnit_generated_by_square`
- **Type**: norm-one `ZSqrtTwoˣ` units `= ±zsqrtTwoFundamentalUnit^(2n)`. **How**: pass to `Solution₁` (`Zsqrtd.norm_eq_one_iff_mem_unitary`), `pellTwoFundamentalSolution_generates_normOnePell`, `map_zpow`/`zpow_mul`. **Uses**: [`pellTwoFundamentalSolution(_generates…)`,`zsqrtTwoFundamentalUnit(_sq_toPell)`] — **Lines**: 188-226 — **Notes**: proof >30 lines.

### `theorem zsqrtTwo_units_generated_by_fundamental`
- **Type**: every `ZSqrtTwoˣ` unit `= ±zsqrtTwoFundamentalUnit^n`. **How**: norm is `±1` (`Zsqrtd.isUnit_iff_norm_isUnit`, `Int.isUnit_eq_one_or`); norm `-1` case multiplies by the fundamental unit to reach norm `1`, then shifts the exponent. **Uses**: [`zsqrtTwo_normOneUnit_generated_by_square`,`zsqrtTwoFundamentalUnit(_norm)`] — **Lines**: 228-265 — **Notes**: proof >30 lines.

### `theorem sqrtTwoFundamentalUnit_generates_unitGroup`
- **Type**: `∀ u:(𝓞 K)ˣ, ∃ n, u = (1+√2)^n ∨ u = -(1+√2)^n`. **What**: every unit is a signed power of the fundamental unit — **fully proved** (the analogue is a SORRY in every other folder). **How**: transport `zsqrtTwo_units_generated_by_fundamental` along `Units.mapEquiv zsqrtTwoEquivRingOfIntegers`. **Uses**: [`zsqrtTwo_units_generated_by_fundamental`,`zsqrtTwoEquivRingOfIntegers(_fundamentalUnit/_unitsMap_neg)`,`sqrtTwoFundamentalUnit`] — **Lines**: 267-292 — **Notes**: KEY; the decisive theorem of this folder.

### `theorem sqrtTwoFundamentalUnit_isFundamental`
- **Type**: `((1+√2)²=3+2√2) ∧ (∀ Pell solution = ±pell^n)`. **How**: `⟨sqrtTwoFundamentalUnit_sq, pellTwoFundamentalSolution_generates_normOnePell⟩`. **Uses**: [those] — **Lines**: 294-306

### `private theorem sqrtTwo_torsion_eq_one_or_neg_one`
- **Type**: `(x : torsion K) → (x:(𝓞 K)ˣ) = 1 ∨ = -1`. **How**: if `orderOf > 2`, a primitive root of order `>2` would force `nrRealPlaces = 0` (`IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt`), contradicting `nrRealPlaces_eq_two`; else `interval_cases` on order ∈{0,1,2}. **Uses**: [`nrRealPlaces_eq_two`] — **Lines**: 310-334 — **Visibility**: private — **Notes**: proof >20 lines; the totally-real torsion argument.

### `theorem torsionOrder_eq_two`
- **Type**: `Units.torsionOrder K = 2`. **How**: `Finset.card_eq_two` with `{1,-1}` + `sqrtTwo_torsion_eq_one_or_neg_one`. **Uses**: [`sqrtTwo_torsion_eq_one_or_neg_one`] — **Lines**: 336-341 — **Notes**: KEY.

### `theorem unitRank_eq_one`
- **Type**: `Units.rank K = 1`. **How**: `rank = card places - 1`, `nrRealPlaces_eq_two`/`nrComplexPlaces_eq_zero`. **Uses**: [`nrRealPlaces_eq_two`,`nrComplexPlaces_eq_zero`] — **Lines**: 343-348 — **Notes**: KEY.

### `private theorem exists_eq_torsion_mul_fundSystem_zpow`
- **Type**: any unit `u = ζ * fundSystem K i₀ ^ n`, `ζ` torsion. **How**: `closure_fundSystem_sup_torsion_eq_top`, `Subgroup.mem_sup`, subsingleton of `Fin (rank)`. **Uses**: [`unitRank_eq_one`] — **Lines**: 350-373 — **Visibility**: private — **Notes**: proof >20 lines.

### `private theorem fundSystem_zpow_mem_torsion`
- **Type**: `fundSystem K i₀ ^ n` torsion ⇒ `n=0`. **How**: quotient by torsion is free, `basisModTorsion.repr`. **Uses**: [] — **Lines**: 375-389 — **Visibility**: private

### `private theorem eq_one_or_neg_one_of_mem_torsion`
- **Type**: `ζ ∈ torsion ⇒ ζ = ±1`. **How**: `sqrtTwo_torsion_eq_one_or_neg_one`. **Uses**: [`sqrtTwo_torsion_eq_one_or_neg_one`] — **Lines**: 391-395 — **Visibility**: private

### `theorem mem_torsion_iff_eq_one_or_neg_one`
- **Type**: `u ∈ torsion ↔ u = 1 ∨ u = -1`. **How**: `eq_one_or_neg_one_of_mem_torsion` + `neg_one_mem_torsion`. **Uses**: [`eq_one_or_neg_one_of_mem_torsion`] — **Lines**: 397-404 — **Notes**: used in LocalGlobal (fundamental cone).

### `theorem regulator_eq`  ✅ proved
- **Type**: `Units.regulator K = Real.log (1 + Real.sqrt 2)`. **What**: the regulator is `log(1+√2) ≈ 0.8814`. **How**: pick the real place `wR`; show the fundamental-unit family generates the units mod torsion (from the Pell-certified `sqrtTwoFundamentalUnit_generates_unitGroup`); then `regOfFamily_div_regulator` (index = 1) ⇒ `regulator = regOfFamily`, `regOfFamily_eq_det`, and `Matrix.det_eq_elem_of_subsingleton` on the rank-1 `1×1` matrix evaluate it to `|log (wR (1+√2))| = log(1+√2)`. **Uses**: [`sqrtTwoFundamentalUnit_generates_unitGroup`, `unitRank_eq_one`, `infinitePlace_card_eq_two`, `infinitePlace_isReal`, `exists_realEmbedding_pos`] — **Lines**: 406-460 — **Visibility**: public
- **Notes**: the whole computation rests on **mature mathlib API** (`regOfFamily_div_regulator`, `regOfFamily_eq_det`); no missing "regulator = log(unit)" bridge. Correcting an earlier note: the regulator was never an API gap — only downstream of fundamentality, which Pell supplies here.

### `private theorem unitGroupStructure_bijective`
- **Type**: `(torsionPowerHom 2 (-1) _).coprod (rankOnePowerHom η)` is bijective. **How**: injectivity — `fundSystem_zpow_mem_torsion` kills the free part, then `ZMod 2`-parity kills the torsion part (using `(-1:𝓞 K)=1 ⇒ 2=0`); surjectivity — `exists_eq_torsion_mul_fundSystem_zpow` + `eq_one_or_neg_one_of_mem_torsion`. **Uses**: [Common `torsionPowerHom`,`rankOnePowerHom`; `fundSystem_zpow_mem_torsion`,`exists_eq_torsion_mul_fundSystem_zpow`,`eq_one_or_neg_one_of_mem_torsion`] — **Lines**: 411-453 — **Visibility**: private — **Notes**: proof >40 lines.

### `theorem unitGroupStructure`
- **Type**: `Nonempty ((𝓞 K)ˣ ≃* (Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ)))`. **What**: the unit group is `μ₂ × ℤ` as an abstract abelian group — **fully proved, no sorry**. **How**: package `ψ₁.coprod ψ₂` (`torsionPowerHom`/`rankOnePowerHom`), `unitGroupStructure_bijective`, `MulEquiv.ofBijective`. **Uses**: [Common `torsionPowerHom`,`rankOnePowerHom`; `unitRank_eq_one`,`unitGroupStructure_bijective`] — **Lines**: 455-471 — **Notes**: KEY — the abstract structure theorem. Contrast SqrtFive, where the analogous result rests on a sorry.

**File Summary — Units.lean**: ~26 decls (abbrevs/defs ~8, theorems ~18, ~5 private). Two `noncomputable section`s (Units + an empty Regulator block). Key API (3+): `zsqrtTwoFundamentalUnit`, `pellTwoFundamentalSolution`, `sqrtTwoFundamentalUnit`, `sqrtTwo_torsion_eq_one_or_neg_one`, `zsqrtTwoEquivRingOfIntegers`, Common `torsionPowerHom`/`rankOnePowerHom`. **1 sorry** (`regulator_eq`). No set_option. >30-line proofs: `zsqrtTwo_normOneUnit_generated_by_square`, `zsqrtTwo_units_generated_by_fundamental`, `unitGroupStructure_bijective`. **The crucial folder**: the `Zsqrtd`/`Pell.Solution₁` API makes the fundamental-unit / unit-group-structure theorems sorry-free here, unlike all the imaginary-quadratic / golden-ratio twins.

---

## Euclidean.lean

### `private theorem abs_norm_int_lt_of_remainder_eq`
- **Type**: packaging lemma: from `bK = algebraMap b`, `algebraMap r = bK·e`, `|norm bK|>0`, `|norm e| = |(u-round u)² - 2(v-round v)²|`, and that fraction `≤ 1/2`, conclude `|norm ℤ r| < |norm ℤ b|`. **How**: applies Common `abs_intNorm_lt_of_abs_norm_le` with the threshold `1/2 < 1`. **Uses**: [Common `abs_intNorm_lt_of_abs_norm_le`] — **Lines**: 35-46 — **Visibility**: private

### `theorem normEuclidean`
- **Type**: `(a b : 𝓞 K) → b ≠ 0 → ∃ q r, a = b*q + r ∧ (norm ℤ r).natAbs < (norm ℤ b).natAbs`. **What**: `ℚ(√2)` is norm-Euclidean (the real quadratic field of smallest discriminant). **How**: take `q` = nearest-integer rounding of the coordinates of `a/b`; the remainder `e` has `|norm e| = |(u-round u)² - 2(v-round v)²| ≤ 1/2 < 1` (`nlinarith` with `abs_sub_round` bounds and `sq_nonneg`), then the packaging lemma + Common `natAbs_lt_of_abs_ratCast_lt`. **Uses**: [`norm_eq_normForm`,`sqrtTwoRoot`,`sqrtTwoInteger`, Common `abs_intNorm_lt_of_abs_norm_le`,`natAbs_lt_of_abs_ratCast_lt`] — **Lines**: 51-98 — **Notes**: KEY; proof >40 lines. **Strengthens** `isPrincipalIdealRing`. Fully proved (the `½` bound is exact for `d=2`) — contrast CubeRootThree where `normEuclidean` is blocked.

**File Summary — Euclidean.lean**: 2 decls (theorem 1 + 1 private packaging lemma). Key Common API: `abs_intNorm_lt_of_abs_norm_le`, `natAbs_lt_of_abs_ratCast_lt`. No sorry/set_option. >30-line proofs: `normEuclidean`. **Note**: the norm-Euclidean inequality `|x²-2y²| ≤ 1/2` (for `|x|,|y| ≤ 1/2`) is discharged cleanly by `nlinarith`, so no extra covering machinery is needed — `ℚ(√2)` has the cleanest Euclidean proof of all the folders.

---

## LocalGlobal.lean  (561 lines)

### `def vTwo` / `vThree` / `vSevenPlus` / `vSevenMinus`
- **Types**: `HeightOneSpectrum (𝓞 K)` for the primes `(√2)`, `(3)`, `(3+√2)`, `(3-√2)`. **How**: package `isPrime_…` + `ne_bot` (via nonzero `absNorm`). **Uses**: [`isPrime_span_sqrtTwoInteger/_three/_three_add/_sub`,`absNorm_…`,`sqrtTwoInteger`] — **Lines**: 37-74 — **Notes**: KEY (used by completions/finite places).

### `abbrev finitePlaceTwo` / `finitePlaceThree` / `finitePlaceSevenPlus` / `finitePlaceSevenMinus`
- **Types**: `NumberField.FinitePlace K := FinitePlace.mk v…`. **Uses**: [`vTwo`,`vThree`,`vSevenPlus`,`vSevenMinus`] — **Lines**: 76-90

### `example` (×8, finite places)
- **Types**: `ramificationIdx`/`inertiaDeg` of each `v….asIdeal` equal the computed `e`,`f` (`2,1` / `1,2` / `1,1`,`1,1`). **How**: cite the PrimeSplitting lemmas. **Uses**: [`ramificationIdx_/inertiaDeg_span_…`] — **Lines**: 92-122 — **Notes**: smoke-tests tying `HeightOneSpectrum` to the ramification data.

### `abbrev CompletionAtTwo` / `CompletionAtThree` / `CompletionAtSevenPlus` / `CompletionAtSevenMinus`
- **Types**: `v….adicCompletion K`. **Uses**: [the `v…`] — **Lines**: 138-152

### `example` (×3, completions)
- **Types**: `2`-adic remembers `e=2`; `3`-adic inert `f=2`; both `7`-completions `f=1`. **How**: cite PrimeSplitting lemmas. **Uses**: [`ramificationIdx_span_sqrtTwoInteger`,`inertiaDeg_span_three/_add/_sub`] — **Lines**: 154-168

### `abbrev InfiniteCompletion`
- **Type**: `(v : InfinitePlace K) → Type := v.Completion`. **Uses**: [] — **Lines**: 184-186

### `example` (infinite completion ≅ ℝ)
- **Type**: `Nonempty (InfiniteCompletion v ≃+* ℝ)`. **How**: `Completion.ringEquivRealOfIsReal (infinitePlace_isReal v)`. **Uses**: [`infinitePlace_isReal`] — **Lines**: 188-191

### `theorem infiniteCompletion_sqrtTwoRoot_norm`
- **Type**: `‖algebraMap K (InfiniteCompletion v) sqrtTwoRoot‖ = Real.sqrt 2`. **How**: `Completion.norm_coe`, `WithAbs.equiv`, `infinitePlace_apply_sqrtTwoRoot`. **Uses**: [`infinitePlace_apply_sqrtTwoRoot`,`sqrtTwoRoot`] — **Lines**: 193-199

### `theorem infinitePlace_sum_inertiaDeg_eq_two`
- **Type**: `(v : InfinitePlace ℚ) → ∑ w ∈ v.placesOver K, v.inertiaDeg w = 2`. **How**: `sum_inertiaDeg_eq_finrank` + `degree_eq_two`. **Uses**: [`degree_eq_two`] — **Lines**: 201-207 — **Notes**: `open scoped Classical in`.

### `example` (×2, product formula)
- **Types**: product formula `(∏ infinite)(∏ finite) = 1` for `√2` and for the fundamental unit `1+√2`. **How**: `NumberField.prod_abs_eq_one` (nonzero witness). **Uses**: [`sqrtTwoRoot(_sq)`,`sqrtTwoFundamentalUnit`] — **Lines**: 224-245

### `theorem finite_support_sqrtTwoRoot_only_vTwo`
- **Type**: `v ≠ finitePlaceTwo → v sqrtTwoRoot = 1`. **What**: the finite-place support of `√2` is exactly `vTwo`. **How**: `norm_embedding_eq`, `norm_eq_one_iff_notMem`; if `√2 ∈` maximal ideal then `span{√2} ≤ that ideal`, and maximality of `(√2)` forces the ideal `= vTwo`. **Uses**: [`sqrtTwoRoot`,`sqrtTwoInteger`,`finitePlaceTwo`,`vTwo`,`isMaximal vTwo`] — **Lines**: 247-265 — **Notes**: proof >15 lines.

### `abbrev SqrtTwoInfiniteAdeleRing` / `infinitePrincipalAdele_sqrtTwoRoot` / `…_fundamentalUnit`
- **Types**: `InfiniteAdeleRing K`; principal infinite adeles of `√2` and `1+√2`. **Uses**: [`sqrtTwoRoot`,`sqrtTwoFundamentalUnit`] — **Lines**: 281-292

### `example` (×3, infinite adeles)
- **Types**: `‖adele‖ = |norm ℚ ·|` for `√2` and the fundamental unit; `DenseRange (algebraMap K …)`. **How**: `InfiniteAdeleRing.coe_norm_eq_abs_norm`, `denseRange_algebraMap`. **Uses**: [`sqrtTwoRoot`,`sqrtTwoFundamentalUnit`] — **Lines**: 294-306

### `private theorem complexEmbedding_norm_sqrtTwoRoot`
- **Type**: `(φ : K →+* ℂ) → ‖φ sqrtTwoRoot‖ = Real.sqrt 2`. **How**: `infinitePlace_apply_sqrtTwoRoot` on `InfinitePlace.mk φ`. **Uses**: [`infinitePlace_apply_sqrtTwoRoot`,`sqrtTwoRoot`] — **Lines**: 322-324 — **Visibility**: private

### `theorem canonicalEmbedding_norm_sqrtTwoRoot`
- **Type**: `‖canonicalEmbedding K sqrtTwoRoot‖ = Real.sqrt 2`. **What**: the house of `√2`. **How**: `le_antisymm`; `canonicalEmbedding.norm_le_iff` + `norm_le_pi_norm`. **Uses**: [`complexEmbedding_norm_sqrtTwoRoot`,`sqrtTwoRoot`] — **Lines**: 326-337 — **Notes**: used in House.

### `theorem canonicalEmbedding_sqrtTwoInteger_mem_integerLattice`
- **Type**: `canonicalEmbedding K (algebraMap sqrtTwoInteger) ∈ integerLattice K`. **How**: exhibit the preimage in `RingHom.range`. **Uses**: [`sqrtTwoInteger`] — **Lines**: 339-345

### `theorem canonicalEmbedding_fundamentalUnit_coordinates`
- **Type**: `∃ σ τ : K →+* ℂ`, `σ(1+√2) = 1+√2` and `τ(1+√2) = 1-√2`. **How**: `exists_realEmbedding_pos/_neg`, compose with `Complex.ofRealHom`. **Uses**: [`exists_realEmbedding_pos/_neg`,`sqrtTwoRoot`,`sqrtTwoFundamentalUnit`] — **Lines**: 347-362 — **Notes**: used in House.

### `abbrev mixedEmbedding_sqrtTwoRoot`
- **Type**: `mixedEmbedding.mixedSpace K := mixedEmbedding K sqrtTwoRoot`. **Uses**: [`sqrtTwoRoot`] — **Lines**: 378-380

### `example` (×3, geometry of numbers)
- **Types**: `mixedEmbedding_sqrtTwoRoot ∈ convexBodyLT K f` under `w √2 < f w`; `MeasurableSet (fundamentalCone K)`; `MeasurableSet (fundamentalCone.normLeOne K)`. **How**: `convexBodyLT_mem`, `measurableSet_fundamentalCone`, `fundamentalCone.measurableSet_normLeOne`. **Uses**: [`mixedEmbedding_sqrtTwoRoot`,`sqrtTwoRoot`] — **Lines**: 382-394

### `theorem polarSpace_nonempty`
- **Type**: `Nonempty (mixedEmbedding.polarSpace K)`. **How**: `infer_instance`. **Uses**: [] — **Lines**: 396-398

### `theorem unit_smul_mem_fundamentalCone_iff_eq_one_or_neg_one`
- **Type**: for `x` in the fundamental cone, `u • x ∈ cone ↔ u = 1 ∨ u = -1`. **How**: `fundamentalCone.unit_smul_mem_iff_mem_torsion` + `mem_torsion_iff_eq_one_or_neg_one`. **Uses**: [`mem_torsion_iff_eq_one_or_neg_one`] — **Lines**: 400-408 — **Notes**: ties the (proved) torsion `{±1}` to the geometry of numbers.

### `theorem house_sqrtTwoRoot`
- **Type**: `NumberField.house sqrtTwoRoot = Real.sqrt 2`. **How**: unfold `house` + `canonicalEmbedding_norm_sqrtTwoRoot`. **Uses**: [`canonicalEmbedding_norm_sqrtTwoRoot`,`sqrtTwoRoot`] — **Lines**: 424-427

### `theorem house_sqrtTwoInteger`
- **Type**: `house (algebraMap sqrtTwoInteger) = Real.sqrt 2`. **How**: `simpa` from `house_sqrtTwoRoot`. **Uses**: [`house_sqrtTwoRoot`,`sqrtTwoInteger`] — **Lines**: 429-432

### `theorem house_sqrtTwoFundamentalUnit`
- **Type**: `house (algebraMap (1+√2)) = 1 + Real.sqrt 2`. **How**: `le_antisymm`; upper bound `norm_add_le` per embedding (each `‖φ√2‖=√2`); lower bound from the real embedding `σ(1+√2)=1+√2` of `canonicalEmbedding_fundamentalUnit_coordinates`. **Uses**: [`infinitePlace_apply_sqrtTwoRoot`,`canonicalEmbedding_fundamentalUnit_coordinates`,`sqrtTwoRoot`,`sqrtTwoFundamentalUnit`] — **Lines**: 434-457 — **Notes**: proof >20 lines.

### `abbrev SqrtTwoAdeleRing` / `principalAdele_sqrtTwoRoot` / `…_fundamentalUnit`
- **Types**: `AdeleRing (𝓞 K) K`; principal adeles of `√2` and `1+√2`. **Uses**: [`sqrtTwoRoot`,`sqrtTwoFundamentalUnit`] — **Lines**: 473-483

### `theorem principalAdele_sqrtTwoRoot_ne_zero`
- **Type**: `principalAdele_sqrtTwoRoot ≠ 0`. **How**: `AdeleRing.algebraMap_injective`; `√2=0 ⇒ 2=0`. **Uses**: [`principalAdele_sqrtTwoRoot`,`sqrtTwoRoot(_sq)`] — **Lines**: 485-494

### `theorem principalAdele_fundamentalUnit_is_unit_everywhere`
- **Type**: `∀ v : FinitePlace K, v (algebraMap (1+√2)) = 1`. **What**: the unit is a local unit at every finite place. **How**: `norm_embedding_eq`, `norm_eq_one_iff_notMem`; if `(1+√2) ∈` maximal ideal then so is `(1+√2)(√2-1)=1`, contradiction. **Uses**: [`sqrtTwoFundamentalUnit`,`sqrtTwoInteger`,`sqrtTwoRoot_sq`] — **Lines**: 496-524 — **Notes**: proof >20 lines.

### `abbrev sqrtTwoDedekindZeta` / `sqrtTwoDedekindZetaResidue`
- **Types**: `dedekindZeta K s`; `dedekindZeta_residue K`. **Uses**: [] — **Lines**: 540-546

### `example` (×2, zeta)
- **Types**: residue `> 0`; the class-number-formula expansion `residue = (2^r₁ (2π)^r₂ · reg · h)/(w · √|disc|)`. **How**: `dedekindZeta_residue_pos`, `dedekindZeta_residue_def`. **Uses**: [] — **Lines**: 548-558

**File Summary — LocalGlobal.lean**: ~34 named decls + ~18 `example` smoke-tests. Seven+ `noncomputable section`s (Finite Places / Completions / Infinite Completions / Product Formula / Infinite Adeles / Canonical Embedding (+Geometry) / House / Adeles / Zeta). Key API (3+): `sqrtTwoRoot`, `infinitePlace_apply_sqrtTwoRoot`, `sqrtTwoFundamentalUnit`, the `v…`/`finitePlace…`/`Completion…` families, `canonicalEmbedding_*`. No sorry/set_option. >30-line proofs: none individually (several ~20-25). Most "results" here are `example` smoke-tests pinning the local data to mathlib's adele/place/zeta API rather than new theorems.

---

## Folder-level notes

- **Sorry count: 0.** Everything — including the full unit-group structure theorem `μ₂ × ℤ`, the fundamental unit `1+√2` (via mathlib's `Zsqrtd`/`Pell.Solution₁` API), and now `regulator_eq` (via `regOfFamily_eq_det`) — is proved. This is the most-complete of the case-study folders.
- **Generic/duplicated helpers**: `ringHom_ext_sqrtTwo` (Embeddings) is a generic `QuadraticAlgebra` ext lemma; `absNorm_span_natCast`, `li_one_sqrtTwo`, `exists_o2_coords`, `unit_sqrtTwo_coeff_not_mem` mirror the SqrtFive private toolkit.
- **set_option**: one `set_option linter.flexible false` (RingOfIntegers `sqrtTwoExplicitIntegralBasis_discr`).
- **Discriminant 8 = 2³**; one ramified prime `(√2)` (`e=2,f=1`); splitting law `p ≡ ±1 (mod 8)` via the second supplement (`ZMod.exists_sq_eq_two_iff`); class number 1; norm-Euclidean.
