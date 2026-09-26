# Inventory: XYin/PhD/Cox/FormalCoxProduct.lean  (228 lines)

Packages the formal product `Φ_m(X) = ∏_{σ ∈ C(m)} (X − transformedJSeries ζ σ)` in
`Polynomial (LaurentSeries K)` (Cox (11.13)) and proves every coefficient of every Laurent
coefficient is an ordinary integer: the coefficients are integral over ℤ (subring of
coefficientwise-integral Laurent series) and Galois-fixed (`ζ ↦ ζ^r` reindexes `C(m)`), hence
rational, hence integral. Executed inside the concrete cyclotomic subfield `ℚ(ζ_m) ⊆ ℂ`.

## Declarations

### `def Cox.formalCoxPolynomial`
- **Type**: `{K} [Field K] (m : ℕ+) (ζ : K) : Polynomial (LaurentSeries K)` := `∏ σ : CoxMatrix m, (X - C (transformedJSeries ζ σ))`
- **What**: The formal Cox product, a monic polynomial over Laurent series whose roots are the (11.13) series.
- **How**: `Finset.prod` over the `Fintype` `CoxMatrix m`.
- **Hypotheses**: `K` a field.
- **Uses from project**: [`CoxMatrix`, `transformedJSeries`]
- **Used by**: `formalCoxPolynomial_map`, `formalCoxPolynomial_coeff_integral`, `formalCoxPolynomial_pow_eq`, `formalCoxPolynomial_coeff_fixed`, `formalCoxPolynomial_coeff_eq_int`, `formalCoxPolynomial_coeff_isInteger`
- **Visibility**: public
- **Lines**: 24–27
- **Notes**: Uses `Finset.prod` directly (no duplication of `Polynomial.prod`/`Multiset.prod`); mathlib's Vieta API (`Multiset.prod_X_sub_C_coeff`, RingTheory/Polynomial/Vieta.lean) would express coefficients as `esymm` of the roots but is not needed. Used by 5 other files. No `natDegree`/`monic`/`leadingCoeff` companion lemmas here.

### `private lemma Cox.transformedJSeries_map`
- **Type**: `(φ : K →+* L) (ζ : K) (σ) : (transformedJSeries ζ σ).map φ = transformedJSeries (φ ζ) σ`
- **What**: The (11.13) series is natural in the field: applying `φ` coefficientwise replaces `ζ` by `φ ζ`.
- **How**: `HahnSeries.ext`, `HahnSeries.map_coeff` (the `@[simps]` projection of `HahnSeries.map`, RingTheory/HahnSeries/Basic.lean:143), `map_mul`, `map_zpow₀`, `map_intCast`.
- **Hypotheses**: `K, L` fields.
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_coeff`]
- **Used by**: `formalCoxPolynomial_map`
- **Visibility**: private
- **Lines**: 29–37, proof ≈ 6 lines
- **Notes**: —

### `private lemma Cox.formalCoxPolynomial_map`
- **Type**: `(φ : K →+* L) (m) (ζ) : (formalCoxPolynomial m ζ).map {toFun := (·.map φ), …} = formalCoxPolynomial m (φ ζ)`
- **What**: Naturality of the formal product under coefficient ring homs.
- **How**: `Polynomial.map_prod` + `transformedJSeries_map`, via `simp`.
- **Hypotheses**: `K, L` fields.
- **Uses from project**: [`formalCoxPolynomial`, `transformedJSeries_map`]
- **Used by**: `formalCoxPolynomial_coeff_fixed`, `formalCoxPolynomial_coeff_isInteger`
- **Visibility**: private
- **Lines**: 39–49, proof ≈ 2 lines (+ 5-line inline RingHom)
- **Notes**: Lines 42–46 hand-build the ring hom `LaurentSeries K →+* LaurentSeries L` from `HahnSeries.map_zero/one/add/mul`; mathlib has NO bundled `HahnSeries.mapRingHom` (grep of `RingTheory/HahnSeries/*` for `mapRingHom|map_ringHom` finds nothing; `HahnSeries.map` at Basic.lean:143 is a bare function over `ZeroHomClass`). Mathlib-worthy addition.

### `private def Cox.integralLaurentSeries`
- **Type**: `(K) [Field K] [CharZero K] : Subring (LaurentSeries K)` with carrier `{F | ∀ k, IsIntegral ℤ (F.coeff k)}`
- **What**: Laurent series all of whose coefficients are algebraic integers.
- **How**: closure axioms from `isIntegral_zero/one`, `IsIntegral.add/neg/mul/sum`; multiplication via `HahnSeries.coeff_mul` (finite sum over the antidiagonal).
- **Hypotheses**: `K` field of char 0 (CharZero is not used in any proof).
- **Uses from project**: []
- **Used by**: `transformedJSeries_mem_integralLaurentSeries`, `formalCoxPolynomial_coeff_integral`
- **Visibility**: private
- **Lines**: 51–72
- **Notes**: Re-implements, for `LaurentSeries` and the predicate `IsIntegral ℤ`, what `XYin/PhD/IntegralPowerSeries/IntegralPowerSeries.lean` does for `PowerSeries ℂ` and the predicate "in the image of `R`" (`IntegralPowerSeriesSubring` line 150, `IsIntegralPowerSeries` line 154, `HasCoeffsIn R A` line 51, `powerSeriesMapSubalgebra` line 43). `IsIntegralPowerSeries` is NOT imported or reused here (imports: `Mathlib.NumberTheory.Cyclotomic.Gal`, `XYin.PhD.Cox.CoxMatrices`); the predicates differ (integral closure vs image of ℤ) because `ζ`-powers are integral but not in ℤ. Mathlib has no "coefficients in a subring" Hahn-series subring (only `cardSuppLTSubring`, HahnSeries/Cardinal.lean:190); the mathlib-shaped construction is `(integralClosure ℤ K).subtype` pushed through a (missing) `HahnSeries.mapRingHom`, whose `RingHom.range` is this subring.

### `private lemma Cox.transformedJSeries_mem_integralLaurentSeries`
- **Type**: `(hζ : IsPrimitiveRoot ζ m) (σ) : transformedJSeries ζ σ ∈ integralLaurentSeries K`
- **What**: Each (11.13) series has algebraic-integer coefficients (`c_n ∈ ℤ`, `ζ^k` a root of unity).
- **How**: `IsIntegral.mul` of `isIntegral_algebraMap` and `IsIntegral.of_pow` with `(ζ^e)^m = 1` via `hζ.zpow_eq_one`.
- **Hypotheses**: `ζ` a primitive `m`-th root.
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_coeff`, `integralLaurentSeries`, `jIntCoeff`]
- **Used by**: `formalCoxPolynomial_coeff_integral`
- **Visibility**: private
- **Lines**: 74–89, proof ≈ 13 lines
- **Notes**: Mathlib has `IsPrimitiveRoot.isIntegral` (used at 207) — `hζ.isIntegral` for `ζ^e` would replace the 5-line `hpow` block (84–88) via `IsIntegral.zpow`? (mathlib: `IsIntegral.pow`; `IsIntegral.zpow` not verified).

### `private lemma Cox.formalCoxPolynomial_coeff_integral`
- **Type**: `(hζ) (n : ℕ) (k : ℤ) : IsIntegral ℤ (((formalCoxPolynomial m ζ).coeff n).coeff k)`
- **What**: Every Laurent coefficient of every polynomial coefficient is an algebraic integer.
- **How**: Rebuild the product in `Polynomial (integralLaurentSeries K)` and map along `S.subtype` (`Polynomial.map_prod`, `Polynomial.coeff_map`); the coefficient is then a subtype element.
- **Hypotheses**: `ζ` primitive.
- **Uses from project**: [`formalCoxPolynomial`, `integralLaurentSeries`, `transformedJSeries`, `transformedJSeries_mem_integralLaurentSeries`, `CoxMatrix`]
- **Used by**: `formalCoxPolynomial_coeff_eq_int`
- **Visibility**: private
- **Lines**: 91–104, proof ≈ 11 lines
- **Notes**: Standard "polynomial over a subring" descent.

### `private lemma Cox.transformedJSeries_pow_eq_reindex`
- **Type**: `(hζ : IsPrimitiveRoot ζ m) (r) (hr : r ⊥ m) (σ) : transformedJSeries (ζ ^ r) σ = transformedJSeries ζ (reindex r hr σ)`
- **What**: Replacing `ζ` by `ζ^r` is the same as reindexing `b ↦ br mod d` (the Galois action on (11.13)).
- **How**: Coefficientwise; reduce to `ζ^(ab r t) = ζ^(a (br mod d) t)` via `IsPrimitiveRoot.zpow_eq_one_iff_dvd` and `Nat.mod_add_div`, with `m = ad` and a `linear_combination`.
- **Hypotheses**: `ζ` primitive, `r ⊥ m`.
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_coeff`, `reindex`, `CoxMatrix.determinant`]
- **Used by**: `formalCoxPolynomial_pow_eq`
- **Visibility**: private
- **Lines**: 106–131, proof ≈ 24 lines
- **Notes**: `simp only [reindex]` (113) unfolds the whole `refine` term for lack of `reindex_a/_b/_d` lemmas.

### `private lemma Cox.formalCoxPolynomial_pow_eq`
- **Type**: `(hζ) (r) (hr : r ⊥ m) : formalCoxPolynomial m (ζ ^ r) = formalCoxPolynomial m ζ`
- **What**: The formal product is invariant under `ζ ↦ ζ^r`.
- **How**: `transformedJSeries_pow_eq_reindex` + `Function.Bijective.prod_comp` with `reindex_bijective`.
- **Hypotheses**: as above.
- **Uses from project**: [`formalCoxPolynomial`, `transformedJSeries_pow_eq_reindex`, `reindex_bijective`, `transformedJSeries`, `CoxMatrix`]
- **Used by**: `formalCoxPolynomial_coeff_fixed`
- **Visibility**: private
- **Lines**: 133–141, proof ≈ 4 lines
- **Notes**: —

### `private lemma Cox.formalCoxPolynomial_coeff_fixed`
- **Type**: `[Algebra ℚ K] (hζ) [IsCyclotomicExtension {m} ℚ K] (n) (k) (φ : K ≃ₐ[ℚ] K) : φ (((formalCoxPolynomial m ζ).coeff n).coeff k) = …`
- **What**: Every coefficient is fixed by `Gal(K/ℚ)`.
- **How**: `IsPrimitiveRoot.autToPow` (RootsOfUnity/PrimitiveRoots.lean:818 `autToPow_spec`) gives `φ ζ = ζ^r` with `r ⊥ m` (`ZMod.val_coe_unit_coprime`, Data/ZMod/Basic.lean:799); combine `formalCoxPolynomial_map φ` with `formalCoxPolynomial_pow_eq` and read off coefficients.
- **Hypotheses**: `K/ℚ` cyclotomic of level `m`, `ζ` primitive.
- **Uses from project**: [`formalCoxPolynomial`, `formalCoxPolynomial_map`, `formalCoxPolynomial_pow_eq`]
- **Used by**: `formalCoxPolynomial_coeff_eq_int`
- **Visibility**: private
- **Lines**: 143–161, proof ≈ 12 lines
- **Notes**: —

### `private lemma Cox.formalCoxPolynomial_coeff_eq_int`
- **Type**: `[Algebra ℚ K] (hζ) [IsCyclotomicExtension {m} ℚ K] (n) (k) : ∃ z : ℤ, ((formalCoxPolynomial m ζ).coeff n).coeff k = (z : K)`
- **What**: Galois-fixed + integral ⇒ in ℤ.
- **How**: `IsGalois.mem_range_algebraMap_iff_fixed` (FieldTheory/Galois/Basic.lean:342) with `IsCyclotomicExtension.isGalois`/`finiteDimensional`, then `isIntegral_algebraMap_iff` and `IsIntegrallyClosed.algebraMap_eq_of_integral` (IntegralClosure/IntegrallyClosed.lean:173) for `ℤ ⊆ ℚ`.
- **Hypotheses**: as above.
- **Uses from project**: [`formalCoxPolynomial`, `formalCoxPolynomial_coeff_integral`, `formalCoxPolynomial_coeff_fixed`]
- **Used by**: `formalCoxPolynomial_coeff_isInteger`
- **Visibility**: private
- **Lines**: 163–189, proof ≈ 25 lines
- **Notes**: The general step "x integral over ℤ and fixed by every ℚ-automorphism of a finite Galois K/ℚ ⇒ x ∈ ℤ" (169–184) is a reusable lemma with no single mathlib analogue found (searched `mem_range_algebraMap_iff_fixed`, `algebraMap_eq_of_integral`; they must be composed). This lemma is the real theorem (any cyclotomic field); it is private while only the ℂ-specialisation is public.

### `private abbrev Cox.zetaField`
- **Type**: `(m : ℕ+) : IntermediateField ℚ ℂ` := `IntermediateField.adjoin ℚ {zeta m}`
- **What**: The concrete cyclotomic field `ℚ(ζ_m) ⊆ ℂ`.
- **How**: `IntermediateField.adjoin`.
- **Hypotheses**: none.
- **Uses from project**: [`zeta`]
- **Used by**: `zetaFieldRoot`, `zetaFieldRoot_isPrimitiveRoot`, `zetaField_isCyclotomicExtension`, `formalCoxPolynomial_coeff_isInteger`
- **Visibility**: private
- **Lines**: 191–192
- **Notes**: Alternative: mathlib's `CyclotomicField m ℚ` with its built-in `IsCyclotomicExtension` instance and an embedding into ℂ — but then one would need to match its `zeta` with `Cox.zeta`; the adjoin route is fine.

### `private def Cox.zetaFieldRoot`
- **Type**: `(m) : zetaField m` := `⟨zeta m, subset_adjoin …⟩`
- **What**: `ζ_m` as an element of `ℚ(ζ_m)`.
- **How**: `IntermediateField.subset_adjoin`.
- **Hypotheses**: none.
- **Uses from project**: [`zeta`, `zetaField`]
- **Used by**: `zetaFieldRoot_isPrimitiveRoot`, `formalCoxPolynomial_coeff_isInteger`
- **Visibility**: private
- **Lines**: 194–195
- **Notes**: —

### `private lemma Cox.zetaFieldRoot_isPrimitiveRoot`
- **Type**: `IsPrimitiveRoot (zetaFieldRoot m) m`
- **What**: It is primitive in the subfield.
- **How**: `IsPrimitiveRoot.coe_submonoidClass_iff` (PrimitiveRoots.lean:158) + `zeta_isPrimitiveRoot`.
- **Hypotheses**: none.
- **Uses from project**: [`zetaFieldRoot`, `zeta_isPrimitiveRoot`, `zetaField`]
- **Used by**: `formalCoxPolynomial_coeff_isInteger`
- **Visibility**: private
- **Lines**: 197–200, proof ≈ 2 lines
- **Notes**: —

### `private instance Cox.zetaField_isCyclotomicExtension`
- **Type**: `(m) : IsCyclotomicExtension {m} ℚ (zetaField m)`
- **What**: `ℚ(ζ_m)` is a cyclotomic extension of ℚ.
- **How**: `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic` (IntermediateField/Adjoin/Algebra.lean:150) with `IsPrimitiveRoot.isIntegral` (+ `tower_top`), then `IsPrimitiveRoot.adjoin_isCyclotomicExtension` (NumberTheory/Cyclotomic/Basic.lean:470).
- **Hypotheses**: none.
- **Uses from project**: [`zetaField`, `zeta`, `zeta_isPrimitiveRoot`]
- **Used by**: `formalCoxPolynomial_coeff_isInteger` (instance argument of `formalCoxPolynomial_coeff_eq_int`)
- **Visibility**: private
- **Lines**: 202–208, proof ≈ 5 lines
- **Notes**: —

### `theorem Cox.formalCoxPolynomial_coeff_isInteger`
- **Type**: `(m : ℕ+) (n : ℕ) (k : ℤ) : ∃ z : ℤ, ((formalCoxPolynomial m (zeta m)).coeff n).coeff k = (z : ℂ)`
- **What**: Every coefficient of the formal Cox product over ℂ is an ordinary integer (the formal half of Cox Thm 11.18(i)).
- **How**: Apply `formalCoxPolynomial_coeff_eq_int` in `ℚ(ζ_m)` and transport along the inclusion `ℚ(ζ_m) →+* ℂ` with `formalCoxPolynomial_map`.
- **Hypotheses**: none.
- **Uses from project**: [`formalCoxPolynomial`, `zeta`, `formalCoxPolynomial_coeff_eq_int`, `zetaFieldRoot_isPrimitiveRoot`, `zetaField`, `zetaFieldRoot`, `formalCoxPolynomial_map`, `zetaField_isCyclotomicExtension`]
- **Used by**: unused in file (used by ModularPolynomial/IntegralDescent.lean)
- **Visibility**: public
- **Lines**: 211–226, proof ≈ 14 lines
- **Notes**: Existential statement; a `Polynomial (LaurentSeries ℤ)` lift (`∃ P : (LaurentSeries ℤ)[X], P.map (mapRingHom Int.cast) = formalCoxPolynomial m (zeta m)`) would be the stronger, mathlib-shaped form.

## File Summary
- Total declarations: 15 (4 defs/abbrevs, 10 lemmas/theorems, 1 instance, 0 other)
- Key API (used by 3+ others in the file): `formalCoxPolynomial` (6), `transformedJSeries` (5, from LaurentExpansion), `zetaField` (4), `formalCoxPolynomial_map` (2), `integralLaurentSeries` (2)
- Unused declarations (not used by anything in this file): `formalCoxPolynomial_coeff_isInteger` (used by IntegralDescent.lean)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: `formalCoxPolynomial_coeff_eq_int` 163–189, 25; `transformedJSeries_pow_eq_reindex` 106–131, 24)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `formalCoxPolynomial` (24) is a plain `Finset.prod` of `X - C r`; it does not duplicate `Polynomial.prod`/`Multiset.prod` machinery. Its coefficients being integral could alternatively come from Vieta (`Multiset.prod_X_sub_C_coeff`, RingTheory/Polynomial/Vieta.lean) + `IsIntegral.esymm`-style closure, but the subring route (51–104) is shorter.
- `integralLaurentSeries` (51): no mathlib subring of Hahn series by coefficient membership (only `HahnSeries.cardSuppLTSubring`, Cardinal.lean:190). The mathlib-shaped route is `HahnSeries.map` (Basic.lean:143) with a bundled `HahnSeries.mapRingHom (f : R →+* S) : R⟦Γ⟧ →+* S⟦Γ⟧` (ABSENT in mathlib; hand-built at 42–46) applied to `(integralClosure ℤ K).subtype`; then `integralLaurentSeries K = (mapRingHom _).range` and `mul_mem'` (69–72, using `HahnSeries.coeff_mul` + `IsIntegral.sum`) is free. Also `HahnSeries.ofPowerSeries` (HahnSeries/PowerSeries.lean:89) + `PowerSeries.map` would connect to the project's `IntegralPowerSeries` framework for the holomorphic part only; not applicable to the pole term.
- `IsIntegralPowerSeries` (IntegralPowerSeries/IntegralPowerSeries.lean:154) and `HasCoeffsIn` (line 51) are NOT reused — this file re-implements the "coefficientwise closed under ring operations" argument for `LaurentSeries` with the `IsIntegral ℤ` predicate. A single generic `HahnSeries.coeffMemSubring (S : Subring R) : Subring R⟦Γ⟧` (carrier `{F | ∀ k, F.coeff k ∈ S}`) would serve both files: `IntegralPowerSeriesSubring` = the `S = (algebraMap ℤ ℂ).range`, `Γ = ℕ` case (via `ofPowerSeries`), and `integralLaurentSeries K` = the `S = integralClosure ℤ K`, `Γ = ℤ` case.
- The descent "integral + Galois-fixed ⇒ in ℤ" (169–184) composes `IsGalois.mem_range_algebraMap_iff_fixed` (FieldTheory/Galois/Basic.lean:342) and `IsIntegrallyClosed.algebraMap_eq_of_integral` (IntegrallyClosed.lean:173); no single mathlib lemma found — mathlib-worthy as `exists_int_eq_of_isIntegral_of_forall_algEquiv_fixed`.
- `IsPrimitiveRoot.autToPow` (PrimitiveRoots.lean:818), `ZMod.val_coe_unit_coprime` (ZMod/Basic.lean:799), `IsPrimitiveRoot.adjoin_isCyclotomicExtension` (Cyclotomic/Basic.lean:470), `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic` (Adjoin/Algebra.lean:150), `IsPrimitiveRoot.coe_submonoidClass_iff` (PrimitiveRoots.lean:158) — all correctly used; no re-implementation.
### Missing API / repeated patterns
- `HahnSeries.mapRingHom` (42–46) — bundle once; also needed for `formalCoxPolynomial_coeff_isInteger`'s transport (216–224, where `ι` is again applied coefficientwise by `change`).
- `reindex_a/_b/_d` simp lemmas (113) shared with LaurentExpansion.lean:333–338.
- A public, field-generic `formalCoxPolynomial_coeff_eq_int` (163) — currently private while the ℂ-only corollary (211) is public; downstream (IntegralDescent) may want the `ℚ(ζ)` version.
- `formalCoxPolynomial_monic`, `formalCoxPolynomial_natDegree : natDegree = Fintype.card (CoxMatrix m)` (mathlib `Polynomial.monic_prod_of_monic`, `Polynomial.natDegree_prod_of_monic`) — absent; presumably re-proved downstream.
- The "read off a coefficient of a mapped polynomial-of-Laurent-series" step (`congrArg (fun P ↦ (P.coeff n).coeff k)` + `Polynomial.coeff_map` + `HahnSeries.map_coeff`) is repeated at 159–161 and 219–226 → `formalCoxPolynomial_map_coeff_coeff` helper.
### Junk candidates
- `[CharZero K]` on `integralLaurentSeries` (51), `transformedJSeries_mem_integralLaurentSeries` (75), `formalCoxPolynomial_coeff_integral` (92): unused hypothesis in all three proofs.
- No dead `#check`/`example`s, no commented-out code; imports are minimal.
### Moral duplicates within this batch
- `integralLaurentSeries` (51–72) vs `IntegralPowerSeriesSubring` (IntegralPowerSeries.lean:150) / `HasCoeffsIn` closure lemmas (`hasCoeffsIn_zero/_one/_add/_mul/_neg`, IntegralPowerSeries.lean:71–98): the same five closure proofs for the same "coefficientwise" predicate family, one for `PowerSeries ℂ`/image-of-ℤ, one for `LaurentSeries K`/integral-over-ℤ.
- `formalCoxPolynomial_coeff_fixed` (143) and `formalCoxPolynomial_coeff_isInteger` (211) both end with the identical `congrArg … coeff n … coeff k` + `Polynomial.coeff_map` extraction.
### Generalization notes
- `integralLaurentSeries` (51) and `formalCoxPolynomial_coeff_integral` (91) hold for any `[CommRing K]` (no field or char-0 structure used); `transformedJSeries_mem_integralLaurentSeries` (74) needs only `IsIntegral.of_pow` (a `[CommRing]` + `IsDomain`-free statement in mathlib) and `hζ`.
- `formalCoxPolynomial` (24) and `formalCoxPolynomial_map` (39) need only `[DivisionRing K]`/`[CommRing K]` (inherited from `transformedJSeries`'s zpow).
- `formalCoxPolynomial_coeff_eq_int` (163) is already generic over any cyclotomic `K/ℚ`; the public theorem (211) specialises to `ℂ` and `Cox.zeta` — the ℂ-specific part is only `zetaField_isCyclotomicExtension` (202).
