# XYin/PhD/Cox/FormalCoxProduct.lean — project imports: `XYin.PhD.Cox.CoxMatrices` (plus mathlib `Mathlib.NumberTheory.Cyclotomic.Gal`)

### `def Cox.formalCoxPolynomial`
- **Type**: `def formalCoxPolynomial {K : Type*} [Field K] (m : ℕ+) (ζ : K) : Polynomial (LaurentSeries K) := ∏ σ : CoxMatrix m, (Polynomial.X - Polynomial.C (transformedJSeries ζ σ))`
- **What**: The formal Cox product of equation (11.13): the polynomial in `X` over Laurent series whose roots are the transformed `j`-expansions `j((aτ+b)/d)` for all Cox representatives `σ` of level `m`, with `ζ` a chosen `m`-th root of unity.
- **How**: Finite product over the fintype `CoxMatrix m` of linear factors `X − C(transformedJSeries ζ σ)`; no proof content.
- **Hypotheses**: `K` a field, `m : ℕ+`, `ζ : K` arbitrary (primitivity is assumed only in later lemmas).
- **Uses from project**: [`CoxMatrix` (XYin.PhD.Cox.CoxMatrices.Basic), `transformedJSeries` (XYin.PhD.Cox.CoxMatrices.LaurentExpansion)]
- **Used by**: `formalCoxPolynomial_map`, `formalCoxPolynomial_coeff_integral`, `formalCoxPolynomial_pow_eq`, `formalCoxPolynomial_coeff_fixed`, `formalCoxPolynomial_coeff_eq_int`, `formalCoxPolynomial_coeff_isInteger`
- **Visibility**: public
- **Lines**: 24–27
- **Notes**: none

### `lemma Cox.transformedJSeries_map`
- **Type**: `{K L : Type*} [Field K] [Field L] (φ : K →+* L) {m : ℕ+} (ζ : K) (σ : CoxMatrix m) : (transformedJSeries ζ σ).map φ = transformedJSeries (φ ζ) σ`
- **What**: Pushing a transformed `j`-series forward along a field homomorphism is the same as forming the series at the image root of unity `φ(ζ)`.
- **How**: Coefficientwise: each coefficient is either `0` or `jIntCoeff(k/a²) · ζ^(ab·(k/a²))` (by `transformedJSeries_coeff`), an integer times a `ζ`-power, and `φ` commutes with integer casts (`map_intCast`) and `zpow` (`map_zpow₀`).
- **Hypotheses**: `φ` a ring hom of fields (hence injective, though only hom properties are used).
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_coeff`, `CoxMatrix`]
- **Used by**: `formalCoxPolynomial_map`
- **Visibility**: private
- **Lines**: 29–37 (proof 7 lines)
- **Notes**: none

### `lemma Cox.formalCoxPolynomial_map`
- **Type**: `(φ : K →+* L) (m : ℕ+) (ζ : K) : (formalCoxPolynomial m ζ).map ⟨fun F ↦ F.map φ, …⟩ = formalCoxPolynomial m (φ ζ)` (the map is the ring hom `LaurentSeries K →+* LaurentSeries L` induced by `φ` via `HahnSeries.map`)
- **What**: The formal Cox product is natural in the coefficient field: mapping every Laurent-series coefficient along `φ` yields the Cox product at `φ(ζ)`.
- **How**: `Polynomial.map_prod` distributes the induced ring hom over the product of linear factors, and `transformedJSeries_map` identifies each factor; the induced hom is assembled from mathlib's `HahnSeries.map_zero/one/add/mul`.
- **Hypotheses**: `K, L` fields.
- **Uses from project**: [`formalCoxPolynomial`, `transformedJSeries_map`]
- **Used by**: `formalCoxPolynomial_coeff_fixed`, `formalCoxPolynomial_coeff_isInteger`
- **Visibility**: private
- **Lines**: 39–49 (proof 2 lines after the hom construction)
- **Notes**: none

### `def Cox.integralLaurentSeries`
- **Type**: `private def integralLaurentSeries (K : Type*) [Field K] [CharZero K] : Subring (LaurentSeries K)` with carrier `{F | ∀ k, IsIntegral ℤ (F.coeff k)}`
- **What**: The subring of Laurent series over `K` all of whose coefficients are algebraic integers.
- **How**: Closure under multiplication is the key step: `HahnSeries.coeff_mul` writes a product coefficient as a finite convolution sum over the antidiagonal, and `IsIntegral.sum`/`IsIntegral.mul` show integrality is preserved; `0`, `1`, sums, and negation are handled by `isIntegral_zero/one`, `IsIntegral.add/neg` (with `HahnSeries.coeff_one` for the unit).
- **Hypotheses**: `K` a field of characteristic zero.
- **Uses from project**: []
- **Used by**: `transformedJSeries_mem_integralLaurentSeries`, `formalCoxPolynomial_coeff_integral`
- **Visibility**: private
- **Lines**: 51–72 (construction with 5 embedded proofs, 20 lines)
- **Notes**: none

### `lemma Cox.transformedJSeries_mem_integralLaurentSeries`
- **Type**: `{K} [Field K] [CharZero K] {m : ℕ+} {ζ : K} (hζ : IsPrimitiveRoot ζ (m : ℕ)) (σ : CoxMatrix m) : transformedJSeries ζ σ ∈ integralLaurentSeries K`
- **What**: Every transformed `j`-series at a primitive `m`-th root of unity has algebraic-integer coefficients.
- **How**: Each nonzero coefficient is `jIntCoeff(k/a²) · ζ^(ab·(k/a²))` (by `transformedJSeries_coeff`); the first factor is in the image of `ℤ` (`isIntegral_algebraMap`) and the `ζ`-power is integral because its `m`-th power is `1` (`IsIntegral.of_pow` with `hζ.zpow_eq_one`), i.e., it is a root of the monic `xᵐ − 1`.
- **Hypotheses**: `ζ` a primitive `m`-th root of unity; `char K = 0`.
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_coeff`, `jIntCoeff` (XYin.PhD.Cox.CoxMatrices.LaurentExpansion), `integralLaurentSeries`, `CoxMatrix` (fields `a`, `b`)]
- **Used by**: `formalCoxPolynomial_coeff_integral`
- **Visibility**: private
- **Lines**: 74–89 (proof 14 lines)
- **Notes**: none

### `lemma Cox.formalCoxPolynomial_coeff_integral`
- **Type**: `[Field K] [CharZero K] (m : ℕ+) {ζ : K} (hζ : IsPrimitiveRoot ζ (m : ℕ)) (n : ℕ) (k : ℤ) : IsIntegral ℤ (((formalCoxPolynomial m ζ).coeff n).coeff k)`
- **What**: Every coefficient (of every Laurent coefficient) of the formal Cox product is integral over ℤ.
- **How**: Re-perform the product `∏ (X − C(Fσ))` inside the subring `integralLaurentSeries K` (each factor lies there by `transformedJSeries_mem_integralLaurentSeries`) and observe that mapping along `S.subtype` recovers `formalCoxPolynomial m ζ` via `Polynomial.map_prod`; hence each coefficient is the coercion of a subring element and inherits its integrality property.
- **Hypotheses**: `ζ` primitive `m`-th root of unity; `char K = 0`.
- **Uses from project**: [`formalCoxPolynomial`, `integralLaurentSeries`, `transformedJSeries_mem_integralLaurentSeries`, `transformedJSeries`, `CoxMatrix`]
- **Used by**: `formalCoxPolynomial_coeff_eq_int`
- **Visibility**: private
- **Lines**: 91–109 (proof 17 lines)
- **Notes**: none

### `lemma Cox.transformedJSeries_pow_eq_reindex`
- **Type**: `[Field K] {m : ℕ+} {ζ : K} (hζ : IsPrimitiveRoot ζ (m : ℕ)) (r : ℕ) (hr : Nat.Coprime r (m : ℕ)) (σ : CoxMatrix m) : transformedJSeries (ζ ^ r) σ = transformedJSeries ζ (reindex r hr σ)`
- **What**: Replacing `ζ` by `ζʳ` (the Galois twist for `r` coprime to `m`) in a transformed `j`-series equals the series at the reindexed Cox matrix, whose `b`-entry is `b·r mod d`.
- **How**: Coefficientwise, the claim reduces to `ζ^(r·ab·e) = ζ^(a·(br mod d)·e)`; the exponent difference is `a·e·(br − (br mod d)) = a·d·q·e` by the division algorithm (`Nat.mod_add_div`), which is divisible by `m = a·d` (the `determinant` field of `CoxMatrix`), so `hζ.zpow_eq_one_iff_dvd` kills it.
- **Hypotheses**: `ζ` a primitive `m`-th root of unity; `r` coprime to `m`.
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_coeff`, `reindex` (XYin.PhD.Cox.CoxMatrices.LaurentExpansion), `CoxMatrix` (fields `a`, `b`, `d`, `determinant`)]
- **Used by**: `formalCoxPolynomial_pow_eq`
- **Visibility**: private
- **Lines**: 111–151 (proof 39 lines)
- **Notes**: proof >30 lines (39); the `calc` chain implementing the divisibility bookkeeping is the bulk

### `lemma Cox.formalCoxPolynomial_pow_eq`
- **Type**: `[Field K] {m : ℕ+} {ζ : K} (hζ : IsPrimitiveRoot ζ (m : ℕ)) (r : ℕ) (hr : Nat.Coprime r (m : ℕ)) : formalCoxPolynomial m (ζ ^ r) = formalCoxPolynomial m ζ`
- **What**: The formal Cox product is invariant under replacing `ζ` by any power `ζʳ` with `r` coprime to `m` — i.e., under the Galois action on roots of unity. This is the Cox (11.13) product-invariance argument.
- **How**: Each factor at `ζʳ` equals the factor at `ζ` of the reindexed matrix (`transformedJSeries_pow_eq_reindex`), and `reindex r hr` is a bijection of `CoxMatrix m` (`reindex_bijective`), so `Function.Bijective.prod_comp` shows the two products coincide up to permutation of factors.
- **Hypotheses**: `ζ` primitive `m`-th root; `r` coprime to `m`.
- **Uses from project**: [`formalCoxPolynomial`, `transformedJSeries_pow_eq_reindex`, `reindex`, `reindex_bijective` (XYin.PhD.Cox.CoxMatrices.LaurentExpansion), `transformedJSeries`, `CoxMatrix`]
- **Used by**: `formalCoxPolynomial_coeff_fixed`
- **Visibility**: private
- **Lines**: 153–171 (proof 13 lines)
- **Notes**: none

### `lemma Cox.formalCoxPolynomial_coeff_fixed`
- **Type**: `[Field K] [Algebra ℚ K] {m : ℕ+} {ζ : K} (hζ : IsPrimitiveRoot ζ m) [IsCyclotomicExtension {(m:ℕ)} ℚ K] (n : ℕ) (k : ℤ) (φ : K ≃ₐ[ℚ] K) : φ (((formalCoxPolynomial m ζ).coeff n).coeff k) = ((formalCoxPolynomial m ζ).coeff n).coeff k`
- **What**: Every coefficient of the formal Cox product over the cyclotomic field `ℚ(ζₘ)` is fixed by every `ℚ`-automorphism — Galois invariance of the Cox product coefficients.
- **How**: By mathlib's `IsPrimitiveRoot.autToPow`/`autToPow_spec`, `φ` sends `ζ ↦ ζʳ` for some unit `r` of `ZMod m` (coprime to `m` by `ZMod.val_coe_unit_coprime`); then `formalCoxPolynomial_map` transports the polynomial along `φ` to the product at `ζʳ`, and `formalCoxPolynomial_pow_eq` identifies that with the original, so extracting the `(n,k)` coefficient gives fixedness.
- **Hypotheses**: `K/ℚ` is the `m`-th cyclotomic extension; `ζ` a primitive `m`-th root.
- **Uses from project**: [`formalCoxPolynomial`, `formalCoxPolynomial_pow_eq`, `formalCoxPolynomial_map`]
- **Used by**: `formalCoxPolynomial_coeff_eq_int`
- **Visibility**: private
- **Lines**: 173–201 (proof 22 lines)
- **Notes**: none

### `lemma Cox.formalCoxPolynomial_coeff_eq_int`
- **Type**: `[Field K] [Algebra ℚ K] {m : ℕ+} {ζ : K} (hζ : IsPrimitiveRoot ζ m) [IsCyclotomicExtension {(m:ℕ)} ℚ K] (n : ℕ) (k : ℤ) : ∃ z : ℤ, ((formalCoxPolynomial m ζ).coeff n).coeff k = (z : K)`
- **What**: Descent to ℤ: each coefficient of the formal Cox product over `ℚ(ζₘ)` is an ordinary integer.
- **How**: The coefficient is Galois-fixed (`formalCoxPolynomial_coeff_fixed`), hence lies in `ℚ` by `IsGalois.mem_range_algebraMap_iff_fixed` (using `IsCyclotomicExtension.isGalois` and finite-dimensionality); it is also integral over ℤ (`formalCoxPolynomial_coeff_integral`), and ℤ is integrally closed in ℚ (`IsIntegrallyClosed.algebraMap_eq_of_integral`), so it is an integer.
- **Hypotheses**: `K/ℚ` the `m`-th cyclotomic extension; `ζ` primitive.
- **Uses from project**: [`formalCoxPolynomial`, `formalCoxPolynomial_coeff_integral`, `formalCoxPolynomial_coeff_fixed`]
- **Used by**: `formalCoxPolynomial_coeff_isInteger`
- **Visibility**: private
- **Lines**: 203–229 (proof 21 lines)
- **Notes**: `letI` instances for `CharZero`, `FiniteDimensional`, `IsGalois` synthesized inline

### `abbrev Cox.zetaField`
- **Type**: `private abbrev zetaField (m : ℕ+) := IntermediateField.adjoin ℚ ({zeta m} : Set ℂ)`
- **What**: The concrete cyclotomic subfield `ℚ(ζₘ) ⊆ ℂ` generated by the project's standard root of unity `ζₘ = e^{2πi/m}`.
- **How**: `IntermediateField.adjoin` of the singleton; no proof.
- **Hypotheses**: none.
- **Uses from project**: [`zeta` (XYin.PhD.Cox.CoxMatrices.LaurentExpansion)]
- **Used by**: `zetaFieldRoot`, `zetaField_isCyclotomicExtension`, `formalCoxPolynomial_coeff_isInteger`
- **Visibility**: private
- **Lines**: 231–232
- **Notes**: none

### `def Cox.zetaFieldRoot`
- **Type**: `private def zetaFieldRoot (m : ℕ+) : zetaField m := ⟨zeta m, IntermediateField.subset_adjoin ℚ {zeta m} (by simp)⟩`
- **What**: The root of unity `ζₘ` viewed as an element of its own adjoined field `ℚ(ζₘ)`.
- **How**: Subtype packaging with membership from `IntermediateField.subset_adjoin`.
- **Hypotheses**: none.
- **Uses from project**: [`zetaField`, `zeta`]
- **Used by**: `zetaFieldRoot_isPrimitiveRoot`, `formalCoxPolynomial_coeff_isInteger`
- **Visibility**: private
- **Lines**: 234–235
- **Notes**: none

### `lemma Cox.zetaFieldRoot_isPrimitiveRoot`
- **Type**: `private lemma zetaFieldRoot_isPrimitiveRoot (m : ℕ+) : IsPrimitiveRoot (zetaFieldRoot m) (m : ℕ)`
- **What**: The element `ζₘ ∈ ℚ(ζₘ)` is a primitive `m`-th root of unity in the subfield.
- **How**: Primitivity descends along the subfield inclusion by mathlib's `IsPrimitiveRoot.coe_submonoidClass_iff`, from the ambient fact `zeta_isPrimitiveRoot`.
- **Hypotheses**: none.
- **Uses from project**: [`zetaFieldRoot`, `zeta_isPrimitiveRoot` (XYin.PhD.Cox.CoxMatrices.LaurentExpansion)]
- **Used by**: `formalCoxPolynomial_coeff_isInteger`
- **Visibility**: private
- **Lines**: 237–240 (proof 2 lines)
- **Notes**: none

### `instance Cox.zetaField_isCyclotomicExtension`
- **Type**: `private noncomputable instance zetaField_isCyclotomicExtension (m : ℕ+) : IsCyclotomicExtension {(m : ℕ)} ℚ (zetaField m)`
- **What**: The subfield `ℚ(ζₘ) ⊆ ℂ` is an `m`-th cyclotomic extension of ℚ, so the Galois machinery of the earlier lemmas applies to it.
- **How**: Rewrites the intermediate field as a subalgebra via `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic` (using that `ζₘ` is integral, hence algebraic, over ℚ by `IsPrimitiveRoot.isIntegral`), then applies mathlib's `IsPrimitiveRoot.adjoin_isCyclotomicExtension`.
- **Hypotheses**: none.
- **Uses from project**: [`zetaField`, `zeta`, `zeta_isPrimitiveRoot`]
- **Used by**: `formalCoxPolynomial_coeff_isInteger` (as an instance, found by typeclass search)
- **Visibility**: private
- **Lines**: 242–248 (proof 5 lines)
- **Notes**: noncomputable instance

### `theorem Cox.formalCoxPolynomial_coeff_isInteger`
- **Type**: `(m : ℕ+) (n : ℕ) (k : ℤ) : ∃ z : ℤ, ((formalCoxPolynomial m (zeta m)).coeff n).coeff k = (z : ℂ)`
- **What**: The file's main theorem: every coefficient of the formal Cox product over ℂ at `ζₘ = e^{2πi/m}` is an ordinary integer. This is the integrality half of Cox equation (11.13), feeding the modular-polynomial integrality descent.
- **How**: Runs the abstract descent `formalCoxPolynomial_coeff_eq_int` inside the concrete cyclotomic subfield `ℚ(ζₘ)` (with `zetaFieldRoot_isPrimitiveRoot` and the `IsCyclotomicExtension` instance), then transports the result to ℂ along the inclusion `ι : ℚ(ζₘ) →+* ℂ` using naturality `formalCoxPolynomial_map` and `HahnSeries.map_coeff`.
- **Hypotheses**: none — fully unconditional in `m, n, k`.
- **Uses from project**: [`formalCoxPolynomial`, `formalCoxPolynomial_coeff_eq_int`, `formalCoxPolynomial_map`, `zetaField`, `zetaFieldRoot`, `zetaFieldRoot_isPrimitiveRoot`, `zetaField_isCyclotomicExtension` (instance), `zeta`]
- **Used by**: unused in file (terminal result; consumed by XYin.PhD.Cox.ModularPolynomial.IntegralDescent)
- **Visibility**: public
- **Lines**: 250–270 (proof 17 lines)
- **Notes**: none

### File Summary
- Total declarations: 15 (5 defs [incl. 1 abbrev, 1 Subring def], 9 lemmas/theorems, 1 instance, 0 tactic/meta decls)
- Key API (used by 3+ others): `formalCoxPolynomial` (6 users), `zetaField` (3 users), `transformedJSeries` chain (external import used throughout)
- Unused declarations (not used by anything in this file): `formalCoxPolynomial_coeff_isInteger` (terminal result)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [`transformedJSeries_pow_eq_reindex` (39 proof lines)]
