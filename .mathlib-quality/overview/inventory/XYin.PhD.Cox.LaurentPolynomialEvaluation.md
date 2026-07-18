# XYin/PhD/Cox/LaurentPolynomialEvaluation.lean
Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/LaurentPolynomialEvaluation.lean
Project-internal imports: [] (only `Mathlib.RingTheory.LaurentSeries`)

File purpose: the lowest-term argument behind Hasse's q-expansion principle — if a Laurent series `J` has order `-w` (`w > 0`) and leading coefficient 1, the lowest coefficient of `P(J)` is the leading coefficient of `P`, hence evaluation at `J` is injective. All declarations are in namespace `Cox`.

### `def laurentSeriesMapRingHom`
- **Type**: `{R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : LaurentSeries R →+* LaurentSeries S`
- **What**: Coefficientwise application of a ring homomorphism `f : R →+* S` to Laurent series, bundled as a ring homomorphism between the Laurent series rings.
- **How**: Wraps `HahnSeries.map f` and discharges the four ring-hom axioms with the existing mathlib lemmas `HahnSeries.map_zero/map_one/map_add/map_mul` applied to the appropriate hom coercions of `f`.
- **Hypotheses**: `R`, `S` commutative rings.
- **Uses from project**: []
- **Used by**: `laurentSeriesMapRingHom_coeff`, `polynomialEvalLaurent_map`, `bivariateSpecializeLaurent_map`, `bivariateSpecializeLaurent_map_apply`
- **Visibility**: public
- **Lines**: 22–28 (definition, 7 lines)
- **Notes**: none

### `theorem laurentSeriesMapRingHom_coeff`
- **Type**: `{R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (F : LaurentSeries R) (k : ℤ) : (laurentSeriesMapRingHom f F).coeff k = f (F.coeff k)`
- **What**: The `k`-th coefficient of the mapped Laurent series is `f` applied to the `k`-th coefficient of the original series — the defining property of `laurentSeriesMapRingHom`, in simp-normal form.
- **How**: True by definitional unfolding (`rfl`), since `HahnSeries.map` acts coefficientwise.
- **Hypotheses**: `R`, `S` commutative rings.
- **Uses from project**: [`laurentSeriesMapRingHom`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 30–35 (proof: `rfl`)
- **Notes**: `@[simp]`

### `def bivariateSpecializeLaurent`
- **Type**: `{R : Type*} [CommRing R] (J : LaurentSeries R) : Polynomial (Polynomial R) →+* Polynomial (LaurentSeries R)`
- **What**: Substitutes the Laurent series `J` for the inner (coefficient) variable of a bivariate polynomial `P(X)(Y) ∈ R[Y][X]`, producing a one-variable polynomial over Laurent series. Mathematically: `Φ(X, Y) ↦ Φ(X, J)` viewed in `(LaurentSeries R)[X]`.
- **How**: Composition of `Polynomial.mapRingHom` with the evaluation hom `Polynomial.eval₂RingHom HahnSeries.C J` applied to each coefficient polynomial.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: []
- **Used by**: `bivariateSpecializeLaurent_map`, `bivariateSpecializeLaurent_map_apply`
- **Visibility**: public
- **Lines**: 38–42 (definition, 5 lines)
- **Notes**: none

### `theorem polynomialEvalLaurent_map` (private)
- **Type**: `{R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (J : LaurentSeries R) (J' : LaurentSeries S) (hJ : laurentSeriesMapRingHom f J = J') (P : Polynomial R) : laurentSeriesMapRingHom f (P.eval₂ HahnSeries.C J) = (P.map f).eval₂ HahnSeries.C J'`
- **What**: Coefficientwise base change commutes with one-variable polynomial evaluation at a Laurent series: mapping `P(J)` along `f` equals evaluating the mapped polynomial `P^f` at the mapped series `J'`.
- **How**: A `calc` chain: `Polynomial.hom_eval₂` pushes the ring hom inside the evaluation, the constant-hom compatibility `HahnSeries.map_C` (via `DFunLike.ext`) identifies the composed coefficient maps, and `Polynomial.eval₂_map` reassembles the result.
- **Hypotheses**: `J'` is the coefficientwise image of `J` under `f`.
- **Uses from project**: [`laurentSeriesMapRingHom`]
- **Used by**: `bivariateSpecializeLaurent_map`
- **Visibility**: private
- **Lines**: 44–65 (proof ~20 lines)
- **Notes**: proof >10 lines; key lemmas `Polynomial.hom_eval₂`, `HahnSeries.map_C`, `Polynomial.eval₂_map`

### `theorem bivariateSpecializeLaurent_map`
- **Type**: `{R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (J : LaurentSeries R) (J' : LaurentSeries S) (hJ : laurentSeriesMapRingHom f J = J') : (Polynomial.mapRingHom (laurentSeriesMapRingHom f)).comp (bivariateSpecializeLaurent J) = (bivariateSpecializeLaurent J').comp (Polynomial.mapRingHom (Polynomial.mapRingHom f))`
- **What**: Laurent specialization of an iterated (bivariate) polynomial commutes with coefficientwise base change along `f`, stated as an equality of ring homomorphisms `R[Y][X] →+* (LaurentSeries S)[X]`.
- **How**: `Polynomial.ringHom_ext` reduces to the generator `X` (trivial by `simp`) and constants `C P`, where the claim is exactly the private lemma `polynomialEvalLaurent_map`.
- **Hypotheses**: `J'` is the coefficientwise image of `J` under `f`.
- **Uses from project**: [`laurentSeriesMapRingHom`, `bivariateSpecializeLaurent`, `polynomialEvalLaurent_map`]
- **Used by**: `bivariateSpecializeLaurent_map_apply`
- **Visibility**: public
- **Lines**: 69–86 (proof ~10 lines)
- **Notes**: key lemma `Polynomial.ringHom_ext`

### `theorem bivariateSpecializeLaurent_map_apply`
- **Type**: `{R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (J : LaurentSeries R) (J' : LaurentSeries S) (hJ : laurentSeriesMapRingHom f J = J') (P : Polynomial (Polynomial R)) : (bivariateSpecializeLaurent J P).map (laurentSeriesMapRingHom f) = bivariateSpecializeLaurent J' (P.map (Polynomial.mapRingHom f))`
- **What**: Pointwise form of `bivariateSpecializeLaurent_map`: for each individual bivariate polynomial `P`, specializing then base-changing equals base-changing then specializing.
- **How**: Immediate by applying `DFunLike.congr_fun` to the ring-hom equality `bivariateSpecializeLaurent_map`.
- **Hypotheses**: `J'` is the coefficientwise image of `J` under `f`.
- **Uses from project**: [`laurentSeriesMapRingHom`, `bivariateSpecializeLaurent`, `bivariateSpecializeLaurent_map`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 89–98 (proof 1 line)
- **Notes**: none

### `theorem laurentSeries_pow_order_of_order_neg`
- **Type**: `{K : Type*} [Field K] (J : LaurentSeries K) (w n : ℕ) (horder : J.order = -(w : ℤ)) : (J ^ n).order = -((w : ℤ) * (n : ℤ))`
- **What**: If a Laurent series over a field has order `-w`, then its `n`-th power has order `-wn` — orders are additive under multiplication in an integral domain.
- **How**: Rewrites with the mathlib lemma `HahnSeries.order_pow` (valid over a domain), then normalizes the integer arithmetic with `simp; ring`.
- **Hypotheses**: `K` a field; `J.order = -w`.
- **Uses from project**: []
- **Used by**: `polynomial_eval₂_laurentSeries_coeff`
- **Visibility**: public
- **Lines**: 101–107 (proof 3 lines)
- **Notes**: none

### `theorem laurentSeries_pow_leadingCoeff_of_eq_one`
- **Type**: `{K : Type*} [Field K] (J : LaurentSeries K) (hleading : J.leadingCoeff = 1) (n : ℕ) : (J ^ n).leadingCoeff = 1`
- **What**: Every power of a Laurent series with leading coefficient 1 again has leading coefficient 1.
- **How**: Induction on `n`; the successor step uses multiplicativity of leading coefficients over a domain (`HahnSeries.leadingCoeff_mul`), the base case `HahnSeries.leadingCoeff_one`.
- **Hypotheses**: `K` a field; `J.leadingCoeff = 1`.
- **Uses from project**: []
- **Used by**: `polynomial_eval₂_laurentSeries_coeff`
- **Visibility**: public
- **Lines**: 111–118 (proof 5 lines)
- **Notes**: none

### `theorem polynomial_eval₂_laurentSeries_coeff`
- **Type**: `{K : Type*} [Field K] (J : LaurentSeries K) (w : ℕ) (hw : 0 < w) (horder : J.order = -(w : ℤ)) (hleading : J.leadingCoeff = 1) (P : Polynomial K) : (P.eval₂ (HahnSeries.C : K →+* LaurentSeries K) J).coeff (-((w : ℤ) * (P.natDegree : ℤ))) = P.leadingCoeff`
- **What**: The lowest-term computation: for `J` with a pole of exact order `w > 0` and leading coefficient 1, the coefficient of `q^{-w·deg P}` in `P(J)` equals the leading coefficient of `P`. This is the heart of Hasse's q-expansion principle.
- **How**: Expands `P(J)` via `Polynomial.eval₂_eq_sum_range` and isolates the top term with `Finset.sum_eq_single`: for `n < deg P` the term `c_n J^n` has order `-wn > -w·deg P` so its coefficient vanishes by `HahnSeries.coeff_eq_zero_of_lt_order` together with `laurentSeries_pow_order_of_order_neg`; the top term contributes `leadingCoeff P · leadingCoeff(J^{deg P}) = leadingCoeff P` by `laurentSeries_pow_leadingCoeff_of_eq_one` and `HahnSeries.leadingCoeff_eq`.
- **Hypotheses**: `K` a field; `w > 0`; `J.order = -w`; `J.leadingCoeff = 1`.
- **Uses from project**: [`laurentSeries_pow_order_of_order_neg`, `laurentSeries_pow_leadingCoeff_of_eq_one`]
- **Used by**: `polynomial_eval₂_laurentSeries_injective`
- **Visibility**: public
- **Lines**: 121–156 (proof 30 lines)
- **Notes**: proof is exactly 30 lines; key lemmas `Finset.sum_eq_single`, `HahnSeries.coeff_eq_zero_of_lt_order`

### `theorem polynomial_eval₂_laurentSeries_injective`
- **Type**: `{K : Type*} [Field K] (J : LaurentSeries K) (w : ℕ) (hw : 0 < w) (horder : J.order = -(w : ℤ)) (hleading : J.leadingCoeff = 1) : Function.Injective (Polynomial.eval₂RingHom (HahnSeries.C : K →+* LaurentSeries K) J)`
- **What**: Polynomial evaluation at a Laurent series with a genuine pole (order `-w`, `w > 0`) and leading coefficient 1 is injective — `J` is transcendental enough that `P(J) = Q(J)` forces `P = Q`.
- **How**: Reduces to showing `R := P - Q` with `R(J) = 0` is zero: if not, `polynomial_eval₂_laurentSeries_coeff` says the coefficient at `-w·deg R` of `R(J)` is `leadingCoeff R ≠ 0` (via `Polynomial.leadingCoeff_ne_zero`), contradicting `R(J) = 0`.
- **Hypotheses**: `K` a field; `w > 0`; `J.order = -w`; `J.leadingCoeff = 1`.
- **Uses from project**: [`polynomial_eval₂_laurentSeries_coeff`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 159–174 (proof 12 lines)
- **Notes**: none

### File Summary
- Total declarations: 10 (2 defs, 8 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): `laurentSeriesMapRingHom` (used by 4)
- Unused declarations (not used by anything in this file): `laurentSeriesMapRingHom_coeff`, `bivariateSpecializeLaurent_map_apply`, `polynomial_eval₂_laurentSeries_injective` (these are the exported API consumed downstream)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [] (longest: `polynomial_eval₂_laurentSeries_coeff` at 30 lines)
