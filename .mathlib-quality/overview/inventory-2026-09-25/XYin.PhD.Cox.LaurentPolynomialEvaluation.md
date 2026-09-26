# Inventory: XYin/PhD/Cox/LaurentPolynomialEvaluation.lean  (151 lines)

Generic Laurent-series infrastructure for Hasse's q-expansion principle (Cox Exercise 11.15): a bundled coefficientwise ring hom `LaurentSeries R →+* LaurentSeries S`, the substitution `R[X][Y] →+* (LaurentSeries R)[X]` of a Laurent series for the inner variable, and the "lowest coefficient of `P(J)` is `leadingCoeff P`" lemma with its injectivity corollary. Imports only `Mathlib.RingTheory.LaurentSeries`; consumed by DiagonalLaurent, SymmetricCubicLaurent, Kronecker, LevelThree, ModularPolynomial/IntegralDescent.

## Declarations

### `def Cox.laurentSeriesMapRingHom`
- **Type**: `{R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : LaurentSeries R →+* LaurentSeries S`
- **What**: Applies a ring hom `f` to every Laurent coefficient, packaged as a ring hom.
- **How**: `toFun F := F.map f` (mathlib's unbundled `HahnSeries.map`), with the four axioms discharged by mathlib's protected `HahnSeries.map_zero/map_one/map_add/map_mul` on the coerced `ZeroHom`/`MonoidWithZeroHom`/`AddMonoidHom`/`NonUnitalRingHom`.
- **Hypotheses**: `R`, `S` commutative rings (only semiring structure is actually needed).
- **Uses from project**: `[]`
- **Used by**: `laurentSeriesMapRingHom_coeff`, `polynomialEvalLaurent_map`, `bivariateSpecializeLaurent_map`, `bivariateSpecializeLaurent_map_apply`
- **Visibility**: public
- **Lines**: 22–28, body 5 lines
- **Notes**: mathlib has NO bundled `HahnSeries.mapRingHom` (grep of `Mathlib/RingTheory/HahnSeries/` and `LaurentSeries.lean`: none); this is a genuine gap and an upstream candidate. `CommRing` is stronger than needed (`Semiring` suffices for the four fields).

### `theorem Cox.laurentSeriesMapRingHom_coeff`
- **Type**: `(f : R →+* S) (F : LaurentSeries R) (k : ℤ) : (laurentSeriesMapRingHom f F).coeff k = f (F.coeff k)`
- **What**: The coefficient of the mapped series is the image of the coefficient.
- **How**: `rfl` (definitional unfolding of `HahnSeries.map`).
- **Hypotheses**: none beyond the ring structures.
- **Uses from project**: `laurentSeriesMapRingHom`
- **Used by**: unused in file (used in Kronecker.lean: `cyclotomicTransformedJSeries_map_complex/_map_mod`, `cyclotomicDescent_polynomialLaurentSeries`)
- **Visibility**: public
- **Lines**: 30–35, proof 1 line
- **Notes**: `@[simp]`. Equivalent to the `@[simps]`-generated `HahnSeries.map_coeff` (Basic.lean:143) after unfolding.

### `def Cox.bivariateSpecializeLaurent`
- **Type**: `{R : Type*} [CommRing R] (J : LaurentSeries R) : Polynomial (Polynomial R) →+* Polynomial (LaurentSeries R)`
- **What**: Substitutes the Laurent series `J` for the inner (coefficient) variable of an iterated polynomial, leaving the outer variable free.
- **How**: `Polynomial.mapRingHom (Polynomial.eval₂RingHom HahnSeries.C J)` — mathlib composition only.
- **Hypotheses**: `R` commutative ring.
- **Uses from project**: `[]`
- **Used by**: `bivariateSpecializeLaurent_map`, `bivariateSpecializeLaurent_map_apply`
- **Visibility**: public
- **Lines**: 38–42
- **Notes**: Since `HahnSeries.C = algebraMap R (LaurentSeries R)` (`HahnSeries.C_eq_algebraMap`, Multiplication.lean:928), `eval₂RingHom HahnSeries.C J` is `(Polynomial.aeval J).toRingHom`; the def is `Polynomial.mapRingHom (aeval J)`.

### `theorem Cox.polynomialEvalLaurent_map` (private)
- **Type**: `(f : R →+* S) (J : LaurentSeries R) (J' : LaurentSeries S) (hJ : laurentSeriesMapRingHom f J = J') (P : Polynomial R) : laurentSeriesMapRingHom f (P.eval₂ HahnSeries.C J) = (P.map f).eval₂ HahnSeries.C J'`
- **What**: Coefficientwise base change commutes with evaluating a polynomial at a Laurent series.
- **How**: `Polynomial.hom_eval₂` pushes the ring hom inside, `HahnSeries.map_C` (via a `DFunLike.ext` identity `hC : mapRingHom ∘ C = C ∘ f`) and `Polynomial.eval₂_map` finish.
- **Hypotheses**: `J'` is the image of `J`.
- **Uses from project**: `laurentSeriesMapRingHom`
- **Used by**: `bivariateSpecializeLaurent_map`
- **Visibility**: private
- **Lines**: 44–57, proof ≈ 8 lines
- **Notes**: none.

### `theorem Cox.bivariateSpecializeLaurent_map`
- **Type**: `(f : R →+* S) (J : LaurentSeries R) (J' : LaurentSeries S) (hJ : laurentSeriesMapRingHom f J = J') : (Polynomial.mapRingHom (laurentSeriesMapRingHom f)).comp (bivariateSpecializeLaurent J) = (bivariateSpecializeLaurent J').comp (Polynomial.mapRingHom (Polynomial.mapRingHom f))`
- **What**: The square "specialize at `J` then base-change" = "base-change then specialize at `J'`" commutes, as an equality of ring homs `R[X][Y] →+* (LaurentSeries S)[X]`.
- **How**: `Polynomial.ringHom_ext` reduces to constants (handled by `polynomialEvalLaurent_map`) and `X` (by `simp`).
- **Hypotheses**: `J'` is the image of `J`.
- **Uses from project**: `bivariateSpecializeLaurent`, `laurentSeriesMapRingHom`, `polynomialEvalLaurent_map`
- **Used by**: `bivariateSpecializeLaurent_map_apply`
- **Visibility**: public
- **Lines**: 61–78, proof ≈ 10 lines
- **Notes**: none.

### `theorem Cox.bivariateSpecializeLaurent_map_apply`
- **Type**: `(f : R →+* S) (J : LaurentSeries R) (J' : LaurentSeries S) (hJ : laurentSeriesMapRingHom f J = J') (P : Polynomial (Polynomial R)) : (bivariateSpecializeLaurent J P).map (laurentSeriesMapRingHom f) = bivariateSpecializeLaurent J' (P.map (Polynomial.mapRingHom f))`
- **What**: Pointwise form of the previous commutation.
- **How**: `DFunLike.congr_fun` of `bivariateSpecializeLaurent_map`.
- **Hypotheses**: `J'` is the image of `J`.
- **Uses from project**: `bivariateSpecializeLaurent`, `laurentSeriesMapRingHom`, `bivariateSpecializeLaurent_map`
- **Used by**: unused in file (Kronecker.lean `specializeJIntegral_map_zmod/_map_complex`; LevelThree.lean:653 `bivariateLaurentEval_map`)
- **Visibility**: public
- **Lines**: 81–90, proof 1 line
- **Notes**: none.

### `theorem Cox.laurentSeries_pow_order_of_order_neg`
- **Type**: `{K : Type*} [Field K] (J : LaurentSeries K) (w n : ℕ) (horder : J.order = -(w : ℤ)) : (J ^ n).order = -((w : ℤ) * (n : ℤ))`
- **What**: A Laurent series of order `-w` has `n`-th power of order `-wn`.
- **How**: `HahnSeries.order_pow` (Multiplication.lean:1034) then `simp; ring` to normalise `n • (-w)`.
- **Hypotheses**: `J.order = -w`.
- **Uses from project**: `[]`
- **Used by**: `polynomial_eval₂_laurentSeries_coeff`
- **Visibility**: public
- **Lines**: 93–99, proof 3 lines
- **Notes**: thin wrapper over `order_pow`; `Field K` only needs `[Semiring K] [NoZeroDivisors K]`.

### `theorem Cox.laurentSeries_pow_leadingCoeff_of_eq_one`
- **Type**: `{K : Type*} [Field K] (J : LaurentSeries K) (hleading : J.leadingCoeff = 1) (n : ℕ) : (J ^ n).leadingCoeff = 1`
- **What**: Powers of a monic (leading coefficient one) Laurent series stay monic.
- **How**: induction on `n` with `HahnSeries.leadingCoeff_one` (base) and `HahnSeries.leadingCoeff_mul` (step, Multiplication.lean:573).
- **Hypotheses**: `J.leadingCoeff = 1`.
- **Uses from project**: `[]`
- **Used by**: `polynomial_eval₂_laurentSeries_coeff`
- **Visibility**: public
- **Lines**: 103–110, proof 4 lines
- **Notes**: the general `HahnSeries.leadingCoeff_pow : (x^n).leadingCoeff = x.leadingCoeff ^ n` does not exist in mathlib (grep `leadingCoeff_pow` in `Mathlib/RingTheory/HahnSeries/`: none); PR candidate. Needs only `[Semiring K] [NoZeroDivisors K]`.

### `theorem Cox.polynomial_eval₂_laurentSeries_coeff`
- **Type**: `{K : Type*} [Field K] (J : LaurentSeries K) (w : ℕ) (hw : 0 < w) (horder : J.order = -(w : ℤ)) (hleading : J.leadingCoeff = 1) (P : Polynomial K) : (P.eval₂ (HahnSeries.C : K →+* LaurentSeries K) J).coeff (-((w : ℤ) * (P.natDegree : ℤ))) = P.leadingCoeff`
- **What**: If `J` has a pole of order `w > 0` with leading coefficient one, the coefficient of `q^(-w·deg P)` in `P(J)` is the leading coefficient of `P` (the lowest-term computation in Cox Exercise 11.15).
- **How**: `Polynomial.eval₂_eq_sum_range` + `HahnSeries.coeff_sum`, then `Finset.sum_eq_single P.natDegree`: the top term contributes `leadingCoeff P · leadingCoeff (J^deg)` via `HahnSeries.leadingCoeff_eq` and the two pow lemmas; lower terms vanish by `HahnSeries.coeff_eq_zero_of_lt_order` since `(J^n).order = -wn > -w·deg`.
- **Hypotheses**: `w > 0`, `J.order = -w`, `J.leadingCoeff = 1`.
- **Uses from project**: `laurentSeries_pow_order_of_order_neg`, `laurentSeries_pow_leadingCoeff_of_eq_one`
- **Used by**: `polynomial_eval₂_laurentSeries_injective`
- **Visibility**: public
- **Lines**: 113–136, proof ≈ 18 lines
- **Notes**: also used by DiagonalLaurent.lean:223 and ModularPolynomial/IntegralDescent.lean:69. The companion statements "`coeff k = 0` for `k < -w·deg`", "`order (P(J)) = -w·deg`", "`leadingCoeff (P(J)) = leadingCoeff P`" are NOT here — they are hand-proved at `K = ℂ` in DiagonalLaurent.lean:226–266.

### `theorem Cox.polynomial_eval₂_laurentSeries_injective`
- **Type**: `{K : Type*} [Field K] (J : LaurentSeries K) (w : ℕ) (hw : 0 < w) (horder : J.order = -(w : ℤ)) (hleading : J.leadingCoeff = 1) : Function.Injective (Polynomial.eval₂RingHom (HahnSeries.C : K →+* LaurentSeries K) J)`
- **What**: Substitution `P ↦ P(J)` is injective on `K[X]` when `J` has a genuine pole with unit leading coefficient (Hasse principle).
- **How**: `injective_iff_map_eq_zero`; if `P(J) = 0` then by `polynomial_eval₂_laurentSeries_coeff` the leading coefficient of `P` is a coefficient of `0`, so `Polynomial.leadingCoeff_eq_zero` gives `P = 0`.
- **Hypotheses**: as above.
- **Uses from project**: `polynomial_eval₂_laurentSeries_coeff`
- **Used by**: unused in file (Kronecker.lean:542 `specializeJMod_injective`)
- **Visibility**: public
- **Lines**: 139–149, proof ≈ 6 lines
- **Notes**: none.

## File Summary
- Total declarations: 10 (3 defs, 7 theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `laurentSeriesMapRingHom` (4 uses)
- Unused declarations (not used by anything in this file): `laurentSeriesMapRingHom_coeff`, `bivariateSpecializeLaurent_map_apply`, `polynomial_eval₂_laurentSeries_injective` (all used cross-file)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations

### Mathlib API candidates
- `laurentSeriesMapRingHom` (22–28): mathlib has the unbundled `HahnSeries.map` (`Mathlib/RingTheory/HahnSeries/Basic.lean:143`, `@[simps]`, any `ZeroHomClass`) and the protected lemmas `HahnSeries.map_zero` (Basic.lean:148), `HahnSeries.map_add` (Addition.lean:128), `HahnSeries.map_one` (Multiplication.lean:103), `HahnSeries.map_mul` (Multiplication.lean:406), `HahnSeries.map_C` (Multiplication.lean:823) — exactly the assembly kit used here — but NO `HahnSeries.mapRingHom` / `LaurentSeries.mapRingHom` anywhere in the pinned mathlib (grep `mapRingHom` over `Mathlib/RingTheory/HahnSeries/*.lean`, `LaurentSeries.lean`: none; `embDomainRingHom` at Multiplication.lean:899 acts on the exponent group, not coefficients). Current state: still project-defined, unchanged since July; upstream candidate `HahnSeries.mapRingHom (f : R →+* S) : R⟦Γ⟧ →+* S⟦Γ⟧` with `[Semiring R] [Semiring S]`.
- `laurentSeriesMapRingHom_coeff` (30–35) ≡ `HahnSeries.map_coeff` (simps-generated from Basic.lean:143).
- `laurentSeries_pow_order_of_order_neg` (93–99): pure `HahnSeries.order_pow` (Multiplication.lean:1034) + `nsmul` arithmetic.
- `laurentSeries_pow_leadingCoeff_of_eq_one` (103–110): no `HahnSeries.leadingCoeff_pow` in mathlib (searched `leadingCoeff_pow`, `leadingCoeff_prod`, `order_prod` in `Mathlib/RingTheory/HahnSeries/` and `LaurentSeries.lean`: none; only `Polynomial.leadingCoeff_pow'` exists). Mathlib has `HahnSeries.leadingCoeff_mul` (Multiplication.lean:573, `[NoZeroDivisors R]`) and `leadingCoeff_one` (:99). PR candidate: `HahnSeries.leadingCoeff_pow [NoZeroDivisors R] (x) (n) : (x ^ n).leadingCoeff = x.leadingCoeff ^ n` next to `order_pow`.
- `polynomial_eval₂_laurentSeries_coeff` / `_injective` (113–149): no mathlib analogue found for polynomial evaluation into `HahnSeries`/`LaurentSeries` (searched `eval₂`, `aeval`, `Polynomial` in `Mathlib/RingTheory/HahnSeries/*.lean` and `LaurentSeries.lean`: only the `RatFunc` coercion `coe_coe` at LaurentSeries.lean:377). Building blocks that exist: `HahnSeries.order_mul` (Multiplication.lean:1022), `orderTop_add_eq_left` (Addition.lean:215), `leadingCoeff_add_eq_left` (Addition.lean:234), `coeff_eq_zero_of_lt_order` (Basic.lean:394), `le_order_iff_forall` (Basic.lean:552).
- `bivariateSpecializeLaurent` (38–42): already a composition of `Polynomial.mapRingHom`/`Polynomial.eval₂RingHom`; via `HahnSeries.C_eq_algebraMap` (Multiplication.lean:928) it is `Polynomial.mapRingHom (Polynomial.aeval J : K[X] →ₐ[K] LaurentSeries K)`. Keep.

### Missing API / repeated patterns
- The "lowest coefficient" lemma has no siblings here: `polynomial_eval₂_laurentSeries_coeff_eq_zero_of_lt (hk : k < -w·deg P) : (P.eval₂ C J).coeff k = 0`, `polynomial_eval₂_laurentSeries_order (hP : P ≠ 0) : (P.eval₂ C J).order = -w·deg P`, `polynomial_eval₂_laurentSeries_leadingCoeff : (P.eval₂ C J).leadingCoeff = P.leadingCoeff`. All three are proved at `K = ℂ`, `J = laurentqExpansion m j` in DiagonalLaurent.lean:226–266 (`eval₂_laurentqExpansion_j_coeff_eq_zero_of_lt_widthM`, `eval₂_laurentqExpansion_j_leadingCoeff_widthM`) using nothing about ℂ or `j`; the vanishing bullet (128–135 here) is the same `coeff_eq_zero_of_lt_order` argument as DiagonalLaurent.lean:231–242.
- Mixed API: this file's consumers use both `F.map f` (Kronecker.lean:177, 230, 245, 321; LevelThree.lean:603, 610) and `laurentSeriesMapRingHom f F` (Kronecker.lean:498–533, 609–719; LevelThree.lean:641–662), relying on their `rfl`-equality (`exact` at Kronecker.lean:503, 521). A `@[simp] laurentSeriesMapRingHom_apply : laurentSeriesMapRingHom f F = F.map f` (or standardising on one form) would remove the `change`/defeq reliance.

### Junk candidates
- None dead. `laurentSeries_pow_order_of_order_neg` is a 3-line wrapper used twice (here and DiagonalLaurent.lean:217); acceptable.

### Moral duplicates within this batch
- `laurentSeries_pow_leadingCoeff_of_eq_one` is reused (not duplicated) by SymmetricCubicLaurent.lean:164–165; the general `leadingCoeff_pow` would subsume it and `laurentMonomial_leadingCoeff` (SymmetricCubicLaurent.lean:160–165).
- `polynomial_eval₂_laurentSeries_coeff` is instantiated verbatim twice: DiagonalLaurent.lean:219–224 (width `m`) and IntegralDescent.lean:66–70 (width 1).

### Generalization notes
- All four `[Field K]` results (93–149) use only `HahnSeries.order_pow`/`leadingCoeff_mul`/`leadingCoeff_one`/`coeff_eq_zero_of_lt_order`/`C_mul_eq_smul` and `Polynomial.leadingCoeff_eq_zero`/`injective_iff_map_eq_zero`; `[CommRing K] [IsDomain K]` (or `[CommSemiring K] [NoZeroDivisors K]` for the first three) suffices.
- `laurentSeriesMapRingHom`, `bivariateSpecializeLaurent` and their `_map` lemmas need only `[Semiring R] [Semiring S]` (`CommSemiring` for `eval₂RingHom`), not `CommRing`.
