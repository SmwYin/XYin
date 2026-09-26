# Inventory: XYin/PhD/qExpansion_tactic/link.lean  (408 lines)

Soundness of the integer coefficient engine in `Qj.lean`: bridging lemmas show that every `foldl`/`push`/`getD` array operation computes the corresponding `PowerSeries ℤ` coefficient (convolution ↔ `coeff_mul`, inversion loop ↔ `invOfUnit`, divisor search ↔ `ArithmeticFunction.sigma`), and the main theorems `Delta_qexpansion_link`, `qj_qexpansion_link` identify `Delta_qexpansion`/`qj_qexpansion` with the analytic q-expansions of Δ and q·j after the base change ℤ → ℂ (`PowerSeries.mapAlgHom (Algebra.ofId ℤ ℂ)`). Coefficientwise corollaries are consumed by `jFunction/qexp_coeffs.lean` and `Cox/LevelThree.lean`. All declarations live in the ROOT namespace.

## Declarations

### `lemma foldl_range_add_eq_sum`
- **Type**: `(f : ℕ → ℤ) (n : ℕ) : List.foldl (fun acc i => acc + f i) 0 (List.range n) = ∑ i ∈ Finset.range n, f i`
- **What**: A left fold of additions over `range n` is the finite sum.
- **How**: Induction on n with `List.range_succ`, `List.foldl_concat`, `Finset.sum_range_succ`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `convArrayCoeff_eq_coeff_mul` (L73), `foldl_sigma_search_eq_sum` (L116), `inverseOnePlusCoeffsUpTo_toList` (L309)
- **Visibility**: public (root namespace)
- **Lines**: 30–35, body 4 lines
- **Notes**: No docstring. Holds for any `AddCommMonoid`. No single mathlib lemma; composable from core `List.sum_eq_foldl` (`Init/Data/List/Lemmas.lean:2782`) + `List.foldl_map` (:2662) + `Finset.sum_eq_multiset_sum` (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:331`) + `Finset.range_val` (`Mathlib/Data/Finset/Range.lean:57`) + `Multiset.coe_range` (`Mathlib/Data/Multiset/Range.lean:26`) + `Multiset.sum_coe` — the 4-line induction is shorter. Becomes unnecessary if `Qj.lean` sums are written as `Finset.sum` (see Qj inventory).

### `lemma foldl_push_toList`
- **Type**: `(g : ℕ → ℤ) (m : ℕ) : ((List.range m).foldl (fun acc j => acc.push (g j)) #[]).toList = (List.range m).map g`
- **What**: A `push`-tabulation over `range m` has underlying list `map g (range m)`.
- **How**: Induction with `List.range_succ`, `List.foldl_concat`, `Array.toList_push`, `List.map_append`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `foldl_push_getD` (L53)
- **Visibility**: public
- **Lines**: 37–46, body 5 lines
- **Notes**: EXACTLY core `Array.foldl_toList_eq_map` (`Init/Data/Array/Lemmas.lean:4389`) with `acc := #[]` — VERIFIED (`simpa using Array.foldl_toList_eq_map` closes it). Holds for any `α`.

### `lemma foldl_push_getD`
- **Type**: `(g : ℕ → ℤ) (m i : ℕ) (hi : i < m) : ((List.range m).foldl (fun acc j => acc.push (g j)) #[]).getD i 0 = g i`
- **What**: Reading entry i < m of a tabulated array gives g i.
- **How**: Rewrite the array as `((range m).map g).toArray` via `foldl_push_toList` + `Array.toArray_toList`, then `Array.getD_eq_getD_getElem?`, `List.getElem?_toArray`, `List.getElem?_map`, `List.getElem?_range`.
- **Hypotheses**: i < m
- **Uses from project**: `foldl_push_toList`
- **Used by**: `coeffArray_getD` (L61), `convArrayUpTo_getD` (L66), `deltaCoeffsArrayUpTo_getD` (L182), `deltaOverQArrayUpTo_getD` (L329)
- **Visibility**: public
- **Lines**: 48–56, body 6 lines
- **Notes**: Key API. Disappears if tabulations become `Array.ofFn` (then `simp [Array.getD_eq_getD_getElem?, hi]` suffices — VERIFIED).

### `lemma coeffArray_getD`
- **Type**: `(f : ℕ → ℤ) (n i : ℕ) (hi : i ≤ n) : (coeffArray f n).getD i 0 = f i`
- **What**: `coeffArray` tabulates f on 0..n.
- **How**: `unfold coeffArray; exact foldl_push_getD … (by omega)`.
- **Hypotheses**: i ≤ n
- **Uses from project**: `coeffArray`, `foldl_push_getD`
- **Used by**: `convArrayUpTo_self_coeff` (L94), `convArrayUpTo_cube_coeff` (L105)
- **Visibility**: public
- **Lines**: 58–61, body 2 lines
- **Notes**: no docstring.

### `lemma convArrayUpTo_getD`
- **Type**: `(A B : Array ℤ) (n i : ℕ) (hi : i ≤ n) : (convArrayUpTo A B n).getD i 0 = convArrayCoeff A B i`
- **What**: The convolution table reads off the convolution coefficient.
- **How**: `unfold; exact foldl_push_getD`.
- **Hypotheses**: i ≤ n
- **Uses from project**: `convArrayUpTo`, `convArrayCoeff`, `foldl_push_getD`
- **Used by**: `convArrayUpTo_self_coeff` (L92), `convArrayUpTo_cube_coeff` (L102), `qjCoeffInt_eq` (L379)
- **Visibility**: public
- **Lines**: 63–66, body 2 lines
- **Notes**: same skeleton as `coeffArray_getD`.

### `lemma convArrayCoeff_eq_coeff_mul`
- **Type**: `(A B : Array ℤ) (α β : ℕ → ℤ) (m i : ℕ) (hA : ∀ j ≤ m, A.getD j 0 = α j) (hB : ∀ j ≤ m, B.getD j 0 = β j) (hi : i ≤ m) : convArrayCoeff A B i = (PowerSeries.mk α * PowerSeries.mk β).coeff i`
- **What**: Array convolution of tables agreeing with α, β up to m is the Cauchy-product coefficient of `mk α * mk β`.
- **How**: `foldl_range_add_eq_sum`, `PowerSeries.coeff_mul`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, then `Finset.sum_congr` with `hA`, `hB`, `coeff_mk`.
- **Hypotheses**: tables agree with α, β on 0..m; i ≤ m
- **Uses from project**: `convArrayCoeff`, `foldl_range_add_eq_sum`
- **Used by**: `convArrayUpTo_self_coeff` (L93), `convArrayUpTo_cube_coeff` (L103), `qjCoeffInt_eq` (L380)
- **Visibility**: public
- **Lines**: 68–79, body 7 lines
- **Notes**: Key API. Generic over any `[Semiring R]`.

### `lemma mk_coeff_self`
- **Type**: `(F : PowerSeries ℤ) : (PowerSeries.mk fun j => F.coeff j) = F`
- **What**: `mk ∘ coeff` is the identity on power series.
- **How**: `ext; coeff_mk`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `convArrayUpTo_cube_coeff` (L106), `qjCoeffInt_eq` (L381)
- **Visibility**: public
- **Lines**: 81–85, body 2 lines
- **Notes**: One-liner: `PowerSeries.ext fun _ => PowerSeries.coeff_mk _ _` (VERIFIED). Mathlib has no named `mk_coeff` (grep `Mathlib/RingTheory/PowerSeries/Basic.lean`: only `coeff_mk`:112, `ext`:91). Generic over `[Semiring R]`. Root-namespace name `mk_coeff_self` is a pollution risk.

### `lemma convArrayUpTo_self_coeff`
- **Type**: `(f : ℕ → ℤ) (N i : ℕ) (hi : i ≤ N) : (convArrayUpTo (coeffArray f N) (coeffArray f N) N).getD i 0 = ((PowerSeries.mk f) ^ 2).coeff i`
- **What**: The self-convolution table computes the square.
- **How**: `convArrayUpTo_getD` + `convArrayCoeff_eq_coeff_mul` with `coeffArray_getD` twice, `pow_two`.
- **Hypotheses**: i ≤ N
- **Uses from project**: `convArrayUpTo`, `coeffArray`, `convArrayUpTo_getD`, `convArrayCoeff_eq_coeff_mul`, `coeffArray_getD`
- **Used by**: `convArrayUpTo_cube_coeff` (L104), `deltaCoeffsArrayUpTo_getD` (L183)
- **Visibility**: public
- **Lines**: 87–95, body 4 lines
- **Notes**: —

### `lemma convArrayUpTo_cube_coeff`
- **Type**: `(f : ℕ → ℤ) (N i : ℕ) (hi : i ≤ N) : (convArrayUpTo (convArrayUpTo (coeffArray f N) (coeffArray f N) N) (coeffArray f N) N).getD i 0 = ((PowerSeries.mk f) ^ 3).coeff i`
- **What**: The iterated convolution table computes the cube.
- **How**: As for the square, with `convArrayUpTo_self_coeff` supplying `hA`, then `mk_coeff_self`, `← pow_succ`.
- **Hypotheses**: i ≤ N
- **Uses from project**: `convArrayUpTo`, `coeffArray`, `convArrayUpTo_getD`, `convArrayCoeff_eq_coeff_mul`, `convArrayUpTo_self_coeff`, `coeffArray_getD`, `mk_coeff_self`
- **Used by**: `deltaCoeffsArrayUpTo_getD` (L182), `qjCoeffInt_eq` (L384)
- **Visibility**: public
- **Lines**: 97–106, body 5 lines
- **Notes**: Same skeleton as `_self_coeff`; a general `convArrayUpTo_pow_coeff (k)` by induction would subsume both.

### `lemma foldl_sigma_search_eq_sum`
- **Type**: `(k m n : ℕ) : List.foldl (fun acc i => let d := i+1; if m % d = 0 then acc + (d:ℤ)^k else acc) 0 (List.range n) = ∑ i ∈ Finset.range n, if m % (i+1) = 0 then ((i+1 : ℕ) : ℤ)^k else 0`
- **What**: The divisor-search fold is a conditional finite sum.
- **How**: `foldl_range_add_eq_sum` on the `ite` summand, `add_ite`/`add_zero`.
- **Hypotheses**: none
- **Uses from project**: `foldl_range_add_eq_sum`
- **Used by**: `sigmaPow_eq_sigma` (L120)
- **Visibility**: public
- **Lines**: 108–116, body 2 lines
- **Notes**: Exists only because `sigmaPow` is hand-rolled; deletable with it.

### `lemma sigmaPow_eq_sigma`
- **Type**: `(k n : ℕ) : sigmaPow k n = (ArithmeticFunction.sigma k n : ℤ)`
- **What**: The hand-rolled divisor power sum is mathlib's σ_k.
- **How**: `foldl_sigma_search_eq_sum`, `ArithmeticFunction.sigma_apply`, shift the range by `Finset.sum_range_succ'`, convert `m % d = 0` to `d ∣ n`, `Finset.sum_filter`, `Nat.filter_dvd_eq_divisors`, `norm_cast`.
- **Hypotheses**: none
- **Uses from project**: `sigmaPow`, `foldl_sigma_search_eq_sum`
- **Used by**: `e4CoeffInt_eq_integralE4_coeff` (L137), `e6CoeffInt_eq_integralE6_coeff` (L145)
- **Visibility**: public
- **Lines**: 118–129, body 11 lines
- **Notes**: Uses `Nat.filter_dvd_eq_divisors` (`Mathlib/NumberTheory/Divisors.lean:80`), `ArithmeticFunction.sigma_apply` (`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:151`). Deletable if `sigmaPow := (σ k n : ℤ)`.

### `lemma e4CoeffInt_eq_integralE4_coeff`
- **Type**: `(n : ℕ) : e4CoeffInt n = integralE4.coeff n`
- **What**: The computed E₄ coefficient is the coefficient of the project's integral E₄ series.
- **How**: case n = 0 via `integralE4_coeff_zero`; else `integralE4_coeff_of_pos` and `sigmaPow_eq_sigma`.
- **Hypotheses**: none
- **Uses from project**: `e4CoeffInt`, `integralE4`, `integralE4_coeff_zero`, `integralE4_coeff_of_pos` (Deltaqexpansions.lean:70/114/128), `sigmaPow_eq_sigma`
- **Used by**: `E4_int_series_eq` (L150)
- **Visibility**: public
- **Lines**: 131–137, body 6 lines
- **Notes**: no docstring.

### `lemma e6CoeffInt_eq_integralE6_coeff`
- **Type**: `(n : ℕ) : e6CoeffInt n = integralE6.coeff n`
- **What**: Same for E₆.
- **How**: Same skeleton + `ring` for the sign.
- **Hypotheses**: none
- **Uses from project**: `e6CoeffInt`, `integralE6`, `integralE6_coeff_zero`, `integralE6_coeff_of_pos` (Deltaqexpansions.lean:73/118/134), `sigmaPow_eq_sigma`
- **Used by**: `E6_int_series_eq` (L154)
- **Visibility**: public
- **Lines**: 139–146, body 7 lines
- **Notes**: moral duplicate of the E₄ version.

### `lemma E4_int_series_eq`
- **Type**: `PowerSeries.mk e4CoeffInt = integralE4`
- **What**: Series-level form of the previous lemma.
- **How**: `ext; coeff_mk; e4CoeffInt_eq_integralE4_coeff`.
- **Hypotheses**: none
- **Uses from project**: `e4CoeffInt`, `integralE4`, `e4CoeffInt_eq_integralE4_coeff`
- **Used by**: `E4_int_link` (L158), `Delta_qexpansion_link` (L212)
- **Visibility**: public
- **Lines**: 148–150, body 2 lines
- **Notes**: —

### `lemma E6_int_series_eq`
- **Type**: `PowerSeries.mk e6CoeffInt = integralE6`
- **What**: Same for E₆.
- **How**: same.
- **Hypotheses**: none
- **Uses from project**: `e6CoeffInt`, `integralE6`, `e6CoeffInt_eq_integralE6_coeff`
- **Used by**: `E6_int_link` (L164), `Delta_qexpansion_link` (L212)
- **Visibility**: public
- **Lines**: 152–154, body 2 lines
- **Notes**: —

### `lemma E4_int_link`
- **Type**: `mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk e4CoeffInt) = qExpansion 1 E4`
- **What**: The computed E₄ series base-changed to ℂ is the analytic q-expansion of E₄.
- **How**: `E4_int_series_eq` then `coeTo_of_toIntegralPowerSeries E4_isIntegralPowerSeries` unfolded through `integralE4`, `coeToComplexPowerSeries.ringHom`, `powerSeriesMapAlgHom`.
- **Hypotheses**: none
- **Uses from project**: `e4CoeffInt`, `E4` (abbrev of `E₄`, Deltaqexpansions.lean:36), `E4_int_series_eq`, `integralE4`, `coeToComplexPowerSeries.ringHom`, `powerSeriesMapAlgHom` (IntegralPowerSeries.lean:107/33), `coeTo_of_toIntegralPowerSeries` (IntegralPowerSeries.lean:167), `E4_isIntegralPowerSeries` (Deltaqexpansions.lean:54)
- **Used by**: `qj_qexpansion_link` (L402)
- **Visibility**: public
- **Lines**: 156–160, body 3 lines
- **Notes**: The `simpa [integralE*, coeToComplexPowerSeries.ringHom, powerSeriesMapAlgHom] using coeTo_of_toIntegralPowerSeries …` idiom recurs at L165–166 and L371–372.

### `lemma E6_int_link`
- **Type**: `mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk e6CoeffInt) = qExpansion 1 E6`
- **What**: Same for E₆.
- **How**: same idiom.
- **Hypotheses**: none
- **Uses from project**: `e6CoeffInt`, `E6`, `E6_int_series_eq`, `integralE6`, `coeToComplexPowerSeries.ringHom`, `powerSeriesMapAlgHom`, `coeTo_of_toIntegralPowerSeries`, `E6_isIntegralPowerSeries` (Deltaqexpansions.lean:62)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 162–166, body 3 lines
- **Notes**: UNUSED anywhere in the project (grep-verified). Junk candidate (kept for symmetry only).

### `lemma int_cast_div_eq_inv_mul_complex`
- **Type**: `{z : ℤ} (hz : Int.ModEq 1728 z 0) : ((z / 1728 : ℤ) : ℂ) = (1/1728 : ℂ) * (z : ℂ)`
- **What**: Casting an exact integer quotient by 1728 into ℂ.
- **How**: `Int.cast_div_charZero` with `Int.modEq_zero_iff_dvd`, then `push_cast; ring`.
- **Hypotheses**: 1728 ∣ z (phrased as `z ≡ 0 [ZMOD 1728]`)
- **Uses from project**: []
- **Used by**: `Delta_qexpansion_link` (L216)
- **Visibility**: public
- **Lines**: 168–174, body 3 lines
- **Notes**: One-line wrapper around mathlib `Int.cast_div_charZero` (`Mathlib/Data/Int/CharZero.lean:27`) + `div_eq_inv_mul`; the hypothesis should be `1728 ∣ z` (`Int.modEq_zero_iff_dvd`, `Mathlib/Data/Int/ModEq.lean:99`). Holds for any `[DivisionRing k] [CharZero k]` and any nonzero divisor, not just ℂ and 1728.

### `lemma deltaCoeffsArrayUpTo_getD`
- **Type**: `(top k : ℕ) (hk : k ≤ top) : (deltaCoeffsArrayUpTo top).getD k 0 = ((mk e4CoeffInt ^ 3 - mk e6CoeffInt ^ 2).coeff k) / 1728`
- **What**: Entry k of the Δ table is the k-th coefficient of (E₄³ − E₆²)/1728 (integer division), independent of table size.
- **How**: `foldl_push_getD`, `convArrayUpTo_cube_coeff`, `convArrayUpTo_self_coeff`, `map_sub`.
- **Hypotheses**: k ≤ top
- **Uses from project**: `deltaCoeffsArrayUpTo`, `e4CoeffInt`, `e6CoeffInt`, `foldl_push_getD`, `convArrayUpTo_cube_coeff`, `convArrayUpTo_self_coeff`
- **Used by**: `deltaCoeffInt_eq` (L190), `delta_array_getD` (L196)
- **Visibility**: public
- **Lines**: 176–183, body 3 lines
- **Notes**: —

### `lemma deltaCoeffInt_eq`
- **Type**: `(n : ℕ) : deltaCoeffInt n = ((mk e4CoeffInt ^ 3 - mk e6CoeffInt ^ 2).coeff n) / 1728`
- **What**: `deltaCoeffInt` is the formal (E₄³ − E₆²)/1728 coefficient.
- **How**: `deltaCoeffsArrayUpTo_getD n n le_rfl`.
- **Hypotheses**: none
- **Uses from project**: `deltaCoeffInt`, `deltaCoeffsArrayUpTo_getD`, `e4CoeffInt`, `e6CoeffInt`
- **Used by**: `delta_array_getD` (L196), `Delta_qexpansion_link` (L212)
- **Visibility**: public
- **Lines**: 185–190, body 1 line
- **Notes**: —

### `lemma delta_array_getD`
- **Type**: `(top k : ℕ) (hk : k ≤ top) : (deltaCoeffsArrayUpTo top).getD k 0 = deltaCoeffInt k`
- **What**: Table-size stability of Δ entries.
- **How**: the two previous lemmas.
- **Hypotheses**: k ≤ top
- **Uses from project**: `deltaCoeffsArrayUpTo`, `deltaCoeffInt`, `deltaCoeffsArrayUpTo_getD`, `deltaCoeffInt_eq`
- **Used by**: `deltaOverQArrayUpTo_getD` (L329)
- **Visibility**: public
- **Lines**: 192–196, body 1 line
- **Notes**: Naming inconsistent with `deltaCoeffsArrayUpTo_getD` (same LHS).

### `lemma eisenstein_difference_coeff_cast`
- **Type**: `(n : ℕ) : (((integralE4 ^ 3 - integralE6 ^ 2).coeff n : ℤ) : ℂ) = (qExpansion 1 (⇑E4 ^ 3 - ⇑E6 ^ 2)).coeff n`
- **What**: Cast of the integral E₄³ − E₆² coefficient is the analytic coefficient.
- **How**: `congrArg (coeff n)` of `map_integralE4_pow_three_sub_integralE6_pow_two`, `change` to `PowerSeries.map`, `PowerSeries.coeff_map`.
- **Hypotheses**: none
- **Uses from project**: `integralE4`, `integralE6`, `E4`, `E6`, `map_integralE4_pow_three_sub_integralE6_pow_two` (Deltaqexpansions.lean:228)
- **Used by**: `Delta_qexpansion_link` (L218)
- **Visibility**: public
- **Lines**: 198–206, body 4 lines
- **Notes**: The "congrArg coeff / change to map / coeff_map" idiom recurs at L228–230 and L235–239.

### `theorem Delta_qexpansion_link`
- **Type**: `mapAlgHom (Algebra.ofId ℤ ℂ) Delta_qexpansion = qExpansion 1 Delta`
- **What**: MAIN: the array-computed τ-series, base-changed to ℂ, is the analytic q-expansion of Δ.
- **How**: coefficientwise; `deltaCoeffInt_eq`, `E4/E6_int_series_eq`, `Delta_qExpansion_eq_smul_eisenstein_difference` (Δ = (1/1728)(E₄³ − E₆²) at the q-expansion level), then `int_cast_div_eq_inv_mul_complex` with `eisenstein_difference_coeff_modEq_zero` and `eisenstein_difference_coeff_cast`.
- **Hypotheses**: none
- **Uses from project**: `Delta_qexpansion`, `Delta` (Delta.lean:170), `Delta_qexpansion_coeff_eq`, `deltaCoeffInt_eq`, `E4_int_series_eq`, `E6_int_series_eq`, `Delta_qExpansion_eq_smul_eisenstein_difference` (Deltaqexpansions.lean:263), `int_cast_div_eq_inv_mul_complex`, `eisenstein_difference_coeff_modEq_zero` (Deltaqexpansions.lean:258), `eisenstein_difference_coeff_cast`, `integralE4`, `integralE6`, `E4`, `E6`
- **Used by**: `Delta_qxp_coeff_link` (L222), `deltaCoeffInt_cast` (L228)
- **Visibility**: public
- **Lines**: 208–218, body 9 lines
- **Notes**: no docstring on a main theorem.

### `theorem Delta_qxp_coeff_link`
- **Type**: `(n : ℕ) : (qExpansion 1 Delta).coeff n = Delta_qexpansion.coeff n` (RHS cast ℤ→ℂ)
- **What**: Coefficientwise form of the link.
- **How**: `congrArg (coeff n)`.
- **Hypotheses**: none
- **Uses from project**: `Delta`, `Delta_qexpansion`, `Delta_qexpansion_link`
- **Used by**: unused in file; consumed by `qexp_coeffs.lean:61–76`
- **Visibility**: public
- **Lines**: 220–222, body 1 line
- **Notes**: "qxp" abbreviation inconsistent with "qexp" everywhere else.

### `lemma deltaCoeffInt_cast`
- **Type**: `(n : ℕ) : ((deltaCoeffInt n : ℤ) : ℂ) = (qExpansion 1 Delta).coeff n`
- **What**: The array-computed τ(n), cast to ℂ, is the analytic coefficient.
- **How**: `congrArg (coeff n) Delta_qexpansion_link`, `change`, `Delta_qexpansion_coeff_eq`.
- **Hypotheses**: none
- **Uses from project**: `deltaCoeffInt`, `Delta`, `Delta_qexpansion_link`, `Delta_qexpansion_coeff_eq`
- **Used by**: `ramanujanTau_link` (L241), `deltaOverQ_qexpansion_link` (L253), `deltaOverQCoeffInt_zero` (L257)
- **Visibility**: public
- **Lines**: 224–230, body 3 lines
- **Notes**: Key API. Is `(Delta_qxp_coeff_link n).symm` after `rw [Delta_qexpansion_coeff_eq]` — moral duplicate of `Delta_qxp_coeff_link`.

### `theorem ramanujanTau_link`
- **Type**: `(n : ℕ) : ramanujanTau n = Delta_qexpansion.coeff n`
- **What**: The project's `ramanujanTau` (coefficients of `integralDelta`) equals the computed series coefficient.
- **How**: Both sides cast to ℂ equal `(qExpansion 1 Delta).coeff n`: `coeTo_of_toIntegralPowerSeries Delta_isIntegralPowerSeries` for the LHS, `deltaCoeffInt_cast` for the RHS; `exact_mod_cast`.
- **Hypotheses**: none
- **Uses from project**: `ramanujanTau`, `integralDelta`, `Delta_isIntegralPowerSeries` (Deltaqexpansions.lean:298/295/286), `coeTo_of_toIntegralPowerSeries`, `Delta`, `Delta_qexpansion`, `Delta_qexpansion_coeff_eq`, `deltaCoeffInt_cast`
- **Used by**: unused in file; consumed by `qexp_coeffs.lean:31–41`
- **Visibility**: public
- **Lines**: 232–241, body 9 lines
- **Notes**: no docstring; the inner `h1` (L234–239) is the third copy of the congrArg/coeff_map idiom.

### `lemma deltaOverQ_qexpansion_link`
- **Type**: `mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk deltaOverQCoeffInt) = qExpansion 1 deltaOverQ`
- **What**: The shifted τ-series is the q-expansion of Δ/q.
- **How**: `qExpansion_ext` transfers to `deltaShiftedQSeries` via `deltaShiftedQSeries_eq_deltaOverQ`; then `deltaCoeffInt_cast (n+1)` and `deltaShiftedQSeries_qExpansion_coeff`.
- **Hypotheses**: none
- **Uses from project**: `deltaOverQCoeffInt`, `deltaOverQ`, `deltaShiftedQSeries`, `deltaShiftedQSeries_eq_deltaOverQ`, `deltaShiftedQSeries_qExpansion_coeff` (jfunction.lean:81/105/132/198), `qExpansion_ext` (Modularforms/qExpansion_lems.lean:75), `deltaCoeffInt_cast`
- **Used by**: `qOverDelta_qexpansion_link` (L364, L369, L370)
- **Visibility**: public
- **Lines**: 243–253, body 8 lines
- **Notes**: no docstring.

### `lemma deltaOverQCoeffInt_zero`
- **Type**: `deltaOverQCoeffInt 0 = 1`
- **What**: Δ/q has constant term τ(1) = 1.
- **How**: Cast to ℂ, `deltaCoeffInt_cast 1` with `Delta_q_one_term`, `exact_mod_cast`.
- **Hypotheses**: none
- **Uses from project**: `deltaOverQCoeffInt`, `Delta_q_one_term` (Modularforms/Eisenstein.lean:374), `deltaCoeffInt_cast`
- **Used by**: `qoverDelta_mul_eq_one` (L358), `qOverDelta_qexpansion_link` (L367)
- **Visibility**: public
- **Lines**: 255–258, body 3 lines
- **Notes**: Could be `rfl`/`decide` (kernel evaluates `deltaCoeffInt 1 = 1`, as done in `qexp_coeffs.lean:31`) instead of going through analysis.

### `lemma coeff_invOfUnit_one_succ`
- **Type**: `{R} [Ring R] (φ : R⟦X⟧) (m : ℕ) : (φ.invOfUnit 1).coeff (m+1) = -∑ i ∈ range (m+1), φ.coeff (i+1) * (φ.invOfUnit 1).coeff (m-i)`
- **What**: The `invOfUnit` recursion at a successor index, in range-sum form.
- **How**: `PowerSeries.coeff_invOfUnit`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, `Finset.sum_range_succ'`, simp with `Nat.succ_sub_succ_eq_sub`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `inverseOnePlusCoeffsUpTo_toList` (L309)
- **Visibility**: public
- **Lines**: 260–269, body 5 lines
- **Notes**: Already generic in `R`; clean specialization of mathlib `coeff_invOfUnit` (`Mathlib/RingTheory/PowerSeries/Inverse.lean:87`); plausible mathlib addition.

### `lemma array_getD_eq_toList_getD`
- **Type**: `(arr : Array ℤ) (i : ℕ) : arr.getD i 0 = arr.toList.getD i 0`
- **What**: `getD` commutes with `toList`.
- **How**: `Array.getD_eq_getD_getElem?`, `List.getD_eq_getElem?_getD`, `List.getElem?_toArray`, `Array.toArray_toList`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `inverseOnePlusCoeffsUpTo_toList` (L314), `inverseOnePlusCoeffsUpTo_getD` (L321)
- **Visibility**: public
- **Lines**: 271–274, body 2 lines
- **Notes**: Composition of 4 core lemmas (`Init/Data/Array/Lemmas.lean:4406`, `Init/Data/List/Lemmas.lean:344`, `Init/Data/Array/Basic.lean:140/91`); no single core lemma found (searched `getD_toList`, `toList_getD`, `getD_eq_toList_getD`). Holds for any `α`.

### `lemma getD_map_range`
- **Type**: `(g : ℕ → ℤ) (L j : ℕ) (hj : j < L) : ((List.range L).map g).getD j 0 = g j`
- **What**: Indexing `map g (range L)`.
- **How**: `List.getD_eq_getElem?_getD`, `List.getElem?_map`, `List.getElem?_range`.
- **Hypotheses**: j < L
- **Uses from project**: []
- **Used by**: `inverseOnePlusCoeffsUpTo_toList` (L315), `inverseOnePlusCoeffsUpTo_getD` (L323)
- **Visibility**: public
- **Lines**: 276–279, body 2 lines
- **Notes**: Duplicates the last 3 rewrites of `foldl_push_getD` (L54–56). Generic in `α`.

### `lemma inverseOnePlusCoeffsUpTo_toList`
- **Type**: `(a : Array ℤ) (α : ℕ → ℤ) (N : ℕ) (hα : ∀ j ≤ N, a.getD j 0 = α j) : ∀ K ≤ N+1, (⟨the foldl loop of inverseOnePlusCoeffsUpTo restricted to range K⟩).toList = (range K).map fun i => ((mk α).invOfUnit 1).coeff i`
- **What**: Loop invariant: after K steps the accumulator tabulates the coefficients of `(mk α)⁻¹` on 0..K−1.
- **How**: Induction on K; `List.range_succ`, `List.foldl_concat`; at a successor index `foldl_range_add_eq_sum` + `coeff_invOfUnit_one_succ`, with `hα`, `array_getD_eq_toList_getD`, `getD_map_range`, `coeff_mk` to match summands.
- **Hypotheses**: `a` agrees with α on 0..N; K ≤ N+1
- **Uses from project**: `foldl_range_add_eq_sum`, `coeff_invOfUnit_one_succ`, `array_getD_eq_toList_getD`, `getD_map_range`
- **Used by**: `inverseOnePlusCoeffsUpTo_getD` (L320)
- **Visibility**: public
- **Lines**: 281–315, body 19 lines
- **Notes**: The statement TEXTUALLY DUPLICATES the loop body of `inverseOnePlusCoeffsUpTo` (Qj.lean:82–92) instead of naming it; a named step function in Qj.lean would let this be stated about `inverseOnePlusCoeffsUpTo` directly. Does not use the constant-term hypothesis (invOfUnit 1 is defined regardless).

### `lemma inverseOnePlusCoeffsUpTo_getD`
- **Type**: `(a) (α) (N) (hα : ∀ j ≤ N, a.getD j 0 = α j) (i) (hi : i ≤ N) : (inverseOnePlusCoeffsUpTo a N).getD i 0 = ((mk α).invOfUnit 1).coeff i`
- **What**: The inversion loop computes `invOfUnit` coefficients.
- **How**: Instantiate the invariant at K = N+1, `array_getD_eq_toList_getD`, `getD_map_range`.
- **Hypotheses**: as above
- **Uses from project**: `inverseOnePlusCoeffsUpTo`, `inverseOnePlusCoeffsUpTo_toList`, `array_getD_eq_toList_getD`, `getD_map_range`
- **Used by**: `qoverDelta_array_getD` (L338)
- **Visibility**: public
- **Lines**: 317–323, body 4 lines
- **Notes**: —

### `lemma deltaOverQArrayUpTo_getD`
- **Type**: `(n j : ℕ) (hj : j ≤ n) : (deltaOverQArrayUpTo n).getD j 0 = deltaOverQCoeffInt j`
- **What**: The shifted table equals the shifted coefficient function.
- **How**: `foldl_push_getD`, `delta_array_getD (n+1) (j+1)`, `rfl`.
- **Hypotheses**: j ≤ n
- **Uses from project**: `deltaOverQArrayUpTo`, `deltaOverQCoeffInt`, `foldl_push_getD`, `delta_array_getD`
- **Used by**: `qoverDelta_array_getD` (L339)
- **Visibility**: public
- **Lines**: 325–330, body 3 lines
- **Notes**: —

### `lemma qoverDelta_array_getD`
- **Type**: `(n i : ℕ) (hi : i ≤ n) : (qoverDeltaCoeffsArrayUpTo n).getD i 0 = ((mk deltaOverQCoeffInt).invOfUnit 1).coeff i`
- **What**: The q/Δ table computes the formal inverse of Δ/q.
- **How**: `inverseOnePlusCoeffsUpTo_getD` with `deltaOverQArrayUpTo_getD`.
- **Hypotheses**: i ≤ n
- **Uses from project**: `qoverDeltaCoeffsArrayUpTo`, `deltaOverQCoeffInt`, `inverseOnePlusCoeffsUpTo_getD`, `deltaOverQArrayUpTo_getD`
- **Used by**: `qoverDeltaCoeffInt_eq` (L345), `qjCoeffInt_eq` (L387)
- **Visibility**: public
- **Lines**: 332–339, body 3 lines
- **Notes**: —

### `lemma qoverDeltaCoeffInt_eq`
- **Type**: `(n : ℕ) : qoverDeltaCoeffInt n = ((mk deltaOverQCoeffInt).invOfUnit 1).coeff n`
- **What**: Pointwise version.
- **How**: previous lemma at i = n.
- **Hypotheses**: none
- **Uses from project**: `qoverDeltaCoeffInt`, `deltaOverQCoeffInt`, `qoverDelta_array_getD`
- **Used by**: `qoverDeltaCoeffInt_zero` (L348), `qoverDelta_mul_eq_one` (L356), `qjCoeffInt_eq` (L387)
- **Visibility**: public
- **Lines**: 341–345, body 1 line
- **Notes**: Key API.

### `lemma qoverDeltaCoeffInt_zero`
- **Type**: `qoverDeltaCoeffInt 0 = 1`
- **What**: q/Δ has constant term 1.
- **How**: `qoverDeltaCoeffInt_eq`, `coeff_zero_eq_constantCoeff`, simp (`constantCoeff (invOfUnit φ 1) = 1⁻¹`).
- **Hypotheses**: none
- **Uses from project**: `qoverDeltaCoeffInt`, `qoverDeltaCoeffInt_eq`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 347–349, body 2 lines
- **Notes**: UNUSED anywhere in the project (grep-verified). Junk candidate.

### `lemma qoverDelta_mul_eq_one`
- **Type**: `PowerSeries.mk deltaOverQCoeffInt * PowerSeries.mk qoverDeltaCoeffInt = 1`
- **What**: The computed Δ/q and q/Δ series are mutually inverse in ℤ⟦q⟧.
- **How**: `mk qoverDeltaCoeffInt = (mk deltaOverQCoeffInt).invOfUnit 1` by ext + `qoverDeltaCoeffInt_eq`; then `PowerSeries.mul_invOfUnit` with constant term 1 via `deltaOverQCoeffInt_zero`.
- **Hypotheses**: none
- **Uses from project**: `deltaOverQCoeffInt`, `qoverDeltaCoeffInt`, `qoverDeltaCoeffInt_eq`, `deltaOverQCoeffInt_zero`
- **Used by**: `qOverDelta_qexpansion_link` (L369)
- **Visibility**: public
- **Lines**: 351–358, body 6 lines
- **Notes**: uses `PowerSeries.mul_invOfUnit` (`Inverse.lean:102`).

### `lemma qOverDelta_qexpansion_link`
- **Type**: `mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk qoverDeltaCoeffInt) = qExpansion 1 qOverDelta`
- **What**: The computed q/Δ series is the q-expansion of the analytic q/Δ.
- **How**: `qExpansion 1 deltaOverQ` is a unit (`isUnit_iff_constantCoeff`, constant term 1); cancel it on the left: LHS·(computed Δ/q) = 1 by `qoverDelta_mul_eq_one` under `map_mul`; RHS·(Δ/q) = 1 by `integralDeltaOverQ_mul_qExpansion_qOverDelta` via `coeTo_integralDeltaOverQ`.
- **Hypotheses**: none
- **Uses from project**: `qoverDeltaCoeffInt`, `qOverDelta`, `deltaOverQ`, `deltaOverQ_qexpansion_link`, `deltaOverQCoeffInt`, `deltaOverQCoeffInt_zero`, `qoverDelta_mul_eq_one`, `coeTo_integralDeltaOverQ` (jfunction.lean:217), `integralDeltaOverQ_mul_qExpansion_qOverDelta` (jfunction.lean:291), `coeToComplexPowerSeries.ringHom`, `powerSeriesMapAlgHom`
- **Used by**: `qj_qexpansion_link` (L402)
- **Visibility**: public
- **Lines**: 360–372, body 11 lines
- **Notes**: no docstring; capital-O `qOverDelta` (project analytic def) vs lower-case `qoverDeltaCoeffInt` naming clash in the same statement.

### `lemma qjCoeffInt_eq`
- **Type**: `(n : ℕ) : qjCoeffInt n = ((mk e4CoeffInt) ^ 3 * mk qoverDeltaCoeffInt).coeff n`
- **What**: The array-computed q·j coefficient is the formal E₄³·(q/Δ) coefficient.
- **How**: `convArrayUpTo_getD`, `convArrayCoeff_eq_coeff_mul` with `hA := convArrayUpTo_cube_coeff … (n+1)` and `hB := qoverDelta_array_getD`, `mk_coeff_self`.
- **Hypotheses**: none
- **Uses from project**: `qjCoeffInt`, `qjCoeffsArrayUpTo`, `e4CoeffInt`, `qoverDeltaCoeffInt`, `convArrayUpTo_getD`, `convArrayCoeff_eq_coeff_mul`, `mk_coeff_self`, `convArrayUpTo_cube_coeff`, `qoverDelta_array_getD`, `qoverDeltaCoeffInt_eq`
- **Used by**: `qj_series_eq` (L393)
- **Visibility**: public
- **Lines**: 374–387, body 9 lines
- **Notes**: —

### `lemma qj_series_eq`
- **Type**: `PowerSeries.mk qjCoeffInt = (mk e4CoeffInt) ^ 3 * mk qoverDeltaCoeffInt`
- **What**: Series form of the previous lemma.
- **How**: ext + `coeff_mk` + `qjCoeffInt_eq`.
- **Hypotheses**: none
- **Uses from project**: `qjCoeffInt`, `e4CoeffInt`, `qoverDeltaCoeffInt`, `qjCoeffInt_eq`
- **Used by**: `qj_qexpansion_link` (L397)
- **Visibility**: public
- **Lines**: 389–393, body 2 lines
- **Notes**: —

### `theorem qj_qexpansion_link`
- **Type**: `mapAlgHom (Algebra.ofId ℤ ℂ) qj_qexpansion = qExpansion 1 qj`
- **What**: MAIN: the computed q·j series, base-changed to ℂ, is the analytic q-expansion of q·j.
- **How**: `qj_series_eq`, `map_mul`/`map_pow`, `E4_int_link`, `qOverDelta_qexpansion_link`; `qExpansion 1 (E4^3) = (qExpansion 1 E4)^3` by mathlib `qExpansion_of_pow` (via `DirectSum.ofPow`); `qExpansion_mul` (analytic-hypothesis version, mathlib) with `E4_pow_three_cuspFunction_analyticAt`, `qOverDelta_cuspFunction_analyticAt`; `E4_pow_three_mul_qOverDelta_eq_qj`.
- **Hypotheses**: none
- **Uses from project**: `qj_qexpansion`, `qj` (jfunction.lean:239), `qj_series_eq`, `E4`, `E4_int_link`, `qOverDelta_qexpansion_link`, `E4_pow_three_cuspFunction_analyticAt` (jfunction.lean:285), `qOverDelta_cuspFunction_analyticAt` (jfunction.lean:274), `E4_pow_three_mul_qOverDelta_eq_qj` (jfunction.lean:242)
- **Used by**: `qj_qxp_coeff_link` (L408)
- **Visibility**: public
- **Lines**: 395–404, body 8 lines
- **Notes**: no docstring on a main theorem. Mathlib: `qExpansion_of_pow` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:638`), `qExpansion_mul` (:466).

### `theorem qj_qxp_coeff_link`
- **Type**: `(n : ℕ) : (qExpansion 1 qj).coeff n = qj_qexpansion.coeff n` (RHS cast)
- **What**: Coefficientwise form.
- **How**: `congrArg`.
- **Hypotheses**: none
- **Uses from project**: `qj`, `qj_qexpansion`, `qj_qexpansion_link`
- **Used by**: unused in file; consumed by `qexp_coeffs.lean:51–108`, `LevelThree.lean:130`
- **Visibility**: public
- **Lines**: 406–408, body 1 line
- **Notes**: —

## File Summary
- Total declarations: 43 (0 defs, 43 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `foldl_range_add_eq_sum` (3), `foldl_push_getD` (4), `convArrayUpTo_getD` (3), `convArrayCoeff_eq_coeff_mul` (3), `deltaCoeffInt_cast` (3), `qoverDeltaCoeffInt_eq` (3)
- Unused declarations (not used by anything in this file): `E6_int_link` (unused project-wide), `qoverDeltaCoeffInt_zero` (unused project-wide), `Delta_qxp_coeff_link`, `ramanujanTau_link`, `qj_qxp_coeff_link` (exports, used downstream)
- Declarations with sorry: none
- Declarations with set_option: none per-declaration; file-level `set_option linter.style.header false` (L4) — no copyright header
- Proofs >30 lines: none (longest: `inverseOnePlusCoeffsUpTo_toList` 19 lines, `qOverDelta_qexpansion_link` 11, `sigmaPow_eq_sigma` 11)

## Observations (evidence for the analysis phases)
### Mathlib API candidates
- `foldl_push_toList` (L39–46) = core `Array.foldl_toList_eq_map` (`Init/Data/Array/Lemmas.lean:4389`), VERIFIED closes by `simpa`. Delete.
- `mk_coeff_self` (L82–85) = `PowerSeries.ext fun _ => PowerSeries.coeff_mk _ _` (`Mathlib/RingTheory/PowerSeries/Basic.lean:91,112`), VERIFIED. Inline.
- `int_cast_div_eq_inv_mul_complex` (L170–174) = `Int.cast_div_charZero` (`Mathlib/Data/Int/CharZero.lean:27`) + `div_eq_inv_mul`; hypothesis should be `1728 ∣ z`. Inline at L216.
- `array_getD_eq_toList_getD` (L271–274), `getD_map_range` (L276–279): compositions of core `Array.getD_eq_getD_getElem?` (`Init/Data/Array/Lemmas.lean:4406`), `List.getD_eq_getElem?_getD` (`Init/Data/List/Lemmas.lean:344`), `List.getElem?_map`, `List.getElem?_range` (`Init/Data/List/Range.lean:149`); no single lemma exists — but both vanish if the tables are `Array.ofFn` (then `Array.getElem?_ofFn` `Init/Data/Array/Lemmas.lean:4288` does everything).
- `foldl_range_add_eq_sum` (L30–35): no single mathlib lemma; would vanish if `Qj.lean` used `Finset.sum` (VERIFIED evaluable).
- `foldl_sigma_search_eq_sum`+`sigmaPow_eq_sigma` (L108–129): vanish if `sigmaPow := (ArithmeticFunction.sigma k n : ℤ)` (`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:143`, VERIFIED evaluable).
- `coeff_invOfUnit_one_succ` (L262–269): tidy specialization of `PowerSeries.coeff_invOfUnit` (`Mathlib/RingTheory/PowerSeries/Inverse.lean:87`) — candidate for upstreaming as `PowerSeries.coeff_invOfUnit_succ`.
- The link theorems use `PowerSeries.mapAlgHom` (`Basic.lean:728`) but go through `change` + `PowerSeries.coeff_map` (`Basic.lean:455`) 3× instead of a `coeff_mapAlgHom` simp lemma (`mapAlgHom_apply` `Basic.lean:732` + `coeff_map`).
- Cast helpers re-proved that mathlib has: only `int_cast_div_eq_inv_mul_complex` (↔ `Int.cast_div_charZero`); no `Nat.cast_*`/`Int.cast_*` lemma is re-proved — casts are otherwise discharged by `norm_cast`/`exact_mod_cast`/`push_cast` (L129, L173, L241, L258). No `Finset.sum_*` lemma is re-proved; `foldl_range_add_eq_sum` is the only sum-shaped helper and it is a `List.foldl`↔`Finset.sum` bridge (absent from mathlib as a single lemma).

### Missing API / repeated patterns
- Idiom A "`congrArg (PowerSeries.coeff n) <map identity>`; `change (PowerSeries.map (Int.castRingHom ℂ) F).coeff n = _ at h`; `rw [PowerSeries.coeff_map] at h`" at L203–206, L228–230, L235–239 (3×). Add `lemma coeff_mapAlgHom_ofId (F : ℤ⟦X⟧) (n) : (mapAlgHom (Algebra.ofId ℤ ℂ) F).coeff n = (F.coeff n : ℂ)` (or use `IntegralPowerSeries` API) and these become one `rw`.
- Idiom B "`simpa [integralX, coeToComplexPowerSeries.ringHom, powerSeriesMapAlgHom] using coeTo_of_toIntegralPowerSeries X_isIntegralPowerSeries`" at L159–160, L165–166, L371–372 (3×). Add in `IntegralPowerSeries.lean`: `lemma mapAlgHom_ofId_toIntegralPowerSeries (h : IsIntegralPowerSeries f) : mapAlgHom (Algebra.ofId ℤ ℂ) (toIntegralPowerSeries h) = f`.
- The loop body of `inverseOnePlusCoeffsUpTo` is copied verbatim into the statement of `inverseOnePlusCoeffsUpTo_toList` (L287–294 vs Qj.lean:82–92): name the step function (`invStep a : Array ℤ → ℕ → Array ℤ`) so the invariant is stated about `inverseOnePlusCoeffsUpTo` itself.
- Missing companions: none of `Delta_qexpansion_link`/`qj_qexpansion_link`/`ramanujanTau_link`/`Delta_qexpansion_coeff_eq`-consumers are `@[simp]`; `deltaCoeffInt_cast` has no `qjCoeffInt_cast` twin (downstream `qexp_coeffs.lean:47–51` re-derives it inline as `qjCoeffs_eq_qjQExpansion_coeff_aux`).

### Junk candidates
- `E6_int_link` (L162–166): unused project-wide (grep).
- `qoverDeltaCoeffInt_zero` (L347–349): unused project-wide (grep); `qOverDelta_qexpansion_link` uses `deltaOverQCoeffInt_zero` instead.
- `set_option linter.style.header false` (L4) instead of a copyright header (Qj.lean and Examples.lean have one).
- 25 of 43 declarations lack docstrings (L30, 58, 63, 108, 118, 131, 139, 148, 152, 156, 162, 208, 220, 232, 243, 255, 271, 276, 317, 347, 351, 360, 389, 395, 406), including both main theorems.
- Root-namespace pollution: `foldl_range_add_eq_sum`, `foldl_push_toList`, `foldl_push_getD`, `mk_coeff_self`, `array_getD_eq_toList_getD`, `getD_map_range`, `coeff_invOfUnit_one_succ` are generic list/array/power-series lemmas declared at top level with no namespace; they should be `XYin.PhD.qExpansion_tactic.*` (or deleted per above).

### Moral duplicates within this batch
- `Delta_qxp_coeff_link` (L220) vs `deltaCoeffInt_cast` (L226): same fact up to `Delta_qexpansion_coeff_eq` and symmetry.
- `deltaCoeffsArrayUpTo_getD` (L178) vs `delta_array_getD` (L194): same LHS, RHS differ by `deltaCoeffInt_eq`.
- `e4CoeffInt_eq_integralE4_coeff`/`e6CoeffInt_eq_integralE6_coeff`, `E4_int_series_eq`/`E6_int_series_eq`, `E4_int_link`/`E6_int_link`: three pairs with identical skeletons (E₆ side of the last pair unused).
- `convArrayUpTo_self_coeff` / `convArrayUpTo_cube_coeff`: same skeleton; a `pow` induction lemma subsumes both.
- `foldl_push_getD` (L49–56) and `getD_map_range` (L276–279) share their last three rewrites.
- Cross-file: `qexp_coeffs.lean:47–51 qjCoeffs_eq_qjQExpansion_coeff_aux` is the `qj` twin of `ramanujanTau_link` (L232) — same proof shape (cast both sides, `exact_mod_cast`).

### Generalization notes
- `foldl_range_add_eq_sum`: any `[AddCommMonoid M]` (only `Finset.sum_range_succ`, `List.foldl_concat` used).
- `foldl_push_toList`, `foldl_push_getD`, `array_getD_eq_toList_getD`, `getD_map_range`: any type `α` with a default (`Inhabited`/explicit default arg); nothing about ℤ is used.
- `convArrayCoeff_eq_coeff_mul`, `mk_coeff_self`, `convArrayUpTo_self/cube_coeff`, `inverseOnePlusCoeffsUpTo_toList/_getD`: any `[Semiring R]` (resp. `[Ring R]` for the inverse ones) — proofs use only `coeff_mul`, `coeff_mk`, `coeff_invOfUnit`, `pow_succ`.
- `int_cast_div_eq_inv_mul_complex`: any `[DivisionRing k] [CharZero k]`, any divisor `d ≠ 0` with `d ∣ z` (`Int.cast_div_charZero` is already that general).
- `coeff_invOfUnit_one_succ`: already generic (`[Ring R]`).
