# Inventory: XYin/PhD/qExpansion_tactic/Qj.lean  (304 lines)

Computational engine of the q-expansion "tactic" layer: integer coefficient tables for E₄, E₆, Δ (Ramanujan τ), Δ/q, q/Δ and q·j built with `List.range`-`foldl`/`Array.push` loops (divisor power sums, array convolution, unit-power-series inversion), the formal series `Delta_qexpansion`, `qj_qexpansion : ℤ⟦X⟧` wrapping them via `PowerSeries.mk`, and a small meta layer (`#qexp` commands, `qexp_coeff` term elaborator) that certifies coefficient identities by compiled native evaluation (`Lean.ofReduceBool`). Soundness w.r.t. the analytic q-expansions is proved in `link.lean`. Imports only `Lean`, `Mathlib.Data.Complex.Basic`, `Mathlib.RingTheory.PowerSeries.Basic`, `Mathlib.Util.Qq`.

## Declarations

### `def XYin.PhD.qExpansion_tactic.reportTiming`
- **Type**: `Bool`
- **What**: Compile-time flag (`true`) controlling whether `#qexp`/`qexp_coeff` log elapsed wall-clock time.
- **How**: Constant `true`; "configured by editing this definition".
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `elab_rules : command` (L252, L264), `elab_rules : term` (L289, L302)
- **Visibility**: public
- **Lines**: 42–44, body 1 line
- **Notes**: Should be a `register_option` (Lean option) rather than a source-edited constant. Being `true` makes every `qexp_coeff` use emit an info message at build time (only Examples.lean uses it).

### `def XYin.PhD.qExpansion_tactic.sigmaPow`
- **Type**: `(k n : ℕ) → ℤ`
- **What**: σ_k(n) = Σ_{d ∣ n} d^k, the divisor power sum, as an integer.
- **How**: Linear search `d = 1..n` with `n % d = 0` test accumulated by `List.foldl` over `List.range n`.
- **Hypotheses**: none (returns 0 for n = 0)
- **Uses from project**: []
- **Used by**: `e4CoeffInt`, `e6CoeffInt`
- **Visibility**: public
- **Lines**: 46–52, body 6 lines
- **Notes**: Hand-rolled duplicate of mathlib `ArithmeticFunction.sigma` (verified evaluable, see Observations). `link.lean:118` proves `sigmaPow k n = σ k n`.

### `def XYin.PhD.qExpansion_tactic.e4CoeffInt`
- **Type**: `ℕ → ℤ`
- **What**: n-th coefficient of the normalized Eisenstein series E₄ = 1 + 240 Σ σ₃(n) qⁿ.
- **How**: `if n = 0 then 1 else 240 * sigmaPow 3 n`.
- **Hypotheses**: none
- **Uses from project**: `sigmaPow`
- **Used by**: `deltaCoeffsArrayUpTo` (L98), `qjCoeffsArrayUpTo` (L135)
- **Visibility**: public
- **Lines**: 54–57, body 1 line
- **Notes**: identified with `integralE4.coeff n` at `link.lean:131`.

### `def XYin.PhD.qExpansion_tactic.e6CoeffInt`
- **Type**: `ℕ → ℤ`
- **What**: n-th coefficient of E₆ = 1 − 504 Σ σ₅(n) qⁿ.
- **How**: `if n = 0 then 1 else -504 * sigmaPow 5 n`.
- **Hypotheses**: none
- **Uses from project**: `sigmaPow`
- **Used by**: `deltaCoeffsArrayUpTo` (L99)
- **Visibility**: public
- **Lines**: 59–62, body 1 line
- **Notes**: same skeleton as `e4CoeffInt`.

### `def XYin.PhD.qExpansion_tactic.coeffArray`
- **Type**: `(f : ℕ → ℤ) → (n : ℕ) → Array ℤ`
- **What**: Tabulates `f 0, …, f n` into an array of length n+1.
- **How**: `List.foldl` over `List.range (n+1)` pushing `f i` onto `#[]`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `deltaCoeffsArrayUpTo` (L98–99), `qjCoeffsArrayUpTo` (L135)
- **Visibility**: public
- **Lines**: 64–66, body 1 line
- **Notes**: Is `Array.ofFn (fun i : Fin (n+1) => f i)` (core); see Observations.

### `def XYin.PhD.qExpansion_tactic.convArrayCoeff`
- **Type**: `(a b : Array ℤ) → (n : ℕ) → ℤ`
- **What**: n-th Cauchy-product coefficient Σ_{i=0}^{n} a_i b_{n−i}, reading missing entries as 0.
- **How**: `List.foldl` accumulation over `List.range (n+1)` with `Array.getD _ 0`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `convArrayUpTo` (L77)
- **Visibility**: public
- **Lines**: 68–72, body 3 lines
- **Notes**: Manual sum that is `∑ i ∈ Finset.range (n+1), …` (computable; see Observations). Specified against `PowerSeries.coeff_mul` at `link.lean:70`.

### `def XYin.PhD.qExpansion_tactic.convArrayUpTo`
- **Type**: `(a b : Array ℤ) → (n : ℕ) → Array ℤ`
- **What**: The convolution table `[(a*b)_0, …, (a*b)_n]`.
- **How**: `foldl`/`push` tabulation of `convArrayCoeff a b i`.
- **Hypotheses**: none
- **Uses from project**: `convArrayCoeff`
- **Used by**: `deltaCoeffsArrayUpTo` (L100–102), `qjCoeffsArrayUpTo` (L136–138)
- **Visibility**: public
- **Lines**: 74–78, body 3 lines
- **Notes**: same `foldl`/`push` pattern as `coeffArray` (= `Array.ofFn`). O(n²).

### `def XYin.PhD.qExpansion_tactic.inverseOnePlusCoeffsUpTo`
- **Type**: `(a : Array ℤ) → (n : ℕ) → Array ℤ`
- **What**: Coefficients c_0..c_n of (1 + a_1 q + a_2 q² + …)⁻¹ via the recursion c_0 = 1, c_{m+1} = −Σ_{i=0}^{m} a_{i+1} c_{m−i} (entry `a_0` is ignored, assumed 1).
- **How**: `List.foldl` over `List.range (n+1)` with a `match k with | 0 | m+1` step reading back the accumulator with `getD`.
- **Hypotheses**: none (soundness needs `a.getD 0 0 = 1`, imposed downstream)
- **Uses from project**: []
- **Used by**: `qoverDeltaCoeffsArrayUpTo` (L125)
- **Visibility**: public
- **Lines**: 80–92, body 11 lines
- **Notes**: Genuinely accumulator-dependent recursion (cannot be `Array.ofFn`). Specified against `PowerSeries.invOfUnit _ 1` at `link.lean:284–323`. The loop body is textually duplicated inside `inverseOnePlusCoeffsUpTo_toList` (link.lean:287–294).

### `def XYin.PhD.qExpansion_tactic.deltaCoeffsArrayUpTo`
- **Type**: `ℕ → Array ℤ`
- **What**: Table [τ(0), …, τ(n)] of Δ = (E₄³ − E₆²)/1728 coefficients.
- **How**: Tabulate E₄, E₆; two convolutions for E₄³, one for E₆²; entrywise exact integer division by 1728 (`Int.div`, exact by E₄³ ≡ E₆² mod 1728, proved as `eisenstein_difference_coeff_modEq_zero` in Deltaqexpansions.lean).
- **Hypotheses**: none
- **Uses from project**: `coeffArray`, `e4CoeffInt`, `e6CoeffInt`, `convArrayUpTo`
- **Used by**: `deltaCoeffInt` (L108), `deltaCoeffsUpTo` (L111), `deltaOverQArrayUpTo` (L118)
- **Visibility**: public
- **Lines**: 94–105, body 8 lines
- **Notes**: Final `foldl`/`push` is again an `Array.ofFn`/`Array.map`-shaped tabulation.

### `def XYin.PhD.qExpansion_tactic.deltaCoeffInt`
- **Type**: `ℕ → ℤ`
- **What**: τ(n), the n-th coefficient of Δ.
- **How**: `(deltaCoeffsArrayUpTo n).getD n 0` (recomputes the whole O(n²) table per call).
- **Hypotheses**: none
- **Uses from project**: `deltaCoeffsArrayUpTo`
- **Used by**: `deltaOverQCoeffInt` (L114), `Delta_qexpansion` (L159), `Delta_qexpansion_coeff_eq`, `deltaTarget` (L206, L208)
- **Visibility**: public
- **Lines**: 107–108, body 1 line
- **Notes**: Downstream `qexp_coeffs.lean:62–77` proves `deltaCoeffInt k = …` by `rfl` (kernel evaluation), not by the native elaborator.

### `def XYin.PhD.qExpansion_tactic.deltaCoeffsUpTo`
- **Type**: `ℕ → List ℤ`
- **What**: `[τ(0), …, τ(n)]` as a list (for `#qexp Delta precision n`).
- **How**: `Array.toList` of the table.
- **Hypotheses**: none
- **Uses from project**: `deltaCoeffsArrayUpTo`
- **Used by**: `deltaTarget` (L209)
- **Visibility**: public
- **Lines**: 110–111, body 1 line
- **Notes**: display-only helper.

### `def XYin.PhD.qExpansion_tactic.deltaOverQCoeffInt`
- **Type**: `ℕ → ℤ`
- **What**: n-th coefficient of the unit series Δ/q = 1 − 24q + 252q² − …, i.e. τ(n+1).
- **How**: `deltaCoeffInt (n + 1)`.
- **Hypotheses**: none
- **Uses from project**: `deltaCoeffInt`
- **Used by**: unused in file (specification-only; used by link.lean)
- **Visibility**: public
- **Lines**: 113–114, body 1 line
- **Notes**: Not used by any computation in this file — `deltaOverQArrayUpTo` re-derives the same entries from the array for efficiency; the two are reconciled at `link.lean:326`.

### `def XYin.PhD.qExpansion_tactic.deltaOverQArrayUpTo`
- **Type**: `ℕ → Array ℤ`
- **What**: Table `[τ(1), …, τ(n+1)]` of Δ/q coefficients.
- **How**: Build `deltaCoeffsArrayUpTo (n+1)` once and re-tabulate shifted by one via `foldl`/`push`.
- **Hypotheses**: none
- **Uses from project**: `deltaCoeffsArrayUpTo`
- **Used by**: `qoverDeltaCoeffsArrayUpTo` (L125)
- **Visibility**: public
- **Lines**: 116–121, body 4 lines
- **Notes**: Is `(deltaCoeffsArrayUpTo (n+1)).extract 1 (n+2)` or `Array.ofFn`; see Observations.

### `def XYin.PhD.qExpansion_tactic.qoverDeltaCoeffsArrayUpTo`
- **Type**: `ℕ → Array ℤ`
- **What**: Coefficients c_0..c_n of q/Δ = (Δ/q)⁻¹.
- **How**: `inverseOnePlusCoeffsUpTo (deltaOverQArrayUpTo n) n`.
- **Hypotheses**: none
- **Uses from project**: `inverseOnePlusCoeffsUpTo`, `deltaOverQArrayUpTo`
- **Used by**: `qoverDeltaCoeffInt` (L129), `qjCoeffsArrayUpTo` (L138)
- **Visibility**: public
- **Lines**: 123–125, body 1 line
- **Notes**: —

### `def XYin.PhD.qExpansion_tactic.qoverDeltaCoeffInt`
- **Type**: `ℕ → ℤ`
- **What**: n-th coefficient of q/Δ.
- **How**: `getD n 0` of the table.
- **Hypotheses**: none
- **Uses from project**: `qoverDeltaCoeffsArrayUpTo`
- **Used by**: unused in file (specification-only; used by link.lean)
- **Visibility**: public
- **Lines**: 127–129, body 1 line
- **Notes**: —

### `def XYin.PhD.qExpansion_tactic.qjCoeffsArrayUpTo`
- **Type**: `ℕ → Array ℤ`
- **What**: Table of q·j = E₄³·(q/Δ) coefficients `[1, 744, 196884, …]` up to index n (entry n is the j-invariant coefficient c(n−1)).
- **How**: Tabulate E₄ up to `n+1`, two convolutions for E₄³, convolve with the q/Δ table up to n.
- **Hypotheses**: none
- **Uses from project**: `coeffArray`, `e4CoeffInt`, `convArrayUpTo`, `qoverDeltaCoeffsArrayUpTo`
- **Used by**: `qjCoeffInt` (L141), `qjCoeffsUpTo` (L144)
- **Visibility**: public
- **Lines**: 131–138, body 5 lines
- **Notes**: `top := n + 1` is one more than needed (only indices ≤ n are read; `link.lean:384` compensates with `(n+1)`). Also recomputes the E₄³ table already computed inside `deltaCoeffsArrayUpTo`.

### `def XYin.PhD.qExpansion_tactic.qjCoeffInt`
- **Type**: `ℕ → ℤ`
- **What**: n-th coefficient of q·j, i.e. c(n−1) for the j-invariant.
- **How**: `getD n 0` of `qjCoeffsArrayUpTo n`.
- **Hypotheses**: none
- **Uses from project**: `qjCoeffsArrayUpTo`
- **Used by**: `qj_qexpansion` (L149), `qj_qexpansion_coeff_eq`, `qjTarget` (L198, L200)
- **Visibility**: public
- **Lines**: 140–141, body 1 line
- **Notes**: `Cox/LevelThree.lean:47–49` proves `qjCoeffInt n = table n` for `n < 13` by `decide +kernel`; `qexp_coeffs.lean:81–109` by `rfl`. So the kernel, not native code, is what the library actually trusts.

### `def XYin.PhD.qExpansion_tactic.qjCoeffsUpTo`
- **Type**: `ℕ → List ℤ`
- **What**: `[1, 744, 196884, …]` as a list for `#qexp qj precision n`.
- **How**: `Array.toList`.
- **Hypotheses**: none
- **Uses from project**: `qjCoeffsArrayUpTo`
- **Used by**: `qjTarget` (L201)
- **Visibility**: public
- **Lines**: 143–144, body 1 line
- **Notes**: display-only.

### `def XYin.PhD.qExpansion_tactic.qj_qexpansion`
- **Type**: `PowerSeries ℤ`
- **What**: The formal series Σ qjCoeffInt(n) qⁿ ∈ ℤ⟦q⟧, candidate q-expansion of q·j.
- **How**: `PowerSeries.mk qjCoeffInt`.
- **Hypotheses**: none
- **Uses from project**: `qjCoeffInt`
- **Used by**: `qj_qexpansion_coeff_eq`, `qjTarget` (L197)
- **Visibility**: public
- **Lines**: 146–149, body 1 line
- **Notes**: Identified with `qExpansion 1 qj` under ℤ→ℂ at `link.lean:395`. Used by `jFunction/qexp_coeffs.lean`, `Cox/LevelThree.lean:130`.

### `theorem XYin.PhD.qExpansion_tactic.qj_qexpansion_coeff_eq`
- **Type**: `(n : ℕ) → qj_qexpansion.coeff n = qjCoeffInt n`
- **What**: Coefficient extraction for the formal series is the computed integer.
- **How**: `simp [qj_qexpansion]` (= `PowerSeries.coeff_mk`).
- **Hypotheses**: none
- **Uses from project**: `qj_qexpansion`, `qjCoeffInt`
- **Used by**: `qjTarget` (L199)
- **Visibility**: public
- **Lines**: 151–154, body 1 line
- **Notes**: Not tagged `@[simp]` although it is the canonical unfolding lemma; used 9× in `qexp_coeffs.lean` via `rw`.

### `def XYin.PhD.qExpansion_tactic.Delta_qexpansion`
- **Type**: `PowerSeries ℤ`
- **What**: Σ τ(n) qⁿ ∈ ℤ⟦q⟧, candidate q-expansion of Δ.
- **How**: `PowerSeries.mk deltaCoeffInt`.
- **Hypotheses**: none
- **Uses from project**: `deltaCoeffInt`
- **Used by**: `Delta_qexpansion_coeff_eq`, `deltaTarget` (L205)
- **Visibility**: public
- **Lines**: 156–159, body 1 line
- **Notes**: Naming: `Delta_qexpansion` (capital D, snake) vs `qj_qexpansion`; mathlib style would be `deltaQExpansion`.

### `theorem XYin.PhD.qExpansion_tactic.Delta_qexpansion_coeff_eq`
- **Type**: `(n : ℕ) → Delta_qexpansion.coeff n = deltaCoeffInt n`
- **What**: Coefficient extraction for `Delta_qexpansion`.
- **How**: `simp [Delta_qexpansion]`.
- **Hypotheses**: none
- **Uses from project**: `Delta_qexpansion`, `deltaCoeffInt`
- **Used by**: `deltaTarget` (L207)
- **Visibility**: public
- **Lines**: 161–164, body 1 line
- **Notes**: Not `@[simp]`; same skeleton as `qj_qexpansion_coeff_eq`.

### `def XYin.PhD.qExpansion_tactic.mkNativeDecideProofFor`
- **Type**: `(p : Expr) → MetaM Expr`
- **What**: Programmatic `native_decide`: returns a proof of a closed decidable `p` by compiling its `Decidable` instance.
- **How**: `Lean.Meta.mkDecide p` then `Lean.Meta.nativeEqTrue` (core `Lean/Meta/Native.lean:37`), wrapping the certificate with `of_decide_eq_true`.
- **Hypotheses**: `p` closed and decidable; proof depends on `Lean.ofReduceBool`.
- **Uses from project**: []
- **Used by**: `mkQexpCoeffProof` (L225)
- **Visibility**: public
- **Lines**: 166–177, body 7 lines
- **Notes**: Mirrors the core `native_decide` tactic implementation.

### `structure XYin.PhD.qExpansion_tactic.QexpTarget`
- **Type**: fields `series : Q(PowerSeries ℤ)`, `coeffName coeffEqName : Name`, `coeffFn : ℕ → ℤ`, `coeffsUpTo : ℕ → List ℤ`
- **What**: Descriptor of one certifiable series: the formal series as a `Qq` expression, the names of its coefficient function and bridging lemma, and the same function as a runtime value.
- **How**: plain structure.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `qjTarget`, `deltaTarget`, `qexpTarget?`, `mkQexpCoeffProof`
- **Visibility**: public
- **Lines**: 179–193
- **Notes**: —

### `def XYin.PhD.qExpansion_tactic.qjTarget`
- **Type**: `QexpTarget`
- **What**: Target record for q·j.
- **How**: record literal.
- **Hypotheses**: none
- **Uses from project**: `QexpTarget`, `qj_qexpansion`, `qjCoeffInt`, `qj_qexpansion_coeff_eq`, `qjCoeffsUpTo`
- **Used by**: `qexpTarget?` (L213)
- **Visibility**: public
- **Lines**: 195–201
- **Notes**: —

### `def XYin.PhD.qExpansion_tactic.deltaTarget`
- **Type**: `QexpTarget`
- **What**: Target record for Δ.
- **How**: record literal.
- **Hypotheses**: none
- **Uses from project**: `QexpTarget`, `Delta_qexpansion`, `deltaCoeffInt`, `Delta_qexpansion_coeff_eq`, `deltaCoeffsUpTo`
- **Used by**: `qexpTarget?` (L214)
- **Visibility**: public
- **Lines**: 203–209
- **Notes**: —

### `def XYin.PhD.qExpansion_tactic.qexpTarget?`
- **Type**: `Lean.Name → Option QexpTarget`
- **What**: Maps the identifiers `qj`/`Delta` to their target records.
- **How**: pattern match on raw names.
- **Hypotheses**: none
- **Uses from project**: `qjTarget`, `deltaTarget`, `QexpTarget`
- **Used by**: both `elab_rules` blocks (L243, L255, L282, L293)
- **Visibility**: public
- **Lines**: 211–215
- **Notes**: Could be a syntax alternative `("qj" <|> "Delta")` instead of an `ident` with runtime lookup.

### `def XYin.PhD.qExpansion_tactic.mkQexpCoeffProof`
- **Type**: `(t : QexpTarget) → (n : ℕ) → (xQ : Q(ℤ)) → MetaM Expr`
- **What**: Builds a proof of `t.series.coeff n = xQ` by chaining the bridging lemma with a native certificate of `t.coeffName n = xQ`.
- **How**: `mkAppM t.coeffEqName #[n]` ⬝ `Eq.trans` ⬝ `mkNativeDecideProofFor (coeffName n = xQ)`, then `mkExpectedTypeHint` to the `Qq`-built target.
- **Hypotheses**: `xQ` a closed integer term equal to the true coefficient.
- **Uses from project**: `QexpTarget`, `mkNativeDecideProofFor`
- **Used by**: `elab_rules : term` (L287, L300)
- **Visibility**: public
- **Lines**: 217–230, body 8 lines
- **Notes**: uses `Qq.mkNatLitQ` (Mathlib/Util/Qq.lean:83).

### `syntax XYin.PhD.qExpansion_tactic.qexpCoeffCmd`
- **Type**: `"#qexp" ident "coeff" num : command`
- **What**: Informational command printing one coefficient.
- **How**: syntax declaration.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `elab_rules : command` (L242)
- **Visibility**: public (global syntax)
- **Lines**: 232–234
- **Notes**: —

### `syntax XYin.PhD.qExpansion_tactic.qexpPrecisionCmd`
- **Type**: `"#qexp" ident "precision" num : command`
- **What**: Informational command printing all coefficients up to n.
- **How**: syntax declaration.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `elab_rules : command` (L254)
- **Visibility**: public
- **Lines**: 236–238
- **Notes**: —

### `elab_rules : command` (for `#qexp … coeff` / `#qexp … precision`)
- **Type**: command elaborator
- **What**: Looks up the target, evaluates `coeffFn n` / `coeffsUpTo n` at elaboration time and logs the value (plus timing).
- **How**: `qexpTarget?`, `toString`, `logInfoAt`, `IO.monoMsNow`.
- **Hypotheses**: identifier must be `qj` or `Delta`.
- **Uses from project**: `qexpTarget?`, `reportTiming`, `QexpTarget`
- **Used by**: unused in file (only Examples.lean)
- **Visibility**: public
- **Lines**: 240–265, 24 lines
- **Notes**: The `valueStr.length == 0` "internal error" checks (L248, L260) are unreachable (`toString` of an `Int`/`List` is never empty) — dead code. Two branches duplicate 10 lines.

### `syntax qexpCoeffAuto` (root namespace)
- **Type**: `"qexp_coeff" ident num : term`
- **What**: Auto form: proof term of `series.coeff n = c` with `c` computed.
- **How**: syntax declaration (declared after `end XYin.PhD.qExpansion_tactic`, so lives in root).
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `elab_rules : term` (L281)
- **Visibility**: public
- **Lines**: 269–272
- **Notes**: —

### `syntax qexpCoeffManual` (root namespace)
- **Type**: `"qexp_coeff" ident num term : term`
- **What**: Manual form: user supplies the expected value.
- **How**: syntax declaration.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `elab_rules : term` (L292)
- **Visibility**: public
- **Lines**: 274–277
- **Notes**: —

### `elab_rules : term` (for `qexp_coeff`)
- **Type**: term elaborator
- **What**: Elaborates `qexp_coeff qj n [x]` into a native-certified proof of `qj_qexpansion.coeff n = x` (x computed by `t.coeffFn` in auto mode, or elaborated at `ℤ` in manual mode).
- **How**: `mkQexpCoeffProof` inside `liftMetaM`; `Qq.mkIntLitQ` (Mathlib/Util/Qq.lean:88) for the literal; `elabTermEnsuringType x q(ℤ)` in manual mode.
- **Hypotheses**: identifier `qj`/`Delta`; manual value must be correct (else `nativeEqTrue` fails).
- **Uses from project**: `qexpTarget?`, `mkQexpCoeffProof`, `reportTiming`, `QexpTarget`
- **Used by**: unused in file (only Examples.lean)
- **Visibility**: public
- **Lines**: 279–304, 25 lines
- **Notes**: Two branches duplicate the timing/lookup scaffolding (~8 lines). Not used anywhere in the library (grep: only `Examples.lean`); library consumers use `rfl`/`decide +kernel` instead.

## File Summary
- Total declarations: 34 (25 defs, 2 theorems, 1 structure, 4 syntax, 2 elab_rules)
- Key API (used by 3+ others in the file): `deltaCoeffsArrayUpTo` (3), `deltaCoeffInt` (4), `qjCoeffInt` (3), `QexpTarget` (4), `qexpTarget?` (4), `reportTiming` (4), `coeffArray`/`convArrayUpTo` (2 each but 5 call sites)
- Unused declarations (not used by anything in this file): `deltaOverQCoeffInt`, `qoverDeltaCoeffInt` (spec-only, used by link.lean); the meta layer `elab_rules` ×2 / `qexp_coeff` syntax / `#qexp` syntax (used only by Examples.lean, nowhere in the library)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (all proofs ≤ 1 line; longest defs are the two `elab_rules` blocks, 24–25 lines)

## Observations (evidence for the analysis phases)
### Mathlib API candidates
- `sigmaPow` (L47–52) duplicates `ArithmeticFunction.sigma` (`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:143`, `sigma_apply`:151; `Nat.divisors` is `{d ∈ Ico 1 (n+1) | d ∣ n}`, `Mathlib/NumberTheory/Divisors.lean:52`, computable). VERIFIED by scratch `#eval (ArithmeticFunction.sigma 3 12 : ℕ) = 2044` and `#eval ∑ d ∈ Nat.divisors 12, (d:ℤ)^3 = 2044` under `lake env lean`. Defining `sigmaPow k n := (σ k n : ℤ)` (or `∑ d ∈ n.divisors, (d:ℤ)^k`) deletes `link.lean:108–129` (`foldl_sigma_search_eq_sum`, `sigmaPow_eq_sigma`, 22 lines). Caveat: downstream `rfl`/`decide +kernel` proofs (`qexp_coeffs.lean:62–113`, `LevelThree.lean:49`) would then kernel-reduce `Finset.filter`/`Multiset` quotients — must be re-timed.
- `convArrayCoeff` (L69–72): the `foldl` sum is `∑ i ∈ Finset.range (n+1), a.getD i 0 * b.getD (n-i) 0`. `Finset.sum` over `range` IS evaluable by compiled code (VERIFIED `#eval ∑ i ∈ Finset.range 5, (i:ℤ) = 10`). Writing it as a `Finset.sum` deletes `link.lean:30–35` (`foldl_range_add_eq_sum`) and makes `convArrayCoeff_eq_coeff_mul` a direct `PowerSeries.coeff_mul` (`Mathlib/RingTheory/PowerSeries/Basic.lean:243`) + `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` (`Mathlib/Algebra/BigOperators/NatAntidiagonal.lean:63`, to_additive) rewrite. Same kernel-reduction caveat.
- `coeffArray` (L65–66), the tabulation in `convArrayUpTo` (L76–78), `deltaCoeffsArrayUpTo` (L103–105), `deltaOverQArrayUpTo` (L119–121): all are `Array.ofFn (fun i : Fin (n+1) => g i)` (core `Init/Data/Array/OfFn.lean`; `Array.size_ofFn` `Init/Data/Array/Lemmas.lean:4255`, `Array.getElem_ofFn`:4283, `getElem?_ofFn`:4288, `toList_ofFn` OfFn.lean:53). VERIFIED: `(Array.ofFn (fun j : Fin (n+1) => f j)).getD i 0 = f i` closes by `simp [Array.getD_eq_getD_getElem?, hi]`. This deletes `link.lean:37–56` (`foldl_push_toList`, `foldl_push_getD`). Alternatively keep `foldl`/`push` and use core `Array.foldl_toList_eq_map` (`Init/Data/Array/Lemmas.lean:4389`), which is `foldl_push_toList` verbatim (VERIFIED by `simpa`).
- `deltaOverQArrayUpTo` (L117–121) is `(deltaCoeffsArrayUpTo (n+1)).extract 1 (n+2)` (core `Array.extract`, with `Array.getElem_extract`) — no need for a fresh loop.
- `PowerSeries.trunc` (`Mathlib/RingTheory/PowerSeries/Trunc.lean:51`) and `Polynomial.coeff` are noncomputable (Finsupp-based) and CANNOT replace the computational layer; `PowerSeries.invOfUnit` (`Inverse.lean:87/102`) likewise is spec-only. No list/array convolution API exists in mathlib or core (searched: `convolve`, `convolution`, `cauchyProduct` in `Mathlib/Data/List`, `Data/Array`, `Algebra/Polynomial`, `RingTheory/PowerSeries` — only `Analysis/Convolution.lean`, analytic). So `convArrayCoeff`/`inverseOnePlusCoeffsUpTo` are legitimately hand-rolled; only their *statement shape* (Finset sums, `Array.ofFn`) should ride on the library.
- `mkNativeDecideProofFor` re-implements core `native_decide` (`Lean/Meta/Native.lean:37 nativeEqTrue`, `Lean/Meta/AppBuilder.lean:588 mkDecide`); acceptable since a term-level elaborator needs the `Expr`.

### Missing API / repeated patterns
- `foldl`/`push` tabulation idiom appears 5× (L66, L77, L104, L120, plus L83–91 inside the inverse loop); one `Array.ofFn`/`Array.map` rewrite removes 4 of them and their 2 bridging lemmas in link.lean.
- `e4CoeffInt`/`e6CoeffInt` (L56–62) are the same template with constants (240, 3)/(−504, 5); a single `eisensteinCoeffInt (c : ℤ) (k n : ℕ)` would halve link.lean's `e4/e6CoeffInt_eq_integralE*_coeff` and `E*_int_series_eq` pairs.
- `qj_qexpansion_coeff_eq`/`Delta_qexpansion_coeff_eq` should be `@[simp]`; both are consumed by `rw` 16× in `qexp_coeffs.lean`.
- The two `elab_rules` blocks each duplicate their lookup+timing scaffolding across two alternatives (L242–253 vs 254–265; L281–291 vs 292–303).

### Junk candidates
- L248–249, L260–261: unreachable "internal error: empty output" branches (`toString` of `Int`/`List Int` is never empty).
- `reportTiming := true` (L44) makes the elaborator noisy in every build that uses it; source-edited flag instead of `register_option`.
- The entire meta layer (L166–304, `mkNativeDecideProofFor`, `QexpTarget`, `qjTarget`, `deltaTarget`, `qexpTarget?`, `mkQexpCoeffProof`, `#qexp`, `qexp_coeff`) is used only by `Examples.lean` (grep-verified: no other file mentions `qexp_coeff`/`#qexp`/`QexpTarget`). The library (`qexp_coeffs.lean`, `LevelThree.lean`) certifies coefficients by `rfl`/`decide +kernel` and never introduces `Lean.ofReduceBool` (grep: no `native_decide`/`ofReduceBool` outside `qExpansion_tactic/`). Either the meta layer should be adopted downstream or moved to a separate, non-library module.
- `qjCoeffsArrayUpTo` `top := n + 1` (L134) computes one unused row; `deltaCoeffInt`/`qjCoeffInt` recompute the whole table per call (fine for tables, wasteful when `qexp_coeffs.lean` asks for coefficients 1..5 separately).

### Moral duplicates within this batch
- `deltaOverQCoeffInt n` (L114) and `(deltaOverQArrayUpTo n).getD n 0` (L117–121) compute the same integer by two routes; reconciled by `link.lean:326 deltaOverQArrayUpTo_getD`.
- `deltaCoeffsUpTo`/`qjCoeffsUpTo` (L111, L144) and `deltaCoeffInt`/`qjCoeffInt` (L108, L141): 4 one-line `getD`/`toList` projections of the same two tables.
- `qj_qexpansion`+`qj_qexpansion_coeff_eq` vs `Delta_qexpansion`+`Delta_qexpansion_coeff_eq`: identical 2-line pattern.

### Generalization notes
- `coeffArray`, `convArrayCoeff`, `convArrayUpTo`, `inverseOnePlusCoeffsUpTo` are stated for `Array ℤ` but only use `+`, `*`, `-`, `0`, `1` — any `[Ring R]` (even `[Semiring R]` for the first three) works; link.lean's specs would then be generic too. Not needed for the project, but it would let the same engine serve `ℤ/pℤ` or `ℚ` coefficient tables.
