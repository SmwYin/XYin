# XYin/PhD/qExpansion_tactic/Qj.lean

**Source path**: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/qExpansion_tactic/Qj.lean
**Project-internal imports**: [] (imports only `Lean`, `Lean.Meta.Native`, `Mathlib.Data.Complex.Basic`, `Mathlib.RingTheory.PowerSeries.Basic`, `Mathlib.Util.Qq`)
**Namespace**: `XYin.PhD.qExpansion_tactic` (except the final term-syntax/elab, which is at root level)

This file is the computational engine of a "q-expansion tactic": fast integer-arithmetic
computation of the q-expansion coefficients of Δ and of q·j (via σ_k divisor sums,
array convolutions, and power-series inversion), together with `#qexp` commands and a
`qexp_coeff` term elaborator that produce kernel-accepted proofs of coefficient values
via `native_decide`-style native evaluation.

### `def reportTiming`
- **Type**: `reportTiming : Bool`
- **What**: A global flag (hard-coded `true`) controlling whether the `#qexp` commands and `qexp_coeff` elaborator log elapsed wall-clock time.
- **How**: Constant definition, value `true`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `elab_rules : command` (#qexp), `elab_rules : term` (qexp_coeff)
- **Visibility**: public
- **Lines**: 12 (1 line)
- **Notes**: Configuration by editing source; not a `set_option`. none otherwise

### `def sigmaPow`
- **Type**: `sigmaPow (k n : Nat) : Int`
- **What**: The divisor power sum σ_k(n) = Σ_{d ∣ n, d > 0} d^k as an integer, with σ_k(0) = 0.
- **How**: Brute-force search: folds over `List.range n`, testing each candidate `d = i+1` for `n % d = 0` and accumulating `d^k`. Proved equal to `ArithmeticFunction.sigma` in link.lean (`sigmaPow_eq_sigma`).
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `e4CoeffInt`, `e6CoeffInt`
- **Visibility**: public
- **Lines**: 15–20 (6 lines)
- **Notes**: none

### `def e4CoeffInt`
- **Type**: `e4CoeffInt (n : Nat) : Int`
- **What**: The n-th q-expansion coefficient of the normalized Eisenstein series E₄: 1 for n = 0, and 240·σ₃(n) for n ≥ 1.
- **How**: Case split on `n = 0`; positive case multiplies `sigmaPow 3 n` by 240 (the classical formula E₄ = 1 + 240 Σ σ₃(n) qⁿ).
- **Hypotheses**: none
- **Uses from project**: [`sigmaPow`]
- **Used by**: `deltaCoeffsArrayUpTo`, `qoverDeltaCoeffsArrayUpTo`, `qjCoeffsArrayUpTo`
- **Visibility**: public
- **Lines**: 22–23 (2 lines)
- **Notes**: none

### `def e6CoeffInt`
- **Type**: `e6CoeffInt (n : Nat) : Int`
- **What**: The n-th q-expansion coefficient of the normalized Eisenstein series E₆: 1 for n = 0, and −504·σ₅(n) for n ≥ 1.
- **How**: Case split on `n = 0`; positive case multiplies `sigmaPow 5 n` by −504 (E₆ = 1 − 504 Σ σ₅(n) qⁿ).
- **Hypotheses**: none
- **Uses from project**: [`sigmaPow`]
- **Used by**: `deltaCoeffsArrayUpTo`, `qoverDeltaCoeffsArrayUpTo`, `qjCoeffsArrayUpTo`
- **Visibility**: public
- **Lines**: 25–26 (2 lines)
- **Notes**: none

### `def coeffArray`
- **Type**: `coeffArray (f : Nat → Int) (n : Nat) : Array Int`
- **What**: Tabulates a coefficient function on indices 0..n into an array of length n+1 (memoization for fast convolution).
- **How**: Folds `Array.push` over `List.range (n+1)`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `deltaCoeffsArrayUpTo`, `qoverDeltaCoeffsArrayUpTo`, `qjCoeffsArrayUpTo`
- **Visibility**: public
- **Lines**: 29–30 (2 lines)
- **Notes**: none

### `def convArrayCoeff`
- **Type**: `convArrayCoeff (a b : Array Int) (n : Nat) : Int`
- **What**: The n-th Cauchy-product (convolution) coefficient (a·b)ₙ = Σ_{i=0}^{n} aᵢ·b_{n−i} of two coefficient arrays, i.e. the coefficient of the product of the corresponding power series.
- **How**: Fold over `List.range (n+1)` accumulating `a.getD i 0 * b.getD (n−i) 0` (out-of-range entries default to 0).
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `convArrayUpTo`
- **Visibility**: public
- **Lines**: 33–36 (4 lines)
- **Notes**: none

### `def convArrayUpTo`
- **Type**: `convArrayUpTo (a b : Array Int) (n : Nat) : Array Int`
- **What**: The table of convolution coefficients (a·b)₀,…,(a·b)ₙ — the truncated product of two power series represented as arrays.
- **How**: Folds `Array.push (convArrayCoeff a b i)` over `List.range (n+1)`. O(n²) truncated multiplication.
- **Hypotheses**: none
- **Uses from project**: [`convArrayCoeff`]
- **Used by**: `deltaCoeffsArrayUpTo`, `qoverDeltaCoeffsArrayUpTo`, `qjCoeffsArrayUpTo`
- **Visibility**: public
- **Lines**: 39–42 (4 lines)
- **Notes**: none

### `def inverseOnePlusCoeffsUpTo`
- **Type**: `inverseOnePlusCoeffsUpTo (a : Array Int) (n : Nat) : Array Int`
- **What**: The coefficients b₀,…,bₙ of the multiplicative inverse of a power series 1 + a₁q + a₂q² + … with constant term 1 (only a₁, a₂, … of the input array are consulted; a₀ is ignored and taken to be 1).
- **How**: The standard inversion recursion b₀ = 1, b_{m+1} = −Σ_{i=0}^{m} a_{i+1}·b_{m−i}, implemented by folding over `List.range (n+1)` with the accumulator array supplying the already-computed bⱼ. Correctness proved in link.lean via `invFn` and `inverseOnePlusCoeffsUpTo_getD`.
- **Hypotheses**: The mathematical interpretation requires the input series to have constant term 1 (unit); the code itself is total.
- **Uses from project**: []
- **Used by**: `qoverDeltaCoeffsArrayUpTo`, `qjCoeffsArrayUpTo`
- **Visibility**: public
- **Lines**: 45–56 (12 lines)
- **Notes**: none

### `def deltaCoeffsArrayUpTo`
- **Type**: `deltaCoeffsArrayUpTo (n : Nat) : Array Int`
- **What**: The q-expansion coefficients τ(0)=0, τ(1)=1, τ(2)=−24, … of the discriminant Δ = (E₄³ − E₆²)/1728 up to index n (Ramanujan tau values, with the convention Δ = q − 24q² + …).
- **How**: Tabulates E₄- and E₆-coefficients via `coeffArray`, forms E₄³ and E₆² by repeated `convArrayUpTo`, then pushes `(E₄³ − E₆²)ᵢ / 1728` (integer division; exact by the classical congruence E₄³ ≡ E₆² mod 1728, proved in the jFunction development).
- **Hypotheses**: none (exactness of the division by 1728 is a theorem, not a hypothesis of the code)
- **Uses from project**: [`coeffArray`, `e4CoeffInt`, `e6CoeffInt`, `convArrayUpTo`]
- **Used by**: `deltaCoeffInt`, `deltaCoeffsUpTo`
- **Visibility**: public
- **Lines**: 58–66 (9 lines)
- **Notes**: none

### `def deltaCoeffInt`
- **Type**: `deltaCoeffInt (n : Nat) : Int`
- **What**: The n-th q-expansion coefficient of Δ, i.e. the Ramanujan tau value τ(n) (with τ(0) = 0). E.g. `deltaCoeffInt 4 = −1472`.
- **How**: Reads entry n of `deltaCoeffsArrayUpTo n` (recomputing the whole table; no cross-call memoization).
- **Hypotheses**: none
- **Uses from project**: [`deltaCoeffsArrayUpTo`]
- **Used by**: `deltaOverQCoeffInt`, `Delta_qexpansion`, `elab_rules : command` (#qexp Delta coeff), `deltaFoo`, `deltaFooWithValue`
- **Visibility**: public
- **Lines**: 68 (1 line)
- **Notes**: none

### `def deltaCoeffsUpTo`
- **Type**: `deltaCoeffsUpTo (n : Nat) : List Int`
- **What**: The list of Δ-coefficients [τ(0), …, τ(n)] for display by the `#qexp Delta precision` command.
- **How**: `Array.toList` of `deltaCoeffsArrayUpTo n`.
- **Hypotheses**: none
- **Uses from project**: [`deltaCoeffsArrayUpTo`]
- **Used by**: `elab_rules : command` (#qexp Delta precision)
- **Visibility**: public
- **Lines**: 70 (1 line)
- **Notes**: none

### `def deltaOverQCoeffInt`
- **Type**: `deltaOverQCoeffInt (n : Nat) : Int`
- **What**: The n-th coefficient of Δ/q = 1 − 24q + 252q² − …, i.e. the shifted series with (Δ/q)ₙ = τ(n+1). This is the unit power series whose inverse gives q/Δ.
- **How**: Index shift: `deltaCoeffInt (n + 1)`.
- **Hypotheses**: none
- **Uses from project**: [`deltaCoeffInt`]
- **Used by**: unused in file (used extensively in link.lean: `deltaOverQ_qexpansion_link`, `invFn` instantiation, `qoverDeltaCoeffInt_eq`, `qoverDelta_mul_eq_one`, …)
- **Visibility**: public
- **Lines**: 72 (1 line)
- **Notes**: none

### `def qoverDeltaCoeffsArrayUpTo`
- **Type**: `qoverDeltaCoeffsArrayUpTo (n : Nat) : Array Int`
- **What**: The coefficients of q/Δ = (Δ/q)⁻¹ up to index n — the inverse of the unit series Δ/q.
- **How**: Rebuilds the Δ-coefficient table up to n+1 inline (same construction as `deltaCoeffsArrayUpTo` but with headroom `top = n+1`), shifts it down one index to get Δ/q, then applies `inverseOnePlusCoeffsUpTo`.
- **Hypotheses**: none
- **Uses from project**: [`coeffArray`, `e4CoeffInt`, `e6CoeffInt`, `convArrayUpTo`, `inverseOnePlusCoeffsUpTo`]
- **Used by**: `qoverDeltaCoeffInt`
- **Visibility**: public
- **Lines**: 74–89 (16 lines)
- **Notes**: Duplicates the Δ-table construction of `deltaCoeffsArrayUpTo` inline (also duplicated in `qjCoeffsArrayUpTo`); the duplication is what forces the auxiliary lemma `delta_array_getD` in link.lean.

### `def qoverDeltaCoeffInt`
- **Type**: `qoverDeltaCoeffInt (n : Nat) : Int`
- **What**: The n-th coefficient of the power series q/Δ (so (q/Δ)₀ = 1, (q/Δ)₁ = 24, …).
- **How**: Reads entry n of `qoverDeltaCoeffsArrayUpTo n`.
- **Hypotheses**: none
- **Uses from project**: [`qoverDeltaCoeffsArrayUpTo`]
- **Used by**: unused in file (used in link.lean: `qoverDeltaCoeffInt_eq`, `qoverDelta_mul_eq_one`, `qOverDelta_qexpansion_link`, `qjCoeffInt_eq`, …)
- **Visibility**: public
- **Lines**: 91–92 (2 lines)
- **Notes**: none

### `def qjCoeffsArrayUpTo`
- **Type**: `qjCoeffsArrayUpTo (n : Nat) : Array Int`
- **What**: The q-expansion coefficients of q·j = E₄³·(q/Δ) up to index n, where j is the modular j-invariant; so entry 0 is 1, entry 1 is 744, entry 2 is 196884, etc. (entry n is the j-coefficient c(n−1)).
- **How**: Builds the E₄³ table and the Δ-table (with headroom top = n+1), shifts Δ to Δ/q, inverts via `inverseOnePlusCoeffsUpTo` to get q/Δ, then convolves E₄³ with q/Δ. This computes j via j = E₄³/Δ without any denominators.
- **Hypotheses**: none
- **Uses from project**: [`coeffArray`, `e4CoeffInt`, `e6CoeffInt`, `convArrayUpTo`, `inverseOnePlusCoeffsUpTo`]
- **Used by**: `qjCoeffInt`, `qjCoeffsUpTo`
- **Visibility**: public
- **Lines**: 94–110 (17 lines)
- **Notes**: Third inline copy of the Δ-table construction (see `qoverDeltaCoeffsArrayUpTo`).

### `def qjCoeffInt`
- **Type**: `qjCoeffInt (n : Nat) : Int`
- **What**: The n-th coefficient of q·j, i.e. the j-invariant Fourier coefficient c(n−1) (e.g. `qjCoeffInt 4 = 864299970 = c(3)`).
- **How**: Reads entry n of `qjCoeffsArrayUpTo n`.
- **Hypotheses**: none
- **Uses from project**: [`qjCoeffsArrayUpTo`]
- **Used by**: `qj_qexpansion`, `elab_rules : command` (#qexp qj coeff), `foo`, `fooWithValue`
- **Visibility**: public
- **Lines**: 112 (1 line)
- **Notes**: none

### `def qjCoeffsUpTo`
- **Type**: `qjCoeffsUpTo (n : Nat) : List Int`
- **What**: The list of q·j coefficients [1, 744, 196884, …] up to index n, for display by `#qexp qj precision`.
- **How**: `Array.toList` of `qjCoeffsArrayUpTo n`.
- **Hypotheses**: none
- **Uses from project**: [`qjCoeffsArrayUpTo`]
- **Used by**: `elab_rules : command` (#qexp qj precision)
- **Visibility**: public
- **Lines**: 114 (1 line)
- **Notes**: none

### `syntax qexpCoeffCmd`
- **Type**: `syntax (name := qexpCoeffCmd) "#qexp" ident "coeff" num : command`
- **What**: Command syntax `#qexp qj coeff n` / `#qexp Delta coeff n` for printing a single q-expansion coefficient.
- **How**: Plain syntax declaration; semantics given by the command `elab_rules` below.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `elab_rules : command` (#qexp)
- **Visibility**: public
- **Lines**: 116 (1 line)
- **Notes**: none

### `syntax qexpPrecisionCmd`
- **Type**: `syntax (name := qexpPrecisionCmd) "#qexp" ident "precision" num : command`
- **What**: Command syntax `#qexp qj precision n` / `#qexp Delta precision n` for printing all coefficients up to index n.
- **How**: Plain syntax declaration; semantics given by the command `elab_rules` below.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `elab_rules : command` (#qexp)
- **Visibility**: public
- **Lines**: 117 (1 line)
- **Notes**: none

### `elab_rules : command` (#qexp … coeff / precision)
- **Type**: command elaboration rules for `qexpCoeffCmd` and `qexpPrecisionCmd`
- **What**: Implements the `#qexp` commands: dispatches on the identifier (`qj` or `Delta`), evaluates `qjCoeffInt`/`deltaCoeffInt` (coeff) or `qjCoeffsUpTo`/`deltaCoeffsUpTo` (precision) inside the elaborator, and logs the value plus optional timing. Purely informational — produces no proof term.
- **How**: `Lean.Elab.Command` monadic code; `IO.monoMsNow` timing bracket, `logInfoAt` output, `throwErrorAt` on unknown target identifier.
- **Hypotheses**: The target identifier must be literally `qj` or `Delta`.
- **Uses from project**: [`qjCoeffInt`, `deltaCoeffInt`, `qjCoeffsUpTo`, `deltaCoeffsUpTo`, `reportTiming`, `qexpCoeffCmd` (syntax), `qexpPrecisionCmd` (syntax)]
- **Used by**: unused in file (exercised in Examples.lean)
- **Visibility**: public
- **Lines**: 119–151 (33 lines)
- **Notes**: Meta code >30 lines (two rules); interpreted (non-compiled) evaluation of the coefficient functions, so large n is slow here compared to the native-evaluation route.

### `def qj_qexpansion`
- **Type**: `qj_qexpansion : PowerSeries ℤ`
- **What**: The formal integer power series Σ qjCoeffInt(n)·qⁿ — the candidate q-expansion of q·j as an element of ℤ⟦q⟧. This is the series the `qexp_coeff qj` elaborator proves facts about, and which link.lean identifies with the analytic q-expansion of q·j.
- **How**: `PowerSeries.mk qjCoeffInt`.
- **Hypotheses**: none
- **Uses from project**: [`qjCoeffInt`]
- **Used by**: `qj_qexpansion_coeff_eq`, `foo`, `fooWithValue` (in proof-target types)
- **Visibility**: public
- **Lines**: 153–154 (2 lines)
- **Notes**: none

### `theorem qj_qexpansion_coeff_eq`
- **Type**: `qj_qexpansion_coeff_eq (n : Nat) : qj_qexpansion.coeff n = qjCoeffInt n`
- **What**: The defining coefficient identity: the n-th coefficient of the formal series `qj_qexpansion` is the computed integer `qjCoeffInt n`. This is the bridging lemma composed with a native-evaluation fact inside the elaborator.
- **How**: Unfolds `qj_qexpansion` and applies `PowerSeries.coeff_mk` (via `simp [qj_qexpansion]`).
- **Hypotheses**: none
- **Uses from project**: [`qj_qexpansion`, `qjCoeffInt`]
- **Used by**: `foo`, `fooWithValue`
- **Visibility**: public
- **Lines**: 156–158 (3 lines, 1-line proof)
- **Notes**: none

### `def Delta_qexpansion`
- **Type**: `Delta_qexpansion : PowerSeries ℤ`
- **What**: The formal integer power series Σ τ(n)·qⁿ (with the array-computed τ) — the candidate q-expansion of Δ in ℤ⟦q⟧.
- **How**: `PowerSeries.mk deltaCoeffInt`.
- **Hypotheses**: none
- **Uses from project**: [`deltaCoeffInt`]
- **Used by**: `Delta_qexpansion_coeff_eq`, `deltaFoo`, `deltaFooWithValue` (in proof-target types)
- **Visibility**: public
- **Lines**: 160–161 (2 lines)
- **Notes**: none

### `theorem Delta_qexpansion_coeff_eq`
- **Type**: `Delta_qexpansion_coeff_eq (n : Nat) : Delta_qexpansion.coeff n = deltaCoeffInt n`
- **What**: The n-th coefficient of `Delta_qexpansion` is the computed integer `deltaCoeffInt n`.
- **How**: Unfolds `Delta_qexpansion` and applies `PowerSeries.coeff_mk` (via `simp [Delta_qexpansion]`).
- **Hypotheses**: none
- **Uses from project**: [`Delta_qexpansion`, `deltaCoeffInt`]
- **Used by**: `deltaFoo`, `deltaFooWithValue`
- **Visibility**: public
- **Lines**: 163–165 (3 lines, 1-line proof)
- **Notes**: none

### `def mkNativeDecideProofFor`
- **Type**: `mkNativeDecideProofFor (p : Expr) : MetaM Expr`
- **What**: Given a decidable proposition `p` (as an `Expr`), produces a proof term of `p` by native compiled evaluation of its `Decidable` instance — a programmatic `native_decide`.
- **How**: Builds `decide p` via `Lean.Meta.mkDecide`, runs `nativeEqTrue` (from `Lean.Meta.Native`) to obtain a native-evaluation certificate that `decide p = true`, then wraps it with `of_decide_eq_true`. Errors if the proposition evaluates to false.
- **Hypotheses**: `p` must have a `Decidable` instance; resulting proofs depend on the `Lean.ofReduceBool` axiom (the `native_decide` trust base: compiler + native code).
- **Uses from project**: []
- **Used by**: `foo`, `fooWithValue`, `deltaFoo`, `deltaFooWithValue`
- **Visibility**: public
- **Lines**: 167–175 (9 lines)
- **Notes**: The whole point of the file's proof-producing machinery rests here; all `qexp_coeff` proofs carry the `ofReduceBool` axiom.

### `def foo`
- **Type**: `foo (n : Nat) : MetaM (Int × (nQ : Q(Nat)) × (ex : Q(ℤ)) × Q(qj_qexpansion.coeff $nQ = $ex))`
- **What**: For a given index n, computes x = qjCoeffInt n and returns (x, the literal n, the literal x, and a proof term of `qj_qexpansion.coeff n = x`) — the "auto" mode of `qexp_coeff qj`, where the coefficient value is discovered rather than supplied.
- **How**: Evaluates `qjCoeffInt n` in the meta layer, builds Qq literals with `Qq.mkNatLitQ`/`Qq.mkIntLitQ`, gets a native-decide proof of `qjCoeffInt n = x` via `mkNativeDecideProofFor`, and chains it with `qj_qexpansion_coeff_eq` by `Eq.trans`, fixing the statement with `mkExpectedTypeHint`.
- **Hypotheses**: none (fails if native evaluation disagrees, which cannot happen since x is computed by the same function)
- **Uses from project**: [`qjCoeffInt`, `qj_qexpansion_coeff_eq`, `mkNativeDecideProofFor`, `qj_qexpansion` (in the target type)]
- **Used by**: `elab_rules : term` (qexp_coeff auto form)
- **Visibility**: public
- **Lines**: 177–192 (16 lines)
- **Notes**: Placeholder name `foo` (and `fooWithValue`) — should be renamed (e.g. `mkQjCoeffProof`). The meta-level `qjCoeffInt n` evaluation is interpreted and duplicates the work the native evaluation then redoes.

### `def fooWithValue`
- **Type**: `fooWithValue (n : Nat) (xQ : Q(ℤ)) : MetaM ((nQ : Q(Nat)) × Q(qj_qexpansion.coeff $nQ = $xQ))`
- **What**: The "checked" mode: for a user-supplied integer expression x, produces a proof of `qj_qexpansion.coeff n = x`, failing if x is not the true coefficient.
- **How**: Same construction as `foo` but with the caller's `xQ` as the right-hand side: native-decide proof of `qjCoeffInt n = x` (`mkNativeDecideProofFor`) chained with `qj_qexpansion_coeff_eq` via `Eq.trans`.
- **Hypotheses**: `xQ` must evaluate (under the compiled `Decidable` check) to the actual coefficient, else elaboration fails.
- **Uses from project**: [`qjCoeffInt`, `qj_qexpansion_coeff_eq`, `mkNativeDecideProofFor`, `qj_qexpansion` (in the target type)]
- **Used by**: `elab_rules : term` (qexp_coeff manual form)
- **Visibility**: public
- **Lines**: 194–205 (12 lines)
- **Notes**: Placeholder-style name. Note: works for any closed integer term `xQ` decidably equal to the coefficient, not only literals.

### `def deltaFoo`
- **Type**: `deltaFoo (n : Nat) : MetaM (Int × (nQ : Q(Nat)) × (ex : Q(ℤ)) × Q(Delta_qexpansion.coeff $nQ = $ex))`
- **What**: Δ-analogue of `foo`: computes τ(n) and returns a proof term of `Delta_qexpansion.coeff n = τ(n)`.
- **How**: Identical pattern to `foo` with `deltaCoeffInt` and `Delta_qexpansion_coeff_eq`: native-decide certificate via `mkNativeDecideProofFor` chained by `Eq.trans`.
- **Hypotheses**: none
- **Uses from project**: [`deltaCoeffInt`, `Delta_qexpansion_coeff_eq`, `mkNativeDecideProofFor`, `Delta_qexpansion` (in the target type)]
- **Used by**: `elab_rules : term` (qexp_coeff auto form, Delta case)
- **Visibility**: public
- **Lines**: 207–222 (16 lines)
- **Notes**: Verbatim structural duplicate of `foo`; the four `foo`-family functions could be one parametrized function.

### `def deltaFooWithValue`
- **Type**: `deltaFooWithValue (n : Nat) (xQ : Q(ℤ)) : MetaM ((nQ : Q(Nat)) × Q(Delta_qexpansion.coeff $nQ = $xQ))`
- **What**: Δ-analogue of `fooWithValue`: proves `Delta_qexpansion.coeff n = x` for a user-supplied x, failing when x ≠ τ(n).
- **How**: Same `mkNativeDecideProofFor` + `Delta_qexpansion_coeff_eq` + `Eq.trans` construction.
- **Hypotheses**: `xQ` must decide equal to `deltaCoeffInt n` under native evaluation.
- **Uses from project**: [`deltaCoeffInt`, `Delta_qexpansion_coeff_eq`, `mkNativeDecideProofFor`, `Delta_qexpansion` (in the target type)]
- **Used by**: `elab_rules : term` (qexp_coeff manual form, Delta case)
- **Visibility**: public
- **Lines**: 224–235 (12 lines)
- **Notes**: Structural duplicate of `fooWithValue`.

### `syntax qexpCoeffAuto`
- **Type**: `syntax (name := qexpCoeffAuto) "qexp_coeff" ident num : term`
- **What**: Term syntax `qexp_coeff qj n` / `qexp_coeff Delta n`: a proof term of the coefficient identity with the value discovered automatically.
- **How**: Syntax declaration at root level (outside the namespace); semantics in the term `elab_rules`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `elab_rules : term`
- **Visibility**: public (root namespace)
- **Lines**: 239 (1 line)
- **Notes**: none

### `syntax qexpCoeffManual`
- **Type**: `syntax (name := qexpCoeffManual) "qexp_coeff" ident num term : term`
- **What**: Term syntax `qexp_coeff qj n x`: a proof term of `…coeff n = x` for a user-supplied value x.
- **How**: Syntax declaration at root level; semantics in the term `elab_rules`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `elab_rules : term`
- **Visibility**: public (root namespace)
- **Lines**: 240 (1 line)
- **Notes**: none

### `elab_rules : term` (qexp_coeff)
- **Type**: term elaboration rules for `qexpCoeffAuto` and `qexpCoeffManual`
- **What**: Implements the `qexp_coeff` proof-producing term elaborator: dispatches on `qj`/`Delta` and auto/manual mode, calls the corresponding `foo`-family function, and returns the constructed proof term (with optional timing log). This is the user-facing entry point that turns e.g. `qexp_coeff qj 4` into a proof of `qj_qexpansion.coeff 4 = 864299970`.
- **How**: `Lean.Elab.Term` code; the manual form elaborates the value argument against ℤ with `elabTermEnsuringType` + `synthesizeSyntheticMVarsNoPostponing` + `instantiateMVars` before passing it to `fooWithValue`/`deltaFooWithValue` via `Lean.Meta.liftMetaM`.
- **Hypotheses**: Target identifier must be `qj` or `Delta`; in manual mode the supplied value must be correct.
- **Uses from project**: [`foo`, `fooWithValue`, `deltaFoo`, `deltaFooWithValue`, `reportTiming`, `qexpCoeffAuto` (syntax), `qexpCoeffManual` (syntax)]
- **Used by**: unused in file (exercised in Examples.lean)
- **Visibility**: public (root namespace)
- **Lines**: 242–279 (38 lines)
- **Notes**: Meta code >30 lines. Proofs produced depend on the `Lean.ofReduceBool` axiom.

### File Summary
- Total declarations: 32 (23 defs, 2 lemmas/theorems, 0 instances, 7 tactic/meta decls [4 syntax + 2 elab_rules blocks counted as 2 + note the 4 `foo`-family and `mkNativeDecideProofFor` defs are also meta-level but counted under defs])
- Key API (used by 3+ others): [`e4CoeffInt`, `e6CoeffInt`, `coeffArray`, `convArrayUpTo`, `sigmaPow` (2 direct but foundational), `deltaCoeffInt`, `qjCoeffInt`, `inverseOnePlusCoeffsUpTo`, `mkNativeDecideProofFor`, `reportTiming`]
- Unused declarations (not used by anything in this file): [`deltaOverQCoeffInt`, `qoverDeltaCoeffInt` (both consumed by link.lean), `elab_rules : command`, `elab_rules : term` (both consumed by Examples.lean)]
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [] (the two elab_rules blocks are 33 and 38 lines of meta code, not proofs)
