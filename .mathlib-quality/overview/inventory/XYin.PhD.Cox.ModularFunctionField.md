# XYin/PhD/Cox/ModularFunctionField.lean
Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/ModularFunctionField.lean
Project-internal imports: [`XYin.PhD.Cox.ModularPolynomial.Interpolation`] (plus `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`)

File purpose: upgrades Cox Theorem 11.9(ii) — every `Γ₀(N)` modular function is a rational function of `j` and `j(Nτ)` — from a guarded pointwise rational expression (`theorem_11_9_ii_pointwise`) to an equality of intermediate fields inside `FunctionField = FractionRing holomorphicFunctions` over the embedded copy of `ℂ(j)` (`RatFunc ℂ`). Declarations live in `Cox.UpperHalfPlaneFunctionField` (final theorem in `Cox`).

### `theorem levelJ_mdifferentiable`
- **Type**: `(N : ℕ+) : MDiff (levelJ N)`
- **What**: The function `τ ↦ j(Nτ)` is holomorphic (MDifferentiable) on the upper half-plane.
- **How**: Via mathlib's `UpperHalfPlane.mdifferentiable_iff`, reduces to differentiability of the corresponding function on the open half-plane, discharged by the project lemma `jN_differentiableAt`.
- **Hypotheses**: `N` a positive natural (as `ℕ+`, giving `NeZero N` for `jN_differentiableAt`).
- **Uses from project**: [`levelJ`, `jN_differentiableAt`]
- **Used by**: `levelJElement`
- **Visibility**: public
- **Lines**: 27–29 (proof 2 lines)
- **Notes**: none

### `def levelJElement`
- **Type**: `(N : ℕ+) : HolomorphicFunction`
- **What**: The holomorphic function `j(Nτ)` bundled as an element of the subring `HolomorphicFunction` of `ℍ → ℂ`.
- **How**: The subtype pair `⟨levelJ N, levelJ_mdifferentiable N⟩`.
- **Hypotheses**: none beyond `N : ℕ+`.
- **Uses from project**: [`levelJ`, `levelJ_mdifferentiable`, `HolomorphicFunction`]
- **Used by**: `evalJLevelHol`, `evalJLevelHol_apply`, `levelJFieldElement`, `evalJLevel_mem_jLevelFunctionField`, `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 32–33
- **Notes**: none

### `def evalJLevelHol`
- **Type**: `(N : ℕ+) : ℂ[X][Y] →+* HolomorphicFunction`
- **What**: Ring homomorphism evaluating a bivariate complex polynomial `P(X, Y)` at `X = j` and `Y = j(Nτ)` inside the ring of holomorphic functions on `ℍ`.
- **How**: `Polynomial.eval₂RingHom` applied to the coefficient map `evalJ : ℂ[X] →+* HolomorphicFunction` (evaluation at `j`) and the outer value `levelJElement N`.
- **Hypotheses**: none beyond `N : ℕ+`.
- **Uses from project**: [`evalJ`, `levelJElement`, `HolomorphicFunction`]
- **Used by**: `evalJLevelHol_apply`, `evalJLevel`, `represents_evalJLevel_of`
- **Visibility**: public
- **Lines**: 36–37
- **Notes**: none

### `theorem evalJLevelHol_apply`
- **Type**: `(N : ℕ+) (P : ℂ[X][Y]) (τ : ℍ) : (evalJLevelHol N P).1 τ = P.evalEval (j τ) (levelJ N τ)`
- **What**: The bundled bivariate evaluation agrees pointwise with the plain complex-number evaluation `P(j(τ), j(Nτ))` at every point `τ` of the upper half-plane.
- **How**: Applies the point-evaluation ring hom `evaluation τ` and commutes it through `Polynomial.eval₂` via `Polynomial.hom_eval₂`; the composite `evaluation τ ∘ evalJ` is identified with `Polynomial.evalRingHom (j τ)` by `Polynomial.ringHom_ext` and the project lemma `evalJ_apply`, then `Polynomial.eval₂_evalRingHom` finishes.
- **Hypotheses**: none.
- **Uses from project**: [`evalJLevelHol`, `evaluation`, `evalJ`, `evalJ_apply`, `j`, `levelJ`, `levelJElement`]
- **Used by**: `represents_evalJLevel_of`
- **Visibility**: public
- **Lines**: 40–55 (proof 13 lines)
- **Notes**: `@[simp]`; key lemmas `Polynomial.hom_eval₂`, `Polynomial.eval₂_evalRingHom`

### `def evalJLevel`
- **Type**: `(N : ℕ+) : ℂ[X][Y] →+* FunctionField`
- **What**: Bivariate evaluation at `(j, j(Nτ))` landing in the ambient analytic function field (the fraction field of holomorphic functions), i.e. `evalJLevelHol` followed by the canonical embedding.
- **How**: Composition of `algebraMap HolomorphicFunction FunctionField` with `evalJLevelHol N`.
- **Hypotheses**: none.
- **Uses from project**: [`evalJLevelHol`, `HolomorphicFunction`, `FunctionField`]
- **Used by**: `represents_evalJLevel_of`, `evalJLevel_mem_jLevelFunctionField`, `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 58–59
- **Notes**: none

### `def levelJFieldElement`
- **Type**: `(N : ℕ+) : FunctionField`
- **What**: The element of the ambient analytic function field represented by the holomorphic function `j(Nτ)`.
- **How**: Image of `levelJElement N` under `algebraMap HolomorphicFunction FunctionField`.
- **Hypotheses**: none.
- **Uses from project**: [`levelJElement`, `HolomorphicFunction`, `FunctionField`]
- **Used by**: `jLevelFunctionField`, `evalJLevel_mem_jLevelFunctionField`
- **Visibility**: public
- **Lines**: 62–63
- **Notes**: none

### `def Represents`
- **Type**: `(f : ℍ → ℂ) (x : FunctionField) : Prop`
- **What**: A raw meromorphic function `f` represents a fraction-field element `x` if `x = a/b` for holomorphic `a, b` with `b ≠ 0` and `f(τ) = a(τ)/b(τ)` at every point where `b(τ) ≠ 0`. This bridges pointwise analysis and the abstract fraction field.
- **How**: Existential definition (no proof).
- **Hypotheses**: none (a `Prop`-valued predicate).
- **Uses from project**: [`HolomorphicFunction`, `FunctionField`]
- **Used by**: `represents_algebraMap`, `represents_unique`, `represents_evalJLevel_of`, `modularRepresentatives`
- **Visibility**: public
- **Lines**: 66–70
- **Notes**: none

### `theorem represents_algebraMap`
- **Type**: `(a : HolomorphicFunction) : Represents a.1 (algebraMap HolomorphicFunction FunctionField a)`
- **What**: A holomorphic function represents its own image in the fraction field.
- **How**: Take the representation `a/1`; both conditions are trivial (`div_one` handled by `simp`).
- **Hypotheses**: none.
- **Uses from project**: [`Represents`, `HolomorphicFunction`, `FunctionField`]
- **Used by**: `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 73–76 (proof 2 lines)
- **Notes**: none

### `theorem represents_unique`
- **Type**: `{f : ℍ → ℂ} {x y : FunctionField} (hx : Represents f x) (hy : Represents f y) : x = y`
- **What**: A meromorphic function has at most one representative in the analytic fraction field: representation is well-defined. This is the key rigidity fact — two fractions of holomorphic functions agreeing off their zero sets are equal.
- **How**: From `f = a/b = c/d` off the zero sets, derives the cross-multiplication identity `(ad − cb)·(bd) = 0` pointwise (each point is handled by case-split on vanishing of `b(τ)`, `d(τ)`, using `div_eq_div_iff`); since `holomorphicFunctions` here has no zero divisors as used, `mul_eq_zero` and `b, d ≠ 0` give `ad = cb`, and `IsFractionRing.to_map_eq_zero_iff` plus `div_eq_div_iff` in the fraction field conclude `a/b = c/d`.
- **Hypotheses**: both `x` and `y` are represented by the same `f`.
- **Uses from project**: [`Represents`, `HolomorphicFunction`, `FunctionField`]
- **Used by**: `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 79–105 (proof 26 lines)
- **Notes**: proof >10 lines; key lemmas `div_eq_div_iff`, `IsFractionRing.to_map_eq_zero_iff`, `mul_eq_zero`. Relies on the pointwise identity `(ad − cb)(bd) = 0` at EVERY `τ` — the zero-divisor step goes through `mul_eq_zero` in `HolomorphicFunction`, i.e. uses that this subring is a domain (identity theorem, supplied upstream via the `IsFractionRing` setup).

### `theorem represents_evalJLevel_of`
- **Type**: `(N : ℕ+) {f : ℍ → ℂ} (P Q : ℂ[X][Y]) (hQ : (fun τ ↦ Q.evalEval (j τ) (levelJ N τ)) ≠ 0) (hf : ∀ τ, Q.evalEval (j τ) (levelJ N τ) ≠ 0 → f τ = P.evalEval (j τ) (levelJ N τ) / Q.evalEval (j τ) (levelJ N τ)) : Represents f (evalJLevel N P / evalJLevel N Q)`
- **What**: A guarded pointwise rational expression `f = P(j, j_N)/Q(j, j_N)` (valid wherever the denominator is nonzero, with denominator not identically zero) yields the corresponding fraction-field representation.
- **How**: Exhibits the witnesses `evalJLevelHol N P` and `evalJLevelHol N Q`; nonvanishing of the denominator as a holomorphic function follows by contraposition through `evalJLevelHol_apply`, and the pointwise condition is exactly `hf` rewritten through `evalJLevelHol_apply`.
- **Hypotheses**: the denominator function `τ ↦ Q(j(τ), j(Nτ))` is not identically zero; `f` agrees with the quotient wherever it is defined.
- **Uses from project**: [`Represents`, `evalJLevel`, `evalJLevelHol`, `evalJLevelHol_apply`, `j`, `levelJ`, `HolomorphicFunction`]
- **Used by**: `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 109–124 (proof 10 lines)
- **Notes**: none

### `def modularRepresentatives`
- **Type**: `(N : ℕ+) : Set FunctionField`
- **What**: The set of ambient function-field elements that are represented by some level-`N` modular function for `Γ₀(N)` — the analytic incarnation of the modular function field, as a raw set.
- **How**: Set-builder over the existential `∃ f, IsGamma0ModularFunction N f ∧ Represents f x`.
- **Hypotheses**: none.
- **Uses from project**: [`IsGamma0ModularFunction`, `Represents`, `FunctionField`]
- **Used by**: `gamma0ModularFunctionField`, `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 127–128
- **Notes**: none

### `def gamma0ModularFunctionField`
- **Type**: `(N : ℕ+) : IntermediateField (RatFunc ℂ) FunctionField`
- **What**: The bundled field of level-`N` modular functions: the intermediate field of the analytic function field generated over the embedded copy of `ℂ(j)` (i.e. `RatFunc ℂ`) by all representatives of `Γ₀(N)` modular functions.
- **How**: `IntermediateField.adjoin (RatFunc ℂ) (modularRepresentatives N)`.
- **Hypotheses**: relies on the algebra structure `RatFunc ℂ → FunctionField` set up in `UpperHalfPlaneFunctionField.lean` (the `ratFuncEvalJ` embedding of `ℂ(j)`).
- **Uses from project**: [`modularRepresentatives`, `FunctionField`]
- **Used by**: `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 131–133
- **Notes**: none

### `def jLevelFunctionField`
- **Type**: `(N : ℕ+) : IntermediateField (RatFunc ℂ) FunctionField`
- **What**: The simple extension `ℂ(j)(j(Nτ))` inside the same ambient function field.
- **How**: `IntermediateField.adjoin (RatFunc ℂ) {levelJFieldElement N}`.
- **Hypotheses**: same ambient algebra structure as above.
- **Uses from project**: [`levelJFieldElement`, `FunctionField`]
- **Used by**: `evalJLevel_mem_jLevelFunctionField`, `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 136–137
- **Notes**: none

### `theorem evalJLevel_mem_jLevelFunctionField`
- **Type**: `(N : ℕ+) (P : ℂ[X][Y]) : evalJLevel N P ∈ jLevelFunctionField N`
- **What**: Every bivariate polynomial expression in `j` and `j_N` (image of `evalJLevel`) lies in the simple extension `ℂ(j)(j_N)`.
- **How**: Rewrites the composite via `Polynomial.hom_eval₂` so evaluation happens through `evalJFracPoly` in the function field, then inducts on `P` with `Polynomial.induction_on'`: sums by field closure under addition, monomials `c(X)·Y^n` since `c(j) ∈ ℂ(j)` is in the base field by `ratFuncEvalJ_algebraMap` and `j_N` is an adjoined generator (`IntermediateField.subset_adjoin`).
- **Hypotheses**: none.
- **Uses from project**: [`evalJLevel`, `jLevelFunctionField`, `evalJ`, `levelJElement`, `evalJFracPoly`, `levelJFieldElement`, `ratFuncEvalJ_algebraMap`, `HolomorphicFunction`, `FunctionField`]
- **Used by**: `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 140–158 (proof 17 lines)
- **Notes**: proof >10 lines; key lemmas `Polynomial.hom_eval₂`, `Polynomial.induction_on'`, `IntermediateField.subset_adjoin`. Two `change` steps exploit the definitional equality `evalJFracPoly = algebraMap ∘ evalJ`.

### `theorem theorem_11_9_ii` (namespace `Cox`)
- **Type**: `(N : ℕ+) : gamma0ModularFunctionField N = jLevelFunctionField N`
- **What**: Cox Theorem 11.9(ii) in bundled form: the field of `Γ₀(N)` modular functions equals the simple extension `ℂ(j)(j(Nτ))`, as intermediate fields of the analytic function field over `ℂ(j)`.
- **How**: Antisymmetry. (≤) Given a modular function `f` representing `x`, the pointwise theorem `theorem_11_9_ii_pointwise` produces polynomials `P, Q` with `f = P(j,j_N)/Q(j,j_N)`; `represents_unique` identifies `x` with `evalJLevel N P / evalJLevel N Q` (via `represents_evalJLevel_of`), which lies in `ℂ(j)(j_N)` by `evalJLevel_mem_jLevelFunctionField` and closure under division. (≥) `j_N` itself is a `Γ₀(N)` modular function (`levelJ_isGamma0ModularFunction`), so its representative lies in the modular field by `IntermediateField.subset_adjoin`.
- **Hypotheses**: none beyond `N : ℕ+`.
- **Uses from project**: [`gamma0ModularFunctionField`, `jLevelFunctionField`, `theorem_11_9_ii_pointwise`, `represents_unique`, `represents_evalJLevel_of`, `evalJLevel_mem_jLevelFunctionField`, `modularRepresentatives`, `levelJ`, `levelJ_isGamma0ModularFunction`, `represents_algebraMap`, `levelJElement`, `evalJLevel`]
- **Used by**: unused in file (terminal result)
- **Visibility**: public
- **Lines**: 165–178 (proof 13 lines)
- **Notes**: key lemmas `IntermediateField.adjoin_le_iff`, `le_antisymm`

### File Summary
- Total declarations: 15 (7 defs, 8 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): `levelJElement` (5), `evalJLevelHol` (3), `evalJLevel` (3), `Represents` (4)
- Unused declarations (not used by anything in this file): `theorem_11_9_ii` (terminal result)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [] (longest: `represents_unique` at 26 lines)
