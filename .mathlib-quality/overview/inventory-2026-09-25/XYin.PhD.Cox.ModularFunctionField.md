# Inventory: XYin/PhD/Cox/ModularFunctionField.lean  (186 lines)

Upgrades Cox Theorem 11.9 from the guarded pointwise predicates (`RationalIn`, `RationalInTwo`) to statements inside the codiscrete meromorphic field: 11.9(i) becomes "`f.toMeromorphicField ∈ range (algebraMap (RatFunc ℂ) FunctionField)`" and 11.9(ii) becomes the equality of intermediate fields `IntermediateField.adjoin ℂ(j) (range toMeromorphicField) = IntermediateField.adjoin ℂ(j) {j_N}`. The key device is `toMeromorphicField_eq_div_of`, which turns a guarded pointwise quotient into an honest field equality by passing to germs. This is the terminal file of the Cox function-field spine (imported only by `Section11BC`).

## Declarations

### `def Cox.UpperHalfPlaneFunctionField.levelJElement`
- **Type**: `(N : ℕ+) : HolomorphicFunction := ⟨levelJ N, levelJ_mdifferentiable N⟩`
- **What**: `j(Nτ)` as an element of the holomorphic subring.
- **How**: subtype constructor.
- **Hypotheses**: none.
- **Uses from project**: `HolomorphicFunction`, `levelJ`, `levelJ_mdifferentiable`
- **Used by**: `evalJLevelHol`, `evalJLevelHol_apply`, `levelJFieldElement`, `evalJLevel_mem_jLevelFunctionField`, `toMeromorphicField_levelJModularFunction`
- **Visibility**: public
- **Lines**: 28–29
- **Notes**: Parallel to `jElement` (UpperHalfPlaneFunctionField.lean:44). Also equals `rightCosetFunction N (baseRightCoset N)` (Arithmetic.lean:57–62 proves `f.1 = levelJ m` for that element) — two holomorphic-subring names for the same function.

### `def Cox.UpperHalfPlaneFunctionField.evalJLevelHol`
- **Type**: `(N : ℕ+) : ℂ[X][Y] →+* HolomorphicFunction := Polynomial.eval₂RingHom evalJ (levelJElement N)`
- **What**: Bivariate evaluation `P(X, Y) ↦ P(j, j_N)` into holomorphic functions.
- **How**: `Polynomial.eval₂RingHom` over the coefficient hom `evalJ`.
- **Hypotheses**: none.
- **Uses from project**: `evalJ`, `levelJElement`, `HolomorphicFunction`
- **Used by**: `evalJLevelHol_apply`, `evalJLevel`, `toMeromorphicField_eq_evalJLevel_div_of`, `evalJLevel_mem_jLevelFunctionField`
- **Visibility**: public
- **Lines**: 32–33
- **Notes**: No external use.

### `@[simp] theorem Cox.UpperHalfPlaneFunctionField.evalJLevelHol_apply`
- **Type**: `(N : ℕ+) (P : ℂ[X][Y]) (τ : ℍ) : (evalJLevelHol N P).1 τ = P.evalEval (j τ) (levelJ N τ)`
- **What**: Pointwise, bivariate evaluation substitutes `j τ` and `j(Nτ)`.
- **How**: `Polynomial.hom_eval₂` with `evaluation τ`, the inline fact `(evaluation τ).comp evalJ = Polynomial.evalRingHom (j τ)` (from `evalJ_apply`), and `Polynomial.eval₂_evalRingHom` (`Mathlib/Algebra/Polynomial/Bivariate.lean:159`).
- **Hypotheses**: none.
- **Uses from project**: `evalJLevelHol`, `evaluation`, `evalJ`, `evalJ_apply`, `levelJElement`, `levelJ`, `j`
- **Used by**: `toMeromorphicField_eq_evalJLevel_div_of`
- **Visibility**: public
- **Lines**: 37–44, proof body ≈ 6 lines
- **Notes**: Lines 41–42 re-prove `evaluation_comp_evalJ` (also at Arithmetic.lean:69–72; missing lemma).

### `def Cox.UpperHalfPlaneFunctionField.evalJLevel`
- **Type**: `(N : ℕ+) : ℂ[X][Y] →+* FunctionField := (algebraMap HolomorphicFunction FunctionField).comp (evalJLevelHol N)`
- **What**: Bivariate evaluation landing in the meromorphic field.
- **How**: composition.
- **Hypotheses**: none.
- **Uses from project**: `FunctionField`, `HolomorphicFunction`, `evalJLevelHol`
- **Used by**: `toMeromorphicField_eq_evalJLevel_div_of`, `evalJLevel_mem_jLevelFunctionField`, `toMeromorphicField_mem_jLevelFunctionField`
- **Visibility**: public
- **Lines**: 47–48
- **Notes**: Parallel to `evalJFracPoly`. With the `Algebra (RatFunc ℂ) FunctionField` instance it equals `Polynomial.aeval (levelJFieldElement N) ∘ Polynomial.map (algebraMap ℂ[X] (RatFunc ℂ))` (not stated).

### `def Cox.UpperHalfPlaneFunctionField.levelJFieldElement`
- **Type**: `(N : ℕ+) : FunctionField := algebraMap HolomorphicFunction FunctionField (levelJElement N)`
- **What**: `j_N` as a field element (the generator of `ℂ(j)(j_N)`).
- **How**: `algebraMap`.
- **Hypotheses**: none.
- **Uses from project**: `FunctionField`, `HolomorphicFunction`, `levelJElement`
- **Used by**: `jLevelFunctionField`, `evalJLevel_mem_jLevelFunctionField`, `toMeromorphicField_levelJModularFunction`
- **Visibility**: public
- **Lines**: 51–52
- **Notes**: Equals `rightCosetRoot N (baseRightCoset N)` (Arithmetic.lean:97 `α`) and `(levelJModularFunction N).toMeromorphicField` (line 162) — three names for one element.

### `theorem Cox.UpperHalfPlaneFunctionField.toMeromorphicField_eq_div_of`
- **Type**: `{Γ : Subgroup (GL (Fin 2) ℝ)} (f : ModularFunction Γ) (a b : HolomorphicFunction) (hb : b ≠ 0) (hf : ∀ τ, b.1 τ ≠ 0 → f τ = a.1 τ / b.1 τ) : f.toMeromorphicField = algebraMap HolomorphicFunction FunctionField a / algebraMap HolomorphicFunction FunctionField b`
- **What**: A guarded pointwise identity `f = a/b` (off the zeros of `b`) is an equality in the meromorphic field. This is the bridge from Cox's pointwise `RationalIn` conclusions to field membership.
- **How**: `b ≠ 0` in the field by injectivity of `holomorphicToMeromorphic`; identify `f.toMeromorphicField` with `ofMeromorphic f` (`toFun_injective`, `toFun_ofMeromorphic`, `toFun_toMeromorphicField`); then show `(f·b − a)·b = 0` as a germ by `Subtype.ext`, `Germ.coe_eq`, `filter_upwards` and the pointwise case split on `b τ = 0` (multiplying by `b` twice makes the identity hold at zeros of `b` too); conclude by `mul_eq_zero`, `sub_eq_zero`, `eq_div_iff`.
- **Hypotheses**: `b` nonzero as a holomorphic function; the guarded quotient identity for all `τ`.
- **Uses from project**: `ModularFunction`, `ModularFunction.toMeromorphicField`, `HolomorphicFunction`, `FunctionField`, `holomorphicToMeromorphic_injective`, `holomorphicToMeromorphic`, `MeromorphicField.ofMeromorphic`, `ModularFunction.meromorphicOn`, `ModularFunction.meromorphicNFOn`, `MeromorphicField.toFun_injective`, `MeromorphicField.toFun_ofMeromorphic`, `ModularFunction.toFun_toMeromorphicField`
- **Used by**: `toMeromorphicField_eq_evalJLevel_div_of`, `toMeromorphicField_eq_ratFunc`
- **Visibility**: public
- **Lines**: 56–86, proof body ≈ 27 lines
- **Notes**: The germ-level unfolding (74–85: `Subtype.ext`, `change … Germ …`, `Germ.coe_eq`, `filter_upwards`) reaches into `MeromorphicOn.germRing` internals that `MeromorphicField.lean` otherwise encapsulates; a lemma `MeromorphicField.ofMeromorphic_mul`/`ofMeromorphic_sub` or `MeromorphicField.ofMeromorphic_eq_ofMeromorphic_of_eventuallyEq` (or `ofMeromorphic_eq_zero_of_forall_eq_zero`) in MeromorphicField.lean would make this ≈8 lines. Lines 61–65 (`hbmap`) are `hb ∘ holomorphicToMeromorphic_injective` after `map_zero` (one line via `Function.Injective.ne`). `hrep` (66–69) is a missing simp lemma `ModularFunction.ofMeromorphic_eq_toMeromorphicField`.

### `theorem Cox.UpperHalfPlaneFunctionField.toMeromorphicField_eq_evalJLevel_div_of`
- **Type**: `{Γ} (N : ℕ+) (f : ModularFunction Γ) (P Q : ℂ[X][Y]) (hQ : (fun τ ↦ Q.evalEval (j τ) (levelJ N τ)) ≠ 0) (hf : ∀ τ, Q.evalEval (j τ) (levelJ N τ) ≠ 0 → f τ = P.evalEval (j τ) (levelJ N τ) / Q.evalEval (j τ) (levelJ N τ)) : f.toMeromorphicField = evalJLevel N P / evalJLevel N Q`
- **What**: A `RationalInTwo f j (levelJ N)` witness gives the field identity `f = P(j, j_N)/Q(j, j_N)`.
- **How**: `toMeromorphicField_eq_div_of` with `a = evalJLevelHol N P`, `b = evalJLevelHol N Q`; `b ≠ 0` from `hQ` via `evalJLevelHol_apply`.
- **Hypotheses**: `Q(j, j_N)` nonzero as a function; the guarded quotient identity.
- **Uses from project**: `ModularFunction`, `levelJ`, `j`, `evalJLevel`, `evalJLevelHol`, `evalJLevelHol_apply`, `toMeromorphicField_eq_div_of`
- **Used by**: `toMeromorphicField_mem_jLevelFunctionField`
- **Visibility**: public
- **Lines**: 89–101, proof body ≈ 7 lines
- **Notes**: The hypotheses `hQ, hf` are exactly the components of `RationalInTwo f j (levelJ N)` (CuspData.lean:56); stating it as `(h : RationalInTwo f j (levelJ N)) : ∃ P Q, evalJLevel N Q ≠ 0 ∧ …` would let `toMeromorphicField_mem_jLevelFunctionField` avoid the `obtain`.

### `theorem Cox.UpperHalfPlaneFunctionField.toMeromorphicField_eq_ratFunc`
- **Type**: `(f : ModularFunction 𝒮ℒ) : ∃ r : RatFunc ℂ, algebraMap (RatFunc ℂ) FunctionField r = f.toMeromorphicField`
- **What**: Cox Theorem 11.9(i) in the ambient field: every level-one modular function lies in the embedded `ℂ(j)`.
- **How**: `theorem_11_9_i` gives `P, Q`; `evalJ Q ≠ 0` by `evalJ_injective`; `toMeromorphicField_eq_div_of` with `evalJ P`, `evalJ Q`; the witness is `algebraMap P / algebraMap Q ∈ RatFunc ℂ`, matched via `map_div₀` and `ratFuncEvalJ_algebraMap`.
- **Hypotheses**: `f` a bundled `SL₂(ℤ)` modular function.
- **Uses from project**: `ModularFunction`, `FunctionField`, `theorem_11_9_i` (ModularFunction.lean:431), `RationalIn` (unfolded), `evalJ`, `evalJ_injective`, `evalJ_apply`, `toMeromorphicField_eq_div_of`, `ratFuncEvalJ`, `ratFuncEvalJ_algebraMap`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 104–118, proof body ≈ 13 lines
- **Notes**: Terminal export; unused anywhere. Exact final form of 11.9(i): `∃ r : RatFunc ℂ, ratFuncEvalJ r = f.toMeromorphicField`, i.e. `f.toMeromorphicField ∈ (algebraMap (RatFunc ℂ) FunctionField).range` (mathlib `RingHom.mem_range` would state it as a `Set`/`Subring` membership). Project lemmas consumed (transitively): everything under `theorem_11_9_i` (see ModularFunction.lean inventory) plus `j_surjective` (via `evalJ_injective`), `holomorphicToMeromorphic_injective`, `MeromorphicField.toFun_injective`, `toFun_ofMeromorphic`, `ModularFunction.toFun_toMeromorphicField`, `RatFunc.liftRingHom` API.

### `def Cox.UpperHalfPlaneFunctionField.modularRepresentatives`
- **Type**: `(N : ℕ+) : Set FunctionField := Set.range (ModularFunction.toMeromorphicField (Γ := Gamma0 N))`
- **What**: The images of all bundled level-`N` modular functions in the meromorphic field.
- **How**: `Set.range`.
- **Hypotheses**: none.
- **Uses from project**: `FunctionField`, `ModularFunction.toMeromorphicField`
- **Used by**: `gamma0ModularFunctionField`, `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 121–123
- **Notes**: Not shown to be a subfield (no `add/mul/inv` on `ModularFunction`), which is why 11.9(ii) is stated for the *generated* field; see Observations.

### `def Cox.UpperHalfPlaneFunctionField.gamma0ModularFunctionField`
- **Type**: `(N : ℕ+) : IntermediateField (RatFunc ℂ) FunctionField := IntermediateField.adjoin (RatFunc ℂ) (modularRepresentatives N)`
- **What**: The subfield of the meromorphic field generated over `ℂ(j)` by all level-`N` modular functions.
- **How**: mathlib `IntermediateField.adjoin` (`Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean`).
- **Hypotheses**: none.
- **Uses from project**: `FunctionField`, `modularRepresentatives`, `instance Algebra (RatFunc ℂ) FunctionField`
- **Used by**: `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 126–128
- **Notes**: —

### `def Cox.UpperHalfPlaneFunctionField.jLevelFunctionField`
- **Type**: `(N : ℕ+) : IntermediateField (RatFunc ℂ) FunctionField := IntermediateField.adjoin (RatFunc ℂ) {levelJFieldElement N}`
- **What**: The simple extension `ℂ(j)(j_N)`.
- **How**: `IntermediateField.adjoin` of a singleton.
- **Hypotheses**: none.
- **Uses from project**: `FunctionField`, `levelJFieldElement`
- **Used by**: `evalJLevel_mem_jLevelFunctionField`, `toMeromorphicField_mem_jLevelFunctionField`, `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 131–132
- **Notes**: Written as `adjoin F {α}` rather than the scoped notation `F⟮α⟯`; the `adjoin_simple_*` simp set (`IntermediateField.adjoin_simple_le_iff`, `Adjoin/Defs.lean:583`; `mem_adjoin_simple_iff`, `Adjoin/Basic.lean:61`) is keyed to that notation and would shorten lines 148–149 and 182–184.

### `theorem Cox.UpperHalfPlaneFunctionField.evalJLevel_mem_jLevelFunctionField`
- **Type**: `(N : ℕ+) (P : ℂ[X][Y]) : evalJLevel N P ∈ jLevelFunctionField N`
- **What**: Every bivariate polynomial in `j, j_N` lies in `ℂ(j)(j_N)`.
- **How**: Rewrite `evalJLevel N P` as `Polynomial.eval₂ evalJFracPoly (levelJFieldElement N) P` (`Polynomial.hom_eval₂`), expand with `Polynomial.eval₂_eq_sum`, and use `IntermediateField.sum_mem`, `mul_mem`, `algebraMap_mem` (coefficients via `ratFuncEvalJ_algebraMap`) and `Subfield.pow_mem` of `subset_adjoin`.
- **Hypotheses**: none.
- **Uses from project**: `evalJLevel`, `jLevelFunctionField`, `evalJ`, `levelJElement`, `evalJFracPoly`, `levelJFieldElement`, `ratFuncEvalJ_algebraMap`
- **Used by**: `toMeromorphicField_mem_jLevelFunctionField` (twice)
- **Visibility**: public
- **Lines**: 135–149, proof body ≈ 13 lines
- **Notes**: Mathlib composition: `evalJLevel N P = Polynomial.aeval (levelJFieldElement N) (P.map (algebraMap ℂ[X] (RatFunc ℂ)))`, and `aeval x q ∈ Algebra.adjoin F {x}` (`Algebra.adjoin_singleton_eq_range_aeval`, `Mathlib/RingTheory/Adjoin/Polynomial/Basic.lean:52`) `≤ F⟮x⟯` (`IntermediateField.algebra_adjoin_le_adjoin`, `Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean:30`) — a 2–3 line proof.

### `theorem Cox.UpperHalfPlaneFunctionField.toMeromorphicField_mem_jLevelFunctionField`
- **Type**: `(N : ℕ+) (f : ModularFunction (Gamma0 N)) : f.toMeromorphicField ∈ jLevelFunctionField N`
- **What**: Every bundled level-`N` modular function lies in `ℂ(j)(j_N)` — the substantive half of 11.9(ii).
- **How**: `theorem_11_9_ii_pointwise N f : RationalInTwo f j (levelJ N)` gives `P, Q`; `toMeromorphicField_eq_evalJLevel_div_of` rewrites `f` as `evalJLevel P / evalJLevel Q`; `IntermediateField.div_mem` with `evalJLevel_mem_jLevelFunctionField`.
- **Hypotheses**: `f` bundled level-`N` modular function.
- **Uses from project**: `ModularFunction`, `theorem_11_9_ii_pointwise` (Interpolation.lean:488), `RationalInTwo` (unfolded), `toMeromorphicField_eq_evalJLevel_div_of`, `jLevelFunctionField`, `evalJLevel_mem_jLevelFunctionField`
- **Used by**: `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 152–158, proof body ≈ 4 lines
- **Notes**: Mathlib `IntermediateField.mem_adjoin_simple_iff (x) : x ∈ F⟮α⟯ ↔ ∃ r s : F[X], x = aeval α r / aeval α s` (`Adjoin/Basic.lean:61`) is literally the target shape once `evalJLevel` is expressed through `aeval`.

### `@[simp] theorem Cox.UpperHalfPlaneFunctionField.toMeromorphicField_levelJModularFunction`
- **Type**: `(N : ℕ+) : (levelJModularFunction N).toMeromorphicField = levelJFieldElement N`
- **What**: The bundled `j_N`'s field element is the holomorphic germ of `levelJ N`.
- **How**: `MeromorphicField.toFun_injective`, `ModularFunction.toFun_toMeromorphicField`, `toFun_holomorphicToMeromorphic`, `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `levelJModularFunction`, `levelJFieldElement`, `levelJElement`, `MeromorphicField.toFun_injective`, `ModularFunction.toFun_toMeromorphicField`, `holomorphicToMeromorphic`, `toFun_holomorphicToMeromorphic`
- **Used by**: `theorem_11_9_ii`
- **Visibility**: public
- **Lines**: 162–169, proof body ≈ 6 lines
- **Notes**: Line 166 uses `change (levelJModularFunction N : ℍ → ℂ) = …` instead of `coe_levelJModularFunction` (LevelJ.lean:322, `@[simp]`, otherwise unused). Same skeleton as `algebraMap_jElement` (UpperHalfPlaneFunctionField.lean:48–52); a general lemma `ModularFunction.toMeromorphicField_eq_algebraMap_of_mdifferentiable (f : ModularFunction Γ) (hf : MDiff f) : f.toMeromorphicField = algebraMap HolomorphicFunction FunctionField ⟨f, hf⟩` covers both.

### `theorem Cox.theorem_11_9_ii`
- **Type**: `(N : ℕ+) : gamma0ModularFunctionField N = jLevelFunctionField N`
- **What**: Cox Theorem 11.9(ii) as an equality of intermediate fields of the meromorphic function field over `ℂ(j)`: the field generated by all level-`N` modular functions is `ℂ(j)(j_N)`.
- **How**: `le_antisymm`; `≤` by `IntermediateField.adjoin_le_iff` (`Adjoin/Defs.lean:55`) and `toMeromorphicField_mem_jLevelFunctionField`; `≥` by `adjoin_le_iff`, `Set.singleton_subset_iff`, and `subset_adjoin` (`Adjoin/Defs.lean:331`) with the witness `levelJModularFunction N` via `toMeromorphicField_levelJModularFunction`.
- **Hypotheses**: none.
- **Uses from project**: `gamma0ModularFunctionField`, `jLevelFunctionField`, `modularRepresentatives`, `toMeromorphicField_mem_jLevelFunctionField`, `levelJModularFunction`, `toMeromorphicField_levelJModularFunction`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 176–184, proof body ≈ 7 lines
- **Notes**: Terminal export; unused anywhere. Exact final form: `IntermediateField.adjoin (RatFunc ℂ) (Set.range (ModularFunction.toMeromorphicField (Γ := Gamma0 N))) = IntermediateField.adjoin (RatFunc ℂ) {algebraMap HolomorphicFunction MeromorphicField ⟨levelJ N, _⟩}` inside `MeromorphicOn.germRing ℂ upperHalfPlaneSet` with the `Algebra (RatFunc ℂ) _` structure from `ratFuncEvalJ` (`Y ↦ j`). It does **not** assert that `modularRepresentatives N` is itself a subfield or equals the carrier of `jLevelFunctionField N` (migration doc, lines 15–17). Project lemmas consumed (transitively): `theorem_11_9_ii_pointwise` → {`CuspData.of_modularFunction`, `rationalInTwo_of_interpolation_coeff_rational`, `interpolation_coeff_cuspData`, `CuspData.rationalInJ`, `recoveryFormula`, `interpolationAt`, `exists_commonDenominator_polynomialEval_of_natDegree_lt`, `modularPolynomialC`/`specializeY`, `evalJ_injective`, `rightCosetFunction`, `rightCosetTranslate`, `coxMatrixEquivRightCosets`} (Interpolation.lean, CoxMatrices); the field layer {`toMeromorphicField_eq_div_of`, `evalJLevel_mem_jLevelFunctionField`, `ratFuncEvalJ_algebraMap`, `levelJModularFunction`, `levelJ_mdifferentiable`, `holomorphicToMeromorphic_injective`, `MeromorphicField.toFun_injective`/`toFun_ofMeromorphic`, `ModularFunction.toFun_toMeromorphicField`}; and, via 11.9(i) inside `interpolation_coeff_cuspData … .rationalInJ`, the entire ModularFunction.lean chain.

## File Summary
- Total declarations: 15 (7 defs, 8 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `levelJElement` (5), `evalJLevelHol` (4), `evalJLevel` (3), `levelJFieldElement` (3), `jLevelFunctionField` (3)
- Unused declarations (not used by anything in this file): `toMeromorphicField_eq_ratFunc` (unused everywhere; terminal), `theorem_11_9_ii` (unused everywhere; terminal)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest `toMeromorphicField_eq_div_of` 27)

## Observations

### Mathlib API candidates
- `evalJLevel_mem_jLevelFunctionField` (135–149): replaceable by `Algebra.adjoin_singleton_eq_range_aeval` (`Mathlib/RingTheory/Adjoin/Polynomial/Basic.lean:52`) + `IntermediateField.algebra_adjoin_le_adjoin` (`Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean:30`) once `evalJLevel N P` is expressed as `Polynomial.aeval (levelJFieldElement N) (P.map (algebraMap ℂ[X] (RatFunc ℂ)))` (needs a lemma `evalJLevel_eq_aeval_map`, provable from `Polynomial.hom_eval₂` + `ratFuncEvalJ_algebraMap`).
- `toMeromorphicField_mem_jLevelFunctionField` (152–158): the target is `IntermediateField.mem_adjoin_simple_iff` (`Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:61`) verbatim in `aeval` form.
- `theorem_11_9_ii` second inclusion (182–184): `IntermediateField.adjoin_simple_le_iff` (`Adjoin/Defs.lean:583`) + `subset_adjoin` — needs `F⟮α⟯` notation in `jLevelFunctionField`.
- `toMeromorphicField_eq_ratFunc` conclusion is `f.toMeromorphicField ∈ (algebraMap (RatFunc ℂ) FunctionField).range` (`RingHom.mem_range`) or, more uniformly with 11.9(ii), `f.toMeromorphicField ∈ (⊥ : IntermediateField (RatFunc ℂ) FunctionField)` (`IntermediateField.mem_bot : x ∈ ⊥ ↔ x ∈ Set.range (algebraMap F E)`, `Adjoin/Defs.lean`; name grep-verified in mathlib as `IntermediateField.mem_bot`? — not re-verified this session, treat as candidate). Stating 11.9(i) as `gamma0ModularFunctionField 1 = ⊥` would make (i) and (ii) uniform.
- `toMeromorphicField_eq_div_of` (56–86): no mathlib analogue (searched `MeromorphicOn.germRing` API in `Mathlib/`: absent — the germ ring is project-local, MeromorphicField.lean:231). The `Germ.coe_eq`/`filter_upwards` step is mathlib `Filter.Germ.coe_eq`.
- `evalJLevelHol` = `Polynomial.eval₂RingHom` over `evalJ`: with `Algebra ℂ[X] HolomorphicFunction := evalJ.toAlgebra` this is `Polynomial.aeval (levelJElement N)` and `evalJLevelHol_apply` follows from `Polynomial.eval₂_evalRingHom` (`Bivariate.lean:159`, already used).

### Missing API / repeated patterns
- `evaluation_comp_evalJ` (41–42 here, Arithmetic.lean:69–72): missing lemma in UpperHalfPlaneFunctionField.lean.
- `MeromorphicField.ofMeromorphic_eq_of_eventuallyEq`/`ofMeromorphic_mul`/`ofMeromorphic_sub` (or `ModularFunction.toMeromorphicField_mul_algebraMap_eq …`): the raw germ manipulation at 74–85 should live in MeromorphicField.lean; the same `Subtype.ext; Germ.coe_eq; filter_upwards` idiom is used at FieldAction.lean:120–126 and 141–145.
- `ModularFunction.ofMeromorphic_eq_toMeromorphicField` (66–69 `hrep`): missing simp lemma in ModularFunctions/Basic.lean.
- `ModularFunction.toMeromorphicField_eq_algebraMap_of_mdifferentiable`: would subsume `toMeromorphicField_levelJModularFunction` (162–169) and `algebraMap_jElement` (UpperHalfPlaneFunctionField.lean:48–52).
- `HolomorphicFunction` ext lemma (97–100 `funext τ; simpa … congrArg (fun g ↦ g.1 τ)`): see UpperHalfPlaneFunctionField inventory.
- Three names for `j_N` in the field: `levelJFieldElement N`, `(levelJModularFunction N).toMeromorphicField`, `rightCosetRoot N (baseRightCoset N)` — only the first two are related by a lemma (162); `Arithmetic.lean:57–62` re-derives the third relation by hand.
- **Mathematical gap (not a bug)**: `modularRepresentatives N` is never shown closed under `+, *, ⁻¹`, so 11.9(ii) is about the *generated* field. Closing this needs ring/field operations on `ModularFunction Γ` (normal-form-compatible `add`/`mul`/`inv`, i.e. `toMeromorphicField` as a ring hom with `range` a subfield) — this is the natural next API for ModularFunctions/Basic.lean and would upgrade `theorem_11_9_ii` to `Set.range toMeromorphicField = (jLevelFunctionField N : Set _)`.

### Junk candidates
- None dead. `toMeromorphicField_eq_ratFunc` and `theorem_11_9_ii` are terminal exports (unused, expected). `evalJLevelHol`, `evalJLevel`, `levelJFieldElement`, `modularRepresentatives` are used only in this file — fine for a terminal file.
- Import `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs` (line 6) is enough for `adjoin`, but `IntermediateField.div_mem`, `sum_mem`, `pow_mem` come through it; OK.

### Moral duplicates within this batch
- `toMeromorphicField_levelJModularFunction` (162) ≈ `algebraMap_jElement` (UpperHalfPlaneFunctionField.lean:48): identical `toFun_injective` + unfolding proof for `j_N` vs `j`.
- `levelJElement`/`evalJLevelHol`/`evalJLevel`/`levelJFieldElement` (28–52) ≈ `jElement`/`evalJ`/`evalJFracPoly` (UpperHalfPlaneFunctionField.lean:44–88): the same three-stage embedding pattern, once for `ℂ[X]` and once for `ℂ[X][Y]`.
- `evalJLevelHol_apply` (37–44) ≈ `evalJ_apply` (UpperHalfPlaneFunctionField.lean:63–73): both are `hom_eval₂` + "evaluation commutes with the coefficient hom".
- `toMeromorphicField_eq_ratFunc` (104) and `toMeromorphicField_eq_evalJLevel_div_of` (89) both instantiate `toMeromorphicField_eq_div_of` after unfolding a `RationalIn`/`RationalInTwo`.

### Generalization notes
- `toMeromorphicField_eq_div_of` (56–86) is stated for `ModularFunction Γ` but uses only `f.meromorphicOn`/`f.meromorphicNFOn` and `toFun_toMeromorphicField`: it holds for any `x : MeromorphicField` with `g := MeromorphicField.toFun x` (`toFun_ofMeromorphic (meromorphicNFOn_toFun x)`), i.e. `MeromorphicField.eq_div_of_forall (x : MeromorphicField) (a b : HolomorphicFunction) (hb) (h : ∀ τ, b.1 τ ≠ 0 → toFun x τ = a.1 τ / b.1 τ) : x = algebraMap a / algebraMap b`. Further, `a, b` need only be meromorphic representatives, not holomorphic, with the same proof.
- `evalJLevel_mem_jLevelFunctionField` and `toMeromorphicField_mem_jLevelFunctionField` never use that the generator is `j_N`; they are "`aeval α q ∈ F⟮α⟯`" and "a guarded quotient of two `aeval α` values lies in `F⟮α⟯`" for any `α`.
- `theorem_11_9_ii` uses no property of `N` beyond the two inclusions; the same proof shape gives "`adjoin F (range φ) = F⟮α⟯` whenever `range φ ⊆ F⟮α⟯` and `α ∈ range φ`" — a two-line general lemma (`IntermediateField.adjoin_range_eq_adjoin_simple_of …`) that would make `theorem_11_9_ii` a one-liner.
