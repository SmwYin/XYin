# Cleanup report — Cox §11.B–C cluster (sandbox `coxc`), 2026-09-26

## 1. Final build
`lake build` (targets `XYin`, `XYinTest`) in SB:
```
✔ [3709/3710] Built XYin (4.4s)
Build completed successfully (3710 jobs).
```
No errors; no warnings in owned files (the only new linter warning, a flexible `simp at` in
SingularModuli, was fixed). No `sorry`/`admit`/`native_decide`/`maxHeartbeats` introduced.

## 2. Files changed (lines before → after); no files added or deleted, `XYin.lean` untouched
| file | before | after |
|---|---|---|
| Cox/ModularFunction/CuspData.lean | 154 | 220 |
| Cox/ModularFunction.lean | 439 | 336 |
| Cox/ModularPolynomial/AnalyticSupport.lean | 96 | 126 |
| Cox/ModularPolynomial/Construction.lean | 379 | 413 |
| Cox/ModularPolynomial/Interpolation.lean | 498 | 340 |
| Cox/ModularPolynomial/Irreducibility.lean | 141 | 134 |
| Cox/Arithmetic.lean | 346 | 254 |
| Cox/SingularModuli.lean | 238 | 166 |
| Cox/UpperHalfPlaneFunctionField.lean | 264 | 255 |
| Cox/ModularFunctionField.lean | 186 | 195 |
| Cox/ModularPolynomial.lean (umbrella) | 16 | 17 |
| Cox/Section11BC.lean (umbrella) | 22 | 33 |
| Cox/CoxMatrices.lean (umbrella) | 14 | 16 |
| **total** | **3098** | **2505** (−593) |

Import changes (owned files only): Construction `+Mathlib.LinearAlgebra.Lagrange`;
AnalyticSupport `+Mathlib.Algebra.Polynomial.Lifts, +ModularFunctions.FieldAction`;
Cox/ModularFunction `+ModularFunctions.FieldAction`; UHPFF `−FieldAction, −JInvariant`
(transitive) `+ModularPolynomial.AnalyticSupport`; MFF `Adjoin.Defs → Adjoin.Algebra`;
Arithmetic `+Cox.ModularFunctionField`.

## 3. Done items
### Task 1 — A15 pipeline dedupe
- `LevelOneCuspData.of_widthM` (CuspData.lean): meromorphic on ℍ + `SL₂(ℤ)`-invariant + meromorphic
  width-`m` cusp function ⇒ `LevelOneCuspData`. Replaces `coxPhiFunction_coeff_widthOne_…` +
  `interpolation_coeff_widthOne_…_aux` + the hand-built 3-component proof of
  `interpolation_coeff_cuspData` (now 4 lines).
- Generic coefficient closure (AnalyticSupport): `Polynomial.coeff_finset_prod_mem` (subsemiring,
  via mathlib `Polynomial.lifts`/`lifts_iff_coeff_lifts`), `Polynomial.coeff_X_sub_C_mem`,
  `Polynomial.coeff_prod_X_sub_C_mem`; `Cox.cuspMeromorphicSubring h : Subring (ℍ → ℂ)` (+`mem_` iff);
  instantiated as `coxNodal_coeff_cuspMeromorphicAt` / `coxNodal_coeff_mdifferentiable`
  (any `s : Finset (CoxMatrix m)`, with `holomorphicFunctions` for the MDiff twin).
- Deleted the twins: AnalyticSupport `coxLinearFactor_coeff_cuspMeromorphicAt`,
  `polynomial_prod_coeff_cuspMeromorphicAt` (public, only used in my files); Interpolation private
  `coxRoot_mdifferentiable_aux`, `coxLinearFactor_coeff_mdifferentiable_aux`,
  `polynomial_prod_coeff_mdifferentiable_aux`, `interpolationRootProduct(Aux, _coeff_mdifferentiable_aux,
  _coeff_cuspMeromorphicAt_aux)`, `rightCosetTranslate_cuspMeromorphicAt_aux`,
  `interpolationFunction_coeff_apply_aux`, `interpolation_coeff_eq_function_coeff_aux` (merged into
  one `interpolation_coeff_eq_aux`), `interpolation_coeff_widthOne_cuspMeromorphicAt_aux`;
  Construction's 25-line Vieta proof of `coxPhiFunction_coeff_mdifferentiable` and inline
  `hcoset/hroot`; UHPFF private `rightCosetEval_mdifferentiable`.
- New public: `rightCosetTranslate_cuspMeromorphicAt` (was private in Interpolation),
  `rightCosetEval_mdifferentiable`, `coxRoot_mdifferentiable`, `rightCosetEval_baseRightCoset`,
  `meromorphicAt_comp_ofComplex_of_mdifferentiable`, `coxPhiFunction_coeff_cuspData`.
- `periodic_comp_of_slashInvariant_one` moved AnalyticSupport → CuspData (same name/statement, still
  reachable by IntegralDescent); 12-line SlashInvariantForm adapter → 2-line
  `periodic_comp_sl2_of_gamma0_invariant 1 _ 1`.
### Task 2 — bivariate layer (Construction)
- `specializeY_eval`, `diagonal_map`, `eval_swap`, `diagonal_eval₂` were already one-line wrappers of
  `map_evalRingHom_eval` / `map_mapRingHom_eval_map` / `aevalAeval_swap` / `hom_eval₂`; kept (used by
  Classification, DiagonalLaurent, Arithmetic, SingularModuli; `diagonal`/`map` are defs, so the
  mathlib lemmas do not rewrite them directly).
- Added `BivariatePolynomial.eval_eq_evalEval` (rfl bridge; deliberately NOT `@[simp]` so simp
  normal forms in non-owned files do not change), `derivative_specializeY`; together they replace
  the private bridge `modularPolynomialC_derivative_evalEval` (Interpolation, deleted).
- Added `BivariatePolynomial.mapRingHom` (abbrev) + `coe_mapRingHom` (simp), `map_neg`, `map_sub`.
- `modularPolynomial_map_complex_swap` (Arithmetic) used at the three former sites
  (`modularPolynomial_dvd_swap`, `theorem_11_18_iii` — the 7-line `map_neg`/`change` detour is now
  one `rwa` — and `modularPolynomial_three`, now a 2-line `rw`).
- `diagonal_coeff_one` moved Arithmetic → Construction as public
  `BivariatePolynomial.diagonal_coeff_one`, generalised `CommRing → CommSemiring`.
- `modularPolynomialC_eval_eq_zero_iff` (roots of `Φ_m(X, j τ)` are exactly `j(σ τ)`) and
  `modularPolynomialC_eval_act_j`; `modularPolynomialC_eval_levelJ_j` is now a 2-line corollary and
  the SingularModuli replay (`exists_nonsquare_modularPolynomialDiagonal_root`) is 2 lines.
### Task 3 — Lagrange
- `coxPhiAtJ_eq_nodal` (rfl); `coxPhiAtJ_monic := Lagrange.nodal_monic`,
  `coxPhiAtJ_natDegree := Lagrange.natDegree_nodal` (term mode).
- `eval_derivative_prod_X_sub_C_at` deleted; inlined at `recoveryFormula` and
  `modularDerivativeHolomorphic_apply` as `Lagrange.eval_nodal_derivative_eval_node_eq` + `eval_nodal`.
- `modularDerivativeHolomorphic_ne_zero`: 10 lines → 3 (`prod_ne_zero_iff`, `Finset.ne_of_mem_erase`,
  `rightCosetFunction_injective`; the separable-product route is not shorter).
- Tactic-mode defs `interpolationAtCosetsAux`, `interpolationFunctionAux`,
  `modularDerivativeHolomorphic` → term mode (`open Classical in` for the quotient index;
  `CoxMatrix` has `DecidableEq`). `interpolationAt` kept.
### Task 4 — Irreducibility
- `card_le_natDegree_of_injective_roots` now for any nonzero `p` (no `minpoly`/`IsIntegral`),
  `eq_minpoly_of_card_conjugates` concludes `p = minpoly F α` via
  `minpoly.unique_of_degree_le_degree_minpoly`.
- New public `modularPolynomialC_map_eq_minpoly` (`Φ_m` over `ℂ(Y)` is the minimal polynomial of the
  identity-coset conjugate); `modularPolynomialC_irreducibleInX` (public name/statement kept) is a
  corollary; private `modularPolynomialRatFunc_irreducible` merged away. Arithmetic uses the
  `= minpoly` form directly.
### Task 5 — Arithmetic
- `eq_or_eq_neg_of_associated_int_bivariate` replaced by general
  `Polynomial.eq_one_or_eq_neg_one_of_isUnit` / `Polynomial.eq_or_eq_neg_of_associated` (domains whose
  units are ±1; applied twice for ℤ[X][Y]).
- `aeval_base_eq_zero_of_forall_eval_eq_zero`: 41 → 7 lines (via `rightCosetRoot_baseRightCoset`,
  `evalJLevel_eq_aeval`, `holomorphicFunction_ext`); `modularPolynomial_dvd_swap` 38 → 17.
- `theorem_11_18_iv_degree`: 40 → 19 lines; `levelJ_diagonalFixedPoint` uses `levelJ_apply`
  (no `unfold levelJ jN`), `diagonalFixedPoint_scale_eq` stated with `natScaleUpperHalfPlane`.
- `theorem_11_18_i/ii` kept (headline aliases).
### Task 6 — SingularModuli
- `not_isSquare_of_between_sq_aux`: 14 → 4 lines via `Nat.not_exists_sq'`.
- Even/odd twins (56 lines) → one `exists_positive_nonsquare_det` (`B = 2b + e`, `e ∈ {0,1}` via
  `omega`, `k = AC − b(b+e)`, `det M_{k−b} = k² + (e+1)k`).
- `coxMatrix_act_eq_smul_aux`: 31 → 16 lines via `CoxMatrix.act_eq_smul_of_mul_eq`.
- `fixingMatrix_content_eq_one` uses `Matrix.rankTwoContent_fin_two_of`.
### Task 7 — CuspData
- Accessors (type of `CuspData` unchanged): `CuspData.meromorphicAt`, `.meromorphicOn`, `.slash_eq`,
  `.meromorphicAt_cuspFunction`, `.apply_smul`; level one: `LevelOneCuspData.slash_sl2`,
  `.apply_sl2_smul`, `.periodic`, `.meromorphicAt_cuspFunction_one`, `.of_widthM`; weight-zero
  helpers `Cox.slash_zero_eq_comp`, `Cox.slash_zero_eq_iff`; `polynomialIn_apply` (simp).
  All `.1/.2.1/.2.2` uses in owned files replaced.
- `j_levelOneCuspData := j_cuspData 1`; wrapper `periodic_comp_sl2` deleted (only used in
  Cox/ModularFunction.lean).
- Private duplicate `cuspFunction_mul_eventuallyEq` deleted: `CuspData.mul` now uses the EXISTING
  public `meromorphicAt_cuspFunction_mul` (LaurentQExpansion.lean:106, already in SB) — no new
  Laurent API needed.
### Task 8 — Cox/ModularFunction.lean
- New public helper `mdifferentiable_of_forall_mem_fd` (SL₂-invariant + MDiffAt on `ModularGroup.fd`
  ⇒ MDiff); `CuspData.exists_polynomial_clearing_poles` 19 → 5 lines.
- `exists_polynomial_clearing_poles_on_fd_aux` 44 → 25 (`choose`, `Finset.dvd_prod_of_mem`, `convert`);
  `CuspData.polynomialInJ_of_holomorphic` 45 → 20 (`induction … using Nat.strong_induction_on
  generalizing f`); `exists_const_poleOrder_sub_mul_pow_lt` 49 → 37; `CuspData.rationalInJ` 12 → 7;
  private `levelOne_invariant_apply` deleted (→ `apply_sl2_smul`); level-one `hper/hinv/hcusp`
  re-derivations replaced by the accessors.
- G-13/G-14: `meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq` and
  `exists_analyticAt_pow_succ_mul_of_meromorphicAt_of_analyticAt_zero` generalised from `ℂ` to any
  `NontriviallyNormedField 𝕜` with unchanged proofs (scratch-verified). The `𝕜 → E` form needs `•`
  rewrites → deferred.
- Retargeted `ModularFunction.j_mdifferentiable` → `_root_.j_mdifferentiable` in owned files (the
  JInvariant copy is flagged DELETE-ONE for the ModularFunctions worker).
### Task 9 — UpperHalfPlaneFunctionField
- `precompAlgEquiv := AlgEquiv.ofRingEquiv (precomp_ratFunc delta)`.
- `holomorphicFunction_ext` (Cox-specific name, no `@[ext]`, to avoid a clash with a future
  `UpperHalfPlane.HolomorphicFunction.ext`), `evaluation_apply` (simp), `evaluation_comp_evalJ`,
  `evalJ_X` (simp), `rightCosetFunction_apply` (simp); used in UHPFF, Irreducibility, Interpolation,
  MFF, Arithmetic.
- `evalJ_apply` 12 → 4 lines, `evalJ_injective` 9 → 4.
- Deleted dead trivial `ratFuncEvalJ_injective`, `algebraMap_jElement` (0 uses).
- Added `instance : IsScalarTower ℂ (RatFunc ℂ) FunctionField` (Prop, diamond-free; the other two
  towers need `Algebra ℂ HolomorphicFunction`, which does not exist).
- `precomp_ratFunc` via `IsLocalization.ringHom_ext`: tried, not shorter than the 2-line
  `RatFunc.induction_on` proof → kept.
### Task 10 — ModularFunctionField
- `evalJLevel_eq_aeval` (bivariate evaluation = `aeval (levelJFieldElement N)` over `ℂ(j)`);
  `evalJLevel_mem_jLevelFunctionField` 15 → 3 lines via `IntermediateField.algebra_adjoin_le_adjoin` +
  `Polynomial.aeval_mem_adjoin_singleton`.
- Three names of `j_N` related: `rightCosetFunction_baseRightCoset`, `rightCosetRoot_baseRightCoset`
  (+ existing `toMeromorphicField_levelJModularFunction`, now 4 lines); Arithmetic's re-derivation gone.
- NEW `gamma0ModularFunctionField_one : gamma0ModularFunctionField 1 = ⊥` (Thm 11.9(i), field form)
  from `theorem_11_9_ii 1`, `adjoin_simple_eq_bot_iff`, new `levelJElement_one`.
- `evalJLevelHol_apply` uses `evaluation_comp_evalJ`; `theorem_11_9_ii` uses `adjoin_simple_le_iff`.
### Task 11 — umbrellas
- Section11BC docstring rewritten: maps each Cox number to its Lean name, adds singular moduli
  (`singularModulus_isIntegral`) and Kronecker (`theorem_11_18_v`); ModularPolynomial umbrella
  mentions AnalyticSupport; CoxMatrices umbrella lists its three submodules.
### Task 12 — junk
- Deleted dead `coe_coxPhiFunction_coeff_modularFunction` (rfl, 0 uses), plus the items above.
  `by exact` → term mode (`modularPolynomialC_monic/_specializeY`, `coxPhiFunction_coeff_polynomialInJ`),
  double blank lines removed.

## 4. New public API
- `Polynomial.coeff_finset_prod_mem (S : Subsemiring R) (hP : ∀ i ∈ s, ∀ n, (P i).coeff n ∈ S) (n) : (∏ i ∈ s, P i).coeff n ∈ S`
- `Polynomial.coeff_X_sub_C_mem (S : Subring R) (ha : a ∈ S) (n) : (X - C a).coeff n ∈ S`
- `Polynomial.coeff_prod_X_sub_C_mem (S : Subring R) (hr : ∀ i ∈ s, r i ∈ S) (n) : (∏ i ∈ s, (X - C (r i))).coeff n ∈ S`
- `Polynomial.eq_one_or_eq_neg_one_of_isUnit`, `Polynomial.eq_or_eq_neg_of_associated` (units ±1)
- `Cox.cuspMeromorphicSubring h : Subring (ℍ → ℂ)`, `Cox.mem_cuspMeromorphicSubring`
- `Cox.slash_zero_eq_comp : f ∣[0] γ = fun τ ↦ f (γ • τ)`, `Cox.slash_zero_eq_iff : f ∣[0] γ = f ↔ ∀ τ, f (γ • τ) = f τ`
- `CuspData.meromorphicAt/meromorphicOn/slash_eq/apply_smul/meromorphicAt_cuspFunction`
- `LevelOneCuspData.slash_sl2/apply_sl2_smul/periodic/meromorphicAt_cuspFunction_one/of_widthM`
- `Cox.polynomialIn_apply` (simp)
- `Cox.mdifferentiable_of_forall_mem_fd`
- `Cox.meromorphicAt_comp_ofComplex_of_mdifferentiable`, `rightCosetTranslate_cuspMeromorphicAt`,
  `rightCosetEval_baseRightCoset : rightCosetEval m (baseRightCoset m) = levelJ m`,
  `rightCosetEval_mdifferentiable`, `coxRoot_mdifferentiable`, `coxNodal_coeff_cuspMeromorphicAt`,
  `coxNodal_coeff_mdifferentiable`
- `BivariatePolynomial.eval_eq_evalEval : eval Φ x y = Φ.evalEval y x`, `derivative_specializeY`,
  `mapRingHom`, `coe_mapRingHom`, `map_neg`, `map_sub`, `diagonal_coeff_one`
- `coxPhiAtJ_eq_nodal`, `coxPhiFunction_coeff_cuspData`, `modularPolynomialC_eval_eq_zero_iff`,
  `modularPolynomialC_eval_act_j`, `modularPolynomial_map_complex_swap`, `modularPolynomialC_map_eq_minpoly`
- UHPFF: `holomorphicFunction_ext`, `evaluation_apply`, `evaluation_comp_evalJ`, `evalJ_X`,
  `rightCosetFunction_apply`, instance `IsScalarTower ℂ (RatFunc ℂ) FunctionField`
- MFF: `levelJElement_one`, `rightCosetFunction_baseRightCoset`, `rightCosetRoot_baseRightCoset`,
  `evalJLevel_eq_aeval`, `gamma0ModularFunctionField_one`

## 5. Kept on purpose
- `coxPhiFunction_coeff_modularFunction` (bundled level-one `ModularFunction` for the Cox
  coefficients; genuine construction, still used), `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`
  (names Cox (11.19)), `toMeromorphicField_eq_ratFunc`, `theorem_11_18_i/ii`, `specializeY_ext`,
  `diagonal_map/eval_swap/diagonal_eval₂/specializeY_eval` (API wrappers, used outside or needed since
  `diagonal`/`map` are defs), `interpolationAt` (un-normalised).

## 6. Deferred / follow-ups
### Need the not-yet-merged Laurent-layer API (names reserved by the orchestrator)
- CuspData.lean: private `meromorphicAt_polynomial_eval` → `MeromorphicAt.polynomial_eval`; private
  `cuspFunction_polynomial_eval_eventuallyEq` and 3rd component of `CuspData.polynomialIn` →
  `meromorphicAt_cuspFunction_polynomial_eval` / `cuspFunction_comp_eventuallyEq`.
- Cox/ModularFunction.lean: private `cuspFunction_sub_const_mul_pow_eventuallyEq` →
  `cuspFunction_comp₂_eventuallyEq`; 3rd component of `cuspData_sub_const_mul_pow` →
  `meromorphicAt_cuspFunction_sub/const_mul/pow`; private `poleOrder_lt_of_neg_lt_meromorphicOrderAt`
  → `poleOrder_lt_iff`; `hForder/hGorder` in `exists_const_poleOrder_sub_mul_pow_lt` → `poleOrder_eq_iff`.
- AnalyticSupport: `cuspMeromorphicSubring.neg_mem'` → `meromorphicAt_cuspFunction_neg`; consider
  moving `Cox.cuspMeromorphicSubring` to LaurentQExpansion as a general subring.
- IntegralDescent (not mine): `polynomialIn_cuspMeromorphicAt_aux`/`laurentqExpansion_polynomialIn_j_aux`
  (:31–52) → `meromorphicAt_cuspFunction_polynomial_eval`/`laurentqExpansion_polynomial_eval`;
  `coxNegativeRoot_cuspMeromorphicAt_aux` (:177–183) → `(cuspMeromorphicSubring _).neg_mem
  (coxRoot_cuspMeromorphicAt m σ)`; `.2.2 1` at :33, :47 → `.meromorphicAt_cuspFunction_one`;
  :240–243 (width-one + periodic) → `(coxPhiFunction_coeff_cuspData m n).periodic`.
- DiagonalLaurent (not mine): `.2.2 1` at :30, :161, :179 → `CuspData.meromorphicAt_cuspFunction`;
  :152–185 twins of IntegralDescent → Laurent API.
### Need the not-yet-merged ModularFunctions API
- Construction `coxPhiFunction_coeff_modularFunction` (bdd_at_cusps' skeleton) →
  `ModularFunction.ofSL2ZHolomorphic`/`ofLevelOneHolomorphic` + `coxPhiFunction_coeff_cuspData`.
- MFF `toMeromorphicField_eq_div_of` (germ manipulation, 25 lines) →
  `MeromorphicField.ofMeromorphic_eq_of_eventuallyEq`/`ofMeromorphic_mul`/`toMeromorphicField_eq_ofMeromorphic`.
- If `UpperHalfPlane.HolomorphicFunction.ext` lands (FieldAction), replace
  `Cox.UpperHalfPlaneFunctionField.holomorphicFunction_ext`; if `ModularForm.SL_slash_zero_eq(_iff)`
  lands (NormalFormSlash), replace `Cox.slash_zero_eq_comp/iff`; if `sl2_mdifferentiable` moves to
  NormalFormSlash, drop the FieldAction imports of Cox/ModularFunction.lean and AnalyticSupport.
- `ModularFunction.j_mdifferentiable` (JInvariant) can be deleted: owned files now use
  `_root_.j_mdifferentiable` (remaining user outside my set: LatticeJ.lean:584).
### Edits outside my owned set (no new API needed)
- CoxMatrices/Basic.lean:530 (`rightCosetTranslate`) `hf.2.1 g₀` + `SL_slash_apply` → `hf.apply_smul`.
- CyclicSublattice/Classification.lean:185–186 → `rw [modularPolynomialC_eval_eq_zero_iff]`.
- LevelThree.lean:689–700 `modularPolynomialC_three_laurent_root` → a
  `formalCoxPolynomial_eval_transformedJSeries` in FormalCoxProduct (L26); LevelThree:753–757 wants
  `modularPolynomial_map_complex_swap`, which lives in Arithmetic (downstream of LevelThree) → move it
  to IntegralDescent after `modularPolynomial_map_complex`; LevelThree:742, 750 and Kronecker:504, 522
  `simp only [BivariatePolynomial.map]` → `BivariatePolynomial.coe_mapRingHom`/`map_neg`/`map_sub`.
- Construction.lean:7 `import XYin.PhD.Cox.FormalCoxProduct` is unused in Construction but
  IntegralDescent needs it transitively: move the import to IntegralDescent, then drop it here.
- IntegralDescent `modularPolynomialC_coeff_polynomialIn` (:265) belongs in Construction (row 120).
- UHPFF private `transformed_leading … conjugate_injective` → public `transformedJSeries_injective`
  in CoxMatrices/LaurentExpansion.lean (`transformed_leading` ≡ DiagonalLaurent:56).
### Deferred in my set
- G-13/G-14 `𝕜 → E` form (needs `•` rewrites); G-30 `IsImaginaryQuadratic ↔ natDegree (minpoly ℚ τ) = 2`
  (medium); G-9 (generalise `RationalIn`/common denominator) and G-10 (`eval_interpolation_sum_at`
  over a Finset, Lagrange PR) — optional/upstream.
- `CuspData` as a structure (instructed not to change its type); naming items (`varX/varY`,
  theorem-number names) per rules.

## 7. Perf (kernel-computation file affected only as a downstream rebuild)
`time lake env lean XYin/PhD/Cox/LevelThree.lean`: before 24.2 s, after 13.2 s / 13.4 s (wall; nothing
it reduces was touched). No other kernel-computation file is downstream of my changes.
