# Cleanup report: integration wave A (worker `fina`), 2026-09-26

SB = `/Users/dfa25dxu/Projects/Lean/.xyin-sandboxes/fina`. I applied the cross-folder follow-ups from
report-mfn, report-lqe, report-coxc, report-coxa and report-mf to the merged Cox (coxa and coxc sets),
ModularFunctions and Modularforms files, and added Cox Theorem 11.9(i)/(ii) in subfield form.

## 1. Final build

Full `lake build` in SB (both default targets, log `SB/.scratch/build_final2.log`):
```
✔ [3710/3711] Built XYin (6.3s)
Build completed successfully (3711 jobs).
```
- **Warnings:** my owned files produce none. The only warnings in the log are the existing `sorry` in
  `Modularforms/DimensionFormulas.lean` (not touched, as the orchestrator instructed) and the
  Tactic2/XYinTest linter warnings.
- **Forbidden constructs:** none were introduced (`sorry`, `admit`, `axiom`, `native_decide`,
  `set_option`). Every line is at most 100 characters.
- **Linters:** `#lint only simpNF docBlame unusedArguments defLemma simpVarHead simpComm in XYin`
  reports nothing in my files. It reports 3 docBlame findings in `Tactic2`, which is not mine.

**Merge simulation.** coxb was merged into main while I was working. To check against the real merge
target, I made a copy-on-write clone in `SB/.scratch/` containing main plus exactly my 17 files,
overlaid main's versions of coxb's 10 files (including the new `LaurentSeriesAux.lean`), and ran a full
`lake build` there: `Build completed successfully (3712 jobs)`, no errors and no new warnings. The clone
has since been deleted. SB's own non-owned files were never edited.

## 2. Files (lines before → after); no files added or deleted, `XYin.lean` untouched

| file | before | after |
|---|---|---|
| Cox/Arithmetic.lean | 254 | 254 |
| Cox/CoxMatrices/Basic.lean | 655 | 651 |
| Cox/CyclicSublattice/Classification.lean | 225 | 220 |
| Cox/LatticeJ.lean | 626 | 603 |
| Cox/ModularFunction/CuspData.lean | 220 | 183 |
| Cox/ModularFunction/LevelJ.lean | 221 | 211 |
| Cox/ModularFunction.lean | 336 | 301 |
| Cox/ModularFunctionField.lean | 195 | 242 (+66 lines of new theorems) |
| Cox/ModularPolynomial/AnalyticSupport.lean | 126 | 125 |
| Cox/ModularPolynomial/Construction.lean | 413 | 400 |
| Cox/ModularPolynomial/Interpolation.lean | 340 | 326 |
| Cox/ModularPolynomial/Irreducibility.lean | 134 | 134 |
| Cox/UpperHalfPlaneFunctionField.lean | 255 | 243 |
| ModularFunctions/Congruence.lean | 154 | 140 |
| ModularFunctions/JInvariant.lean | 44 | 40 |
| Modularforms/Eisenstein.lean | 210 | 216 (hoisted `Delta_eq_E4_E6`) |
| Modularforms/ForMathlib_Cusps.lean | 37 | 63 (two new helpers) |
| **total** | **4445** | **4352** (−93; existing proofs lost about 175 lines, about 80 lines of new API/theorems were added) |

**Import changes:**
- `ForMathlib_Cusps` gains `public import Mathlib.NumberTheory.ModularForms.QExpansion`.
- `Eisenstein` gains `public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing`. This was
  already in the import closure of every downstream file, via `Deltaqexpansions`.
- `Cox/ModularFunction.lean` drops `XYin.PhD.ModularFunctions.FieldAction`. The only thing it used from
  there was `sl2_mdifferentiable`, which now lives in `NormalFormSlash`.
- `Cox/ModularFunctionField.lean` gains `XYin.PhD.ModularFunctions.Algebra`.

## 3. Done items

### Task 1: ModularFunctions API → Cox
1. **`toMeromorphicField_eq_div_of`** (MFF): 30 → 15 lines. It now uses the `ofMeromorphic_*` API plus
   `ofMeromorphic_eq_iff`; this is mfn's verified code with a type ascription added on `hbmap`. The
   docstring is updated.
2. **`coxPhiFunction_coeff_modularFunction`** (Construction): structure literal (17 lines) →
   `ModularFunction.ofLevelOneHolomorphic` (3 lines).
3. **`levelJModularFunction`** (LevelJ): → `ModularFunction.ofGamma0Holomorphic`. The hand-built normal
   form proof is gone.
4. **`toMeromorphicField_levelJModularFunction`** (MFF): 5 → 1 line
   (`ModularFunction.toMeromorphicField_ofGamma0Holomorphic ..`).
   - UHPFF `algebraMap_jElement` needed nothing: coxc had already deleted it.
5. **`periodic_comp_of_slashInvariant_one`** (CuspData):
   - It is now a one-line wrapper around `UpperHalfPlane.periodic_comp_ofComplex_of_slashInvariant`,
     with the same statement.
   - It is kept because coxb's merged `IntegralDescent.lean:128` still uses it.
   - My internal uses (`LevelOneCuspData.periodic`, `of_widthM`) now call the new lemma directly.
6. **UHPFF holomorphic-function plumbing:**
   - Private `constant` (6 lines) → `algebraMap ℂ HolomorphicFunction`.
   - New simp lemma `evalJ_C`, which also shortens the `IsScalarTower` instance proof.
   - `precomp_evalJPoly` → term `precomp_algebraMap_eq_of_forall …`.
   - `precompAlgEquiv_rightCosetRoot` 4 → 1 line (`precomp_algebraMap_eq_of_forall _ _ _ (rightCosetEval_smul …)`).
7. **`HolomorphicFunction.ext`** replaces the Cox duplicate at UHPFF, MFF ×2, Arithmetic, Interpolation
   and Irreducibility. **Deleted** `Cox.UpperHalfPlaneFunctionField.holomorphicFunction_ext`.
8. **`sl2_det_pos`:** no sites were left; coxc had already switched them to `sl2_mdifferentiable`.
9. **`ModularForm.SL_slash_zero_eq(_iff)`** now serves all sites:
   - CuspData ×5, Cox/ModularFunction, Interpolation, Construction.
   - LatticeJ `inv_j_sub_slashInvariant_aux` goes from 4 lines to a 1-line term.
   - CuspData `of_widthM` becomes `rw [← SL_slash_zero_eq, hslash γ]`.
   - **Deleted** `Cox.slash_zero_eq_comp` and `Cox.slash_zero_eq_iff` (10 lines).
10. **Extra, from mfn's `meromorphicOn_comp_sl2_smul`:** Interpolation `rightCosetTranslate_meromorphicOnH_aux`
    19 → 2 lines (`Quotient.inductionOn c (MeromorphicField.meromorphicOn_comp_sl2_smul hf.meromorphicOn)`).

### Task 2: Laurent-layer API → Cox
1. **CuspData:**
   - Deleted private `meromorphicAt_polynomial_eval` (9 lines) and `cuspFunction_polynomial_eval_eventuallyEq` (10 lines).
   - `CuspData.polynomialIn` (10 lines) becomes a 4-line term using `MeromorphicAt.polynomial_eval`
     and `meromorphicAt_cuspFunction_polynomial_eval`.
   - `CuspData.mul`'s first component is a term.
2. **Cox/ModularFunction.lean:**
   - Deleted private `cuspFunction_sub_const_mul_pow_eventuallyEq` (11 lines). The call site is
     `cuspFunction_comp₂_eventuallyEq 1 (fun x y ↦ x - a * y ^ m) f g`.
   - `cuspData_sub_const_mul_pow` is now a term using `meromorphicAt_cuspFunction_sub/const_mul/pow`
     and `MeromorphicAt.fun_sub/fun_mul/fun_pow`.
   - Deleted private `poleOrder_lt_of_neg_lt_meromorphicOrderAt` (13 lines); the call site is `(poleOrder_lt_iff hm).2`.
   - `hGorder` 3 → 1 line (`(poleOrder_eq_iff one_ne_zero).1 hgorder`, coxc's note).
3. **AnalyticSupport:** `cuspMeromorphicSubring.neg_mem' := meromorphicAt_cuspFunction_neg`.
4. **LevelJ:**
   - The punctured-disc block in `affine_j_cuspFunction_meromorphicAt` (5 lines) → `eventually_ne_zero_and_norm_lt_one`.
   - `cuspFunction_affine_j_eq`'s `hleft` 4 → 1 line (`cuspFunction_apply_of_ne_zero`).

### Task 3: other follow-ups
1. **CoxMatrices/Basic:** `rightCosetTranslate` well-definedness 7 → 3 lines (`hf.apply_smul`, no `SL_slash_apply`).
2. **Classification:** `modularPolynomialC_zero_iff_normalizedCyclicSublattice` 16 → 11 lines
   (`rw [modularPolynomialC_eval_eq_zero_iff]`).
3. **Congruence:** deleted the private `ModularFunction.periodic_comp_ofComplex_of_vadd` (14 lines); it
   now uses the root lemma in LaurentQExpansion.lean, reached via JInvariant → jfunction.
4. **JInvariant:** deleted the alias `ModularFunction.j_mdifferentiable`. Its last user, LatticeJ, now
   uses `_root_.j_mdifferentiable`.
5. **Limit at i∞: new helpers in `Modularforms/ForMathlib_Cusps.lean`** (step7 L26 / step5 H6):
   `UpperHalfPlane.tendsto_atImInfty_of_continuousAt_cuspFunction` and
   `ModularFormClass.tendsto_atImInfty_qExpansion_coeff_zero`. Uses:
   - LatticeJ `E4_tendsto_atImInfty_aux` 10 → 3 lines (with `E4_q_exp`).
   - Cox/ModularFunction `levelOne_constant_of_holomorphic`'s `hfbdd` 7 → 3 lines.
   - LatticeJ `levelOneWeightZeroCuspForm_aux.zero_at_cusps'` 5 → 1 line, via mathlib's `OnePoint.isZeroAt_iff_forall_SL2Z`.
6. **`Delta_eq_E4_E6` hoisted into `Modularforms/Eisenstein.lean`** with the same name, now stated with
   the root `E₄`/`E₆`. `E4`/`E6` are reducible abbreviations of these.
   - LatticeJ keeps using it through its import chain (LatticeJ → JInvariant → jfunction → Deltaqexpansions → Eisenstein).
   - `E4_cube_sub_E6_sq_ne_zero_aux` 6 → 2 lines (`Δ_ne_zero`; no more `Delta_eq_eta_pow` detour; mf item 5).
   - No non-owned file used it (checked main, SB and the jq sandbox).
7. **coxa follow-up, UHPFF `transformed_injective`:** `toFin_injective; simp […]` → `CoxMatrix.ext ha … hd`.
8. **Lint fix, Construction `BivariatePolynomial.coe_mapRingHom`:**
   - The `@[simp]` attribute was removed because `simpNF` flagged it: `simp` unfolds the abbreviation
     first, so the lemma never fires. A docstring now explains this.
   - The lemma is referenced nowhere in main, SB or jq.

### Task 4: Cox Theorem 11.9 as statements about the field of modular functions (new, additive)
- **`Cox.theorem_11_9_ii_subfield (N : ℕ+)`:**
  `ModularFunction.subfield (CongruenceSubgroup.Gamma0 (N : ℕ)) = (IntermediateField.adjoin (RatFunc ℂ) {levelJFieldElement N}).toSubfield`.
  In words: the Γ₀(N)-modular functions are exactly ℂ(j, j_N), i.e. Cox Thm 11.9(ii) literally.
- **`Cox.theorem_11_9_i_subfield`:**
  `ModularFunction.subfield 𝒮ℒ = (algebraMap (RatFunc ℂ) FunctionField).fieldRange`.
  In words: the SL₂(ℤ)-modular functions are exactly ℂ(j), i.e. Cox Thm 11.9(i).
- **Key step, `algebraMap_ratFunc_mem_subfield`:** for any discrete `Γ ≤ 𝒮ℒ` of determinant one,
  ℂ(j) ⊆ `ModularFunction.subfield Γ`. The proof uses constants (`IsModular.algebraMap`), `j` (from
  `jModularFunction.restrict`), and induction on polynomials and on `RatFunc`.
- **Proof of the Γ₀(N) version:** `modularRepresentatives_eq` identifies `modularRepresentatives N`
  with the subfield via `range_toMeromorphicField`. Then `IntermediateField.adjoin_self` is applied to
  `(subfield Γ₀(N)).toIntermediateField`, combined with the unchanged `theorem_11_9_ii`.
- The MFF module docstring now describes both results.

### Task 5
- **Headline statements:** all 12 headline declarations in my files (`theorem_11_9_i/ii/ii_pointwise`,
  `theorem_11_18_i…iv`, `modularPolynomial_three`, `theorem_11_23`, `j_surjective`,
  `j_eq_iff_exists_sl2_smul_eq`) have byte-identical statements, checked by script against SB.base.
- **Public API:** no public name used elsewhere was renamed.
- **Definition-form changes:** `levelJModularFunction` and `coxPhiFunction_coeff_modularFunction`
  changed form (same type and same coercion by `rfl`). They are used only in my files' proofs.
- **Deleted/moved declarations:** a grep of main (with coxb merged), SB, and the jq sandbox finds no
  reference to anything I deleted or moved outside my set. My new names clash with nothing.

## 4. New public API
- `UpperHalfPlane.tendsto_atImInfty_of_continuousAt_cuspFunction (hh : 0 < h) (hper : Periodic (f ∘ ofComplex) h) (hf : ContinuousAt (cuspFunction h f) 0) : Tendsto f atImInfty (𝓝 (cuspFunction h f 0))`
- `ModularFormClass.tendsto_atImInfty_qExpansion_coeff_zero [ModularFormClass F Γ k] (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) : Tendsto f atImInfty (𝓝 ((qExpansion h f).coeff 0))`
- `Delta_eq_E4_E6 (τ : ℍ) : Delta τ = (E₄ τ ^ 3 - E₆ τ ^ 2) / 1728` (moved from LatticeJ into Eisenstein)
- `Cox.UpperHalfPlaneFunctionField.evalJ_C (c : ℂ) : evalJ (C c) = algebraMap ℂ HolomorphicFunction c` (simp)
- `Cox.UpperHalfPlaneFunctionField.modularRepresentatives_eq (N) : modularRepresentatives N = ModularFunction.subfield (Gamma0 N)`
- `Cox.UpperHalfPlaneFunctionField.algebraMap_ratFunc_mem_subfield [DiscreteTopology Γ] [Γ.HasDetOne] (hΓ : Γ ≤ 𝒮ℒ) (r : RatFunc ℂ) : algebraMap (RatFunc ℂ) FunctionField r ∈ ModularFunction.subfield Γ`
- `Cox.theorem_11_9_i_subfield`, `Cox.theorem_11_9_ii_subfield` (statements in §3, Task 4)

**Deleted:**
- Public: `Cox.slash_zero_eq_comp`, `Cox.slash_zero_eq_iff`, `Cox.UpperHalfPlaneFunctionField.holomorphicFunction_ext`, `ModularFunction.j_mdifferentiable`.
- Private: `ModularFunction.periodic_comp_ofComplex_of_vadd`, `Cox.meromorphicAt_polynomial_eval`,
  `Cox.cuspFunction_polynomial_eval_eventuallyEq`, `Cox.cuspFunction_sub_const_mul_pow_eventuallyEq`,
  `Cox.poleOrder_lt_of_neg_lt_meromorphicOrderAt`, UHPFF `constant`.

## 5. Kept on purpose
- `zero_at_cusps_of_zero_at_infty` and `bounded_at_cusps_of_bounded_at_infty` (ForMathlib_Cusps): genuine
  arithmetic-subgroup versions of mathlib's SL₂(ℤ) lemmas. Now unused.
- `Cox.periodic_comp_of_slashInvariant_one`: a thin wrapper, used by coxb's IntegralDescent.
- `coxPhiFunction_coeff_widthOne_cuspMeromorphicAt`: used by IntegralDescent.
- `modularRepresentatives`: still defined as `Set.range`, so that `gamma0ModularFunctionField` and the
  headline `theorem_11_9_ii` unfold exactly as before; the bridge to the subfield is `modularRepresentatives_eq`.
- In Eisenstein, the global `FunLike (ℍ → ℂ) ℍ ℂ` instance and `qExpansion_ext`: still used by jq's
  `jfunction.lean:200` and `link.lean:250`.

## 6. Deferred
1. **Post-merge patch, verified.** It needs coxb's merged files, so it cannot be applied in SB, which
   still has the pre-coxb LevelThree and LaurentExpansion. I built main + my 17 files + this patch in a
   clone: full `lake build` green (3712 jobs). The patch is saved as `SB/.scratch/postmerge-followups.patch`.
   - (a) `Modularforms/Eisenstein.lean`: delete the 3-line `public import Mathlib.Tactic.NormNum.BigOperators`
     re-export. coxb's LevelThree now imports it directly.
   - (b) `Cox/UpperHalfPlaneFunctionField.lean`, −9 lines:
     - Delete private `transformed_leading` (≈ coxb's `transformedJSeries_coeff_neg_sq`).
     - `transformed_leading_ne` becomes `rw [transformedJSeries_coeff_neg_sq]; exact zpow_ne_zero _ (zeta_ne_zero m)`.
     - `transformed_phase` uses `rw [transformedJSeries_coeff_neg_sq, ha, transformedJSeries_coeff_neg_sq] at hc`.
     - `cox_b_eq` gets `hzeta0 := zeta_ne_zero m`.
2. **Global FunLike instance and `qExpansion_ext` deletion:** waits for jq (`jfunction.lean:197–201`, `link.lean:250`).
3. **UHPFF `transformed_*` chain → a public `transformedJSeries_injective`:** that lemma belongs in coxb's
   `CoxMatrices/LaurentExpansion.lean`, which is not mine.
4. **`modularPolynomialC_coeff_polynomialIn`:** it lives in IntegralDescent (not mine) and belongs in
   Construction. Adding it to Construction now would clash with IntegralDescent.
5. **`evalJ` as `Polynomial.aeval jElement` (AlgHom):** this would change the type of a def used as a
   RingHom at 6 sites. It shortens nothing, so I skipped it.
6. **mfn's own deferrals and naming items:** an ᵐᵒᵖ `MulAction` for `precomp`, `IsMeromorphicAt.infty_iff`,
   turning `meromorphic'` into an NF predicate, and style renames. All out of scope.
7. **`AxiomCheck.lean`, updated by the orchestrator at 20:22:** the 22 original lines are all
   `[propext, Classical.choice, Quot.sound]`. The two new lines concern the separate
   DimensionFormulas/SturmBound worker. In SB, `dim_gen_cong_levels` still shows `sorryAx` (untouched,
   as instructed) and `ModularForm.sturm_bound_of_finiteIndex` is an unknown constant (that worker's new
   file does not exist here; I created no `SturmBound.lean`).

## 7. Perf
I edited no kernel-computation file and nothing they reduce. Interleaved A/B, `lake env lean F` (real
seconds, same load), with BASE being a clone holding the SB.base versions of my 17 files:

| file | BASE | NEW |
|---|---|---|
| `qExpansion_tactic/link.lean` | 8.22 / 8.50 | 9.01 / 7.95 |
| `jFunction/qexp_coeffs.lean` | 7.67 / 7.92 | 7.64 / 7.77 |
| `Cox/LevelThree.lean` | 17.96 / 18.12 / 17.86 | 17.98 / 17.78 / 17.71 |

That is ≈ 1.0× (noise only).

### Axioms of the new theorems (`SB/.scratch/AxiomNew.lean`)
`Cox.theorem_11_9_ii_subfield`, `Cox.theorem_11_9_i_subfield`,
`Cox.UpperHalfPlaneFunctionField.algebraMap_ratFunc_mem_subfield`, `…modularRepresentatives_eq`,
`…evalJ_C`, `Delta_eq_E4_E6`, `UpperHalfPlane.tendsto_atImInfty_of_continuousAt_cuspFunction`,
`ModularFormClass.tendsto_atImInfty_qExpansion_coeff_zero`: each depends on axioms
`[propext, Classical.choice, Quot.sound]`.
