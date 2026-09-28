# CLEANUP_REPORT — sandbox `sl` (Γ(1) → 𝒮ℒ, one name per object), 2026-09-26/27

Owned set: the whole source tree (`XYin/`, `XYinTest/`, `XYin.lean`, `XYinTest.lean`).
User instructions implemented: (a) level-one objects use mathlib's `𝒮ℒ` objects instead of
`CongruenceSubgroup.Gamma 1`; (b) one name per object, no aliases (the rule "don't rename public
declarations for style" is overridden for these renames); (c) no book-numbered name changed.

## 1. Final gate

* `lake build` (targets `XYin`, `XYinTest`) in SB: `Build completed successfully (3713 jobs).`,
  0 warnings, 0 errors (log: full rebuild of every affected module after the edits, then a
  no-op re-run).
* `grep -rnw sorry XYin XYinTest XYin.lean XYinTest.lean` → 0.
* `lake env lean …/cleanup-2026-09-26/AxiomCheck.lean` (run from SB, file unchanged — it references
  no renamed name): all 27 declarations print `[propext, Classical.choice, Quot.sound]`.
* `#lint only defsWithUnderscore in XYin` (`SB/.scratch/LintUnderscore.lean`, imports `XYin`,
  `XYinTest`, `Batteries.Tactic.Lint`): `Found 0 errors in 1310 declarations … All linting checks
  passed!` (before: `PeriodPair.instSMulUnitsComplex_xYin` was a hit).
* `grep -rn "Gamma 1\|Γ(1)" XYin XYinTest` → no hits at all (also none for `Gamma ↑1`,
  `Gamma_one`, `gamma1`).
* Removed names (`E4`, `E6`, root `E₄`/`E₆`, `Δ` as a declaration, `Delta`, `jN`, `FunctionField`,
  `laurentSeriesMapRingHom`, `one_mem_strictPeriods_gamma1`) are neither declared nor referenced
  (code and docstrings). Remaining `Δ` occurrences are mathematical notation in docstrings and the
  file-local `local notation "Δ" => ModularForm.discriminant` of `Modularforms/Delta.lean`
  (exactly as mathlib's `Discriminant.lean`; declares no global name). `qOverDelta`, `deltaOverQ`,
  `integralDelta`, `integralDeltaOverQ`, `deltaCoeffInt`, `deltaQExpansion`, `deltaTarget`,
  `qoverDelta*`, `integralE4`, `integralE6`, `e4CoeffInt`, `ramanujanTau` are other objects and
  keep their names.

## 2. Files changed (lines before → after); no file added or deleted, `XYin.lean` unchanged

| file | before → after |
|---|---|
| XYin/PhD/Modularforms/Delta.lean | 108 → 73 |
| XYin/PhD/Modularforms/Eisenstein.lean | 204 → 182 |
| XYin/PhD/jFunction/Deltaqexpansions.lean | 225 → 220 |
| XYin/PhD/jFunction/jfunction.lean | 389 → 390 |
| XYin/PhD/jFunction/jLevelN.lean | 105 → 106 |
| XYin/PhD/jFunction/qexp_coeffs.lean | 131 → 132 |
| XYin/PhD/qExpansion_tactic/Qj.lean | 283 → 283 |
| XYin/PhD/qExpansion_tactic/link.lean | 309 → 309 |
| XYin/PhD/Tactic2/qexp_simp.lean | 164 → 160 |
| XYin/PhD/Cox/LatticeJ.lean | 603 → 603 |
| XYin/PhD/Cox/ModularFunction/LevelJ.lean | 203 → 195 |
| XYin/PhD/Cox/UpperHalfPlaneFunctionField.lean | 171 → 168 |
| XYin/PhD/Cox/ModularFunctionField.lean | 242 → 243 |
| XYin/PhD/Cox/ModularPolynomial/Irreducibility.lean | 134 → 134 |
| XYin/PhD/Cox/LaurentSeriesAux.lean | 137 → 141 |
| XYin/PhD/Cox/LaurentPolynomialEvaluation.lean | 194 → 187 |
| XYin/PhD/Cox/Kronecker.lean | 355 → 355 |
| XYin/PhD/Cox/LevelThree.lean | 376 → 376 |
| XYinTest/Tactic2/QExpSimpConditionTests.lean | 67 → 68 |
| XYinTest/qExpansion_tactic/Examples.lean | 66 → 66 |

Net: 4466 → 4391 lines (−75).

## 3. Done items

### A. Level-one objects: `Γ(1)` → mathlib's `𝒮ℒ` objects

1. **Eisenstein series.** Deleted the project's `E₄`, `E₆ : ModularForm (Gamma ↑1) _`
   (`Modularforms/Eisenstein.lean`) and the aliases `E4 := _root_.E₄`, `E6 := _root_.E₆`
   (`jFunction/Deltaqexpansions.lean`). Every use now refers to mathlib's
   `ModularForm.E₄ : ModularForm 𝒮ℒ 4`, `ModularForm.E₆ : ModularForm 𝒮ℒ 6` (via `open ModularForm`;
   `open ModularForm hiding E₄ E₆` removed). The project's objects were definitionally the same
   functions (mathlib's are `.copy`-ed along `Gamma_one_coe_eq_SL.symm`), so e.g. the `rfl` in
   `periodPair_g₂_eq_E₄` still works.
2. **Discriminant.** Deleted the function `Δ` (cexp-product form, `Modularforms/Delta.lean`) and the
   cusp form `Delta : CuspForm (Gamma 1) 12` (a `.copy` of `CuspForm.discriminant`). Uses now refer
   to `ModularForm.discriminant` (the function; statements use this simp-normal form, as mathlib's
   `discriminant_qExpansion_coeff_one` does) and `CuspForm.discriminant` (where the bundled cusp
   form is needed: `ModularFormClass.holo`, `slash_action_eq'`, `vAdd_apply_of_mem_strictPeriods`,
   the `qexp_simp` tests). `CuspForm.coe_discriminant` is `rfl`.
3. **Mathlib duplicates deleted** (uses retargeted):
   `Δ_ne_zero` → `discriminant_ne_zero`; `Delta_q_one_term` → `discriminant_qExpansion_coeff_one`;
   `Delta_eq_E4_E6` → `discriminant_eq_E₄_cube_sub_E₆_sq`; `Delta_eq_eta_pow` is the definition of
   `ModularForm.discriminant`; `Delta_apply`, `coe_Delta`, `Δ_eq_discriminant` unnecessary;
   `Delta_boundedfactor` (a `simpa [eta_q_eq_cexp]` restatement of mathlib's
   `tendsto_atImInfty_tprod_one_sub_eta_q_pow`) deleted, its single use
   (`deltaOverQ_tendsto_atImInfty`) calls mathlib directly.
4. **Genuine project lemmas kept and restated for mathlib's objects**, names following the object:
   `E₄_q_exp`, `E₆_q_exp`, `E₄_imag_axis_real`, `E₆_imag_axis_real` (Eisenstein.lean);
   `discriminant_resToImagAxis`, `discriminant_imag_axis_real`,
   `re_ResToImagAxis_discriminant_eq_real_prod`, `discriminant_imag_axis_pos` (Delta.lean, proof of
   `discriminant_resToImagAxis` now via `discriminant_eq_q_prod` + `eta_q_eq_cexp`);
   `E₄_pow_three_qExpansion`, `E₆_pow_two_qExpansion`, `E₄_isIntegralPowerSeries`,
   `E₆_isIntegralPowerSeries`, `E₄_pow_three_isIntegralPowerSeries`,
   `discriminant_qExpansion_eq_smul_eisenstein_difference`, `discriminant_isIntegralPowerSeries`
   (Deltaqexpansions.lean); `qExpansion_discriminant_eq_X_mul`,
   `deltaOverQ_eq_qParam_inv_mul_discriminant`, `E₄_pow_three_mul_qOverDelta_eq_qj`,
   `E₄_pow_three_cuspFunction_analyticAt` (jfunction.lean); `E₄_int_series_eq`,
   `E₆_int_series_eq`, `E₄_int_link`, `discriminant_qxp_coeff_link` (link.lean);
   `discriminant_qExpansion_coeff_two/three/four/five` (qexp_coeffs.lean, continuing mathlib's
   `discriminant_qExpansion_coeff_one`); `periodPair_g₂_eq_E₄`, `periodPair_g₃_eq_E₆` (LatticeJ.lean).
   Unchanged names: `bernoulli'_six`, `E_even_imag_axis_real`, the `E₂` results, `tprod_pos_nat_im`,
   `ModularForm.qExpansion_coe_pow`, `integralE4/E6/Delta` and their coefficient lemmas,
   `ramanujanTau(_cast)`, `eisenstein_difference_coeff_modEq_zero`, …
5. **Remaining `Gamma 1` uses removed.**
   `j_slash_invariant` (jfunction.lean): membership `(γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ` is `⟨γ, rfl⟩`
   (was `Subgroup.map (mapGL ℝ) (Gamma 1)` + `mem_Gamma_one`, 3 lines);
   `discriminant_qExpansion_eq_smul_eisenstein_difference` builds its auxiliary form in
   `ModularForm 𝒮ℒ 12` (was `mcast` into `Gamma 1`); `(by simp)` side goals `1 ∈ Γ.strictPeriods`
   now use mathlib's `one_mem_strictPeriods_SL`; `QExpSimp.one_mem_strictPeriods_gamma1` deleted
   (mathlib's `one_mem_strictPeriods_SL` was already tagged `qexp_simps`; `open scoped
   CongruenceSubgroup` dropped); docstrings updated (Eisenstein/Delta module docs).
6. **`j` keeps its meaning**: `def j : ℍ → ℂ := fun τ ↦ E₄ τ ^ 3 / discriminant τ` (same function
   as before: `E₄` definitionally, `discriminant` = old `Δ` by the deleted `Δ_eq_discriminant`).
   No statement about `j` changed its text.
7. **`#qexp` / `qexp_coeff` target keyword** (Qj.lean): the identifier selecting the `Δ` table was
   `Delta` (named after the deleted declaration); it is now `discriminant`
   (`#qexp discriminant coeff 4`, `qexp_coeff discriminant 4 (-1472)`); error messages, docstrings
   and `XYinTest/qExpansion_tactic/Examples.lean` updated. `qj` unchanged.
8. **Imports**: `Eisenstein.lean` imports `XYin.PhD.Modularforms.ResToImagAxis` instead of
   `…Modularforms.Delta` and drops `LevelOne.GradedRing` (both only served the deleted lemmas);
   `Deltaqexpansions.lean` gets `open scoped MatrixGroups` (for `𝒮ℒ`).

### B. Other pairs of names for one object

9. **`jN` / `Cox.levelJ` → `levelJ`** (one definition, `jFunction/jLevelN.lean`):
   `def levelJ (N : ℕ) [NeZero N] : ℍ → ℂ := fun z ↦ j (natScale N z)` (root namespace, next to
   `j`); `Cox.levelJ (N : ℕ+) := jN N` deleted. `jN_apply`/`Cox.levelJ_apply` merged into
   `levelJ_apply`; `jN_slash_invariant` → `levelJ_slash_invariant`, `jN_differentiableAt` →
   `levelJ_differentiableAt`. All Cox uses with `N : ℕ+` still read `levelJ N` (coercion
   `↑N : ℕ`, `NeZero` from mathlib's `NeZero.pnat`); `theorem_11_9_ii_pointwise`,
   `theorem_11_9_ii_subfield`, `theorem_11_9_ii` unchanged in text and meaning.
   `Cox.levelJ_mdifferentiable`, `Cox.levelJ_smul_eq_j_affine`, `Cox.levelJ_cuspData`,
   `levelJElement`, `levelJFieldElement`, `levelJModularFunction`, `jLevelFunctionField` unchanged.
10. **`FunctionField` → `MeromorphicField`**: `abbrev Cox.UpperHalfPlaneFunctionField.FunctionField
   := MeromorphicField` deleted; all 30+ uses (UpperHalfPlaneFunctionField.lean,
   ModularFunctionField.lean, Irreducibility.lean) use `UpperHalfPlane.MeromorphicField`. Statement
   text of `theorem_11_9_i_subfield` now reads `(algebraMap (RatFunc ℂ) MeromorphicField).fieldRange`
   (same type; name unchanged). Names containing the words (`UpperHalfPlaneFunctionField`,
   `gamma0ModularFunctionField`, `jLevelFunctionField`, private `modularPolynomialFunctionField`,
   the file name) unchanged. Side effect: the two anonymous instances of the file get new
   auto-generated names (see rename table).
11. **`laurentSeriesMapRingHom` → `HahnSeries.mapRingHom`**: abbrev deleted
   (LaurentPolynomialEvaluation.lean); `laurentSeriesMapRingHom_coeff` → `HahnSeries.mapRingHom_coeff`
   (moved next to `mapRingHom_apply` in LaurentSeriesAux.lean, generalised to any `Γ`, `rfl`, no
   longer `@[simp]` since `simp` already proves it via `mapRingHom_apply` + `map_coeff`);
   `laurentSeriesMapRingHom_comp_eval₂RingHom` → `HahnSeries.mapRingHom_comp_eval₂RingHom`
   (generalised from `LaurentSeries` to `HahnSeries Γ`, same proof). Uses in Kronecker.lean and
   LevelThree.lean retargeted.
12. **Instance name** (LatticeJ.lean): `instance instSMulUnitsComplex : SMul ℂˣ PeriodPair` —
   replaces the auto-name `PeriodPair.instSMulUnitsComplex_xYin` (Lean appends `_xYin` because
   `PeriodPair` is a mathlib namespace); `PeriodPair.instSMulUnitsComplex` is free in mathlib
   (mathlib declares no instance on `PeriodPair`).
13. **Survey for other pure synonyms** (every `def`/`abbrev` of the tree — 279 before, 270 after —
   was listed with its body): the only pure synonyms were the ones above (items 1, 2, 9, 10, 11). Considered and kept:
   * specialisations / composites (not "same name applied to the same arguments"):
     `BivariatePolynomial R := Polynomial (Polynomial R)` (carries the `BivariatePolynomial.*`
     dot-notation API); `BivariatePolynomial.eval Φ x y := Φ.evalEval y x` (argument swap, documented
     Cox `(x, y)` order); `BivariatePolynomial.varX := Polynomial.X`, `varY := C X`,
     `BivariatePolynomial.map`/`mapRingHom` (function vs bundled hom), `specializeY`, `diagonal`;
     `LevelOneCuspData f := CuspData 1 f` and the lemma `j_levelOneCuspData := j_cuspData 1`;
     `PeriodPair.CyclicSublattice.j S := S.toPeriodPair.j`;
     `UpperHalfPlane.ellipticCurve τ := (periodPair τ).weierstrassCurve`;
     `cyclicSublatticeEquivCoxMatrix`, `CoxMatrix.toCyclicSublattice` (at `periodPair τ`);
     `rightCosetEval` (at `levelJ m`); `primeCoxMatrixEquiv := (primeFinEquivCoxMatrix p).symm`;
     `LevelThree` jets `sigmaJetThree`, `widthJetThree`, …;
   * bundlings/constructions: `ModularFunction.toMeromorphicFieldRingHom/AlgHom`, `subring`,
     `subfield`, `restrict`, `ofLevelOneCuspData`, `ofGamma0CuspData`, `precomp`, `sigmaZero`, …;
   * specification-vs-algorithm pairs linked by a correctness theorem: `integralE4`/`e4CoeffInt`
     (`E₄_int_series_eq`), `integralE6`/`e6CoeffInt`, `integralDelta`/`deltaQExpansion`
     (`ramanujanTau_link`), `qjCoeffs`/`qjCoeffInt`, `ramanujanTau`/`deltaCoeffInt`;
   * user-listed keeps: `IsIntegralPowerSeries`, `toIntegralPowerSeries`,
     `IntegralPowerSeriesSubring`, `powerSeriesMapAlgHom`, `coeToComplexPowerSeries.ringHom`,
     `MeromorphicField`, `integerCoeffLaurentSeries`, `HolomorphicFunction`.
   No `alias`, `@[deprecated]`, `export` or global `notation` exists in the tree.

## 4. New public API

* `HahnSeries.mapRingHom_coeff (f : R →+* S) (x : HahnSeries Γ R) (g : Γ) :
  (mapRingHom f x).coeff g = f (x.coeff g)` (renamed + generalised from
  `Cox.laurentSeriesMapRingHom_coeff`).
* `HahnSeries.mapRingHom_comp_eval₂RingHom (f : R →+* S) (hJ : mapRingHom f J = J') :
  (mapRingHom f).comp (Polynomial.eval₂RingHom C J) =
  (Polynomial.eval₂RingHom C J').comp (Polynomial.mapRingHom f)` for `J : HahnSeries Γ R`
  (renamed + generalised from `Cox.laurentSeriesMapRingHom_comp_eval₂RingHom`).
* `levelJ (N : ℕ) [NeZero N]` and `levelJ_apply/_slash_invariant/_differentiableAt` (the former
  `jN*`, see rename table). Nothing else new.

## 5. Kept on purpose (genuine mathematics, unused elsewhere)

`discriminant_resToImagAxis`, `discriminant_imag_axis_real`,
`re_ResToImagAxis_discriminant_eq_real_prod`, `tprod_pos_nat_im`, `discriminant_imag_axis_pos`
(Delta.lean); `E_even_imag_axis_real`, `E₄_imag_axis_real`, `E₆_imag_axis_real`,
`E₂_imag_axis_real`, `norm_exp_two_pi_I_le_exp_neg_two_pi`, `norm_tsum_logDeriv_expo_le(_of_norm_le)`,
`E₂_isBoundedAtImInfty` (Eisenstein.lean). The file names `Modularforms/Delta.lean`,
`jFunction/Deltaqexpansions.lean`, `jFunction/jLevelN.lean` were not changed (not requested).

## 6. Deferred / notes (nothing needs edits outside the owned set)

* The user's external notes / blueprint must follow the rename table below (e.g. the headline
  coefficient lemmas `Delta_qExpansion_coeff_two…five` are now `discriminant_qExpansion_coeff_*`
  with `qExpansion 1 discriminant` in the statement — a forced consequence of deleting `Delta`;
  `theorem_11_9_i_subfield` now displays `MeromorphicField`). The `.mathlib-quality` reports keep
  the old names as historical records.
* Tactic syntax change: `#qexp Delta …` / `qexp_coeff Delta …` → `#qexp discriminant …` /
  `qexp_coeff discriminant …`.
* `CuspData.lean:81` (`LevelOneCuspData.slash_sl2`) still mentions `CongruenceSubgroup.Gamma0 1`:
  this is the `Γ₀(N)` family of `CuspData N` at `N = 1`, not a `Γ(1)` level-one object; left as is.
* Possible follow-ups (not synonyms by the task's definition, so not done): `ℂ[X][Y]` (mathlib
  notation, used by `RationalInTwo`/`ModularFunctionField`) coexists with the abbrev
  `BivariatePolynomial ℂ`; `BivariatePolynomial.eval` is an argument swap of `Polynomial.evalEval`
  (step5 [V-20]); the anonymous instances of `UpperHalfPlaneFunctionField.lean` have very long
  auto-generated names (they had equally long ones before) and could be given explicit names.

## 7. Performance (kernel-computation files; `lake env lean F`, warm runs, same machine)

| file | before | after (quiet run) |
|---|---|---|
| qExpansion_tactic/link.lean | 5.21 s (cold 19.8) | 4.99 / 4.95 s |
| jFunction/qexp_coeffs.lean | 5.14 / 5.02 s | 4.82 / 4.83 s |
| Cox/LevelThree.lean | 10.50 / 10.61 s | 9.70 / 9.38 s |

No slowdown (all ≤ 1.0×). Under heavy machine load some runs were slower (e.g. 7.9 s / 14.7 s, and
one outlier during a session stall); the kernel-reduced definitions (`Qj` arrays, LevelThree
tables) were not touched — only `laurentSeriesMapRingHom` (a reducible abbrev) was replaced by its
body in one LevelThree proof.

## 8. Rename table (every public declaration renamed or removed)

| old name | new name / replacement |
|---|---|
| `E₄` (root, `ModularForm (Gamma ↑1) 4`) | `ModularForm.E₄` (mathlib) |
| `E₆` (root, `ModularForm (Gamma ↑1) 6`) | `ModularForm.E₆` (mathlib) |
| `E4` (abbrev) | `ModularForm.E₄` |
| `E6` (abbrev) | `ModularForm.E₆` |
| `Δ` (root function) | `ModularForm.discriminant` (mathlib) |
| `Delta` (`CuspForm (Gamma 1) 12`) | `CuspForm.discriminant` (bundled) / `ModularForm.discriminant` (function) |
| `Delta_eq_eta_pow` | removed: definition of `ModularForm.discriminant` (`rfl`) |
| `Δ_eq_discriminant` | removed (no longer needed) |
| `Δ_ne_zero` | `ModularForm.discriminant_ne_zero` |
| `Delta_apply` | removed (`CuspForm.coe_discriminant`, `rfl`) |
| `coe_Delta` | `CuspForm.coe_discriminant` |
| `Delta_boundedfactor` | `ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow` (+ `eta_q_eq_cexp`) |
| `Delta_q_one_term` | `ModularForm.discriminant_qExpansion_coeff_one` |
| `Delta_eq_E4_E6` | `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq` |
| `E4_q_exp` / `E6_q_exp` | `E₄_q_exp` / `E₆_q_exp` |
| `Δ_resToImagAxis` | `discriminant_resToImagAxis` |
| `Delta_imag_axis_real` | `discriminant_imag_axis_real` |
| `re_ResToImagAxis_Delta_eq_real_prod` | `re_ResToImagAxis_discriminant_eq_real_prod` |
| `Delta_imag_axis_pos` | `discriminant_imag_axis_pos` |
| `E4_pow_three_qExpansion` / `E6_pow_two_qExpansion` | `E₄_pow_three_qExpansion` / `E₆_pow_two_qExpansion` |
| `E4_isIntegralPowerSeries` / `E6_isIntegralPowerSeries` | `E₄_isIntegralPowerSeries` / `E₆_isIntegralPowerSeries` |
| `E4_pow_three_isIntegralPowerSeries` | `E₄_pow_three_isIntegralPowerSeries` |
| `Delta_qExpansion_eq_smul_eisenstein_difference` | `discriminant_qExpansion_eq_smul_eisenstein_difference` |
| `Delta_isIntegralPowerSeries` | `discriminant_isIntegralPowerSeries` |
| `qExpansion_Delta_eq_X_mul` | `qExpansion_discriminant_eq_X_mul` |
| `deltaOverQ_eq_qParam_inv_mul_Delta` | `deltaOverQ_eq_qParam_inv_mul_discriminant` |
| `E4_pow_three_mul_qOverDelta_eq_qj` | `E₄_pow_three_mul_qOverDelta_eq_qj` |
| `E4_pow_three_cuspFunction_analyticAt` | `E₄_pow_three_cuspFunction_analyticAt` |
| `E4_int_series_eq` / `E6_int_series_eq` | `E₄_int_series_eq` / `E₆_int_series_eq` |
| `E4_int_link` | `E₄_int_link` |
| `Delta_qxp_coeff_link` | `discriminant_qxp_coeff_link` |
| `Delta_qExpansion_coeff_two/three/four/five` | `discriminant_qExpansion_coeff_two/three/four/five` |
| `periodPair_g₂_eq_E4` / `periodPair_g₃_eq_E6` | `periodPair_g₂_eq_E₄` / `periodPair_g₃_eq_E₆` |
| `QExpSimp.one_mem_strictPeriods_gamma1` | `one_mem_strictPeriods_SL` (mathlib) |
| `jN` and `Cox.levelJ` | `levelJ` (root; `(N : ℕ) [NeZero N]`) |
| `jN_apply` and `Cox.levelJ_apply` | `levelJ_apply` |
| `jN_slash_invariant` | `levelJ_slash_invariant` |
| `jN_differentiableAt` | `levelJ_differentiableAt` |
| `Cox.UpperHalfPlaneFunctionField.FunctionField` | `UpperHalfPlane.MeromorphicField` |
| `Cox.laurentSeriesMapRingHom` | `HahnSeries.mapRingHom` |
| `Cox.laurentSeriesMapRingHom_coeff` | `HahnSeries.mapRingHom_coeff` |
| `Cox.laurentSeriesMapRingHom_comp_eval₂RingHom` | `HahnSeries.mapRingHom_comp_eval₂RingHom` |
| `PeriodPair.instSMulUnitsComplex_xYin` | `PeriodPair.instSMulUnitsComplex` |
| `Cox.UpperHalfPlaneFunctionField.instAlgebraRatFuncComplexSubtypeGermCodiscreteWithinUpperHalfPlaneSetMemSubringFunctionField` (auto) | `…MemSubringMeromorphicField` (auto) |
| `Cox.UpperHalfPlaneFunctionField.instIsScalarTowerComplexRatFuncSubtypeGermCodiscreteWithinUpperHalfPlaneSetMemSubringFunctionField` (auto) | `…MemSubringMeromorphicField` (auto) |
| tactic target `#qexp Delta` / `qexp_coeff Delta` | `#qexp discriminant` / `qexp_coeff discriminant` |

Private helpers renamed alongside (not public): `E4_qExpansion_coeff`/`E6_qExpansion_coeff` →
`E₄_…`/`E₆_…`; `E4_vadd_one_aux` → `E₄_vadd_one_aux`; `Delta_vadd_one_aux` →
`discriminant_vadd_one_aux`; `E4_tendsto_atImInfty_aux` → `E₄_tendsto_atImInfty_aux`;
`E4_cube_sub_E6_sq_ne_zero_aux` → `E₄_cube_sub_E₆_sq_ne_zero_aux`.

Public declarations whose name is unchanged but whose statement text now mentions the mathlib
object: `j` (body), `deltaShiftedQSeries` (body), `ramanujanTau_cast`, `deltaOverQ_qExpansion_coeff`,
`map_integralE4_pow_three_sub_integralE6_pow_two`, `eisenstein_difference_coeff_cast`,
`deltaQExpansion_link`, `deltaCoeffInt_cast`, `E₄_imag_axis_real`, `E₆_imag_axis_real`,
`theorem_11_9_i_subfield` and the `FunctionField`-typed Cox API (`evalJFracPoly`, `ratFuncEvalJ`,
`algebraMap_ratFunc`, `precompAlgEquiv`, `rightCosetRoot`, `evalJLevel`, `levelJFieldElement`,
`toMeromorphicField_eq_div_of`, `toMeromorphicField_eq_ratFunc`, `modularRepresentatives`,
`gamma0ModularFunctionField`, `jLevelFunctionField`, `algebraMap_ratFunc_mem_subfield`) and the
`laurentSeriesMapRingHom`-typed Cox API (`bivariateSpecializeLaurent_map(_apply)`,
`bivariateLaurentEvalHom_map`, `specializeJIntegral_map_zmod/_map_complex`,
`specializeJIntegral_modularPolynomial_map_complex`, `cyclotomicCoxPolynomial_map(_complex/_mod)`,
`cyclotomicDescent_polynomialLaurentSeries`) — all definitionally/semantically the same statements.
