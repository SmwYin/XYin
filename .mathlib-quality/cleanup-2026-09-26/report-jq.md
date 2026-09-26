# Cleanup report — worker `jq` (jFunction / qExpansion_tactic / Tactic2 / XYinTest)

Date: 2026-09-26. Sandbox: `/Users/dfa25dxu/Projects/Lean/.xyin-sandboxes/jq`.

## 1. Build

Final `lake build` in SB (both default targets `XYin`, `XYinTest`), log `.scratch/build_final_raw.log`:

```
✔ [3708/3709] Built XYin (6.2s)
Build completed successfully (3709 jobs).
```

(3709 instead of 3710 jobs: `qexp_simp.lean` no longer imports the deprecated umbrella
`Mathlib.NumberTheory.ModularForms.LevelOne`.) The only warning of the whole build is the
pre-existing `sorry` in `Modularforms/DimensionFormulas.lean`; all 67 former Tactic2/XYinTest
warnings (headers, module docstrings, long lines, deprecated import) are gone. Environment linters
`#lint only simpNF simpComm simpVarHead defLemma unusedArguments` and `#lint only docBlame` pass on
all 589 `XYin` declarations of the import closure of my modules. Only owned files were edited
(`diff -rq` against SB.base); `XYin.lean`, `XYinTest.lean` unchanged.

## 2. Files (lines before → after)

| File | before | after | decls before → after |
|---|---|---|---|
| `XYin/PhD/jFunction/Deltaqexpansions.lean` | 300 | 225 | 41 → 33 |
| `XYin/PhD/jFunction/jfunction.lean` | 504 | 389 | 67 → 59 |
| `XYin/PhD/jFunction/jLevelN.lean` | 193 | 105 | 15 → 11 |
| `XYin/PhD/jFunction/qexp_coeffs.lean` | 163 | 131 | 24 → 19 (+1 moved to jfunction) |
| `XYin/PhD/jFunction/jInvariantLink.lean` | 81 | 81 | unchanged (see §6) |
| `XYin/PhD/qExpansion_tactic/Qj.lean` | 304 | 283 | 32 → 32 |
| `XYin/PhD/qExpansion_tactic/link.lean` | 408 | 309 | 43 → 36 |
| `XYin/PhD/Tactic2/QExpSimpAttr.lean` | 3 | 19 | (header + docstrings) |
| `XYin/PhD/Tactic2/qexp_simp.lean` | 207 | 164 | 28 → 18 |
| library total | 2163 | 1706 | 257 → 215 |
| `XYinTest/Tactic2/LaurentQExpSimpTests.lean` | 63 | 58 | 9 → 8 examples |
| `XYinTest/Tactic2/QExpSimpConditionTests.lean` | 55 | 67 | header + module doc |
| `XYinTest/qExpansion_tactic/Examples.lean` | 65 | 66 | |

No files added or deleted.

## 3. Done items

### Follow-ups (FOLLOWUPS.md / report-lqe §6)
* `jfunction.lean`: `deltaOverQ_isIntegralPowerSeries` via `coeff_toIntegralPowerSeries_cast`;
  private `qj_coeff_cast_aux` → public `qjCoeffs_cast`; `integralDeltaOverQ` unit proof via
  `coeff_toIntegralPowerSeries_cast` (the `coeToComplexPowerSeries.ringHom`/`coeff_map` dance is
  gone); `qj_periodic := periodic_comp_ofComplex_of_vadd qj_vadd_one_aux` (13 → 2 lines);
  `inv_mul_cuspFunction_qj_eq_j_aux` via `cuspFunction_qpow_mul_eventuallyEq` (12 → 7);
  `j_poleRemoved` via `poleRemoved_apply`; `j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one` =
  `coeff_eq_zero_of_lt' j_poleOrder hn`; `j_laurentQExpansion_isIntegral` via the new explicit
  witness lemma (below).
* **FunLike independence**: `jfunction.lean` no longer applies the `FunLike`-generic
  `qExpansion_coeff_unique` (whole `deltaShiftedQSeries` analyticity route removed, see Task 2).
  Verified by a meta check (`.scratch/FunLikeCheck.lean`): none of the 341 declarations of
  `jFunction/`, `qExpansion_tactic/`, `Tactic2/` uses `instFunLikeForallUpperHalfPlaneComplex_xYin`.
* `Deltaqexpansions.lean`: private `E4/E6_qExpansion_coeff_aux` → `congr_fun E4_q_exp n` (cast form);
  `toIntegralPowerSeries_coeff_eq` deleted (→ `coeff_toIntegralPowerSeries_cast`);
  `toIntegralPowerSeries_eisenstein_difference_aux` + `eisenstein_difference_isIntegralPowerSeries_aux`
  deleted (→ `toIntegralPowerSeries_eq_of_map_eq _ map_integralE4_pow_three_sub_integralE6_pow_two`
  inline); `E4_pow_three_isIntegralPowerSeries` = `hasCoeffsIn_pow ℤ ℂ …` (1 line);
  `Delta_qExpansion_eq_smul_eisenstein_difference` via `coe_Delta` +
  `discriminant_eq_E₄_cube_sub_E₆_sq` (21 → 13 lines).
* `jLevelN.lean`: the periodicity/punctured-disc sites disappeared with the dead chain (Task 3);
  `⟨N * z, _⟩` scaling → new `UpperHalfPlane.natScale` built on mathlib `posRealAction`.
* `qexp_coeffs.lean`: private bridges `qjCoeffs_eq_qjQExpansion_coeff_aux` and
  `j_laurentQExpansion_coeff_eq_qj_coeff_aux` deleted (→ public `qjCoeffs_eq_qjCoeffInt`,
  `j_laurentQExpansion_coeff_sub_one`).
* `link.lean`: `E4_int_link` = `rw [E4_int_series_eq]; exact mapAlgHom_ofId_toIntegralPowerSeries …`;
  `eisenstein_difference_coeff_cast` = one `rw` via `coeToComplexPowerSeries.coeff_ringHom_int`;
  `deltaCoeffInt_cast` = one `rw` via `coeff_mapAlgHom_ofId_int`; `ramanujanTau_link` via
  `ramanujanTau_cast` (7 → 3 lines); `qExpansion_ext` no longer needed at all
  (`deltaOverQ_qexpansion_link` goes through `deltaOverQ_qExpansion_coeff`).
* `XYinTest/Tactic2/LaurentQExpSimpTests.lean`: examples via `coeff_of_geq'`,
  `coeff_eq_zero_of_lt'`, `coeff_neg_poleOrder_add'` (most become terms); byte-identical duplicate
  example deleted; header, module docstring, long lines fixed.

### Task 1 — integer-coefficient bridges
* Public `qjCoeffs_cast`, `qjCoeffs_eq_qjCoeffInt` (link.lean), shift lemmas
  `j_laurentQExpansion_coeff_sub_one` (ℕ form) and `j_laurentQExpansion_coeff_of_neg_one_le`
  (ℤ form), and the **explicit-witness lemma**
  `j_laurentQExpansion_coeff (n : ℤ) : (laurentqExpansion 1 j).coeff n =
  ((if n < -1 then 0 else qjCoeffs (n + 1).toNat : ℤ) : ℂ)`, whose right side is exactly
  `(jIntCoeff n : ℂ)` once `Cox.jIntCoeff n := if n < -1 then 0 else qjCoeffs (n + 1).toNat`;
  `j_laurentQExpansion_isIntegral` (statement kept) is now `⟨_, j_laurentQExpansion_coeff n⟩`.
* `qjCoeffs_zero` moved (same name/statement, analytic proof, no kernel evaluation) from
  `qexp_coeffs.lean` to `jfunction.lean`, so it is in the import closure of
  `Cox/CoxMatrices/LaurentExpansion.lean` (for `jIntCoeff_neg_one`).
* `ramanujanTau_cast` (Deltaqexpansions) and `qj_apply` added for the same purpose.

### Task 2 — jfunction.lean
* The whole `deltaShiftedQSeries` analyticity block (7 private lemmas, ≈ 90 lines, incl. the
  re-derivation of mathlib's private `hasFPowerSeriesOnBall_update`) is replaced by: `deltaOverQ`
  is 1-periodic (`periodic_comp_ofComplex_of_vadd`), holomorphic and bounded (it tends to `1`), so
  `UpperHalfPlane.analyticAt_cuspFunction_zero` gives analyticity; `Δ = 𝕢 · (Δ/q)` and
  `qExpansion_qpow_mul` give `qExpansion_Delta_eq_X_mul`, hence the coefficient shift
  `deltaOverQ_qExpansion_coeff` by `PowerSeries.coeff_succ_X_mul`. `deltaShiftedQSeries` and
  `deltaShiftedQSeries_eq_deltaOverQ` are kept (3-line proof via `hasSum_qExpansion`);
  `deltaShiftedQSeries_qExpansion_coeff` (trivial restatement, only used in link) deleted.
* `qOverDelta` analyticity by the same route (4 private lemmas deleted);
  `qj_cuspFunction_analyticAt` = `analyticAt_cuspFunction_zero …` (2 lemmas → 1);
  `Delta_qExpansion_coeff_zero_aux` no longer needed (deleted);
  `E4_pow_three_isModularForm_aux` deleted; `qj_mdifferentiable` = `mdifferentiable_cexp_aux.mul
  j_mdifferentiable`; `j_eq_qjCoeffs_tsum` absorbs 5 private helpers (`infSumQj_summable_aux`,
  …) into a 6-line proof; shared private helpers `cexp_vadd_one_aux`, `E4/Delta_vadd_one_aux`,
  `mdifferentiable_cexp_aux`; `cuspFunction_apply_zero_of_tendsto` made public and general
  (`0 < h`), new `isBoundedAtImInfty_of_tendsto` (used 3×).
* `qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3` (×4) → `ModularForm.qExpansion_coe_pow` +
  `E4_pow_three_qExpansion` / `E6_pow_two_qExpansion` (Deltaqexpansions).
* `j_cuspFunction_not_analyticAt` kept (genuine).

### Task 3 — jLevelN.lean
* Deleted `jN_cuspFunction_meromorphicAt` and its 8 private helpers (`qjN`, `qjN_periodic_aux`,
  …, `jN_cuspFunction_eq_aux`; 75 lines, 0 users): it is the `γ = 1` case of
  `Cox.levelJ_meromorphicAt_cusp` / `Cox.levelJ_cuspData` (docstring now points there). The
  period-N note is moot with it.
* New `UpperHalfPlane.natScale N τ := (⟨N, _⟩ : {x : ℝ // 0 < x}) • τ` (mathlib `posRealAction`),
  `@[simp] coe_natScale`, `jN N z := j (natScale N z)` (same function; `Cox.levelJ_apply` is
  now `rfl`, its existing proof still compiles), `jN_apply`. Γ₀(N)-conjugation identity and
  `gamma0Conjugate`'s determinant proof reduced to `obtain ⟨c, hc⟩; simp only; push_cast; ring`
  / `linear_combination` (26 + 11 → 9 + 7 lines).

### Task 4 — Deltaqexpansions.lean
* E4/E6 twins shortened to 1–3 lines each through the cast-form coefficient lemmas; new public
  `integralE4_coeff`/`integralE6_coeff` (`if n = 0 then 1 else 240 σ₃(n)` / `-504 σ₅(n)`), which
  makes link's `e4/e6CoeffInt_eq_integral…_coeff` `.symm`.
* `three/four/twelve_dvd_weighted_powers_aux` → one `decide` over `ZMod 12` inside
  `twelve_dvd_weighted_sigma_aux`.
* The 1728-divisibility chain (`remainder_coeff_dvd_aux`, `…_modEq_linear_aux`,
  `linear_coeff_eq_aux`, `…_modEq_aux`, `…_coeff_dvd_aux`, 47 lines) → one 22-line lemma
  (`E₄³ − E₆² = (e₄³ + 3e₄² − e₆²) + (3e₄ − 2e₆)`), plus the kept closure `coeff_mul_dvd_aux` /
  `coeff_pow_dvd_aux`; `integralE4/E6_constantCoeff_aux`, `…_coeff_dvd_aux` deleted.

### Task 6 — Qj.lean (perf-sensitive, timed: §7)
* `sigmaPow` deleted: `e4CoeffInt n := if n = 0 then 1 else 240 * (σ 3 n : ℤ)` (mathlib
  `ArithmeticFunction.sigma`; import `ArithmeticFunction.Misc`).
* Tabulations → `coeffArray f n := Array.ofFn …` (structural in this toolchain);
  `convArrayUpTo`, `deltaCoeffsArrayUpTo`, `deltaOverQArrayUpTo` defined through `coeffArray`;
  `convArrayCoeff` and the inversion step are `Finset.range` sums.
* Named loop step `invStep` (shared with link's loop invariant).
* `reportTiming := true` → `register_option qexp.reportTiming` (default `false`; Examples turns it on
  for one command); unreachable "empty output" branches removed (timing now brackets the evaluation
  and the logging, so it stays meaningful); `qj/Delta_qexpansion_coeff_eq` = `coeff_mk`.

### Task 7 — link.lean
* Deleted `foldl_range_add_eq_sum`, `foldl_push_toList`, `foldl_push_getD`, `mk_coeff_self`
  (the convolution lemma is stated for arbitrary `F G : ℤ⟦X⟧`), `foldl_sigma_search_eq_sum`,
  `sigmaPow_eq_sigma`, `int_cast_div_eq_inv_mul_complex` (→ `Int.cast_div_charZero` inline),
  dead `E6_int_link`, dead `qoverDeltaCoeffInt_zero`.
* Generic helpers `array_getD_eq_toList_getD`, `getD_map_range`, `coeff_invOfUnit_one_succ` moved
  into `namespace XYin.PhD.qExpansion_tactic` (no users elsewhere).
* Copyright header + module docstring (the `set_option linter.style.header false` escape is gone);
  docstrings on `Delta_qexpansion_link`, `qj_qexpansion_link` and 12 further lemmas.

### Task 8 — Tactic2 + tests
* 11 exact aliases deleted and replaced by `attribute [qexp_simps]` on the mathlib lemmas
  (`SlashInvariantFormClass.periodic_comp_ofComplex`, `ModularFormClass.holo`, `.bdd_at_infty`,
  `.analyticAt_cuspFunction_zero`, `CuspFormClass.zero_at_infty`, `.cuspFunction_apply_zero`,
  `MDifferentiable.mul/add/sub/neg/const_smul`); the macro applies the mathlib names.
* The two 21-line macros → one `syntax "qexp_simp" (" [" simpLemma,* "]")?` + `macro_rules` and a
  helper `qexp_simp_core`; `simp (config := { maxDischargeDepth := 20 })` ×16 →
  `simp (maxDischargeDepth := 20)`; `sub_eq_add_neg` removed from the simp set (it made the `_sub`
  lemmas dead; tests pass); deprecated import fixed; headers/docstrings in both Tactic2 files.
* `QExpSimpConditionTests`: header + module docstring, the 5 no-op `noncomputable example` →
  `example`; all tests pass. `Examples.lean`: redundant `open scoped` dropped.

### Task 9 — qexp_coeffs.lean
* All public lemmas kept (statements unchanged); added `ramanujanTau_four/five`. Each value is now
  certified once on the ℤ side (`rfl`), the ℂ-valued lemmas are derived through
  `ramanujanTau_cast`/`qjCoeffs_cast` (kernel evaluations 16 → 9; `qjCoeffs_zero` is analytic);
  `exists_int_coeff_j_eq_principal_part_add_tsum_with_initial` is a term (11 → 3 lines); the
  Laurent values are one `simpa` each through `j_laurentQExpansion_coeff_sub_one`.

## 4. New public API (exact statements)

Deltaqexpansions.lean:
* `ModularForm.qExpansion_coe_pow [Γ.HasDetPlusMinusOne] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : ModularForm Γ k) (n : ℕ) : qExpansion h (⇑f ^ n) = qExpansion h f ^ n`
* `E4_pow_three_qExpansion : qExpansion 1 (E4 ^ 3) = qExpansion 1 E4 ^ 3`; `E6_pow_two_qExpansion : qExpansion 1 (E6 ^ 2) = qExpansion 1 E6 ^ 2`
* `integralE4_coeff (n) : integralE4.coeff n = if n = 0 then 1 else 240 * (sigma 3 n : ℤ)`; `integralE6_coeff (n) : integralE6.coeff n = if n = 0 then 1 else -504 * (sigma 5 n : ℤ)`
* `ramanujanTau_cast (n : ℕ) : ((ramanujanTau n : ℤ) : ℂ) = (qExpansion 1 Delta).coeff n`

jfunction.lean:
* `cuspFunction_apply_zero_of_tendsto (hh : 0 < h) (hf : Tendsto f atImInfty (𝓝 a)) : cuspFunction h f 0 = a` (was private, `h = 1`)
* `isBoundedAtImInfty_of_tendsto (hf : Tendsto f atImInfty (𝓝 a)) : IsBoundedAtImInfty f`
* `deltaOverQ_cuspFunction_analyticAt : AnalyticAt ℂ (cuspFunction 1 deltaOverQ) 0`
* `qExpansion_Delta_eq_X_mul : qExpansion 1 Delta = X * qExpansion 1 deltaOverQ`
* `deltaOverQ_qExpansion_coeff (n : ℕ) : (qExpansion 1 deltaOverQ).coeff n = (qExpansion 1 Delta).coeff (n + 1)`
* `qj_apply (τ : ℍ) : qj τ = 𝕢 1 τ * j τ`
* `qjCoeffs_cast (n : ℕ) : ((qjCoeffs n : ℤ) : ℂ) = (qExpansion 1 qj).coeff n` (was private `qj_coeff_cast_aux`)
* `qjCoeffs_zero : qjCoeffs 0 = 1` (moved here from qexp_coeffs, unchanged)
* `j_laurentQExpansion_coeff_of_neg_one_le (hn : -1 ≤ n) : (laurentqExpansion 1 j).coeff n = (qExpansion 1 qj).coeff (n + 1).toNat`
* `j_laurentQExpansion_coeff_sub_one (n : ℕ) : (laurentqExpansion 1 j).coeff ((n : ℤ) - 1) = (qExpansion 1 qj).coeff n` (was private in qexp_coeffs)
* `j_laurentQExpansion_coeff (n : ℤ) : (laurentqExpansion 1 j).coeff n = ((if n < -1 then 0 else qjCoeffs (n + 1).toNat : ℤ) : ℂ)`

jLevelN.lean:
* `UpperHalfPlane.natScale (N : ℕ) [NeZero N] (τ : ℍ) : ℍ := (⟨(N : ℝ), _⟩ : {x : ℝ // 0 < x}) • τ`
* `@[simp] UpperHalfPlane.coe_natScale : (natScale N τ : ℂ) = N * τ`; `jN_apply : jN N τ = j (natScale N τ)` (rfl)

qexp_coeffs.lean: `ramanujanTau_four : ramanujanTau 4 = -1472`, `ramanujanTau_five : ramanujanTau 5 = 4830`.

Qj.lean: option `qexp.reportTiming : Bool` (default `false`); `invStep (a acc : Array Int) : ℕ → Array Int`.

link.lean: `qjCoeffs_eq_qjCoeffInt (n : ℕ) : qjCoeffs n = qjCoeffInt n` (was private in qexp_coeffs).

Tactic2: syntax `qexp_simp_core [lemmas]` (helper) and the unified `qexp_simp` / `qexp_simp [lemmas]`.

Removed public declarations (all with 0 users outside the owned set; build green):
`deltaShiftedQSeries_qExpansion_coeff`, `jN_cuspFunction_meromorphicAt`, link's
`foldl_range_add_eq_sum`, `foldl_push_toList`, `foldl_push_getD`, `mk_coeff_self`,
`foldl_sigma_search_eq_sum`, `sigmaPow_eq_sigma`, `E6_int_link`, `int_cast_div_eq_inv_mul_complex`,
`qoverDeltaCoeffInt_zero`; Qj's `reportTiming`, `sigmaPow`; the 11 `QExpSimp` aliases. Renamed by
namespacing (0 outside users): `array_getD_eq_toList_getD`, `getD_map_range`,
`coeff_invOfUnit_one_succ` → `XYin.PhD.qExpansion_tactic.*`.

## 5. Kept on purpose (genuine, unused or test-only)
`j_cuspFunction_not_analyticAt`; `deltaShiftedQSeries` + `deltaShiftedQSeries_eq_deltaOverQ`;
`qj_differentiableAt_of_im_pos`; `PeriodPair.weierstrassCurve_c₆`, `UpperHalfPlane.ellipticCurve_j`;
all explicit-value lemmas of `qexp_coeffs.lean`; the closure lemmas `QExpSimp.analyticAt_cuspFunction_{mul,add,sub,neg,smul}`,
`QExpSimp.periodic_comp_ofComplex_{mul,add,sub,neg,smul}` (not aliases: they compose `Periodic.*`
with `Pi.*_comp`; `Periodic.neg` negates the period), `QExpSimp.isBoundedAtImInfty_{mul,add,sub,neg,smul}`
(restatements of `BoundedAtFilter.*` through the non-reducible `IsBoundedAtImInfty`, needed for simp
matching), `QExpSimp.one_mem_strictPeriods_gamma1`; `coeff_mul_dvd_aux`/`coeff_pow_dvd_aux` (per task;
the `CoeffMulMem` ideal version is not shorter).

## 6. Deferred / refuted / follow-ups outside the owned set

Refuted / not done inside the set:
* `PeriodPair.weierstrassCurve_j` via `WeierstrassCurve.j_of_isShortNF`: not shorter (the formula
  `6912 a₄³ / (4a₄³ + 27a₆²)` needs a sign/inverse manipulation of the discriminant that `ring`
  cannot see; tried 2 variants in `.scratch/TestJIL.lean`); existing 4-line proof kept.
* Parametric E4/E6 lemma: after the cast-form helpers every twin is 1–3 lines; a parametric lemma
  would not shorten.
* G-17 (generalise the two private divisibility helpers to `CommSemiring`): private, no value.
* Renames (naming items): `LaurentQExpSimpTests` (never uses `qexp_simp`), `jN` vs `Cox.levelJ`,
  root-namespace placement of `cuspFunction_apply_zero_of_tendsto`/`isBoundedAtImInfty_of_tendsto`.
* `@[fun_prop]` registration for `MDiff` goals; Γ(1) → 𝒮ℒ migration of `E4`/`E6`/`Delta`.

Follow-ups needing edits outside my set (all targets exist in the merged tree once this set is merged):
* [coxb] `Cox/CoxMatrices/LaurentExpansion.lean:30–36`: define
  `jIntCoeff n := if n < -1 then 0 else qjCoeffs (n + 1).toNat`; then
  `jIntCoeff_spec n := j_laurentQExpansion_coeff n` (statement matches verbatim) and the
  `.choose` disappears; `:38–46` `jIntCoeff_neg_one` → `by simp [jIntCoeff, qjCoeffs_zero]`
  (`qjCoeffs_zero` is now in `jfunction.lean`, in the import closure); `:284–286` (`hjcoeff`) →
  `(j_laurentQExpansion_coeff_of_neg_one_le ht).trans (jIntCoeff_spec t)`; `:191–192`
  (`show qj (σ.act τ) = qParam … * j …`) → `qj_apply _`; `:241` is now the last user of the global
  `FunLike (ℍ → ℂ)` instance (`qExpansion_coeff_unique g …`).
* [coxb] `Cox/Kronecker.lean:149–157` `jIntCoeff_eq_zero_of_lt` → `if_pos hn` (after the above) or
  `by exact_mod_cast (jIntCoeff_spec n).symm.trans (j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one hn)`.
* [coxb] `Cox/LevelThree.lean:122–130` `jIntCoeff_eq_qjCoeffInt_three` →
  `Int.cast_injective (by rw [← jIntCoeff_spec, j_laurentQExpansion_coeff_sub_one, ← qjCoeffs_cast, qjCoeffs_eq_qjCoeffInt])`
  (or `by simp [jIntCoeff]; exact qjCoeffs_eq_qjCoeffInt n` after the redefinition).
* [final] `Cox/LatticeJ.lean:615` `show qj τ = q τ * j τ by simp [q, qj, Periodic.qParam]` → `qj_apply τ`.
* [final] `Cox/ModularFunction/LevelJ.lean:29–39`: `natScaleUpperHalfPlane N` is
  `UpperHalfPlane.natScale (N : ℕ)` (same term); `levelJ_apply` is `rfl`; `coe_natScaleUpperHalfPlane`
  → `coe_natScale`; also `Cox/Arithmetic.lean:199–202`.
* [final] `Modularforms/Eisenstein.lean`: `qExpansion_ext` now has 0 users (delete); the global
  `instance : FunLike (ℍ → ℂ) ℍ ℂ` is needed only by `LaurentExpansion.lean:241` (its docstring
  still cites `XYin.PhD.jFunction` — stale).
* Merge note: `jN`'s body changed form (`j (natScale N z)`, same function); every external use
  (`LevelJ`, `CoxMatrices/Basic.lean:633 j_act_sigmaZero`, `Arithmetic`) compiled unchanged in
  this sandbox. New root-level names that other workers must not reuse: see §4.

## 7. Perf (kernel-computation files; `lake env lean F`, 2 runs each)

Qj/link/qexp_coeffs definitions changed (σ via `ArithmeticFunction.sigma`, `Array.ofFn`,
`Finset.range` sums, `invStep`). Wall clock is load-dependent (three workers share the machine),
so "before" was re-measured in the same session by temporarily restoring the SB.base versions of
all my files, rebuilding, timing, and restoring (CPU = user+sys of the `lean` process):

| File | before (SB.base, same session) | after (final tree) | early baseline (low load) |
|---|---|---|---|
| `jFunction/qexp_coeffs.lean` | 7.85 / 7.28 s (cpu 6.02 / 5.58) | 7.97 / 8.62 s (cpu 5.55 / 5.79) | 5.11 / 4.95 s |
| `qExpansion_tactic/link.lean` | 8.13 / 7.97 s (cpu 6.72 / 6.54) | 9.19 / 7.74 s (cpu 6.14 / 5.66) | 5.08 / 5.23 s |
| `Cox/LevelThree.lean` | 17.43 / 17.74 s (cpu 26.36 / 27.03) | 18.20 / 17.93 s (cpu 26.36 / 27.46) | 13.09 / 12.27 s |
| `qExpansion_tactic/Qj.lean` | 66.1 (outlier) / 5.87 s (cpu 6.25 / 3.84) | 6.01 / 5.87 s (cpu 3.88 / 3.89) | 3.76 / 3.87 s |

Worst wall ratio 1.18× (qexp_coeffs, within run-to-run noise), CPU ratios ≤ 1.04×; nothing close
to 1.5×. Micro-benchmark of the engine alone (`.scratch/Bench*.lean`: 13 `decide +kernel` of
`qjCoeffInt n` as in LevelThree + 10 `rfl` checks as in qexp_coeffs, import baseline 5.4 s):
old 6.24 / 6.09 s vs combined new 6.57 / 6.27 s (kernel) and 5.48 / 5.84 vs 5.36 / 5.49 s (rfl).
`#qexp qj coeff 100` (compiled) reports 35 ms with `qexp.reportTiming`.
