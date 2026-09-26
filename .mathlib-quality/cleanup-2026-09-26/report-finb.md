# Cleanup report — integration wave B (worker `finb`), 2026-09-26

SB = `/Users/dfa25dxu/Projects/Lean/.xyin-sandboxes/finb` (base `finb.base` = main tree after the
fina/sorry merges). Owned set: all of `XYin/`, `XYinTest/`, `XYin.lean`, `XYinTest.lean`.
Inputs: `FOLLOWUPS.md` and `report-{mf,lqe,coxa,coxb,coxc,mfn,jq,fina,sorry}.md`; every item was
re-checked against the current source before acting (many were already done by earlier waves).

## 1. Final gate

`lake build` in SB (default targets `XYin`, `XYinTest`), log `SB/.scratch/build_final.log`:

```
info: XYinTest/qExpansion_tactic/Examples.lean:54:19: [1, 744, 196884, …]
Build completed successfully (3713 jobs).
```

- Warnings in the whole build log: **0**. Errors: 0.
- `grep -rnw sorry XYin XYinTest XYin.lean XYinTest.lean` → **0**.
- No `admit`, `axiom`, `maxHeartbeats`, `maxRecDepth`, `synthInstance` options introduced;
  `native_decide` mentions are byte-identical to base (docs/strings of the `qexp_coeff` tactic).
- `lake env lean …/AxiomCheck.lean` (run from SB, `SB/.scratch/axioms_final.txt`): all **27/27**
  lines `[propext, Classical.choice, Quot.sound]`.
- New/changed declarations (`SB/.scratch/AxiomNew.lean`): `transformedJSeries_injective`,
  `jIntCoeff_spec`, `jIntCoeff_neg_one`, `jIntCoeff_eq_zero_of_lt`, `jIntCoeff_sub_one`,
  `BivariatePolynomial.map_injective`, `modularPolynomial_map_complex_swap`,
  `modularPolynomialC_coeff_polynomialIn`, `levelJ_apply`, `smul_natScale_smul_eq_affine`,
  `laurentqExpansion_coxAction`, `hasse_qExpansion_principle`,
  `formalCoxPolynomial_eq_modularPolynomialC_map_j`: all `[propext, Classical.choice, Quot.sound]`.
- Headline statements: none touched (diff contains no headline statement line;
  `modularPolynomial_three_of_complex_swap` only had its last proof line changed).

## 2. Files (lines before → after); none added or deleted, `XYin.lean`/`XYinTest.lean` unchanged

| file | before | after |
|---|---|---|
| Cox/UpperHalfPlaneFunctionField.lean | 234 | 171 (−63) |
| Cox/CoxMatrices/LaurentExpansion.lean | 442 | 465 (+23: `transformedJSeries_injective`, `jIntCoeff_sub_one`, docstrings) |
| Cox/ModularPolynomial/Construction.lean | 400 | 416 (+16: moved lemma + `map_injective`) |
| Cox/ModularPolynomial/IntegralDescent.lean | 172 | 169 |
| Cox/Arithmetic.lean | 254 | 247 |
| Cox/LevelThree.lean | 383 | 376 |
| Cox/ModularFunction/CuspData.lean | 183 | 176 |
| Cox/ModularFunction/LevelJ.lean | 211 | 203 |
| Cox/DiagonalLaurent.lean | 108 | 105 |
| Cox/LatticeJ.lean | 603 | 603 |
| Cox/Section11BC.lean | 33 | 35 |
| Modularforms/Eisenstein.lean | 213 | 204 |
| **project total (XYin + XYinTest)** | **15921** | **15855** (−66) |

Import changes: `Cox/ModularPolynomial/Construction.lean` drops `XYin.PhD.Cox.FormalCoxProduct`
(unused there); `Cox/ModularPolynomial/IntegralDescent.lean` imports it directly (it uses
`formalCoxPolynomial*`). All other importers of Construction (Interpolation, Irreducibility, MFF,
…) still build unchanged.

## 3. Done items

### Item 1 — explicit `jIntCoeff` (Cox/CoxMatrices/LaurentExpansion.lean)
- `jIntCoeff n := if n < -1 then 0 else qjCoeffs (n + 1).toNat` (the `Classical.choose` on
  `j_laurentQExpansion_isIntegral` is gone; name/type unchanged; the values are pinned down by
  `jIntCoeff_spec`, statement unchanged).
- `jIntCoeff_spec := j_laurentQExpansion_coeff n` (jfunction's explicit-witness lemma, verbatim).
- `jIntCoeff_neg_one`: 4-line `rw … exact_mod_cast` → `simp [jIntCoeff, qjCoeffs_zero]`.
- `jIntCoeff_eq_zero_of_lt` (moved here from Kronecker by coxb): `exact_mod_cast` chain → `if_pos hn`.
- NEW `jIntCoeff_sub_one (n : ℕ) : jIntCoeff ((n : ℤ) - 1) = qjCoeffs n` (1-line `rw`).
- `hjcoeff` in `laurentqExpansion_coxAction_coeff_aux`: 4 lines →
  `(j_laurentQExpansion_coeff_of_neg_one_le ht).symm.trans (jIntCoeff_spec t)`.
- `poleRemoved_coxAction_aux`: the `show qj … = qParam … * j … by simp [qj, …]` detour (3 `rw`
  lines) → one `rw [poleRemoved_apply, poleOrder_coxAction_aux, qj_apply, qParam_coxAction_aux]`.
- LevelThree: private `jIntCoeff_eq_qjCoeffInt_three` (5 lines, `Int.cast_injective` + analytic
  detour through `qj_qxp_coeff_link`) deleted; its single use is
  `rw [… coeff_jUnitPowerSeries, jIntCoeff_sub_one, qjCoeffs_eq_qjCoeffInt]`.
- IntegralDescent `mem_lifts_of_eval₂_mem`: the integrality witness `⟨jIntCoeff n, …⟩` now goes
  through an explicit `have hj : laurentqExpansion 1 j ∈ integerCoeffLaurentSeries` (needed after
  item 3, see below).
- Timing: see §7 (≈1.0×).

### Item 2 — one ℕ-scaling API
- Deleted `Cox.natScaleUpperHalfPlane` and `Cox.coe_natScaleUpperHalfPlane` (LevelJ.lean): the
  same term as jq's `UpperHalfPlane.natScale (N : ℕ)` (for `N : ℕ+` the instance
  `NeZero.pnat` fires).
- `levelJ N := jN N` (was `@jN (N : ℕ) ⟨PNat.ne_zero N⟩`; same term up to the `Prop` instance).
- `levelJ_apply : levelJ N τ = j (natScale N τ) := rfl` (was an `ext` proof; now documented).
- `smul_natScale_smul_eq_affine` (LevelJ) and Arithmetic's `diagonalFixedPoint_scale_eq`
  restated with `natScale` / `coe_natScale`.
- LatticeJ `inv_j_sub_isZeroAtImInfty_aux`: `show qj τ = q τ * j τ by simp [q, qj, Periodic.qParam]`
  → `… from qj_apply τ`.

### Item 3 — Eisenstein.lean global instance and dead lemma
- Deleted `qExpansion_ext` (0 users anywhere; verified by grep).
- Deleted the global `instance : FunLike (ℍ → ℂ) ℍ ℂ` (and its stale docstring). No declaration
  needs it: LaurentExpansion's `to_qExpansion_coxAction_aux` already uses a local `letI`. One
  elaboration accident surfaced: IntegralDescent's `pow_mem (fun n ↦ ⟨jIntCoeff n, …⟩) _` only
  elaborated with the global instance present (the membership type `?x ∈ ?S` was unresolved);
  fixed by the typed `have hj` above. Full build green, no new warnings.
- (The `Mathlib.Tactic.NormNum.BigOperators` re-export was already removed by fina's post-merge
  patch; LevelThree imports it directly.)

### Item 4 — Construction / IntegralDescent / LevelThree / Kronecker
- `modularPolynomial_map_complex_swap` moved Arithmetic → IntegralDescent (right after
  `modularPolynomial_map_complex`, next to the definition of `modularPolynomial`); Arithmetic's two
  uses unchanged. (The LevelThree ≈:753–757 site that wanted it no longer exists: coxb inlined it.)
- `simp only [BivariatePolynomial.map]` at LevelThree ≈:742/750 and Kronecker ≈:504/522: those
  sites no longer exist (coxb rewrote them as direct terms). NEW
  `BivariatePolynomial.map_injective (hf : Injective f) : Injective (map f)` (Construction);
  `modularPolynomial_three_of_complex_swap`'s 2-line `Polynomial.map_injective` nest → 1 line.
- `modularPolynomialC_coeff_polynomialIn` moved IntegralDescent → Construction, right after
  `modularPolynomialC_specializeY` (same name/statement/proof).
- `import XYin.PhD.Cox.FormalCoxProduct` moved from Construction to IntegralDescent.
- `.2.2 1` projections: IntegralDescent had none left; DiagonalLaurent's private
  `j_widthM_cuspMeromorphicAt` (`(j_cuspData m).2.2 1`) deleted, its single use inlined as
  `by simpa using (j_cuspData m).meromorphicAt_cuspFunction 1`.
- IntegralDescent ≈:177–183: already `meromorphicAt_cuspFunction_neg (coxRoot_cuspMeromorphicAt m σ)`
  (equally short; left). ≈:240–243: `periodic_comp_of_slashInvariant_one
  (coxPhiFunction_coeff_slashInvariant m n)` → `(coxPhiFunction_coeff_cuspData m n).periodic`;
  the wrapper `Cox.periodic_comp_of_slashInvariant_one` (CuspData, alias of
  `UpperHalfPlane.periodic_comp_ofComplex_of_slashInvariant`, kept by fina only for this use) now
  has 0 users and was deleted.

### Item 5 — `transformedJSeries_injective`
- NEW public `Cox.transformedJSeries_injective (m) : Injective (transformedJSeries (zeta m))` in
  CoxMatrices/LaurentExpansion.lean, proved from the existing API: equal series have equal
  `order` (`transformedJSeries_order` ⇒ `a² = a'²` ⇒ `a = a'` via `Nat.pow_left_injective`, then
  `d = d'` from `a d = m`) and equal `leadingCoeff` (`transformedJSeries_leadingCoeff` ⇒
  `ζ_m^(a(b'−b)) = 1` ⇒ `d ∣ b' − b` via `zpow_eq_one_iff_dvd`, `mul_dvd_mul_iff_left`) ⇒
  `CoxMatrix.ext`. 17 lines.
- UHPFF: private `transformed_leading_ne`, `cox_a_le`, `transformed_phase`, `cox_b_eq`,
  `transformed_injective` (66 lines) deleted; `conjugate_injective` uses the new lemma.
- NOT done: dropping the `-(a²) ≤ k` clause from `transformedJSeries(_coeff)`. It is no longer
  blocked by UHPFF, but it would make things longer, not shorter: the clause keeps the
  `ofSuppBddBelow` support proofs trivial and keeps `transformedJSeries`,
  `jLaurentSeriesWidth` and `cyclotomicTransformedJSeries` in one shape, which
  `transformedJSeries_eq_jLaurentSeriesWidth` (a `simp only`), `cyclotomicTransformedJSeries_map`,
  `transformedJSeries_order` and the `change` in `laurentqExpansion_coxAction_coeff_aux` rely on;
  every other user (`split_ifs` in FCP ×3, Kronecker) is shape-agnostic. Kept as is.

### Item 6 — stale text
- Method: extracted the 669 declaration names that existed in the pre-cleanup backup
  (`.mathlib-quality/backups/pre-cleanup-2026-09-26.tar.gz`) but no longer exist, and searched
  all comments/docstrings of the current tree for them (plus `IsCuspForm`, `eta.lean`, `csqrt`,
  `Summability`, `qExpansion_lems`, `natScaleUpperHalfPlane`, `still open`, `sorry`, …): only
  false positives (common words such as "constant", "sublattice"; live namespaces). Then a Lean
  meta check (`SB/.scratch/CheckTicks.lean`) that every backticked identifier in a
  comment/docstring resolves (as a suffix/prefix of some constant or a module name): 41
  unresolved, all intentional (file names in the ProjectVD provenance note and Kronecker/Qj docs,
  partial module paths, lemma-family suffixes `_add`/`_sub`…, math notation `Φ_m`, `ζ_p`, `j_N`,
  tactic names `native_decide`, `qexp_simp`, `qexp_coeff`, local names). `dim_gen_cong_levels`'s
  docstring is already current (sorry worker).
- Fixed: `Cox/Section11BC.lean` umbrella now also lists the subfield forms of Thm 11.9
  (`theorem_11_9_i_subfield`, `theorem_11_9_ii_subfield`, added by fina);
  LaurentExpansion module docstring mentions `transformedJSeries_injective`; new docstrings on
  `jIntCoeff`, `jIntCoeff_spec`, `jIntCoeff_neg_one`, `levelJ_apply`; the stale FunLike docstring
  disappeared with the instance.
- NOT in my set: `PROJECT_OVERVIEW.md` (see §6).

### Item 7 — global lint (`SB/.scratch/Lint.lean`, imports `XYin` + `Batteries.Tactic.Lint`)
- `#lint only simpNF simpComm simpVarHead unusedArguments defLemma docBlame synTaut in XYin`:
  **0 errors in 1329 declarations** (+1187 auto-generated).
- `#lint- in XYin` (full default set, 16 linters): only `defsWithUnderscore`, all pre-existing
  names — the whole `XYin.PhD.qExpansion_tactic` namespace (underscore in the namespace;
  jq's new `coeffArray`/`invStep` are flagged only for that reason), `UpperHalfPlane.to_qExpansion`,
  `Cox.coxPhiFunction_coeff_modularFunction`, auto-named `PeriodPair.instSMulUnitsComplex_xYin`.
  Naming items → deferred (no style renames).
- Opt-in linters (not chased, reported): `explicitVarsOfIff` flags 15 iff lemmas (incl. the headline `theorem_11_23`, `j_eq_iff_exists_sl2_smul_eq`, whose statements must not change), of which today's
  are `Cox.modularPolynomialC_eval_eq_zero_iff` (coxc), `Matrix.isColumnHermiteNormalForm_fin_two_iff`
  (coxa), `UpperHalfPlane.isBoundedAtImInfty_exp_mul_iff_isBigO` (mfn); making the variables
  implicit is a binder change of used API (call sites pass them explicitly) → deferred.
  `docBlameThm` (theorem docstrings, not required by mathlib) lists ≈ 300 theorems, mostly
  structure-field/simp/`ext` lemmas.

### Item 8 (optional) — LevelThree jets vs `qExpansion_tactic/Qj.lean`: not done
- The overlap is superficial: LevelThree's jets are function-level (`ℕ → ℤ`: `jetMul`, `jetPow`,
  `jetShift`, `jetExpand`, 13 lines) with PowerSeries-coefficient correctness lemmas
  (`powerSeries_coeff_{mul,pow,shift}_eq_jet…`); Qj's layer is memoized `Array Int` tables
  specialised to E₄/E₆/Δ/q/Δ/qj. Only the 2-line convolution sum is shared; merging would need
  array↔function bridge lemmas (more code) and would change what the `decide +kernel`
  certificate reduces. Condition "deletes code" fails → skipped.

## 4. New public API
- `Cox.jIntCoeff_sub_one (n : ℕ) : jIntCoeff ((n : ℤ) - 1) = qjCoeffs n`
- `Cox.transformedJSeries_injective (m : ℕ+) : Function.Injective (transformedJSeries (zeta m) : CoxMatrix m → LaurentSeries ℂ)`
- `Cox.BivariatePolynomial.map_injective {f : R →+* S} (hf : Function.Injective f) : Function.Injective (BivariatePolynomial.map f)`
- Moved (same name/statement): `Cox.modularPolynomial_map_complex_swap` (Arithmetic → IntegralDescent),
  `Cox.modularPolynomialC_coeff_polynomialIn` (IntegralDescent → Construction).
- Changed form (same type/meaning, all uses updated): `Cox.jIntCoeff` (explicit body),
  `Cox.levelJ` (`jN N`); `Cox.levelJ_apply` and `Cox.smul_natScale_smul_eq_affine` now stated
  with `UpperHalfPlane.natScale` (0 users outside the Cox files, all updated).
- Deleted: `Cox.natScaleUpperHalfPlane`, `Cox.coe_natScaleUpperHalfPlane` (duplicate of
  `UpperHalfPlane.natScale`/`coe_natScale`), `Cox.periodic_comp_of_slashInvariant_one` (alias),
  `qExpansion_ext` (dead), the global `FunLike (ℍ → ℂ) ℍ ℂ` instance; private
  `jIntCoeff_eq_qjCoeffInt_three`, `j_widthM_cuspMeromorphicAt`, UHPFF `transformed_leading_ne`,
  `cox_a_le`, `transformed_phase`, `cox_b_eq`, `transformed_injective`.

## 5. Kept on purpose
- `j_laurentQExpansion_isIntegral` (jfunction; now 0 users, but it is the headline-style
  "every Laurent coefficient of j is an integer" statement, 1 line).
- `BivariatePolynomial.mapRingHom`, `coe_mapRingHom`, `map_sub` (coxc API, currently 0 users;
  genuine bundled/API forms).
- `transformedJSeries`' `-(a²) ≤ k` clause (§3 item 5).
- `conjugate_injective` stays private in UHPFF (its only user).

## 6. Deferred (with reason)
- `PROJECT_OVERVIEW.md` (main-tree root, not in my owned set) is the 2026-09-25 pre-cleanup
  analysis and is stale throughout, e.g. :4/:38/:136 "active sorry: 1 (`dim_gen_cong_levels`)",
  :139–155 per-file rows for deleted files (`Eisensteinqexpansions`, `IsCuspForm`, `NormNumI`,
  `Summability/*`, `csqrt`, `eta`, `qExpansion_lems`), :222 `natScaleUpperHalfPlane`, :277/:340
  the deleted `jIntegralLaurentSeries`/`jUnitLaurentSeriesMod`/`jLaurentSeriesMod`/
  `unitJPowerSeries`/`qjIntegralPowerSeriesThree`, :279 the global `FunLike` instance. Needs a
  regenerated overview (or a "superseded by 2026-09-26 cleanup" banner) by the orchestrator.
  Same for the user's memory notes (sorry report).
- Naming (no style renames): `defsWithUnderscore` hits above (namespace `qExpansion_tactic`,
  `to_qExpansion`, `coxPhiFunction_coeff_modularFunction`, instance `…_xYin`);
  `explicitVarsOfIff` binder changes; plus the earlier waves' naming lists.
- `transformedJSeries` clause removal (not an improvement, §3 item 5); LevelThree/Qj jet merge
  (no deletion, §3 item 8).
- Earlier waves' deferred design items remain deferred: `substMonomial` bridge,
  `laurentqExpansionRingHom` (refuted), `CuspData` as a structure, SL₂ `MulAction` on the
  meromorphic field, Γ(1) → 𝒮ℒ migration of `E4/E6/Delta`, G-13/14/26/30.

## 7. Perf (kernel-computation file touched: `Cox/LevelThree.lean`)
`/usr/bin/time -p lake env lean XYin/PhD/Cox/LevelThree.lean` (real / user, seconds):
- Before any change (21:52, original tree): 29.15 (cold) / 15.25 / 15.09 / 14.99; user 16.1–16.8.
- After item 1 (22:03): 15.30 / 16.87 / 15.41 / 14.98; user 16.1–17.0 (one further run stalled at
  473 s wall with unchanged 16.7 s user — a machine stall, not compile time).
- Final tree (22:40, lower load): 9.68 / 9.37 / 9.61; user 10.6–11.0.
- Interleaved A/B on identical upstream (base LevelThree file vs final file, both compiled from
  `.scratch/` against the final oleans): base 9.60 / 9.62 (user 10.80 / 10.94), new 9.64 / 9.68
  (user 10.96 / 10.99) → **1.0×**. None of the `decide +kernel` certificates reduces anything I
  changed (they evaluate `qjCoeffInt` and the jets; `jIntCoeff` is never kernel-reduced).
- `Qj.lean`, `link.lean`, `qexp_coeffs.lean`: not edited.
