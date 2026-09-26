# Step 8 — Junk identification, project-wide (83 files), 2026-09-25

Method. (1) Every one of the 336 rows of `_public-unused-candidates.tsv` was re-grepped with a
Unicode-aware word-boundary matcher over `XYin/**/*.lean`, `XYin.lean`, `ScratchGS.lean`
(dot-notation `.name` and `open`-namespace uses count as hits; docstring mentions do not).
Result: 249 rows have zero code hits, 87 rows are used only through dot-notation / `open`
namespaces / `Fintype` instances and were false positives of the TSV (all listed in §5 as KEEP).
(2) A declaration-level dependency graph over all 1,792 declarations was built (body of each
declaration scanned for the short name of every other declaration; conservative over-approximation
because short-name collisions such as `add`, `mul`, `swap`, `E`, `j` are counted as uses).
Two closures were computed: (a) the `Modularforms/` subtree with roots = every declaration outside
the subtree, and (b) a global cascade with roots = KEEP-TERMINAL names + all instances/structures +
the `#qexp` meta layer. Everything reported REMOVE-DEAD below is dead in the *conservative* graph,
so cascades are real, not artefacts. (3) Every "Junk candidates" section of the 83 inventories and
all 84 entries of the July report were re-verified against current line numbers.
(4) No builds were run; `@[simp]` lemmas and anonymous instances are flagged "rebuild check".

Line counts: project 19,649 lines (83 files under `XYin/` + `XYin.lean`) + `ScratchGS.lean` 11.
`XYin/PhD/Modularforms/` = 26 files, 4,263 lines.

## 1. Summary table

| Verdict | Entries | Lines |
|---|---|---|
| REMOVE-FILE (whole file dead / 100 % mathlib / test-only) | 33 files | 4,709 gross; ≈ 4,580 net after relocating ≈ 130 live lines (Delta core 70, Eisenstein 20, SlashActionAuxil 37, `standardcongruencecondition` 1, sorry 3) |
| REMOVE-DEAD (declarations in files that stay) | 83 declarations (46 entries) | 569 |
| REMOVE-WRAPPER | 6 | 24 |
| REPLACE (mathlib duplicate with call sites; incl. LevelThree jet split) | 15 | ≈ 300 (LevelThree jet split ≈ 210, Delta/Eisenstein core ≈ 60, rest ≈ 35) |
| INLINE | 7 | 45 |
| Non-declaration junk (comments, imports, `variable`, headers, `open`, escapes, placeholders, unreachable branches, instances) | 74 items | ≈ 120 |
| KEEP-TERMINAL | 47 (28 TSV rows + 19 used headline results named in §3) | — |
| KEEP (TSV rows with grep-verified real uses) | 56 | — |

Total removable from the library: **≈ 5,300 lines of 19,660 (27 %)** without any mathematical loss
(≈ 4,580 whole-file + 569 declaration + 24 wrapper + 45 inline + ≈ 120 non-declaration), plus ≈ 300
lines that collapse under REPLACE. Of the 4,263 lines in `Modularforms/`, at most ≈ 150 survive
(≈ 21 once `Delta`/`E₄`/`E₆` are retargeted to `CuspForm.discriminant`/`ModularForm.E₄`/`E₆`).

Top 15 removals by lines (see §2/§3 for evidence):
1. `Modularforms/Eisenstein.lean` — 672 of 692 lines dead (66/71 decls); live: `E₄` :55-57, `E₆` :59-60, `bernoulli'_six` :287-292, `Delta_q_one_term` :374-377.
2. `Modularforms/ResToImagAxis.lean` — 403 (only consumers are the dead imaginary-axis blocks Delta:282-408, Eisenstein:434-692).
3. `Modularforms/Delta.lean` — 338 of 408 dead now; all 408 after REPLACE by `CuspForm.discriminant`.
4. `Modularforms/Summability/Reciprocal.lean` — 297 (0 live).
5. `Modularforms/Summability/QExpansion.lean` — 296 (0 live).
6. `Tactic2/*` — 328 (qexp_simp 207 + tests 118 + attr 3), library-unused; move to `test/`.
7. `Modularforms/SlashActionAuxil.lean` — 250 of 287 (Γ(2) chain + wrappers); 37 live lines feed only `Delta.lean:62`.
8. `Modularforms/Summability/Basic.lean` — 206 (all 3 "live" decls are used only by dead code).
9. `Modularforms/NormNumI.lean` — 205 (vendored `norm_numI`, invoked nowhere).
10. `Modularforms/DimensionFormulas.lean` — 200 (every proved statement is a Γ(1)-transport of mathlib `LevelOne/DimensionFormula.lean`; only the `sorry` `dim_gen_cong_levels` :198-200 carries content).
11. `Cox/LevelThree.lean:349-557` — ≈ 210 lines of term/row/chunk jet split collapsible to 1–2 `decide +kernel` declarations (REPLACE, not dead).
12. `Modularforms/Eisensteinqexpansions.lean` — 154 of 155 (`standardcongruencecondition` :20 is the only live line).
13. `Modularforms/IsCuspForm.lean` — 152 (100 % mathlib `CuspFormSubmodule.lean`; only consumer is DimensionFormulas).
14. `Modularforms/tsumderivWithin.lean` — 138 (0 live).
15. `LaurentQExpansion/LaurentQExpansion.lean:600-706` — 107-line circle-integral subtree with zero consumers; plus `MeromorphicField.lean` 20 dead decls / 113 lines.

## 2. Whole-file verdicts (evidence: subtree closure (a); "importers" from `_import-graph.md`)

Notation: `live` = reachable from a declaration outside `Modularforms/`.

| File | Lines | Decls live/total | Verdict | Live declarations to relocate / retarget | Importers (besides `XYin.lean`) |
|---|---|---|---|---|---|
| `Modularforms/BigO.lean` | 61 | 0/8 | REMOVE-FILE | none (`linear_bigO` = `EisensteinSeries.linear_inv_isBigO_right`, `linear_bigO'` = `linear_inv_isBigO_left`, Summable.lean:186) | Summability/Reciprocal:10 (dead) |
| `Modularforms/clog_arg_lems.lean` | 94 | 0/8 | REMOVE-FILE | none; `arg_pow_aux` :18-51 is the only non-mathlib content (real-valued `arg_pow`) — park in git | Delta:4 (import unused) |
| `Modularforms/eta.lean` | 81 | 0/4 | REMOVE-FILE | none (1:1 image of mathlib Discriminant.lean:66-143) | Delta:5 (import unused) |
| `Modularforms/csqrt.lean` | 57 | 0/5 | REMOVE-FILE | none (`csqrt z` = `z ^ (1/2 : ℂ)` for `z ≠ 0`) | eta:4 |
| `Modularforms/equivs.lean` | 46 | 0/6 | REMOVE-FILE | none (`negEquiv` = `Equiv.neg ℤ`; root `swap` hits in Cox files are `BivariatePolynomial.swap`) | Summability/Basic:11 |
| `Modularforms/upperhalfplane.lean` | 17 | 0/2 | REMOVE-FILE | none (`pnat_div_upper` = `UpperHalfPlane.im_pnat_div_pos`; callers eta:37,68,70 are dead) | eta:5, Reciprocal:11 |
| `Modularforms/exp_lems.lean` | 29 | 0/3 | REMOVE-FILE | none (`exp_upperHalfPlane_lt_one` = `UpperHalfPlane.norm_exp_two_pi_I_lt_one`; all 9 call sites are in dead files) | Summability/Basic:10, tsumderivWithin:12 |
| `Modularforms/AtImInfty.lean` | 27 | 0/3 | REMOVE-FILE | none (`Filter.eventually_atImInfty` :14-16 is a 3-line ForMathlib candidate; re-add if wanted) | ResToImagAxis:11 |
| `Modularforms/IsCuspForm.lean` | 152 | 0/17 | REMOVE-FILE | none — entire file is mathlib `CuspFormSubmodule.lean` (`IsCuspForm` :73, `toCuspForm` :127, `isCuspForm_iff_coeffZero_eq_zero` :136); sole consumer DimensionFormulas (dead) and Eisenstein `Delta_E4_E6_aux` :326-329 (dead) | Eisenstein:9 |
| `Modularforms/DimensionFormulas.lean` | 200 | 0/30 | REMOVE-FILE | relocate the `sorry` `dim_gen_cong_levels` :198-200 to a `ForMathlib` file restated as `[Γ.FiniteIndex] → FiniteDimensional ℂ (ModularForm Γ k)`; `dimension_level_one_XYin` :193-196 = mathlib `ModularForm.dimension_level_one` (DimensionFormula.lean:249) so it is not a terminal result; `SlashInvariantForm.mul_apply` :88-90 declared into a mathlib namespace, 0 uses | — |
| `Modularforms/E2.lean` | 109 | 0/18 | REMOVE-FILE | optional salvage `E₂_S_transform` :86-91, `E₂_eq` :104-109 (12 lines, not literally in mathlib; both consumers dead) | eta:3 |
| `Modularforms/Eisensteinqexpansions.lean` | 155 | 1/15 | REMOVE-FILE | `standardcongruencecondition` :20 (1 line) → inline into `E₄`/`E₆` (Eisenstein:56,60) or move beside them; `E` :22-24 = `ModularForm.E`; `E_k_q_expansion` :149-155 used only by dead Eisenstein:236,477 | Eisenstein:8 |
| `Modularforms/Summability/QExpansion.lean` | 296 | 0/25 | REMOVE-FILE | none (`q_exp_iden` :274 = `EisensteinSeries.qExpansion_identity_pnat`) | Eisensteinqexpansions:7 (unused there), summable_lems |
| `Modularforms/Summability/Reciprocal.lean` | 297 | 0/35 | REMOVE-FILE | none (`summable_3` :233-242 only feeds QExpansion) | QExpansion:9 |
| `Modularforms/Summability/Basic.lean` | 206 | 0/25 | REMOVE-FILE | none — `a33` :107-120 is used only by Eisenstein:508 (`E_even_imag_axis_real`, dead) and by `hsum` :122-136 (dead; other `hsum` hits are local hypotheses); `sum_range_zero` :147-149 unused (Eisenstein:285,292 use `Finset.sum_range_zero`) | Eisenstein:10, multipliable_lems:4, Reciprocal:9 |
| `Modularforms/tsumderivWithin.lean` | 138 | 0/11 | REMOVE-FILE | none (`derivWithin_tsum_fun'` = `derivWithin_tsum`; `ℍ'` = `upperHalfPlaneSet`) | QExpansion:10 |
| `Modularforms/iteratedderivs.lean` | 72 | 0/6 | REMOVE-FILE | none (`exp_iter_deriv_within` = `iteratedDeriv_cexp_const_mul`; `aut_iter_deriv` = `iter_deriv_inv_linear`) | tsumderivWithin:13 |
| `Modularforms/multipliable_lems.lean` | 81 | 0/13 | REMOVE-FILE | none (`Multipliable_pow` = `Multipliable.pow`; `MultipliableEtaProductExpansion` :37-40 used only by dead Delta:329) | Delta:6 |
| `Modularforms/qExpansion_lems.lean` | 113 | 1/16 | REMOVE-FILE | `qExpansion_ext` :75-77 (= `congrArg (qExpansion 1)`): inline at `qExpansion_tactic/link.lean:250` first. `qExpansion_pow` :97-101 unused (Eisenstein:319 and Deltaqexpansions:78,232,234 resolve to mathlib `ModularForm.qExpansion_pow`, QExpansion.lean:603). Global `instance : FunLike (ℍ → ℂ) ℍ ℂ` :73 goes with the file (rebuild check) | IsCuspForm:6 |
| `Modularforms/summable_lems.lean` | 16 | 0/0 | REMOVE-FILE | facade; replace `XYin.lean:26` (nothing else imports it) | — |
| `Modularforms/NormNumI.lean` | 205 | 0/16 | REMOVE-FILE | none; `norm_numI`/`NormNumI.` referenced nowhere outside the file; declared into `Mathlib.Meta.NormNum*` namespaces (bump hazard) | Delta:10 (import unused) |
| `Modularforms/ResToImagAxis.lean` | 403 | 0/45 (outside subtree) | REMOVE-FILE | none — `ResToImagAxis`/`resToImagAxis` appear outside `Modularforms/` only in `XYin.lean:16`; all in-subtree consumers (Delta:282-408, Eisenstein:434-692) are dead. The "used-by" pollution in the graph (`.add`, `.mul`, `.pow`, `.const`) is short-name collision | Delta:7 |
| `Modularforms/SlashActionAuxil.lean` | 287 | 4/27 | REMOVE-FILE (after Delta REPLACE) | live chain (37 lines): `SL2Z_generate` :68-69, `slashaction_generators` :217-235, `slashaction_generators_SL2Z` :260-266, `slashaction_generators_GL2R` :268-273 — sole consumer `Delta.lean:62` (`Discriminant_SIF`); all three are mathlib (`SL2Z_generators.symm`, `slash_action_generators` Identities.lean:54, `slash_action_generators_SL2Z` LevelOne/Basic:56). Γ(2) chain :99-285 (≈ 190 lines) genuinely new but consumer-less → REMOVE-DEAD (park in git) | ResToImagAxis:12, E2:4, Delta:3 |
| `Modularforms/Delta.lean` | 408 | 11/41 | REMOVE-FILE via REPLACE | interim core (≈ 70 lines) :26-62 (`Δ`, `DiscriminantProductFormula`†, `Delta_eq_eta_pow`, `delta_eq_discriminant`, `Δ_ne_zero`, `Discriminant_T/S_invariant`, `Discriminant_SIF`) + :151-191 (`Delta_boundedfactor`, `Discriminant_zeroAtImInfty`, `Delta`, `Delta_apply`). Everything is mathlib: `Δ` = `ModularForm.discriminant` (Discriminant.lean:50), `Delta` = `CuspForm.discriminant` (:235), `Δ_ne_zero` = `discriminant_ne_zero` (:123), `Delta_boundedfactor` = `tendsto_atImInfty_tprod_one_sub_eta_q_pow` (:153, alias `discriminant_bounded_factor` :173), zero-at-infinity :175. Call sites to retarget: jfunction (34), Qj (11), Deltaqexpansions (7), link (5), LatticeJ (4), qexp_coeffs (4), Examples (6), QExpSimpConditionTests (2). Dead now: :64-149 (86 lines incl. global `instance natPosSMul : SMul ℕ+ ℍ` :81-82) and :193-408 (216 lines: `CuspForm_div_Discriminant` :213-270 = `CuspForm.divDiscriminant`, imaginary-axis block :282-408) | Eisensteinqexpansions:6 |
| `Modularforms/Eisenstein.lean` | 692 | 5/71 | REMOVE-FILE (keep ≈ 20 lines) | `E₄` :55-57, `E₆` :59-60 (= `ModularForm.E₄/E₆` EisensteinSeries/Basic.lean:51,54 modulo `Γ(1)` vs `𝒮ℒ`; consumers Deltaqexpansions:E4/E6), `bernoulli'_six` :287-292 (no mathlib analogue; consumers Deltaqexpansions, LatticeJ:186), `Delta_q_one_term` :374-377 (= `discriminant_qExpansion_coeff_one` via `Delta_eq_eta_pow`; consumers jfunction, link). `PowerSeries.coeff_add` :430-432 has 0 qualified uses (Cox hits are `Polynomial.coeff_add`/`HahnSeries.coeff_add`). Everything else — φ block :110-125, cusp-function utilities :134-201, `Ek_q_exp` chain :206-273, `asdf` :342-366, `E_even_imag_axis_real` :469-536, boundedness block :590-692 — is dead | DimensionFormulas:12 (dead), Deltaqexpansions:8 |
| `Modularforms/ForMathlib_Cusps.lean` | 21 | 1/2 | KEEP | `zero_at_cusps_of_zero_at_infty` :9-14 live (LatticeJ:565, Delta:189); `bounded_at_cusps_of_bounded_at_infty` :16-21 REMOVE-DEAD once Delta:213-270 goes | IsCuspForm, Delta, LatticeJ |
| `Tactic2/qexp_simp.lean` | 207 | 0 library users | REMOVE-FILE (move to `test/`) | `qexp_simp`/`qexp_simps`/`QExpSimp.` appear outside `Tactic2/` only in `XYin.lean:32`. 22/27 lemmas dead even inside the tactic (:20-22, :43-47, :54-154); genuine content worth a ForMathlib file: `analyticAt_cuspFunction_{mul,add,sub,neg,smul}` :54-81, `isBoundedAtImInfty_sub` :142-145. Macros :165-185 ≡ :187-207 (21-line duplicate); `simp (config := …)` ×16 | QExpSimpConditionTests:1 |
| `Tactic2/QExpSimpAttr.lean` | 3 | — | REMOVE-FILE (with qexp_simp) | `register_simp_attr qexp_simps`; imported by root :30 | qexp_simp |
| `Tactic2/QExpSimpConditionTests.lean` | 55 | 0 decls | REMOVE-FILE (move to `test/`) | test-only; 5 no-op `noncomputable example` :40-52 | — |
| `Tactic2/LaurentQExpSimpTests.lean` | 63 | 0 decls | REMOVE-FILE (move to `test/`) | misnamed (never uses qexp_simp); :35-40 ≡ :28-33 byte-identical | — |
| `qExpansion_tactic/Examples.lean` | 65 | 0 decls | REMOVE-FILE (move to `test/`) | `#qexp`/`#check`/`example` only; all four facts already `rfl`-proved in qexp_coeffs:71-73,108-109; :21 redundant `open scoped`; :55-65 commented-out stress test; costs 14 info messages + native evaluation per build | — |
| `qExpansion_tactic/Qj.lean:166-304` (meta layer) | 139 | used only by Examples | REMOVE-FILE-SECTION (move with Examples to `test/` or a non-library module) | `#qexp` (:234-267), `qexp_coeff` (:272-304), `QexpTarget`/`mkNativeDecideProofFor` (:166-233) referenced by no library file; the computable layer :1-165 stays (link.lean, LevelThree) | — |
| `jFunction/qexp_coeffs.lean` | 163 | 24/24 | KEEP-TERMINAL (documentation-grade) | all 18 public lemmas have 0 external uses by design (explicit τ(n), Δ and j coefficients, showcase `exists_int_coeff_j_eq_principal_part_add_tsum_with_initial` :120-134); private bridge `qjCoeffs = qjCoeffInt` :46 is the only such bridge (promote, see Step 7) | — |
| `LaurentQExpansion/LaurentQExpansion.lean:600-706` | 107 | 0/6 | REMOVE-DEAD | `qExpansion_coeff_eq_circleIntegral_of_differentiableOn` :600-609 (verbatim mathlib `qExpansion_coeff_eq_circleIntegral` with weaker hyps → upstream refactor, not project code), `exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt` :611-631, private :633-648, :650-673, :675-687, `laurentqExpansion_coeff_eq_circleIntegral` :689-706. Advertised as a main result (docstring :32-33) but consumed by nothing; July marked it KEEP-INTENTIONAL — reversed: delete and drop the docstring bullet (git keeps it) | — |
| `Cox/LevelThree.lean:349-557` (jet split) | ≈ 210 | all "live" | REPLACE | 35 private `explicitCandidateClearedJet{Term,Row}Three_*` :349-502 + `explicitCandidateLaurentEvalThree_coeff_eq_jet` :504-517 + 29-line conjunction `_observed_coefficients` :518-557 collapse to one `decide +kernel` (all ten coefficients in one call, 6.7 s per Batch M timing) once `jIntegralLaurentSeriesWidth m = single (−m) 1 * ↑(expand m (mk (jIntCoeff ∘ (·−1))))` is stated at Kronecker level; also :577-600 ≡ :609-636 and :227-236 ≡ :238-247 duplicates | — |
| `ScratchGS.lean` | 11 | — | REMOVE-FILE | root-level scratch (9 `#check` + `import`), not in the `XYin` lean_lib, not imported | — |
| `XYin/Basic.lean` | 1 | 0/1 | REMOVE-FILE | Lake template `def hello := "world"`; drop `XYin.lean:1` | — |
| `ModularFunctions/CuspPeriod.lean` | 62 | 0/3 (cascade) | REMOVE-FILE | `exists_pos_period_at_cusp` :48-60 → only consumer `Cusps.isOfExponentialGrowthAt_iff_isMeromorphicAt` :57-72 → only consumers `Basic.meromorphic_at_cusps` :83-87 and `Cusps.exponential_growth_at_cusps_iff` :78-86, both unused; `discreteTopology_conj` :29-42 and instance `hasDetPlusMinusOne_conj` :22-28 feed only that. Drop `Cusps.lean:9`. **Confirm with author**: `ModularFunctions/` is an untracked in-progress development and this may be intended API (mathlib lacks `Subgroup.hasDetPlusMinusOne_conj`/`discreteTopology_conj`) | Cusps:9 |

† `DiscriminantProductFormula` :29-34 has 0 uses (dead even in the interim core).

Umbrella/facade files that are fine: `Cox/Section11BC.lean`, `Cox/CoxMatrices.lean`, `Cox/ModularPolynomial.lean` (no declarations, correct imports; docstring issues in §4).

## 3. Full classified list, grouped by file

Format: `name (file:start-end, N lines) — VERDICT — reason — action`. Line ranges include docstring/attributes.
Files entirely covered by §2 are not repeated here except for declarations that must survive the file.

### XYin.lean / root
- `hello` (XYin/Basic.lean:1-1, 1) — REMOVE-DEAD — template stub, 0 uses — delete file + `XYin.lean:1`. (July #1, still open)
- `ScratchGS.lean` (1-11, 11) — REMOVE-FILE — see §2. (July #2, still open)
- `XYin.lean:29,31,39` — REMOVE (root-import hygiene) — imports three declaration-free test files into the library — move `Tactic2/{LaurentQExpSimpTests,QExpSimpConditionTests}.lean`, `qExpansion_tactic/Examples.lean` (+ `qexp_simp`, `QExpSimpAttr`, Qj meta layer) to a second `[[lean_lib]] name = "XYinTest"` (MathlibTest pattern).
- `XYin.lean:26` — REPLACE — `summable_lems` facade — delete line (or replace by `Summability.QExpansion` until that file is removed).

### XYin/uniqueness.lean
- `invariantsDetermineLattice` (:290-293, 4) — REMOVE-DEAD — 0 uses; docstring cites nonexistent `talk4.lean` — delete. (July #4, still open)
- `derivWeierstrassPExcept_zero_eq` (:49-51, 3) — REMOVE-WRAPPER — `simpa` around mathlib `derivWeierstrassPExcept_def`; call sites :73, :115 — retarget.
- `eventually_notMem_lattice` :37-43, `weierstrassP_eq` :44-48, `eventually_derivWeierstrassP_ne_zero` :63-80, `eventually_deriv_derivWeierstrassP` :81-... — KEEP — used via dot-notation `L.…` (:83, :112-127, :235); TSV false positives.
- `lattice_eq_of_g₂_eq_of_g₃_eq` — KEEP-TERMINAL — uniqueness theorem (LatticeJ ×3).
- import `Mathlib.Topology.Algebra.Module.Cardinality` (:21) — REMOVE-IMPORT (probable) — `countable_of_Lindelof_of_discrete` (:240,242) and `isConnected_compl_of_one_lt_rank` (:245) live in Lindelof.lean / Normed/Module/Connected.lean, reachable from the Weierstrass import — needs a build check.

### XYin/PhD/IntegralPowerSeries/IntegralPowerSeries.lean
- `powerSeriesMapAlgHom_apply` (:37-40, 4) — REMOVE-DEAD — 0 uses — delete.
- `powerSeriesMapSubmodule` (:46-48, 3) + `mem_powerSeriesMapSubmodule_iff` (:66-69, 4) — REMOVE-DEAD — 0 uses (successor of July #9) — delete.
- `hasCoeffsIn_one` :75-77, `hasCoeffsIn_neg` :94-96, `hasCoeffsIn_sub` :98-100, `hasCoeffsIn_C_algebraMap` :102-104 (12) — REMOVE-DEAD — 0 uses (July #48 kept them for API symmetry; reversed — if `HasCoeffsIn` becomes a `PowerSeries.lifts` PR they go there) — delete.
- ModularForms section: `modularFormModuleofIsScalarTower` :191-194, `qExpansion_smul_algebra` :196-202, `modularFormQExpansionSubmodule` :204-225 (44 lines incl. header) — REMOVE-DEAD — 0 uses (July #11/#12 successors) — delete; cascade `hasCoeffsIn_zero` :71-73, `hasCoeffsIn_add` :79-82, `hasCoeffsIn_smul` :89-92 (11) become dead — delete. Module docstring :16-22 lists two of these.
- `IsIntegralPowerSeriesmod`, `hasCoeffsIn_mul`, `toIntegralPowerSeries`, `coeTo_of_toIntegralPowerSeries`, … — KEEP (jfunction/link/Deltaqexpansions).

### XYin/PhD/LaurentQExpansion/LaurentQExpansion.lean
- circle-integral subtree (:600-706, 107) — REMOVE-DEAD — see §2 — delete + drop docstring :32-33.
- `to_qExpansion_ne_zero` (:538-543, 6) — REMOVE-DEAD — 0 uses — delete.
- `laurentqExpansion.to_qExpansion_eq_powerSeriesPart` (:571-581, 11) — REMOVE-DEAD — 0 uses (July #49 kept as bridge API; reversed) — delete (mathlib `single_order_mul_powerSeriesPart` gives it in one line if ever needed).
- `laurentqExpansion.coeff_zero` (:490-494, 5) — REMOVE-DEAD — 0 qualified uses (`coeff_zero` hit at LPE:149 is `HahnSeries.coeff_zero`) — delete.
- `variable {h : ℝ}` (:44) — REMOVE — used by exactly one declaration (:600, itself dead).
- `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` — KEEP — now 5 call sites (July #26 INLINE: done/obsolete).

### XYin/PhD/LaurentQExpansion/Algebra.lean
- `laurentqExpansion_one` (:231-234, 4) — REMOVE-DEAD — 0 uses — delete.
- `to_qExpansion_nat_mul` (:365-381) — KEEP — feeds `laurentqExpansion_nat_mul_coeff*` (used by IntegralDescent/DiagonalLaurent/Kronecker).

### XYin/PhD/ModularFunctions/MeromorphicField.lean (20 dead decls, 113 lines — ProjectVD port residue)
- `Filter.codiscreteWithin_neBot_iff` (:96-98, 3), `mem_subring_iff` (:219-220, 2), `toGermRingHom_surjective` (:250-254, 5), `coe_div` (:281-287, 7), `isField` (:343-347, 5), `isDomain` (:365-369, 5), `coe_constRingHom` (:431-435, 5), `constRingHom_injective` (:437-442, 6), `algebraMap_eq_constRingHom` (:447-448, 2), `toGermRingHom_toNF` (:552-555, 4) — REMOVE-DEAD — 0 uses each — delete (44 lines).
- valuation block: `orderAt` :454-458, `orderAt_coe` :460-467, `orderAt_mul` :469-474, `eq_zero_iff_forall_orderAt_eq_top` :476-480, `orderAt_ne_top` :482-492, `coe_eq_zero_iff` :313-320 (only feeds it), `out_eventuallyEq` :417-420, `divisor_coe` :504-510, `divisor_mul` :512-522, `divisor_inv` :524-527 (69 lines) — REMOVE-DEAD — closed subgraph with no external user; the `AddValuation` promised at :483 was never built — delete now, re-add with the valuation when needed.
- `Filter.eventuallyEq_codiscreteWithin_of_forall_eventuallyEq_nhdsNE` (:51-57) — KEEP — used at :151 via `open Filter`.
- `instField` (:353), `toFun_injective` (:626), `meromorphicNFOn_iff_exists` (:635), `toFun_ofHolomorphic` (:651), `instFact*` (:581-588) — KEEP — used (UHPFF:51, ModularFunctionField:67,164, LevelJ:316-318, Construction:268, FieldAction:57, JInvariant:47); the two `Fact` instances are load-bearing for `instField` on `MeromorphicField` (standard mathlib pattern for concrete sets) — do NOT scope.

### XYin/PhD/ModularFunctions/Basic.lean
- `toMeromorphicField_injective` (:72-77, 6), `meromorphic_at_cusps` (:83-87, 5) — REMOVE-DEAD — 0 uses — delete.
- `toSlashInvariantForm_coe` (:48-50, 3) — REMOVE-DEAD — only user Delta:225,227 (`CuspForm_div_Discriminant`, dead) — delete with it.
- `meromorphicNFOn` :64, `meromorphicOn` :69, `meromorphicAt_cuspFunction` :90 — KEEP (dot-notation uses; TSV false positives).

### XYin/PhD/ModularFunctions/Congruence.lean
- `coe_restrict` (:32-34, 3), `coe_ofGamma0CuspData` (:142-148, 7) — REMOVE-DEAD — `@[simp]` rfl lemmas, 0 uses — delete (rebuild check).
- `restrict` :25, `cuspFunction_gamma0` :95 — KEEP (CuspData:70,75,79).

### XYin/PhD/ModularFunctions/Cusps.lean, CuspPeriod.lean
- `IsMeromorphicAt` (Cusps:39-44, 6), `isOfExponentialGrowthAt_iff_isMeromorphicAt` (:57-72, 16), `exponential_growth_at_cusps_iff` (:78-86, 9) — REMOVE-DEAD (cascade from `Basic.meromorphic_at_cusps`) — delete; then `CuspPeriod.lean` REMOVE-FILE (§2). Author confirmation advised.
- `isOfExponentialGrowthAt_iff_meromorphicAt_cuspFunction` (:47), `…_of_meromorphicNFOn` (:27) — KEEP (Basic:90 → Congruence:108).

### XYin/PhD/ModularFunctions/FieldAction.lean, JInvariant.lean
- `toFun_algebraMap` (FieldAction:66-70, 5) — REMOVE-DEAD — duplicate of `toFun_holomorphicToMeromorphic`, 0 uses — delete.
- `coe_jModularFunction` (JInvariant:56-57, 2) — REMOVE-DEAD — 0 uses — delete.
- `ModularFunction.j_mdifferentiable` (JInvariant:23-25, 3) — REMOVE-WRAPPER — re-export of `_root_.j_mdifferentiable`; call sites JInvariant:46-47 — retarget, delete.
- `j_isOfExponentialGrowth` :34 — KEEP (:54).

### XYin/PhD/Cox/CoxMatrices/Basic.lean
- `rightCosetMul_mk` (:664-668, 5) — REMOVE-DEAD — 0 uses — delete.
- `a_le`, `d_le`, `mobiusMatrix`, `inclusionMatrix_isColumnHermiteNormalForm`, `inclusionMatrix_det`, `inclusionMatrix_content_eq_one`, `coe_act`, `gamma0RightCosetsFintype` — KEEP (dot-notation / instance; :92-94, :176-818, Classification:108-144, SingularModuli:156-164, LaurentExpansion:80).
- `coe_slStar` (:236) / `coxMatrixEquivRightCosets_coxRepresentative` (:605) — KEEP; drop `@[simp]` on private lemmas (style).

### XYin/PhD/Cox/CoxMatrices/Cardinality.lean, LaurentExpansion.lean
- `card_coxMatrix` (Cardinality:268-278) — KEEP-TERMINAL — headline count (Dedekind ψ).
- `cuspFunction_coxAction_aux` (LaurentExpansion:115-119, 5) — INLINE — one-line specialisation used once (:132).
- `laurentqExpansion_coxAction` — KEEP-TERMINAL (Cox 11.13) and used.
- import `Mathlib.NumberTheory.Cyclotomic.Basic` (LaurentExpansion:6) — REMOVE-IMPORT (probable; only `Complex.isPrimitiveRoot_exp` used) — build check.

### XYin/PhD/Cox/CyclicSublattice.lean
- `map_carrier` (:149-153, 5) — REMOVE-DEAD — 0 uses (July #78 kept as simp API; reversed) — delete.
- private `carrierEquiv_apply_coe` (:251-255, 5), private `transportedBasis_apply_coe` (:268-272, 5) — REMOVE-DEAD — private `@[simp]`, never fired by name — delete (rebuild check). (July #23 still open)
- private `hermite_repr_apply` (:293-298, 6) — REMOVE-DEAD — verbatim duplicate of `HermiteNormalForm.repr_apply` (HNF:206), used at :298 only by itself — delete, use `S.hermiteNormalForm.repr_apply`.
- `carrier_finrank`, `toPeriodPair_lattice`, `ofLatticeEq*`, `j_ofLatticeEq`, `scale`, `j_scale`, `dual_*`, `dual_sub_j`, `dual_base_j` — KEEP (dot-notation uses :57-533, Classification:303,361-363, Arithmetic:44).

### XYin/PhD/Cox/CyclicSublattice/Classification.lean
- `cyclicSublattice_hnf_matrix` (:286-292, 7) — REMOVE-DEAD — 0 uses; restates `hermiteNormalForm_matrix_eq_inclusionMatrix` — delete. (July #20 still open)
- `CoxMatrix.toCyclicSublattice_carrier` (:188-192, 5) — REMOVE-DEAD — rfl, 0 uses — delete.
- `cyclicSublatticeEquivCoxMatrixOfPeriodPair` (:168-175), `cyclicSublatticeEquivCoxMatrix` (:280-284), `toCyclicSublatticeOfPeriodPair_toCoxMatrix` (:146-153), `toCoxMatrix_inclusionMatrix` (:77-80) — KEEP-TERMINAL — the bijection `CyclicSublattice L m ≃ CoxMatrix m` is Cox 11.23's classification content (zero external users but headline).
- `range_complexSublatticeGenerators` (:255) — INLINE — one-line wrapper of `Matrix.range_cons_cons_empty`, used once (:278).
- `theorem_11_23` (:345) — KEEP-TERMINAL, used (Arithmetic ×4).
- `hermiteNormalForm_matrix_eq_inclusionMatrix`, `sublatticeOfPeriodPair`, `toCyclicSublatticeOfPeriodPair`, `toCoxMatrix_toCyclicSublatticeOfPeriodPair` — KEEP (used :80-342).

### XYin/PhD/Cox/HermiteNormalForm.lean
- `bN_eq` (:280-288, 9) — REMOVE-DEAD — 0 uses (July #46 KEEP for "API completeness"; reversed) — delete. `matrix_eq` :239-278 stays (Classification:152).
- `rankTwoContent`, `rankTwoContent_dvd_mul_right`, `exists_right_mul_isColumnHermiteNormalForm`, `repr_apply`, `range_toLin_matrix_eq`, `index_eq_natAbs_det`, `quotient_isAddCyclic_iff_rankTwoContent_eq_one` — KEEP (36/4/2/4/1/5/3 uses).
- `reduced_eq_of_eq_add_mul` (:232-237) — KEEP but misplaced pure-`Int` lemma.

### XYin/PhD/Cox/Kronecker.lean, KroneckerFrobenius.lean
- `jIntegralLaurentSeries_coeff` (Kronecker:171-174, 4, `@[simp]`), `jIntegralLaurentSeries_map_complex` (:176-181, 6), `specializeJMod_varX` (:476-481, 6), `specializeJMod_varY` (:483-488, 6, `@[simp]`) — REMOVE-DEAD — 0 uses each (July #17/#18 still open; #68 simp-keep reversed) — delete (rebuild check for the two simp lemmas).
- `transformedJSeries_one_sigmaZero_eq_primeLower_pow` (KF:167-174, 8) — REMOVE-DEAD — 0 uses — delete. (July #19 still open)
- `theorem_11_18_v` (KF:221) — KEEP-TERMINAL.
- import `XYin.PhD.Cox.LaurentPolynomialEvaluation` (Kronecker:9) — REMOVE-IMPORT — already transitive via DiagonalLaurent:11 (harmless).
- `[Fact (Nat.Prime p)]` unused in KF:26-37, :77-96, :104-139 and Kronecker:444-458 — REMOVE-HYPOTHESIS.

### XYin/PhD/Cox/LatticeJ.lean
- `coe_smulLatticeEquiv_apply` (:86-89, 4), `coe_smulLatticeEquiv_symm_apply` (:91-97, 7) — REMOVE-DEAD — `@[simp]`, 0 uses (July #55 reversed) — delete (rebuild check).
- `j_eq_iff_exists_sl2_smul_eq` (:551) — KEEP-TERMINAL — Cox 11.2(ii) headline.
- `Homothetic`, `mem_smul_lattice`, `j_smul`, `discriminant_ne_zero`, `j_eq_iff_homothetic` — KEEP (dot-notation uses).
- import `Mathlib.NumberTheory.ModularForms.NormTrace` (:7) — KEEP (used at :574 `ModularForm.eq_const_of_weight_zero`); optional REPLACE by `levelOne_weight_zero_const` to drop the import.

### XYin/PhD/Cox/ModularFunction/*.lean, ModularFunction.lean, ModularFunctionField.lean
- `coe_levelJModularFunction` (LevelJ:321-323, 3) — REMOVE-DEAD — 0 uses — delete.
- `matrix_eq_upper_triangular_aux` (LevelJ:203-210, 8) — REMOVE-WRAPPER — `Matrix.eta_fin_two`; call site :241 — retarget.
- `periodic_comp_sl2` (CuspData:62-64, 3) — REMOVE-WRAPPER — wraps `periodic_comp_sl2_of_gamma0_invariant`; call sites ModularFunction:35, :247 — retarget with `hf.2.1`.
- `j_levelOneCuspData` (CuspData:82-83, 2) — REPLACE — definitionally `j_cuspData 1`; call sites ModularFunction:226,423, IntegralDescent:33,47 — make it an `abbrev`/`alias` or retarget.
- `cuspFunction_mul_eventuallyEq` (CuspData:86-95, 10) — REPLACE (project-internal duplicate) — verbatim copy of private LaurentQExpansion.lean:79; call site CuspData:112 — publicize the LQE one, delete this.
- `toMeromorphicField_eq_ratFunc` (ModularFunctionField:104), `theorem_11_9_ii` (:176), `theorem_11_9_i` (ModularFunction:431) — KEEP-TERMINAL.

### XYin/PhD/Cox/ModularPolynomial/*.lean
- `coe_coxPhiFunction_coeff_modularFunction` (Construction:279-281, 3) — REMOVE-DEAD — 0 uses — delete.
- `specializeY_eval` (Construction:70-72) — REPLACE — = `Polynomial.map_evalRingHom_eval` (Bivariate.lean:162); call sites SingularModuli:213, Classification:330, Construction:364.
- `diagonal_map` (Construction:126-131) — REPLACE — = `map_mapRingHom_eval_map` (Bivariate.lean:172); call sites Arithmetic:213,291.
- `eval_swap` (Construction:88-93) — REPLACE — = `aevalAeval_swap` + `coe_aevalAeval_eq_evalEval` (Bivariate.lean:286,237); call site Arithmetic:109.
- `diagonal_eval₂` (Construction:135-…) — REPLACE — ≈ `eval₂_eval₂RingHom_apply` (Bivariate.lean:194); call sites SingularModuli:209, DiagonalLaurent:210.
- `varX`/`varY` (Construction:33-36) — KEEP (13 uses each in LevelThree/Kronecker/KF; mathlib's `Y`/`C X` would serve — Step 5).
- `specializeY_ext` :75 — KEEP (:337).
- `eval_derivative_prod_X_sub_C_at` (Interpolation:291-299, 9) — REPLACE — = `Lagrange.eval_nodal_derivative_eval_node_eq` (Lagrange.lean:605) + `eval_nodal` (:571); call sites :328, :417.
- `modularPolynomialC_irreducibleInX` (Irreducibility:134-137) — KEEP; merge the private `modularPolynomialRatFunc_irreducible` into it (one-line re-export, style).
- import `XYin.PhD.Cox.FormalCoxProduct` (Construction:6) — REPLACE-IMPORT — nothing from FormalCoxProduct is used in Construction (grep `formalCox|reindex_bijective|integralLaurentSeries`: 0 hits); IntegralDescent consumes `formalCoxPolynomial_coeff_isInteger` transitively — move the import to IntegralDescent. (July #27 still open)
- tactic-mode `def`s: Interpolation:32-33 (`interpolationAt … := by`), :404 (`modularDerivativeHolomorphic`), Classification:28 (`toCoxMatrix`), Eisensteinqexpansions:30 (dead file) — REPLACE by term-mode definitions (they are opaque to `rfl`/`simp`).

### XYin/PhD/Cox/{Arithmetic, SingularModuli, DiagonalLaurent, SymmetricCubicLaurent, FormalCoxProduct, LaurentPolynomialEvaluation, LevelThree}.lean
- `theorem_11_18_i` (Arithmetic:22-27), `theorem_11_18_ii` (:28-33), `theorem_11_18_iv_degree` (:297-…), `modularPolynomial_three` (:338-346) — KEEP-TERMINAL — numbered Cox results.
- `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity` (Arithmetic:223-229, 7) — INLINE — single consumer :234.
- `singularModulus_isIntegral` (SingularModuli:233), `exists_nonsquare_coxMatrix_j_eq` (:189, used :207) — KEEP-TERMINAL / KEEP.
- `not_isSquare_of_between_sq_aux` (SingularModuli:59-72, 14) — REPLACE — 3-line corollary of `Nat.not_exists_sq` after `lift`; call sites :91, :120.
- `laurentqExpansion_j_pow_order_widthM` (DiagonalLaurent:214-217, 4) — INLINE — used once (:239).
- duplicated copyright header (DiagonalLaurent:1-10) — REMOVE lines 6-10. (July #24 still open)
- `symmetricCubicExpansion_coeff_zero/_one/_two/_three` (SymmetricCubicLaurent:64-86, 4 × ≈ 5) — INLINE — each used once at :97-100; `interval_cases` on `_coeff_aux` removes all four.
- `bivariateLaurentEval` (SCL:116-118) — KEEP (9 uses).
- `[CharZero K]` unused on FormalCoxProduct:51, :75, :92 — REMOVE-HYPOTHESIS.
- `three_dvd_iff_dvd_shift_natAbs` (LevelThree:569-571), `nine_dvd_iff_dvd_shift_natAbs` (:573-575) (7) — REMOVE-WRAPPER — one-line `simpa` instances of `int_dvd_iff_dvd_add_natAbs` :559; call sites :589,596,623,630 — retarget.
- LevelThree jet split :349-557 — REPLACE (§2).
- dead `@[simp]` on private `bivariateLaurentEval_intCastThree` (LevelThree:311) — REMOVE-ATTRIBUTE.
- import `Mathlib.RingTheory.PowerSeries.Trunc` (LevelThree:7) — REMOVE-IMPORT — `trunc` appears nowhere else in the file. (verified)

### XYin/PhD/Cox/UpperHalfPlaneFunctionField.lean
- `algebraMap_jElement` (:46-52, 7), `ratFuncEvalJ_injective` (:99-102, 4) — REMOVE-DEAD — 0 uses (`RingHom.injective` recovers the latter) — delete. (July #21 still open)

### XYin/PhD/jFunction/*.lean
- jLevelN: `jN_cuspFunction_meromorphicAt` (:171-181, 11) + private chain `qjN` :92-93, `qjN_periodic_aux` :103-114, `qjN_differentiableAt_aux` :116-125, `qjN_mdifferentiable_aux` :127-129, `qjN_isBoundedAtImInfty_aux` :131-138, `qjN_cuspFunction_analyticAt_aux` :140-144, `jN_cuspFunction_eq_aux` :146-169 (75 lines total) — REMOVE-DEAD — 0 uses; the cusp analysis of `jN` is carried by `Cox.j_cuspData m` / `levelJ_cuspData` (CuspData/LevelJ). July #42 kept it as a docstring-named headline — reversed; also delete docstring bullet :20. `natCast_mul_ofComplex_coe_aux` :95-101 stays (used by `jN_differentiableAt` :192).
- jfunction: `j_cuspFunction_not_analyticAt` (:472-475, 4) — KEEP-TERMINAL — documents genuine pole. `Delta_qExpansion_coeff_zero_aux` (:108, private) — KEEP (used :126; July #22 now done).
- jInvariantLink: `ellipticCurve_j` (:78-81), `weierstrassCurve_j` (:61-…, used :79), `weierstrassCurve_c₆` (:45-48) — KEEP-TERMINAL (file's terminal theorem; API symmetry with used `_c₄`).
- qexp_coeffs: `Delta_qExpansion_coeff_three/four/five` (:65-79), `j_laurentQExpansion_coeff_zero/one/two/three` (:148-163), `ramanujanTau_*`, `exists_int_coeff_…` — KEEP-TERMINAL (documentation-grade explicit values).
- Deltaqexpansions: `integralE4/E6_constantCoeff_aux` (:121-125) — INLINE (one-line restatements, in-file only). Otherwise KEEP.

### XYin/PhD/qExpansion_tactic/*.lean
- `E6_int_link` (link:162-166, 5) — REMOVE-DEAD — 0 uses (July #45 symmetry argument dropped: the E6 route has no consumer) — delete.
- `qoverDeltaCoeffInt_zero` (link:347-349, 3) — REMOVE-DEAD — 0 uses (`deltaOverQCoeffInt_zero` is the one used) — delete.
- `set_option linter.style.header false` (link:4) — REPLACE with the standard copyright header (Examples/LaurentQExpansion/IntegralPowerSeries already fixed; July #29 ¾ done).
- Qj meta layer :166-304 — see §2; `reportTiming := true` (:44) → `register_option`; unreachable branches :248-249, :260-261 (`toString` of `Int`/`List Int` is never empty) — REMOVE.
- 7 generic root-namespace lemmas in link.lean (`foldl_range_add_eq_sum`, `foldl_push_toList`, `foldl_push_getD`, `mk_coeff_self`, `array_getD_eq_toList_getD`, `getD_map_range`, `coeff_invOfUnit_one_succ`) — KEEP (used) but namespace them; `foldl_push_toList` :39 = `Array.foldl_toList_eq_map`, `mk_coeff_self` :82 = `PowerSeries.ext fun _ => coeff_mk` → REMOVE-WRAPPER candidates (Step 5 scope).

### XYin/PhD/Modularforms/*.lean — declarations that survive the §2 file verdicts
- `E₄` (Eisenstein:55-57), `E₆` (:59-60) — REPLACE — `ModularForm.E₄`/`E₆` (EisensteinSeries/Basic.lean:51,54) modulo `Γ(1)`↔`𝒮ℒ` (`Gamma_one_coe_eq_SL`); call sites Deltaqexpansions `E4`/`E6` defs and `_qExpansion_coeff_aux` — until then KEEP (with `standardcongruencecondition` inlined).
- `bernoulli'_six` (Eisenstein:287-292) — KEEP — no mathlib analogue (Deltaqexpansions, LatticeJ:186); relocate to Deltaqexpansions.
- `Delta_q_one_term` (Eisenstein:374-377) — REPLACE — `ModularForm.discriminant_qExpansion_coeff_one` (Discriminant.lean:210) after `Delta = CuspForm.discriminant`; call sites jfunction (`deltaShiftedQSeries_analyticAt_aux`), link (`deltaOverQCoeffInt_zero`).
- `Δ`, `Delta`, `Delta_apply`, `Delta_eq_eta_pow`, `Δ_ne_zero`, `Delta_boundedfactor`, `Discriminant_SIF`, `Discriminant_zeroAtImInfty`, `Discriminant_T/S_invariant`, `delta_eq_discriminant` (Delta.lean) — REPLACE — see §2 mathlib names; `delta_eq_discriminant` is private and re-proved at Eisenstein:333,375 and DimensionFormulas:122 → publicize until the REPLACE lands.
- `zero_at_cusps_of_zero_at_infty` (ForMathlib_Cusps:9-14) — KEEP (true ForMathlib).
- `SL2Z_generate`, `slashaction_generators`, `slashaction_generators_SL2Z`, `slashaction_generators_GL2R` (SlashActionAuxil) — REPLACE — mathlib `SL2Z_generators.symm`, `slash_action_generators`, `slash_action_generators_SL2Z`; single call site Delta:62.
- `standardcongruencecondition` (Eisensteinqexpansions:20) — INLINE into `E₄`/`E₆`.
- `qExpansion_ext` (qExpansion_lems:75-77) — INLINE at link:250 (`congrArg (qExpansion 1) h`).
- Everything else in `Modularforms/` (373 of 391 declarations) — REMOVE-DEAD via the file verdicts; the per-declaration evidence (name, range, dead users) is in the closure listing summarised in §2. Notable named items the task asked about: `natPosSMul : SMul ℕ+ ℍ` (Delta:81-82, diamond hazard, 0 uses), `instance : FunLike (ℍ → ℂ) ℍ ℂ` (qExpansion_lems:73, mathlib deliberately has none, 0 named uses — rebuild check for silent elaboration through it), `asdf` (Eisenstein:342-366, 25 lines = `multipliableLocallyUniformlyOn_one_sub_pow` + `HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange`), `auxasdf` (:198-201), `a1`/`a4`/`a33`/`aux33` (Summability/Basic), `t9`/`q_exp_iden''` (QExpansion), `aus`/`upbnd`/`summable_hammerTime_nat`/`summable_pain`/`extracted_abs_norm_summable` (Reciprocal), `EQ0`/`EQ1`/`EQ2` (Eisensteinqexpansions), `cuspFormOfSIFTendstoZero` (IsCuspForm:100-111; ≡ LatticeJ:556 `levelOneWeightZeroCuspForm_aux`), `IsCuspForm_to_CuspForm` (IsCuspForm:84-87, `hf.choose` where `(equivCuspFormSubmodule).symm ⟨f,hf⟩` is explicit), `Modform_mul_Delta'` (DimensionFormulas:84-86, `Classical.choose` although the witness `CuspForm.mcast (by ring) (Delta.mulModularForm f)` is written at :80).

## 4. Non-declaration junk (exact lines)

Dead commands / examples / tests
1. `ScratchGS.lean:3-11` — 9 `#check`s (whole file, §2).
2. `qExpansion_tactic/Examples.lean:24-29,39-43,52-53` — `#qexp`/`#check` demos; `:55-65` commented-out stress test; `:21` redundant `open scoped XYin.PhD.qExpansion_tactic` (namespace declares nothing scoped).
3. `Tactic2/QExpSimpConditionTests.lean:40,43,46,49,52` — five no-op `noncomputable example`.
4. `Tactic2/LaurentQExpSimpTests.lean:35-40` — byte-identical duplicate of `:28-33`. (July #16 still open)
5. `Modularforms/NormNumI.lean:147-153` — `norm_numI_parse` "Testing the `parse` function" elab; `:127-129` commented-out code; `:140-145` `norm_numI` conv never invoked.

Stale / noise comments
6. `uniqueness.lean:290` — "from `talk4.lean`" (nonexistent file).
7. `Modularforms/Eisensteinqexpansions.lean:147-148` — "being PRed (slowly) into mathlib"; `:23-24` duplicates `Eisenstein.lean:56-57`.
8. `Modularforms/Eisenstein.lean:53` (`/- The Eisenstein Series E₄ and E₆ -/` non-doc), `:110`, `:114` (φ block), `:289-290` (`-- shrug`), `:415` ("This is in the mod forms repo" — it is mathlib `E_ne_zero`), `:455`, `:488`, `:520`, `:556`.
9. `Modularforms/Delta.lean:25` (non-doc header), `:43` ("should be easy … Mulitpliable bit"), `:48` ("This one is easy."), `:53` ("This is the hard one."), `:303`, `:328`, `:397` (non-doc `/- -/` that should be docstrings).
10. `Modularforms/Summability/Basic.lean:38` ("this is being Pr'd"), `:162`, `:184` ("mod forms repo"); `Reciprocal.lean:61`, `:248`; `multipliable_lems.lean:15` ("this is being PRd"); `eta.lean:19-21` (Lean 4.29 identifier note).
11. `Modularforms/SlashActionAuxil.lean:18-19` — promises Jacobi-theta applications that do not exist in the project.
12. `Cox/Section11BC.lean:13-19` — docstring cites "Lemma 11.10", "Lemma 11.11", "Lemma 11.24" (no `lemma_11_*` declarations exist) and omits `SingularModuli` (`singularModulus_isIntegral`) and Kronecker/Frobenius (`theorem_11_18_v` lives in KroneckerFrobenius.lean:221).
13. `ModularFunctions/MeromorphicField.lean:73` — docstring references nonexistent `eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE`; `:1-5` header attributes the whole file to Kebekus although `:573-658` is project code.
14. `Cox/ModularPolynomial.lean:11-16` — umbrella docstring omits AnalyticSupport; `jFunction/jLevelN.lean:20` — names `jN_cuspFunction_meromorphicAt` (to be deleted); `LaurentQExpansion.lean:32-33` — names the dead circle-integral result.
15. `IntegralPowerSeries.lean:16-22` — module docstring lists dead `powerSeriesMapAlgHom`/`modularFormQExpansionSubmodule`.

Duplicated headers / docstrings / `open` / `variable`
16. `Cox/DiagonalLaurent.lean:1-10` — copyright block twice; delete `:6-10`. (July #24 still open)
17. `ModularFunctions/MeromorphicField.lean` — five merged "This file …" module docstrings `:13-26, :29-36, :80-90, :120-131, :183-198, :376-393`; `open Filter Set Topology` ×5 at `:38, :92, :133, :200, :395`; `variable` re-declared at `:40, :94, :135-137, :202, :397`; keep one header + one `open`, section-local `variable`s.
18. `ModularFunctions/CuspPeriod.lean:16-17` — `MatrixGroups` opened twice.
19. `ModularFunctions/JInvariant.lean:16` — `open Complex … Matrix.SpecialLinearGroup` unused.
20. `Modularforms/Delta.lean:16-19` — `open MeasureTheory intervalIntegral Metric`, `open scoped Interval NNReal ENNReal` unused; `:157` mid-file `open Real`; `:143` `variable {α ι : Type*}` serves one dead lemma.
21. `Modularforms/Eisenstein.lean:102` `variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)` (dead), `:128` `variable … (n : ℕ) (f : F)` leaks `n f` into unrelated signatures, `:379-381` `variable {α β γ} [CommMonoid α] [TopologicalSpace α] [UniformSpace α]` (dead); `:29`/`:108` nested `noncomputable section`s; `:106` `open Complex Real` then `:444` `open _root_.Complex hiding I`.
22. `Modularforms/iteratedderivs.lean:59-60` — dead `variable {𝕜 …} (n : ℕ) (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜)`.
23. `Modularforms/IsCuspForm.lean:20` `variable {α ι : Type*}`, `:23` `(n : ℕ) (f : F)` — dead binders.
24. `LaurentQExpansion.lean:44` `variable {h : ℝ}` — one (dead) user; `:582-583`, `:598-599` double blank lines.
25. `Modularforms/SlashActionAuxil.lean:25` — `local notation "GL(" n ", " R ")" "⁺"` never used.

Unused / boilerplate imports (all need a build check; ordered by confidence)
26. `Cox/LevelThree.lean:7` `Mathlib.RingTheory.PowerSeries.Trunc` — `trunc` unused (verified by grep).
27. `Modularforms/Delta.lean:4-5,10` `clog_arg_lems`, `eta`, `NormNumI` — nothing referenced.
28. `Modularforms/{BigO:3-5, clog_arg_lems:3-4,7-8, csqrt:3-4,7-10, equivs:3-7 (incl. `Mathlib.Tactic`), iteratedderivs:3,9-10, qExpansion_lems:3-4,6-7, upperhalfplane:4, AtImInfty:3 (`Tannery`), tsumderivWithin:10, DimensionFormulas:9-10, IsCuspForm:3 (`CStarAlgebra.Module.Defs`), IsCuspForm:6 (`qExpansion_lems`, no named use), Summability/Basic:8-9}` — `CStarAlgebra.Classes`, `Algebra.Order.Ring.Star`, `Data.Int.Star`, `Data.Real.StarOrdered`, `Order.CompletePartialOrder`, `Tactic.Cases` boilerplate — all moot once the files go.
29. `Cox/Kronecker.lean:9` — redundant (transitive via DiagonalLaurent).
30. `Cox/CoxMatrices/Cardinality.lean:6-7` — `Data.Finset.NatDivisors`, `Data.Nat.Totient` transitive via `ArithmeticFunction.Misc` (harmless).
31. `Cox/CoxMatrices/LaurentExpansion.lean:6` — `Cyclotomic.Basic` (only `Complex.isPrimitiveRoot_exp` used).
32. `uniqueness.lean:21` — `Topology.Algebra.Module.Cardinality` (see file entry).
33. `Cox/LatticeJ.lean:7` — `NormTrace` (used; replaceable), `:9` `ForMathlib_Cusps` (used at :565 — keep).
34. `Cox/ModularPolynomial/Construction.lean:6` — `FormalCoxProduct` (move to IntegralDescent). (July #27 still open)
35. `XYin.lean:1,26,29,31,39` — root-import hygiene (§3 first block).

Placeholder / non-mathlib names (all in dead files unless noted): `auxasdf`, `asdf` (Eisenstein:198,342), `a1`, `a4`, `a33`, `aux33`, `hsum`, `tsum_pNat`, `nat_pos_tsum2'` (Summability/Basic), `aus`, `upbnd`, `summable_hammerTime_nat`, `summable_pain`, `extracted_abs_norm_summable`, `summable_1/2/3` (Reciprocal), `t9`, `q_exp_iden''`, `exp_series_ite_deriv_uexp'''`, `auxp_…` (QExpansion), `EQ0/EQ1/EQ2/EQ22` (Eisensteinqexpansions), `atImInfy_pnat_mono`, `log_one_neg_cexp_tendto_zero` (Delta typos), `cuspFuntion`, `modfom`, `diffwithinat` (Eisenstein typos). No `foo`/`bar` occurrences exist in the project (grep-verified).

Linter escapes / deprecated syntax
36. `qExpansion_tactic/link.lean:4` `set_option linter.style.header false` — the only remaining escape (Examples, LaurentQExpansion, IntegralPowerSeries now carry headers).
37. `Tactic2/qexp_simp.lean:168,170,175,177,179,181,183,185,190,192,197,199,201,203,205,207` — 16 deprecated `simp (config := { maxDischargeDepth := 20 })` (`simp +maxDischargeDepth` spelling); `:165-185` ≡ `:187-207` duplicate macro bodies; `:158` `sub_eq_add_neg` in the set makes every `_sub` lemma dead; `:20-22` `one_mem_strictPeriods_gamma1` duplicates the tagged `one_mem_strictPeriods_SL` `:159`.

`Classical.choose` where an explicit witness exists
38. `Modularforms/DimensionFormulas.lean:80-86` — `Modform_mul_Delta'` chooses although `CuspForm.mcast (by ring) (Delta.mulModularForm f)` is the witness at :80 (dead file).
39. `Modularforms/IsCuspForm.lean:84-87` — `IsCuspForm_to_CuspForm := hf.choose`; explicit `(equivCuspFormSubmodule).symm ⟨f, hf⟩` (dead file).
40. `jFunction/jfunction.lean:319` — `qjCoeffs` via `toIntegralPowerSeries` (= `Classical.choose`, IntegralPowerSeries:130) and `:493` `j_laurentQExpansion_isIntegral` is an `∃` whose witness is `.choose`d again at `Cox/CoxMatrices/LaurentExpansion.lean:32` (`jIntCoeff`) although `qjCoeffs (n+1).toNat` is in hand — define `jIntCoeff n := if n < -1 then 0 else qjCoeffs (n+1).toNat` (Step 7 item; here: junk-adjacent opacity).
41. `ModularFunctions/Basic.lean:56` `toMeromorphicField := f.meromorphic'.choose` — `meromorphic'` should be the predicate `MeromorphicNFOn`; `MeromorphicField.lean:406` `out` is a legitimate choice.

Unreachable / no-op code
42. `qExpansion_tactic/Qj.lean:248-249`, `:260-261` — "internal error: empty output" branches unreachable.
43. `qExpansion_tactic/Qj.lean:44` `def reportTiming : Bool := true` — noisy per build; `register_option`.
44. `Cox/LevelThree.lean:311` dead `@[simp]` on a private lemma; `Cox/CoxMatrices/Basic.lean:236,605` `@[simp]` on private lemmas.

Global instances
45. `Modularforms/qExpansion_lems.lean:73` `instance : FunLike (ℍ → ℂ) ℍ ℂ` — REMOVE (with file; rebuild check: IsCuspForm/Eisenstein/jLevelN elaborate FunLike-generic lemmas that may silently use it — jLevelN:188-192 and jfunction:358 must still compile).
46. `Modularforms/Delta.lean:81-82` `instance natPosSMul : SMul ℕ+ ℍ` — REMOVE (dead, diamond hazard with mathlib `posRealAction`).
47. `ModularFunctions/MeromorphicField.lean:581-588` `Fact (IsPreconnected upperHalfPlaneSet)`, `Fact upperHalfPlaneSet.Nontrivial` — KEEP (load-bearing for `instField`); anonymous instances `:266, :276, :309, :445` get unreadable auto-names — name them.
48. `Modularforms/IsCuspForm.lean:70-79` `CuspFormSubmodule.funLike` (priority 100) + `CuspFormClass` instance — REMOVE with file.
49. `Cox/CoxMatrices/Basic.lean:144` `gamma0RightCosetsFintype` — KEEP (used by `∏ c : Gamma0RightCosets m`).

Unused hypotheses
50. `[CharZero K]` FormalCoxProduct:51,75,92; `[Fact (Nat.Prime p)]` KroneckerFrobenius:26-37,77-96,104-139 and Kronecker:444-458; `_hc` ResToImagAxis:277, `_hn₀ _hc` :346 (dead file); `hF` Algebra:331.

## 5. Candidates from `_public-unused-candidates.tsv` that are NOT junk (KEEP / KEEP-TERMINAL)

KEEP-TERMINAL (47): `theorem_11_18_i`, `theorem_11_18_ii`, `theorem_11_18_iv_degree`, `modularPolynomial_three` (Arithmetic); `card_coxMatrix` (Cardinality); `theorem_11_18_v` (KroneckerFrobenius); `j_eq_iff_exists_sl2_smul_eq` (LatticeJ); `toMeromorphicField_eq_ratFunc`, `theorem_11_9_ii` (ModularFunctionField); `singularModulus_isIntegral` (SingularModuli); `weierstrassCurve_c₆`, `weierstrassCurve_j`, `ellipticCurve_j`, `weierstrassCurve` (jInvariantLink); `j_cuspFunction_not_analyticAt` (jfunction); `Delta_qExpansion_coeff_three/_four/_five`, `j_laurentQExpansion_coeff_zero/_one/_two/_three` (qexp_coeffs; with the 9 other explicit-value lemmas not in the TSV); `cyclicSublatticeEquivCoxMatrixOfPeriodPair`, `cyclicSublatticeEquivCoxMatrix`, `toCyclicSublatticeOfPeriodPair_toCoxMatrix`, `toCoxMatrix_toCyclicSublatticeOfPeriodPair`, `toCoxMatrix_inclusionMatrix` (Classification — Cox 11.23 bijection form); `dim_gen_cong_levels` (DimensionFormulas — the only `sorry`; relocate, do not delete); `bernoulli'_six` (Eisenstein, no mathlib analogue); `bernoulli'_five` (Eisenstein:281-285 — REMOVE-DEAD in fact: 0 uses; listed here only because it is the natural companion — verdict REMOVE-DEAD); `lattice_eq_of_g₂_eq_of_g₃_eq` (not in TSV; used).

KEEP — used through dot-notation, `open` namespaces, instances or the `#qexp` elaborator (TSV false positives, 87 rows; grep-verified call sites in parentheses):
Cox/CoxMatrices/Basic: `a_le` (:92), `d_le` (:93-94), `mobiusMatrix` (11 sites), `inclusionMatrix_isColumnHermiteNormalForm` (:409-410, Classification:126), `inclusionMatrix_det` (:546, Classification:108,141), `inclusionMatrix_content_eq_one` (Classification:144), `coe_act` (:759, LaurentExpansion:80, Classification:275, SingularModuli:159), `gamma0RightCosetsFintype` (instance).
Cox/CyclicSublattice: `carrier_finrank` (:57), `toPeriodPair_lattice` (7), `ofLatticeEq` (6), `ofLatticeEq_carrier_map_subtype` (:181), `ofLatticeEq_toPeriodPair_lattice` (:187), `j_ofLatticeEq` (Classification:363), `scale` (9), `j_scale` (Classification:363), `dual_carrier_map_subtype` (:525), `dual_toPeriodPair_lattice` (:533), `dual_sub_j`, `dual_base_j` (Arithmetic:44).
Cox/CyclicSublattice/Classification: `hermiteNormalForm_matrix_eq_inclusionMatrix` (:80,163,292), `sublatticeOfPeriodPair` (4), `toCyclicSublatticeOfPeriodPair` (5).
Cox/HermiteNormalForm: `rankTwoContent` (36), `rankTwoContent_dvd_mul_right` (4), `exists_right_mul_isColumnHermiteNormalForm` (CoxMatrices/Basic:347, HNF:391), `repr_apply` (4), `range_toLin_matrix_eq` (Classification:164), `matrix_eq` (Classification:152, HNF:288), `index_eq_natAbs_det` (5), `quotient_isAddCyclic_iff_rankTwoContent_eq_one` (3).
Cox/LatticeJ: `Homothetic` (10), `mem_smul_lattice` (6), `j_smul` (4), `discriminant_ne_zero` (8), `j_eq_iff_homothetic` (:553).
Cox/ModularPolynomial/Construction: `varX`, `varY` (13 each), `specializeY_eval` (3 — REPLACE), `specializeY_ext` (:337).
Cox/SingularModuli: `exists_nonsquare_coxMatrix_j_eq` (:207).
ModularFunctions/Basic: `toSlashInvariantForm_coe` (Delta:225,227 — dies with Delta block), `meromorphicNFOn` (5), `meromorphicOn` (8), `meromorphicAt_cuspFunction` (Congruence:108).
ModularFunctions/Congruence: `restrict` (CuspData:75,79), `cuspFunction_gamma0` (CuspData:70).
ModularFunctions/CuspPeriod: `discreteTopology_conj` (:55), `exists_pos_period_at_cusp` (Cusps:67) — used, but the whole chain is cascade-dead (§2).
ModularFunctions/Cusps: `IsMeromorphicAt` (3), `isOfExponentialGrowthAt_iff_isMeromorphicAt` (2) — same cascade caveat.
ModularFunctions/JInvariant: `j_isOfExponentialGrowth` (:54).
ModularFunctions/MeromorphicField: `Filter.eventuallyEq_codiscreteWithin_of_forall_eventuallyEq_nhdsNE` (:151), `instField` (instance), `toFun_injective` (3), `meromorphicNFOn_iff_exists` (3), `toFun_ofHolomorphic` (4), `instFactIsPreconnectedUpperHalfPlaneSet`, `instFactNontrivialUpperHalfPlaneSet` (instances, load-bearing), `divisor_mul`/`divisor_inv` (self-recursive only → REMOVE-DEAD, see §3).
Modularforms/E2: `D2_mul`, `D2_inv`, `D2_T`, `D2_S` (in-file only — dead with file).
Modularforms/NormNumI: `eq_of_eq_of_eq_of_eq`, `ne_of_re_ne`, `ne_of_im_ne`, `re_eq_of_eq`, `im_eq_of_eq` (used by the elaborator :175-201 — dead with file).
Modularforms/ResToImagAxis: `resToImagAxis` (29 in-subtree), `resToImagAxis_eq_resToImagAxis` (:74), `resToImagAxis_apply` (:118) — dead with file.
Modularforms/Summability/Basic: `sum_range_zero` — 0 real uses (Eisenstein hits are `Finset.sum_range_zero`) → dead.
Modularforms/multipliable_lems: `tprod_pow` (self-recursive `hf.tprod_pow` → mathlib `Multipliable.tprod_pow`) → dead.
Modularforms/qExpansion_lems: `qExpansion_pow` — 0 real uses (hits are mathlib `ModularForm.qExpansion_pow`) → dead.
Tactic2/qexp_simp: `periodic_comp_ofComplex_of_slashInvariantFormClass`, `mdiff_of_modularFormClass`, `isBoundedAtImInfty_of_modularFormClass`, `isZeroAtImInfty_of_cuspFormClass`, `cuspFunction_apply_zero_of_cuspFormClass` (used by the macros :169-196 — move with the tactic).
jFunction/jInvariantLink: `weierstrassCurve` (8), `weierstrassCurve_j` (:79).
uniqueness: `eventually_notMem_lattice` (:83,112), `weierstrassP_eq` (:127,235), `derivWeierstrassPExcept_zero_eq` (:73,115 — REMOVE-WRAPPER), `eventually_derivWeierstrassP_ne_zero` (:83), `eventually_deriv_derivWeierstrassP` (:113).
IntegralPowerSeries: none of the 8 TSV rows is used (all REMOVE-DEAD, §3).

Everything in the TSV not named in this section or in §3 as KEEP/KEEP-TERMINAL/INLINE/REPLACE/REMOVE-WRAPPER is REMOVE-DEAD (either individually in §3 or through its file in §2). Reconciliation of the 336 rows: 28 KEEP-TERMINAL (26 with zero hits + `weierstrassCurve`, `weierstrassCurve_j`), 56 KEEP with grep-verified real uses (the 87 rows with code hits minus 27 that are dead with their file or self-recursive — `D2_*` ×4, NormNumI ×5, `resToImagAxis*` ×3, `sum_range_zero`, `tprod_pow`, `qExpansion_pow`, `QExpSimp.*` ×5, `divisor_mul/_inv`, `toSlashInvariantForm_coe`, CuspPeriod/Cusps ×4 — minus 2 with call sites but replaced), 2 REPLACE/REMOVE-WRAPPER with call sites (`specializeY_eval`, `derivWeierstrassPExcept_zero_eq`), 250 dead (223 zero-hit rows + the 27 above; every one appears in the §2 file table or the §3 lists by name or block range). 28 + 56 + 2 + 250 = 336.

## 6. Safe deletion order (leaf files first; each step keeps `lake build` green if the listed retargets are done first)

0. Delete `ScratchGS.lean`, `XYin/Basic.lean` (+ `XYin.lean:1`); fix DiagonalLaurent:6-10 header; delete the 83 REMOVE-DEAD declarations of §3 in non-Modularforms files (LaurentQExpansion circle subtree, IntegralPowerSeries dead sections, MeromorphicField 20, Basic/Congruence/FieldAction/JInvariant, Cox 16, jLevelN chain, link 2, uniqueness 1) — 569 lines; these have no importers to adjust.
1. Move `Tactic2/{LaurentQExpSimpTests,QExpSimpConditionTests,qexp_simp,QExpSimpAttr}.lean`, `qExpansion_tactic/Examples.lean` and Qj.lean:166-304 (meta layer) to a second lean_lib `XYinTest`; drop `XYin.lean:29-32,39`. Optional: keep `analyticAt_cuspFunction_{mul,add,sub,neg,smul}` + `isBoundedAtImInfty_sub` in a ForMathlib file. (−328 −65 −139 library lines)
2. `Modularforms/DimensionFormulas.lean` (root-only importer): move `dim_gen_cong_levels` sorry to `ForMathlib`; delete; drop `XYin.lean:9`. (−200)
3. `Modularforms/IsCuspForm.lean`: drop `Eisenstein.lean:9` (nothing live in Eisenstein needs it once `Delta_E4_E6_aux` :304-329 is deleted) and `XYin.lean:14`; delete. Then `qExpansion_lems.lean` (inline `qExpansion_ext` at link:250 first; drop `XYin.lean:25`). (−152 −113)
4. `Modularforms/Eisenstein.lean`: delete everything except `E₄`, `E₆`, `bernoulli'_six`, `Delta_q_one_term` (or move those four to `jFunction/Deltaqexpansions.lean` and delete the file, retargeting `DimensionFormulas`-free consumers); drop imports `IsCuspForm`, `Summability.Basic`. (−672)
5. `Modularforms/Eisensteinqexpansions.lean`: inline `standardcongruencecondition`; delete; Eisenstein/Deltaqexpansions import `Delta` directly. This also frees `Summability/QExpansion.lean` (delete, with `summable_lems.lean` and `XYin.lean:26-27`), then `Summability/Reciprocal.lean`, `tsumderivWithin.lean`, `iteratedderivs.lean`, `BigO.lean`, then `Summability/Basic.lean` (its last importer `multipliable_lems` goes in step 6), `exp_lems.lean`, `equivs.lean`, `upperhalfplane.lean`. (−155 −296 −16 −297 −138 −72 −61 −206 −29 −46 −17)
6. `Modularforms/Delta.lean`: delete `:64-149` and `:193-408`; drop `public import` lines 4-7,10 (`clog_arg_lems`, `eta`, `multipliable_lems`, `ResToImagAxis`, `NormNumI`); then delete `clog_arg_lems.lean`, `eta.lean` (→ `E2.lean`, `csqrt.lean`), `multipliable_lems.lean`, `NormNumI.lean`, `ResToImagAxis.lean` (→ `AtImInfty.lean`), and drop the matching `XYin.lean` lines. (−302 −94 −81 −109 −57 −81 −205 −403 −27)
7. `Modularforms/SlashActionAuxil.lean`: delete `:28-66, :71-215, :237-258, :275-287` (Γ(2) chain and wrappers), keep the 37-line generator chain until step 8. (−250)
8. REPLACE step (Step 5/9 scope, but it finishes the cleanup): retarget `Delta`→`CuspForm.discriminant`, `Δ`→`ModularForm.discriminant`, `E₄/E₆`→`ModularForm.E₄/E₆`, `Delta_q_one_term`→`discriminant_qExpansion_coeff_one`, `Δ_ne_zero`→`discriminant_ne_zero`, `Delta_boundedfactor`→`discriminant_bounded_factor`; then delete `Delta.lean`, `SlashActionAuxil.lean`, the Eisenstein remnant; `Modularforms/` is reduced to `ForMathlib_Cusps.lean` (21 lines, minus `bounded_at_cusps_of_bounded_at_infty` :16-21). (−106 −37 −20 −6)
9. `ModularFunctions/CuspPeriod.lean` + Cusps:39-86 dead chain (after author confirmation); `Cox/LevelThree.lean` jet split collapse (REPLACE, ≈ −210); INLINE/REMOVE-WRAPPER items of §3 (≈ −70).

Estimated total removable: **≈ 5,300 lines now (27 % of the project) + ≈ 300 under REPLACE**, leaving `Modularforms/` at ≤ 150 lines (21 after step 8) and the library free of test/tactic-demo modules.

## 7. July 2026 report (84 entries) — status on 2026-09-25

DONE (18): #3 (`ModularFunctions/Basic.lean` is now a real 97-line module), #5-#8 (`HasIntegralQExpansion.lean` and the four `*_hasIntegralQExpansion` theorems removed), #9, #10, #12 (removed), #13 (`theorem order` gone), #14, #15 (`I∞` gone), #22 (`Delta_qExpansion_coeff_zero_aux` moved to jfunction:108 and used at :126 — now live), #25 (`#min_imports` gone), #26 (`meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` now has 5 call sites — keep), #28 (LaurentQExpansion imports fixed), #29 for Examples/LaurentQExpansion/IntegralPowerSeries (headers added), #30 (`-- double check` gone).
STILL OPEN (14): #1 `hello`, #2 `ScratchGS.lean`, #4 `invariantsDetermineLattice`, #11 (successor `modularFormQExpansionSubmodule` :204-225 + section), #16 test-5 duplicate (LaurentQExpSimpTests:35-40), #17 `jIntegralLaurentSeries_map_complex` (:176-181), #18 `specializeJMod_varX` (:476-481), #19 `transformedJSeries_one_sigmaZero_eq_primeLower_pow` (KF:167-174), #20 `cyclicSublattice_hnf_matrix` (:286-292), #21 `ratFuncEvalJ_injective` (:99-102), #23 `transportedBasis_apply_coe` (:268-272), #24 DiagonalLaurent header (:1-10), #27 Construction:6 import, #29 link.lean:4 escape.
KEEP verdicts re-verified (#31-#84): still correct for #31-#41, #43, #44, #47, #52-#54 (moved to `test/`), #56-#67, #69-#77, #79-#84. Reversed to REMOVE-DEAD on current evidence: #42 `jN_cuspFunction_meromorphicAt` (+ 64 lines of private helpers; superseded by `CuspData.j_cuspData`), #45 `E6_int_link`, #46 `bN_eq`, #48 `hasCoeffsIn_one/neg/sub/C_algebraMap`, #49 `laurentqExpansion.coeff_zero` and `to_qExpansion_eq_powerSeriesPart` (`coeff_of_qExpansion` stays), #50 `laurentqExpansion_coeff_eq_circleIntegral` subtree, #55 `coe_smulLatticeEquiv_apply/_symm_apply`, #68 `jIntegralLaurentSeries_coeff`/`specializeJMod_varY`, #78 `map_carrier`/`toCyclicSublattice_carrier` (`toCoxMatrix_inclusionMatrix` and `ofLatticeEq_carrier` stay). #51 (test files KEEP-INTENTIONAL) → move out of the library.
