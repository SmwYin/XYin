# Step 9 — Mathlibable assessment: pre-filter + triage (2026-09-25)

**Scope statement.** The full per-declaration `/mathlibable` loop (10 phases, nine-channel literature
search) was **not** executed in this session: after pre-filtering there are 1,088 public candidates, the
`chatgpt-math` MCP server failed to connect, and the July 2026 loop stands at 13/595. What follows is
(a) the cheap pre-filter over every declaration, (b) the 13 July verdicts carried forward (all 13
declarations still exist at the current source), and (c) a triage of every candidate that Steps 4/6/7
identified as a mathlib gap or a mathlib duplicate, graded by the evidence those agents produced
(grep-verified mathlib search at pin 2abc242 plus scratch compiles). Triage buckets are LIKELY-YES /
WORTH-FULL-CHECK / BORDERLINE / NO — they are *not* `/mathlibable` verdicts.

## 9a — Pre-filter (all 1,792 lexical declarations; table in `../inventory-2026-09-25/_step9-prefilter.tsv`)

| Status | Count | Rule |
|---|---:|---|
| SKIP private | 600 | `private` modifier |
| SKIP collides-with-mathlib-name | 71 | exact unqualified name exists in mathlib (mostly namespaced short names: `j`, `map`, `ext`, `coe_inv`, …; the Modularforms hits `E₄ E₆ Δ G₂ D₂ D2_* IsCuspForm qExpansion_pow cuspFunction clog_pow succEquiv norm_symm` are real duplicates) |
| SKIP anonymous instance | 18 | — |
| SKIP aux-name | 14 | `_aux` suffix / `aux` prefix |
| SKIP docstring-internal | 1 | — |
| **CANDIDATE** | **1,088** | Modularforms 397 · Cox 319 · ModularFunctions 90 · jFunction 82 · qExpansion_tactic 71 · LaurentQExpansion 53 · IntegralPowerSeries 33 · Tactic2 27 · uniqueness 15 · Basic 1 |
| after Step 8 junk pruning (estimate) | ≈ 560 | Step 8 removes ≈ 33 whole files (≈ 430 public decls, mostly Modularforms/Tactic2) and 83 dead declarations |

## 9b — July 2026 verdicts carried forward (re-verified to exist, 2026-09-25)

| Declaration | File:line (current) | Verdict (July) | Status now |
|---|---|---|---|
| `lattice_eq_of_g₂_eq_of_g₃_eq` | uniqueness.lean:282 | **YES-add-as-is** | unchanged; Step 4A/6 confirm the whole ℘-recursion block :154–282 goes with it into `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` (TODO there at :938) |
| `laurentSeriesMapRingHom` | Cox/LaurentPolynomialEvaluation.lean:22 | YES-but-generalise-first | Step 7B **compiled** `HahnSeries.mapRingHom` at `[PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]` — ready |
| `card_coxMatrix` | Cox/CoxMatrices/Cardinality.lean:270 | YES-but-generalise-first | Step 4B/6/7B: define `dedekindPsi = pmul μ μ * id`; Step 7B **compiled** `(Gamma0 m).index = Fintype.card (CoxMatrix m)` (5 lines) |
| `…HNF.index_eq_natAbs_det` | Cox/HermiteNormalForm.lean:294 | NO-composable | unchanged |
| `Matrix.rankTwoContent` | Cox/HermiteNormalForm.lean:44 | NO-composable (`Finset.gcd`) | Step 4B reduced the identification to a residual `normalize_eq` goal — still composable |
| `Matrix.IsColumnHermiteNormalForm` | HermiteNormalForm.lean:34 | BORDERLINE | Step 6 (G-24) supplies the missing scoping fact: the correct rank-n cyclic criterion is D_{n−1}(A)=1 (gcd of (n−1)-minors); rank-2 `rankTwoContent` = D₁ only at n=2 |
| `Matrix.exists_right_mul_isColumnHermiteNormalForm` | :173 | BORDERLINE | mathlib `FixedDetMatrices.reduce` uses a different normal form — not convertible (re-confirmed) |
| `Matrix.isColumnHermiteNormalForm_fin_two` | :86 | BORDERLINE | inherits |
| `Module.Basis.HermiteNormalForm` | :189 | BORDERLINE | inherits |
| `…HNF.bN_eq` | :281 | BORDERLINE | now also **unused project-wide** (Step 8: REMOVE-DEAD) |
| `…HNF.quotient_isAddCyclic_iff_rankTwoContent_eq_one` | :352 | BORDERLINE | see G-24 |
| `Submodule.exists_hermiteNormalForm` | :369 | BORDERLINE | inherits |
| `Submodule.hermiteNormalForm` | Cox/CyclicSublattice.lean:55 | BORDERLINE | inherits |

## 9c — Triage of Step 4/6/7 findings

### LIKELY-YES — genuine gaps, statement at (or one generalisation from) mathlib generality
Legend: **C** = scratch-compiled by an analysis agent this session; **T** = statement typechecked only; **G** = grep-verified absent, needs the noted generalisation first.

Analytic (Steps 4A / 6 / 7A):
- `PeriodPair` uniqueness block (uniqueness.lean:154–282: ℘'' = 6℘² − g₂/2, coefficient recursion, `lattice_eq_of_g₂_eq_of_g₃_eq`) + sub-gap `AnalyticAt.eventuallyEq_of_iteratedDeriv_eq` — **AS**
- `cuspFunction_inv` (jfunction:262), `cuspFunction_apply_zero_of_tendsto` (:43), `cuspFunction_nat_mul_eq_cuspFunction_pow` (LaurentQExpansion:46), hypothesis-free `cuspFunction_add/mul_eventuallyEq` (:68–88), `cuspFunction_apply_zero_eq` (:340) — **AS**
- `meromorphicAt_of_comp_pow` (LaurentQExpansion:194; descent along z^m; ℂ-specific by Step 6 refutation) — **AS**
- `analyticTaylor_comp_pow` as "HasFPowerSeriesAt (G∘(·^m)) (ofScalars (expand m …))" over any 𝕜 — **G**
- `MeromorphicNFAt.analyticAt_of_eventually_norm_le` (NormalFormGrowth:21) — **C** compiles for 𝕜 → E
- `MeromorphicNFAt.comp_analyticAt_of_deriv_ne_zero`, `AnalyticAt.conj_conj`, `MeromorphicNFAt.conj_conj` (NormalFormSlash:22/32/39) — G/AS/AS
- `meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq`, `exists_analyticAt_pow_succ_mul…` (Cox/ModularFunction.lean:96, :294) — **G** (𝕜 → E, Step 6 G-13/14)
- `Subgroup.hasDetPlusMinusOne_conj`, `Subgroup.discreteTopology_conj` (CuspPeriod:21/29) — **AS**
- 8 codiscrete / `NeBot` lemmas (MeromorphicField.lean:46–117) → `Topology/DiscreteSubset` — **AS**
- `Algebra R (Filter.Germ l A)` instance (mathlib has only `instModule`) — **AS**
- `Filter.eventually_atImInfty` (AtImInfty:14), `arg_pow_aux` (clog_arg_lems:18), `hasProd_le_nonneg` (multipliable_lems:69, **G**: `IsOrderedMonoid`-free form), `Complex.im_tsum_eq_zero_of_forall` (**C**, 2 lines)
- `E₂_S_transform` (E2.lean:87), `E₂_isBoundedAtImInfty` + `norm_tsum_logDeriv_expo_le` (Eisenstein:660/609) — **AS**
- `analyticAt_cuspFunction_{mul,add,sub,neg,smul}`, `isBoundedAtImInfty_sub` (Tactic2/qexp_simp.lean:54–81, :142) — **AS**
- `ForMathlib_Cusps.zero_at_cusps_of_zero_at_infty` — mathlib repeats the composition inline 3× — **AS**
- `qExpansion_coeff_eq_circleIntegral_of_differentiableOn` (LaurentQExpansion:600) — weaker-hypothesis refactor of mathlib's own lemma — upstream as a PR to `QExpansion.lean`, delete locally
- `periodic_comp_ofComplex_of_vadd` (Congruence:36) — generalisation of `SlashInvariantFormClass.periodic_comp_ofComplex` — **AS**
- `modularFormModuleofIsScalarTower` (IntegralPowerSeries:191) — mathlib has `Module` only for ℝ/ℂ — **AS**
- publicise mathlib's private `hasFPowerSeriesOnBall_update` (QExpansion.lean:239) and expose the `δ`/`G2Term` block of `E2/Transform.lean:79–180` (before `public section`) — two small upstream PRs that each delete ≈ 50 project lines
- Transport lemma family `cuspFunction_eventuallyEq_comp` / `cuspFunction_comp₂_eventuallyEq` (Step 7A L1–L4, **C**) — natural home `NumberTheory/ModularForms/QExpansion.lean`

Algebraic (Steps 4B / 6 / 7B):
- `HahnSeries.mapRingHom` (**C**), `HahnSeries.coeffSubring (S : Subring R)` (**C**), `HahnSeries.leadingCoeff_pow` (**C**, `[NoZeroDivisors R]`), `CharP (HahnSeries Γ R) p` (**C**), `HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt` (**C**, 2 lines)
- `PowerSeries.map_frobenius_expand` (**T**; project uses `MvPowerSeries` version via `change`), `LaurentSeries.coeff_single_neg_mul_coe_expand` (**T**), `LaurentSeries.substMonomial` (**T**, def via `ofSuppBddBelow`)
- `PowerSeries.lifts` mirroring `Polynomial.lifts` (seeded by `HasCoeffsIn`, IntegralPowerSeries:51) — **G**
- `coeff_invOfUnit_one_succ` (link.lean:262, generic `[Ring R]`) — **AS**
- `ArithmeticFunction.dedekindPsi` (= `pmul μ μ * id`) + `card_coxMatrix = ψ m` + `(Gamma0 m).index = ψ m` (**C** for the index equality) — **G**
- `Matrix.exists_SL2_inv_mul_eq_upperTriangular` (Step 7B L1), `Matrix.SpecialLinearGroup.mul_coe_mul_coe_inv` (**C**), `Matrix.toLin_injective_of_det_ne_zero` (L34), `exists_coprime_add_mul_of_gcd_gcd_eq_one` (CoxMatrices/Basic:484) — AS
- `Polynomial.associated_iff_eq_or_eq_neg` over `R[X]` (Arithmetic:164) — **G**
- `card_le_minpoly_natDegree_of_injective_roots` / `irreducible_of_card_conjugates` (Irreducibility:89/102) — **G** (drop `minpoly`, conclude `p = minpoly F α`; Step 6 G-25)
- `eval_interpolation_sum_at` (Interpolation:301; un-normalised nodal sum, coincident nodes allowed) — **AS**
- Bivariate `coeff_coeff_swap`, `map_swap`, `diagonal_swap`, `specializeY_ext` (Construction:97/108/145/75) → `Algebra/Polynomial/Bivariate.lean` — **AS**
- `PeriodPair` scaling / homothety / `discriminant` / `j` (LatticeJ:33–164) + lattice→`WeierstrassCurve` bridge (jInvariantLink) — fills the mathlib TODO at `Weierstrass.lean:938` — **AS**
- `MeromorphicAt.aeval_polynomial` (CuspData:115), Γ₀(N) conjugation API (jLevelN:40–82, Congruence:50) — AS/G
- `Nat.not_isSquare_of_lt_of_lt` (ℤ-`IsSquare` corollary of `Nat.not_exists_sq'`) — AS (tiny)

### BORDERLINE — needs a human scoping decision before any PR
- The rank-2 HNF family (7 declarations above) — one decision: commit to rank-n over Bézout/PID (High; correct cyclic criterion D_{n−1}=1) or keep project-local.
- `ModularFunction Γ` bundle + `MeromorphicField` (ModularFunctions/): mathlib-idiomatic construction, but (i) it lacks ring/field operations, (ii) `MeromorphicField` is adapted from Kebekus's ProjectVD `VD/Field` — coordinate with that upstream effort rather than PR independently.
- `IsOfExponentialGrowth` / `GrowthAtCusp` — after restating as `∃ ρ ≥ 0, f =O[atImInfty] exp(ρ·im)` (Step 4A verified) it mirrors `BoundedAtCusp.lean`; PR only together with the meromorphy-at-cusp equivalence.
- `OnePoint.IsMeromorphicAt` (Cusps.lean:41) — no chart-independence lemmas yet.
- `symmetric_bidegree_three_eq_zero_of_laurent_coeff` — hard-coded at level 3 (Step 6 G-26); only the triangular kernel (SymmetricCubicLaurent:285–342) is general.
- `CyclicSublattice` classification (Thm 11.23) — generalise to any rank-2 free ℤ-module first (Step 6 G-22/23), then WORTH-FULL-CHECK.
- `Γ2_generate` (SlashActionAuxil:189) — genuinely new but consumer-less; park in git.
- `interpolationAt` un-normalised Lagrange sum — deliberate design; WORTH-FULL-CHECK with `Lagrange.nodal` framing.

### NO — mathlib already has it (Step 4A/4B, grep-verified; see step8-junk.md §2 for the file-level list)
`E₄ E₆ E4 E6 E` → `ModularForm.E₄/E₆/E`; `Δ Delta` → `ModularForm.discriminant`/`CuspForm.discriminant` (+ 9 wrappers); `G₂ E₂ D₂ D2_*` → `EisensteinSeries.*`; `eta.lean` (4) → `Discriminant.lean:66–143`; `csqrt` → `Complex.sqrt`; `IsCuspForm.lean` (17) → `CuspFormSubmodule.lean`; `DimensionFormulas.lean` (28 proved) → `LevelOne/DimensionFormula.lean`; `BigO.lean` (8) → `EisensteinSeries/Summable.lean`; Summability/{Basic,Reciprocal,QExpansion}, `tsumderivWithin`, `iteratedderivs`, `multipliable_lems`, `qExpansion_lems`, `exp_lems`, `equivs`, `upperhalfplane` (≈ 120 lemmas) → named mathlib lemmas per inventory; `SlashActionAuxil` generator lemmas (4) → `Identities.lean`/`LevelOne/Basic.lean`/`FixedDetMatrices.lean`; `Ek_q_exp*`, `q_exp_unique`, `cuspfunc_lim_coef`, `Delta_E4_E6_aux`, `deltaShiftedQSeries_analyticAt_aux` → `QExpansion.lean`/`GradedRing.lean`; `powerSeriesMapAlgHom`/`coeToComplexPowerSeries.ringHom` → `PowerSeries.mapAlgHom`/`map`; `analyticTaylor` → `UpperHalfPlane.qExpansion`; `ℍ'` → `upperHalfPlaneSet`; `natScaleUpperHalfPlane` → `posRealAction`; `matrix_eq_upper_triangular_aux` → `Matrix.eta_fin_two`; `specializeY_eval`/`diagonal_map`/`eval_swap`/`diagonal_eval₂` → `Bivariate.lean`; `coxPhiAtJ_monic/_natDegree` → `Lagrange.nodal_monic`/`natDegree_nodal`; `jUnitLaurentSeriesMod_eq_unitJPowerSeries` → `LaurentSeries.single_order_mul_powerSeriesPart`; `sigmaPow` → `ArithmeticFunction.sigma`; `foldl_push_toList` → `Array.foldl_toList_eq_map`; `not_isSquare_of_between_sq_aux` → `Nat.not_exists_sq'`; `precompAlgEquiv` → `AlgEquiv.ofRingEquiv`; `precomp_ratFunc` → `IsLocalization.ringHom_ext`; `conjugate_T_pow_mem_Gamma0` → `Gamma_normal`.

### NO — composable from mathlib (1–3 calls; verified where marked)
`rankTwoContent` (`Finset.gcd`, July), `index_eq_natAbs_det` (July), `belowDiagonal_eq_zero` (`Matrix.BlockTriangular`, **C**) with `det_of_upperTriangular` (**C**), `dualMatrix` (`Matrix.adjugate`, **C**), `carrierEquiv` (`Submodule.equivSubtypeMap`, **C**), `matrixStar` (`(submatrix Fin.rev Fin.rev)ᵀ`, **C**), the 4+1 anonymous `HahnSeries` builds (`HahnSeries.embDomain`, **C** for two of them), `bivariateLaurentEvalHom` (`aevalAeval`), `eval_derivative_prod_X_sub_C_at` (Lagrange, 3-line wrapper now), `hasse_qExpansion_principle` (`Polynomial.induction_with_natDegree_le` + `lifts`), `integerCoeffLaurentSeries`/`integralLaurentSeries` (`(laurentSeriesMapRingHom _).range`), `E_k_q_expansion`, `Delta_qExpansion_eq_smul_eisenstein_difference` (`discriminant_eq_E₄_cube_sub_E₆_sq_graded` + `qExpansionRingHom`), `mk_coeff_self`, `int_cast_div_eq_inv_mul_complex`, `IteratedDeriv_zero_fun`, `derivWithin_tsum_fun'`, `tendsto_neg_cexp_atImInfty`, `im_tprod_eq_zero…`, `bdd_at_cusps'`, `CuspForm_div_Discriminant`, `swap_equiv`, `negEquiv`, `succEquiv`.
