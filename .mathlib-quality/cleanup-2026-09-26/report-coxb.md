# CLEANUP_REPORT — worker coxb (Cox Ch. 11 §§B–C Laurent / Kronecker / level three), 2026-09-26

## 1. Final build (SB = /Users/dfa25dxu/Projects/Lean/.xyin-sandboxes/coxb)
```
info: XYinTest/qExpansion_tactic/Examples.lean:53:19: [qexp time: 19ms]
Build completed successfully (3711 jobs).
```
No warnings in any owned file (checked in the `lake build` log). No `sorry`/`admit`/`native_decide`/
`maxHeartbeats`/`maxRecDepth`. `#print axioms` of `theorem_11_18_v`, `modularPolynomial_three_of_complex_swap`,
`modularPolynomialC_diagonal_leadingCoeff_pow`, `exists_modularPolynomialZ`, `laurentqExpansion_coxAction`:
`[propext, Classical.choice, Quot.sound]`.

## 2. Files (lines before → after)
| file | before | after |
|---|---|---|
| XYin/PhD/Cox/CoxMatrices/LaurentExpansion.lean | 354 | 442 (gains the j-series API + moved order lemmas) |
| XYin/PhD/Cox/FormalCoxProduct.lean | 228 | 197 |
| XYin/PhD/Cox/LaurentPolynomialEvaluation.lean | 151 | 194 (gains generic lemmas moved from SCL/DL/LevelThree) |
| XYin/PhD/Cox/DiagonalLaurent.lean | 293 | 108 |
| XYin/PhD/Cox/SymmetricCubicLaurent.lean | 391 | 277 |
| XYin/PhD/Cox/Kronecker.lean | 771 | 355 |
| XYin/PhD/Cox/KroneckerFrobenius.lean | 233 | 109 |
| XYin/PhD/Cox/LevelThree.lean | 858 | 383 |
| XYin/PhD/Cox/ModularPolynomial/IntegralDescent.lean | 305 | 172 |
| **NEW** XYin/PhD/Cox/LaurentSeriesAux.lean | 0 | 137 (imported by LPE and LaurentExpansion; not added to XYin.lean) |
| **total** | 3584 | 2374 (−1210) |
No file outside the owned set was edited. `XYin.lean` unchanged (new file reached transitively).

## 3. Done items
### Task 1 — one series instead of four
* NEW `jLaurentSeriesWidth (R) [Ring R] (m : ℕ+) : LaurentSeries R` (via `HahnSeries.ofSuppBddBelow`) in
  `CoxMatrices/LaurentExpansion.lean` next to `jIntCoeff`, with `_coeff` (rfl), `@[simp] _coeff_mul`, `_coeff_of_not_dvd`,
  `@[simp] _map`, `_order`, `_leadingCoeff`, `_eq_single_mul_expand`, `_complex`, `_map_complex`; and
  `jUnitPowerSeries R` (+ `@[simp] coeff_jUnitPowerSeries`).
* Deleted (all only used inside the owned set): `jIntegralLaurentSeries` (+`_coeff`, `_map_complex`, both dead),
  `jIntegralLaurentSeriesWidth` (+`_coeff`, `_coeff_mul_map_complex`, `_map_complex`, `_map_zmod`),
  `jUnitLaurentSeriesMod` (+`_coeff`, `_coeff_neg_one`, `_coeff_eq_zero_of_lt`, `_order`), `jLaurentSeriesMod`
  (+`_coeff`, `_coeff_neg_p`, `_order`, `_leadingCoeff`), KF `unitJPowerSeries` (+`_coeff`), LevelThree
  `qjIntegralPowerSeriesThree`, `sigma/widthLaurentSeriesThree` (now `jLaurentSeriesWidth ℤ 9/3`).
* The twin order lemmas (row 126) are the single `jLaurentSeriesWidth_order` (via the new order helper).
* Frobenius (Kronecker:282–468, 190 lines of normal-form/case-split lemmas + KF:66–174): replaced by
  `jLaurentSeriesWidth_pow_prime_pow : jLaurentSeriesWidth (ZMod p) m ^ p ^ n = jLaurentSeriesWidth (ZMod p) (m * p ^ n)`
  (7 lines, via `_eq_single_mul_expand` + `PowerSeries.pow_prime_pow_eq_expand` + `PowerSeries.expand_mul`) and its n = 1 case.
* `transformedJSeries_eq_jLaurentSeriesWidth (hζ : ζ ^ (a*b) = 1) : transformedJSeries ζ σ = jLaurentSeriesWidth K ⟨a², _⟩`
  (the correct `sigmaZero` / phase-one identity); KF's σ₀/lower-root lemmas are now 1–3 lines.
* `transformedJSeries`, `cyclotomicTransformedJSeries` rebuilt with `HahnSeries.ofSuppBddBelow` (PWO blocks gone;
  `transformedJSeries_coeff` keeps its exact statement for UHPFF).
### Task 2 — `LaurentSeries.coeff_single_neg_mul_coe_expand` (LaurentSeriesAux, 20 lines, proved). After Task 1 it is
  needed once (`jLaurentSeriesWidth_eq_single_mul_expand`); all 5 former case-split sites are gone
  (KF:104–139, Kronecker:389–458, LevelThree:577–636, plus natAbs shims KF:98, LevelThree:559–575).
### Task 3 — LevelThree
* 35 jet lemmas + 29-line conjunction → ONE `decide +kernel` certificate
  `∀ i ≤ 3, ∀ j ≤ i, explicitCandidateClearedJetThree (36 - (9 * i + 3 * j)) = 0`; Term/Row defs merged.
* The three 10-fold conjunction transports (:518–557, :675–687, :806–819) are gone: SCL now takes
  `∀ i j, j ≤ i → i ≤ 3 → coeff (-(9i+3j)) = 0`, fed by a 4-line triangular lemma.
* `sigma/widthPowerSeriesThree_coeff_eq_jet` twins → one `expand_jUnitPowerSeries_coeff_eq_jet r`.
* `bivariateLaurentEval_map` + inline rebuilds → LPE `bivariateLaurentEvalHom_map`; order/leading-coefficient
  shims (:702–725) inlined as `simpa`; `modularPolynomialC_three_natDegree` via `card_coxMatrix_of_prime`;
  `modularPolynomialC_three_laurent_root` via new `formalCoxPolynomial_eval_transformedJSeries`;
  `shiftedPowerSeries_mul`/`clearTwoShiftedPowerSeries` golfed, `C_mul_single_one` deleted.
* Imports: dropped `Mathlib.RingTheory.PowerSeries.Trunc`; added `Mathlib.Tactic.NormNum.BigOperators` (FOLLOWUP).
* 29 `decide +kernel` sites → 2; 84 theorems → 29. Timings §7.
### Task 4 — Hahn/Laurent API (new `LaurentSeriesAux.lean`)
* `HahnSeries.mapRingHom` (+`@[simp] mapRingHom_apply`); `laurentSeriesMapRingHom` kept as `abbrev` of it
  (typeclass `[Semiring]`); FormalCoxProduct's hand-built twin deleted.
* `HahnSeries.coeffSubring` (+`@[simp] mem_coeffSubring`): `integralLaurentSeries` (FCP) and
  `integerCoeffLaurentSeries` (IntegralDescent) are now `coeffSubring (integralClosure ℤ K).toSubring` /
  `coeffSubring (Int.castRingHom ℂ).range` (two 23-line subring proofs deleted).
* `HahnSeries.leadingCoeff_pow` (`@[simp]`, `[NoZeroDivisors R]`); `HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt`;
  instance `HahnSeries.charP` (replaces KF `letI charP_of_injective_ringHom`);
  `PowerSeries.pow_prime_pow_eq_expand` (n-general; replaces Kronecker's `change`-defeq proof and KF's twin).
* KF `jUnitLaurentSeriesMod_eq_unitJPowerSeries` no longer needed at all (deleted with the chain).
### Task 5 — LPE / DiagonalLaurent
* LPE: `polynomial_eval₂_laurentSeries_{coeff_eq_zero_of_lt, order, leadingCoeff}` added; `[Field K]` →
  `[CommSemiring K] [NoZeroDivisors K]` (`_injective`: `[CommRing K] [NoZeroDivisors K]`);
  `laurentSeries_pow_leadingCoeff_of_eq_one` deleted (= `simp` with `leadingCoeff_pow`).
* DiagonalLaurent: 4 private K = ℂ re-proofs + `laurentqExpansion_polynomialIn_j_widthM` + 3 widthM helpers
  deleted; `cox_diagonal_factor_leadingCoeff` 47 → 23 lines (`leadingCoeff_sub`/`leadingCoeff_add_eq_right`);
  duplicated copyright header removed; `laurentqExpansion_j_order/leadingCoeff_widthM` and
  `transformedJSeries_order/_leadingCoeff` moved (same names/statements) to LaurentExpansion, 1–4-line proofs.
* FCP: dead `[CharZero K]` (×3) gone; `formalCoxPolynomial_map_coeff_coeff` helper (row 146) shortens
  `_coeff_fixed`/`_coeff_isInteger`; `transformedJSeries_map`, `formalCoxPolynomial_map` made public.
* Dead `[Fact (Nat.Prime p)]` (KF:77, Kronecker:263/389/426/445) disappeared with the deleted lemmas; the
  remaining ones are needed by statements (`transformedJSeries (1 : ZMod p)` needs `Field (ZMod p)`).
### Task 6 — SymmetricCubicLaurent
* `bivariateLaurentEvalHom` made public in LPE (`[CommSemiring R]`) with `_apply`, `@[simp] _monomial/_X/_C_X`,
  `_map`; SCL wrapper `bivariateLaurentEval` and `_add` deleted; quadruplet `_coeff_zero/one/two/three` deleted;
  `coeff_comm_of_swap_eq` → local `have` (1 line); `[Field K]` → `[CommRing K] [IsDomain K]`
  (algebraic part only `[CommRing K]`); final `fin_cases`/`norm_num`/`assumption` step → direct term.
### Task 7 — IntegralDescent
* width-1 inductions/aux (:25–70) deleted → `laurentqExpansion_polynomial_eval`, `laurentqExpansion_j_*_widthM 1`,
  LPE lemma; `:181` → `meromorphicAt_cuspFunction_neg`; Hasse principle restated in subring/lifts form and proved
  by a 16-line strong induction (`eraseLead_natDegree_lt_or_eraseLead_eq_zero`, `monomial_mem_lifts`);
  `bivariate_exists_of_coeff_lifts` inlined (`mem_lifts` + `lifts_iff_coeff_lifts`); `∃ z : ℤ` → subring membership
  in `hasse_qExpansion_principle`, `coxPhiFunction_coeff_integerLaurent` (4 `obtain ⟨z,hz⟩` dances gone).
### Task 8 — Kronecker misc
* `cyclotomicDescent_dvd` 26 → 10 lines (`cyclotomic_eq_minpoly` + `minpoly.isIntegrallyClosed_dvd`).
* Twins → `cyclotomicTransformedJSeries_map` / `cyclotomicCoxPolynomial_map` (φ, ζ, hφ); `_map_complex/_mod`
  (Cox product) are 1-line instances; `specializeJIntegral_map_zmod/_complex` 1-line terms;
  `specializeJMod_modularPolynomial_eq_formal` 33 → 6 lines; `primeFinToCoxMatrix_surjective` via
  `CoxMatrix.ext`/`a_dvd`; redundant LPE import dropped; dead `transformedJSeries_one_sigmaZero_eq_primeLower_pow` deleted.
* `specializeJMod_varX/varY` KEPT: step8's "dead" verdict is wrong — `simp` in `kronecker_after_specializeJ`
  needs them (verified: `simp [-specializeJMod_varX, -specializeJMod_varY]` fails).
### Task 9 — CoxMatrices/LaurentExpansion
* `jIntCoeff_eq_zero_of_lt` moved here (2-line proof from `j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one`);
  `jIntCoeff_neg_one` 10 → 5 lines (`coeff_neg_poleOrder_add'`); new `zeta_ne_zero`.
* lqe follow-ups: `eventually_ne_zero_and_norm_lt_one` (:124–131), `meromorphicOrderAt_comp_const_mul_pow`
  (`poleOrder_coxAction_aux` 42 → 10 lines), `poleRemoved_apply`, `coeff_of_geq'`, `cuspFunction_apply_of_ne_zero`;
  `cuspFunction_coxAction_aux` inlined.
* FunLike: `to_qExpansion_coxAction_aux` uses a local `letI : FunLike (ℍ → ℂ) ℍ ℂ`; verified independent of the
  global `instFunLikeForallUpperHalfPlaneComplex_xYin` (compiles with `attribute [-instance]`, fails without the letI).
* `reindex` term-mode structure literal + `@[simp] reindex_a/_b/_d`; `reindex_bijective` via `CoxMatrix.ext`,
  `d_dvd`, `Nat.ModEq.cancel_right_of_coprime`; import `Cyclotomic.Basic` → `RootsOfUnity.Complex`.
* `substMonomial` bridge: NOT done (see §6).

## 4. New public API
LaurentSeriesAux: `HahnSeries.mapRingHom f : R⟦Γ⟧ →+* S⟦Γ⟧`, `mapRingHom_apply : mapRingHom f x = x.map f`;
`HahnSeries.coeffSubring S : Subring R⟦Γ⟧`, `mem_coeffSubring : x ∈ coeffSubring S ↔ ∀ g, x.coeff g ∈ S`;
`HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt (h : x.coeff g ≠ 0) (h' : ∀ i < g, x.coeff i = 0) : x.order = g`;
`HahnSeries.leadingCoeff_pow : (x ^ n).leadingCoeff = x.leadingCoeff ^ n`; `instance HahnSeries.charP : CharP R⟦Γ⟧ p`;
`LaurentSeries.coeff_single_neg_mul_coe_expand : (single (-N) 1 * ↑(F.expand N hN)).coeff k = if ↑N ∣ k ∧ -↑N ≤ k then coeff (k / N + 1).toNat F else 0`;
`PowerSeries.pow_prime_pow_eq_expand : F ^ p ^ n = F.expand (p ^ n) _` (over `ZMod p`).
LPE: `laurentSeriesMapRingHom_comp_eval₂RingHom (hJ) : (lsmrh f).comp (eval₂RingHom C J) = (eval₂RingHom C J').comp (mapRingHom f)`;
`bivariateLaurentEvalHom T J : R[X][X] →+* LaurentSeries R` (+`_apply`, `_monomial`, `_X`, `_C_X`, `_map (hT) (hJ) P`);
`polynomial_eval₂_laurentSeries_coeff_eq_zero_of_lt`, `_order (hP : P ≠ 0) : = -(w * deg P)`, `_leadingCoeff : = P.leadingCoeff`.
LaurentExpansion: `zeta_ne_zero`; `jUnitPowerSeries R`, `coeff_jUnitPowerSeries`; `jLaurentSeriesWidth R m` + 9 lemmas (§3);
`transformedJSeries_eq_jLaurentSeriesWidth`; `transformedJSeries_coeff_neg_sq : coeff (-a²) = ζ ^ (-(a b))`; `reindex_a/_b/_d`.
FCP: `transformedJSeries_map`, `formalCoxPolynomial_map` (were private); `formalCoxPolynomial_eval_transformedJSeries : (formalCoxPolynomial m ζ).eval (transformedJSeries ζ σ) = 0`.
Kronecker: `jLaurentSeriesWidth_pow_prime_pow`, `jLaurentSeriesWidth_pow_prime`, `cyclotomicTransformedJSeries_map`, `cyclotomicCoxPolynomial_map`.

Statement changes of existing public decls (0 users outside the owned set): `hasse_qExpansion_principle`,
`coxPhiFunction_coeff_integerLaurent` (subring form); `symmetric_bidegree_three_eq_zero_of_laurent_coeff`
(`[CommRing K] [IsDomain K]`, ∀-form `hcoeff`); LPE lemmas (weaker typeclasses); KF/Kronecker statements now say
`jLaurentSeriesWidth (ZMod p) 1 / p` instead of `jUnitLaurentSeriesMod p / jLaurentSeriesMod p`;
`cyclotomicDescent_polynomialLaurentSeries` phrased with `phaseEvalComplex/phaseEvalMod` (defeq).
All externally used names/statements unchanged (`jIntCoeff_neg_one`, `laurentqExpansion_coxAction`, `transformedJSeries(_coeff)`,
`zeta(_isPrimitiveRoot)`, `modularPolynomial(_map_complex, _monic)`, `modularPolynomialC_diagonal_leadingCoeff_pow`,
`modularPolynomialThreeExplicit`, `modularPolynomial_three_of_complex_swap`, `theorem_11_18_v`).

## 5. Kept on purpose
`jLaurentSeriesWidth_pow_prime_pow` (n-general; only n = 1 used); `specializeJMod_varX/varY` (used by `simp`);
`jUnitPowerSeries` (used by LevelThree and the Frobenius proof); `polynomial_eval₂_laurentSeries_order`.

## 6. Deferred
1. `LaurentSeries.substMonomial` + analytic bridge (row 141 / L21): the only in-set instance is the private
   chain LaurentExpansion:213–405 (~190 lines); the other instance (c = 1) is lqe's `laurentqExpansion_nat_mul`
   (Algebra.lean, not mine). A general bridge needs re-proving Algebra's private `analyticTaylor_comp_pow` with a
   rescale and a general `HasSum` q-expansion for `poleRemoved`, ~150 lines → no net deletion inside the owned
   set. Design: `substMonomial c r hr F := embDomain (natMulOrderEmbedding r hr) (rescaleZ c F)`,
   `coeff k = if r ∣ k then c^(k/r) * F.coeff (k/r) else 0`, bridge
   `(∀ τ, qParam h' (φ τ) = c * qParam h τ ^ r) → laurentqExpansion h (f ∘ φ) = substMonomial c r hr (laurentqExpansion h' f)`;
   then `transformedJSeries ζ σ = substMonomial (ζ^(ab)) (a²) _ (jLaurentSeriesWidth K 1)`.
2. UHPFF (coxc/final): `transformed_leading` (UHPFF:140–147) = new public `transformedJSeries_coeff_neg_sq`;
   `transformed_leading_ne` = `zpow_ne_zero _ (zeta_ne_zero m)`; UHPFF:152, :186 → `zeta_ne_zero m`.
   Dropping the redundant `-(a²) ≤ k` clause from `transformedJSeries(_coeff)` is only blocked by UHPFF:143–147, 163.
3. Construction (coxc/final): `modularPolynomialC_coeff_polynomialIn` (IntegralDescent:134) belongs beside
   `modularPolynomialC_specializeY` (Construction's `coxCoefficientPolynomialAux_eval` is private — cannot be reused).
4. Eisenstein.lean (final): the global `FunLike (ℍ → ℂ) ℍ ℂ` instance is no longer needed by any owned file (only
   `jfunction.lean:197-201`, jq); the `Mathlib.Tactic.NormNum.BigOperators` re-export is no longer needed by LevelThree.
5. LevelThree jets (`jetMul/Pow/Shift/Expand`) ≡ `qExpansion_tactic/Qj.lean` computable layer (qExpansion_tactic owner).
6. `coxPhiFunction_coeff_laurentqExpansion_widthM` (38 lines, two Vieta copies) collapses once a bundled
   `laurentqExpansionRingHom` on a cusp-meromorphic subring exists (lqe-deferred).
7. `bivariateLaurentEvalHom` as `(Polynomial.aevalAeval J T).toRingHom`: evaluated, does not shorten anything.
8. G-26 (bidegree ≤ n) — High, not attempted. Renames (`theorem_11_18_*`, `varX/varY`) — style, deferred.
9. PROJECT_OVERVIEW.md (lines ~235–526) still names the deleted series (`jIntegralLaurentSeries`, `jLaurentSeriesMod`, …).

## 7. Perf (kernel-computation file LevelThree.lean; `time lake env lean XYin/PhD/Cox/LevelThree.lean`)
* Session start (old file): 12.01 s, 11.25 s. Mid-session (new file): 9.39 s, 9.50 s.
* Back-to-back under identical load (old chain temporarily restored from SB.base and rebuilt, then new restored):
  OLD 16.97 / 16.84 / 17.40 s (user 21.0 / 20.8 / 21.7) — NEW 14.82 / 14.90 / 14.09 s (user 15.8 / 16.9 / 15.8)
  → new ≈ 0.86× wall, ≈ 0.76× user.
* Kernel part isolated (scratch, identical imports; imports alone 4.8 s real / 1.4 s user): old 29-site split
  11.6–11.8 s real / 8.5–8.8 s user; new single certificate 10.0–10.3 s real / 6.6–6.8 s user
  (profiler: the certificate is one 5–6 s declaration).
* Other owned files (no kernel computation): 4.6–6.5 s each, unchanged within noise.
