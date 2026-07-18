# Step 4 — Mathlib API audit: Laurent-series computation & certified-computation layers

Files audited (all read in full):
`XYin/PhD/Cox/LaurentPolynomialEvaluation.lean`, `Cox/DiagonalLaurent.lean`,
`Cox/SymmetricCubicLaurent.lean`, `Cox/Kronecker.lean`, `Cox/KroneckerFrobenius.lean`,
`Cox/LevelThree.lean`, `qExpansion_tactic/Qj.lean`, `qExpansion_tactic/link.lean`,
`Tactic2/qexp_simp.lean`.

Every mathlib name cited below was verified to exist by grep against
`.lake/packages/mathlib` (file:line noted where useful).

---

## Definitions to Replace with Mathlib

**`bivariateLaurentEvalHom` / `bivariateLaurentEval` (SymmetricCubicLaurent.lean:143–150, private) → use `Polynomial.evalEvalRingHom` / `Polynomial.evalEval` / `Polynomial.aevalAeval`** —
Current: hand-bundled `Polynomial.eval₂RingHom (Polynomial.eval₂RingHom HahnSeries.C J) T`, plus bespoke `bivariateLaurentEval_add` / `bivariateLaurentEval_monomial` simp lemmas.
Mathlib alternative (verified, `Mathlib/Algebra/Polynomial/Bivariate.lean`): `Polynomial.evalEval`, `Polynomial.evalEvalRingHom` (line 151), `Polynomial.aevalAeval : R[X][Y] →ₐ[R] A` (line 230), and crucially `Polynomial.eval₂RingHom_eval₂RingHom (f : R →+* S) (x y : S) : eval₂RingHom (eval₂RingHom f x) y = (evalEvalRingHom x y).comp (mapRingHom (mapRingHom f))` (line 189) and `Polynomial.eval₂_eval₂RingHom_apply` (line 194). Since `HahnSeries.C = algebraMap K (LaurentSeries K)` (`HahnSeries.C_eq_algebraMap`, Multiplication.lean:928), `bivariateLaurentEvalHom T J` is `(aevalAeval J T : K[X][Y] →ₐ[K] LaurentSeries K)` (note argument order: inner variable ↦ J, `Y` ↦ T).
Impact: deletes two private defs and two simp lemmas; the `evalEval` API (`evalEval_add/mul/pow/prod/monomial`, `aevalAeval_C/X/Y`) replaces the hand-rolled ones.
**Action**: replace the private defs by `aevalAeval`/`evalEvalRingHom` composed with `mapRingHom (mapRingHom HahnSeries.C)` via `eval₂RingHom_eval₂RingHom`; keep statements of the public theorem unchanged.
Difficulty: medium (mechanical but touches many `change`/`rfl` steps).

**`invFn` (link.lean:302–310) → `PowerSeries.invOfUnit`** —
Current: a bespoke well-founded recursion for the coefficients of `(1 + Σ α(k+1)qᵏ⁺¹)⁻¹`, plus the 25-line hand proof `qoverDelta_mul_eq_one`.
Mathlib alternative (verified, `Mathlib/RingTheory/PowerSeries/Inverse.lean`): `PowerSeries.invOfUnit` (line 84), `PowerSeries.coeff_invOfUnit` (line 87 — exactly the same recursion, with `u = 1`), `PowerSeries.mul_invOfUnit (φ u) (h : constantCoeff φ = u) : φ * invOfUnit φ u = 1` (line 102).
Impact: `invFn`, `invFn_succ`, and `qoverDelta_mul_eq_one` (~45 lines) collapse; `qOverDelta_qexpansion_link` keeps working since `mul_invOfUnit` provides the unit identity directly. The array bridge `inverseOnePlusCoeffsUpTo_getD` would be re-targeted at `coeff_invOfUnit` (antidiagonal-filtered sum) instead of `invFn`.
**Action**: define the abstract inverse as `PowerSeries.invOfUnit (PowerSeries.mk deltaOverQCoeffInt) 1` and re-derive the array agreement by strong induction from `coeff_invOfUnit`.
Difficulty: medium.

---

## API Choice Improvements

**`jIntegralLaurentSeries`, `jIntegralLaurentSeriesWidth`, `jLaurentSeriesMod`, `cyclotomicTransformedJSeries` (Kronecker.lean:160, 184, 300, 594) → `HahnSeries.ofSuppBddBelow`** —
Current: four anonymous-constructor `LaurentSeries` builds, each repeating the boilerplate `Set.IsWF.isPWO (BddBelow.isWF ⟨bound, …⟩)`.
Mathlib alternative (verified, `Mathlib/RingTheory/HahnSeries/Basic.lean:574`): `HahnSeries.ofSuppBddBelow (f : Γ → R) (hf : BddBelow (Function.support f))`, tagged `@[simps]`, with `coeff_ofSuppBddBelow` (line 589), `ofSuppBddBelow_eq_zero`, and support helper `forallLTEqZero_supp_BddBelow`. (`suppBddBelow_supp_PWO` is deprecated in favour of `BddBelow.isWF`, 2026-01-02.)
Impact: kills 4 × ~10 lines of PWO plumbing and the four manual `_coeff` rfl-lemmas (the `@[simps]` projections do it).
**Action**: rewrite the four definitions with `HahnSeries.ofSuppBddBelow`; drop the hand-written `isPWO_support'` proofs.
Difficulty: low.

**`jLaurentSeriesMod` (Kronecker.lean:300) → define as `(jIntegralLaurentSeriesWidth p).map (Int.castRingHom (ZMod p))`** —
Current: an independent coefficientwise definition, then `jIntegralLaurentSeriesWidth_map_zmod` proves it agrees with the map of the integral series.
Alternative: make the map the definition (via the project's own `laurentSeriesMapRingHom`); `jIntegralLaurentSeriesWidth_map_zmod` becomes `rfl` and `jLaurentSeriesMod_coeff` follows from `laurentSeriesMapRingHom_coeff` + `jIntegralLaurentSeriesWidth_coeff` and `Int.cast_ite/Int.cast_zero` (push_cast).
Impact: one fewer bespoke Hahn-series construction; keeps every downstream statement.
**Action**: redefine and simp-derive the coeff lemma. Difficulty: low.

**Optional: width series as `HahnSeries.embDomainRingHom`** — mathlib has `HahnSeries.embDomainRingHom (f : Γ →+ Γ') (hfi : Injective f) (hf : ∀ g g', f g ≤ f g' ↔ g ≤ g')` (`Multiplication.lean:899`) with `embDomain_coeff` (Basic.lean:449). `jIntegralLaurentSeriesWidth m` is exactly `embDomainRingHom (AddMonoidHom.mulLeft (m : ℤ)) … jIntegralLaurentSeries` up to the (redundant) `-(m) ≤ k` guard, since `jIntCoeff` vanishes below `-1` (`jIntCoeff_eq_zero_of_lt`). This buys multiplicativity of the width construction for free (relevant to `jUnitLaurentSeriesMod_pow_prime`). Difficulty: medium; worthwhile only if more width-change lemmas are needed.

**Order-computation blocks (DiagonalLaurent.lean:64–83 `transformedJSeries_order`; Kronecker.lean:263–280 `jUnitLaurentSeriesMod_order`, 339–359 `jLaurentSeriesMod_order`; DiagonalLaurent.lean:314–339 `eval₂_…_leadingCoeff_widthM`) → `HahnSeries.order_le_of_coeff_ne_zero` + `HahnSeries.le_order_iff_forall`** —
Current: each computes `orderTop` via `HahnSeries.orderTop_eq_of_le`, then converts with `order_eq_orderTop_of_ne_zero` and `exact_mod_cast` (4 near-identical ~15-line blocks).
Mathlib alternative (verified, HahnSeries/Basic.lean): `order_le_of_coeff_ne_zero` (line 383) and `le_order_iff_forall` (near line 560, cf. `order_lt_iff_exists` line 560) give `order = k` directly by `le_antisymm`, no `orderTop`/`WithTop` casting.
Impact: ~40 lines saved, and no `exact_mod_cast` on `WithTop ℤ`.
**Action**: extract one project helper `LaurentSeries.order_eq_of_coeff (h₁ : F.coeff k ≠ 0) (h₂ : ∀ j < k, F.coeff j = 0) : F.order = k` proved with the two mathlib lemmas, and use it in all four places. Difficulty: low.

**`powerSeries_pow_prime_eq_expand` (Kronecker.lean:282) and `unitJPowerSeries_pow_prime_sq_eq_expand` (KroneckerFrobenius.lean:149) → unify via `ZMod.frobenius_zmod`** —
Current: the first proves `F ^ p = expand p F` over `ZMod p` with a hand `ext`/`ZMod.pow_card` step to remove the Frobenius map; the second separately proves `F ^ (p²) = expand (p²) F` with a hand `iterateFrobenius … = RingHom.id` computation from `ZMod.pow_card_pow`.
Mathlib alternative (all verified): `ZMod.frobenius_zmod : frobenius (ZMod p) p = RingHom.id _` (`Mathlib/FieldTheory/Finite/Basic.lean:593`); `MvPowerSeries.map_iterateFrobenius_expand` (`Mathlib/RingTheory/MvPowerSeries/Expand.lean:247`); `iterateFrobenius` of the identity collapses by `frobenius_zmod` + `RingHom.id` iteration (or keep `ZMod.pow_card_pow`, Basic.lean:587).
Impact: one general lemma `(F : PowerSeries (ZMod p)) : F ^ p ^ k = F.expand (p ^ k) …` serves both call sites; each proof shrinks to ~4 lines.
**Action**: state the general lemma once (in Kronecker.lean), instantiate `k = 1` and `k = 2`. Note: mathlib has no `PowerSeries.map_frobenius_expand` (only the `MvPowerSeries`/`MvPolynomial` versions — verified `PowerSeries/Expand.lean` contains no `frobenius` lemma), so the general single-variable lemma is also a small **mathlib-PR candidate**.
Difficulty: low.

**`bivariateLaurentEval_map` (LevelThree.lean:638–674, private) → derive from `Polynomial.eval₂_eval₂RingHom_apply` + `Polynomial.map_mapRingHom_evalEval`, and relocate** —
Lead confirmed: it is fully generic (`{R S : Type*} [CommRing R] [CommRing S]`) and its inner `hinner` block re-proves `polynomialEvalLaurent_map` of `LaurentPolynomialEvaluation.lean:44` verbatim.
Not in mathlib as stated (the `HahnSeries.map_C` glue is project-specific), but the skeleton is: `Polynomial.eval₂_eval₂RingHom_apply` (Bivariate.lean:194) converts both sides to `evalEval` of a doubly-mapped polynomial, then `Polynomial.map_mapRingHom_evalEval (f) (x y) : (p.map (mapRingHom f)).evalEval (f x) (f y) = f (p.evalEval x y)` (Bivariate.lean:179) with `f := laurentSeriesMapRingHom …` plus `Polynomial.map_map` and `HahnSeries.map_C` finishes it.
Impact: ~37 lines → ~10; removes the duplicated inner calc.
**Action**: move the lemma to `LaurentPolynomialEvaluation.lean` (next to `bivariateSpecializeLaurent_map`), reprove via the Bivariate API, reuse `polynomialEvalLaurent_map` (un-private it) instead of inlining it. Difficulty: medium.

**`polynomial_eval₂_laurentSeries_injective` (LaurentPolynomialEvaluation.lean:159) — optional restatement as `Transcendental`** —
Since `HahnSeries.C = algebraMap K (LaurentSeries K)` (`HahnSeries.C_eq_algebraMap`), the statement is `Function.Injective (aeval J)`, i.e. `Transcendental K J` by `transcendental_iff_injective` (`Mathlib/RingTheory/Algebraic/Basic.lean:105`, verified). Recording the corollary `Transcendental K J` would connect this file to mathlib's algebraic/transcendental API for later use (e.g. `Algebra.adjoin` results). The order-based proof itself has no mathlib replacement.
**Action**: add a `Transcendental` corollary; keep the proof. Difficulty: low.

---

## Hand-Rolled Patterns to Replace

**`sigmaPow_eq_sigma` (link.lean:110–153, 44 lines) → `Nat.filter_dvd_eq_divisors`** —
Lead partially refuted: it does *use* `ArithmeticFunction.sigma_apply` (verified: `Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:151`), so it is not re-proving it — but the 30-line `Finset.sum_bij` establishing `{i ∈ range n | n % (i+1) = 0} ↦ divisors` is re-proving mathlib's `Nat.filter_dvd_eq_divisors (h : n ≠ 0) : {d ∈ range n.succ | d ∣ n} = n.divisors` (`Mathlib/NumberTheory/Divisors.lean:80`, verified).
**Action**: rewrite as: convert the mod-test to `∣` (`Nat.dvd_iff_mod_eq_zero`), shift `range n` under `i ↦ i+1` (`Finset.sum_range_succ'`/`Finset.sum_Ico_eq_sum_range`), and close with `Finset.sum_filter` + `Nat.filter_dvd_eq_divisors`. Expected ~12 lines. Difficulty: low-medium.

**Duplicate `leadingCoeff`-of-power inductions → one local `HahnSeries.leadingCoeff_pow`** —
`laurentSeries_pow_leadingCoeff_of_eq_one` (LaurentPolynomialEvaluation.lean:111) and the private `laurentqExpansion_j_pow_leadingCoeff_widthM` (DiagonalLaurent.lean:250) are the same induction; `laurentMonomial_leadingCoeff` (SymmetricCubicLaurent.lean:192) reuses the first. Mathlib has `HahnSeries.leadingCoeff_mul` (`Multiplication.lean:573`) and `leadingCoeff_one` but **no `leadingCoeff_pow`** (verified by grep — only `Polynomial.leadingCoeff_pow` exists).
**Action**: prove `HahnSeries.leadingCoeff_pow [NoZeroDivisors R] : (x ^ n).leadingCoeff = x.leadingCoeff ^ n` once (3-line induction from `leadingCoeff_mul`), derive both `…_of_eq_one` variants; flag as a **mathlib-PR candidate** next to `order_pow` (`Multiplication.lean:1034`). Difficulty: low.

**DiagonalLaurent.lean:258–339 re-proves the generic lowest-coefficient lemma at `K = ℂ`** —
`eval₂_laurentqExpansion_j_coeff_widthM`, `eval₂_laurentqExpansion_j_coeff_eq_zero_of_lt_widthM`, `eval₂_laurentqExpansion_j_leadingCoeff_widthM` duplicate `polynomial_eval₂_laurentSeries_coeff` (LaurentPolynomialEvaluation.lean:121) and its proof structure almost line-for-line, instead of instantiating it at `J := laurentqExpansion (m) j`, `w := m` (both hypotheses `order = -m`, `leadingCoeff = 1` are already proved in the same file).
**Action**: generalize the two missing pieces (`coeff_eq_zero_of_lt` and `leadingCoeff` versions) into `LaurentPolynomialEvaluation.lean` with the `(J, w, hw, horder, hleading)` signature, then delete the ~80 private lines in DiagonalLaurent. Difficulty: medium.

**`int_dvd_iff_dvd_add_natAbs` (LevelThree.lean:559) vs `prime_sq_dvd_iff_dvd_shift_natAbs` (KroneckerFrobenius.lean:98)** —
Same statement (`(d:ℤ) ∣ k ↔ d ∣ (k+d).natAbs`), proved twice; LevelThree's version is the general one.
**Action**: keep one copy (e.g. in Kronecker.lean, un-private) and use it in both files; the specializations `three_dvd_…`/`nine_dvd_…` then stay as `simpa`s. Difficulty: low.

**`unitJPowerSeries` (KroneckerFrobenius.lean:66) vs `qjIntegralPowerSeriesThree` (LevelThree.lean:132)** —
Both are `PowerSeries.mk fun n ↦ jIntCoeff ((n : ℤ) - 1)` (the second is `unitJPowerSeries ℤ` after `Int.cast_id`).
**Action**: un-private `unitJPowerSeries` and let LevelThree use `unitJPowerSeries ℤ`. Difficulty: low.

**`symmetricCubicExpansion_coeff_zero/one/two/three` (SymmetricCubicLaurent.lean:44–118)** —
Four byte-identical proofs differing only in the index literal.
**Action**: one lemma `symmetricCubicExpansion_coeff (i : ℕ) (hi : i ≤ 3) …` closed by `interval_cases i` (the existing tactic block already handles all four uniformly). Difficulty: low. (Internal cleanup, no mathlib content.)

**`C_mul_single_one`, `shiftedPowerSeries_mul/pow` (LevelThree.lean:147–198)** —
Thin compositions of `HahnSeries.single_mul_single` (`Multiplication.lean` — verified), `HahnSeries.single_pow` (line 795), `HahnSeries.C_mul_eq_smul` (line 848) and `RingHom.map_mul/map_pow` of `HahnSeries.ofPowerSeries` (`HahnSeries/PowerSeries.lean:89`). No single mathlib lemma covers them; keeping them as local helpers is correct, but they belong in one place if any other file grows the same normal-form manipulation.

---

## Missing tags/instances

**`jLaurentSeriesMod_coeff` (Kronecker.lean:313) and `cyclotomicTransformedJSeries_coeff` (Kronecker.lean:611) — add `@[simp]`** — their siblings `jUnitLaurentSeriesMod_coeff`, `jIntegralLaurentSeriesWidth_coeff`, `jIntegralLaurentSeries_coeff`, `laurentSeriesMapRingHom_coeff` are all `@[simp]` rfl-lemmas; these two are the same kind but untagged, forcing explicit `rw` chains downstream. (Moot for whichever defs move to `ofSuppBddBelow` `@[simps]`.)

**`qj_qexpansion_coeff_eq`, `Delta_qexpansion_coeff_eq` (Qj.lean:156, 163) — add `@[simp]`** — pure `coeff_mk` unfoldings, used repeatedly by `rw` in link.lean.

**`laurentSeriesMapRingHom` — add `laurentSeriesMapRingHom_id` / `_comp` functoriality lemmas** if the descent chains grow (currently every ℤ→ℂ / ℤ→ZMod / Polynomial-eval map is threaded by hand through `bivariateSpecializeLaurent_map_apply`); not urgent.

No missing instances found: the local `CharP (LaurentSeries (ZMod p))` via `charP_of_injective_ringHom` (KroneckerFrobenius.lean:203) is the idiomatic route (mathlib has no `CharP` instance for `HahnSeries`), and `Fact (Nat.Prime p)` threading is standard.

---

## Verified no-change (including refuted leads)

**`laurentSeriesMapRingHom` (LaurentPolynomialEvaluation.lean:22) — KEEP; mathlib has no equivalent** — Verified: mathlib's `HahnSeries.map` (`Basic.lean:143`) is an unbundled function on `ZeroHomClass`, and the protected `HahnSeries.map_zero/map_one/map_add/map_mul/map_C` lemmas (exactly the four used here) are an assembly kit — no bundled `R⟦Γ⟧ →+* S⟦Γ⟧` exists anywhere in `Mathlib/RingTheory/HahnSeries/` or `LaurentSeries.lean` (`embDomainRingHom` acts on the *exponent* group, not coefficients). The project def is right. **Upstream candidate**: generalize to `HahnSeries.mapRingHom (f : R →+* S) : R⟦Γ⟧ →+* S⟦Γ⟧` and PR it; the proof is exactly the current four fields.

**`bivariateSpecializeLaurent` — KEEP** — it is already a composition of mathlib API (`Polynomial.mapRingHom`, `Polynomial.eval₂RingHom`); nothing thinner exists. Its map-commutation lemmas necessarily involve `HahnSeries.map_C` and stay project-side.

**`phasePolynomial` / `cyclotomicCoxPolynomial` vs `Polynomial.cyclotomic` — LEAD REFUTED** — `phasePolynomial p e = X ^ (e % p).toNat` is a monomial lift of a root-of-unity phase, and `cyclotomicCoxPolynomial` is a product over Cox matrices; neither is a cyclotomic polynomial. The actual cyclotomic content (`cyclotomicDescent_dvd`, Kronecker.lean:691) already uses the correct mathlib API: `Polynomial.cyclotomic_eq_minpoly_rat`, `minpoly.dvd`, `Polynomial.map_cyclotomic`, `Polynomial.cyclotomic.monic`, `Polynomial.eval_one_cyclotomic_prime` — all verified. No change.

**LevelThree jet infrastructure (`jetMul`, `jetPow`, `jetShift`, `jetExpand`) — LEAD REFUTED as a replacement target** — Mathlib's truncation API (`PowerSeries.trunc`, `coeff_trunc`, `trunc_trunc_mul_trunc`, `trunc_trunc_pow`, `coeff_mul_eq_coeff_trunc_mul_trunc₂` — all verified in `Mathlib/RingTheory/PowerSeries/Trunc.lean`) lands in `Polynomial R`, a `Finsupp`-based type that is hopeless for `decide +kernel` evaluation; mathlib has no computation-friendly truncated-power-series ring (`TruncatedWittVector` is a different animal). The `ℕ → ℤ` jets with explicit bound 37 are the right vehicle for kernel certification, and the bridging lemmas (`powerSeries_coeff_mul_eq_jetMul` etc.) already lean on the right mathlib primitives (`PowerSeries.coeff_mul`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, `PowerSeries.coeff_X_pow_mul'`, `PowerSeries.coeff_expand`). Note only: `jetExpand`/`jetShift` mirror `PowerSeries.coeff_expand` / `coeff_X_pow_mul'` semantics by design.

**Qj.lean array layer (`sigmaPow`, `coeffArray`, `convArrayCoeff/UpTo`, `inverseOnePlusCoeffsUpTo`) — KEEP (modulo the `invFn` item above)** — no mathlib support exists for certified fast convolution; `ArithmeticFunction.sigma` is computable but far too slow under `native_decide`-scale evaluation, and `Nat.divisorsAntidiagonalList` (Divisors.lean:73) would not change that materially. The architecture (fast `Array` code + `link.lean` bridge to `PowerSeries`) is sound. The `foldl`/`push` bridging lemmas (`foldl_push_toList`, `foldl_push_getD`, `foldl_range_add_eq_sum`) have no mathlib/Batteries equivalents (verified by grep); keep.

**`qexp_simps` simp set (Tactic2/qexp_simp.lean) — LEAD REFUTED; mechanism and content are right** — Verified against `Mathlib/NumberTheory/ModularForms/QExpansion.lean`: the base lemmas the set tags (`qExpansion_mul/add/sub/neg/smul/zero/one` at lines 466–515, `cuspFunction_mul/add/sub/neg/smul` at 440–464, `analyticAt_cuspFunction_zero` (101), `hasSum_qExpansion` (189), `qExpansion_coeff_zero` (173), `qExpansion_coeff_eq_circleIntegral/intervalIntegral` (279/294)) are genuine mathlib lemmas, not restatements. The 15 custom `QExpSimp.*` members are *closure* lemmas (`AnalyticAt (cuspFunction h (f*g)) 0` from the factors, `Periodic ((f*g) ∘ ofComplex)`, `MDiff (f*g)`, `IsBoundedAtImInfty (f*g)` …) that mathlib does not provide in one step — each is a 1-line `simpa` gluing a mathlib congruence lemma to a mathlib closure lemma. A named custom simp set is the correct mechanism for a side-condition-discharging DSL (tagging mathlib's default `simp` set is impossible from downstream and would be wrong anyway, since these are conditional lemmas keyed to goal shapes). **Upstream candidate**: the `analyticAt_cuspFunction_mul/add/sub/neg/smul` quintet is generic enough for `Mathlib/NumberTheory/ModularForms/QExpansion.lean`.

**`decide +kernel` (30 decls, LevelThree) and `native_decide`/`ofReduceBool` (Qj elaborators) — flagged, by design** — LevelThree's docstring promise ("no native-code proof oracle") is honoured: all 30 numeric certificates use `decide +kernel` (kernel reduction only, no extra axioms). Qj's `mkNativeDecideProofFor` goes through `Lean.Meta.Native.nativeEqTrue`, so every term built by `qexp_coeff`/`foo`/`deltaFoo` depends on the `Lean.ofReduceBool` / `Lean.trustCompiler` axioms; anything downstream of `link.lean`'s `qj_qxp_coeff_link` chain that consumed such terms would inherit them. LevelThree avoids this by re-certifying the 13 needed `qjCoeffInt` values with `decide +kernel` (`qjCoeffInt_eq_tableThree`). Consistent; no change, but keep the two layers separated as they are.

**Frobenius/`ZMod` leads — all verified present and correctly used**: `ZMod.pow_card` (FieldTheory/Finite/Basic.lean:583), `ZMod.pow_card_pow` (587), `ZMod.frobenius_zmod` (593), `MvPowerSeries.map_frobenius_expand` (MvPowerSeries/Expand.lean:232), `MvPowerSeries.map_iterateFrobenius_expand` (247), `PowerSeries.expand` + `coeff_expand`/`coeff_expand_mul`/`coeff_expand_of_not_dvd`/`order_expand` (PowerSeries/Expand.lean), `zpow_eq_zpow_emod'` (Algebra/Group/Basic.lean:858), `Polynomial.Bivariate.swap` (+ `swap_X/swap_Y/swap_C`, Bivariate.lean:248ff), `HahnSeries.single_pow`, `HahnSeries.coeff_single_mul`, `LaurentSeries.coeff_coe_powerSeries`, `LaurentSeries.single_order_mul_powerSeriesPart`, `HahnSeries.ofPowerSeries_C/X_pow`. The only genuinely missing single-variable convenience is `PowerSeries.map_frobenius_expand` (see the unification item above).

**`primeCoxMatrixEquiv` machinery (Kronecker.lean:32–146) — KEEP** — enumeration of Cox representatives at prime level is project-specific combinatorics; `Fin.lastCases`/`Equiv.ofBijective` is the right mathlib toolkit and is used correctly.

**Minor style note (not API)**: DiagonalLaurent.lean has a duplicated copyright header (lines 1–10).
