# Step 4 — Mathlib-API audit: q-expansion analytic core

Files audited: `LaurentQExpansion/LaurentQExpansion.lean`, `LaurentQExpansion/Algebra.lean`,
`IntegralPowerSeries/IntegralPowerSeries.lean`, `IntegralPowerSeries/HasIntegralQExpansion.lean`,
`jFunction/{jfunction, Deltaqexpansions, jLevelN, qexp_coeffs, jInvariantLink}.lean`.

Every mathlib name cited below was verified to exist by grep over
`.lake/packages/mathlib/Mathlib/` (file:line noted where useful).

---

## A. Definitions to Replace with Mathlib

1. **`powerSeriesMapAlgHom` → replace by `PowerSeries.mapAlgHom (Algebra.ofId R A)`** —
   Current: hand-bundled `PowerSeries.map (algebraMap R A)` as an `→ₐ[R]` with a coefficientwise
   `commutes'` proof (IntegralPowerSeries.lean:5–11).
   Mathlib alternative: `PowerSeries.mapAlgHom : (A →ₐ[R] B) → PowerSeries A →ₐ[R] PowerSeries B`
   (Mathlib/RingTheory/PowerSeries/Basic.lean:728) applied to `Algebra.ofId R A : R →ₐ[R] A`;
   `PowerSeries.mapAlgHom_apply` gives the `map` unfolding.
   Impact: deletes the def + `commutes'` proof; every downstream lemma
   (`powerSeriesMapSubalgebra`, `coeToComplexPowerSeries.ringHom`, injectivity) becomes a direct
   application of mathlib's `AlgHom.range` / `AlgHom.toRingHom` API.
   **Action**: `def powerSeriesMapAlgHom R A := PowerSeries.mapAlgHom (Algebra.ofId R A)` (or
   inline it away entirely). Difficulty: easy.

2. **`analyticAt_hasFPowerSeriesAt_taylor` (private, Algebra.lean:353) → DELETE, use
   `AnalyticAt.hasFPowerSeriesAt`** —
   Current: 10-line proof that an analytic F is represented by
   `ofScalars ℂ (fun n ↦ (n!)⁻¹ * iteratedDeriv n F 0)`.
   Mathlib alternative: `AnalyticAt.hasFPowerSeriesAt`
   (Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:339) is *exactly* this statement, with
   coefficients `iteratedDeriv n f x / n!` (same term up to `div_eq_inv_mul`). Also available:
   `AnalyticOn.hasFPowerSeriesOnSubball` / `AnalyticOn.hasFPowerSeriesOnBall`
   (IteratedDeriv/ConvergenceOnBall.lean) for the on-ball version.
   Impact: removes a duplicated general fact; `analyticTaylor_comp_pow` shrinks accordingly.
   **Action**: replace uses with `hF.hasFPowerSeriesAt` + `div_eq_inv_mul` rewriting.
   Difficulty: easy.

3. **`natCast_mul_im_pos_aux` + ad-hoc `⟨N·z, proof⟩` terms (jLevelN.lean) → use
   `UpperHalfPlane.posRealAction`** —
   Current: private lemma `0 < im z → 0 < im (N·z)` used 8×, and `jN N τ := j ⟨N·τ, …⟩` built with
   explicit subtype constructors.
   Mathlib alternative: `UpperHalfPlane.posRealAction : MulAction {x : ℝ // 0 < x} ℍ`
   (Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean:197) with simp lemmas
   `coe_pos_real_smul`, `pos_real_im`, `pos_real_re`, plus `pos_real_smul_injective`.
   Impact: `jN N = j (⟨(N:ℝ), pos⟩ • ·)` gets the `MulAction` API (associativity of scaling,
   simp-normal im/re) for free; kills the aux lemma and the repeated `UpperHalfPlane.ext` glue in
   `natCast_mul_ofComplex_coe_aux` / `natCast_smul_gamma0_comm_aux`.
   **Action**: refactor `jN`/`qjN` through `posRealAction`. Difficulty: medium (touches most of
   jLevelN.lean, but mechanically).

4. **`coeToComplexPowerSeries.ringHom` → `(PowerSeries.mapAlgHom (Algebra.ofId R ℂ)).toRingHom`,
   and fix the bogus dot-name** —
   Current: abbrev named `coeToComplexPowerSeries.ringHom` declared *outside* any namespace, so it
   creates a phantom root namespace `coeToComplexPowerSeries`.
   Impact: naming hygiene + rides on finding A1.
   **Action**: rename to e.g. `powerSeriesMapRingHom` (or drop: for `R = ℤ` it is literally
   `PowerSeries.map (Int.castRingHom ℂ)`, and `PowerSeries.map_C`/`map_pow`/`map_sub` then apply
   directly without unfolding an abbrev). Difficulty: easy.

## B. API Choice Improvements

5. **`UpperHalfPlane.poleOrder` → redefine without the `if`, as
   `(-(meromorphicOrderAt (cuspFunction h f) 0).untopD 0).toNat`** —
   Current: if-then-else on `meromorphicOrderAt … < 0` extracting `Int.natAbs ∘ untopD 0`
   (LaurentQExpansion.lean:209–212). The project's own theorem `order` (line 666) proves the two
   forms equal in 20 lines.
   Verified: mathlib has NO `poleOrder` (zero grep hits), so a project def is justified; but the
   `toNat`-of-negated-order form makes `order` a `rfl`, and removes the repeated
   "`if`-condition must have held" case splits inside `poleOrder_nat_mul` (37 lines),
   `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero` (16 lines), and `analyticAt_iff`.
   Impact: −50 lines of `WithTop ℤ` bookkeeping across 4 proofs.
   **Action**: change the def body; keep the name/signature. Difficulty: medium.

6. **`to_qExpansion_coeff_zero_ne` (40 lines) → drive through `meromorphicTrailingCoeffAt`** —
   Current: hand-computes `meromorphicOrderAt (q^M·cusp f) = 0` via `meromorphicOrderAt_mul`,
   `meromorphicOrderAt_pow`, then `AnalyticAt.analyticOrderAt_eq_zero`.
   Mathlib alternative: `Mathlib/Analysis/Meromorphic/TrailingCoefficient.lean` —
   `meromorphicTrailingCoeffAt`, `MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero` (line 143),
   `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt` (line 116: the trailing coefficient is
   the limit of `z^{-order} • f`), `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero`.
   The statement "`(to_qExpansion h f).coeff 0 = meromorphicTrailingCoeffAt (cuspFunction h f) 0`"
   is a natural bridging lemma; nonvanishing then IS `meromorphicTrailingCoeffAt_ne_zero`, and the
   file gains the whole trailing-coefficient algebra (`_mul`, `_smul`, `_add_eq_left_of_lt`) for
   future leading-coefficient arguments (e.g. monicity of modular polynomials downstream).
   **Action**: add the bridge lemma, derive `to_qExpansion_coeff_zero_ne` from it. Difficulty:
   medium.

7. **`qExpansion_coeff_eq_circleIntegral_of_differentiableOn` — keep, but note mathlib's
   `UpperHalfPlane.qExpansion_coeff_eq_circleIntegral`** —
   Mathlib (NumberTheory/ModularForms/QExpansion.lean:279) has the same conclusion under
   `Periodic`+`MDiff`+`IsBoundedAtImInfty` hypotheses; the project version assumes
   `DifferentiableOn ℂ (cuspFunction h g) (closedBall 0 R)` instead, which is what is available
   for `poleRemoved` (whose ℍ-side regularity is never established). Both wrap
   `DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul`. Verified: hypotheses genuinely
   differ, so the project lemma is NOT redundant — but it is a good mathlib-PR candidate as the
   more primitive form (mathlib's own proof reproves it inline).
   **Action**: none locally; consider upstreaming. Difficulty: n/a.

8. **jfunction "value at q = 0" cluster → use `UpperHalfPlane.valueAtInfty` /
   `cuspFunction_apply_zero`** —
   Current: `cuspFunction_deltaOverQ_zero_aux`, `cuspFunction_qOverDelta_zero_aux`,
   `cuspFunction_deltaShiftedQSeries_zero_aux`, and the 23-line
   `integralDeltaOverQ_constantCoeff_isUnit_aux` each redo the composition
   `Tendsto f atImInfty (𝓝 a)` → `Periodic.invQParam_tendsto` → `Tendsto.limUnder_eq` by hand.
   Mathlib alternative: `UpperHalfPlane.valueAtInfty f := limUnder atImInfty f` (QExpansion.lean:61)
   with `UpperHalfPlane.cuspFunction_apply_zero : cuspFunction h f 0 = valueAtInfty f` (line 107,
   needs analyticity + periodicity) and `UpperHalfPlane.qParam_tendsto_atImInfty` (line 67).
   For the raw-limit direction a single project helper
   `cuspFunction_zero_eq_of_tendsto : Tendsto f atImInfty (𝓝 a) → cuspFunction h f 0 = a`
   (3 lines via `Periodic.cuspFunction_zero_eq_limUnder_nhds_ne`, `Periodic.invQParam_tendsto`,
   `Tendsto.limUnder_eq`) replaces 4 near-identical proofs.
   **Action**: add the helper, rewrite the four aux lemmas. Difficulty: easy.

9. **`HasIntegralQExpansion` — design mismatch CONFIRMED; align multiplier with the period** —
   Verified in source (HasIntegralQExpansion.lean:6–7): the multiplier is
   `cexp (2π i z) ^ n = 𝕢 1 z ^ n` while the expansion is `qExpansion h (…)` for a *general* `h`;
   the two agree only at `h = 1`, and for `h ≠ 1` the multiplied function is not even the
   pole-cancelled one. Moreover the whole predicate is subsumed by the (later-written)
   LaurentQExpansion layer: "some q-power multiple has integral expansion" is equivalent to
   "`laurentqExpansion h f` has all coefficients in ℤ" (cf. `j_laurentQExpansion_isIntegral`,
   proved without ever using `HasIntegralQExpansion`). The sorried `HasIntegralQExpansion.sum`
   would be immediate from `laurentqExpansion_add` + `HahnSeries.add_coeff` in that formulation.
   **Action**: either (a) change the multiplier to `𝕢 h z ^ n` (`Periodic.qParam`), or better
   (b) redefine `HasIntegralQExpansion h f := ∀ n, ∃ m : ℤ, (laurentqExpansion h f).coeff n = m`
   and derive the old form at `h = 1`; then `sum` follows from `laurentqExpansion_add`.
   Difficulty: medium (5 small downstream uses: `Delta/E4/E6/j_hasIntegralQExpansion`).

10. **`IsIntegralPowerSeries` / `HasCoeffsIn` / `powerSeriesMapSubalgebra` — design verified
    sound; simplify the abbrev tower** —
    Verified: mathlib has NO power-series analogue of `Polynomial.lifts`
    (Mathlib/Algebra/Polynomial/Lifts.lean:60 — polynomials only; `PowerSeries/Restricted.lean` is
    about norm-restricted series, unrelated). The `AlgHom.range`-membership design is the right
    mathlib idiom. But the project stacks four names for one predicate:
    `HasCoeffsIn ℤ ℂ = IsIntegralCPowerSeries = IsRIntegralCPowerSeries ℤ = IsIntegralPowerSeries`.
    Impact: search/`simp` friction, four coefficientwise-iff lemmas restating each other
    (`hasCoeffsIn_iff_coeff`, `isRIntegralCPowerSeries_iff_coeff`, `int_iff`,
    `mem_powerSeriesMapSubmodule_iff_coeff`).
    **Action**: keep `HasCoeffsIn` (general) and `IsIntegralPowerSeries` (ℤ,ℂ endpoint); delete
    the two middle abbrevs and one of the iff-restatements. `powerSeriesMapAlgHom_injective` can
    also be packaged as `AlgEquiv.ofInjective` if an equiv is ever wanted. Difficulty: easy.

11. **`hasCoeffsIn_zero/one/add/mul/smul/neg/sub` → drop; use `Subalgebra` membership API
    directly** — each is a one-line wrapper around `Subalgebra.zero_mem`/`add_mem`/… and half of
    them are unused (per inventory). Membership `hf : HasCoeffsIn R A f` already elaborates as
    subalgebra membership, so call sites can write `add_mem hx hy` etc.
    **Action**: delete the unused ones (`one`, `mul`, `neg`, `sub`, `C_algebraMap`), keep at most
    `zero/add/smul` if the `modularFormQExpansionSubmodule` construction reads better with them.
    Difficulty: easy.

## C. Hand-Rolled Patterns to Replace

12. **The 4× "`F 0 = limUnder`" calc block inside `analyticAt_cuspFunction_poleRemoved`
    (132-line proof) — CONFIRMED; extract one helper** —
    Verified in source (four occurrences of
    `F 0 = limUnder (nhdsWithin 0 {0}ᶜ) F := Periodic.cuspFunction_zero_eq_limUnder_nhds_ne …`
    followed by a `Tendsto.limUnder_eq`). The uniform statement is:
    `(hFg : cuspFunction h f =ᶠ[𝓝[≠] 0] g) (hg : Tendsto g (𝓝[≠] 0) (𝓝 a)) →
     cuspFunction h f 0 = a`, provable once from
    `Periodic.cuspFunction_zero_eq_limUnder_nhds_ne` + `Filter.limUnder_congr`(or
    `Tendsto.limUnder_eq` after `Tendsto.congr'`). With it, each branch of the case analysis
    becomes ~3 lines, and the final glue can keep using
    `eventuallyEq_nhds_of_eventuallyEq_nhdsNE` (verified: Mathlib/Topology/NhdsWithin.lean) or
    `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE` (used by mathlib's own
    `hasFPowerSeriesOnBall_cuspFunction`, QExpansion.lean:260).
    Also: the entire `h ≤ 0` branch verbatim-duplicates `analyticAt_cuspFunction_of_not_pos`
    (declared 20 lines later!) — reorder and apply it.
    **Action**: add helper, deduplicate `h ≤ 0` branch; expect 132 → ~60 lines. Difficulty: medium.

13. **`meromorphicOrderAt_cuspFunction_nat_mul`: duplicated `analyticOrderAt (·^m) 0 = m`
    sub-proof** — the block computing the analytic order of `q ↦ q^m` (via `analyticOrderAt_pow`,
    `analyticOrderAt_id`, both verified in Mathlib/Analysis/Analytic/Order.lean:455/186) appears
    twice verbatim inside one proof. Extract as a `have` or a private lemma
    `analyticOrderAt_pow_id : analyticOrderAt (· ^ m : ℂ → ℂ) 0 = m`.
    **Action**: factor out. Difficulty: easy.

14. **`laurentqExpansion_coeff_eq_circleIntegral` (151 lines): repeated zpow/sphere bookkeeping** —
    the two `EqOn`-on-sphere calc blocks re-derive `z ≠ 0` and `‖z‖ < 1` on `sphere 0 R` and
    shuffle `z^a * z^b = z^(a+b)` by hand. A tiny private lemma
    `(hz : z ∈ Metric.sphere (0:ℂ) R) (hR : 0 < R) (hR' : R < 1) : z ≠ 0 ∧ ‖z‖ < 1` plus
    systematic use of `zpow_add₀`/`zpow_sub₀` in one direction would halve the proof. No mathlib
    replacement for the full statement exists (verified: mathlib has no analytic-Laurent-expansion
    API at all — `Mathlib/Analysis/Meromorphic/` has order/trailing-coefficient/normal-form but no
    coefficient-series; `RingTheory/LaurentSeries.lean` is purely algebraic). This theorem is a
    strong mathlib candidate.
    **Action**: local cleanup only. Difficulty: easy–medium.

15. **`deltaShiftedQSeries` analyticity chain (jfunction.lean:125–213, ~70 lines) → the
    `differentiableOn_cuspFunction_ball` route used for `qj`** —
    Current: hand-builds `HasFPowerSeriesOnBall` from `ofScalars` + summability.
    Alternative: `deltaShiftedQSeries = deltaOverQ = q⁻¹·Δ` is 1-periodic, `MDiff` (quotient of
    MDiff by nonvanishing entire factor — same argument as `qj_differentiableAt_of_im_pos`), and
    bounded at i∞ (`Delta_boundedfactor` gives Tendsto → `BoundedAtFilter`); then mathlib's
    `UpperHalfPlane.analyticAt_cuspFunction_zero` (QExpansion.lean:101) yields
    `deltaOverQ_analyticAt_aux` directly, and `hasFPowerSeriesOnBall_cuspFunction`
    (QExpansion.lean:260, PUBLIC) converts the existing HasSum into the coefficient
    identification now done by `deltaShiftedQSeries_qExpansion_coeff`. REFUTED as a pure deletion:
    the `HasSum` lemmas are still needed for `deltaShiftedQSeries_qExpansion_coeff`; but the
    bespoke radius/`Function.update` argument in `deltaShiftedQSeries_analyticAt_aux` can be
    replaced by these two mathlib lemmas.
    **Action**: optional refactor. Difficulty: medium.

16. **`qExpansion_qpow_mul` / `qExpansion_qParam_pow` / `analyticAt_cuspFunction_const`
    (Algebra.lean): `cuspFunction h 1 = 1` re-proved inline 3×** — mathlib proves the same
    identity inline in `UpperHalfPlane.qExpansion_one` (QExpansion.lean:515). Extract
    `cuspFunction_const : cuspFunction h (fun _ ↦ a) = fun _ ↦ a` once (the project's private
    `analyticAt_cuspFunction_const` already contains the proof) and reuse; also a candidate for a
    small mathlib PR next to `UpperHalfPlane.qExpansion_one`.
    **Action**: share the sub-proof. Difficulty: easy.

17. **`Deltaqexpansions.coeff_mul_dvd_aux` — general-purpose, extract or upstream** —
    "`a ∣ every coeff f`, `b ∣ every coeff g` ⇒ `a*b ∣ every coeff (f*g)`" is modular-forms-free.
    Mathlib has no direct match (checked `PowerSeries/CoeffMulMem.lean`, which is the ideal-flavoured
    cousin: coefficients in ideals `I`, `J` ⇒ product coefficients in `I*J` — worth checking as a
    replacement: membership in `Ideal.span {a}` IS divisibility, so
    `PowerSeries.coeff_mul_mem_ideal_mul` -style lemmas there may already close it).
    **Action**: try the `CoeffMulMem` route; else move the lemma to IntegralPowerSeries.lean.
    Difficulty: easy.

## D. Missing tags / instances

18. **`modularFormModuleofIsScalarTower` — diamond risk CONFIRMED; do not leave as a global
    unrestricted instance** —
    Mathlib (NumberTheory/ModularForms/Basic.lean) already provides
    `instSMulℝ : SMul α (ModularForm Γ k)` for `[SMul α ℝ] [SMul α ℂ] [IsScalarTower α ℝ ℂ]`,
    `instSMulℂ : SMul α (ModularForm Γ k)` for `[SMul α ℂ] [IsScalarTower α ℂ ℂ] [Γ.HasDetOne]`,
    but Module instances ONLY for ℝ (line 324) and ℂ (line 327). The project's
    `instance … (R) [Semiring R] [Module R ℂ] [IsScalarTower R ℂ ℂ] : Module R (ModularForm Γ k)`
    therefore *overlaps* mathlib's `Module ℝ`/`Module ℂ` instances at `R = ℝ, ℂ` (two competing
    Module instances; the ℝ ones go through *different* SMul instances — `instSMulℝ` vs
    `instSMulℂ` — so defeq is at best fragile), and at `R = ℕ, ℤ` it competes with
    `AddCommMonoid.toNatModule` / `AddCommGroup.toIntModule`, whose `SMul` (nsmul/zsmul
    iteration) is NOT defeq to `instSMulℂ`'s structure-map smul. That is a genuine
    non-defeq diamond.
    **Action**: (a) restrict availability — make it `local instance`/`scoped instance` or take it
    out of instance search (`def` + `letI` at the three use sites `qExpansion_smul_algebra`,
    `modularFormQExpansionSubmodule`, `modularFormQExpansionLinearMap`); or (b) upstream properly
    to mathlib next to `instSMulℂ` with the priority/defeq analysis done there.
    Difficulty: easy locally, medium to upstream.

19. **Missing `@[simp]` on the coefficient normal forms** — good simp candidates (all
    unconditional equations with LHS in "project normal form"):
    `laurentqExpansion.coeff_neg_poleOrder_add`, `laurentqExpansion.coeff_of_qExpansion`
    (the complete if-then-else description), `j_poleOrder`, `j_poleRemoved`, `j_to_qExpansion`,
    `deltaShiftedQSeries_qExpansion_coeff`, and the numeric endpoints in qexp_coeffs.lean
    (`qjCoeffs_zero…four`, `j_laurentQExpansion_coeff_*`) — the last group in the same spirit as
    mathlib's simp-tagged special values. jInvariantLink.lean already tags its two bridges.
    **Action**: add tags after checking loops (`coeff_of_qExpansion` vs the two directional
    lemmas: pick one form). Difficulty: easy.

20. **Naming: root-namespace pollution CONFIRMED** —
    verified in source: `lemma analyticAt_iff` (LaurentQExpansion.lean:457) and `theorem order`
    (line 666) are ROOT-namespace with maximally generic names — `order` in particular will
    ambiguate against dozens of mathlib `order` declarations at `open`-time. Additionally all
    `laurentqExpansion.*` coefficient lemmas (lines 526–731) are declared with a *literal dotted
    name* outside any namespace, creating a phantom root namespace `laurentqExpansion` distinct
    from `UpperHalfPlane.laurentqExpansion` — so dot-notation on a `laurentqExpansion h f` term
    does NOT find them.
    **Action**: wrap the file's lemma section in `namespace UpperHalfPlane`; rename
    `analyticAt_iff → analyticAt_cuspFunction_iff_poleOrder_eq_zero`,
    `order → poleOrder_eq_toNat_neg_meromorphicOrderAt`. Difficulty: easy (plus downstream
    renames in qexp_coeffs.lean / jfunction.lean).

## E. Verified no-change (checked; project version justified)

21. **`meromorphicAt_of_comp_pow` — NOT in mathlib (lead REFUTED in the other direction)** —
    searched `Mathlib/Analysis/Meromorphic/*` (no `of_comp`/descent lemmas), leansearch ("if f∘z^n
    meromorphic then f meromorphic" returns only `MeromorphicAt.pow/zpow`), and the `comp` API
    (`MeromorphicAt.comp_analyticAt`, `MeromorphicAt.meromorphicOrderAt_comp` — both one-way).
    The building blocks used (`Complex.isOpenQuotientMap_pow` [Analysis/Complex/OpenMapping.lean],
    `analyticAt_comp_iff_of_deriv_ne_zero` [Calculus/InverseFunctionTheorem/Analytic.lean:40],
    `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
    [Complex/RemovableSingularity.lean]) all exist and are the right tools. Verdict: keep;
    **prime mathlib-PR candidate** (together with its aux lemma), as is `analyticTaylor_comp_pow`
    (= "Taylor series of G∘(·^m) is `PowerSeries.expand m` of Taylor series of G";
    `PowerSeries.expand` + `coeff_expand_mul` + `coeff_expand_of_not_dvd` verified in
    Mathlib/RingTheory/PowerSeries/Expand.lean, no analytic counterpart in mathlib).

22. **`poleOrder`/`poleRemoved`/`to_qExpansion`/`laurentqExpansion` layering — sound** —
    mathlib's cusp API (`UpperHalfPlane.cuspFunction`, `qExpansion`, `qExpansion_mul/add/smul`,
    `hasSum_qExpansion`, `qExpansionFormalMultilinearSeries(_radius)`) stops at *analytic*-at-cusp
    functions; there is no meromorphic-at-cusp/Laurent layer anywhere in mathlib (verified:
    `Analysis` has no analytic Laurent expansion; `RingTheory/LaurentSeries.lean` is algebraic).
    Defining the Laurent expansion as `single(−M) 1 * ofPowerSeries (qExpansion h (q^M f))` on top
    of `meromorphicOrderAt` is the correct layering; `poleOrder` is *not* redundant with
    `meromorphicOrderAt` (it is its ℕ-truncation, needed as a `pow` exponent), though its body
    should be the closed formula (finding 5).

23. **Private `cuspFunction_{add,mul,const}_eventuallyEq` + `meromorphicAt_cuspFunction_*` —
    justified** — mathlib's `UpperHalfPlane.cuspFunction_add/mul/sub/neg/smul`
    (QExpansion.lean:429–465) all require `ContinuousAt (cuspFunction …) 0`, which is exactly what
    a meromorphic (pole-bearing) cusp function lacks; the project's punctured-neighbourhood
    versions + `MeromorphicAt.congr` are the correct generalization. Candidate for upstreaming
    next to the mathlib lemmas rather than replacement.

24. **jfunction integrality chain (`deltaOverQ` → unit → `qOverDelta` → `qj`)** — uses the right
    mathlib API throughout: `PowerSeries.isUnit_iff_constantCoeff`, `qExpansion_mul`,
    `hasSum_qExpansion`, `hasSum_nat_add_iff'`, `EisensteinSeries.E_qExpansion_coeff(_zero)`
    (verified EisensteinSeries/QExpansion.lean:324/348), `ModularForm.qExpansion_pow`
    (QExpansion.lean:603). No better mathlib route exists for `Δ/1728`-integrality
    (`IsIntegralPowerSeriesmod` has no mathlib counterpart). Minor nits only: dead
    `Delta_qExpansion_coeff_zero_aux` (Deltaqexpansions) re-proved inline in jfunction.lean; the
    `IsIntegralPowerSeriesmod` hypothesis would read better as `c ∣ coeff` than `ModEq c _ 0`.

25. **jInvariantLink.lean — model use of mathlib API** — `WeierstrassCurve.IsShortNF`,
    `c₄/c₆/Δ_of_isShortNF`, `isElliptic_iff`, `WeierstrassCurve.j`: nothing to change.

26. **Duplicates to delete (exact restatements, found during audit)**:
    `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` (= `…_of_ne_zero`, same statement & hyps);
    `cuspFunction_to_analyticAt_analyticAt` (= `analyticAt_cuspFunction_poleRemoved`);
    `cuspFunction_to_analyticAt_meromorphicAt` (one-liner, garbled name — inline it);
    `laurentqExpansion.coeff_neg_poleOrder` (= `coeff_neg_poleOrder_add _ _ 0` — keep only if
    simp-tagged as the n=0 normal form).
