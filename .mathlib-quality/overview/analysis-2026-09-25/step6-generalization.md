# Step 6 — Generalization Analysis (project-wide, 2026-09-25)

Scope: every module under `XYin/` (83 inventories in `.mathlib-quality/overview/inventory-2026-09-25/`,
including `PhD/Modularforms/` and `PhD/ModularFunctions/`, which the July 2026 pass excluded).
Method: (1) re-verified all 24 July findings + 4 July refutations against CURRENT source (Sep 21
cleanup moved most line numbers); (2) for every candidate opened the proof and listed the lemmas it
invokes to deduce the minimal typeclass; (3) grep-checked the pinned mathlib
(`.lake/packages/mathlib`, rev 2abc242) for a general version; (4) WebSearch for the literature
generality of the mathematically substantive items; (5) two scratch compiles (budget 4) verifying the
two highest-count claims:

* `scratchpad/Step6LPE.lean` — the four `[Field K]` lemmas of `LaurentPolynomialEvaluation.lean`
  compile **verbatim** with `[CommSemiring K] [NoZeroDivisors K]` (first three) and
  `[CommRing K] [IsDomain K]` (injectivity), and a bundled `LaurentSeries R →+* LaurentSeries S`
  builds from `[Semiring R] [Semiring S]` alone. Compiled clean.
* `scratchpad/Step6NF.lean` — `MeromorphicNFAt.analyticAt_of_eventually_norm_le` for `f : 𝕜 → E`,
  `ne_zero_of_tendsto_ne_zero` for any `[l.NeBot]`/`[T2Space E]`, and `tsum_pNat` with only
  `[AddCommMonoid α] [TopologicalSpace α]`. Compiled clean.

Difficulty scale: **Low** = binder/typeclass change with the proof unchanged (or a ≤ 5-line
rewrite); **Medium** = some proof rework or a new small API; **High** = restructuring.
"Upstream-first" means the general statement has no project-specific content and should be
written once in mathlib form.

---

## Part I — July 2026 findings re-verified against current source

| July # | Declaration (CURRENT `file:line`) | July action | Status 2026-09-25 |
|---|---|---|---|
| A1 | `Matrix.exists_hnf_transform` `Cox/HermiteNormalForm.lean:123` (public wrapper `:173`) | 2×2/ℤ → n×n / Bézout | **STILL OPEN** — still `!![a,b;c,d]`, proof `:123–171` still `Int.gcd_eq_gcd_ab`/`Int.emod_*`. See G-24 for the corrected general form. |
| A2 | `matrix_mul_toMatrix_eq` `HermiteNormalForm.lean:227` | move above the rank-2 `variable` | **STILL OPEN** — still `private`, still under `variable {bM : Basis (Fin 2) ℤ M}` (`:225`); proof is `linearMap_toMatrix_mul_basis_toMatrix` only. |
| A3 | `matrix_eq` `:241`, `bN_eq` `:281` | rank n | **STILL OPEN** (rank 2, `Int.le_of_dvd`, `reduced_eq_of_eq_add_mul`). |
| A3′ | `reduced_eq_of_eq_add_mul` `:232` | extract ℤ residue lemma | **STILL OPEN and now DUPLICATED**: byte-identical copy `reduced_eq_of_eq_add_mul_aux` at `Cox/CoxMatrices/Basic.lean:239`. |
| A4 | `rankTwoContent` `:44`, `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` `:303` | document D₁ vs D_{n−1} | **STILL OPEN** — no docstring warning; see G-24. |
| B1 | `meromorphicAt_of_comp_pow` `LaurentQExpansion/LaurentQExpansion.lean:194` (aux `:161`) | upstream, ℂ → Banach codomain | **STILL OPEN** (still `g : ℂ → ℂ`). |
| B2 | `poleOrder` `:236`, `poleRemoved` `:316`, `to_qExpansion` `:321`, `laurentqExpansion` `:326`, `analyticAt_cuspFunction_poleRemoved` `:374` | Laurent expansion of a meromorphic germ | **STILL OPEN**; the circle-integral subtree `:600–706` is now dead (Batch A). |
| B3 | `analyticOrderAt (·^m) 0 = m` | extract | **STILL OPEN** — but mathlib now supplies it directly: `analyticOrderAt_pow` (`Analysis/Analytic/Order.lean:455`) + `analyticOrderAt_id` (`:186`); the project already composes them at `Cox/CoxMatrices/LaurentExpansion.lean:151–157` and re-derives the same block inside `meromorphicOrderAt_cuspFunction_nat_mul` (`LaurentQExpansion.lean:275`). Action: one lemma, two call sites. Low. |
| B4 | `analyticTaylor_comp_pow` `LaurentQExpansion/Algebra.lean:328` (aux `:290`) | upstream expand bridge | **STILL OPEN** (private, ℂ). See G-19. |
| C1 | `powerSeriesMapAlgHom` `IntegralPowerSeries/IntegralPowerSeries.lean:33` | delete for `PowerSeries.mapAlgHom (Algebra.ofId R A)` | **DONE** (body is now exactly that); the wrapper def + `_apply` simp lemma `:39` could still become an `abbrev`. |
| C2 | `HasCoeffsIn` `:51` | → `PowerSeries.lifts` | **STILL OPEN**. See G-20. |
| C3 | `IsIntegralPowerSeriesmod` `:173` | lifts + regular `c` | **STILL OPEN**. See G-21. |
| D1 | `card_le_minpoly_natDegree_of_injective_roots` `Cox/ModularPolynomial/Irreducibility.lean:89`, `irreducible_of_card_conjugates` `:102` | extract + upstream | **STILL OPEN** (still `private`). See G-25 (sharper form). |
| E1 | `eval_derivative_prod_X_sub_C_at` `Interpolation.lean:291` | delete for Lagrange | **DONE (proof)**: body is now `simpa [Lagrange.nodal, eval_prod] using Lagrange.eval_nodal_derivative_eval_node_eq …`; the 9-line private wrapper remains (callers `:328`, `:417`). Inline it. |
| E2 | `eval_interpolation_sum_at` `:301` | `univ` → `Finset`, upstream | **STILL OPEN**. See G-10. |
| E3 | `polynomial_prod_coeff_mdifferentiable_aux` `Interpolation.lean:156` / `polynomial_prod_coeff_cuspMeromorphicAt` `AnalyticSupport.lean:61` | consolidate via subring | **STILL OPEN** (verbatim twins, same `Finset.induction_on`/`coeff_mul` skeleton `:163`/`:69`). See G-34. |
| F1 | jet soundness `Cox/LevelThree.lean:249–283` | window 37 → `N` | **STILL OPEN** (`n < 37` hard-coded in all three lemmas). |
| F2 | ℤ compute layer → `CommRing` | REFUTED | **Confirmed refuted** (unchanged design, `decide +kernel` at `LevelThree.lean:47–49`). |
| G1 | `card_filter_range_coprime_mul_aux` `Cox/CoxMatrices/Cardinality.lean:23` | upstream | **STILL OPEN** (proof now via `Nat.count_add'`, still private). |
| G2 | `coxDivisorSumAux` `:140` … `card_coxMatrix` `:270` | Dedekind ψ | **STILL OPEN**. See G-27/G-28. |
| H1 | SymmetricCubicLaurent `[Field K]` (26 sites `:111–369`) | → `IsDomain` | **STILL OPEN**; re-verified: the Laurent block `:144–232` invokes only `HahnSeries.order_pow/order_mul/leadingCoeff_mul/leadingCoeff_eq/coeff_eq_zero_of_lt_order/C_mul_eq_smul/coeff_add`, `pow_ne_zero` — no `⁻¹`/`div` anywhere in the file. See G-1. |
| H2 | `symmetric_bidegree_three_eq_zero_of_laurent_coeff` `:368` | bidegree n | **STILL OPEN**; Batch L confirms hard-coding (`:29–42`, `:142`, `:233–235`, `:263`, `:378–387`). See G-26. |
| I1 | `polynomial_eval₂_laurentSeries_*` `Cox/LaurentPolynomialEvaluation.lean:93/103/113/139` | `Field` → `IsDomain` | **STILL OPEN — scratch-VERIFIED** (`Step6LPE.lean`). See G-1. |
| I2 | `laurentSeriesMapRingHom` `:22` | Semiring/Γ, upstream `HahnSeries.mapRingHom` | **STILL OPEN — scratch-VERIFIED** Semiring bundling; mathlib still has only unbundled `HahnSeries.map` (`RingTheory/HahnSeries/Basic.lean:143`). See G-35. |
| J1 | uniqueness.lean beyond ℂ | REFUTED | **Confirmed refuted** — `eqOn_weierstrassP` `XYin/uniqueness.lean:237` uses `countable_of_Lindelof_of_discrete`, `isConnected_compl_of_one_lt_rank` (`rank ℝ ℂ = 2`, `:245`), `eqOn_of_preconnected_of_eventuallyEq`; `weierstrassP_eventuallyEq` `:228` uses `HasFPowerSeriesAt` over ℂ; `lattice_le_of_eqOn` `:256` uses `meromorphicOrderAt`; mathlib `PeriodPair` is ℂ-only. Literature agrees the theorem lives over ℂ ([MathWorld, Weierstrass elliptic function](https://mathworld.wolfram.com/WeierstrassEllipticFunction.html); [DLMF §23.3](https://dlmf.nist.gov/23.3)). |
| J2 | `iteratedDeriv_sq_mul` `uniqueness.lean:140` | ℂ → 𝕜 | **STILL OPEN**. See G-11. |
| K1/K2 | `CoxMatrix` hypotheses; `primeLowerCoxMatrix` `Cox/Kronecker.lean:32` | no action | unchanged; K2 refutation confirmed (|C(m)| = ψ(m) ≠ m+1 for composite m). |
| K3 | width/expand Laurent constructions `Kronecker.lean:160,184,300,572`; `KroneckerFrobenius.lean:104`; `LaurentExpansion.lean:50` | `LaurentSeries.expand` / `embDomain` | **STILL OPEN**. See G-18 (the same `embDomainRingHom` packaging serves all six sites). |

Tally of July items: **2 DONE** (C1, E1-proof), **22 STILL OPEN**, **4 refutations confirmed**.

---

## Part II — Generalization Opportunities (project-wide)

### II.A Typeclass / binder weakenings (Low unless stated)

#### G-1. `[Field K]` → `[CommRing K] [IsDomain K]` (and defs → `Semiring`) across the Laurent layer
- **Current**: `Cox/LaurentPolynomialEvaluation.lean:94,104,114,140` (`[Field K]`);
  `Cox/DiagonalLaurent.lean:57,66,81`; `Cox/SymmetricCubicLaurent.lean` 26 sites `:111–369`
  (defs `bivariateLaurentEvalHom :111`, `symmetricBivariateMonomial :136`, `cubicCoeff :237`,
  `cubicBasis :241` also carry `[Field K]`); `Cox/FormalCoxProduct.lean:24,29,39,107,134`;
  root cause `transformedJSeries` `Cox/CoxMatrices/LaurentExpansion.lean:50` (`ζ ^ (e : ℤ)` = `zpow`).
- **Proof-usage evidence**: LPE `:93–149` invokes `HahnSeries.order_pow` (`Multiplication.lean:1034`,
  `[Semiring R] [NoZeroDivisors R]`), `leadingCoeff_mul` (`:573`, `[NoZeroDivisors R]`),
  `leadingCoeff_one` (`:99`, `MulZeroOneClass`), `C_mul_eq_smul` (`:848`, `Semiring`),
  `coeff_eq_zero_of_lt_order`/`leadingCoeff_eq` (`Basic.lean:394/416`), `Polynomial.eval₂_eq_sum_range`,
  `Polynomial.leadingCoeff_eq_zero`, `injective_iff_map_eq_zero` (needs `Ring`). SCL `:144–232`: same list
  plus `pow_ne_zero`, `HahnSeries.coeff_add`. DiagonalLaurent `:56–85` additionally use `zpow_ne_zero`
  (`GroupWithZero`) because of the `zpow` in `transformedJSeries`. **Scratch-verified** (`Step6LPE.lean`):
  LPE `:93/103/113` compile under `[CommSemiring K] [NoZeroDivisors K]`, `:139` under `[CommRing K] [IsDomain K]`.
- **Literature**: the "lowest-term" injectivity of `P ↦ P(J)` is the standard proof that `j` is
  transcendental and needs only an integral domain of coefficients; Kronecker.lean wants it over `ZMod p`
  (a field only because `p` is prime) and over ℤ.
- **Mathlib**: all cited HahnSeries lemmas are already stated at `NoZeroDivisors`/`Semiring` level (paths above).
- **Action**: (i) LPE and SCL: replace `[Field K]` by `[CommRing K] [IsDomain K]` (defs: `Semiring K`);
  (ii) DiagonalLaurent `:57/66/81` and FormalCoxProduct `:24/29/39`: `[DivisionRing K]` suffices as long as
  `transformedJSeries` keeps `zpow`; (iii) to reach `CommRing` (and let `Fact (Nat.Prime p)` go, G-3),
  re-express the phase as `Multiplicative ℤ →* Kˣ` or reduce the exponent mod `m` via `IsPrimitiveRoot`
  (Kronecker inventory's "phase-generalised transformedJSeries").
- **Impact**: ~35 binder edits, 0 proof edits for (i)–(ii); unlocks Kronecker over ℤ without casts.
- **Difficulty**: **Low** for (i)–(ii); **Medium** for (iii). In-project.

#### G-2. `[CharZero K]` unused — `Cox/FormalCoxProduct.lean:51, 75, 92`
- **Evidence**: `integralLaurentSeries :51` uses only `isIntegral_zero/one`, `IsIntegral.add/neg/mul/sum`
  (any `CommRing`); `transformedJSeries_mem_integralLaurentSeries :74` uses `isIntegral_algebraMap`,
  `IsIntegral.of_pow`, `hζ.zpow_eq_one` (no characteristic); `formalCoxPolynomial_coeff_integral :91`
  works in `Polynomial (integralLaurentSeries K)`. The genuinely char-0 lemmas (`:144/:164`) take
  `[Algebra ℚ K] [IsCyclotomicExtension …]` and *derive* `CharZero` at `:169–170`.
- **Action**: delete the three `[CharZero K]` binders. **Low**.

#### G-3. `[Fact (Nat.Prime p)]` — `Cox/KroneckerFrobenius.lean:26–37, 77–96, 104–139` and `Cox/Kronecker.lean:263, 389, 426, 445`
- **Evidence (CORRECTS the Batch L digest)**: `jUnitLaurentSeriesMod_eq_unitJPowerSeries` `KF:77` and
  `jUnitLaurentSeriesMod_order` `Kronecker:263` (only `(Fact.out).one_lt` at `:266`) are genuinely
  prime-free: `jUnitLaurentSeriesMod p` (`Kronecker:244`) and `unitJPowerSeries K [Ring K]` (`KF:66`)
  are defined for every `p : ℕ+`. **But** `KF:26` and `KF:104` mention `transformedJSeries (1 : ZMod p) …`,
  and `transformedJSeries` demands `[Field K]`; `ZMod p` is a field only through `ZMod.instField [Fact p.Prime]`.
  So there the instance is consumed by the *statement*, not the proof, and cannot be dropped until G-1(iii).
  `KF:142` (`ZMod.pow_card_pow`), `Kronecker:282` (`MvPowerSeries.map_frobenius_expand`, `ZMod.pow_card`),
  `:460`, `KF:190` (`sub_pow_char`) genuinely need primality.
- **Action**: drop `Fact` at `KF:77` and `Kronecker:263` now (replace by `(hp : 1 < p)` as
  `jLaurentSeriesMod_order :339` already does); drop at `KF:26/104` and `Kronecker:389/426/445` after G-1(iii). **Low**.

#### G-4. `tsum_pNat` — `PhD/Modularforms/Summability/Basic.lean:54`
- **Evidence**: proof is `PNat.coe_injective.tsum_eq` (`Function.Injective.tprod_eq`,
  `Topology/Algebra/InfiniteSum/Basic.lean:525`, context `[CommMonoid α] [TopologicalSpace α]` `:38`) —
  the `UniformSpace/IsUniformAddGroup/T2Space/CompleteSpace` binders are dead. **Scratch-verified**.
  Sibling `sum_int_even :95` needs `CommRing` only for `nsmul_eq_mul`; state with `2 • _`.
- **Action**: `[AddCommMonoid α] [TopologicalSpace α]`. **Low**. (File is 100 % wrapper-grade per Batch F; deletion supersedes.)

#### G-5. `ne_zero_of_tendsto_ne_zero` — `PhD/Modularforms/AtImInfty.lean:25`
- **Evidence**: `tendsto_nhds_unique` (`Topology/Separation/Hausdorff.lean:179`, `[T2Space X] [NeBot l]`) +
  `tendsto_const_nhds`. **Scratch-verified** for `f : α → E`, `{l : Filter α} [l.NeBot]`, `[T2Space E] [Zero E]`.
- **Mathlib**: no analogue by name (searched `ne_zero_of_tendsto`, `Tendsto.ne_zero` in `Topology/`).
- **Action**: restate generally (or inline at the 0 external callers). **Low**.

#### G-6. `pos_nat_div_upper` — `PhD/Modularforms/upperhalfplane.lean:15`
- **Evidence**: proof uses `Int.cast_pos`, `z.im_pos`, `z.normSq_pos`, `Complex.div_im` — any real `r > 0`.
- **Mathlib**: `UpperHalfPlane.im_pnat_div_pos (n : ℕ) [NeZero n]` (`Analysis/Complex/UpperHalfPlane/Basic.lean:180`) is itself the ℕ special case; `pnat_div_upper :13` is a pure rename of it (Batch G).
- **Action**: delete both; if kept, `(r : ℝ) (hr : 0 < r)`. A real-`r` `im_div_pos` would be a 2-line mathlib generalisation. **Low**.

#### G-7. `diagonal_coeff_one` — `Cox/Arithmetic.lean:239`
- **Evidence**: `Polynomial.induction_on'`, `eval_add`, `coeff_add`, `eval_monomial`, `coeff_mul_X_pow'`,
  `coeff_monomial`, `ring` — no subtraction. `BivariatePolynomial.diagonal` is `[CommSemiring R]`
  (`Cox/ModularPolynomial/Construction.lean:53`).
- **Action**: `[CommSemiring R]`, move to Construction's `diagonal_*` API, make public. **Low**.

#### G-8. `eq_or_eq_neg_of_associated_int_bivariate` — `Cox/Arithmetic.lean:164`
- **Evidence**: `Polynomial.isUnit_iff` twice (`Algebra/Polynomial/Degree/Units.lean:48`) + `Int.isUnit_iff`.
- **Mathlib**: `Int.associated_iff : Associated a b ↔ a = b ∨ a = -b` (`Algebra/GCDMonoid/Nat.lean:168`) is
  scalar-only; no `Polynomial.associated_iff_eq_or_eq_neg` (searched `associated_iff_eq_or_eq_neg`,
  `eq_or_eq_neg_of_associated` in `Mathlib/`).
- **Action**: one-variable lemma `Polynomial.eq_or_eq_neg_of_associated {R} [CommRing R] [IsDomain R]
  (hR : ∀ u : Rˣ, (u : R) = 1 ∨ (u : R) = -1) {P Q : R[X]} : Associated P Q → Q = P ∨ Q = -P`, applied
  twice for `R[X][Y]`; upstream-worthy next to `Int.associated_iff`. **Low**.

#### G-9. `exists_commonDenominator_polynomialEval_of_natDegree_lt` — `Cox/ModularPolynomial/Interpolation.lean:351`
- **Evidence**: `eq_div_iff`, `field_simp`, `Polynomial.eval_eq_sum_range'`, `evalEval_*`,
  `Finset.mul_prod_erase`, `Finset.prod_ne_zero_iff` — any `[Field K]`, any index type `X` for `ℍ`.
  Blocker: `RationalIn` (`Cox/ModularFunction/CuspData.lean:48`) is stated for `ℍ → ℂ` but uses nothing of ℍ/ℂ.
- **Mathlib**: no "common denominator for a polynomial with rational-function coefficients" lemma (searched `Lagrange.lean`, `RatFunc`).
- **Action**: generalise `RationalIn`/`RationalInTwo` to `(f g : X → K)` and this lemma with them. **Low**.

#### G-10. `eval_interpolation_sum_at` — `Interpolation.lean:301` (July E2)
- **Evidence**: `Finset.sum_eq_single i`, `Finset.prod_eq_zero (… (sub_self _))` — no injectivity of `r`;
  `Finset.univ` → any `s` with `i ∈ s`.
- **Mathlib**: `Lagrange.nodal` is `[CommRing R]` (`LinearAlgebra/Lagrange.lean:531–543`) but
  `Lagrange.interpolate` is `[Field F]` with normalised basis (`:290–299`); the un-normalised node-evaluation
  identity is absent.
- **Action**: restate as `(∑ k ∈ s, C (a k) * nodal (s.erase k) r).eval (r i) = a i * ∏ l ∈ s.erase i, (r i - r l)`; upstream next to `eval_nodal_derivative_eval_node_eq` (`:605`). **Low**.

#### G-11. `iteratedDeriv_sq_mul` — `XYin/uniqueness.lean:140` (July J2)
- **Evidence**: `iteratedDeriv_fun_mul` (`Analysis/Calculus/IteratedDeriv/Lemmas.lean:417`, `to_fun` of the
  smul version; file variables `:23–30` are `{𝕜} [NontriviallyNormedField 𝕜] {F} [NormedAddCommGroup F] [NormedSpace 𝕜 F]`),
  `iteratedDeriv_fun_pow_zero` (`:429`), `Nat.cast_choose_two`; only `hg.contDiffAt` is used from analyticity.
- **Action**: `{𝕜} [NontriviallyNormedField 𝕜] (g : 𝕜 → 𝕜) (hg : ContDiffAt 𝕜 n g 0)`; upstream beside `iteratedDeriv_fun_pow_zero`. **Low**.

#### G-12. `MeromorphicNFAt.analyticAt_of_eventually_norm_le` — `PhD/ModularFunctions/NormalFormGrowth.lean:21`
- **Evidence**: `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt` (`Analysis/Meromorphic/NormalForm.lean:114`),
  `tendsto_cobounded_of_meromorphicOrderAt_neg` (`Order.lean:149`), `tendsto_norm_atTop_iff_cobounded` — all
  `f : 𝕜 → E`. **Scratch-verified** for `[NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]` (no completeness).
- **Mathlib**: no "locally bounded normal-form ⇒ analytic" lemma (only the iff `tendsto_cobounded_iff_meromorphicOrderAt_neg` `Order.lean:211`).
- **Action**: restate for `𝕜 → E`, upstream to `NormalForm.lean`. **Low**, upstream-first.

#### G-13. `meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq` — `Cox/ModularFunction.lean:96`
- **Evidence**: `meromorphicOrderAt_eq_int_iff` (`Order.lean:94`, `f : 𝕜 → E`),
  `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE` (`TrailingCoefficient.lean:90`),
  `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`, `meromorphicOrderAt_mul` (`Order.lean:429`, scalar) —
  replace by `meromorphicOrderAt_smul` (`:407`, `{f : 𝕜 → 𝕜} {g : 𝕜 → E}`), `meromorphicOrderAt_zpow_id_sub_const`;
  the `simp [… mul_sub]` at `:121` becomes `smul_sub`.
- **Action**: `{f g : 𝕜 → E}`; upstream (`TrailingCoefficient.lean`). **Low**, upstream-first.

#### G-14. `exists_analyticAt_pow_succ_mul_of_meromorphicAt_of_analyticAt_zero` — `Cox/ModularFunction.lean:294`
- **Evidence**: `MeromorphicAt` unfolds to `∃ n, AnalyticAt 𝕜 (fun z ↦ (z - x) ^ n • F z) x`;
  `sub_smul_dslope_of_zero` (`Analysis/Calculus/Dslope.lean:145`, `{f : 𝕜 → E}`),
  `HasFPowerSeriesAt.has_fpower_series_dslope_fslope` (`Analytic/IsolatedZeros.lean:78`).
- **Action**: `{F : 𝕜 → E} {J : 𝕜 → 𝕜}`; upstream. **Low**, upstream-first.

#### G-15. NormalFormSlash lemmas — `PhD/ModularFunctions/NormalFormSlash.lean:22, 54`
- **Evidence**: `comp_analyticAt_of_deriv_ne_zero :22` uses `meromorphicNFAt_iff_analyticAt_or`
  (`NormalForm.lean:53`, `E`-valued) and `meromorphicOrderAt_comp_of_deriv_ne_zero` (`Order.lean:806ff`,
  `{f : 𝕜 → E} {g : 𝕜 → 𝕜}`) → holds for `f : 𝕜 → E`. `meromorphicNFOn_slash_zero_of_pos :54` extends to
  weight `k` because `denom g τ ^ (-k)` is analytic and nonvanishing on ℍ and
  `meromorphicNFAt_mul_iff_left` (`NormalForm.lean:257`) applies. `AnalyticAt.conj_conj :32`/`MeromorphicNFAt.conj_conj :39` are genuinely ℂ (complex conjugation) — correct as stated.
- **Action**: `:22` → `𝕜 → E` (upstream); `:54` → weight `k` (in-project, unlocks "meromorphic modular forms of weight k"). **Low**.

#### G-16. `IsOfExponentialGrowth` and `.slash` — `PhD/ModularFunctions/CuspGrowth.lean:26`, `GrowthAtCusp.lean:23`
- **Current**: `∃ ρ ≥ 0, IsBoundedAtImInfty (fun τ ↦ exp (-ρ τ.im) * f τ)`; `.slash` at weight `0` only.
- **Evidence**: `IsBoundedAtImInfty` is `f =O[atImInfty] 1` (`FunctionsBoundedAtInfty.lean:46`), so the
  API-rich form `∃ ρ ≥ 0, f =O[atImInfty] fun τ ↦ (exp (ρ τ.im) : ℂ)` is definitionally close and gives
  `.add/.mul/.smul/.const` as `IsBigO.add/mul/const_mul_left` one-liners (Batch D scratch-checked the shape).
  `.slash` proof `:22–42` already computes `(g • τ).im = a τ.im` for upper-triangular `g`; the weight-`k`
  factor `denom g τ ^ (-k) = (g 1 1)^(-k)` is constant — exactly how mathlib's `IsBoundedAtImInfty.slash (hg : g 1 0 = 0) : IsBoundedAtImInfty (f ∣[k] g)` (`NumberTheory/ModularForms/BoundedAtCusp.lean:35`) is stated.
- **Action**: (i) IsBigO form + `.add/.mul/.neg/.smul/.of_isBoundedAtImInfty`; (ii) `.slash` for all `k : ℤ`; codomain `E` is also free. Weight 0 elsewhere in the folder is a design choice, not a proof limitation. **Low**.

#### G-17. Deltaqexpansions / Eisenstein / multipliable_lems micro-binders
- `coeff_mul_dvd_aux`, `coeff_pow_dvd_aux` (`PhD/jFunction/Deltaqexpansions.lean:159,166`): only `PowerSeries.coeff_mul`,
  `Finset.dvd_sum`, `mul_dvd_mul` → any `CommSemiring`; no `PowerSeries` analogue of `Polynomial.C_dvd_iff_dvd_coeff` in mathlib. **Low**.
- `exists_smul_eq_of_rank_one(')` (`PhD/Modularforms/Eisenstein.lean:34,41`): `finrank_eq_one_iff_of_nonzero'` is `[DivisionRing K]`-general. **Low**.
- `hasProd_le_nonneg`/`HasProd.le_one_nonneg` (`multipliable_lems.lean:74,78`): `Finset.prod_le_prod` + `le_of_tendsto_of_tendsto'` → `OrderedCommSemiring` + `OrderClosedTopology`, any `ι`. Genuine gap (mathlib's need `IsOrderedMonoid`, unavailable for ℝ). **Low**, upstream.

### II.B Repackagings that change the shape (Medium)

#### G-18. `laurentqExpansion_nat_mul_coeff` / `_of_not_dvd` as `HahnSeries.embDomain` — `LaurentQExpansion/Algebra.lean:384, 419` (+ July K3)
- **Evidence**: both proofs are `Int.toNat` bookkeeping around `PowerSeries.coeff_expand_mul/_of_not_dvd`
  (`RingTheory/PowerSeries/Expand.lean:87/97`) after `to_qExpansion_nat_mul` + `poleOrder_nat_mul`.
- **Mathlib**: `HahnSeries.embDomainRingHom (f : Γ →+ Γ') (hfi : Injective f) (hf : ∀ g g', f g ≤ f g' ↔ g ≤ g')`
  (`HahnSeries/Multiplication.lean:899`), `embDomain_coeff` (`Basic.lean:449`), `embDomain_notin_range` (`:477`).
  With `f = zmultiplesHom ℤ m` (m > 0) this is exactly "substitute q ↦ qᵐ".
- **Action**: one lemma `laurentqExpansion (m * h) f = embDomainRingHom (zmultiplesHom ℤ m) _ _ (laurentqExpansion h f)`;
  both coefficient lemmas become `embDomain_coeff`/`embDomain_notin_range`. The same packaging retires the four
  anonymous `⟨fun k ↦ if m ∣ k ∧ … , isPWO⟩` constructions at `Kronecker.lean:160,184,300,572`, the
  `single (-N) 1 * ↑(expand N _)` normal form at `KroneckerFrobenius.lean:104` and `transformedJSeries`
  (`LaurentExpansion.lean:50`) up to a phase. **Low–Medium**; ~60 lines saved.

#### G-19. `analyticTaylor_comp_pow` as a pure `PowerSeries.expand` statement — `Algebra.lean:290–339` (July B4)
- **Evidence**: the only ℂ input is `Complex.hasSum_taylorSeries_on_ball` (`Analysis/Complex/TaylorSeries.lean:45`);
  the reindexing along `n ↦ m·n` uses `PowerSeries.coeff_expand_mul`, `Injective.hasSum_iff`.
- **General form**: `HasFPowerSeriesAt G p 0 → HasFPowerSeriesAt (G ∘ (· ^ m)) (ofScalars (fun n ↦ (expand m (mk p.coeff)).coeff n)) 0`
  over any `𝕜`, proved from `HasFPowerSeriesAt.hasSum` + `FormalMultilinearSeries.apply_eq_pow_smul_coeff`
  (`Analysis/Calculus/FormalMultilinearSeries.lean:328`) instead of the Taylor theorem; then
  `analyticTaylor_comp_pow` is `HasFPowerSeriesAt.eq_formalMultilinearSeries`. Note `PowerSeries.expand`
  is stated for `[CommRing R]` (`Expand.lean:28`).
- **Mathlib**: nothing linking `HasFPowerSeriesAt` and `PowerSeries.expand` (searched `Expand.lean`, `Analytic/`).
- **Action**: upstream as `HasFPowerSeriesAt.comp_pow_expand`; project keeps the cusp instance. **Medium**.

#### G-20. `HasCoeffsIn` → `PowerSeries.lifts`; three coefficientwise subrings → one `HahnSeries.coeffMem` — `IntegralPowerSeries.lean:51`, `FormalCoxProduct.lean:51`, `IntegralDescent.lean:72` (July C2)
- **Evidence**: `hasCoeffsIn_iff_coeff :56` is the `PowerSeries` twin of `Polynomial.lifts_iff_coeff_lifts`
  (`Algebra/Polynomial/Lifts.lean:72`); `integralLaurentSeries` and `integerCoeffLaurentSeries` are the same
  `{F | ∀ k, F.coeff k ∈ S}` subring for `S = integralClosure ℤ K` resp. `(Int.castRingHom ℂ).range`, proved by
  `HahnSeries.coeff_mul` + `Subring.sum_mem`.
- **Mathlib**: `Polynomial.lifts (f : R →+* S) : Subsemiring S[X]` (`Lifts.lean:60`), `liftsRing` (`:209`);
  **no** `PowerSeries.lifts` and **no** coefficient-membership subring for `HahnSeries` (grep `lifts` in
  `RingTheory/PowerSeries/`, `coeff.*Subring` in `RingTheory/HahnSeries/` → none).
- **Action**: `PowerSeries.lifts (f : R →+* S) : Subsemiring S⟦X⟧` (+ `liftsRing`, `lifts_iff_coeff_lifts`)
  and `HahnSeries.coeffMemSubring (S : Subring R) : Subring R⟦Γ⟧` for any `[Ring R]`, ordered `Γ`; keep the
  ℤ→ℂ abbrevs as instances. **Medium**, upstream-first; deletes ~70 project lines and the private/duplicate subrings.

#### G-21. `IsIntegralPowerSeriesmod` — `IntegralPowerSeries.lean:173` (July C3)
- **Evidence**: `Int.modEq_zero_iff_dvd`, `coeTo_of_toIntegralPowerSeries`, `simp [… hc]` (cancellation in ℂ).
- **General form**: `[CommRing R] [Field A] [Algebra R A] {c : R} (hc : algebraMap R A c ≠ 0) (hf : HasCoeffsIn R A f)
  (hdvd : ∀ n, c ∣ (lift hf).coeff n) : HasCoeffsIn R A ((algebraMap R A c)⁻¹ • f)`.
- **Action**: restate after G-20; rename `_mod`. **Low–Medium**.

#### G-22. `CyclicSublattice` and `map` are ℂ-free — `Cox/CyclicSublattice.lean:24–157`
- **Evidence**: `structure CyclicSublattice (L : PeriodPair) (m : ℕ+)` `:24` stores a `Submodule ℤ L.lattice`,
  its index and `IsAddCyclic` of the quotient; `ext :35`; `carrier_finrank :43` uses
  `AddSubgroup.finrank_eq_of_finiteIndex` (`GroupTheory/IndexNSmul.lean:73`, needs `Module.Finite ℤ M`,
  `IsTorsionFree ℤ M`) + `finrank = 2`; `hermiteNormalForm :55` uses `L.latticeBasis` only; `mapCarrier/_index/mapQuotientEquiv/map :133–157`
  use `Submodule.map`, `AddSubgroup.index_map_equiv` (`GroupTheory/Index.lean:334`), `Submodule.Quotient.equiv`
  (`LinearAlgebra/Quotient/Basic.lean:325`), `isAddCyclic_of_surjective`. ℂ first appears at `hnfPeriod :60`/`toPeriodPair :107`.
  Likewise `dualLinearMap_injective :336` (only `IsTorsionFree ℤ`) and `dual_index_eq/dual_cyclic :453/479`
  (adjugate of the HNF matrix; ℂ only enters `:495`, `:527`).
- **Mathlib**: no "finite-index submodule with cyclic quotient" structure; building blocks present.
- **Action**: split into `CyclicSubmodule (M : Type*) [AddCommGroup M] [Module.Finite ℤ M] [IsTorsionFree ℤ M] (bM : Basis (Fin 2) ℤ M) (m : ℕ+)`
  (carrier, index, cyclic, HNF, map, dual) + a thin `PeriodPair` layer (`toPeriodPair`, `j`). **Medium** (restructure, proofs unchanged).

#### G-23. `Classification.lean:28–175` never uses ℂ
- **Evidence**: `toCoxMatrix :28` reads `S.hermiteNormalForm` fields; `inclusionLinearMap :94` = `Matrix.toLin L.latticeBasis L.latticeBasis σ.inclusionMatrix`;
  `inclusionLinearMap_injective :98` uses `LinearMap.det_toMatrix`, `inclusionMatrix_det` (needs `IsDomain ℤ` only);
  `sublatticeOfPeriodPair :113`, `inclusionHermiteNormalForm :117`, `toCyclicSublatticeOfPeriodPair :133`, round trips `:147/:156`,
  `cyclicSublatticeEquivCoxMatrixOfPeriodPair :169` — only `L.latticeBasis : Basis (Fin 2) ℤ L.lattice` is consumed.
  ℂ/ℍ enter at `CoxMatrix.sublattice :178` onward.
- **Literature**: index-`n` sublattices of ℤ² ↔ HNF matrices `(a b; 0 d)`, `ad = n`, `0 ≤ b < d` (σ(n) of them);
  primitive/cyclic ones (`gcd(a,b,d)=1`) counted by ψ(n) — [OEIS A001615](https://oeis.org/A001615); Cox Lemma 11.24.
- **Action**: state `cyclicSubmoduleEquivCoxMatrix (bM : Basis (Fin 2) ℤ M) (m) : CyclicSubmodule bM m ≃ CoxMatrix m`
  after G-22; the PeriodPair version is `bM := L.latticeBasis`. **Medium** (depends on G-22).

#### G-24. Rank-2 HNF → rank-n / Bézout, with the CORRECT cyclic criterion — `Cox/HermiteNormalForm.lean:34, 44, 123, 241, 303` (July A1/A3/A4)
- **Evidence**: `exists_hnf_transform :123–171` uses Bézout (`Int.gcd_eq_gcd_ab`), exact division, Euclidean
  remainders (`Int.emod_*`) and sign normalisation (`exists_unit_mul_pos_aux :97`); `matrix_eq :241` uses
  `Int.le_of_dvd` + the residue lemma `:232`; `quotient_isAddCyclic_iff_… :303` uses Smith normal form
  (`Submodule.smithNormalFormBotBasis`, `FreeModule/PID.lean:612`), content invariance under unimodular
  multiplication (`rankTwoContent_dvd_mul_left/right :67/76`, GCD-domain facts) and `Nat.coprime_iff_gcd_eq_one`.
- **Literature**: HNF exists over any PID (indeed Bézout domain); uniqueness needs a chosen residue system and
  associate representatives — [Wikipedia, Hermite normal form](https://en.wikipedia.org/wiki/Hermite_normal_form);
  [Hermite/Smith canonical forms over a PID (ACM SIGSAM)](https://dl.acm.org/doi/10.1145/101104.101105);
  [Damer, Computing the HNF: a survey (2024)](https://eprint.iacr.org/2024/2089.pdf). For the cyclic criterion:
  with invariant factors `d₁ ∣ … ∣ dₙ`, `d₁⋯d_k = D_k(A)` = gcd of the `k×k` minors
  ([Wikipedia, Smith normal form](https://en.wikipedia.org/wiki/Smith_normal_form); [Stanley, SNF in combinatorics](https://math.mit.edu/~rstan/papers/snf_survey.pdf)),
  so `M/N ≅ ⊕ ℤ/dᵢ` is cyclic ⟺ `d₁ = … = d_{n−1} = 1` ⟺ **`D_{n−1}(A) = 1`**. `rankTwoContent = D₁` coincides with
  `D_{n−1}` only at `n = 2`; the naive rank-`n` statement "gcd of entries = 1 ⇒ cyclic" is **false** for `n ≥ 3`
  (`diag(1,2,2)`: content 1, quotient `ℤ/2 × ℤ/2`).
- **Mathlib**: no HNF (grep `Hermite` in `LinearAlgebra/`, `Data/Matrix/`, `RingTheory/` → only Hermite polynomials);
  no matrix content / determinantal divisors; `Matrix.BlockTriangular` (`LinearAlgebra/Matrix/Block.lean:61`) and
  `det_of_upperTriangular` (`:324`) express the triangular part; `IsBezout` (`RingTheory/PrincipalIdealDomain.lean:65`) exists.
- **Action**: (i) now: docstring on `rankTwoContent` naming it `D₁ = D_{n−1}` and stating the general criterion;
  extract `reduced_eq_of_eq_add_mul` once (also deletes `CoxMatrices/Basic.lean:239`); move `matrix_mul_toMatrix_eq :227`
  above the rank-2 `variable` (July A2). (ii) upstream path: `Matrix.IsColumnHermiteNormalForm` over ℤ for `Fin n`
  (already `{ι} [Preorder ι]`), existence by induction on columns over an `EuclideanDomain` with a residue choice, and
  `Matrix.detDivisor k A` over a `GCDMonoid`. **Low** for (i); **High** for (ii); upstream-first for (ii).

#### G-25. Conjugate-counting lemmas — `Cox/ModularPolynomial/Irreducibility.lean:89, 102` (July D1, sharpened)
- **Evidence**: `card_le_minpoly_natDegree_of_injective_roots :89` is `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`
  (`Algebra/Polynomial/Roots.lean:713`, `[CommRing R] [IsDomain R]`) applied to `(minpoly F α).map (algebraMap F E)`;
  nothing about `minpoly`/`IsIntegral` is used beyond `Monic.natDegree_map` and `ne_zero`, so the honest statement is
  `∀ p ≠ 0, (∀ i, aeval (c i) p = 0) → Injective c → card ι ≤ p.natDegree`. `irreducible_of_card_conjugates :102` then
  reads `p = minpoly F α` from `Polynomial.eq_of_monic_of_dvd_of_natDegree_le` — the stronger conclusion `p = minpoly F α` should be exposed.
- **Literature**: "as many distinct conjugates as the degree ⇒ irreducible / equals the minimal polynomial"
  ([Aitken, Minimal, primitive and irreducible polynomials](https://public.csusm.edu/aitken_html/Essays/Algebra/polynomials2021.pdf);
  [Macauley, Polynomials and irreducibility](https://www.math.clemson.edu/~macaule/classes/m20_math4120/slides/math4120_lecture-6-03_h.pdf)).
- **Mathlib**: no `minpoly.eq_of_card_roots_le_natDegree`-style criterion (searched `FieldTheory/Minpoly/`).
- **Action**: de-`private`, drop `IsIntegral` from the first, conclude `p = minpoly F α` in the second, `Fintype ι` → `Finset`; PR to `FieldTheory/Minpoly/`. **Low**, upstream-first.

#### G-26. `symmetric_bidegree_three_eq_zero_of_laurent_coeff` → bidegree ≤ n with injective weight — `Cox/SymmetricCubicLaurent.lean:368` (July H2)
- **Current**: bidegree ≤ 3, orders `(−9, −3)`, ten literal exponents; NOT parametrised — hard-coded in
  `symmetricCubicExpansion :29–42` (16 explicit monomials), `cubicWeight = 9i + 3j :142`, `cubicI/cubicJ : Fin 10 → ℕ :233–235`,
  `cubicWeight_strictMono :263` (`fin_cases`), and the ten-conjunct hypothesis `:378–387`.
- **What a generic version needs** (only the kernel `:285–342` — `symmetricCubicLaurentExpansionFin_coeff_eq`,
  `cubicCoeff_eq_zero_of_laurent_coeff` — is already generic in `(ι, LinearOrder ι, basis, StrictMono weight)`):
  (i) index set the triangle `T_n = {(i,j) | j ≤ i ≤ n}` as a `Finset (ℕ × ℕ)` and the expansion lemma
  "symmetric `P` of bidegree ≤ n = Σ_{T_n} c_{ij} S_{ij}" (`eq_symmetricCubicExpansion :88` generalised);
  (ii) weights `w(i,j) = a·i + b·j` with `T.order = −a`, `J.order = −b` and `a > b` so that `TⁱJʲ + TʲJⁱ` has leading exponent `−w(i,j)`
  (the mirror inequality `9j + 3i < 9i + 3j` at `:215–216`);
  (iii) an explicit hypothesis that `w` is injective on `T_n` (a decidable arithmetic condition; at level 3 it holds only because
  `j ≤ i` excludes the collision `9·1 = 3·3`, so it is NOT `b·n < a`); the sorted enumeration becomes `Finset.sort` /
  `Finset.orderEmbOfFin` instead of `![…]` + `fin_cases`. Level 3 then follows by `decide`.
- **Literature**: this is the classical computation of `Φ_m` by comparing q-expansion coefficients of a symmetric polynomial of
  known bidegree ψ(m) — [Baginski–Fuchs, Explicit formulas for the modular equation](https://www.math.ucdavis.edu/~efuchs/ModEquation.pdf);
  [Sutherland, Computing the modular equation](https://math.mit.edu/~drew/MomoseSeminar.pdf); Kaltofen–Yui (1984) for `Φ₁₁`; Cox §11 (11.22).
- **Mathlib**: nothing comparable.
- **Action**: restructure as above; this is what levels 5/7 need. **High** (in-project).

#### G-27. `coxDivisorSumAux` IS the Dedekind ψ function — `Cox/CoxMatrices/Cardinality.lean:113–243` (July G2)
- **Evidence**: `coxDivisorSumAux n = ∑_{d ∣ n} (d / gcd(n/d, d)) · φ(gcd(n/d, d))` `:140`; multiplicativity `:143`, prime-power value `p^e + p^{e−1}` `:186`,
  `ArithmeticFunction` packaging `:205`, `IsMultiplicative` `:211`, factorisation product `:219`, ℚ Euler product `:243`; the Cox-specific input is only the
  fibration `card_coxMatrix_eq_divisorSum_aux :102`.
- **Literature**: `|C(m)| = [SL₂(ℤ):Γ₀(m)] = ψ(m) = m ∏_{p∣m}(1 + 1/p)`, ψ = number of primitive index-`m` sublattices —
  [Wikipedia, Dedekind psi function](https://en.wikipedia.org/wiki/Dedekind_psi_function); [OEIS A001615](https://oeis.org/A001615).
- **Mathlib**: no Dedekind ψ (grep `dedekind|psi` in `NumberTheory/ArithmeticFunction/` → none); available: `ArithmeticFunction.pmul`
  (`Zeta.lean:104`), `μ`, `id`, `IsMultiplicative.mul/pmul`, `multiplicative_factorization`.
- **Action**: `def ArithmeticFunction.dedekindPsi : ArithmeticFunction ℕ := pmul μ μ * id` (i.e. `μ² ∗ id`), `isMultiplicative_dedekindPsi`,
  `dedekindPsi_apply_prime_pow`, `dedekindPsi_eq_factorization_prod`, ℚ Euler-product form; then the six private lemmas collapse to instances.
  **Medium**, upstream-first.

#### G-28. `card_coxMatrix` ℕ-valued — `Cardinality.lean:270`
- **Evidence**: `card_coxMatrix_eq_divisorSum_aux :102` + `coxDivisorSum_eq_factorizationProd_aux :219` already give the ℕ identity; the ℚ cast at `:270` is a presentation choice; `card_coxMatrix` is unused project-wide (`_public-unused-candidates.tsv`).
- **Action**: `Fintype.card (CoxMatrix m) = dedekindPsi m` (ℕ), keep the ℚ Euler product as a corollary. **Low** (given G-27).

#### G-29. `dim_gen_cong_levels` (sorry) — `PhD/Modularforms/DimensionFormulas.lean:198`
- **Current**: `(Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) : FiniteDimensional ℂ (ModularForm Γ k)`.
- **Standard hypothesis**: Γ of finite index in SL₂(ℤ) (not necessarily congruence): Sturm's bound holds for every finite-index
  Γ with `m = [SL₂(ℤ) : ±Γ]` — [Brunault, Sturm bounds for general congruence subgroups](https://perso.ens-lyon.fr/francois.brunault/recherche/Sturm-bound-general.pdf);
  finite dimensionality via valence/Riemann–Roch for arithmetic subgroups ([Sage: arithmetic subgroups](https://doc.sagemath.org/html/en/reference/arithgroup/sage/modular/arithgroup/arithgroup_generic.html)); Diamond–Shurman §3.5 for the congruence case.
- **Mathlib**: `[Γ.FiniteIndex]` is the typeclass (`isArithmetic_iff_finiteIndex`, `ArithmeticSubgroups.lean:93`; instance `:100`),
  with instances for `Γ(N)`, `Γ₀(N)`, `Γ₁(N)` (`CongruenceSubgroups.lean:86/206/209`); `FiniteDimensional ℂ (ModularForm 𝒮ℒ k)` only at level one
  (`LevelOne/DimensionFormula.lean:273`), `sturm_bound_levelOne` (`:306`), `ModularForm.norm` (`NormTrace.lean:107`, needs `[𝒢.IsFiniteRelIndex ℋ]`, weight `k * Nat.card 𝒬`).
- **Action**: restate as `[Γ.FiniteIndex]` (typeclass, so the norm/trace instances fire); proof route: `ModularForm.norm` to level one
  → `sturm_bound_levelOne` → Sturm bound for Γ → injection into truncated coefficient vectors. **Low** to restate, **High** to prove (mathlib gap).

#### G-30. `PrimitiveQuadraticEquation` / `IsImaginaryQuadratic` vs `minpoly ℚ τ` — `Cox/SingularModuli.lean:25, 38`
- **Current**: explicit primitive integral `(A, B, C)` with `Aτ² + Bτ + C = 0`, `B² − 4AC < 0`.
- **Evidence**: the structure is *consumed* as data by `fixingMatrix :50` (`!![n, −C; A, n + B]`), so it must stay; but `IsImaginaryQuadratic` as a
  *predicate* is equivalent to `(minpoly ℚ (τ : ℂ)).natDegree = 2` (τ ∉ ℝ forces negative discriminant; clearing denominators and dividing by the content gives a primitive equation).
- **Literature**: singular moduli are algebraic integers for every imaginary-quadratic τ — Cox Thm 11.1;
  [Zagier, Traces of singular moduli](https://people.mpim-bonn.mpg.de/zagier/files/tex/TracesSingModuli/fulltext.pdf); [Vanderbilt CM lecture notes](https://math.vanderbilt.edu/rolenl/ModularFormsLecture28.pdf).
- **Mathlib**: no `IsImaginaryQuadratic`; `IsQuadraticExtension R S` (`LinearAlgebra/Dimension/StrongRankCondition.lean:679`, `finrank = 2`) and `minpoly` API.
- **Action**: add `isImaginaryQuadratic_iff_natDegree_minpoly_eq_two` (⇔ `IsQuadraticExtension ℚ ℚ⟮(τ:ℂ)⟯`) so `singularModulus_isIntegral :233` can be stated for `minpoly`-quadratic τ; keep the structure. **Medium**.

#### G-31. Theorem 11.9(i) in field form — `Cox/ModularFunction.lean:431`, `Cox/ModularFunctionField.lean:126, 176`
- **Current**: `theorem_11_9_i (f : ModularFunction 𝒮ℒ) : RationalIn f j` (pointwise); `theorem_11_9_ii N : gamma0ModularFunctionField N = jLevelFunctionField N`.
- **Evidence**: with `levelJ 1 = j` the field form is `gamma0ModularFunctionField 1 = ⊥`, and it follows from `theorem_11_9_ii 1` plus
  `levelJFieldElement 1 ∈ ⊥` (`IntermediateField.adjoin_simple_eq_bot_iff`); the Γ(1)-vs-`Gamma0 1` mismatch is a coercion detail (Batch G/D).
- **Action**: add `gamma0ModularFunctionField_one : gamma0ModularFunctionField 1 = ⊥` as a corollary; the honest generalisation of 11.9(ii) itself is the two-line
  `adjoin F (range φ) = F⟮α⟯` given `range φ ⊆ F⟮α⟯` and `α ∈ range φ` (ModularFunctionField inventory). **Low–Medium**.

#### G-32. `toMeromorphicField_eq_div_of` — `Cox/ModularFunctionField.lean:56`
- **Evidence**: uses only `f.meromorphicOn`, `f.meromorphicNFOn`, `toFun_toMeromorphicField`, `MeromorphicField.toFun_injective`, `toFun_ofMeromorphic`,
  `holomorphicToMeromorphic_injective`, and a `Germ.coe_eq` computation — nothing about `Γ`; holds for any `x : MeromorphicField` with representative
  `MeromorphicField.toFun x`, and for `a b` merely meromorphic (same proof once `ofMeromorphic_mul`/`ofMeromorphic_eq_of_eventuallyEq` exist, which the MeromorphicField inventory lists as missing).
- **Action**: `MeromorphicField.eq_div_of_forall (x) (a b : HolomorphicFunction) (hb) (h : ∀ τ, b τ ≠ 0 → toFun x τ = a τ / b τ)`, then the meromorphic-`a b` version. **Medium**.

#### G-33. Right-coset translate API — `Cox/CoxMatrices/Basic.lean:615, 641, 671, 675, 682`
- **Evidence**: `rightCosetTranslate` uses only `hf.2.1` (Γ₀(m)-invariance) and `QuotientGroup.rightRel_apply`; `rightCosetMul`, `baseRightCoset`,
  `exists_rightCosetMul_baseRightCoset_eq`, `rightCosetTranslate_smul` use only group axioms — valid for any `H : Subgroup G` acting on any `X` and any `H`-invariant `f : X → Y`.
- **Mathlib**: `QuotientGroup.rightRel` (`GroupTheory/Coset/Defs.lean:106`) exists; no "translate an `H`-invariant function by a right coset" API.
- **Action**: `Subgroup.rightCosetTranslate (H) (hf : ∀ h ∈ H, f (h • x) = f x) : Quotient (rightRel H) → X → Y` + `MulAction G (Quotient (rightRel H))` by right multiplication; Cox instance with `G = SL(2,ℤ)`, `H = Γ₀(m)`. **Low–Medium**.

#### G-34. Coefficientwise closure twins — `AnalyticSupport.lean:61` / `Interpolation.lean:156` (July E3)
- **Evidence**: identical `Finset.induction_on` + `Polynomial.coeff_mul` + antidiagonal proofs for the predicates "cusp-meromorphic" and "MDifferentiable"; only closure under `0, 1, +, *` is used.
- **Mathlib**: `Polynomial.liftsRing (f : R →+* S) : Subring S[X]` (`Lifts.lean:209`) + `Subring.prod_mem` already express "a product of polynomials with coefficients in a subring has coefficients in it".
- **Action**: one lemma parametrised by `S : Subsemiring (ℍ → ℂ)` (or work in `Polynomial S`). **Low–Medium**.

#### G-35. `laurentSeriesMapRingHom` → `HahnSeries.mapRingHom` — `LaurentPolynomialEvaluation.lean:22` (July I2)
- **Evidence**: bundling uses `HahnSeries.map_zero/one/add/mul` (`Basic.lean:143`, `Addition.lean`, `Multiplication.lean:406`), all `NonUnitalNonAssocSemiring`-level; nothing uses ℤ. **Scratch-verified** for `[Semiring R] [Semiring S]` (`Step6LPE.lean`).
  `bivariateSpecializeLaurent :38` and `_map :61/81` only need `CommSemiring` (for `eval₂RingHom`).
- **Mathlib**: unbundled `HahnSeries.map` only; no `→+*` (grep `mapRingHom` in `RingTheory/HahnSeries/`, `LaurentSeries.lean` → none). `FormalCoxProduct.lean:42–46` rebuilds the same hom inline.
- **Action**: `HahnSeries.mapRingHom (f : R →+* S) : R⟦Γ⟧ →+* S⟦Γ⟧` for `[AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ] [NonAssocSemiring R] [NonAssocSemiring S]`; upstream. **Low**, upstream-first.

#### G-36. `meromorphicAt_of_comp_pow` codomain ℂ → Banach `E` — `LaurentQExpansion.lean:194` (July B1)
- **Evidence**: `Complex.isOpenQuotientMap_pow` (`Analysis/Complex/OpenMapping.lean:253`) is about the base; `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` (`RemovableSingularity.lean:36`) is stated for `f : ℂ → E`, `[CompleteSpace E]`; `analyticAt_comp_iff_of_deriv_ne_zero` is `E`-valued. Base field cannot move (see Refuted R-2).
- **Action**: `{g : ℂ → E}`, base point `z₀` via translation; upstream to `Analysis/Meromorphic/` (no `of_comp` there — grep empty). **Low–Medium**, upstream-first.

#### G-37. Laurent expansion of a meromorphic germ — `LaurentQExpansion.lean:236, 316, 321, 326, 374` (July B2)
- **Evidence**: all four definitions read `f` only through the germ `cuspFunction h f` at `0 ∈ ℂ`; `analyticAt_cuspFunction_poleRemoved :374–417` is
  "`z^{poleOrder} • g` is analytic" = `meromorphicOrderAt_eq_int_iff` (`Order.lean:94`) transported.
- **Literature**: Laurent expansion at a pole with `aₙ = (2πi)⁻¹∮ g(z) z^{−n−1} dz` — [Wikipedia, Laurent series](https://en.wikipedia.org/wiki/Laurent_series); [Siu, Cauchy's integral formula and Laurent series](https://people.math.harvard.edu/~siu/math113/5_cauchy_integral_formula_power_and_laurent_series_expansion.pdf); natural generality `g : ℂ → E`, `E` Banach.
- **Mathlib**: no `Analysis/` file imports `LaurentSeries`/`HahnSeries` (grep) — absent.
- **Action**: `MeromorphicAt.laurentExpansionAt (g : ℂ → ℂ) (z₀) : LaurentSeries ℂ` (pole order `(−order).toNat`, pole-removed `(· − z₀)^M • g`, series = shifted `HasFPowerSeriesAt` coefficients) with the coefficient lemmas, then `laurentqExpansion h f := laurentExpansionAt (cuspFunction h f) 0`. **High**, upstream-first (prime contribution).

#### G-38. Small upstream gaps discovered on the way (all Low)
- `HahnSeries` has no `CharP` instance (grep `CharP` in `RingTheory/HahnSeries/*`, `LaurentSeries.lean` → none); `KroneckerFrobenius.lean:195` builds it by `charP_of_injective_ringHom`. Upstream `HahnSeries.charP`.
- No `PowerSeries.map_frobenius_expand` (only `MvPolynomial.map_frobenius_expand`, `RingTheory/MvPolynomial/Expand.lean:25`, and the `MvPowerSeries` version that `Kronecker.lean:286` reaches via `@… Unit` + `change`). Upstream the `PowerSeries` corollary.
- `card_filter_range_coprime_mul_aux` (`Cardinality.lean:23`, July G1): `((range (k*g)).filter (g.Coprime ·)).card = k * φ g`; mathlib has only the one-block `Nat.filter_coprime_Ico_eq_totient` (`Data/Nat/Totient.lean:79`). Upstream; generalises to any `g`-periodic predicate.
- `Deltaqexpansions.lean:159/166` divisibility closure: a `PowerSeries` twin of `Polynomial.C_dvd_iff_dvd_coeff` is missing.

---

## Part III — Refuted (looks generalisable, is not)

- **R-1 `uniqueness.lean` beyond ℂ** (July J1) — confirmed; see Part I. The algebraic analogue over other fields is a statement about Weierstrass curves already in mathlib's `WeierstrassCurve`/`EllipticCurve` (e.g. `j_of_isShortNF`), not about lattices.
- **R-2 `meromorphicAt_of_comp_pow` beyond ℂ as base field** (July B1) — proof needs the open-mapping theorem for `(·^m)` and the removable-singularity theorem, both one-complex-variable; only the codomain generalises (G-36).
- **R-3 ℤ compute layer (`Qj.lean`, `link.lean`, `LevelThree.lean` jets) to `CommRing`** (July F2) — would destroy the `decide +kernel`/`rfl` certificates that are its purpose (`LevelThree.lean:47–49`, `qexp_coeffs.lean:71–109`).
- **R-4 `primeFinEquivCoxMatrix` beyond primes** (July K2) — false for composite `m` (`|C(m)| = ψ(m) > m + 1`).
- **R-5 "`[Fact (Nat.Prime p)]` is unused in `KroneckerFrobenius.lean:26–37` and `:104–139`"** (Batch L digest) — refuted *as stated*: those statements mention `transformedJSeries (1 : ZMod p)`, which requires `Field (ZMod p)`, i.e. the `Fact`. Only `:77–96` (and `Kronecker.lean:263`) are droppable today; the rest only after G-1(iii).
- **R-6 `transformedJSeries` to `[CommRing K]` "for free"** — no: the phase `ζ ^ (e : ℤ)` is a `zpow`, so `DivisionRing` is the floor without redesigning the phase (G-1(iii)).
- **R-7 "bidegree ≤ n is a parameter change"** — refuted; the enumeration is literal (`Fin 10` vectors, `fin_cases`); only the kernel `SymmetricCubicLaurent.lean:285–342` is generic (G-26 is High, not Low).
- **R-8 Canonical HNF over an arbitrary PID** — uniqueness of the *canonical* form requires a chosen residue system and associate representatives (literature, G-24); the mathlib-shaped general statement is existence over Bézout/Euclidean domains plus uniqueness over ℤ (or relative to a residue choice), not a bare-PID canonical form.

---

## Part IV — Summary table

| # | Declaration(s) | From → To | Difficulty |
|---|---|---|---|
| G-1(i–ii) | LPE `:94–140`, SCL 26 sites, DiagonalLaurent `:57/66/81`, FCP `:24–39` | `Field` → `IsDomain` / `DivisionRing` (scratch-verified) | Low |
| G-2 | FCP `:51,75,92` | drop `CharZero` | Low |
| G-3 | KF `:77`, Kronecker `:263` (now); KF `:26,104`, Kronecker `:389–445` (after G-1 iii) | drop `Fact Prime` | Low |
| G-4 | `tsum_pNat` Summability/Basic `:54` | drop 4 dead typeclasses (scratch-verified) | Low |
| G-5 | `ne_zero_of_tendsto_ne_zero` AtImInfty `:25` | any NeBot filter / T2 (scratch-verified) | Low |
| G-6 | `pos_nat_div_upper` upperhalfplane `:15` | positive real | Low |
| G-7 | `diagonal_coeff_one` Arithmetic `:239` | `CommSemiring`, publicise | Low |
| G-8 | `eq_or_eq_neg_of_associated_int_bivariate` Arithmetic `:164` | `R[X]`, units ±1 | Low |
| G-9 | `exists_commonDenominator…` Interpolation `:351` (+`RationalIn` CuspData `:48`) | any field / index type | Low |
| G-10 | `eval_interpolation_sum_at` Interpolation `:301` | `univ` → `Finset`, via `nodal` | Low |
| G-11 | `iteratedDeriv_sq_mul` uniqueness `:140` | ℂ/Analytic → 𝕜/ContDiffAt | Low |
| G-12 | `analyticAt_of_eventually_norm_le` NormalFormGrowth `:21` | `𝕜 → E` (scratch-verified), upstream | Low |
| G-13 | `meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq` ModularFunction `:96` | `𝕜 → E`, upstream | Low |
| G-14 | `exists_analyticAt_pow_succ_mul…` ModularFunction `:294` | `𝕜 → E`, upstream | Low |
| G-15 | NormalFormSlash `:22`, `:54` | `𝕜 → E`; weight k | Low |
| G-16 | `IsOfExponentialGrowth` CuspGrowth `:26`, `.slash` GrowthAtCusp `:23` | IsBigO form; weight k | Low |
| G-17 | Deltaqexpansions `:159/166`, Eisenstein `:34/41`, multipliable_lems `:74/78` | `CommSemiring` / `DivisionRing` / ordered semiring | Low |
| G-25 | Irreducibility `:89,102` | drop `minpoly` from the count lemma; conclude `p = minpoly`; upstream | Low |
| G-28 | `card_coxMatrix` Cardinality `:270` | ℕ-valued | Low |
| G-35 | `laurentSeriesMapRingHom` LPE `:22` | `HahnSeries.mapRingHom`, Semiring/Γ (scratch-verified) | Low |
| G-38 | `HahnSeries.charP`, `PowerSeries.map_frobenius_expand`, totient block count, PowerSeries `C_dvd` | small upstream lemmas | Low |
| B3 | `analyticOrderAt (·^m) 0 = m` (LQE `:275`, LaurentExpansion `:151`) | use `analyticOrderAt_pow`+`_id` once | Low |
| G-18 | `laurentqExpansion_nat_mul_coeff*` Algebra `:384,419` (+K3 sites) | `HahnSeries.embDomainRingHom` | Low–Medium |
| G-21 | `IsIntegralPowerSeriesmod` IPS `:173` | lifts + regular `c` | Low–Medium |
| G-31 | 11.9(i) field form | `gamma0ModularFunctionField 1 = ⊥` | Low–Medium |
| G-33 | right-coset API CoxMatrices/Basic `:615–690` | any `H ≤ G` acting on `X` | Low–Medium |
| G-34 | coefficient-closure twins AnalyticSupport `:61` / Interpolation `:156` | `liftsRing`/subring | Low–Medium |
| G-36 | `meromorphicAt_of_comp_pow` LQE `:194` | codomain Banach `E`, upstream | Low–Medium |
| G-1(iii) | `transformedJSeries` LaurentExpansion `:50` | phase as hom → `CommRing` | Medium |
| G-19 | `analyticTaylor_comp_pow` Algebra `:328` | `HasFPowerSeriesAt` + `expand` over 𝕜 | Medium |
| G-20 | `HasCoeffsIn` IPS `:51`, FCP `:51`, IntegralDescent `:72` | `PowerSeries.lifts` + `HahnSeries.coeffMemSubring` | Medium |
| G-22 | `CyclicSublattice` `:24–157` | any rank-2 free ℤ-module | Medium |
| G-23 | Classification `:28–175` | `(M, bM)`-generic equivalence with `CoxMatrix m` | Medium |
| G-27 | Dedekind ψ Cardinality `:113–243` | `ArithmeticFunction.dedekindPsi` | Medium |
| G-30 | `IsImaginaryQuadratic` SingularModuli `:38` | `minpoly` degree-2 bridge | Medium |
| G-32 | `toMeromorphicField_eq_div_of` ModularFunctionField `:56` | any `MeromorphicField` element, meromorphic `a b` | Medium |
| F1 | jets LevelThree `:249–283` | window `N` | Low–Medium |
| G-24 | HNF rank n / Bézout (A1/A3/A4) | correct criterion `D_{n−1} = 1`; docstring now | Low (doc) / High |
| G-26 | symmetric bidegree SCL `:368` | triangle `T_n`, weights, injectivity hypothesis | High |
| G-29 | `dim_gen_cong_levels` DimensionFormulas `:198` | `[Γ.FiniteIndex]` (restating Low) | High (proof) |
| G-37 | Laurent expansion of a germ LQE `:236–374` | `MeromorphicAt.laurentExpansionAt` | High |

**Counts**: **22 Low**, **6 Low–Medium**, **9 Medium**, **4 High** (G-24 upstream path, G-26, G-29 proof, G-37); **8 refuted** (4 July confirmed + 4 new).
July carry-over: 2 DONE (C1, E1-proof), 22 STILL OPEN, 4 refutations confirmed.

### Sources (literature checks)
- [Wikipedia — Hermite normal form](https://en.wikipedia.org/wiki/Hermite_normal_form); [Hermite/Smith canonical forms over a PID — ACM SIGSAM](https://dl.acm.org/doi/10.1145/101104.101105); [Damer — Computing the HNF: a survey (IACR 2024/2089)](https://eprint.iacr.org/2024/2089.pdf)
- [Wikipedia — Smith normal form](https://en.wikipedia.org/wiki/Smith_normal_form); [Stanley — Smith normal form in combinatorics](https://math.mit.edu/~rstan/papers/snf_survey.pdf)
- [Wikipedia — Dedekind psi function](https://en.wikipedia.org/wiki/Dedekind_psi_function); [OEIS A001615](https://oeis.org/A001615)
- [MathWorld — Weierstrass elliptic function](https://mathworld.wolfram.com/WeierstrassEllipticFunction.html); [DLMF §23.3](https://dlmf.nist.gov/23.3)
- [Brunault — Sturm bounds for general congruence subgroups](https://perso.ens-lyon.fr/francois.brunault/recherche/Sturm-bound-general.pdf); [Sage — arithmetic subgroups of SL₂(ℤ)](https://doc.sagemath.org/html/en/reference/arithgroup/sage/modular/arithgroup/arithgroup_generic.html)
- [Wikipedia — Kronecker's congruence](https://en.wikipedia.org/wiki/Kronecker's_congruence); [Drinfeld modular polynomials II: Kronecker congruences (arXiv 1303.4086)](https://arxiv.org/pdf/1303.4086)
- [Zagier — Traces of singular moduli](https://people.mpim-bonn.mpg.de/zagier/files/tex/TracesSingModuli/fulltext.pdf); [Vanderbilt — Complex multiplication lecture notes](https://math.vanderbilt.edu/rolenl/ModularFormsLecture28.pdf)
- [Wikipedia — q-expansion principle](https://en.wikipedia.org/wiki/Q-expansion_principle); [Conrad — Algebraic theory of q-expansions](https://virtualmath1.stanford.edu/~conrad/248BPage/handouts/qexp.pdf)
- [Wikipedia — Laurent series](https://en.wikipedia.org/wiki/Laurent_series); [Siu — Cauchy's integral formula, power and Laurent series](https://people.math.harvard.edu/~siu/math113/5_cauchy_integral_formula_power_and_laurent_series_expansion.pdf)
- [Aitken — Minimal, primitive and irreducible polynomials](https://public.csusm.edu/aitken_html/Essays/Algebra/polynomials2021.pdf); [Macauley — Polynomials and irreducibility](https://www.math.clemson.edu/~macaule/classes/m20_math4120/slides/math4120_lecture-6-03_h.pdf)
- [Baginski–Fuchs — Explicit formulas for the modular equation](https://www.math.ucdavis.edu/~efuchs/ModEquation.pdf); [Sutherland — Computing the modular equation](https://math.mit.edu/~drew/MomoseSeminar.pdf); [Computing modular polynomials in quasi-linear time (arXiv 0704.3177)](https://arxiv.org/pdf/0704.3177)
- [Unimodular equivalence of sublattices (arXiv 2310.12519)](https://arxiv.org/pdf/2310.12519)
