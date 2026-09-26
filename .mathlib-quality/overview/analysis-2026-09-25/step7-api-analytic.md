# Step 7 — API-Design Review, ANALYTIC side (2026-09-25)

Scope: `LaurentQExpansion/*`, `IntegralPowerSeries/*`, `jFunction/*`, `ModularFunctions/**`,
`Modularforms/**` (live API only: E₄/E₆/Δ/ResToImagAxis/ForMathlib_Cusps + what jFunction/Cox
consume; E2/eta/IsCuspForm/DimensionFormulas/Summability are Step-4 wholesale replacements and
are only mentioned where their *live* fragments hand-roll something), `qExpansion_tactic/*`,
`Tactic2/*`, `uniqueness.lean`, `Cox/ModularFunction{.lean,/CuspData,/LevelJ}`, `Cox/LatticeJ.lean`.
Line numbers are CURRENT (re-grepped 2026-09-25). Mathlib = pinned rev 2abc242.

Verification: four scratch compiles (`scratchpad/Step7Check.lean`, `lake env lean`, ≤ 5 s each,
final one clean) proved, verbatim, the statements marked **[verified]** below:
the transport lemma `cuspFunction_eventuallyEq_comp` + `cuspFunction_comp/comp₂_eventuallyEq`;
`meromorphicAt_cuspFunction_{neg,sub,pow,inv,smul,polynomialIn}` as 1–4-liners;
`laurentqExpansion_nat_mul` as `HahnSeries.embDomain` (8 lines from the existing coeff lemmas);
`Complex.im_tsum_eq_zero_of_forall` (2 lines); `S_smul_eq_of_slash` (4 lines);
`CuspData.apply_smul` (2 lines) and `CuspData.neg/.sub` (6 lines each); `SL_slash_zero` (2 lines);
`HolomorphicFunction.ext`; `poleRemoved_of_poleOrder_eq_zero`; `coeff_of_geq'` via `subst`.

Headline counts: 44 missing-lemma items (§1), 11 core definitions with thin/no simp API (§2: 83
`@[simp]` tags project-wide in 19,649 lines; LaurentQExpansion.lean 0, jfunction.lean 0, Cox
ModularFunction/CuspData 0; 66 manual `simp [def]`/`unfold` sites of core defs in scope),
9 instance/structure verdicts (§3), 12 definitions with completeness gaps (§4), 22 proofs > 30
lines with a collapse plan (§5), 24 naming/namespace items (§6).

---

## 0. July `step7-api.md` re-verification (scope-relevant items)

| July item | Status 2026-09-25 |
|---|---|
| `analyticAt_cuspFunction_of_eventuallyEq` + `cuspFunction_apply_zero_eq` | **DONE** — LaurentQExpansion.lean:340, :353; `analyticAt_cuspFunction_poleRemoved` 132 → 44 lines (:374–417). |
| `Periodic.cuspFunction_eventuallyEq_comp_invQParam` transfer lemma | **STILL OPEN** — the `=ᶠ[𝓝[≠]0]` skeleton is now at 7 sites (§1.1); no transport lemma exists. |
| `analyticOrderAt_const_mul_pow` | **STILL OPEN** — CoxMatrices/LaurentExpansion.lean:151–160 and LaurentQExpansion.lean:287–293. |
| `poleOrder_eq_of_meromorphicOrderAt_eq` | **DONE** — LaurentQExpansion.lean:243 (+ `_eq_zero_of_nonneg` :255, `_eq_toNat_neg_` :261). |
| `laurentqExpansion_pow` / `_polynomial_eval₂` / `meromorphicAt_…_polynomial_eval` | **STILL OPEN** — IntegralDescent.lean:25–52, DiagonalLaurent.lean:152–185 verbatim twins; CuspData.lean:115 private `meromorphicAt_polynomial_eval`. |
| `symmetricCubicExpansion_coeff`, `CoxMatrix.ofColumnHNF`, `CoxMatrix.ext`, BivariatePolynomial/CoxMatrix simp, LevelThree jets | out of analytic scope (algebraic Step-7 report). |
| `UpperHalfPlane.natScale` | **STILL OPEN** — jLevelN.lean:32–38 (`natCast_mul_im_pos_aux`, 8 users), LevelJ.lean:29–38 (`natScaleUpperHalfPlane`, private), CoxMatrices/Basic.lean:725; mathlib `posRealAction` (UpperHalfPlane/Basic.lean:197) unused. |
| one canonical `jIntCoeff` + cast API | **STILL OPEN** — three notions persist (jfunction.lean:319 `qjCoeffs`, LaurentExpansion.lean:31 `jIntCoeff` via `choose`, Qj.lean:141 `qjCoeffInt`); both bridges private (qexp_coeffs.lean:46, LevelThree.lean:122). `jIntCoeff_of_lt_neg_one` now EXISTS as `jIntCoeff_eq_zero_of_lt` (Kronecker.lean:149) but is misplaced and unused by `transformedJSeries` (§1.5). |
| sphere-membership helpers (circle integral) | **DONE** — one private lemma `cuspFunction_poleRemoved_div_zpow_eq_of_mem_sphere` (:635); `laurentqExpansion_coeff_eq_circleIntegral` 151 → 16 lines; but the whole subtree :600–706 is now dead (0 users). |
| `qExpansion_coeff_eq_intCast_of` cast-dance (qexp_coeffs) | **STILL OPEN** — pattern is now `rw [link, coeff_eq]; rfl` ×12 (qexp_coeffs.lean:30–113). |
| simp set for `laurentqExpansion.coeff_*`; defining-equation simp lemmas for the four core defs | **STILL OPEN** — LaurentQExpansion.lean has 0 `@[simp]`. |
| `poleRemoved_of_poleOrder_eq_zero` (inline ×3) | **STILL OPEN** — :426–428, :442–444, :594–596. |
| `HolomorphicFunction` eval API / `ext` | **STILL OPEN** — `congrArg (fun f : HolomorphicFunction ↦ f.1 _)` at UHPFF:81, :239, ModularFunctionField:100; `Subtype.ext; funext` ×4. |
| `IsGamma0ModularFunction` closure set | renamed `CuspData`; **STILL OPEN** — only `.mul`, `.polynomialIn` public; `cuspData_sub_const_mul_pow` private (Cox/ModularFunction.lean:75). |
| naming: `analyticAt_iff`, `order`, duplicate `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder`, `cuspFunction_to_analyticAt_analyticAt` | **DONE** (renamed to `analyticAt_cuspFunction_iff_poleOrder_eq_zero` :420; duplicates removed). |
| `laurentqExpansion` sub/pow/smul/inv/congr; `poleOrder_congr/_add_le/_mul_le`; `levelJ_apply`, `jN 1 = j` | **STILL OPEN** (§4). |
| `to_qExpansion` docstring | **DONE** (:319–320); snake_case name **STILL OPEN**. |
| Long proofs: `analyticAt_cuspFunction_poleRemoved` 132→44 (DONE), `laurentqExpansion_coeff_eq_circleIntegral` 151→16 (DONE), `laurentqExpansion_mul` 38→16 (DONE), `to_qExpansion_nat_mul` 46→17 (DONE), `poleOrder_coxAction_aux` 54→42 (partial), `laurentqExpansion_coxAction_coeff_aux` 90→43 (partial), `to_qExpansion_coxAction_aux` 44→46 (OPEN), `exists_const_poleOrder_sub_mul_pow_lt` 49→52 (OPEN). |

---

## 1. Missing lemmas (would simplify multiple proofs)

Format: NAME — statement — home — current hand-rolled sites — saving — mathlib ingredients.

### 1.1 The cusp-function transport lemma (master key) **[verified]**

**L1 `UpperHalfPlane.cuspFunction_eventuallyEq_comp`**
```lean
lemma cuspFunction_eventuallyEq_comp (h : ℝ) (f : ℍ → ℂ) :
    cuspFunction h f =ᶠ[𝓝[≠] (0 : ℂ)] f ∘ UpperHalfPlane.ofComplex ∘ Periodic.invQParam h
```
Home: `LaurentQExpansion/LaurentQExpansion.lean` (top, public; or upstream next to
`Periodic.cuspFunction_eq_of_nonzero`, Periodic.lean:119, as `Periodic.cuspFunction_eventuallyEq`).
Proof: `filter_upwards [self_mem_nhdsWithin] with q hq; exact Periodic.cuspFunction_eq_of_nonzero _ _ hq`.

**L2 `cuspFunction_comp_eventuallyEq (φ : ℂ → ℂ)`** and **L3 `cuspFunction_comp₂_eventuallyEq (op : ℂ → ℂ → ℂ)`**
```lean
lemma cuspFunction_comp_eventuallyEq (φ : ℂ → ℂ) (h : ℝ) (f : ℍ → ℂ) :
    cuspFunction h (fun τ ↦ φ (f τ)) =ᶠ[𝓝[≠] (0 : ℂ)] fun q ↦ φ (cuspFunction h f q)
lemma cuspFunction_comp₂_eventuallyEq (op : ℂ → ℂ → ℂ) (h : ℝ) (f g : ℍ → ℂ) :
    cuspFunction h (fun τ ↦ op (f τ) (g τ)) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q ↦ op (cuspFunction h f q) (cuspFunction h g q)
```
(3 lines each: `filter_upwards [L1 f, L1 g, L1 (fun τ ↦ …)]; simp [*]`.)
Sites that hand-roll the identical 7–11-line skeleton (`filter_upwards [self_mem_nhdsWithin]; simp only [cuspFunction]; rw [Periodic.cuspFunction_eq_of_nonzero …]×k; rfl`):
- LaurentQExpansion.lean:68–77 (`cuspFunction_add_eventuallyEq`, private), :79–88 (`_mul_`, private), :90–96 (`_const_`, private)
- Cox/ModularFunction/CuspData.lean:86–95 (`cuspFunction_mul_eventuallyEq`, private — byte-identical to the LaurentQExpansion one), :125–134 (`_polynomial_eval_`)
- Cox/ModularFunction.lean:63–73 (`cuspFunction_sub_const_mul_pow_eventuallyEq`)
- LaurentQExpansion/Algebra.lean:40–46 (`cuspFunction_const`, global form)
Plus 6 inline "value of the cusp function at nonzero `q`" gadgets that are `L1` + `ofComplex_apply_of_im_pos`: jfunction.lean:152–158, jLevelN.lean:151–154, CoxMatrices/LaurentExpansion.lean:102–106, LevelJ.lean:141–147, LaurentQExpansion.lean:371, CuspGrowth.lean:64–70.
Saving: 7 × ~9 + 6 × ~4 ≈ 85 lines; 4 private lemmas deleted; every future pointwise operation is free.
Mathlib: `Periodic.cuspFunction_eq_of_nonzero`; no mathlib `=ᶠ[𝓝[≠]0]` form exists (mathlib's `cuspFunction_add/mul/smul/neg/sub`, QExpansion.lean:440–461, are pointwise-at-0 under `ContinuousAt`).

**L4 `meromorphicAt_cuspFunction_{neg,sub,smul,pow,inv,div}`** (each one line from L2/L3):
```lean
lemma meromorphicAt_cuspFunction_neg (hf : MeromorphicAt (cuspFunction h f) 0) :
    MeromorphicAt (cuspFunction h (fun τ ↦ -f τ)) 0 :=
  hf.neg.congr (cuspFunction_comp_eventuallyEq Neg.neg h f).symm
lemma meromorphicAt_cuspFunction_sub (hf) (hg) : MeromorphicAt (cuspFunction h (fun τ ↦ f τ - g τ)) 0
lemma meromorphicAt_cuspFunction_smul (a : ℂ) (hf) : MeromorphicAt (cuspFunction h (fun τ ↦ a * f τ)) 0
lemma meromorphicAt_cuspFunction_pow (hf) (n : ℕ) : MeromorphicAt (cuspFunction h (fun τ ↦ f τ ^ n)) 0
lemma meromorphicAt_cuspFunction_inv (hf) : MeromorphicAt (cuspFunction h (fun τ ↦ (f τ)⁻¹)) 0
lemma meromorphicAt_cuspFunction_div (hf) (hg) : MeromorphicAt (cuspFunction h (fun τ ↦ f τ / g τ)) 0
```
Home: LaurentQExpansion.lean beside `_add/_mul` (:99–115), which should be re-proved the same way.
Sites currently doing this by hand: Cox/ModularFunction.lean:89–94 (`sub`+`const_mul`+`pow` inline), CuspData.lean:110–113, :149–152, Algebra.lean:236–247 (`laurentqExpansion_neg` via `C (-1) *`), jfunction.lean:262–267 (`cuspFunction_qOverDelta_eq_inv_aux`, `funext; by_cases` — the `inv` case), jLevelN.lean:174–181. Mathlib: `MeromorphicAt.neg/sub/mul/pow/inv/div/const` (Meromorphic/Basic.lean, namespace `MeromorphicAt`).

**L5 `meromorphicAt_cuspFunction_polynomialIn`** **[verified, 5 lines]**
```lean
lemma meromorphicAt_cuspFunction_polynomialIn (hf : MeromorphicAt (cuspFunction h f) 0)
    (P : Polynomial ℂ) : MeromorphicAt (cuspFunction h (fun τ ↦ P.eval (f τ))) 0
```
Replaces CuspData.lean:115–134 (private `meromorphicAt_polynomial_eval` + `cuspFunction_polynomial_eval_eventuallyEq`, 20 lines), IntegralDescent.lean:31–33 and :45–47, DiagonalLaurent.lean:159–161 and :176–179 (each detours through `(j_cuspData m).polynomialIn P |>.2.2 1`, i.e. builds full `CuspData` just to read one component). Also the general `MeromorphicAt.aeval_polynomial` is a mathlib gap (mathlib has only `AnalyticAt.aeval_polynomial`, Analytic/Polynomial.lean:38).

**L6 `CuspData.cuspFunction_meromorphicAt_one`** — `(hf : CuspData N f) : MeromorphicAt (cuspFunction N f) 0` (:= by simpa using hf.2.2 1). The idiom `simpa using hf.2.2 (1 : SL(2, ℤ))` appears at Cox/ModularFunction.lean:209, :249; DiagonalLaurent.lean:30, :161, :179; IntegralDescent.lean:33, :47 (7 sites).

### 1.2 `poleOrder` / `laurentqExpansion` algebra

**L7 `laurentqExpansion_pow`, `laurentqExpansion_sub`, `laurentqExpansion_smul`, `laurentqExpansion_polynomialIn`**
```lean
lemma laurentqExpansion_pow (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0) (n : ℕ) :
    laurentqExpansion h (fun τ ↦ f τ ^ n) = laurentqExpansion h f ^ n
lemma laurentqExpansion_sub (hh) (hf) (hg) :
    laurentqExpansion h (fun τ ↦ f τ - g τ) = laurentqExpansion h f - laurentqExpansion h g
lemma laurentqExpansion_smul (hh) (a : ℂ) (hf) :
    laurentqExpansion h (fun τ ↦ a * f τ) = HahnSeries.C a * laurentqExpansion h f
theorem laurentqExpansion_polynomialIn (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0)
    (P : Polynomial ℂ) :
    laurentqExpansion h (fun τ ↦ P.eval (f τ)) =
      P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion h f)
```
Home: `LaurentQExpansion/Algebra.lean` (after `laurentqExpansion_finset_prod`; `_pow` is `finset_prod` over `range n` + `Finset.prod_const`, 3 lines; `_polynomialIn` is one `Polynomial.induction_on'` using `_add/_smul/_pow` + L5, ~12 lines).
Sites: IntegralDescent.lean:25–29 (`laurentqExpansion_j_pow_aux`), :35–52 (`laurentqExpansion_polynomialIn_j_aux`, 18-line induction); DiagonalLaurent.lean:152–157 (`_j_pow_widthM`), :164–185 (`_polynomialIn_j_widthM`, 22-line induction, verbatim twin with `1 ↦ m`); LevelThree.lean:715–725 re-wraps at `m = 3`. Saving ≈ 55 lines, 4 private lemmas; the two inductions become `laurentqExpansion_polynomialIn one_pos j_cuspFunction_meromorphicAt P` and `… (by positivity) (j_widthM_cuspMeromorphicAt m) P`.
Note the Cox files state the polynomial as `Cox.polynomialIn P f` (CuspData.lean:41 = `fun τ ↦ P.eval (f τ)`), which is `Polynomial.aeval f P` in the Pi-algebra (`Polynomial.aeval_fn_apply`, AlgebraMap.lean:480) — adopting `aeval` would give `map_add/map_mul/aeval_X/aeval_C` for free.

**L8 `poleOrder` bounds / normalisations** (completeness; unlock the Cox 11.10 induction in `poleOrder` language)
```lean
lemma poleOrder_const (h) (a : ℂ) : poleOrder h (fun _ ↦ a) = 0          -- from analyticAt_iff + const
@[simp] lemma poleOrder_zero (h) : poleOrder h 0 = 0;  @[simp] lemma poleOrder_one (h) : poleOrder h 1 = 0
lemma poleOrder_neg (hf) : poleOrder h (fun τ ↦ -f τ) = poleOrder h f
lemma poleOrder_smul (hf) (ha : a ≠ 0) : poleOrder h (fun τ ↦ a * f τ) = poleOrder h f
lemma poleOrder_add_le (hf) (hg) : poleOrder h (fun τ ↦ f τ + g τ) ≤ max (poleOrder h f) (poleOrder h g)
lemma poleOrder_mul_le (hf) (hg) : poleOrder h (fun τ ↦ f τ * g τ) ≤ poleOrder h f + poleOrder h g
lemma poleOrder_pow_le (hf) (n) : poleOrder h (fun τ ↦ f τ ^ n) ≤ n * poleOrder h f
lemma poleOrder_congr (hfg : f =ᶠ[atImInfty] g) : poleOrder h f = poleOrder h g
lemma poleOrder_lt_of_neg_lt_meromorphicOrderAt (hm : 0 < m)
    (hord : ((-(m : ℤ) : ℤ) : WithTop ℤ) < meromorphicOrderAt (cuspFunction h f) 0) : poleOrder h f < m
```
Home: LaurentQExpansion.lean after :261. The last one exists privately at Cox/ModularFunction.lean:132–144 (generic, no Cox content) — publicise. Sites: Algebra.lean:170–177 and :203–211 avoid the bounds by taking `N := sum of all three pole orders` (works, so 0 lines saved there); Cox/ModularFunction.lean:146–194 works directly in `meromorphicOrderAt`. Mathlib: `meromorphicOrderAt_add` (Order.lean:563, gives `≥ min`), `meromorphicOrderAt_mul`, `meromorphicOrderAt_neg` (:388), `meromorphicOrderAt_mul_of_ne_zero` (:863), plus `poleOrder_eq_toNat_neg_meromorphicOrderAt` (:261) and `Int.toNat` monotonicity.

**L9 `poleRemoved_of_poleOrder_eq_zero`** **[verified]** `(h0 : poleOrder h f = 0) : poleRemoved h f = f` — inline ×3: LaurentQExpansion.lean:426–428, :442–444, :594–596 (3 lines → 1 each).

**L10 `cuspFunction_poleRemoved_eventuallyEq`** `(hh : 0 < h) : cuspFunction h (poleRemoved h f) =ᶠ[𝓝[≠] 0] fun q ↦ q ^ poleOrder h f * cuspFunction h f q` — hand-rolled as `hEq_shift` LaurentQExpansion.lean:378–384 (7 lines; re-proves `cuspFunction_poleRemoved_eq` :432 which is stated *later*), again inside `to_qExpansion_coeff_zero_ne` :520–531 (12 lines), and Algebra.lean:343–362 (`_nat_mul_` variant). Follows from `cuspFunction_qpow_mul_eq` (:330) + L11. Saving ≈ 20 lines; also lets `analyticAt_cuspFunction_poleRemoved` drop from 44 to ≈ 20 lines (§5).

**L11 `eventually_norm_lt_one_nhdsNE_zero`** — `{q : ℂ | ‖q‖ < 1} ∈ 𝓝[≠] (0 : ℂ)` (or `∀ᶠ q in 𝓝[≠] 0, q ≠ 0 ∧ ‖q‖ < 1`). Exists privately as Algebra.lean:34 (`norm_lt_one_mem_nhdsNE_zero`); inlined at LaurentQExpansion.lean:363–364, :380–381, :523–524, jfunction.lean:444–446, jLevelN.lean:177–179, LevelJ.lean:291–293, CoxMatrices/LaurentExpansion.lean:128–130, CuspGrowth.lean:64–65 — 8 copies × 2–3 lines. Make public in LaurentQExpansion.lean (`nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 one_pos)`).

**L12 `laurentqExpansion.coeff_of_geq'`** **[verified]** `(hM : poleOrder h f = M) (hn : -(M : ℤ) ≤ n) : (laurentqExpansion h f).coeff n = (to_qExpansion h f).coeff (n + M).toNat` (`subst hM; exact coeff_of_geq hn`) and the twin `coeff_eq_zero_of_lt'`, `coeff_neg_add'` — the Tactic2/LaurentQExpSimpTests.lean:9–61 examples (8 of them) each spend 2–3 lines `simpa [hM] using …` to substitute; jfunction.lean:487–490, :498–502, CoxMatrices/LaurentExpansion.lean:284–286, LevelThree.lean:126–130 do the same with `j_poleOrder`. 12 sites × 2 lines.

### 1.3 Period change and the (11.13) bridge

**L13 `laurentqExpansion_nat_mul` as `HahnSeries.embDomain`** **[verified, 8 lines]**
```lean
def mulEmb (m : ℕ) (hm : m ≠ 0) : ℤ ↪o ℤ :=
  OrderEmbedding.ofStrictMono (fun k ↦ (m : ℤ) * k) (fun a b hab ↦ Int.mul_lt_mul_of_pos_left hab (by omega))
theorem laurentqExpansion_nat_mul (hm : m ≠ 0) (hmero : MeromorphicAt (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ ofComplex) h) :
    laurentqExpansion ((m : ℝ) * h) f = HahnSeries.embDomain (mulEmb m hm) (laurentqExpansion h f)
```
Home: Algebra.lean replacing the two coefficient lemmas :384–439 (56 lines of `Int.toNat` bookkeeping → `embDomain_coeff` / `embDomain_notin_range` one-liners at the consumers Kronecker.lean:213, :239, DiagonalLaurent.lean:47). With `HahnSeries.embDomainRingHom` (Multiplication.lean:899) the `(·*m)` map is a ring hom, so `laurentqExpansion_nat_mul` commutes with the whole §1.2 algebra automatically. Mathlib: `HahnSeries.embDomain` (Basic.lean:441), `embDomain_coeff` (:449), `embDomain_notin_range` (:477), `embDomainRingHom` (Multiplication.lean:899).

**L14 The `LaurentSeries.substMonomial` bridge (batch J) — assessment: YES, one bridge subsumes both chains.**
```lean
/-- Substitute `q ↦ c * q ^ r` into a Laurent series: coefficient `k` is `c^(k/r) * F.coeff (k/r)`
when `r ∣ k` and `0` otherwise (`c ≠ 0` so that `c ^ (k/r)` is a `zpow`). -/
def LaurentSeries.substMonomial (c : K) (r : ℕ) (F : LaurentSeries K) : LaurentSeries K :=
  HahnSeries.ofSuppBddBelow (fun k ↦ if (r : ℤ) ∣ k then c ^ (k / r) * F.coeff (k / r) else 0)
    ⟨r * F.order …⟩
@[simp] theorem substMonomial_coeff … ;  theorem substMonomial_one : substMonomial 1 r F = embDomain (mulEmb r hr) F
theorem laurentqExpansion_comp_of_qParam_eq {h h' : ℝ} (hh : 0 < h) (hh' : 0 < h')
    {φ : ℍ → ℍ} {c : ℂ} (hc : c ≠ 0) {r : ℕ} (hr : r ≠ 0)
    (hφ : ∀ τ, Periodic.qParam h' (φ τ) = c * Periodic.qParam h τ ^ r)
    (hfper : Periodic (f ∘ ofComplex) h') (hf : MeromorphicAt (cuspFunction h' f) 0) :
    laurentqExpansion h (f ∘ φ) = substMonomial c r (laurentqExpansion h' f)
```
together with the two order lemmas it needs (`meromorphicAt_cuspFunction_comp_of_qParam_eq`, `poleOrder_comp_of_qParam_eq : poleOrder h (f ∘ φ) = r * poleOrder h' f`).
Instances: (i) `φ = id, h = m·h', c = 1, r = m` (hypothesis `hφ` is the 3-line identity `qParam (m h') τ ^ m = qParam h' τ`) ⇒ subsumes LaurentQExpansion.lean:46–66 (`cuspFunction_nat_mul_eq_cuspFunction_pow`), :147–159, :275–312 (`meromorphicOrderAt/poleOrder_nat_mul`) and Algebra.lean:343–439 (`_poleRemoved_nat_mul_`, `to_qExpansion_nat_mul`, both coeff lemmas) — ≈ 170 lines; (ii) `φ = σ.act, h = m, h' = 1, c = ζ^{ab}, r = a²` (`hφ` = `qParam_coxAction_aux`, CoxMatrices/LaurentExpansion.lean:77–91, 15 lines) ⇒ subsumes LaurentExpansion.lean:93–300 (`cuspFunction_coxCompose_aux` … `laurentqExpansion_coxAction_coeff_aux`, ≈ 190 lines, incl. the three 42–46-line `_aux` proofs). The bridge's own cost is Algebra.lean:285–339 generalised from `expand r` to `expand r ∘ rescale c` (≈ 60 lines; `PowerSeries.rescale`, `coeff_rescale` Basic.lean:562, `coeff_expand_mul` Expand.lean:87) + `analyticOrderAt_const_mul_pow` (L35) + ≈ 30 lines of coefficient assembly ≈ 120 lines. Net ≈ 360 − 150 ≈ **210 lines saved**, two parallel chains → one, and `transformedJSeries ζ σ = substMonomial (ζ^{ab}) (a²) (laurentqExpansion 1 j)` becomes a `HahnSeries.ext; simp` fact once L20 removes the redundant `-(a²) ≤ k` clause. Caveats: `c ^ (k/r)` is a `zpow` (needs `c ≠ 0`; fine: `coxPhase_ne_zero_aux` :121); mathlib has no Laurent-series `rescale`, so `substMonomial_mul` (if wanted) must be proved once (~15 lines) or obtained as `embDomainRingHom ∘ rescaleRingHom`.

### 1.4 Coefficient / integrality layer (`IntegralPowerSeries`, `link.lean`)

**L15 `coeff_toIntegralPowerSeries_cast`** (×6)
```lean
@[simp] lemma coeff_toHasCoeffsInPowerSeries (hf : HasCoeffsIn R A f) (n : ℕ) :
    algebraMap R A ((toHasCoeffsInPowerSeries R A hf).coeff n) = f.coeff n
@[simp] lemma coeff_toIntegralPowerSeries_cast (hf : IsIntegralPowerSeries f) (n : ℕ) :
    (((toIntegralPowerSeries hf).coeff n : ℤ) : ℂ) = f.coeff n
```
Home: IntegralPowerSeries.lean after :135. Sites re-deriving it (`congrArg (PowerSeries.coeff n) (coeTo_of_toIntegralPowerSeries …)` + cast dance): IntegralPowerSeries.lean:180–181, Deltaqexpansions.lean:107–111 (`toIntegralPowerSeries_coeff_eq`, private), jfunction.lean:208–211, :321–323 (`qj_coeff_cast_aux`, private), link.lean:234–239, qexp_coeffs.lean:48–50. Saving ≈ 15 lines, 2 private lemmas; mathlib: `PowerSeries.coeff_map` (Basic.lean:455).

**L16 `hasCoeffsIn_pow / _X / _algebraMap / _finset_sum / _finset_prod / _coeff`** — one-liners over `Subalgebra.pow_mem/algebraMap_mem/sum_mem/prod_mem` + the `.1` direction of `hasCoeffsIn_iff_coeff`. Deltaqexpansions.lean:80 uses `IntegralPowerSeriesSubring.pow_mem` instead (works only because of the abbrev tower). Completeness.

**L17 `PowerSeries.coeff_mapAlgHom_ofId`** (×3)
```lean
@[simp] lemma coeff_mapAlgHom_ofId (F : PowerSeries ℤ) (n : ℕ) :
    (PowerSeries.mapAlgHom (Algebra.ofId ℤ ℂ) F).coeff n = (F.coeff n : ℂ)
```
Sites: link.lean:203–206, :228–230, :235–239 (`congrArg (coeff n) …; change (PowerSeries.map (Int.castRingHom ℂ) _).coeff n = _; rw [coeff_map]`, 3–4 lines → 1 `rw`). The general `coeff_mapAlgHom (φ) (F) (n) : (mapAlgHom φ F).coeff n = φ (F.coeff n)` is a mathlib gap (only `mapAlgHom_apply` :732 + `coeff_map` :455 unfused).

**L18 `mapAlgHom_ofId_toIntegralPowerSeries`** (×3) — `(hf) : PowerSeries.mapAlgHom (Algebra.ofId ℤ ℂ) (toIntegralPowerSeries hf) = f`, i.e. `coeTo_of_toIntegralPowerSeries` restated with the mathlib name (they are defeq through the abbrevs `coeToComplexPowerSeries.ringHom`/`powerSeriesMapAlgHom`). Sites link.lean:159–160, :165–166, :371–372 (`simpa [integralE4, coeToComplexPowerSeries.ringHom, powerSeriesMapAlgHom] using …` → `exact`). Better: delete the two renames (IntegralPowerSeries.lean:33, :107) and state everything with `PowerSeries.map (Int.castRingHom ℂ)`.

**L19 `toIntegralPowerSeries_eq_of_map_eq`** — `(hf) (g : PowerSeries ℤ) (hg : g.map (Int.castRingHom ℂ) = f) : toIntegralPowerSeries hf = g` (lift uniqueness; `PowerSeries.map_injective` + `Int.cast_injective`). Site: Deltaqexpansions.lean:246–255 (10 lines → 1); also makes `qjCoeffs`/`integralDelta` specs canonical (L21).

### 1.5 `j`-coefficient bridges (three notions, zero public bridges)

**L20 `jIntCoeff_eq_zero_of_lt`: EXISTS at Kronecker.lean:149 — misplaced; move beside `jIntCoeff_neg_one` (CoxMatrices/LaurentExpansion.lean:38) and use it to delete the redundant `-((σ.a : ℤ)^2) ≤ k` conjunct from `transformedJSeries` (:52, :69) and from `cox_a_le` (UHPFF.lean:160–167).**

**L21 public bridges** (currently private or absent):
```lean
theorem qjCoeffs_eq_qjCoeffInt (n : ℕ) : qjCoeffs n = qjCoeffInt n            -- qexp_coeffs.lean:46–51 private
theorem laurentqExpansion_j_coeff_sub_one (n : ℕ) :
    (laurentqExpansion 1 j).coeff ((n : ℤ) - 1) = (qExpansion 1 qj).coeff n   -- qexp_coeffs.lean:138–141 private
theorem jIntCoeff_eq_qjCoeffs (n : ℤ) (hn : -1 ≤ n) : jIntCoeff n = qjCoeffs (n + 1).toNat  -- absent
theorem jIntCoeff_eq_qjCoeffInt (n : ℕ) : jIntCoeff ((n : ℤ) - 1) = qjCoeffInt n            -- LevelThree.lean:122 private
```
The shift bridge is re-proved at CoxMatrices/LaurentExpansion.lean:42–45, :284–286, LevelThree.lean:126–130, jfunction.lean:498–502 (5 sites × 3–5 lines). Home: `jFunction/jfunction.lean` (shift) / `qExpansion_tactic/link.lean` (`qjCoeffInt` bridges).

**L22 design: explicit witness for `jIntCoeff`.** `noncomputable def jIntCoeff (n : ℤ) : ℤ := if n < -1 then 0 else qjCoeffs (n + 1).toNat` with `jIntCoeff_spec` proved exactly as jfunction.lean:493–502 does today; then `jIntCoeff_neg_one = qjCoeffs_zero`, `jIntCoeff_eq_zero_of_lt = if_pos`, and one `Classical.choose` (LaurentExpansion.lean:32) disappears. The `qjCoeffs` definition itself (jfunction.lean:319, via `toIntegralPowerSeries` = `Classical.choose`) should get a public spec `qjCoeffs_cast : (qjCoeffs n : ℂ) = (qExpansion 1 qj).coeff n` (= L15 instance) instead of the private `qj_coeff_cast_aux`.

### 1.6 Live modular-forms API (E₄/E₆/Δ/E₂ fragments that survive Step 4)

**L23 `Complex.im_tsum_eq_zero_of_forall`** **[verified, 2 lines]** `(hf : Summable f) (h : ∀ a, (f a).im = 0) : (∑' a, f a).im = 0` (+ `im_tprod_eq_zero_of_forall` twin via `Complex.ofRealHom` and `Multipliable.map_tprod`, the route already taken at Delta.lean:357–361). Sites: Eisenstein.lean:512–515, :579–582 (4 lines each), Delta.lean:317–326 (10-line hand-rolled `tendsto_nhds_unique` for `tprod`). Honest saving ≈ 12 lines; the other 40 lines of each imag-axis proof are *summability*, which Step 4 replaces by mathlib `summable_pow_mul_cexp` / `summable_norm_pow_mul_geometric_div_one_sub`. Mathlib: `Complex.im_tsum` (Analysis/Complex/Basic.lean:546).

**L24 `S_smul_eq_of_slash` / `SlashInvariantForm.S_smul_eq`** **[verified, 4 lines]**
```lean
lemma S_smul_eq_of_slash {f : ℍ → ℂ} {k : ℤ} (hS : f ∣[k] ModularGroup.S = f) (z : ℍ) :
    f (ModularGroup.S • z) = z ^ k * f z
lemma SlashInvariantForm.S_smul_eq (f : SlashInvariantForm ↑Γ(1) k) (z : ℍ) : f (ModularGroup.S • z) = z ^ k * f z
```
Sites (the `SL_slash_apply, denom_S, zpow_neg … field_simp/mul_inv_eq_iff` tail): Eisenstein.lean:79–88, :91–100 (10 lines each), Delta.lean:69–73 (5), E2.lean:87–91 (5; E₂ is quasi-modular, only the tail collapses). ≈ 20 lines. Mathlib: `SlashInvariantForm.slash_S_apply` (Identities.lean:47), `modular_S_smul`.

**L25 `strictPeriods_Gamma` discharge ×8** — qExpansion_lems.lean:26, :57–58, :70–71, :106 and Eisenstein.lean:171, :173, :180, :191 all repeat `(Nat.cast_pos.mpr (Nat.pos_of_neZero n)) (by simp)`. Every one of these declarations is a Γ(n)-specialisation of a mathlib lemma slated for deletion in Step 4 (`qExpansion_mul/smul/of_pow/eq_zero_iff`; Eisenstein's dead cusp-function block :135–196). Action: delete; no new lemma (mathlib's `strictPeriods_Gamma`, Cusps.lean:452, is already `@[simp]`).

**L26 `tendsto_atImInfty_of_analyticAt_cuspFunction` family** (mathlib has none: searched `tendsto.*atImInfty` in ModularForms/QExpansion.lean, BoundedAtCusp.lean, EisensteinSeries/* — only `qParam_tendsto_atImInfty`)
```lean
lemma tendsto_atImInfty_of_analyticAt_cuspFunction (hh : 0 < h) (hper : Periodic (f ∘ ofComplex) h)
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) : Tendsto f atImInfty (𝓝 (cuspFunction h f 0))
lemma ModularFormClass.tendsto_atImInfty [ModularFormClass F Γ k] (f : F) (hh) (hΓ) :
    Tendsto f atImInfty (𝓝 ((qExpansion h f).coeff 0))
lemma isBoundedAtImInfty_of_analyticAt_cuspFunction (hh) (hper) (hf) : IsBoundedAtImInfty f
lemma cuspFunction_apply_zero_of_tendsto (hh : 0 < h) (hf : Tendsto f atImInfty (𝓝 a)) : cuspFunction h f 0 = a
```
Sites: LatticeJ.lean:593–602 (`E4_tendsto_atImInfty_aux`, 10), IsCuspForm.lean:113–120 (8), Cox/ModularFunction.lean:36–45 (`hfbdd`, 10), jfunction.lean:43–48 (converse, private, `h = 1` only). ≈ 25 lines; upstream candidates (QExpansion.lean).

**L27 Γ(1) corollary of `ForMathlib_Cusps`** — `zero_at_cusps_of_zero_at_infty_of_SL2Z_invariant (hslash : ∀ γ : SL(2,ℤ), f ∣[k] γ = f) (h : IsZeroAtImInfty f) (hc : IsCusp c Γ(1)) : c.IsZeroAt k f` (3 lines). Sites: IsCuspForm.lean:107–111, :128–132, LatticeJ.lean:564–568 (5 lines each). After Step 4 only the LatticeJ site survives.

### 1.7 Cox analytic layer (`CuspData` / `ModularFunction` / `MeromorphicField`)

**L28 `CuspData.apply_smul`** **[verified, 2 lines]** + `slash_zero_eq_iff`
```lean
theorem CuspData.apply_smul (hf : CuspData N f) (γ : Gamma0 N) (τ : ℍ) : f ((γ : SL(2, ℤ)) • τ) = f τ
theorem LevelOneCuspData.apply_sl2_smul (hf : LevelOneCuspData f) (γ : SL(2, ℤ)) (τ) : f (γ • τ) = f τ
theorem ModularForm.SL_slash_zero (f : ℍ → ℂ) (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] γ = fun τ ↦ f (γ • τ)   -- [verified]
theorem ModularForm.SL_slash_zero_eq_iff : f ∣[(0 : ℤ)] γ = f ↔ ∀ τ, f (γ • τ) = f τ
```
Sites of the `simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one] using congrFun (hf.2.1 γ) τ` idiom: Cox/ModularFunction.lean:85–88, :349–350; CuspData.lean:106–109, :146–148; Interpolation.lean:285–286; Congruence.lean:75–77 (6 sites). The same simp set proving the *other* direction (`funext τ; simp only [SL_slash_apply, …]`): jLevelN.lean:88, jfunction.lean:78, LatticeJ.lean:585, Interpolation.lean:258, Construction.lean:206 (5 sites). `hslash : (f ∣[0] γ) = fun τ ↦ f (γ • τ)` is built inline at Congruence.lean:103–105, :132–134. Level-one lift `⟨γ, Gamma0_mem.mpr (Subsingleton.elim _ _)⟩` at Cox/ModularFunction.lean:47–48, :347–348. Total ≈ 30 lines over 15 sites.

**L29 `LevelOneCuspData.of_widthM`** (the A15 collapse)
```lean
theorem LevelOneCuspData.of_widthM (m : ℕ+) {f : ℍ → ℂ}
    (hH : ∀ z : ℂ, 0 < z.im → MeromorphicAt (f ∘ ofComplex) z)
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f)
    (hcusp : MeromorphicAt (cuspFunction (m : ℝ) f) 0) : LevelOneCuspData f
```
(≈ 10 lines: L28 + `meromorphicAt_cuspFunction_of_nat_mul` + `periodic_comp_of_slashInvariant_one`, AnalyticSupport.lean:83–94.) Sites: Construction.lean:251–277 (`_widthOne_cuspMeromorphicAt` + `coxPhiFunction_coeff_modularFunction`, 27 lines) ≡ Interpolation.lean:262–289 (`_widthOne_` + `interpolation_coeff_cuspData`, 28 lines) → 3 lines each. ≈ 50 lines, 4 privates.

**L30 `ModularFunction.ofGamma0Holomorphic` / `ofSL2ZHolomorphic`**
```lean
def ofGamma0Holomorphic (N : ℕ+) (f : ℍ → ℂ) (hf : MDiff f) (hinv : ∀ γ : Gamma0 N, f ∣[0] γ = f)
    (hcusp : ∀ γ : SL(2, ℤ), MeromorphicAt (cuspFunction N (fun τ ↦ f (γ • τ))) 0) : ModularFunction (Gamma0 N)
def ofSL2ZHolomorphic (f) (hf : MDiff f) (hslash : ∀ γ : SL(2,ℤ), f ∣[0] γ = f) (hgrowth : IsOfExponentialGrowth f) :
    ModularFunction 𝒮ℒ
lemma meromorphicNFOn_of_mdifferentiable (hf : MDiff f) : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet
```
Sites building `meromorphic' := ⟨MeromorphicField.ofHolomorphic _ h, toFun_ofHolomorphic _ h⟩` + the `bdd_at_cusps'` skeleton by hand: LevelJ.lean:313–319 (7 → 2), JInvariant.lean:41–54 (14 → 3), Construction.lean:261–277 (17 → 3); `meromorphicNFOn_of_mdifferentiable` is inlined at MeromorphicField.lean:647, :654. ≈ 30 lines.

**L31 `MeromorphicField.ofMeromorphic_eq_iff` / `ofMeromorphic_mul`** — ModularFunctionField.lean:56–86 (`toMeromorphicField_eq_div_of`, 31 lines) reaches into `Subtype.ext`, `Germ.coe_eq`, `filter_upwards` because nothing states
```lean
theorem ofMeromorphic_eq_iff (hf) (hg) : ofMeromorphic f hf = ofMeromorphic g hg ↔
    f ∘ ofComplex =ᶠ[codiscreteWithin upperHalfPlaneSet] g ∘ ofComplex
theorem ofMeromorphic_mul (hf) (hg) : ofMeromorphic (f * g) (hf.mul hg) = ofMeromorphic f hf * ofMeromorphic g hg  -- (+ _sub/_neg/_zero/_one/_algebraMap)
theorem ModularFunction.toMeromorphicField_eq_ofMeromorphic (f : ModularFunction Γ) :
    f.toMeromorphicField = ofMeromorphic f f.meromorphicOn                    -- inline `hrep` at MFF:66–69
```
With these the theorem is `eq_div_iff` + 5 lines. Mathlib: `Filter.Germ.coe_eq`, `map_mul toGermRingHom`.

**L32 `MeromorphicField.toFun_precomp`** — `(δ : SL(2, ℤ)) (a : MeromorphicField) : toFun (precomp δ a) = fun τ ↦ toFun a (δ • τ)`; provable in ≈ 10 lines from `meromorphicNFOn_slash_zero` (NormalFormSlash.lean:87) + `eqOn_toNF_of_meromorphicNFOn` (MeromorphicField.lean:560) + L28 `SL_slash_zero`. No current site (FieldAction never states it); it is the missing link for (a) ring operations on `ModularFunction` (§3), (b) `precomp_toMeromorphicField (f : ModularFunction Γ) (hγ : γ ∈ Γ) : precomp γ f.toMeromorphicField = f.toMeromorphicField` (fixed-field form of 11.9(ii)), (c) replacing the `precomp_algebraMap` detours at UHPFF.lean:118–125, :252–261.

**L33 `IsOfExponentialGrowth.{of_isBoundedAtImInfty, mono, const, add, mul, neg, sub, smul, pow, congr_atImInfty}`** — none exist (only `.slash`, GrowthAtCusp.lean:24). No site hand-rolls them today *because* Cox works with `CuspData` instead of `ModularFunction` (see §3). Recommended: redefine `IsOfExponentialGrowth f := ∃ ρ ≥ 0, f =O[atImInfty] fun τ ↦ (Real.exp (ρ * τ.im) : ℂ)` (batch D scratch-verified it typechecks) so that `add` = `IsBigO.add` after `mono`, `mul` = `IsBigO.mul` + `Real.exp_add`, `slash` = `IsBigO.comp_tendsto` (deletes the manual `∃ M A` unpacking at CuspGrowth.lean:96–104, GrowthAtCusp.lean:36–42, NormalFormGrowth.lean:43–64) and the `‖exp(-ρ·im) * f‖` normalisation copied 4× (CuspGrowth.lean:40–41, :100–101; GrowthAtCusp.lean:40–41; NormalFormGrowth.lean:61–63 → one `@[simp] norm_exp_neg_mul_im_mul`).

**L34 `OnePoint.isOfExponentialGrowthAt_of_forall_SL2Z`** (analogue of mathlib `isBoundedAt_iff_exists_SL2Z`, BoundedAtCusp.lean:94)
```lean
lemma OnePoint.isOfExponentialGrowthAt_iff_exists_SL2Z (hc : IsCusp c 𝒮ℒ) :
    c.IsOfExponentialGrowthAt f ↔ ∃ γ : SL(2, ℤ), γ • ∞ = c ∧ IsOfExponentialGrowth (f ∣[(0 : ℤ)] γ)
lemma OnePoint.isOfExponentialGrowthAt_of_forall_SL2Z (hc : IsCusp c 𝒮ℒ)
    (h : ∀ γ : SL(2, ℤ), IsOfExponentialGrowth (f ∣[(0 : ℤ)] γ)) : c.IsOfExponentialGrowthAt f
```
(4 lines from `isCusp_SL2Z_iff'` + `isOfExponentialGrowthAt_iff`, GrowthAtCusp.lean:68.) Sites: JInvariant.lean:48–54, Congruence.lean:126–140, Construction.lean:269–277, Cox/ModularFunction.lean:56–60 (bounded twin) — 5–15 lines each → 1. ≈ 25 lines. Home: GrowthAtCusp.lean.

### 1.8 Order bookkeeping

**L35 `analyticOrderAt_const_mul_pow` + `meromorphicOrderAt_comp_const_mul_pow`**
```lean
lemma analyticOrderAt_const_mul_pow (hc : c ≠ 0) (r : ℕ) : analyticOrderAt (fun q : ℂ ↦ c * q ^ r) 0 = r
lemma not_eventuallyConst_const_mul_pow (hc : c ≠ 0) (hr : r ≠ 0) : ¬ EventuallyConst (fun q : ℂ ↦ c * q ^ r) (𝓝 0)
lemma meromorphicOrderAt_comp_const_mul_pow (hF : MeromorphicAt F 0) (hc : c ≠ 0) (hr : r ≠ 0) :
    meromorphicOrderAt (F ∘ fun q ↦ c * q ^ r) 0 = r * meromorphicOrderAt F 0
```
Sites: CoxMatrices/LaurentExpansion.lean:151–160 (`hsuborder`+`hφnc`) and :161–182 (`hcompOrder`); LaurentQExpansion.lean:287–293 (`horderPow`+`hg_nc`, `c = 1`) and :294–298. ≈ 35 lines; both are the order half of L14. Mathlib: `analyticOrderAt_mul` (Analytic/Order.lean:444), `analyticOrderAt_pow` (:455), `analyticOrderAt_id`, `AnalyticAt.analyticOrderAt_eq_zero`, `eventuallyConst_iff_analyticOrderAt_sub_eq_top` (:80), `MeromorphicAt.meromorphicOrderAt_comp` (Order.lean:810).

**L36 `meromorphicOrderAt_const_mul_pow` / `meromorphicTrailingCoeffAt_const_mul_pow`**
```lean
lemma meromorphicOrderAt_const_mul_pow (hG : MeromorphicAt G x) (ha : a ≠ 0) (m : ℕ) :
    meromorphicOrderAt (fun q ↦ a * G q ^ m) x = m * meromorphicOrderAt G x
lemma meromorphicTrailingCoeffAt_const_mul_pow (hG) (m) :
    meromorphicTrailingCoeffAt (fun q ↦ a * G q ^ m) x = a * meromorphicTrailingCoeffAt G x ^ m
```
Site: Cox/ModularFunction.lean:174–188 (15 → 2). Mathlib: `meromorphicOrderAt_mul_of_ne_zero` (Order.lean:863), `meromorphicOrderAt_pow`, `MeromorphicAt.meromorphicTrailingCoeffAt_mul` (TrailingCoefficient.lean:395), `meromorphicTrailingCoeffAt_const` (:153), `_pow` (:495). Also publicise `meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq` (:96–130, generic, mathlib candidate).

**L37 `∏ (X − C c)^e` pole-clearing lemma**
```lean
lemma mdifferentiableAt_polynomialIn_mul_of_finite {f g : ℍ → ℂ} (hg : MDiff g) (S : Finset ℍ) (e : ℍ → ℕ)
    (hS : ∀ τ ∈ S, MDiffAt (fun z ↦ (g z - g τ) ^ (e τ + 1) * f z) τ) (hoff : ∀ τ ∉ S, MDiffAt f τ) (τ : ℍ) :
    MDiffAt (fun z ↦ (∏ σ ∈ S, (X - C (g σ)) ^ (e σ + 1)).eval (g z) * f z) τ
```
Site: Cox/ModularFunction.lean:364–395 (32 lines of `Finset.mul_prod_erase` + `funext; ring`) → ≈ 10; the lemma itself ≈ 15 lines and is reusable for any pole-clearing by a holomorphic `g`.

**L38 "SL₂(ℤ)-invariant + `MDiffAt` on `fd` ⇒ `MDiff`"**
```lean
lemma MDifferentiable.of_forall_smul_eq_of_fd {H : ℍ → ℂ} (hinv : ∀ (γ : SL(2, ℤ)) τ, H (γ • τ) = H τ)
    (hfd : ∀ τ ∈ ModularGroup.fd, MDiffAt H τ) : MDiff H
```
Site: Cox/ModularFunction.lean:403–415 (13 → 2). Mathlib: `ModularGroup.exists_smul_mem_fd`, `UpperHalfPlane.mdifferentiable_smul` (Manifold.lean:119).

### 1.9 Lattices / uniqueness

**L39 `PeriodPair.smul_lattice_eq_span` + `periodPair_ω₁/ω₂` + `mem_periodPair_lattice` (public)**
```lean
@[simp] lemma UpperHalfPlane.periodPair_ω₁ (τ : ℍ) : (periodPair τ).ω₁ = 1
@[simp] lemma UpperHalfPlane.periodPair_ω₂ (τ : ℍ) : (periodPair τ).ω₂ = τ
lemma UpperHalfPlane.mem_periodPair_lattice : x ∈ (periodPair τ).lattice ↔ ∃ m n : ℤ, x = m + n * τ  -- LatticeJ:402 private
lemma PeriodPair.smul_lattice_eq_span (a : ℂˣ) (L : PeriodPair) :
    (a • L).lattice = Submodule.span ℤ {(a : ℂ) * L.ω₁, (a : ℂ) * L.ω₂}
```
Sites: Classification.lean:261–278 (18 → 4), :237, :243, :270, :274 and LatticeJ.lean:177, :257, :260, :405 (`simp [UpperHalfPlane.periodPair]` ×8), LatticeJ.lean:454–498 and :500–539 (`mem_smul_lattice` ×5 + `mem_periodPair_lattice_aux` ×6 obtain-blocks). ≈ 35 lines. Mathlib: `PeriodPair.lattice = span ℤ {ω₁, ω₂}` (Elliptic/Weierstrass.lean:79), `Submodule.mem_span_pair`, `Submodule.span_image`.

**L40 `AnalyticAt.eventuallyEq_of_iteratedDeriv_eq`** — `(hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) (h : ∀ n, iteratedDeriv n f x = iteratedDeriv n g x) : f =ᶠ[𝓝 x] g`. Site: uniqueness.lean:228–235 (`weierstrassP_eventuallyEq`, ℘-specific). Mathlib composes it from `AnalyticAt.hasFPowerSeriesAt`, `HasFPowerSeriesAt.eventually_hasSum_sub` (Analytic/Basic.lean:326), `HasFPowerSeriesAt.factorial_smul` (FDeriv/Analytic.lean:843) but has no packaged lemma (searched `eventuallyEq_of_iteratedDeriv`, `eq_of_iteratedFDeriv`: none) — upstream.

### 1.10 q-expansion odds and ends

**L41 `qExpansion_const`, public `qExpansion_qParam_pow`, `qExpansion_qpow_mul`, `laurentqExpansion_qParam_pow`**
```lean
@[simp] lemma qExpansion_const (h : ℝ) (a : ℂ) : qExpansion h (fun _ ↦ a) = PowerSeries.C a   -- Algebra.lean:219–223 inline
lemma qExpansion_qParam_pow (hh : 0 < h) (n : ℕ) : qExpansion h (fun τ ↦ 𝕢 h τ ^ n) = X ^ n  -- Algebra.lean:77 private
lemma qExpansion_qpow_mul (hh) (hf) (n) : qExpansion h (fun τ ↦ 𝕢 h τ ^ n * f τ) = X ^ n * qExpansion h f  -- :94 private
lemma laurentqExpansion_qParam_pow (hh) (n : ℕ) : laurentqExpansion h (fun τ ↦ 𝕢 h τ ^ n) = HahnSeries.single (n : ℤ) 1
```
Consumers: jfunction.lean:449–451 (`cuspFunction_qpow_mul_eq` with `n = 1`), CoxMatrices/LaurentExpansion.lean:191–193, LatticeJ.lean:621; mathlib has `qExpansion_zero/one` (QExpansion.lean:500/515) but no `_const`/`_qParam`.

**L42 `ResToImagAxis` companions** — `@[simp] resToImagAxis_of_pos (ht : 0 < t) : F.resToImagAxis t = F ⟨I * t, _⟩` (16 unfold sites: ResToImagAxis.lean:96,102,106,110,118,130,253,255,282,388,394,402; Eisenstein.lean:474,542; Delta.lean:331,370), public `_add/_mul/_smul_apply` (private :100–110) and missing `_neg/_sub/_pow/_zero/_one/_const_apply` (`Real.neg` :127–130 re-does it inline).

**L43 `UpperHalfPlane.natScale`** (July item, still open) — see §0; `jN`, `qjN`, `natScaleUpperHalfPlane`, `zN` all re-create `⟨N * τ, _⟩`; use mathlib `posRealAction` (`(⟨N, _⟩ : {x : ℝ // 0 < x}) • τ`, Basic.lean:197, `pos_real_im` :210).

**L44 `HolomorphicFunction.ext`** **[verified]** `(h : ∀ τ, f.1 τ = g.1 τ) : f = g` (+ `FunLike HolomorphicFunction ℍ ℂ` and `@[simp] evaluation_apply`). Sites: `congrArg (fun f : HolomorphicFunction ↦ f.1 _)` at UHPFF.lean:81, :239, ModularFunctionField.lean:100; `apply Subtype.ext; funext` at UHPFF.lean:122, :259, Irreducibility.lean:35, Interpolation.lean:457; 18 raw `.1 τ` applications across UHPFF/MFF/Irreducibility/Interpolation/Arithmetic.

---

## 2. Missing simp lemmas / simp families

Project: 83 `@[simp]` in 19,649 lines. In scope: LaurentQExpansion.lean **0**, Algebra.lean 3, IntegralPowerSeries.lean 1, jfunction.lean **0**, jLevelN.lean 0, Deltaqexpansions.lean 0, qexp_coeffs.lean 0, Cox/ModularFunction.lean 0, CuspData.lean 0, LevelJ.lean 3, ModularFunctions/Basic.lean 2, MeromorphicField.lean 8, FieldAction.lean 3, Congruence.lean 2, CuspGrowth/GrowthAtCusp/Cusps 0, ResToImagAxis.lean 2, Eisenstein.lean 3, Delta.lean 0, LatticeJ.lean 6. Manual `simp [def]`/`unfold` sites of core definitions: 66 (LaurentQExpansion 19, ResToImagAxis 12, jfunction 6, Algebra 5, Cox/ModularFunction 5, IntegralDescent 4, CuspData 4, DiagonalLaurent 3, Eisenstein 2, LaurentExpansion 2, jLevelN/MeromorphicField/IntegralPowerSeries/Construction 1 each).

| Definition | simp lemmas that EXIST | MISSING (proposed `@[simp]`) | manual `simp [def]`/`unfold` sites they replace |
|---|---|---|---|
| `poleOrder` (LQE:236) | none | `poleOrder_const/_zero/_one` (= 0), `poleOrder_neg`; non-simp: `poleOrder_of_analyticAt`, `poleOrder_eq_iff` | LQE:246, 257, 402, 411, 451, 499 (6) |
| `poleRemoved` (LQE:316) | none | `poleRemoved_apply : poleRemoved h f τ = 𝕢 h τ ^ poleOrder h f * f τ` (rfl), `poleRemoved_of_poleOrder_eq_zero` (L9) | LQE:382, 428, 437, 444, 596; Algebra:120; jfunction:480; LaurentExpansion:190 (8) |
| `to_qExpansion` (LQE:321) | none | `to_qExpansion_coeff : (to_qExpansion h f).coeff n = (qExpansion h (poleRemoved h f)).coeff n` (rfl), `to_qExpansion_const`, `to_qExpansion_of_poleOrder_eq_zero : … = qExpansion h f` | LQE:536, 597, 704; Algebra:380; jfunction:484; LaurentQExpSimpTests:18, 25, 50, 55, 60 (10) |
| `laurentqExpansion` (LQE:326) | `laurentqExpansion_const/_zero/_one` (Algebra:214/227/232) | `laurentqExpansion.coeff_neg_poleOrder_add` (LHS `coeff (-(poleOrder h f) + n)`), `coeff_neg_poleOrder`, `coeff_eq_zero_of_lt` (conditional), `laurentqExpansion_qParam_pow` (L41), `laurentqExpansion_nat_mul` (L13) | LQE:450, 597; Algebra:136 (3) + 8 `rw` sites in Cox |
| `shiftedLaurent` (Algebra:108, private) | — | none needed if `laurentqExpansion` is parametrised by `N` (recommended: `laurentqExpansionAt (N) (f)` with `laurentqExpansion = laurentqExpansionAt (poleOrder h f)`); otherwise keep private | — |
| `HasCoeffsIn`/`toIntegralPowerSeries` (IPS:51/163) | `powerSeriesMapAlgHom_apply` | `coeff_toIntegralPowerSeries_cast` (L15), `map_toHasCoeffsInPowerSeries` (tag), `coeff_mapAlgHom_ofId` (L17), `hasCoeffsIn_C_algebraMap`/`_X` | IPS:160; link:159, 165, 371; jfunction:227; Deltaqexpansions:251 (6) |
| `qj` (jfunction:239) | none | `qj_apply : qj τ = cexp (2πiτ) * j τ` (rfl), `qj_eq_qParam_mul_j : qj τ = 𝕢 1 τ * j τ`, `qjCoeffs_cast` | jfunction:333, 400, 450, 480; jLevelN:168; LaurentExpansion:192 (6) |
| `jN`/`levelJ` (jLevelN:37, LevelJ:25) | none | `jN_apply`, `levelJ_apply : levelJ N τ = j (natScale N τ)`, `levelJ_one : levelJ 1 = j`, `jN_one` | jLevelN:88, 168, 191; LevelJ:269 (`change`), Arithmetic/Interpolation `change` sites (≥ 4) |
| `ResToImagAxis` (:32) | `resToImagAxis_eq_resToImagAxis`, `resToImagAxis_apply` (both rfl, :40/:43) | `resToImagAxis_of_pos`, `_of_nonpos`, `_add/_mul/_smul/_neg/_sub/_pow/_const_apply`, `Real_iff` | 16 (L42) |
| `ModularFunction.toFun` (Basic:31) | `toSlashInvariantForm_coe`, `toFun_toMeromorphicField`, `coe_restrict`, `coe_ofGamma0CuspData` | `coe_mk`, `coe_ofGamma0Holomorphic`, ring-op `coe_*` (§3) | (ModularFunctionField:166 `change`) |
| `MeromorphicField.toFun/out/toNF` (MF:599/406/539) | `coe_out`, `coe_toNF`, `toFun_ofMeromorphic`, `toFun_ofHolomorphic`, `coe_constRingHom`, `coe_inv`, `coe_div` | `toFun_zero`, `toFun_one`, `toFun_neg`, `toFun_algebraMap` (ℂ), `toFun_precomp` (L32), `ofMeromorphic_toFun` | MF:623 |
| `precomp` (FieldAction:129) | `precomp_algebraMap` | `precomp_one`, `precomp_mul`, `precomp_symm`, `precomp_ofMeromorphic` | UHPFF:118–125, 252–261 |
| `CuspData`/`polynomialIn` (CuspData:30/41) | none | `polynomialIn_apply` (rfl), `polynomialIn_C/_X/_add/_mul/_monomial` (or use `aeval`) | Cox/ModularFunction:217, 389, 422, 428; IntegralDescent:41, 46, 49, 272; DiagonalLaurent:171, 178, 182; CuspData:142, 151; Construction:298 (14) |
| `IsOfExponentialGrowth(At)` (CuspGrowth:26, GrowthAtCusp:50) | none (`smul_iff`, `infty_iff`, `iff` untagged) | tag `isOfExponentialGrowthAt_infty_iff`, `IsOfExponentialGrowthAt.smul_iff` `@[simp]` (mathlib's bounded twins are used by `simp` at BoundedAtCusp.lean:83/98) | NormalFormGrowth:39–40 restates the def; CuspGrowth:90; GrowthAtCusp:27, 32, 77 |

---

## 3. Missing instances / structure (verdicts)

1. **`holomorphicFunctions : Subring (ℍ → ℂ)` → `Subalgebra ℂ (ℍ → ℂ)`** (FieldAction.lean:26). Evidence: batch D scratch — `Algebra ℂ HolomorphicFunction` does not synthesize; UHPFF.lean:36–41 hand-builds `constant : ℂ →+* HolomorphicFunction`; `evalJ := eval₂RingHom constant jElement` (:55) instead of `Polynomial.aeval jElement`; `evalJ_apply` (:63–73, 11 lines) would be `aeval_fn_apply`; three `Algebra _ FunctionField` structures (`HolomorphicFunction`, `RatFunc ℂ`, `ℂ` via `germRing`) with no `IsScalarTower`. Action: `def holomorphicFunctions : Subalgebra ℂ (ℍ → ℂ) where … algebraMap_mem' _ := mdifferentiable_const` (`MDifferentiable.const_smul`, MFDeriv/SpecificFunctions.lean:847 covers `smul_mem`); delete `constant`; `evalJ := aeval jElement`; add `IsScalarTower ℂ HolomorphicFunction MeromorphicField`.
2. **`Algebra R (Filter.Germ l A)`**: mathlib has only `Germ.instModule` (Germ/Basic.lean:656). MeromorphicField.lean:427–448 builds `constRingHom` + `Algebra 𝕜 (germRing 𝕜 U)` (22 lines). Action: upstream `Filter.Germ.instAlgebra [CommSemiring R] [Semiring A] [Algebra R A] : Algebra R (Germ l A)` via `(coeRingHom l).comp (Pi.constRingHom _ _)` (batch D verified `c • a = constRingHom c * a` is `rfl`, so no diamond with `instModule`); then `germRing` becomes `Subalgebra 𝕜 (Germ …)` and `constRingHom/instAlgebra/algebraMap_eq_constRingHom/constRingHom_injective` are deleted.
3. **Ring/field operations on `ModularFunction Γ`** (Basic.lean:31): none — no `Zero/One/Add/Mul/Neg/Inv/SMul ℂ`, no `ModularFunctionClass`. This is the main structural gap: ModularFunctionField.lean:176 (`theorem_11_9_ii`) equates `adjoin (range toMeromorphicField)` with `ℂ(j)(j_N)` but cannot say `range toMeromorphicField` *is* a subfield, and every Cox intermediate expression is carried as raw `CuspData` (24 `.1/.2.1/.2.2` projections) because bundled functions cannot be added or multiplied. Verdict/design: define `ModularFunction.subfield Γ : Subfield MeromorphicField` with carrier `{a | (∀ γ ∈ Γ, precomp γ a = a) ∧ ∀ c, IsCusp c Γ → c.IsOfExponentialGrowthAt (toFun a)}` and `ModularFunction Γ ≃ subfield Γ` (transport via `toFun`/`ofMeromorphic`), then `Field (ModularFunction Γ)` by `Equiv.field`. Ingredients needed: L32 `toFun_precomp` (slash-invariance of transported ops), `precomp_mul/_inv` (§4), L33 growth closure incl. `.inv` (via `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction` + `MeromorphicAt.inv` + L4) and `.congr_atImInfty` (normal-form representative of `f*g` agrees with `f*g` on a high half-plane by NormalFormGrowth.lean:37). Add `class ModularFunctionClass (F) (Γ) extends FunLike F ℍ ℂ, SlashInvariantFormClass F Γ 0` with fields `meromorphicNFOn`, `bdd_at_cusps`.
4. **`MulAction SL(2,ℤ) MeromorphicField` for `precomp`** (FieldAction.lean:129): missing `precomp_one`, `precomp_mul`, `precomp_symm` (grep: none). Consumers: UHPFF.lean (13 sites), Irreducibility.lean (2). Verdict: add `precomp_one : precomp 1 = RingEquiv.refl _`, `precomp_mul : precomp (δ₁ * δ₂) = (precomp δ₂).trans (precomp δ₁)` (from `Germ.compTendsto` functoriality, `mul_smul`), package as `precompHom : SL(2,ℤ) →* (MeromorphicField ≃ₐ[RatFunc ℂ] MeromorphicField)ᵐᵒᵖ`/`MulAction` — the `→*`-to-`AlgEquiv` form is what `IntermediateField.fixedField` needs for the Galois reading of 11.18.
5. **`IsDomain` instead of `NoZeroDivisors`** (FieldAction.lean:72): `Function.Injective.isDomain` (Algebra/Ring/Hom/InjSurj.lean:23) gives `IsDomain HolomorphicFunction` directly (`MeromorphicField` is a field); replace the instance. `MeromorphicField.isDomain` (MeromorphicField.lean:366) is an unused theorem while `instField` exists — delete.
6. **`Fintype`/`DecidableEq`**: `CoxMatrix` has both (CoxMatrices/Basic.lean:105/108); `Gamma0RightCosets` has a noncomputable `Fintype` (:144); `CyclicSublattice L m` has none (`Fintype (CyclicSublattice L m)` should come from `cyclicSublatticeEquivCoxMatrix`, Classification.lean:282) — algebraic scope, noted.
7. **Global `FunLike (ℍ → ℂ) ℍ ℂ`** (qExpansion_lems.lean:73) and **global `SMul ℕ+ ℍ`** (`natPosSMul`, Delta.lean:81): mathlib deliberately has neither; the `FunLike` instance leaks into IsCuspForm/Eisenstein/jLevelN elaboration (bare functions accepted by `SlashInvariantFormClass` lemmas); `natPosSMul` sits in a dead block (Delta.lean:75–149) and collides with the intended `posRealAction`. Verdict: delete both (rebuild to find silent dependents; if any, make the `FunLike` one `scoped` in a `ForMathlib` namespace).
8. **`CuspData` as a `structure`** (CuspData.lean:30, anonymous 3-conjunction): 24 `.1/.2.1/.2.2` sites (Cox/ModularFunction 11, CuspData 8, Interpolation 2, AnalyticSupport 1, CoxMatrices/Basic 1) and 4 `refine ⟨?_, ?_, ?_⟩` constructions. Verdict: `structure CuspData (N : ℕ+) (f : ℍ → ℂ) : Prop where meromorphicOn : ∀ z, 0 < z.im → MeromorphicAt (f ∘ ofComplex) z; slash_eq : ∀ γ : Gamma0 N, f ∣[0] γ = f; cuspFunction_meromorphicAt : ∀ γ : SL(2,ℤ), MeromorphicAt (cuspFunction N (fun τ ↦ f (γ • τ))) 0` + L28/L6 + closure set `zero/one/const/add/sub/neg/const_mul/pow/mul/polynomialIn` (each 6 lines with L1–L5, **[verified for neg/sub]**), replacing the three copies of the 3-bullet template (Cox/ModularFunction.lean:75–94, CuspData.lean:98–113, :137–152).
9. **`@[ext]`**: `ModularFunction.ext` exists (Basic.lean:52). Missing: `HolomorphicFunction.ext` (L44), `MeromorphicField.ext_toFun` (tag `toFun_injective`, MeromorphicField.lean:626, used at MFF:67, :164, UHPFF:51), `CoxMatrix.ext` (algebraic scope).
   **`@[fun_prop]`**: 29 tags, 25 of them in ResToImagAxis.lean on `Prop`-valued *predicates* (`ResToImagAxis.Real/Pos/EventuallyPos`, :52/:59/:67) — `fun_prop` cannot discharge these without a registered predicate class, so the tags are decorative; `Pos.const` (:163) lacks the tag its siblings have; `Differentiable` (:71) carries a non-dischargeable `0 < t` side condition. Hand proofs that `fun_prop` should discharge: NormalFormGrowth.lean:50–53 (`ContinuousAt (fun z ↦ M / exp (-ρ z.im))`, 4 lines → `by fun_prop`), jLevelN.lean:120–121, :188–189 (`DifferentiableAt` of `N * ·`), jfunction.lean:355–357 (`MDiff (cexp (2πi ·))`), LevelJ.lean:284–285 (`AnalyticAt (c * ·^n)`). For the `MDiff` ones, `fun_prop` needs `attribute [fun_prop] MDifferentiable.mul/add/sub/neg/pow/const_smul UpperHalfPlane.mdifferentiable_coe mdifferentiable_smul ModularFunction.j_mdifferentiable levelJ_mdifferentiable` (mathlib tags only 4 lemmas in MFDeriv/SpecificFunctions.lean, none in UpperHalfPlane/Manifold.lean).

---

## 4. API completeness gaps (per definition)

- **`MeromorphicOn.GermRing.orderAt`** (MeromorphicField.lean:457): has `orderAt_coe`, `orderAt_mul`, `orderAt_ne_top`, `eq_zero_iff_forall_orderAt_eq_top`; missing `orderAt_one`, `orderAt_zero = ⊤`, `orderAt_inv = -orderAt`, `orderAt_algebraMap (c ≠ 0) = 0`, `min_le_orderAt_add`, `orderAt_pow`, and the `AddValuation` promised at :482–484 (`AddValuation.of` needs exactly `_one/_mul/_add`). **`divisor`** (:501): has `divisor_coe/_mul/_inv`; missing `divisor_one/_zero/_div/_algebraMap/_pow`. **`toFun`** (:599): missing `toFun_zero/_one/_neg/_algebraMap`, `ofMeromorphic_toFun` (round trip from `coe_toNF`), `ofMeromorphic_eq_iff`, `ofMeromorphic_add/_mul/_sub/_neg` (L31), `toFun_precomp` (L32); `coe_out_mul : ((out a * out b : 𝕜 → 𝕜) : Germ _ 𝕜) = a * b` (inline at :472–473, :519–520, :526).
- **`PeriodPair`** (LatticeJ.lean:33–164): has `smul`, `mem_smul_lattice`, `map_lattice_mulLeftLinearEquiv`, `smulLatticeEquiv`, `G/g₂/g₃/discriminant/j_smul`, `Homothetic`, `j_eq_iff_homothetic`; missing `MulAction ℂˣ PeriodPair` (`one_smul`, `mul_smul`), `smul_lattice_eq_span` (L39), `Homothetic.refl/symm/trans` (a `Setoid`), `periodPair_ω₁/ω₂`, public `mem_periodPair_lattice`, `j_eq_zero_iff`/`j_eq_1728_iff` (private with a redundant `hΔ` at :299/:303), `discriminant_smul` sign lemma. **`CyclicSublattice`** (algebraic file, requested): `map` (:142), `scale` (:190), `dual` (:506) exist with no `map_id/map_map/scale_scale/scale_one/dual_dual/toPeriodPair_ω₁/ω₂` and no `Fintype`; `dual_base_j` (:536) is `rfl`.
- **`precomp`** (FieldAction.lean:129): `precomp_one/_mul/_symm/_ofMeromorphic/toFun_precomp` missing (§3.4, L32).
- **`OnePoint.IsMeromorphicAt`** (Cusps.lean:41): only `isOfExponentialGrowthAt_iff_isMeromorphicAt`; missing `smul_iff`, `infty_iff`, `iff (hg : g • ∞ = c)` (chart independence — provable directly via L13/`meromorphicAt_cuspFunction_of_nat_mul`); used once (Basic.lean:85).
- **`IsOfExponentialGrowth`** (CuspGrowth.lean:26): only `.slash` + two iff's; missing the closure set (L33) and `of_isBoundedAtImInfty`.
- **`laurentqExpansion`**: has `zero/one/const/add/mul/neg/finset_sum/finset_prod/nat_mul_coeff(+_of_not_dvd)/coeff_*`; missing `sub/smul/pow/polynomialIn` (L7), `inv/div` (needs `poleOrder` of an inverse = order of zero — new), `congr`, `qParam_pow` (L41), `order : (laurentqExpansion h f).order = -poleOrder h f` (the sign-flipped `poleOrder_to_order` :552, re-derived at :567 and :578), `leadingCoeff`, `eq_coe_qExpansion_of_analyticAt`, `nat_mul` (L13). External use counts today: `_add` 2, `_mul` 2, `_neg` 1, `_finset_prod` 3, `_finset_sum` 1, `_one` 0, `to_qExpansion_nat_mul` 0, `laurentqExpansion_coeff_eq_circleIntegral` 0, `meromorphicAt_cuspFunction_add` 0, `_nat_mul` 0, `meromorphicAt_of_comp_pow` 0.
- **`poleOrder`**: L8 list; **`poleRemoved`**: `poleRemoved_apply`, L9, L10; **`to_qExpansion`**: `to_qExpansion_coeff`, `_const`, `_of_poleOrder_eq_zero`; dead: `to_qExpansion_ne_zero` (:538), `to_qExpansion_eq_powerSeriesPart` (:571), `laurentqExpansion.coeff_zero` (:490), circle-integral subtree (:600–706).
- **`HasCoeffsIn`/`IsIntegralPowerSeries`**: L15–L19; also `IsIntegralPowerSeries.inv_of_constantCoeff_eq_one` packaging jfunction.lean:221–306 (`integralDeltaOverQ_*`, `qOverDelta_isIntegralPowerSeries_aux`, 60 lines: "unit in ℤ⟦X⟧ ⇒ inverse integral").
- **`qj`**: missing `qj_apply`, public `qjCoeffs_cast`, L21; **`jN/levelJ`**: `levelJ_apply/coe_levelJ`, `levelJ_one = j`, `jN_periodic` (period 1: jLevelN.lean:103–114 proves period `N` where period 1 holds, propagating the exponent `N²` at :146–147), `jN_mdifferentiable` (only `jN_differentiableAt` :184; `levelJ_mdifferentiable` LevelJ:308).
- **`ResToImagAxis`**: L42; two names for one function (:32/:38) with two rfl simp lemmas relating them.
- **`CuspData`**: `add/sub/neg/const/const_mul/pow`, `apply_smul`, `cuspFunction_meromorphicAt_one` (L6), `of_widthM` (L29), `slash_eq` for level one.
- **`ModularFunction`**: ring ops + class (§3.3), `ofGamma0Holomorphic`/`ofSL2ZHolomorphic` (L30), `toMeromorphicField_restrict`, `precomp_toMeromorphicField` (L32), `coe_mk`.

---

## 5. Long-proof collapse map (every proof > 30 lines in scope)

| Proof (file:line, lines) | Collapsing helper(s) | Residual |
|---|---|---|
| Delta.lean:213 `CuspForm_div_Discriminant` (58) | mathlib `CuspForm.divDiscriminant`/`discriminantEquiv` (Step 4) | 0 |
| Eisenstein.lean:471 `E_even_imag_axis_real` (56) | L23 + mathlib `summable_pow_mul_cexp`, `E_qExpansion_coeff` | ≈ 15 |
| Eisenstein.lean:540 `E₂_imag_axis_real` (53) | L23 + `summable_norm_pow_mul_geometric_div_one_sub` | ≈ 15 |
| Cox/ModularFunction.lean:146 `exists_const_poleOrder_sub_mul_pow_lt` (52) | L36 (`const_mul_pow` order/trailing, −15), public `poleOrder_lt_of_neg_lt_meromorphicOrderAt` (L8), `meromorphicTrailingCoeffAt_cuspFunction` naming | ≈ 22 |
| LatticeJ.lean:454 `exists_sl2_smul_eq_of_periodPair_homothetic_aux` (45) | L39 (`smul_lattice_eq_span` + `mem_span_pair`) | ≈ 25 |
| LaurentQExpansion.lean:374 `analyticAt_cuspFunction_poleRemoved` (44) | L10 (`cuspFunction_poleRemoved_eventuallyEq`), require `0 < h` (drop :417 branch), `meromorphicOrderAt_eq_int_iff` + `poleOrder_eq_toNat_neg_meromorphicOrderAt` | ≈ 20 |
| Cox/ModularFunction.lean:352 `exists_polynomial_clearing_poles_on_fd_aux` (44) | L37 | ≈ 18 |
| Cox/ModularFunction.lean:198 `CuspData.polynomialInJ_of_holomorphic` (44) | inductive-step lemma `exists_polynomialIn_of_poleOrder_lt (hf) (hfH) : ∃ a, LevelOneCuspData (f − a·j^m) ∧ MDiff … ∧ poleOrder < m` + `CuspData.sub/const_mul/pow` (§3.8) | ≈ 20 |
| uniqueness.lean:183 `iteratedDeriv_eq_of_invariants` (42) | `PeriodPair.G_four_eq_of_g₂_eq`/`G_six_eq_of_g₃_eq` (hG4/hG6 :188–195), integer-coefficient recursion (drop `hcoef` :216–222) | ≈ 25 |
| CoxMatrices/LaurentExpansion.lean:196 `to_qExpansion_coxAction_aux` (46), :258 `laurentqExpansion_coxAction_coeff_aux` (43), :143 `poleOrder_coxAction_aux` (42) | L14 bridge + L35 | ≈ 5 each (instances) |
| Algebra.lean:290 `hasFPowerSeriesAt_expand_analyticTaylor` (40) | none — this *is* the general engine; generalise to `expand r ∘ rescale c` and upstream (`HasFPowerSeriesAt.comp_const_mul_pow`) | 40 (once) |
| LatticeJ.lean:500 `periodPair_homothetic_of_sl2_smul_aux` (40) | L39 | ≈ 20 |
| Eisenstein.lean:227 `Ek_q_exp` (37) | dead; mathlib `E_qExpansion_coeff` (Step 4) | 0 |
| Eisenstein.lean:609 `norm_tsum_logDeriv_expo_le` (35) | `summable_norm_pow_mul_geometric_div_one_sub` (TsumDivisorsAntidiagonal.lean:69) | ≈ 15 |
| Cox/ModularFunction.lean:96 `meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq` (35) | none (generic mathlib candidate: `meromorphicOrderAt_sub_gt_of_trailingCoeff_eq`); publicise as is | 35 (upstream) |
| LatticeJ.lean:352 `homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux` (35) | `homothetic_of_exists_pow : (∃ c ≠ 0, c^4 • g₂ M = g₂ L ∧ c^6 • g₃ M = g₃ L) → Homothetic L M` (also collapses the two 20-line siblings :313/:334) | ≈ 12 |
| LevelJ.lean:168 `exists_sl2_inv_mul_first_column_gcd_aux` (34) + :212 (30) | public `Matrix.exists_SL2_inv_mul_eq_upperTriangular` in HermiteNormalForm.lean (deletes :159–257) | 0 |
| Algebra.lean:384 `laurentqExpansion_nat_mul_coeff` (33) | L13 (`embDomain_coeff`) | 3 |
| link.lean:284 `inverseOnePlusCoeffsUpTo_toList` (32) | name the loop step function (batch C) | ≈ 20 |
| Cox/ModularFunction.lean:30 `levelOne_constant_of_holomorphic` (32) | L26 (`isBoundedAtImInfty_of_analyticAt_cuspFunction`, −10) + L34 (−5) + L28 (−4) | ≈ 12 |
| uniqueness.lean:105 `key_eventuallyEq` (31) | mathlib `eventuallyEq_nhds_of_eventuallyEq_nhdsNE` (NhdsWithin.lean:432) replaces :130–135 | ≈ 24 |
| LaurentQExpansion.lean:161 `eventually_differentiableAt_pow_mul_of_meromorphicAt_comp_pow_aux` (31) + :194 `meromorphicAt_of_comp_pow` (27) | none local — upstream `meromorphicAt_comp_pow_iff` (mathlib has only `meromorphicAt_comp_iff_of_deriv_ne_zero`, Basic.lean:458); currently 0 external users | 58 (upstream) |

---

## 6. Naming / namespace hygiene that blocks API discovery

1. `laurentqExpansion.*` — 8 lemmas (LaurentQExpansion.lean:447–581) live in the **root** namespace `laurentqExpansion`, not `UpperHalfPlane.laurentqExpansion`, so dot-notation `(laurentqExpansion h f).coeff_of_geq` cannot work; 9 external files (Algebra 7, LaurentQExpSimpTests 8, LaurentExpansion 3, jfunction 2, DiagonalLaurent/Kronecker/LevelThree/IntegralDescent/qexp_coeffs 1 each) spell the full name. Move into `namespace UpperHalfPlane` and rename `coeff_of_geq` → `coeff_of_neg_poleOrder_le`, `coeff_eq_HahnSeries_add` → `coeff_eq_coeff_to_qExpansion_add`, `poleOrder_to_order` → `order_eq_neg_poleOrder` (flip sides), `coeff_of_qExpansion` → `coeff_eq_ite`.
2. `UpperHalfPlane.to_qExpansion` (:321): snake_case def (30 uses in 6 files) → `regularQExpansion`/`poleRemovedQExpansion`.
3. `analyticAt_cuspFunction_of_not_pos` (:359), `cuspFunction_nat_mul_eq_cuspFunction_pow` (:46, allows `m = 0`), `exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt` (:613): junk-value names/statements.
4. `levelJ` (LevelJ.lean:25, 39 uses / 8 files) vs `jN` (jLevelN.lean:37, 17 uses / 3 files): two names for `@jN N ⟨_⟩`; keep one (`jN` with `ℕ+`), add `levelJ_apply`.
5. `E4` (Deltaqexpansions.lean:36; 71 uses / 6 files) vs `E₄` (Eisenstein.lean:55; 6 uses) vs mathlib `ModularForm.E₄`: three names, one object (coe agrees by `rfl`, Deltaqexpansions:43). Step 4: keep mathlib's.
6. `one_le_tprod_nonneg` (multipliable_lems.lean:78) proves `∏' i, g i ≤ 1` — misnamed (`tprod_le_one_of_nonneg`).
7. `qExpansion_injective` (qExpansion_lems.lean:103) is `qExpansion n f = 0 ↔ f = 0` (`_eq_zero_iff`); `qExpansion_mul_coeff` (:53) has no coefficient; `qExpansion_smul2` (:68); `IteratedDeriv_smul`/`IteratedDeriv_zero_fun` (:63/:89 CamelCase).
8. `dual_base_j` (CyclicSublattice.lean:536) is `rfl` and names nothing (`toPeriodPair_j`).
9. `exp_periodo` (exp_lems.lean:25, unused, misspelt), `auxasdf` (Eisenstein.lean:198), `asdf` (:342), `cuspFuntion` (:331), `modfom` (:164), `diffwithinat` (:368), `infSumQj_summable_aux` (jfunction.lean:390).
10. `Filter.eventually_atImInfty` (AtImInfty.lean:14): ℍ-specific lemma in the `Filter` namespace (used at ResToImagAxis.lean:353) → `UpperHalfPlane.eventually_atImInfty` (upstream candidate).
11. Project theorems declared into mathlib namespaces: `Mathlib.Meta.NormNum*` (NormNumI.lean:15, vendored sphere-packing tactic — clash risk on bump), `ModularGroup.modular_negI_sq/_inv` (SlashActionAuxil.lean:38/41), `SlashInvariantForm.mul_apply` (DimensionFormulas.lean:88), `SlashInvariantFormClass.cuspFunction` (qExpansion_lems.lean:110, alias of `UpperHalfPlane.cuspFunction`), `namespace SlashInvariantForm` (CuspPeriod.lean:46, Cusps.lean:76 — acceptable only if the file is a `ForMathlib` file destined upstream; otherwise use `XYin.`-prefixed or `UpperHalfPlane.`), `Complex.im_tprod_eq_zero_of_im_eq_zero`/`Complex.im_finset_prod_…` (Delta.lean:304–326), `Complex.I_pow_six`, `PowerSeries.coeff_add` (Eisenstein).
12. `coeToComplexPowerSeries.ringHom` (IntegralPowerSeries.lean:107): dotted def name inside no namespace; `IsIntegralPowerSeriesmod` (:173); `powerSeriesMapAlgHom` = `PowerSeries.mapAlgHom (Algebra.ofId _ _)` rename.
13. Duplicate private names across files: `cuspFunction_mul_eventuallyEq` (LaurentQExpansion.lean:79 = CuspData.lean:86, byte-identical), `cuspFunction_const` (Algebra.lean:40) vs `cuspFunction_const_eventuallyEq` (LaurentQExpansion.lean:90); `natScaleUpperHalfPlane` (LevelJ:29) ≈ `zN` (CoxMatrices/Basic:725) ≈ the anonymous point in `jN`.
14. `Cox.polynomialIn P g` (CuspData.lean:41) shadows the mathlib concept `Polynomial.aeval g P`; `RationalIn`/`RationalInTwo` (:48/:56) are fine but should mention `RatFunc` in docstrings.
15. `ResToImagAxis` (root, :32) vs `Function.resToImagAxis` (:38): keep only the dot-notation one.
16. `theorem_11_9_i/_ii` (Cox/ModularFunction.lean:431, ModularFunctionField.lean:176): theorem numbers as names (fine for a thesis index file, but give each a descriptive alias: `levelOne_rationalIn_j`, `gamma0ModularFunctionField_eq_jLevelFunctionField`).

---

## 7. Priority (top 12 by impact)

1. **L1–L4 transport lemma family** — 13 sites, ≈ 85 lines, 4 privates deleted, all future closures free **[verified]**.
2. **L14 `substMonomial` bridge** — one theorem subsumes Algebra.lean:343–439 + LaurentQExpansion.lean:46–66/147–159/275–312 + CoxMatrices/LaurentExpansion.lean:93–300 (≈ 210 net lines; residual = the two `hφ` identities).
3. **L7 `laurentqExpansion_polynomialIn/_pow` + L5** — deletes two verbatim 20-line inductions (IntegralDescent/DiagonalLaurent), 4 privates, ≈ 55 lines.
4. **L29 `LevelOneCuspData.of_widthM` + L30 `ofGamma0Holomorphic/ofSL2ZHolomorphic`** — Construction/Interpolation/LevelJ/JInvariant, ≈ 80 lines, 9 privates/defs.
5. **L20–L22 canonical `jIntCoeff`** — move `jIntCoeff_eq_zero_of_lt`, drop the `-(a²) ≤ k` clause, publish the two private bridges (5 re-proofs), explicit witness removes a `Classical.choose`.
6. **§3.8 `CuspData` structure + L28 `apply_smul`/`SL_slash_zero_eq_iff` + closure set** — 24 projection sites, 15 slash-idiom sites, 3 template copies **[verified]**.
7. **L15/L17/L18/L19 IntegralPowerSeries cast lemmas** — 13 sites, ≈ 35 lines, 2 privates; plus delete the two mathlib renames.
8. **L26 `tendsto_atImInfty_of_analyticAt_cuspFunction` family** — 4 sites, ≈ 25 lines, mathlib gap.
9. **L32 `toFun_precomp` + L33 growth closure + L34 `isOfExponentialGrowthAt_of_forall_SL2Z` + §3.3 field ops on `ModularFunction`** — unlocks the subfield form of 11.9(ii) and bundled Cox arithmetic (4 immediate sites, ≈ 25 lines).
10. **L35/L36 order lemmas** (`analyticOrderAt_const_mul_pow`, `meromorphicOrderAt_comp_const_mul_pow`, `_const_mul_pow` order/trailing) — 5 sites, ≈ 50 lines.
11. **L13 `laurentqExpansion_nat_mul` as `embDomain`** **[verified 8 lines]** + L41 `qExpansion_const/qParam_pow` public + L9–L12 `poleRemoved`/`coeff_of_geq'` helpers (≈ 40 lines, 12 test-file sites).
12. **§2 simp families** (`poleRemoved_apply`, `coeff_neg_poleOrder_add`, `resToImagAxis_of_pos`, `polynomialIn_apply`, `qj_apply`, `levelJ_apply`, `periodPair_ω₁/ω₂`, `precomp_one/_mul`) — 66 manual unfold sites; and L39 `PeriodPair.smul_lattice_eq_span` (≈ 35 lines) / L24 `S_smul_eq` (4 sites) **[verified]**.
