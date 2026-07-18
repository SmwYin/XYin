# /mathlibable report — `Cox.card_coxMatrix`

Date: 2026-07-17 · mathlib pin 2026-05-28 · project: XYin (branch PhD_Experiment)

---

### Baseline (Phase 0)
- lake build:               ✓ clean (`Build completed successfully (3909 jobs)`)
- decl `Cox.card_coxMatrix`: ✓ resolved at `XYin/PhD/Cox/CoxMatrices/Cardinality.lean:291`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "Cardinality of the Cox representatives — this file proves Cox's Euler-product formula for the cardinality of `C(m)`."

---

### Statement (Phase 1)

`Cox.card_coxMatrix` is a theorem stating the following:

Let `C(m)` be Cox's set of primitive upper-triangular matrices of determinant `m`
— triples `(a, b, d)` with `a, d > 0`, `ad = m`, `0 ≤ b < d`, `gcd(a, b, d) = 1`
(structure `Cox.CoxMatrix m`, `Basic.lean:24`). Then

  |C(m)| = m · ∏_{p | m} (1 + 1/p),

the classical cardinality formula of Cox, *Primes of the form x² + ny²*, Lemma 11.11
(pp. 228–229; cf. `.mathlib-quality/decomposition.md` §D1). The right-hand side is
the **Dedekind psi function** ψ(m).

Variables / typeclasses (Lean side):
- `m : ℕ+` — the determinant / level; arbitrary positive natural.

Hypotheses (Lean side): none beyond `m : ℕ+`.

Conclusion (math): the cardinality of the Cox matrix set equals ψ(m) = m∏_{p|m}(1+1/p).

Conclusion (Lean):
```lean
(Fintype.card (CoxMatrix m) : ℚ) = (m : ℚ) * ∏ p ∈ (m : ℕ).primeFactors, (1 + 1 / (p : ℚ))
```
Note the statement is cast to `ℚ` "to keep the displayed Euler product literal"
(docstring). The proof route: a fibration `CoxMatrix m ≃ Σ d ∣ m, {b : Fin d // coprimality}`
(Cox-specific), then a private multiplicative arithmetic function
`coxDivisorSumAux n = ∑_{d∣n} (d / gcd(n/d, d)) · φ(gcd(n/d, d))` with
multiplicativity, prime-power value `p^e + p^{e−1}`, and the ℚ Euler-product cast
— i.e. a complete anonymous re-development of ψ (lines 126–287, all `private`).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is the main result of its file (module docstring: "This file proves Cox's
Euler-product formula") and it is a named literature result (Cox Lemma 11.11; the count
is the Dedekind psi function, the index formula [SL₂(ℤ):Γ₀(m)] = ψ(m) of
Diamond–Shurman Ex. 1.2.3). Literature width is EXHAUSTIVE regardless.

### One-line check (Phase 2b)

n/a — kind is theorem (multi-line calc proof). No one-liner check applies.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Dedekind psi function" definition multiplicative n product (1+1/p) primes dividing n | yes | ψ(n) = n∏_{p∣n}(1+1/p), multiplicative, introduced by Dedekind for modular functions | [Wikipedia: Dedekind psi function](https://en.wikipedia.org/wiki/Dedekind_psi_function), [OeisWiki](https://oeis.org/wiki/Dedekind_psi_function) |
|  2 | WebSearch (general form)         | index of congruence subgroup Gamma0(N) in SL2(Z) formula N product (1+1/p) proof | yes | [SL₂(ℤ):Γ₀(N)] = N∏_{p∣N}(1+1/p) = ψ(N) | [K. Conrad, SL2(Z)](https://kconrad.math.uconn.edu/blurbs/grouptheory/SL(2,Z).pdf), [Sage arithgroup docs](http://match.stanford.edu/reference/arithgroup/sage/modular/arithgroup/congroup_gamma0.html) — the group-theoretic incarnation of the same count |
|  3 | WebSearch (aliases / convolution forms) | Dedekind psi Dirichlet convolution mu^2 identity psi = id * mu^2 Jordan totient J_2/J_1 | yes | ψ = id ∗ μ² ; ψ = J₂/J₁ ; ψ(n) = n∑_{d∣n} μ(d)²/d ; ψ = σ on squarefree n | [OEIS A001615](https://oeis.org/A001615), [Tóth–Zsákó subgroup-counting survey, arXiv:2407.14511](https://arxiv.org/pdf/2407.14511) |
|  4 | ChatGPT MCP (gpt-5.4)            | standard name/form/generality of the count of primitive [[a,b],[0,d]], ad=m, b<d, gcd=1; historical evolution; canonical library statement | yes | Confirms ψ(m); equivalent forms ∏(p^k+p^{k−1}), ∑_{d∣m} d·μ²(m/d), id∗μ², J₂/J₁, [SL₂(ℤ):Γ₀(m)], # cyclic index-m sublattices of ℤ². History: Dedekind's context was modular (η-transformations); the multiplicative-arithmetic-function packaging is modern. Canonical library form: **ℕ-valued** `card = ψ(m)` with ψ an `ArithmeticFunction`; ℚ Euler product as derived corollary; the coset equivalence C(m) ≃ Γ₀(m)\SL₂(ℤ) is the fundamental structural statement | full answer in session; matches Phase 4c conclusion |
|  5 | Local references                 | `.mathlib-quality/references/` absent; checked `decomposition.md` §D1 (quotes Cox pp. 228–229: `\|C(m)\| = m∏_{p\|m}(1+1/p)`, "one-to-one correspondence" with Γ₀(m)\SL₂(ℤ)) and prior analyses `overview/analysis/step6-generalization.md` §G2, `step4-coxmatrices.md` | yes | Cox Lemma 11.11; G2 already identifies the sum as Dedekind ψ, "strong upstream candidate", OEIS A001615 | references dir absent → fell back to project planning docs, which quote the source verbatim |
|  6 | nLab                             | fetched `ncatlab.org/nlab/show/Dedekind+psi+function` + site search "Dedekind psi" | no | 404; site search: "No pages contain 'Dedekind psi'" | nLab has no page on this function — checked, not skipped |
|  7 | nCatLab (categorical)            | same search as #6 | n/a | — | not a categorical concept; nLab search confirmed empty |
|  8 | Stacks Project                   | — | n/a | — | elementary multiplicative number theory / modular curves over ℂ; Stacks covers scheme-theoretic AG, no arithmetic-function content |
|  9 | MathOverflow / Math.StackExchange | mathoverflow OR math.stackexchange "Dedekind psi" number of cyclic subgroups index n Z^2 OR "Gamma_0" index | yes | c₂-cyclic-subgroup count: for ℤ², the number of cyclic-quotient index-n sublattices is ψ(n); [SL₂(ℤ):Γ₀(N)] = ψ(N) confirmed | results routed to arXiv survey [2407.14511](https://arxiv.org/pdf/2407.14511) which is the authoritative modern treatment |
| 10 | recent arXiv (last 5 years)      | (via #3, #9) Tóth–Zsákó "Counting subgroups of ℤ_{n₁}×⋯×ℤ_{n_k}: a survey" (2024, arXiv:2407.14511); "Arithmetic Functions and Geometry" (arXiv:2504.13328, 2025) | yes | modern usage unchanged: ψ = id∗μ², cyclic-sublattice count, Γ₀ index | the 2×2 case of the general subgroup-counting theory; no more general "standard form" beyond the ones in #3/#4 |

### Literature summary (Phase 3)

Concept identified as: **Dedekind psi function ψ(n)** (OEIS A001615), equivalently the
index formula **[SL₂(ℤ) : Γ₀(n)] = ψ(n)**.
Sources agree on the standard form: **yes** — all channels give the same function with the
same equivalent presentations.
Most general standard form: ψ is the multiplicative arithmetic function with
ψ(p^e) = p^e + p^{e−1}; equivalently ψ = id ∗ μ² (Dirichlet convolution),
ψ(n) = n∏_{p∣n}(1+1/p), ψ = J₂/J₁. Its primary combinatorial meanings: number of
cyclic-quotient (primitive) sublattices of index n in ℤ², and [SL₂(ℤ):Γ₀(n)].
Generality dimensions where the literature varies:
  - value codomain: ℕ-valued arithmetic function (canonical) vs ℝ/ℚ Euler product (display form);
  - packaging: divisor sum vs prime-power factorization vs Dirichlet convolution id∗μ² vs Jordan-totient quotient — all standard, all interderivable;
  - k-generalization: ψ is the k = 2 instance of the cyclic-sublattice count for ℤ^k (Tóth–Zsákó); the literature does NOT treat the k-general version as the default named object — ψ itself is the standard citizen.
Disagreement with the literature: the project's form is ℚ-valued and leaves ψ anonymous
(a `private` divisor sum); the literature-canonical object is the *named* ℕ-valued
multiplicative function.

---

### Generality analysis — `Cox.card_coxMatrix` (Phase 4a)

Literature-standard form: `Fintype.card (CoxMatrix m) = ψ(m)` with ψ the named ℕ-valued
multiplicative arithmetic function; ℚ Euler product as corollary.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|--------------------------------|
| 1 | `m : ℕ+`               | arbitrary positive natural | arbitrary positive natural | NO | already fully general; no squarefree/`1 < m` restriction anywhere (confirmed also by step6 §K1) |
| 2 | conclusion codomain `ℚ` | ℚ-cast equality with literal Euler product | ℕ-valued equality against named ψ | **yes (strengthening)** | the ℕ-valued `Fintype.card (CoxMatrix m) = ψ m` is *stronger* (implies the ℚ form by casting + Euler-product lemma); the private proof already establishes it at `card_coxMatrix_eq_divisorSum_aux` before the cast |
| 3 | subject `CoxMatrix m`  | project-specific structure | Γ₀(m)\SL₂(ℤ) coset space (mathlib-facing) | yes (re-aim) | project already has `coxMatrixEquivRightCosets` (Basic.lean); the mathlib-facing statement is `(Gamma0 m).index = ψ m` — mathlib has `CongruenceSubgroup.Gamma0` + `instFiniteIndexGamma0` but no index value |

### Generality verdict (Phase 4b)

There are **no hypotheses to drop** — the sole parameter is `m : ℕ+` with no side
conditions, so the mechanical-weakening verification is vacuous (nothing to weaken;
no `lean_diagnostic_messages` run needed because no candidate edit exists). The
current form is: **MAXIMALLY GENERAL** in the hypothesis-weakening sense.
Number of weakening opportunities found: 0 (hypothesis side); 2 restatement
opportunities (rows 2–3 above) — handled under Phase 4c, not 4b.
Cost of restatement: n/a here (see 4c).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|--------------------------------|
| 1 | Typeclass-ify preambles | no | — | no bundled hypotheses; single `ℕ+` parameter |
| 2 | Filters vs sequences | no | — | finite combinatorial identity; no topology |
| 3 | Universal-property class | no | — | a numerical count, not a construction |
| 4 | Bundled substructure | no | — | no closure predicate involved |
| 5 | Weaken concrete typeclass | no | — | statement is about ℕ; no typeclass hierarchy in play |
| 6 | Higher-categorical form | no | — | not categorical |
| 7 | Generalise concrete index | no | — | k-generalization to ℤ^k exists in the literature (Tóth–Zsákó) but ψ itself is the standard named object; mathlib's ArithmeticFunction file family names each classical function individually (ζ, σ, φ, μ, Λ) — ψ at k = 2 is the right grain |
| 8 | **Concrete-via-abstract** | **yes** | Adversarial diagnostic run: grep of the proof pipeline for `CoxMatrix` shows the identifier last appears at `card_coxMatrix_eq_divisorSum_aux` (line 115–124, the fibration `CoxMatrix m ≃ Σ d ∣ m, fiber`). Everything from `coxDivisorTermAux` (line 126) through `cast_coxDivisorSum_eq_eulerProduct_aux` (line 287) — 6 of the 8 supporting lemmas, ~160 lines — never mentions `CoxMatrix`: it is a pure anonymous re-development of ψ (multiplicativity, ψ(p^e) = p^e + p^{e−1}, factorization product, ℚ Euler product) using `ArithmeticFunction` + `IsMultiplicative.multiplicative_factorization`. Abstract restatement: public `ArithmeticFunction.dedekindPsi` with that API; `card_coxMatrix : Fintype.card (CoxMatrix m) = dedekindPsi m` becomes a two-line corollary of the fibration + `dedekindPsi` divisor-sum lemma | mathlib gains ψ next to ζ/σ/φ/μ in `Mathlib/NumberTheory/ArithmeticFunction/`; enables the Γ₀-index formula `(Gamma0 N).index = dedekindPsi N` (mathlib has `CongruenceSubgroup.Gamma0`, `instFiniteIndexGamma0`, but **no index value** — needed downstream for dimension/genus formulas of modular-forms spaces) |
| 9 | False-generalisation guard | no | The proposal keeps the identical mathematical object: `dedekindPsi` is definitionally the same divisor sum / factorization product the file already proves things about; the ℕ-valued statement implies the current ℚ one by `Nat.cast` + the Euler-product lemma. No meaning change | safeguards satisfied |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (Q8).
- Proposed mathlib-idiomatic restatement:
  ```lean
  /- mathlib side: Mathlib/NumberTheory/ArithmeticFunction/DedekindPsi.lean -/
  def ArithmeticFunction.dedekindPsi : ArithmeticFunction ℕ := ...  -- ψ, e.g. via ∑_{d∣n} d·μ²(n/d) or the file's divisor sum
  theorem ArithmeticFunction.isMultiplicative_dedekindPsi : dedekindPsi.IsMultiplicative
  theorem ArithmeticFunction.dedekindPsi_apply_prime_pow (hp : p.Prime) (he : 0 < e) :
      dedekindPsi (p ^ e) = p ^ e + p ^ (e - 1)
  theorem ArithmeticFunction.cast_dedekindPsi_eq_mul_prod (hn : n ≠ 0) :
      (dedekindPsi n : ℚ) = n * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ))
  -- mathlib-facing index formula (via the project's coxMatrixEquivRightCosets):
  theorem CongruenceSubgroup.index_Gamma0 (N : ℕ) [NeZero N] :
      (Gamma0 N).index = ArithmeticFunction.dedekindPsi N

  /- project side (stays local until CoxMatrix/Γ₀-index PR lands): -/
  theorem card_coxMatrix (m : ℕ+) : Fintype.card (CoxMatrix m) = ArithmeticFunction.dedekindPsi m
  theorem card_coxMatrix_ratCast (m : ℕ+) :  -- current statement, now a corollary
      (Fintype.card (CoxMatrix m) : ℚ) = m * ∏ p ∈ (m : ℕ).primeFactors, (1 + 1 / (p : ℚ))
  ```
- Cost: **MODERATE** — mostly re-packaging: 5 of the file's 8 private lemmas become the
  public ψ API with only a name change (step6 §G2 rated it "Medium (mostly re-packaging)");
  the Γ₀-index bridge additionally needs `coxMatrixEquivRightCosets` recast against
  mathlib's `Gamma0` (the project already uses mathlib's coset API for it, per step4).
- Mathlib downstream this enables: (i) ψ joins the `ArithmeticFunction` family with the
  full `IsMultiplicative` machinery; (ii) `[SL₂(ℤ):Γ₀(N)]` gets a value, upgrading
  mathlib's bare `instFiniteIndexGamma0`; (iii) exact precedent pattern exists:
  `Nat.totient_eq_mul_prod_factors : (φ n : ℚ) = n * ∏ p ∈ n.primeFactors, (1 - 1/p)`
  (`Mathlib/Data/Nat/Totient.lean:313`) — ψ's ℚ Euler product mirrors it with `+`.
- Real mathematical improvement: replaces an anonymous private divisor sum + ℚ-cast
  display identity with the named, ℕ-valued, multiplicative object every source treats
  as canonical; the current statement loses information (ℚ equality is weaker than the
  ℕ one) and hides the reusable content behind `private`.

---

### Proof strategy — `Cox.card_coxMatrix` (Phase 4.6a)

| # | Question | Applies? | Idiomatic alternative | Cost of switch |
|---|----------|----------|------------------------|----------------|
| 1 | ε-δ vs filters | no | finite counting; no topology | — |
| 2 | Element-wise vs point-free algebra | no | already argues via `ArithmeticFunction`, `IsMultiplicative.multiplicative_factorization`, `Nat.Coprime.divisors_mul`, `Nat.sum_divisors_prime_pow`, `Nat.sum_totient`, `Nat.totient_mul`, `Nat.totient_prime_pow` — the correct mathlib API throughout (verified in step4 audit) | — |
| 3 | Sequences vs nets | no | — | — |
| 4 | Construction vs universal property | no | — | — |
| 5 | Missing mathlib helpers | **yes** | the missing helper IS `ArithmeticFunction.dedekindPsi` + its API — exactly the Phase 4c package; an alternative derivation via ψ = id ∗ μ² with `ArithmeticFunction.IsMultiplicative.mul` was considered in the step4 audit and rejected (termwise identity costs as much as the direct proof) | file as the upstream PR |

### Proof strategy verdict (Phase 4.6b)

Current strategy: **MATHLIB-IDIOMATIC** (fibration → multiplicative arithmetic function →
factorization product → cast; each step on the canonical mathlib API).
Missing mathlib API: `ArithmeticFunction.dedekindPsi` and its multiplicativity /
prime-power / Euler-product lemmas — the Phase 4c upstream package, not a strategy change.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem**; no definitional equalities or instance paths introduced.
(The proposed upstream `def ArithmeticFunction.dedekindPsi` is a plain `ArithmeticFunction ℕ`
value in the established ζ/σ/φ/μ pattern — no instances, no coercions, no `@[reducible]`;
risk profile identical to `ArithmeticFunction.sigma`.)

---

### Mathlib search-status: `Cox.card_coxMatrix` (Phase 5)

[A] Lean-Finder       "index of the congruence subgroup Gamma0(N) in SL2(Z) equals N times product over primes dividing N of (1+1/p)"  → no hits for a value; only `CongruenceSubgroup.instFiniteIndexGamma0/Gamma1/Gamma` (finiteness, no formula) and `IsCongruenceSubgroup.finiteIndex`
[B] Loogle            `Subgroup.index, CongruenceSubgroup.Gamma0` → empty (no theorem relates the two)
[C] LeanSearch        "Dedekind psi function n times product over prime divisors of (1 + 1/p)" → no ψ; nearest: `ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul`, `Nat.prod_divisors_prime_pow`. "number of subgroups of index n in Z x Z / primitive sublattices" → only `Subgroup.index_eq_card`, Smith-normal-form index lemmas (`Module.Basis.SmithNormalForm.toAddSubgroup_index_eq_pow_mul_prod`) — no counting-by-n results
[D] Grep mathlib src  `dedekind.?psi|dedekindPsi` (case-insensitive) over all of Mathlib → **zero hits**; `psi` in `NumberTheory/ArithmeticFunction/` → zero; `Subgroup.index` in `NumberTheory/ModularForms/` → zero; `sublattice` in `NumberTheory/` → zero; `ArithmeticFunction/` dir contents: Carmichael, Defs, LFunction, Liouville, Misc, Moebius, VonMangoldt, Zeta — no ψ file
[E] Name pattern      grep for decl-name shapes `dedekindPsi`, `psi_apply`, `index_Gamma0`, `Gamma0_index` in `.lake/packages/mathlib` → zero hits (lean_local_search unavailable before file-based tool init; grep over the mathlib source tree is the equivalent exhaustive local check)

Searched for both:
  - the user's current form (ℚ Euler product for a matrix count) — no hit
  - the literature-standard form (named ψ as arithmetic function; [SL₂(ℤ):Γ₀(N)] index value; cyclic-sublattice count) — no hit on any of the three incarnations

Concluded: **not in mathlib (all 5 methods exhausted, plus the literature-standard form)**.
Mathlib has the *framework* (`ArithmeticFunction`, `IsMultiplicative.multiplicative_factorization`,
`Nat.totient` API, `CongruenceSubgroup.Gamma0` + `instFiniteIndexGamma0`) but neither ψ nor any
Γ₀-index value nor any sublattice-counting theorem.

---

### Normal-form check — `Cox.card_coxMatrix` (Phase 5.5a)

Equivalent formalisms this statement could take:
1. ℚ-valued Euler product (current): `(card : ℚ) = m ∏ (1 + 1/p)`
2. ℕ-valued against named ψ: `card = dedekindPsi m`
3. divisor-sum form: `card = ∑_{d∣m} (d / gcd(m/d, d)) · φ(gcd(m/d, d))` (the private aux)
4. factorization form: `card = m.factorization.prod (p^e + p^{e−1})`
5. index form: `card = (Gamma0 m).index`

Does mathlib already have a canonical form for this idea? **No named ψ** — but mathlib's
established convention for this family (φ) makes form 2 the canonical one: `Nat.totient`
is ℕ-valued and primary, with `Nat.totient_eq_mul_prod_factors` as the ℚ Euler-product
corollary. Our statement is currently the *corollary* shape without the canonical anchor.
Proposed canonical form: `Fintype.card (CoxMatrix m) = ArithmeticFunction.dedekindPsi m`
(RHS = normal form — respected).
RHS convention respected? In the proposed restatement, yes (named ψ on the RHS).

### Syntactic generality (Phase 5.5b)

Alternative restatements attempted: the five forms above.
Chosen restatement: form 2 (ℕ-valued vs `dedekindPsi`), with form 1 kept as a corollary.
Justification: ℕ-equality rewrites/casts into every consumer context (ℚ, ℝ, ℂ,
`Nat.card`, index arithmetic), whereas the ℚ form cannot recover the ℕ equality;
and a named ψ makes the multiplicativity/prime-power API applicable at call sites.

### Superfluous-argument audit (Phase 5.5c)

| # | Argument / typeclass | Essentially used? | Notes |
|---|----------------------|-------------------|-------|
| 1 | `m : ℕ+`             | yes               | positivity is essential (`divisors` of 0 is ∅; the count is about determinant m ≥ 1); `ℕ+` matches the `CoxMatrix` structure parameter — no `NeZero`-style relaxation available since `CoxMatrix` itself takes `ℕ+` |

### Statement-shape verdict (Phase 5.5d)

Normal form: REFACTOR (target: ℕ-valued `= dedekindPsi m`)
Syntactic generality: RESTATE (ℕ-valued primary, ℚ corollary)
Superfluous arguments: NONE

Overall: **RESTATE-BEFORE-SHIP**

---

### Call sites — `Cox.card_coxMatrix` (Phase 6.0)

```
grep -rn "\bcard_coxMatrix\b" XYin/ --include="*.lean"   (excluding declaring file, excluding the distinct decl one_lt_card_coxMatrix)
```

Internal use count: **0** (within the project, not counting the declaring file)
External-to-file callers: 0 distinct files

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | — |

Inline-derivation grep: `one_lt_card_coxMatrix` (`Basic.lean:132`, used at `Arithmetic.lean:172`)
proves `1 < Fintype.card (CoxMatrix m)` for `1 < m` *independently* — it does not re-derive the
Euler product (it exhibits two elements), so it is a coarser fact, not an inline re-derivation
of this statement. No inline re-derivations found.

Signal reading: K = 0 for a **theorem that is the terminal main result of its file** (a
literature-named formula, not a helper def) — the "dead code?" row of the signal table does
not apply to result-endpoints; per Phase 2a this is a BIG main result whose value is the
statement itself. Its natural consumer is mathlib's modular-forms development (Γ₀ index),
not the project's downstream files.

### Composition check (Phase 6)

Can `Cox.card_coxMatrix` be derived from mathlib in ≤3 chained calls?

Attempt 1: no candidate sketch exists — the statement's subject `CoxMatrix m` is a
project-local structure; mathlib has no declaration mentioning it, no Dedekind ψ, no
Γ₀-index value, and no cyclic-sublattice count to compose from.
  - Mathlib decls that could serve as blocks: `ArithmeticFunction.*` framework,
    `Nat.totient_mul`, `Nat.sum_divisors_prime_pow`, `Nat.sum_totient` — these are the
    *ingredients of the 170-line proof*, not a ≤3-call composition.
  - Result: **fails** (the file's existing proof is itself the shortest known route and
    uses ~10 mathlib lemmas across 8 helper lemmas with real reasoning between them —
    squarely the "multiple `have`s with non-trivial reasoning" NON-composable pattern).

Conclusion: **NOT-COMPOSABLE**.

---

## Verdict: `Cox.card_coxMatrix`

**Category:** YES-but-generalise-first

**Evidence:**
- Literature search (Phase 3): 10-channel exhaustive protocol; the count is the Dedekind
  psi function ψ(m) (OEIS A001615), canonically an ℕ-valued multiplicative arithmetic
  function, equivalently [SL₂(ℤ):Γ₀(m)]; all sources agree.
- Generality analysis (Phase 4): 4b MAXIMALLY GENERAL (no hypothesis to weaken — vacuous
  verification); 4c **modern idiom available** via Q8 concrete-via-abstract (proof pipeline
  from line 126 onward never mentions `CoxMatrix`; it anonymously re-develops ψ), with Q9
  false-generalisation guard passed.
- Mathlib search (Phase 5): not in mathlib — no ψ, no Γ₀-index value, no sublattice count
  (all 5 methods + both forms).
- Composition check (Phase 6): NOT-COMPOSABLE (project-local subject; mathlib has only the
  framework the 170-line proof is built on).
- Statement shape (Phase 5.5): RESTATE-BEFORE-SHIP (ℕ-valued vs named ψ, per the
  `Nat.totient` precedent).
- Proof strategy (Phase 4.6): MATHLIB-IDIOMATIC; the only missing API is ψ itself.

**Rationale:**

The theorem is a genuine, literature-named result (Cox Lemma 11.11 = the Γ₀-index
formula) whose mathematical content mathlib demonstrably lacks: repo-wide grep and all
search engines confirm mathlib has no Dedekind ψ and — despite having
`CongruenceSubgroup.Gamma0` with a `FiniteIndex` instance — no value for that index. But
the current Lean form is the wrong shipping shape on two counts. First, the statement is
ℚ-cast for display; the ℕ-valued equality it is proved from
(`card_coxMatrix_eq_divisorSum_aux`) is strictly stronger, and mathlib's own convention
for this exact family (`Nat.totient` primary, `Nat.totient_eq_mul_prod_factors` as ℚ
Euler-product corollary at `Mathlib/Data/Nat/Totient.lean:313`) dictates the ℕ-valued
named-ψ form. Second, the Q8 diagnostic fired decisively: 6 of the 8 supporting lemmas
(~160 lines) never mention `CoxMatrix` — they are a private anonymous re-development of
ψ (multiplicativity, ψ(p^e) = p^e + p^{e−1}, factorization product, Euler product). The
reusable content is ψ and its API; the Cox-specific content is one fibration equivalence.

Reason for the generalisation: **MODERN-IDIOM** (Bourbaki 2.0, Q8 concrete-via-abstract),
not literature-weakening — Phase 4b found nothing to weaken and the ℕ-restatement is a
strengthening, not a hypothesis drop, so no mechanical-weakening compile check applies.

Proposed restatement:
```lean
-- mathlib PR 1: Mathlib/NumberTheory/ArithmeticFunction/DedekindPsi.lean
def ArithmeticFunction.dedekindPsi : ArithmeticFunction ℕ := by sorry -- promote coxDivisorSumArithmeticFunctionAux
theorem ArithmeticFunction.isMultiplicative_dedekindPsi : dedekindPsi.IsMultiplicative := by sorry
theorem ArithmeticFunction.dedekindPsi_apply_prime_pow {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    dedekindPsi (p ^ e) = p ^ e + p ^ (e - 1) := by sorry
theorem ArithmeticFunction.cast_dedekindPsi_eq_mul_prod {n : ℕ} (hn : n ≠ 0) :
    (dedekindPsi n : ℚ) = n * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ)) := by sorry

-- mathlib PR 2 (follow-up, the mathlib-facing incarnation of card_coxMatrix):
theorem CongruenceSubgroup.index_Gamma0 (N : ℕ) [NeZero N] :
    (Gamma0 N).index = ArithmeticFunction.dedekindPsi N := by sorry

-- project side, after PR 1: ℕ-valued primary + current statement as corollary
theorem card_coxMatrix (m : ℕ+) :
    Fintype.card (CoxMatrix m) = ArithmeticFunction.dedekindPsi m := by sorry
theorem card_coxMatrix_ratCast (m : ℕ+) :
    (Fintype.card (CoxMatrix m) : ℚ) = m * ∏ p ∈ (m : ℕ).primeFactors, (1 + 1 / (p : ℚ)) := by sorry
```
Estimated cost of regeneralisation: **MODERATE** — the ψ package is 5 of the file's private
lemmas generalized "only by a name" (step6 §G2); the Γ₀-index bridge additionally routes
through the existing `coxMatrixEquivRightCosets` and mathlib's right-coset API already used
by the project. Cost does not affect the verdict bucket.

Mathlib downstream this enables (MODERN-IDIOM, required):
- ψ joins ζ/σ/φ/μ/Λ in `Mathlib/NumberTheory/ArithmeticFunction/` with the full
  `IsMultiplicative` / `multiplicative_factorization` machinery immediately applicable;
- `(Gamma0 N).index` gets a value, upgrading `instFiniteIndexGamma0` from "finite" to
  computed — the standard input to dimension/genus formulas for `Γ₀(N)` modular-forms
  spaces (Diamond–Shurman §3), an active mathlib direction (Cusps.lean is new);
- the ℚ Euler product becomes one corollary in the exact `Nat.totient_eq_mul_prod_factors`
  pattern instead of the primary statement;
- proofs blocked by the old form: nothing outside the project can consume a `private`
  divisor sum about a project structure; the named ψ is consumable by any lattice / modular
  curve / Hecke-operator development (ψ(m) also = degree of the classical Hecke
  correspondence T_m on X₀(m)-related counts).

Next action: run `/generalise card_coxMatrix` (tension against the Phase 3
literature-standard ψ and this 4c target), then split as: PR 1 = `dedekindPsi` API
(self-contained, no project dependencies); PR 2 = `index_Gamma0` (needs the coset
equivalence ported); project keeps `card_coxMatrix` (ℕ-valued) + `card_coxMatrix_ratCast`
locally until/unless `CoxMatrix` itself is upstreamed as the HNF-representative
parametrization of Γ₀(m)\SL₂(ℤ).

---

## Next step

Run `/generalise card_coxMatrix` before any PR: restate ℕ-valued against a new public
`ArithmeticFunction.dedekindPsi` (promoting `coxDivisorSumAux` + its 4 lemmas), keep the
current ℚ Euler product as a corollary, and stage the mathlib contribution as
(1) `dedekindPsi` package, (2) `CongruenceSubgroup.index_Gamma0`.
