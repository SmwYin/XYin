# /mathlibable report — `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq`

Assessed 2026-07-18, mathlib pin 2026-05-28 (commit `2abc2425`).

### Baseline (Phase 0)
- lake build:               ✓ clean (`lake build XYin.uniqueness` — Build completed successfully, 2736 jobs)
- decl `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq`: ✓ resolved at `XYin/uniqueness.lean:319`
- kind:                      theorem
- has sorry:                 no (0 sorries in file)
- module docstring summary:  Uniqueness theorem for complex lattices — a period lattice is determined by its Weierstrass invariants `g₂`, `g₃`, via the Laurent-coefficient recursion for `℘`, the identity theorem on a countable-complement connected set, and pole-order comparison.

### Statement (Phase 1)

`PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq` is a theorem stating the following:

If two rank-2 lattices Λ₁, Λ₂ ⊂ ℂ (given by period pairs L₁, L₂ of ℝ-linearly-independent
complex numbers) have equal Weierstrass invariants — g₂(Λ₁) = g₂(Λ₂) and g₃(Λ₁) = g₃(Λ₂),
where g₂ = 60·G₄ and g₃ = 140·G₆ are the normalised Eisenstein series — then Λ₁ = Λ₂ as
lattices (genuine equality of subgroups of ℂ, not merely homothety). This is the injectivity
half of the uniformization correspondence {lattices} ↔ {(g₂,g₃) : g₂³ − 27g₃² ≠ 0}.

Variables / typeclasses involved (Lean side):
- `L₁ L₂ : PeriodPair` — mathlib's carrier for the Weierstrass theory (a pair of ℝ-independent periods; `L.lattice : Submodule ℤ ℂ` is the spanned lattice)

Hypotheses (Lean side):
- `hg₂ : L₁.g₂ = L₂.g₂` — equality of the weight-4 invariant
- `hg₃ : L₁.g₃ = L₂.g₃` — equality of the weight-6 invariant

Conclusion (math): the two period lattices coincide, Λ₁ = Λ₂.

Conclusion (Lean): `L₁.lattice = L₂.lattice`

Proof pipeline (all in the same file, ~300 lines): (1) the Laurent coefficients of ℘ at 0 are
`(n+1)!·G(n+2)`; (2) from `℘'² = 4℘³ − g₂℘ − g₃` (mathlib's `derivWeierstrassP_sq`) derive
`℘'' = 6℘² − g₂/2` and hence a recursion `(n(n−1)−12)·cₙ = 6n(n−1)·(convolution of earlier cₖ)`;
(3) strong induction: all coefficients are determined by g₂, g₃ (the singular case n = 4 is
handled directly from g₂); (4) equal power series ⇒ `℘[L₁] =ᶠ[𝓝 0] ℘[L₂]`; (5) identity theorem
on the connected, countable-complement set `(Λ₁ ∪ Λ₂)ᶜ` (via `rank ℝ ℂ = 2`); (6) the lattice is
the polar set of ℘ (`order_weierstrassP = −2` vs. `meromorphicOrderAt ≥ 0`), so Λ₁ = Λ₂.

### Size classification (Phase 2a)

Verdict: BIG
Reason: main result of the file (its header names it as the theorem), a classical theorem with a
literature identity ("uniqueness half of the uniformization theorem for elliptic curves over ℂ" /
"modular inversion"), and a known mathlib-roadmap continuation of `Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass`.

(Note: literature width is EXHAUSTIVE regardless; recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 7 (proof) — n/a (kind is theorem, not def)
One-liner verdict: n/a — theorem; check skipped.

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|----------------------|-------|
|  1 | WebSearch (specific form)        | lattice determined by invariants g2 g3 Weierstrass uniqueness theorem  | yes  | "g₂(L), g₃(L) uniquely determine ℘(z;L) and therefore the lattice L where ℘ has poles" | Stevenhagen, *Elliptic Functions* (Leiden notes); Taylor UNC notes; MIT 18.783 Lecture 16 |
|  2 | WebSearch (general form)         | uniformization theorem elliptic curves every (g2,g3) nonzero discriminant unique lattice | yes | "for A,B with 4A³−27B²≠0 there exists a UNIQUE lattice Λ with g₂(Λ)=A, g₃(Λ)=B" | Park (Harvard) uniformization notes; MIT 18.783 Lec 15/16; Schwartz (Brown) Weierstrass-uniformization notes — user's decl is the uniqueness half |
|  3 | WebSearch (named/alias forms)    | ℘ Laurent coefficient recursion "determined by" g2 g3 identity theorem lattice poles | yes | exact proof route: Laurent series of ℘ determined by g₂,g₃ via recursion, lattice = polar set | same sources; also DLMF §23 conventions ℘(z; g₂, g₃) |
|  4 | ChatGPT MCP (gpt-5.4)            | standard name, generality, packaging, historical evolution of "lattice determined by (g₂,g₃)" | yes  | "injectivity of Λ ↦ (g₂(Λ),g₃(Λ)); uniqueness half of complex uniformization / modular inversion". Refs: Whittaker–Watson §§20.22/21.73, Chandrasekharan Ch. 3–4, Lawden §6.7, Silverman AEC VI §5, DLMF §23.3 | Confirms: (a) the ℂ-lattice statement IS the standard form; (b) generalisations (Tate curves, formal groups, algebraic j-classification) are *different theorems*, not more general forms of this one; (c) usually packaged inside the full existence+uniqueness uniformization theorem, uniqueness rarely isolated; (d) historically absorbed into the notation ℘(z; g₂, g₃) |
|  5 | Local references                 | ls `.mathlib-quality/references/`                                      | n/a  | (directory absent)   | recorded n/a — no references dir in this project |
|  6 | nLab                             | site-restricted search: Weierstrass elliptic function, j-invariant, moduli of elliptic curves | yes | nLab "elliptic curve"/"j-invariant": over ℂ, curve determined up to iso by j; Weierstrass uniformization u ↦ (℘(u), ℘'(u)) | nLab states the homothety/j-classification, not the strict-equality injectivity; consistent with #4 |
|  7 | nCatLab (if categorical)         | (same engine as #6)                                                    | n/a  | —                    | not a categorical concept beyond the moduli-stack framing already covered in #6 |
|  8 | Stacks Project (if alg geom)     | —                                                                      | n/a  | —                    | Stacks treats elliptic curves purely algebraically; complex-analytic lattice uniformization is out of its scope |
|  9 | MathOverflow / Math.SE           | lattice uniquely determined by g2 g3 Weierstrass invariants proof injective | yes | same statement + same Laurent-series proof; AMS Trans. 1977 "Weierstrass normal forms and invariants" for the algebraic analogue | corroborates #1–#3 |
| 10 | recent arXiv (last 5 years)      | formalization Weierstrass elliptic functions Lean mathlib uniformization lattice invariants | yes (context) | No formalisation of this theorem found anywhere; nearest is Angdinata–Xu (algebraic group law on Weierstrass curves, already in mathlib) | confirms novelty as a formalisation target |

### Literature summary (Phase 3)

Concept identified as: **uniqueness half of the uniformization theorem for elliptic curves over ℂ**
(a.k.a. injectivity of Λ ↦ (g₂(Λ), g₃(Λ)); part of the classical "modular inversion problem";
implicit in the DLMF/Whittaker–Watson notation ℘(z; g₂, g₃)).
Sources agree on the standard form: yes — all sources state it for rank-2 lattices in ℂ with
g₂ = 60G₄, g₃ = 140G₆, conclusion Λ₁ = Λ₂ (strict equality).
Most general standard form: exactly the user's — two ℂ-lattices with equal g₂ and g₃ are equal.
Generality dimensions where the literature varies:
  - packaging: standalone injectivity (Stevenhagen, 18.783) vs. uniqueness clause of the full
    existence-and-uniqueness uniformization theorem (Silverman VI §5, Park). The injectivity
    half is exactly what the user has; the existence half (modular inversion via j-surjectivity)
    is a separate future theorem.
  - base object: lattices Λ vs. period pairs (ω₁, ω₂). Mathlib's `PeriodPair` carries the basis;
    concluding `L₁.lattice = L₂.lattice` (not `L₁ = L₂`, which is false) is the correct
    basis-independent statement.
  - "generalisations" beyond ℂ (Tate uniformization over p-adic fields, algebraic j-invariant
    classification over arbitrary fields, formal groups) are **different theorems** with
    different statements and proofs — not weakenings of this one (ChatGPT channel, confirmed by
    mathlib already containing the algebraic one separately as
    `WeierstrassCurve.exists_variableChange_of_j_eq`).
Disagreement with the literature: none.

### Generality analysis — `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq` (Phase 4a)

Literature-standard form (from Phase 3): two rank-2 lattices in ℂ with equal g₂ and g₃ invariants
are equal. (Identical to the user's form.)

| # | Parameter / hypothesis  | Current Lean form         | Literature-standard form  | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------|---------------------------|----------------------------|---------------------|----------------------------------|
| 1 | `L₁ L₂ : PeriodPair`    | ℂ-period pairs (mathlib)  | ℂ-lattices                 | NO                  | The proof is essentially ℂ-analytic: identity theorem, `HasFPowerSeriesAt` over ℂ, countable-complement connectivity via `rank ℝ ℂ = 2`, `meromorphicOrderAt` pole comparison. Prior step-6 analysis (J1) explicitly REFUTED any generalisation beyond ℂ; the literature scope matches. `PeriodPair` is mathlib's own carrier for this theory. |
| 2 | `hg₂ : L₁.g₂ = L₂.g₂`   | equality of g₂            | equality of g₂             | NO                  | Essential: g₃ alone does not determine the lattice (weight-6 data only fixes the homothety orbit partially). |
| 3 | `hg₃ : L₁.g₃ = L₂.g₃`   | equality of g₃            | equality of g₃             | NO                  | Essential: g₂ alone determines the lattice only up to the action of 4th roots of unity scalings in general; both invariants are needed to pin the lattice (classical). |

### Generality verdict (Phase 4b)

No weakening was proposed, so no mechanical-weakening verification was required (there is
nothing to drop: two hypotheses, both mathematically essential; one implicit carrier type that
is mathlib's own and ℂ-bound by the subject matter). This matches false-positive class 1/2 of
the verdict-gate catalogue: concrete ℂ-analytic theorem, already at literature generality.

The current form is: **MAXIMALLY GENERAL**
Number of weakening opportunities found: 0
Proposed restatement: n/a
Cost of restatement: n/a

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | Typeclasses instead of bundled hypotheses? | no | — | The two hypotheses are equalities of specific complex numbers, not structure. |
| 2 | Filters/nets instead of sequences/metrics? | no | — | Proof already fully filter-based (`𝓝[≠]`, `=ᶠ`, `nhdsNE_sup_pure`). |
| 3 | Universal-property class instead of construction? | no | — | It is a propositional equality, not a construction. |
| 4 | Bundled substructure instead of set-with-predicate? | no | — | Conclusion is already `Submodule ℤ ℂ` equality. |
| 5 | Weaker typeclass hierarchy (modules/pseudometric/semiring)? | no | — | ℂ-specific by mathematical content (Phase 4a row 1); the field-general analogue is the *algebraic* j-classification, already in mathlib as a different theorem. |
| 6 | Higher-categorical generalisation? | no | — | The stacky/moduli formulation (nLab) classifies up to isomorphism/homothety — a strictly *weaker* conclusion than lattice equality; adopting it would change the mathematical content (Q9 guard). |
| 7 | Concrete index generalisable? | no | — | No index types in the statement. |
| 8 | Concrete-via-abstract (statement concrete, proof abstract)? | no | — | Adversarial diagnostic: the proof body references `℘`, `G`, `g₂`, `g₃`, `lattice` throughout all six stages (recursion, induction, identity theorem, pole comparison) — the concrete objects never drop out after an unfolding rewrite. The one genuinely abstract helper (`iteratedDeriv_sq_mul`) is already a separate declaration with its own (separately assessed) upstream path. |
| 9 | False-generalisation guard | no false generalisation | — | No proposal from Q1–Q8 to guard. Note the trap this row exists for: restating "up to homothety via j" *looks* more modern but proves a weaker statement. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no
One-line reason: the statement is already in mathlib's own idiom for this theory (`PeriodPair`,
`Submodule ℤ ℂ` equality, hypothesis-conclusion `eq_of_..._of_...` shape); every candidate
"modernisation" either changes the mathematical content (homothety/j reformulation is weaker) or
targets a different theorem (algebraic classification, already in mathlib).

One deliberate design note (not a blocker): mathlib could one day re-key `G`, `g₂`, `g₃` to
lattices (they factor through `L.lattice` — the tsum runs over lattice points only) and state
this as literal injectivity of a map on lattices. That is a refactor of the *upstream
definitions* in mathlib's own file, not of this theorem; the present statement transports along
it by `g₂_congr`-style lemmas in one line. Ship now; do not block on it.

### Proof strategy — Phase 4.6

| # | Question | Applies? | Idiomatic alternative | Cost of switch |
|---|----------|----------|------------------------|----------------|
| 1 | ε-δ where filters would compose? | no | — proof is filter-native (`filter_upwards`, `=ᶠ`, `nhdsNE_sup_pure` glueing) | — |
| 2 | Element-wise where point-free would abstract? | no | conclusion is `le_antisymm` of `Submodule` inequalities — already point-free at the top | — |
| 3 | Sequences where filter-limits generalise? | no | no sequences anywhere | — |
| 4 | Construction where universal property characterises? | no | n/a | — |
| 5 | Helper lemmas mathlib SHOULD have but doesn't? | yes | (i) `iteratedDeriv_sq_mul` (Leibniz collapse for `z²·g`, general 𝕜 — file it near `iteratedDeriv_fun_mul`); (ii) "analytic + equal iterated derivatives at a point ⇒ eventually equal" (currently inlined in `weierstrassP_eventuallyEq` via `HasFPowerSeriesAt.sub`; step-4 audit confirmed no such mathlib lemma) | file as same-PR helpers / follow-up |

### Proof strategy verdict (Phase 4.6)

Current strategy: **MATHLIB-IDIOMATIC**
The pipeline is the classical proof (Laurent recursion → identity theorem → polar set), executed
on mathlib's best current API — the step-4 audit verified `eqOn_weierstrassP`/`lattice_le_of_eqOn`
sit on `countable_of_Lindelof_of_discrete`, `Set.Countable.isConnected_compl_of_one_lt_rank`,
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `meromorphicOrderAt_congr` with "no change"
possible. The alternative literature route (homothety + j + automorphism analysis) would require
the whole analytic j/homothety theory first — strictly more machinery, not less. The two helper
extractions in row 5 are recommended for the PR series but do not change the strategy.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`.

### Mathlib search-status: `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq` (Phase 5)

[A] Lean-Finder       "two period lattices with equal g2 and g3 invariants are equal; injectivity of lattice-to-invariants map" — **no hits** (returns `PeriodPair.g₂/g₃` defs, periodicity lemmas, and the *algebraic* `WeierstrassCurve.ofJ*` family only)
[B] Loogle            `PeriodPair.lattice, PeriodPair.g₂` — **1 hit**: `PeriodPair.derivWeierstrassP_sq` (the differential equation — an *input* to our proof, not the result)
[C] LeanSearch        "a complex lattice is uniquely determined by its Weierstrass invariants g2 and g3" — **no hits** (top results are the g₂/g₃ definitions themselves)
[D] Grep mathlib src  `PeriodPair` referenced in exactly ONE mathlib file (`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`, ends at `derivWeierstrassP_sq` + `G`-lemmas, with explicit TODO at line ~938: "Establish connections with the `ModularForm` library"); `uniformiz*` in EllipticCurve/Elliptic/NumberTheory: only valuation-theoretic uniformizers; `lattice_eq|lattice.*determ`: only `lattice_eq_span_range_basis` — **no hits**
[E] Name pattern      `lean_local_search "lattice_eq"` — only `PeriodPair.lattice_eq_span_range_basis` — **no hits**

Searched for both:
  - the user's current form (lattice equality from equal g₂, g₃) — absent;
  - the literature-standard form (uniqueness clause of uniformization; also the homothety/j
    variants) — absent analytically. The closest mathlib result is the **algebraic**
    classification `WeierstrassCurve.exists_variableChange_of_j_eq`
    (`Mathlib/AlgebraicGeometry/EllipticCurve/IsomOfJ.lean:333`): curves with equal j are
    related by variable change, over any field. It concerns Weierstrass *equations* up to
    isomorphism, knows nothing about lattices or ℘, and cannot yield lattice equality (mathlib
    has no lattice ↔ curve functor — verified: `PeriodPair` unreferenced outside its home file).

Concluded: **"not in mathlib (all 5 methods exhausted, plus the literature-standard form)"**

### Normal-form check — Phase 5.5a

Equivalent formalisms this statement could take:
- `L₁.g₂ = L₂.g₂ → L₁.g₃ = L₂.g₃ → L₁.lattice = L₂.lattice` (current)
- `Function.Injective (fun Λ : {ZLattice in ℂ} ↦ (g₂ Λ, g₃ Λ))` — requires re-keying g₂/g₃ to lattices first (upstream-definition refactor, see Phase 4c note)
- `℘[L₁] = ℘[L₂] → L₁.lattice = L₂.lattice` plus separately "(g₂,g₃) determine ℘" — the current proof factors through exactly these stages as separate public lemmas

Does mathlib already have a canonical form for this idea? no — this would *establish* the canonical form.
Current statement is hypothesis-conclusion (`eq_of_…_of_…`), matching mathlib's naming and simp-free rewrite conventions for conditional equalities. RHS convention respected: yes (n/a for a non-iff).

### Syntactic generality — Phase 5.5b

Alternative restatements attempted:
- Conjunction hypothesis `(h : L₁.g₂ = L₂.g₂ ∧ L₁.g₃ = L₂.g₃)` — strictly worse at call sites (all three existing callers supply the two equalities as separate `?_` goals).
- ∀-quantified form (`invariantsDetermineLattice`, uniqueness.lean:328) — redundant eta-expansion; the step-4 audit already marks it for deletion. Do NOT ship it.

Chosen restatement: the current curried two-hypothesis form.
Justification: matches all observed call-site shapes (`lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_`) and mathlib's `eq_of_A_of_B` idiom.

### Superfluous-argument audit — Phase 5.5c

| # | Argument / typeclass | Essentially used? | Notes |
|---|----------------------|-------------------|-------|
| 1 | `L₁ L₂ : PeriodPair` (implicit) | yes | the subjects of the theorem; implicit binders correct (inferable from the hypotheses) |
| 2 | `hg₂` | yes | drives `G 4` base case of the coefficient induction; without it only the homothety class is constrained |
| 3 | `hg₃` | yes | drives `G 6` base case; conclusion false without it |

### Statement-shape verdict (Phase 5.5)

Normal form: OK · Syntactic generality: OK · Superfluous arguments: NONE
Overall: **SHIP-AS-STATED**

### Call sites — `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq` (Phase 6.0)

Internal use count: **4** (3 external-to-file + 1 in-file wrapper)
External-to-file callers: **1 distinct file**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| XYin/PhD/Cox/LatticeJ.lean:369 | `refine ⟨Units.mk0 c hc0, lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_⟩` (homothety from equal j) |
| XYin/PhD/Cox/LatticeJ.lean:393 | `refine ⟨Units.mk0 c hc0, lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_⟩` |
| XYin/PhD/Cox/LatticeJ.lean:432 | `refine ⟨Units.mk0 c hc0, lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_⟩` |
| XYin/uniqueness.lean:330 | `fun _ _ => lattice_eq_of_g₂_eq_of_g₃_eq` (the redundant `invariantsDetermineLattice` wrapper) |

Inline-derivation grep (equivalent re-derived elsewhere without using it?): **(none)** — the only
other `lattice = lattice` facts in the project are the converse-direction congruence lemmas
(`g₂_congr`, `g₃_congr`, `j_congr`) and sublattice bookkeeping; nothing re-proves invariants ⇒
lattice equality inline.

Signal (per 6.0.1): K ≥ 3 real uses, no inline re-derivation — genuine API, YES-* leaning. It is
the load-bearing input to the project's j-invariant/homothety theory (`j_eq_iff_homothetic` etc.).

### Composition check (Phase 6)

Can `lattice_eq_of_g₂_eq_of_g₃_eq` be derived from mathlib in ≤3 chained calls?

Attempt 1 (analytic route): mathlib's Weierstrass file provides `derivWeierstrassP_sq`,
`order_weierstrassP`, `analyticOnNhd_weierstrassP`, `iteratedDeriv_weierstrassPExcept_self`.
  - Result: **fails.** Between these primitives and the theorem stand: the second-derivative ODE
    (needs eventual nonvanishing of ℘′ near 0 — a bespoke quantitative estimate), the pole-cleared
    germ identity with the `𝓝[≠] ⊔ pure = 𝓝` glueing, the Leibniz-collapse recursion, a strong
    induction dodging the singular index n = 4, a power-series comparison, the countable-complement
    identity-theorem argument, and the two-sided pole-order comparison — ~300 lines of new proof.
Attempt 2 (algebraic route): `WeierstrassCurve.exists_variableChange_of_j_eq` + a hypothetical
  lattice↔curve bridge.
  - Result: **fails.** No such bridge exists in mathlib (`PeriodPair` unreferenced outside its
    file), the algebraic theorem concludes only isomorphism-up-to-variable-change (homothety at
    best, never lattice equality), and building the bridge is itself a larger project than the
    direct proof.

Conclusion: **NOT-COMPOSABLE**

## Verdict: `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): 9-channel exhaustive protocol; concept identified as the
  uniqueness half of the uniformization theorem over ℂ (Silverman AEC VI §5, Stevenhagen,
  Whittaker–Watson, DLMF §23.3); the ℂ-lattice statement is THE standard form.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (0 weakening opportunities; beyond-ℂ
  "generalisations" are different theorems; Phase 4c modern idiom: none applicable).
- Mathlib search (Phase 5): not in mathlib — all 5 methods exhausted on both the user's form and
  the literature forms; `PeriodPair` API ends at `derivWeierstrassP_sq`.
- Composition check (Phase 6): NOT-COMPOSABLE (two attempts; the gap is a ~300-line development).
- Phase 4.5: n/a (theorem). Phase 4.6: MATHLIB-IDIOMATIC. Phase 5.5: SHIP-AS-STATED.

**Rationale:**

Mathlib's `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` (Andrew Yang, 2025)
builds ℘, ℘′, the Laurent-expansion machinery (`weierstrassPExcept`,
`iteratedDeriv_weierstrassPExcept_self`), the Eisenstein series `G`, the invariants `g₂`, `g₃`,
the pole order (`order_weierstrassP`), and stops at the differential equation
`derivWeierstrassP_sq`, with an explicit TODO to connect onward to the modular-forms library.
`lattice_eq_of_g₂_eq_of_g₃_eq` is precisely the next classical theorem in that development: the
injectivity half of the uniformization correspondence, which the literature states at exactly
this generality and which every account of complex elliptic-curve theory needs (it is what makes
"the lattice of the curve y² = 4x³ − g₂x − g₃" well-defined, and it is the engine behind
j-invariant/homothety classification — exactly how this project consumes it three times in its
LatticeJ development). The statement is stated on mathlib's own carrier (`PeriodPair`), concludes
in the correct basis-independent form (`L₁.lattice = L₂.lattice`), and its proof runs entirely on
mathlib's intended API surface (filter germs, `HasFPowerSeriesAt`, `meromorphicOrderAt`,
countable-complement connectivity), so it upstreams with its supporting file essentially as-is.

WHY add it (bucket-specific, refactor-actionable):
- **New mathematical content:** the first injectivity/uniqueness result of complex uniformization
  in mathlib — currently mathlib can compute invariants *from* a lattice but cannot conclude
  anything about the lattice from the invariants.
- **The specific gap:** (i) the explicit TODO in `Elliptic/Weierstrass.lean` (line ~938) marks the
  file as unfinished at exactly this frontier; (ii) the uniformization correspondence is a known
  mathlib roadmap item (the analytic counterpart of the completed algebraic
  `EllipticCurve/IsomOfJ.lean` story); (iii) no formalisation of this theorem exists in any
  library (arXiv channel).
- **Composition with existing API:** unlocks well-definedness of lattice-level constructions from
  curve data; combined with the (project-proved, separately assessable) homothety-weight lemmas
  `g₂_smul`/`g₃_smul` it yields the classical "equal j ⟺ homothetic lattices", connecting
  `PeriodPair` to `WeierstrassCurve.j` / `ModularForm` — the file's own TODO.

Proposed mathlib location:  `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass/Uniqueness.lean`
  (new file under a split of the existing `Elliptic/` directory; imports the existing
  `Elliptic.Weierstrass`)
Proposed PR title:          "feat(Analysis/SpecialFunctions/Elliptic): a lattice is determined by its invariants g₂ and g₃"
PR grouping:                ship the whole `uniqueness.lean` pipeline as one PR — the intermediate
  lemmas (`recursion`, `iteratedDeriv_eq_of_invariants`, `weierstrassP_eventuallyEq`,
  `eqOn_weierstrassP`, `lattice_le_of_eqOn`) are the proof and are individually good API. Two
  extractions to place elsewhere in the same series: `iteratedDeriv_sq_mul` → generalise ℂ → 𝕜
  and file near `iteratedDeriv_fun_mul` (step-6 item J2, difficulty Low); the
  power-series-comparison germ inside `weierstrassP_eventuallyEq` → optional helper "analytic +
  equal iterated derivatives ⇒ eventually equal". Do NOT ship `invariantsDetermineLattice`
  (redundant wrapper; delete per step-4 audit).
Pre-PR checklist before opening:
  - [ ] `/generalise PeriodPair.iteratedDeriv_sq_mul` (the one genuinely generalisable helper: ℂ → 𝕜)
  - [ ] `/cleanup XYin/uniqueness.lean` — full audit + diff gates (incl. deleting `invariantsDetermineLattice`)
  - [ ] Pick a reviewer from `Mathlib/Analysis/SpecialFunctions/Elliptic/` history (Andrew Yang authored the base file)

---

## Next step

Run the pre-PR checklist above, then open the PR containing the full `uniqueness.lean` pipeline
(minus `invariantsDetermineLattice`) targeted at
`Mathlib/Analysis/SpecialFunctions/Elliptic/`, with `iteratedDeriv_sq_mul` generalised to a
nontrivially normed field and placed near `iteratedDeriv_fun_mul`.
