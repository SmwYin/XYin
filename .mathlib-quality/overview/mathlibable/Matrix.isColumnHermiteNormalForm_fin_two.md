# /mathlibable report — `Matrix.isColumnHermiteNormalForm_fin_two`

Assessed 2026-07-18 against mathlib pin 2026-05-28 (`2abc2425`). Mode A, full protocol.
Landscape shared with the six stored sibling verdicts in this directory
(`Matrix.IsColumnHermiteNormalForm` → BORDERLINE, `Matrix.exists_right_mul_isColumnHermiteNormalForm`
→ BORDERLINE, `Submodule.exists_hermiteNormalForm` → BORDERLINE, `Submodule.hermiteNormalForm`
→ BORDERLINE, `…index_eq_natAbs_det` → NO-composable, `…quotient_isAddCyclic_iff…` →
BORDERLINE). Concept-level searches are cited from those reports where they genuinely
cover this decl; everything specific to this lemma (its content status as definitional
unpacking, the fin-two literal-lemma pattern in mathlib, iff-vs-intro shape, call sites,
standalone-shippability) was verified fresh.

**Headline finding, stated up front per the assessment brief:** this lemma is pure
convenience unfolding of the project-local predicate `Matrix.IsColumnHermiteNormalForm`
at the `Fin 2` matrix literal, with no independent mathematical content (verified three
ways below: proof-body reading, literature anchoring, independent ChatGPT check). Its
honest verdict therefore follows the predicate's fate — BORDERLINE, inherited from
`Matrix.IsColumnHermiteNormalForm.md`, resolved by the same shared Q1.

---

### Baseline (Phase 0)

- lake build:               ✓ clean (fresh run: "Build completed successfully (3909 jobs)"; only informational q-expansion output in qExpansion_tactic/Examples.lean — same state as all six sibling assessments)
- decl `Matrix.isColumnHermiteNormalForm_fin_two`: ✓ resolved at `XYin/PhD/Cox/HermiteNormalForm.lean:84`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Hermite-normal-form API for full-rank integer submodules (Cox Ch. 11); bundled HNF structure in arbitrary finite rank, constructive existence in rank two.

---

### Statement (Phase 1)

`Matrix.isColumnHermiteNormalForm_fin_two` is a theorem stating the following:

For integers d, r, a with 0 < d, 0 < a, and 0 ≤ r < d, the 2×2 matrix
`!![d, r; 0, a]` is in column Hermite normal form. That is: the defining conditions of
the (project-local) column-HNF predicate — upper triangularity, positive pivots,
canonical nonnegative residues above the diagonal — hold for the explicit rank-two
shape, given exactly the four inequalities that instantiate those conditions at
`Fin 2`. Docstring in source: "The defining inequalities for a rank-two column HNF
matrix." It is the intro/constructor lemma for the predicate at the 2×2 literal.

Variables / typeclasses involved (Lean side):
- `{d r a : ℤ}` — the three free entries of the literal (bottom-left is the literal 0)

Hypotheses (Lean side):
- `hd : 0 < d` — pivot positivity at index 0 (`diagonal_pos 0`)
- `ha : 0 < a` — pivot positivity at index 1 (`diagonal_pos 1`)
- `hr0 : 0 ≤ r`, `hrd : r < d` — the residue condition (`reduced 0 1`: `r ∈ Set.Ico 0 d`)

Conclusion (math): `!![d, r; 0, a]` satisfies the column-HNF predicate.

Conclusion (Lean): `IsColumnHermiteNormalForm !![d, r; 0, a]`

Proof body (read in full, lines 86–93): `refine ⟨?_, ?_, ?_⟩` then, per field,
`fin_cases` + `simp_all` (with `Set.mem_Ico` for the residue field). The proof does
nothing but expand the structure, evaluate the matrix literal entrywise, and reduce the
finite `<` relations on `Fin 2`. The hypotheses are exactly equivalent to the
conclusion (each is a field instance; the below-diagonal field is the literal `0`), so
the lemma is the forward direction of a definitional iff.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a helper/intro lemma — definitional unpacking of the sibling predicate at one
concrete literal; not a named theorem, not a main result (the module docstring names
the bundled structure and the existence theorem, not this). (Literature width
EXHAUSTIVE-by-citation regardless; see Phase 3.)

### One-line check (Phase 2b)

Body line count: n/a
One-liner verdict: n/a (kind is theorem, not def) — check skipped. (Note: though a
theorem, its content status is that of glue — the Mode B verdict-inheritance criterion
"a lemma whose statement involves a parent def already assessed" applies in spirit; it
is not literally `rfl`-glue, so the full Mode A workflow was run anyway.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

The nine-channel concept-level protocol for this lemma's mathematics — the HNF
predicate, its 2×2 shape, conventions, and generality landscape — was run in full by
`Matrix.IsColumnHermiteNormalForm.md` (rows 1–10, assessed 2026-07-18 at this pin,
covering the predicate whose definitional content this lemma unpacks) and
`Submodule.exists_hermiteNormalForm.md` / `Matrix.exists_right_mul_isColumnHermiteNormalForm.md`
(existence/uniqueness landscape). Those searches genuinely cover this decl: the lemma
states nothing beyond the predicate's definition at `Fin 2`. Incorporated by citation.
Decl-specific rows searched fresh:

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form) — FRESH | 2x2 Hermite normal form sublattice index "0 <= b < d" upper triangular matrix characterization | yes | The rank-two shape `!![d, r; 0, a]`, 0 < d, 0 < a, 0 ≤ r < d is exactly the literature's *membership condition* for HNF_n(m) at n = 2: "one-to-one correspondence with integral matrices H in HNF, upper-triangular, 0 ≤ h_ij < h_j" (arXiv 2310.12519; UCSD CSE206A lecture notes; MathWorld; AFP Hermite doc) | Confirms: the lemma's content is the *definition instantiated at n = 2*, not an independent theorem — no source states it as a lemma; it appears only as the defining condition of the bijection index-m sublattices ↔ HNF matrices |
|  2 | WebSearch (general form)         | (cited: predicate report rows 1–3 — HNF predicate conditions, convention variants, rectangular/Bézout generality) | yes | three-condition predicate; rectangular staircase standard scope | Fully covers this lemma: its "general form" IS the predicate |
|  3 | WebSearch (aliases/named-after)  | (cited: predicate report rows 2–3, existence report rows 1, 3 — column vs row conventions; AFP; no Lean HNF anywhere) | yes | convention package free but fixed; project's is poly-matrix column style | Nothing alias-specific to a fin-two intro lemma exists to search |
|  4 | ChatGPT MCP (gpt-5.4) — FRESH, decl-specific | (i) does the Fin-2 intro lemma have independent mathematical content? (ii) if the predicate ships, what form would reviewers want — intro or iff? (iii) any standalone-contribution scenario? | yes | (i) "**essentially no independent mathematical content** … its mathematical worth is entirely derivative of the predicate"; (ii) reviewers would want the **iff characterization** (`isColumnHermiteNormalForm_fin_two_iff : … ↔ 0 < d ∧ 0 < a ∧ r ∈ Set.Ico 0 d`), with the one-way intro derived in one line and included only if usage pays for it; possibly `[simp]`; "the useful lemma is usually the fully unfolded characterization, not merely one introduction direction"; (iii) "**No, not realistically.** Without the predicate in mathlib, this lemma has no natural home and no standalone API value. Mathlib does not generally accept lemmas whose only purpose is to unpack a project-local definition specialized to one tiny case." | Independently confirms the headline finding and fixes the PR-facing shape |
|  5 | Local references                 | `.mathlib-quality/references/` absent (n/a — recorded, consistent with all siblings); substituted analysis notes via predicate report row 5 (step4-lattice) | yes | step4 flags the predicate's carrier question; nothing specific to this intro lemma beyond it | — |
|  6 | nLab                             | (cited: predicate report row 6 — HNF as canonical representative; conventions each yield uniqueness) | yes | the 2×2 shape is the definition's instance, no separate nLab content | — |
|  7 | nCatLab (if categorical)         | n/a — not a categorical concept (verified by predicate report row 7) | n/a | — | — |
|  8 | Stacks Project (if alg geom)     | n/a — not an algebraic-geometry concept (verified by sibling row 8: no HNF tag) | n/a | — | — |
|  9 | MathOverflow / Math.StackExchange| (cited: sibling rows 9 — index-m sublattices ↔ HNF matrices `!![d, r; 0, a]`, 0 ≤ r < d, da = m) | yes | the lemma's inequalities are the well-known parametrisation of index-m sublattices — as a *definition of the parameter range*, never as a theorem | Directly covers the 2×2 shape |
| 10 | recent arXiv (last 5 years)      | (cited: sibling rows 10 + fresh row-1 hit arXiv 2310.12519, which works with exactly the 2×2/n×n HNF parametrisation) | yes | contemporary usage identical: shape conditions as definition | — |

### Literature summary (Phase 3)

Concept identified as: **the defining membership condition of 2×2 column Hermite normal
form** — the instantiation at n = 2 of the HNF predicate (Hermite 1851), i.e. the
parameter range of the standard bijection between index-m sublattices of ℤ² and
matrices `!![d, r; 0, a]` with 0 < d, 0 < a, 0 ≤ r < d, da = m (Cox Ch. 11 context).

Sources agree on the standard form: yes — and uniformly treat it as a *definition
instance*, not a lemma. No source in any channel states "these inequalities imply HNF"
as a theorem; it is the definition unfolded.

Most general standard form: the predicate itself (see the predicate report's Phase 3:
rectangular staircase scope, residue-parametrised ring generality). This lemma has no
generality axis of its own — at general index type the "intro lemma" is the structure's
anonymous constructor; the `Fin 2` content is purely literal-matrix evaluation.

Generality dimensions where the literature varies: none specific to this decl — all
variation (shape, ring, convention, index) lives at the predicate level and is analysed
in `Matrix.IsColumnHermiteNormalForm.md`.

Disagreement with the literature: none; the direction (one-way intro rather than iff)
is a project-ergonomics choice the literature is silent on and mathlib convention
(fresh ChatGPT + the `isParabolic_iff_of_upperTriangular` precedent, Phase 5) would
restate as an iff.

---

### Generality analysis — `Matrix.isColumnHermiteNormalForm_fin_two` (Phase 4a)

Literature-standard form (from Phase 3): the predicate's definition; at rank two, the
iff between `IsColumnHermiteNormalForm !![d, r; 0, a]` and the four inequalities.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|--------------------------------|
| 1 | `hd : 0 < d` | strict positivity | same (pivot condition) | NO | the conclusion implies it (`.diagonal_pos 0` evaluates to `0 < d`); hypothesis ≡ conclusion-field, nothing to weaken |
| 2 | `ha : 0 < a` | strict positivity | same | NO | conclusion implies it (`.diagonal_pos 1`) |
| 3 | `hr0 : 0 ≤ r`, `hrd : r < d` | split pair | `r ∈ Set.Ico 0 d` (the predicate's own spelling) | NO (equivalent repackaging only) | conclusion implies both (`.reduced 0 1`); bundling as `Set.Ico` membership is cosmetic and would match the field |
| 4 | the literal `!![d, r; 0, a]` | 2×2, bottom-left hard-coded 0 | general ι: the anonymous constructor | NO (not mechanically) | at general ι there is no literal — the "generalisation" of an unfolding lemma is the constructor `⟨_, _, _⟩`, which already exists by definition; nothing to state |
| 5 | ring ℤ / index `Fin 2` | inherited from the predicate | see predicate report rows 1–3 | NO at this decl | all ring/shape/index generality questions are the predicate's (its report: zero sound mechanical widenings; redesigns only) — this lemma tracks them verbatim |

### Generality verdict (Phase 4b)

Verified-weakening note: every hypothesis is implied by the conclusion (each is a field
of the predicate evaluated at the literal — verified by reading the proof body and the
structure definition), so no hypothesis can be dropped and no compile probe is
meaningful: dropping any makes the statement false. Zero weakening opportunities. The
only genuine "generalisation" — restating against a rank-n/rectangular/ring-general
predicate — is the predicate-level redesign already routed to BORDERLINE by the
predicate report (verdict-gate false-positive class 5), and at general index the lemma
degenerates into the anonymous constructor, i.e. it *has no general form of its own*.

The current form is: MAXIMALLY GENERAL for what it is (a definitional unpacking at a
literal — hypotheses exactly equivalent to the conclusion); all real generality
questions live one level up at the predicate.

Number of weakening opportunities found: 0 (one cosmetic repackaging: `Set.Ico`
membership instead of the split pair, aligning with the field's spelling).

Cost of restatement: n/a (nothing to restate at this level).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|--------------------------------|
| 1 | typeclasses instead of bundled hypotheses | no | four arithmetic hypotheses; nothing to typeclass-ify | — |
| 2 | filters/nets | no | finite arithmetic; no topology | — |
| 3 | universal property | no | it is a constructor application | — |
| 4 | bundled substructure | no | — | — |
| 5 | typeclass-hierarchy weakening | no | ring/order questions are the predicate's (its Q9 guard rejected the ordered-ring widening) | — |
| 6 | higher-categorical | no | — | — |
| 7 | concrete index generalisation | no — degenerate | at general ι the lemma IS the anonymous constructor; the `Fin 2` literal evaluation is the entire point of the decl | — |
| 8 | concrete-via-abstract (proof-body diagnostic) | no — diagnostic run, does NOT fire in the abstraction direction | grep of the proof body: it consists ONLY of constructor-splitting, `fin_cases`, and `simp` on the literal — there is no abstract argument hiding behind the concrete statement; conversely there is no concrete content hiding behind an abstract statement. The proof is 100% definitional evaluation | n/a |
| 9 | false-generalisation guard | n/a | no generalisation proposed at this level | — |
| — | **shape modernisation (decl-specific, fresh)** | **yes** | if this ever ships (inside the predicate's PR), restate as the simp-able characterization `isColumnHermiteNormalForm_fin_two_iff : IsColumnHermiteNormalForm !![d, r; 0, a] ↔ 0 < d ∧ 0 < a ∧ r ∈ Set.Ico 0 d`, with the intro direction as a one-line `.mpr` corollary — ChatGPT-recommended ("the useful lemma is usually the fully unfolded characterization"), matching mathlib's fin-two pattern (`Matrix.isParabolic_iff_of_upperTriangular` in `GeneralLinearGroup/FinTwo.lean` is the exact precedent shape; the `det/trace/adjugate _fin_two_of` family is the literal-evaluation precedent) | `simp`/`rw`-composability in both directions; extraction as well as construction |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes, but conditional and cosmetic — the iff restatement above,
relevant ONLY inside a future predicate PR (it is a shape choice for the predicate's
`Fin 2` API, not an independent improvement this decl can carry alone). Cost: CHEAP.
Real improvement: two-directional composability, consistent with mathlib's fin-two
characterization precedents. Project-locally the one-way intro is fine: both consumers
use exactly the intro direction.

---

### Proof strategy — `Matrix.isColumnHermiteNormalForm_fin_two` (Phase 4.6a)

| # | Question | Applies? | Idiomatic alternative | Cost of switch |
|---|----------|----------|------------------------|----------------|
| 1 | ε-δ vs filters | no — no topology | — | — |
| 2 | element-wise vs point-free | no — entrywise evaluation of a literal is the entire content; `fin_cases` + `simp` is the mathlib-standard tactic pattern for it | — | — |
| 3 | sequences vs nets | no | — | — |
| 4 | construction vs universal property | no | — | — |
| 5 | missing mathlib helpers | no — decidable-fragment `simp`/`fin_cases` suffices; (the predicate-level gap — mathlib lacking any HNF — is the siblings' shared upstream ticket, not a helper this proof needs) | — | — |

### Proof strategy verdict (Phase 4.6b)

Current strategy: MATHLIB-IDIOMATIC — constructor split + `fin_cases` + `simp_all` is
exactly how mathlib proves fin-two characterizations (cf. the `FinTwo.lean` file's own
proofs). No refactor recommended.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is theorem.

---

### Mathlib search-status: `Matrix.isColumnHermiteNormalForm_fin_two` (Phase 5)

Structural note driving the search design: the lemma's conclusion is headed by the
project-local predicate `Matrix.IsColumnHermiteNormalForm`, which the predicate
report's five-method search (this pin, 2026-07-18) established mathlib does not have in
any form (no HNF/echelon predicate anywhere; only the partial carrier
`Matrix.BlockTriangular`). Mathlib therefore *cannot state* this lemma. The fresh
searches below target the two residual questions: (a) does mathlib have the analogous
fin-two/literal intro lemma for any adjacent predicate, and (b) does anything match the
mathematical content (entrywise 2×2 shape ⇒ normal-form membership).

[A] Lean-Finder    (cited: predicate report [A] — no HNF hits, SNF-side nearest; existence report [A] — surfaced `FixedDetMatrices.*`, analysed there) — nothing an intro-lemma search could add beyond [C] below
[B] Loogle         **fresh**: `Matrix.BlockTriangular !![_, _; _, _]` → **zero hits** — mathlib has no literal-matrix intro lemma even for its own triangularity carrier; sibling [B]: `"Hermite"` → polynomials + `NumberField.hermiteTheorem.*` only
[C] LeanSearch     **fresh**: "2x2 upper triangular integer matrix with positive diagonal and reduced top-right entry is in Hermite normal form" → no match; nearest: `FixedDetMatrices.reps` (membership conditions *defined* entrywise — the reps analogue of this lemma is definitional, not a named lemma), `FixedDetMatrices.reps_one_id` (entrywise conditions at det 1 ⇒ A = 1 — a *uniqueness*-flavoured fin-two lemma, different content), `Matrix.isParabolic_iff_of_upperTriangular` (the fin-two iff-characterization pattern — shape precedent, unrelated content)
[D] Grep mathlib   **fresh**: `fin_two`-pattern grep over the pin → the `*_fin_two_of` literal-evaluation family exists (`det_fin_two_of`, `trace_fin_two_of`, `adjugate_fin_two`, SpecialLinearGroup/UnitaryGroup fin-two files) but NO predicate-intro-at-literal lemma for any normal-form-like predicate; sibling [D]: no "hermite normal", no echelon, no `IsHermite` (zero files)
[E] Name pattern   `grep isColumnHermiteNormalForm_fin_two` project + mathlib → project-only (declaring file ×2 + CoxMatrices/Basic.lean:61); no name-adjacent mathlib decl

Searched for both:
- the user's current form — not statable in mathlib (head symbol is the project-local
  predicate, itself absent from mathlib per the predicate report's five methods)
- the literature-standard form (the fin-two characterization of any HNF/echelon-type
  predicate; a `BlockTriangular` literal intro lemma; entrywise-shape ⇒ normal-form
  membership in any convention) — none in mathlib; the nearest object,
  `FixedDetMatrices.reps`, bakes the analogous conditions into a set *definition* with
  no intro lemma, in a different convention (left action, SL₂, unsigned second pivot —
  non-convertibility established by the existence sibling's Phase 6 + ChatGPT check)

Concluded: **"not in mathlib (all 5 methods exhausted, plus the literature-standard
form)"** — with the sharper structural fact that the statement is not even expressible
in mathlib until the predicate exists, so this decl's mathlib status is strictly
downstream of the predicate's BORDERLINE.

---

### Normal-form check — Phase 5.5a

Equivalent formalisms this statement could take:
1. one-way intro with four split hypotheses (current)
2. one-way intro with `hr : r ∈ Set.Ico 0 d` bundled (matches the field's spelling)
3. iff characterization `IsColumnHermiteNormalForm !![d, r; 0, a] ↔ 0 < d ∧ 0 < a ∧ r ∈ Set.Ico 0 d`, intro as `.mpr` (ChatGPT-recommended PR form; `isParabolic_iff_of_upperTriangular` precedent)

Does mathlib already have a canonical form for this idea? No (no HNF predicate). The
normal-form principle for "definition specialized to a small finite type" in mathlib is
the fully-unfolded iff with the unfolded conditions on the RHS — formalism 3 respects
the RHS convention (predicate on LHS, arithmetic normal form on RHS, simp-able).

RHS convention respected? Current form n/a (implication); formalism 3 yes.

### Syntactic generality — Phase 5.5b

Alternative restatements attempted: forms 1–3 above.
Chosen restatement: form 1 for the project — both consumers (`exists_hnf_transform`
:190 with four loose hypotheses in hand; `inclusionMatrix_isColumnHermiteNormalForm`
discharging four `exact_mod_cast` goals after `apply`) supply exactly the split
hypotheses, so the current shape is easiest to apply at the actual call sites. For a
PR: form 3 primary, intro derived.
Justification: verified against both call sites (read in source); `apply` +
four-goal discharge at CoxMatrices/Basic.lean:61–65 works precisely because the
hypotheses are split.

### Superfluous-argument audit — Phase 5.5c

| # | Argument / typeclass | Essentially used? | Notes |
|---|----------------------|-------------------|-------|
| 1 | `hd : 0 < d` | yes | conclusion implies it (`.diagonal_pos 0`) |
| 2 | `ha : 0 < a` | yes | conclusion implies it (`.diagonal_pos 1`) |
| 3 | `hr0 : 0 ≤ r` | yes | conclusion implies it (`.reduced 0 1`.1) |
| 4 | `hrd : r < d` | yes | conclusion implies it (`.reduced 0 1`.2) |

None superfluous — the hypothesis set is exactly the conclusion unfolded.

### Statement-shape verdict (Phase 5.5d)

Normal form: OK locally / for a PR the target normal form is the iff (formalism 3)
Syntactic generality: OK (current split-hypothesis intro is what both call sites want)
Superfluous arguments: NONE

Overall: SHIP-AS-STATED project-locally; RESTATE-BEFORE-SHIP for any mathlib PR (iff
primary + derived intro — carried into the Phase 7 next-action list, conditional on
the predicate shipping at all).

---

### Call sites — `Matrix.isColumnHermiteNormalForm_fin_two` (Phase 6.0)

Internal use count: **1** (excluding the declaring file); **2** total consumers
External-to-file callers: 1 distinct file

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| XYin/PhD/Cox/HermiteNormalForm.lean:190 (in-file) | `exact isColumnHermiteNormalForm_fin_two hpositivePivot hgpos hr0 hrp` — closes the HNF-shape goal of the private existence core `exists_hnf_transform` |
| XYin/PhD/Cox/CoxMatrices/Basic.lean:61 | `apply Matrix.isColumnHermiteNormalForm_fin_two` — proves `inclusionMatrix_isColumnHermiteNormalForm` for the Cox matrix `!![d, b; 0, a]` (four `exact_mod_cast` goals from the `CoxMatrix` fields) |

Inline-derivation grep (equivalent re-derived elsewhere without using the decl?):
(none) — grep for anonymous-constructor proofs of the predicate at literals
(`IsColumnHermiteNormalForm` + `⟨`/`refine`/`fin_cases` outside this lemma): zero
sites; every literal-shape HNF proof in the project flows through this lemma.

Signal (per 6.0.1): K = 2 consumers (one being the file's own existence engine, one the
CoxMatrix bridge), no inline re-derivation → genuine but thin convenience API. K = 1
external-only leans "possibly inlineable" per the table — but inlining would mean
pasting the `fin_cases`+`simp` block at both sites, and the lemma is the predicate's
designated intro point; the thinness reinforces that it has no standing independent of
the predicate rather than that it is junk.

### Composition check (Phase 6)

Can `Matrix.isColumnHermiteNormalForm_fin_two` be derived from mathlib in ≤3 chained
calls?

Attempt 1 (direct): the statement's head symbol is the project-local predicate,
absent from mathlib (predicate report, five methods). No mathlib composition can even
*state* the goal, let alone prove it. The only derivation is the predicate's anonymous
constructor `⟨fun i j h => …, fun i => …, fun i j h => …⟩` with entrywise `fin_cases`
+ `simp` evaluation — i.e. the current proof, which uses project + core tactics, not
mathlib lemma calls.
  - Mathlib decls used: none available for the head symbol
  - Result: fails — not expressible from mathlib primitives

Attempt 2 (via the adjacent `FixedDetMatrices.reps` machinery): reps membership is a
different convention on a different carrier with no exported bridge (existence
sibling's Phase 6, ChatGPT-confirmed non-convertible); it cannot produce a statement
about this predicate.
  - Result: fails.

Conclusion: **NOT-COMPOSABLE** — vacuously so: composability is downstream of the
predicate existing in mathlib. If the predicate ever ships WITH this lemma's iff form,
the intro direction becomes a one-line `.mpr` composition *of the shipped iff* — which
is precisely why the lemma has no independent life: it is glue for the predicate in
every possible world.

---

## Verdict: `Matrix.isColumnHermiteNormalForm_fin_two`

**Category:** BORDERLINE-needs-human (inherited: follows `Matrix.IsColumnHermiteNormalForm` → BORDERLINE)

**Evidence:**
- Literature search (Phase 3): the lemma's content — `!![d, r; 0, a]` with 0 < d,
  0 < a, 0 ≤ r < d is in column HNF — appears in every source only as the *definition*
  of the 2×2 HNF shape / the parameter range of the index-m sublattice bijection
  (fresh WebSearch: arXiv 2310.12519, UCSD CSE206A, MathWorld, AFP; sibling rows), never
  as a theorem. Fresh ChatGPT check (gpt-5.4): "essentially no independent mathematical
  content … entirely derivative of the predicate"; standalone contribution scenario:
  "No, not realistically."
- Generality analysis (Phase 4): MAXIMALLY GENERAL for what it is — all four hypotheses
  are implied by the conclusion (definitional equivalence), zero weakenings exist, and
  at general index type the lemma degenerates into the predicate's anonymous
  constructor; every real generality axis (shape, ring, convention, index) is the
  predicate's, already routed to BORDERLINE in its report.
- Mathlib search (Phase 5): not in mathlib and not statable in mathlib (head symbol is
  the project-local predicate, absent per the predicate report's five methods —
  re-anchored fresh: no literal intro lemma exists even for `BlockTriangular`; the
  `FixedDetMatrices.reps` analogue is a set definition in a non-convertible convention).
- Composition check (Phase 6): NOT-COMPOSABLE (vacuously — nothing in mathlib can
  express the goal). K = 2 call sites, no inline re-derivation.

**Rationale:**

This is the case the assessment brief anticipated, and the evidence confirms it
three ways: the proof body is pure constructor-split + `fin_cases` + `simp` literal
evaluation; the literature knows the statement only as a definition instance; and an
independent ChatGPT check states flatly that the lemma is definitional unpacking with
no standalone mathlib scenario. A declaration with no mathematical content of its own
cannot out-verdict the definition it unpacks. Both NO buckets fail on their gates:
`NO-mathlib-has-it` fails because mathlib has no decl to cite (it cannot even state
the lemma), and `NO-composable-from-mathlib` fails because Phase 6 concluded
NOT-COMPOSABLE — both NO buckets would also wrongly imply the lemma should be deleted
now, when it is the predicate's designated intro point with two live consumers and its
fate is genuinely undecided. Both YES buckets fail because the lemma can only ship
inside the predicate's PR (ChatGPT: a lemma "whose only purpose is to unpack a
project-local definition specialized to one tiny case" is not a contribution), and the
predicate's own verdict is BORDERLINE on the siblings' shared scope question. The
honest verdict is therefore the inherited one — exactly the Mode B glue-inheritance
rule applied in Mode A: `INHERITED-BORDERLINE` from `Matrix.IsColumnHermiteNormalForm`,
resolving with the same Q1. The only decl-specific facts worth recording for that
resolution: (1) if the predicate ships, this lemma's mathlib form should be the
simp-able iff characterization with the intro direction as a `.mpr` corollary (fresh
ChatGPT recommendation; `Matrix.isParabolic_iff_of_upperTriangular` is the in-pin
precedent shape); (2) in a rank-n library the fin-two lemma remains legitimate `Fin 2`
API (mathlib's `*_fin_two_of` family is the precedent) but is not load-bearing — the
general constructor subsumes it; (3) project-locally the current one-way split-
hypothesis form is exactly what both call sites consume — no local change needed.

**Numbered questions (≤3):**

1. (= the six siblings' shared decisive Q1 — this decl adds nothing to it and resolves
   with it) Are you committing to the mathlib-right HNF development (rank-n existence +
   uniqueness over ℤ, matrix + basis forms)? This lemma ships only inside that unit, as
   part of the predicate's `Fin 2` API; if no, it stays project-local with everything
   else. (yes/no)
2. If yes to 1: adopt the iff shape for the shipped `Fin 2` characterization
   (`isColumnHermiteNormalForm_fin_two_iff`, RHS `0 < d ∧ 0 < a ∧ r ∈ Set.Ico 0 d`,
   possibly `[simp]`; intro direction as a one-line corollary kept only if usage pays
   for it)? (yes/no — recommended yes, ChatGPT + mathlib fin-two precedent)
3. Project-local: keep the lemma exactly as stated (both consumers supply the split
   hypotheses; no refactor warranted)? (yes/no — recommended yes; nothing to do now)

**Next action:** none for this decl alone — answer Q1 jointly with the six sibling
reports (all seven resolve as a unit). Yes to Q1 ⇒ this lemma is absorbed into the
predicate's PR as its `Fin 2` characterization, in the iff form of Q2, inside the
`/develop` ticket the siblings specify. No ⇒ no action; the decl stays project-local
as-is.
