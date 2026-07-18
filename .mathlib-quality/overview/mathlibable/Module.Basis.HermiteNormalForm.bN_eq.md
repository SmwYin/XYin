# /mathlibable report — `Module.Basis.HermiteNormalForm.bN_eq`

Assessed 2026-07-18 against mathlib pin 2026-05-28. Mode A. This is the tenth verdict of
the HermiteNormalForm.lean family. Per protocol, the nine stored sibling reports in this
directory were read FIRST. The family's landscape facts — mathlib verifiably has no
Hermite normal form in any formulation; the HNF literature is settled (unique HNF basis
of a sublattice relative to a fixed ambient basis, rectangular scope, Bézout-ready ring
axis); and the whole family shares one blocking scope question (rank-n/rectangular
redesign, parent report Q1) — are established across those reports
([SIB:Module.Basis.HermiteNormalForm], [SIB:Matrix.IsColumnHermiteNormalForm],
[SIB:Submodule.exists_hermiteNormalForm]) and are cited rather than re-searched.
Everything specific to this lemma (build, call sites, the mathlib no-analogue check for
*basis-uniqueness* statements, the rank-2 dependency chain) was verified fresh.

---

### Baseline (Phase 0)

- lake build:               ✓ clean ("Build completed successfully (3909 jobs)"; verified fresh this session)
- decl `Module.Basis.HermiteNormalForm.bN_eq`: ✓ resolved at `XYin/PhD/Cox/HermiteNormalForm.lean:338`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Hermite-normal-form API for full-rank integer sublattices (Cox Ch. 11), templated on `Module.Basis.SmithNormalForm` but with the ambient basis as an explicit parameter.

---

### Statement (Phase 1)

`Module.Basis.HermiteNormalForm.bN_eq` is a theorem stating the following:

In rank two, the submodule basis occurring in a Hermite-normal-form datum is unique:
if h and h′ are two HNF data for the same submodule N ≤ M relative to the same fixed
ambient basis bM (each bundling a basis of N, the integer inclusion matrix, and the
column-HNF property of that matrix), then the two submodule bases coincide, h.bN = h′.bN.
This is the basis-level face of the classical uniqueness of Hermite normal form ("for
every basis B of Λ there is a *unique* basis B′ of the sublattice Λ′ in HNF"); the
matrix-level face is the sibling theorem `matrix_eq` (:278), of which this is a direct
transport: a basis of N is determined by its coordinate matrix in bM
(`Basis.repr` is injective), and `repr_apply` (:230) identifies that coordinate matrix
with the bundled `h.matrix`.

Variables / typeclasses involved (Lean side):
- `M : Type*` `[AddCommGroup M]` — ambient ℤ-module
- `{bM : Basis (Fin 2) ℤ M}` — the fixed ambient basis (rank 2 — pinned by the variable block at :262)
- `{N : Submodule ℤ M}` — the sublattice

Hypotheses (Lean side):
- `h h' : HermiteNormalForm bM N` — two HNF data for the same N over the same bM

Conclusion (math): the HNF basis of a rank-two sublattice relative to a fixed ambient basis is unique.

Conclusion (Lean): `h.bN = h'.bN`

Proof body (7 lines): `DFunLike.ext` + `Subtype.ext` + `bM.repr.injective`, then
`rw [h.repr_apply, h'.repr_apply, h.matrix_eq h']`. All mathematical content is imported
from `matrix_eq`; this lemma is the repr-injectivity transport of it to the basis level.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a corollary-level transport of the sibling `matrix_eq` through `Basis.repr`
injectivity — not a new structure, not a project main result on its own (the module
docstring's headline results are the structure, existence, and `matrix_eq`;
`bN_eq` is the companion restatement). The *concept* it expresses (HNF uniqueness) is
named-after-Hermite territory, but that concept's exhaustive literature treatment is the
parent's and predicate's reports, cited below.

### One-line check (Phase 2b)

One-liner verdict: n/a — kind is theorem, not def. (Body is a 7-line tactic proof.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

The concept — uniqueness of the HNF basis of a sublattice relative to a fixed ambient
basis — is *identically* the concept row-by-row covered by the parent structure's
exhaustive table ([SIB:Module.Basis.HermiteNormalForm] rows 1–10, run at this same pin),
whose row 1 finding is verbatim the content of this lemma: "For any lattice L ⊂ ℤⁿ there
is a **unique basis in HNF**; … for every basis B of Λ a unique basis B′ of Λ′ with
B′ = BH" (Wikipedia HNF; Shmonin EPFL notes; Nguyen MPRI Lecture 2; arXiv 2310.12519).
Re-running the nine channels on the same concept the same week would spend rate-limited
channels to reproduce a stored table. Rows below cite the stored evidence; the one
genuinely lemma-specific literature question (is the *basis-level* uniqueness statement,
as distinct from the matrix-level one, a separately-stated literature item?) is answered
fresh from the already-retrieved sources.

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | [SIB:parent row 1] "Hermite normal form" basis sublattice "fixed basis" canonical unique | yes | unique HNF basis for every sublattice, fixed ambient basis | THE content of `bN_eq`; stated at rank n (not rank 2) throughout |
|  2 | WebSearch (general form)         | [SIB:parent row 2 / Submodule.exists_hermiteNormalForm row 2] HNF uniqueness rectangular, PID/Bézout | yes | uniqueness holds rectangular over ℤ and Bézout-with-representatives | Storjohann; AFP formalises matrix-level uniqueness in the general setting |
|  3 | WebSearch (named-after/aliases, formalisation) | [SIB:parent row 3] AFP "Hermite" (Divasón–Aransay) uniqueness | yes | **matrix-level** uniqueness formalised in AFP; no formalisation states basis-level uniqueness (no basis bundle exists anywhere) | the basis-level statement is novel packaging, exactly as the parent bundle is |
|  4 | ChatGPT MCP                      | [SIB:parent row 4] full design review incl. uniqueness theorems | yes | uniqueness (`matrix_eq`/`bN_eq`) is *the* payoff the parameter-bM design enables ("a field-bM could not even state them"); "predicate + uniqueness can land earlier" than the bundle | sequencing recommendation: matrix-level uniqueness in PR 1, basis-level with the bundle in PR 2 |
|  5 | Local references                 | `.mathlib-quality/references/` | n/a | directory absent at this path (consistent with all 9 sibling reports) | — |
|  6 | nLab                             | [SIB:parent row 6] Hermite normal form | yes | canonical representative per unimodular class; each convention gives uniqueness | — |
|  7 | nCatLab                          | n/a — not a categorical concept [SIB:parent row 7] | n/a | — | — |
|  8 | Stacks Project                   | n/a — not an algebraic-geometry concept [SIB:parent row 8] | n/a | — | — |
|  9 | MathOverflow / Math.SE           | [SIB:parent row 9] sublattice HNF basis uniqueness | yes | unique HNF basis for every sublattice of ℤⁿ | Straub notes, UCSD CSE 206A |
| 10 | recent arXiv (last 5 years)      | [SIB:parent row 10] | yes | arXiv 2310.12519: sublattice ↔ HNF-matrix bijection — *injectivity of that bijection is this lemma + matrix_eq* | contemporary form is rank-n |

### Literature summary (Phase 3)

Concept identified as: uniqueness of the Hermite-normal-form basis of a sublattice
relative to a fixed ambient basis (basis-level face; matrix-level face = `matrix_eq`).
Sources agree on the standard form: yes — uniqueness is part of every HNF treatment.
Most general standard form: rank-n (indeed rectangular) sublattices of ℤⁿ; Bézout-ready.
Generality dimensions where the literature varies:
  - rank: the literature states uniqueness at rank n; this lemma is rank 2 only
  - level: matrix-level (all formalisations, AFP) vs basis-level (no precedent; this
    project's bundle is the only basis-level HNF object anywhere)
Disagreement with the literature: none on content; the rank-2 restriction is strictly
narrower than every source.

---

### Generality analysis — `Module.Basis.HermiteNormalForm.bN_eq` (Phase 4)

Literature-standard form (from Phase 3): for any n, two HNF data for the same N over the
same bM have equal bases (and rectangular beyond that).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `bM : Basis (Fin 2) ℤ M` | rank 2 pinned (variable block :262) | rank n | yes in the literature, **NO mechanically** | the proof's closing rewrite is `h.matrix_eq h'`, and `matrix_eq` exists only at `Fin 2` (its proof is an explicit 2×2 entry chase: `fin_cases i <;> fin_cases j`, :330–335). A `Fin n` `bN_eq` has no `matrix_eq` to invoke — the widening is blocked by a missing rank-n theorem whose proof needs new ideas (column induction), not by this lemma's own text. Verified at the type level: no probe can compile `h.matrix_eq h'` when `bM : Basis (Fin n) ℤ M`, since the only `matrix_eq` in scope requires `Basis (Fin 2) ℤ M`. Verdict-gate false-positive class 5 |
| 2 | `h h' : HermiteNormalForm bM N` | the project-local bundle | n/a — no literature/formalisation has a basis-level bundle | NO | the statement is inexpressible without the parent structure, whose own verdict is BORDERLINE ([SIB:parent]) |
| 3 | ring ℤ | ℤ (inherited from predicate) | Bézout + representatives | yes in the literature, NO mechanically | predicate-level redesign, inherited [SIB:Matrix.IsColumnHermiteNormalForm] |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (rank 2 vs rank n; ℤ vs Bézout) —
with **zero mechanically-reachable weakenings**: the rank axis is blocked by `matrix_eq`
being rank-2-only (a real rank-n uniqueness proof is new work, class 5), and the ring
axis is the family's predicate redesign (class 5 by inheritance). No compiling weakening
exists to verify → `YES-but-generalise-first` is unavailable per the verdict gate.
Number of weakening opportunities found: 0 mechanical, 2 real-but-redesign.
Cost of the real restatement (rank-n `matrix_eq` + `bN_eq`): EXPENSIVE for `matrix_eq`
(new induction proof), CHEAP for `bN_eq` itself once `matrix_eq` is rank-n (the transport
proof is rank-agnostic — nothing in :338–345 mentions 2). Cost noted for sequencing only.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|---|---|---|---|
| 1 | Typeclasses instead of bundled hypotheses? | no | the hypotheses are two structure instances; that IS the idiom | — |
| 2 | Filters/nets? | no | finite algebra, no topology | — |
| 3 | Universal property? | partially | the pair (`matrix_eq`, `bN_eq`) could be repackaged as `Subsingleton (HermiteNormalForm bM N)` — the mathlib-idiomatic spelling of "the HNF datum is unique" (rank 2). Both current lemmas become `congrArg` corollaries | `Subsingleton` API (`Subsingleton.elim` at every use site); this is the honest normal form for "uniqueness of a bundle" and worth adopting IF the family ships (noted in Phase 5.5) |
| 4 | Bundled substructure? | no | already about a bundle | — |
| 5 | Typeclass-hierarchy weakening? | no | ring axis is a predicate redesign (4a row 3) | — |
| 6 | Higher-categorical? | no | elementary lattice theory [SIB:parent row 7] | — |
| 7 | Concrete index generalises? | yes in principle (Fin 2 → Fin n) | blocked by `matrix_eq` (4a row 1) — a dev ticket, not a restatement | rank-n uniqueness is the literature form |
| 8 | Concrete-via-abstract? | no | proof-body grep: after the `change` at :344 the proof mentions only `repr_apply` and `matrix_eq` — it is *already* the abstract transport; the concreteness (rank 2) sits in the dependency `matrix_eq`, not in this proof | — |
| 9 | False-generalisation guard | applied | the rank-n and `Subsingleton` reformulations preserve meaning exactly (same object, same uniqueness); no false generalisation among the proposals | safeguard recorded |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — (i) `Subsingleton (HermiteNormalForm bM N)` as the
canonical packaging of the uniqueness pair (CHEAP, rank 2 as-is); (ii) rank-n statement
(EXPENSIVE, gated on rank-n `matrix_eq`). Real improvement: (i) replaces two ad-hoc
equality lemmas with mathlib's standard uniqueness API; (ii) is the literature scope.
Both are contingent on the parent bundle shipping at all — which is the family's open
BORDERLINE question — so neither converts this verdict to YES-but-generalise-first on
its own.

### Proof strategy — Phase 4.6

| # | Question | Applies? | Idiomatic alternative | Cost of switch |
|---|---|---|---|---|
| 1 | ε-δ vs filters | no — algebraic | — | — |
| 2 | Element-wise vs point-free | no — the proof is already the point-free transport (repr-injectivity + one rewrite); the ext/intro steps are forced by `Basis` extensionality | — | — |
| 3 | Sequences vs nets | no | — | — |
| 4 | Construction vs universal property | no | — | — |
| 5 | Missing mathlib helpers | yes (family-level): mathlib lacks the HNF predicate/uniqueness entirely — the family IS the missing API [SIB:parent 4.6 row 5] | HNF PR series | — |

### Proof strategy verdict (Phase 4.6)

Current strategy: MATHLIB-IDIOMATIC (a 7-line repr-injectivity transport of `matrix_eq`;
the shortest path modulo what should exist. The only strategic upgrade is the
`Subsingleton` repackaging noted in 4c, a statement-shape point, not a proof one).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is theorem.

---

### Mathlib search-status: `Module.Basis.HermiteNormalForm.bN_eq` (Phase 5)

[A] Lean-Finder       (via the family's five-method searches at this pin)  no HNF hits in any formulation [SIB:parent, Submodule.exists_hermiteNormalForm, Matrix.IsColumnHermiteNormalForm — three independent full five-method runs]
[B] Loogle            [SIB:parent B] `"Hermite"`                            only Hermite polynomials + `NumberField.hermiteTheorem.*`; no normal form
[C] LeanSearch        [SIB:parent C] HNF-basis natural-language             no HNF hit; top results are the SNF family — the template, not a substitute
[D] Grep mathlib src  fresh this session: `hermiteNormalForm|HermiteNormalForm` over Mathlib/  **zero matches**; fresh: `SmithNormalForm` uniqueness grep over `LinearAlgebra/FreeModule/PID.lean` (`uniq|_eq |subsingleton`)  **zero matches** — mathlib has no "normal-form basis is unique" lemma of ANY kind (SNF is genuinely non-unique, so no analogue can exist there)
[E] Name pattern      `bN_eq` cannot exist in mathlib under this namespace (the parent structure is project-local; verified zero `HermiteNormalForm` matches in [D])

Searched for both:
  - the user's current form (basis-level rank-2 HNF uniqueness): absent — inexpressible
    in mathlib (the structure and predicate do not exist there)
  - the literature-standard form (rank-n HNF uniqueness, matrix or basis level): absent —
    mathlib has no HNF at all; the nearest object, `Basis.SmithNormalForm`, has no
    uniqueness statement because SNF bases are not unique (fresh grep, zero hits)

Concluded: "not in mathlib (family five-method searches + two fresh lemma-specific greps
exhausted, both forms); no analogous normal-form-basis-uniqueness lemma exists anywhere
in mathlib"

---

### Statement shape (Phase 5.5)

### Normal-form check

Equivalent formalisms:
1. current: `h.bN = h'.bN` (paired with sibling `matrix_eq : h.matrix = h'.matrix`)
2. `Subsingleton (HermiteNormalForm bM N)` — implies both, since the remaining fields are
   propositions; instances-as-uniqueness is mathlib's canonical idiom (cf. `Unique`/`Subsingleton` instances for canonical structures)
3. `h = h'` (bare structure equality) — subsumed by 2 with better API

Does mathlib already have a canonical form for this idea? No HNF form; for the *idiom*,
mathlib states "this bundle is unique" as a `Subsingleton`/`Unique` instance when it does
so at all → form 2 is the canonical shape; the current pair (1) is the pre-normal-form
spelling. RHS convention: n/a (not an iff).

### Syntactic generality

Alternative restatements attempted: (1) vs (2) vs (3) above. Chosen restatement IF the
family ships: (2) `Subsingleton (HermiteNormalForm bM N)`, with `matrix_eq`/`bN_eq` as
`congrArg`-corollaries (or dropped). Justification: one instance discharges every
future "two HNF data agree" obligation via `Subsingleton.elim`, instead of two
field-by-field lemmas. For the project as it stands, (1) is fine — `matrix_eq` is the
one actually consumed (Classification.lean:175) and it applies by direct rewrite.

### Superfluous-argument audit

| # | Argument / typeclass | Essentially used? | Notes |
|---|---|---|---|
| 1 | `[AddCommGroup M]` | yes | needed to state `Submodule ℤ M`, `Basis` |
| 2 | `bM : Basis (Fin 2) ℤ M` | yes | HNF is basis-relative; rank-2 pin is the 4a row-1 axis, not a superfluous hypothesis |
| 3 | `h h' : HermiteNormalForm bM N` | yes | the objects being compared |

### Statement-shape verdict (Phase 5.5)

Normal form: REFACTOR candidate — `Subsingleton (HermiteNormalForm bM N)` is the target
normal form if the family ships (carried into the Phase 7 questions).
Syntactic generality: OK for project use; RESTATE (Subsingleton) for mathlib.
Superfluous arguments: NONE.
Overall: RESTATE-BEFORE-SHIP (Subsingleton packaging + rank-n), contingent on the
family's BORDERLINE questions — consistent with a non-YES verdict.

---

### Call sites — `Module.Basis.HermiteNormalForm.bN_eq` (Phase 6.0)

Internal use count: **0** (fresh grep, whole project, `--exclude-dir=.lake`: the only
match is the declaration itself at HermiteNormalForm.lean:338).
External-to-file callers: 0 files.

| Caller file:line | Usage pattern (one-line excerpt) |
|---|---|
| (none) | — |

Context: the sibling `matrix_eq` — the matrix-level face — IS consumed: fresh grep shows
`S.hermiteNormalForm.matrix_eq (σ.inclusionHermiteNormalForm L)` at
XYin/PhD/Cox/CyclicSublattice/Classification.lean:175, the classification's key
uniqueness step. `bN_eq` is the basis-level companion, stated for completeness of the
uniqueness pair (the literature states uniqueness of the *basis*; `matrix_eq` is the
form proofs actually rewrite with).

Inline-derivation grep (equivalent re-derived without using `bN_eq`?): (none) — no site
proves `h.bN = h'.bN` by hand; the one consumer of uniqueness goes through `matrix_eq`.

Pattern read-off (table 6.0.1): K = 0 internal uses, no inline re-derivation → "dead
code? brand new + unused?" → here: genuinely-new completeness lemma for a family whose
fate is BORDERLINE; the K = 0 leans NO-composable/BORDERLINE, and rules out any
standalone YES (no consumer evidence, and the Subsingleton repackaging would replace it
anyway).

### Composition check (Phase 6)

Can `bN_eq` be derived from mathlib in ≤3 chained calls?

Attempt 1: the statement's type mentions `HermiteNormalForm bM N`, which does not exist
in mathlib (Phase 5 [D]: zero matches), nor does its field predicate
`Matrix.IsColumnHermiteNormalForm` [SIB:Matrix.IsColumnHermiteNormalForm Phase 5]. The
statement is not expressible in mathlib, so no mathlib composition can produce it.
  - Mathlib decls used: n/a
  - Result: fails — inexpressible, inherited from the parent's NOT-COMPOSABLE
    ([SIB:parent Phase 6], both attempts, incl. the verified SNF-cannot-substitute
    argument: SNF forgets the fixed ambient basis and its bases are non-unique)
Attempt 2: compose from *project* decls (for calibration, not a mathlib composition):
`bN_eq` IS a ≤3-step transport of project-local `matrix_eq` + `repr_apply` +
`Basis.repr.injective` — confirming its content lives in `matrix_eq`, but this is
irrelevant to mathlib-composability since `matrix_eq` is itself project-local (and
BORDERLINE-family).

Conclusion: NOT-COMPOSABLE (from mathlib).

---

## Verdict: `Module.Basis.HermiteNormalForm.bN_eq`

**Category:** BORDERLINE-needs-human (inherited: follows the parent structure
`Module.Basis.HermiteNormalForm` → BORDERLINE; same pattern as
`Matrix.isColumnHermiteNormalForm_fin_two` inheriting from the predicate)

**Evidence:**
- Literature search (Phase 3): the lemma's content — the HNF basis of a sublattice
  relative to a fixed ambient basis is unique — is verbatim the headline uniqueness
  statement of every HNF source ([SIB:parent row 1]), stated there at rank n; no
  formalisation states it at the basis level because no basis-level HNF bundle exists
  anywhere outside this project.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD (rank 2 vs rank n) with
  zero mechanically-reachable weakenings — the rank-n form requires a rank-n `matrix_eq`
  that does not exist (its proof is an explicit 2×2 entry chase, `fin_cases` at :330);
  verdict-gate false-positive class 5 excludes YES-but-generalise-first. Phase 4c/5.5
  identified `Subsingleton (HermiteNormalForm bM N)` as the mathlib-normal-form
  repackaging of the uniqueness pair, contingent on the family shipping.
- Mathlib search (Phase 5): not in mathlib in either form; fresh greps confirm zero HNF
  matches and zero normal-form-basis-uniqueness analogues (SNF has none — SNF bases are
  not unique).
- Composition check (Phase 6): NOT-COMPOSABLE — the statement is inexpressible in
  mathlib (parent type absent). Call sites: K = 0 (the project's one uniqueness consumer
  uses the sibling `matrix_eq` instead, Classification.lean:175).

**Rationale:**

This lemma has no independent mathlib fate. Its statement quantifies over the
project-local bundle `HermiteNormalForm bM N` — a type mathlib cannot express (no HNF
predicate, no HNF bundle; three independent five-method searches plus two fresh greps) —
so it can only ever ship *with* the parent structure, and the parent's fully-argued
verdict is BORDERLINE-needs-human on the family's shared scope questions (rectangular
shape before the structure fossilises; redundant `matrix` field; rank-n existence
commitment; PR sequencing). Its proof confirms the dependency is total: seven lines that
transport the sibling `matrix_eq` through `Basis.repr` injectivity — the mathematical
content (uniqueness) lives in `matrix_eq`, and the rank-2 restriction is inherited from
`matrix_eq`'s hand-cranked 2×2 proof, not from anything in `bN_eq` itself. Both NO
buckets fail on the evidence (mathlib has neither the result nor the vocabulary to
compose it); both YES buckets fail because a lemma about a structure that cannot ship
yet cannot ship first, because K = 0 consumers gives no standalone-API evidence, and
because no mechanical weakening compiles (class 5). Inheriting the parent's BORDERLINE
is the honest verdict — with two lemma-specific riders recorded for whenever the family
questions are answered: (a) the literature form is rank-n, so the uniqueness pair should
be generalised together with `matrix_eq` (whose rank-n proof is the actual new work;
`bN_eq`'s transport is already rank-agnostic); (b) the mathlib-idiomatic packaging of
the pair is a `Subsingleton (HermiteNormalForm bM N)` instance, which would subsume both
`matrix_eq` and `bN_eq`.

For BORDERLINE-needs-human:
  Numbered questions (≤5 — Q1 defers to the parent's question set rather than re-asking):
    1. **Family gate (defer to parent):** the verdict resolves automatically with the
       parent structure's five questions ([SIB:Module.Basis.HermiteNormalForm] Q1–Q5,
       especially Q1 rectangular-redesign and Q4 rank-n existence). Do you want this
       lemma tracked as part of that same decision, with no separate action? (yes/no;
       "yes" closes this report until the parent is resolved)
    2. **Uniqueness packaging:** if the family ships, do you adopt
       `instance : Subsingleton (HermiteNormalForm bM N)` as the shipped form of the
       uniqueness pair, demoting `matrix_eq`/`bN_eq` to corollaries or deleting them?
       (yes/no)
    3. **Rank-n uniqueness ticket:** is generalising `matrix_eq` (and with it, for free,
       `bN_eq`) from `Fin 2` to `Fin n` in scope for the project — the standard
       triangular-unimodular argument, new proof work — or does rank-2 remain the
       endpoint? (yes/no/defer; mirrors parent Q4 for the uniqueness side)
    4. **Keep-though-unused:** `bN_eq` currently has zero call sites (the classification
       uses `matrix_eq`). Keep it as the literature-facing statement of basis uniqueness,
       or drop it project-locally until a consumer appears? (keep/drop)
  Next action: user answers the parent report's five questions (this lemma requires no
  separate re-run — a resolution of the parent that commits to the rectangular rank-n
  redesign turns the uniqueness pair into a dev ticket: rank-n `matrix_eq` proof, then
  `bN_eq` transports unchanged, then optionally the `Subsingleton` repackaging).

---

## Next step

No independent action. The lemma inherits the parent structure's
BORDERLINE-needs-human; it ships if and only if the `HermiteNormalForm` bundle ships,
in whatever shape the parent's Q1–Q5 answers dictate. The two riders to carry into that
resolution: generalise the uniqueness pair to rank n together (the new work is in
`matrix_eq`; `bN_eq`'s transport proof is already rank-agnostic), and prefer the
`Subsingleton` instance as the shipped packaging of uniqueness.
