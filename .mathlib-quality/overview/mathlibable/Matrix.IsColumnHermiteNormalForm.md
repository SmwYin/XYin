# /mathlibable report — `Matrix.IsColumnHermiteNormalForm`

Assessed 2026-07-18 against mathlib pin 2026-05-28 (`2abc2425`). Mode A, full exhaustive
protocol. Landscape shared with the four stored sibling verdicts in this directory
(`Submodule.exists_hermiteNormalForm` → BORDERLINE, `Submodule.hermiteNormalForm` →
BORDERLINE, `…index_eq_natAbs_det` → NO-composable, `…quotient_isAddCyclic_iff…` →
BORDERLINE): concept-level searches are cited from those reports where they genuinely
cover this decl; everything predicate-specific (definition conventions, the
`BlockTriangular` carrier question, mechanical-widening probes, echelon-predicate
searches) was verified fresh.

---

### Baseline (Phase 0)

- lake build:               ✓ clean ("Build completed successfully (3909 jobs)"; only informational q-expansion output in qExpansion_tactic/Examples.lean)
- decl `Matrix.IsColumnHermiteNormalForm`: ✓ resolved at `XYin/PhD/Cox/HermiteNormalForm.lean:33`
- kind:                      structure (Prop-valued predicate)
- has sorry:                 no
- module docstring summary:  Hermite-normal-form API for full-rank integer submodules (Cox Ch. 11); HNF is canonical only after fixing the ambient basis; bundled structure in arbitrary finite rank, constructive existence in rank two.

---

### Statement (Phase 1)

`Matrix.IsColumnHermiteNormalForm` is a definition (Prop-valued structure) of the
following:

A square integer matrix A, with rows/columns indexed by a preordered type ι, is in
column Hermite normal form when (i) it is upper triangular (entries below the diagonal
vanish), (ii) every diagonal pivot is strictly positive, and (iii) every entry above the
diagonal is the canonical nonnegative residue of its row's pivot: A i j ∈ [0, A i i) for
i < j. In the rank-two case this is the shape !![d, r; 0, a] with 0 < d, 0 < a,
0 ≤ r < d — the canonical basis shape for a finite-index sublattice of ℤ² used
throughout Cox, *Primes of the Form x²+ny²*, Chapter 11, under right (column)
unimodular action A ↦ A·U.

Variables / typeclasses involved (Lean side):
- `ι : Type*` `[Preorder ι]` — the index type; only `<` is used
- `A : Matrix ι ι ℤ` — the square integer matrix

Fields (each a defining condition, not a hypothesis):
- `belowDiagonal_eq_zero : ∀ i j, j < i → A i j = 0` — upper triangularity
- `diagonal_pos : ∀ i, 0 < A i i` — positive pivots (sign normalisation)
- `reduced : ∀ i j, i < j → A i j ∈ Set.Ico 0 (A i i)` — row-wise canonical residues

Conclusion (math): "A is in column HNF" — the canonical-representative predicate for
the right unimodular action on nonsingular integer matrices.

Conclusion (Lean): n/a — definition.

**Convention note (verified, drives Phase 3/4).** The reduction is against the pivot in
the entry's ROW (`A i i`), not its column. For the right-action upper-triangular form
this is the coherent choice: column operations change A i j modulo A i i in the
triangular case, and the file's own rank-2 uniqueness theorem
(`Module.Basis.HermiteNormalForm.matrix_eq`, :278) proves the predicate really is a
canonical form under right unimodular action. This matches the polynomial-matrix
"column Hermite form" convention (upper triangular, right multiplication, row-wise
degree/residue reduction) rather than MathWorld's integer-matrix "columns version"
(which is lower triangular); see Phase 3 rows 1–3.

---

### Size classification (Phase 2a)

Verdict: BIG
Reason: it introduces a new mathematical structure — the defining predicate of a named
concept (Hermite normal form, Hermite 1851) that mathlib lacks entirely; every other
decl in the file (and the CoxMatrices/CyclicSublattice developments) is stated against
it. (Literature width EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 3 substantive lines (three fields)
One-liner verdict: MULTI-LINE — exemption table not required. (Note for Phase 4c: field
1 is nevertheless definitionally a single mathlib term, `A.BlockTriangular id`.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

Concept-level channels (HNF existence/uniqueness/generality landscape, formalisation
precedent, nLab/Stacks/MathOverflow/arXiv) were run in full by the sibling reports
`Submodule.exists_hermiteNormalForm.md` (rows 1–10) and `Submodule.hermiteNormalForm.md`
(rows 1–10), both assessed 2026-07-18 at this pin, and are incorporated by citation.
Predicate-specific rows (the *definition's* conditions, conventions, carrier, ring
generality) were searched fresh:

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | Hermite normal form definition matrix conditions column upper triangular positive pivots entries reduced convention variants | yes | Square nonsingular HNF: diagonal positive, zero on one side of the diagonal, entries on the other side reduced mod their pivot; nLab: "no one single definition … some authors impose different conditions"; row form (UM = H) vs column form (MU = H) | nLab HNF page, MathWorld, dcode, AFP Hermite document (Divasón–Aransay, Feb 2026 build) |
|  2 | WebSearch (conventions/aliases)  | "column Hermite normal form" lower triangular versus upper triangular right multiplication unimodular convention Cohen Sage | yes | MathWorld/integer convention: "columns version makes the result lower triangular"; polynomial-matrix column Hermite form: **upper** triangular under right multiplication with row-wise reduction (project's shape); Wolfram uses rows/upper; uniqueness holds under each convention | Confirms the project's convention is a legitimate variant (poly-matrix style, matches Cox) but NOT the dominant integer-matrix "column" convention — naming/convention must be settled for a PR |
|  3 | WebSearch (general form)         | (sibling report rows 1–3: rectangular m×n, any rank, staircase pivots; ℤ → Euclidean → Bézout; AFP formalises Bézout-domain echelon/Hermite with parametrised associate/residue choices) | yes | Literature-standard predicate: rectangular echelon/staircase + normalised pivots + reduced off-pivot entries; canonicity over general rings via chosen associates/residues, not order | Cited: `Submodule.exists_hermiteNormalForm.md` rows 1–3, 10 |
|  4 | ChatGPT MCP (gpt-5.4, high)      | Is this the standard column-HNF predicate; convention variants and dominance; rectangular-from-day-one vs square-first; BlockTriangular as triangularity carrier; is LinearOrderedCommRing widening genuine or false; would predicate + 2×2-only theorems be accepted; is Preorder ι right | yes | (i) dominant computational convention is Cohen's row version; column/lower-triangular occurs as the transpose/right-action version; residues 0 ≤ r < d or balanced; (ii) "rectangular is the right ultimate definition … avoid a public square-only 'main' definition"; (iii) **yes, use `A.BlockTriangular id`** for the square layer (reuses `BlockTriangular.mul`, `det_of_upperTriangular`); only downside: `BlockTriangular` is square-only, so don't force the eventual rectangular predicate through it; (iv) **ordered-ring widening is a FALSE generalization** — canonicity needs chosen associates/residues, not order; ℤ-specific first is right; (v) "a predicate plus only 2×2 existence/uniqueness theorems is unlikely to be accepted as a standalone mathlib contribution"; `Preorder ι` "too loose for public HNF" — use `Fin n` or `[LinearOrder ι] [Fintype ι]`; naming: upper-triangular right-action form named "Column" is misleading vs the dominant terminology — document or rename | The reduction-position flag ChatGPT raised (row vs column pivot) resolves as a convention difference, not an error: for the right-action upper-triangular form, row-wise reduction is the coherent choice, and the file's rank-2 uniqueness proof confirms canonicity (Phase 1 note) |
|  5 | Local references                 | `.mathlib-quality/references/` absent (n/a — recorded); substituted `.mathlib-quality/overview/analysis/step4-lattice.md` (predicate-specific lines 55–59, 109, 119) + `step6-generalization.md` §A1 (via siblings) | yes | step4 :55–59: `belowDiagonal_eq_zero` is "definitionally `A.BlockTriangular id` (Block.lean:61), but stated raw, so the triangular-determinant computation is redone by hand at ≥3 sites"; recommends `blockTriangular`/`det_eq`/`det_pos` derived lemmas or restating the field — "kills the three ad-hoc det_fin_two computations and scales past rank two"; step4 :119: no HNF in mathlib, `Matrix.IsUpperTriangular` does not exist (only `BlockTriangular`) | The caller-flagged carrier question is a pre-existing, verified project finding |
|  6 | nLab                             | "Hermite normal form" (fresh hit via row 1; also sibling row 6) | yes | HNF as canonical representative of unimodular-equivalence classes; sign/convention variants each give uniqueness; explicitly notes there is no single definition | Predicate-relevant: conventions are a free choice a library must fix and document |
|  7 | nCatLab (if categorical)         | n/a — not a categorical concept (matrix/lattice reduction theory; sibling row 7 verified the nLab page offers no categorical abstraction) | n/a | — | — |
|  8 | Stacks Project (if alg geom)     | n/a — not an algebraic-geometry concept (sibling row 8 verified: no HNF tag; SNF incidental only) | n/a | — | — |
|  9 | MathOverflow / Math.StackExchange| (sibling rows 9: unique HNF basis per sublattice, index-m sublattices ↔ HNF matrices) | yes | The predicate's three conditions are exactly what makes the sublattice↔matrix bijection well-defined | Cited from siblings; nothing predicate-specific beyond conventions (row 2) |
| 10 | recent arXiv (last 5 years)      | (sibling rows 10 + fresh row-2 hits) | yes | arXiv 2310.12519, 2405.19302 (HNF over Hermitian lattices), 2605.07784 Labahn–Storjohann; polynomial-matrix column-Hermite usage in Krylov/computer-algebra papers (arXiv 2402.07345) | Contemporary research states HNF rectangular over ℤ (or ring-generalised); the poly-matrix column convention is alive in the algorithms literature |

### Literature summary (Phase 3)

Concept identified as: **the defining predicate "matrix in (column) Hermite normal
form"** — triangular/echelon shape + normalised pivots + reduced off-pivot entries; the
canonical-representative predicate for one-sided unimodular equivalence (Hermite 1851).

Sources agree on the standard form: yes on the three-condition *shape*; no single
convention — row vs column action, upper vs lower triangular, residue window
(nonnegative vs balanced), and reduction position covary, and each coherent combination
yields a unique canonical form (nLab, MathWorld, AFP). The dominant computational
convention is Cohen's row version; the project's combination (right action + upper
triangular + row-wise nonnegative residues) is the polynomial-matrix column-Hermite
style and is internally coherent (rank-2 uniqueness proved in-file).

Most general standard form: a predicate on **rectangular m×n matrices of arbitrary
rank** (staircase pivots, zero columns allowed) over ℤ; over general Euclidean/Bézout
rings, canonicity is parametrised by chosen associate and residue systems (AFP
precedent) — NOT by an order.

Generality dimensions where the literature varies:
- shape: square nonsingular (user; most textbook statements) → **rectangular any-rank staircase** (standard)
- ring: ℤ with order-based normalisation (user; standard for ℤ) → associate/residue-parametrised over Bézout/Euclidean (AFP)
- convention: row/column × upper/lower × residue window — free choice, must be fixed and documented
- index type: `Fin n` (literature) vs the user's arbitrary `[Preorder ι]` (MORE general than literature — and per ChatGPT too loose: HNF needs a total pivot order)

Disagreement with the literature: none on mathematical substance; the name
"ColumnHermiteNormalForm" for an upper-triangular form conflicts with the dominant
integer-matrix terminology (where the columns version is lower triangular) — a
documentation/naming decision for any PR.

---

### Generality analysis — `Matrix.IsColumnHermiteNormalForm` (Phase 4a)

Literature-standard form (from Phase 3): predicate on rectangular m×n integer matrices,
staircase pivots, positive pivots, entries reduced against their pivot; ring-generalised
form parametrised by associates/residues.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|--------------------------------|
| 1 | index `{ι : Type*} [Preorder ι]` | arbitrary preorder | `Fin n` / `[LinearOrder ι] [Fintype ι]` (total pivot order) | yes mechanically (`[LT ι]` compiles — verified lean_run_code) — but the literature points the OTHER way | only `<` is used, so `[LT ι]` type-checks; however HNF is a canonical form tied to a total pivot order, and the companion det API (`Matrix.det_of_upperTriangular`) needs `[LinearOrder ι]`; the mathlib-right binder is *tighter*, not looser (ChatGPT: "Preorder is too loose for public HNF") |
| 2 | ring ℤ | ℤ, order-based normalisation (`0 < A i i`, `Set.Ico 0 (A i i)`) | ℤ is standard; general rings use associate/residue parametrisation | compiles-but-FALSE: widening to `[Zero R] [Preorder R]` type-checks (verified lean_run_code) but is a **false generalisation** (Q9): over an arbitrary ordered ring the symbols exist but the concept (canonical representative; existence/uniqueness) fails — ChatGPT explicit, AFP precedent parametrises by residues, not order | keep ℤ; the abstract form is a statement-level redesign, not a widening |
| 3 | square `Matrix ι ι ℤ` | square | rectangular m×n, staircase pivots | NO (not mechanically) | the diagonal-indexed fields (`A i i`) presuppose square; the rectangular predicate needs a pivot function/staircase formulation — a redesign (verdict-gate false-positive class 5) |
| 4 | field 1 spelling | raw `∀ i j, j < i → A i j = 0` | mathlib's canonical triangularity carrier `A.BlockTriangular id` | yes — **verified**: the two are interconvertible by `fun i j hij => …` (definitional up to binder explicitness; lean_run_code clean both directions), and `Matrix.det_of_upperTriangular` applies directly through the field | pure modern-idiom respelling, CHEAP (see 4c) |
| 5 | convention (upper-tri + right action + row residues) | poly-matrix column-Hermite style | no single standard; Cohen row version dominant | n/a — convention choice, not a generality axis | must be fixed + documented (or renamed) for a PR; internally coherent (rank-2 uniqueness proved in-file) |

### Generality verdict (Phase 4b)

Verified-weakening note: a Prop-structure has no proof body, so "weakening" means
parameter widening, and both candidate widenings were compile-probed
(lean_run_code, clean): `[Preorder ι] → [LT ι]` compiles but is the wrong direction
per the literature (the public form should be *tighter*: `Fin n` / `LinearOrder`+
`Fintype`); `ℤ → [Zero R] [Preorder R]` compiles but is rejected by the Q9
false-generalisation guard (ordered-ring "HNF" is symbol-sharing, not the literature
concept — canonicity over general rings is residue-parametrised, per AFP and ChatGPT).
The genuine literature-standard generalisation (rectangular staircase predicate;
residue-parametrised ring form) is a statement-level redesign — verdict-gate
false-positive class 5, which excludes `YES-but-generalise-first`.

The current form is: STRICTLY NARROWER THAN STANDARD in shape (square vs rectangular
staircase) and, for the ring axis, at the standard ℤ level whose true generalisation is
a redesign; on the index axis it is nonstandardly *looser* than the literature form.

Number of weakening opportunities found: 0 sound mechanical widenings (2 compile but
are rejected: one wrong-direction, one false generalisation); 1 verified CHEAP
modern-idiom respelling (BlockTriangular carrier, row 4); 2 real-but-expensive
redesigns (rectangular shape; residue-parametrised ring form).

Cost of the true generalisation: EXPENSIVE (rectangular redesign rides the sibling
reports' rank-n scope decision). Does not downgrade any verdict — scoping question,
Phase 7.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|--------------------------------|
| 1 | typeclasses instead of bundled hypotheses | no | a Prop-valued structure with named fields is the right shape for a 3-condition predicate (cf. mathlib's structure-predicates); consumers use dot-notation fields at 15+ sites | — |
| 2 | filters/nets | no | finite algebra; no topology | — |
| 3 | universal property instead of construction | no | HNF is a canonical-representative predicate; its "characterisation" is the uniqueness theorem, which lives on the theorem side | — |
| 4 | bundled substructure instead of set-with-predicate | no | it IS the predicate; the bundled object is the sibling `Module.Basis.HermiteNormalForm` | — |
| 5 | typeclass-hierarchy weakening | no — rejected | ℤ → ordered ring compiles but fails Q9 (false generalisation); the honest ring generalisation is the AFP-style residue-parametrised predicate, a redesign | — |
| 6 | higher-categorical | no | matrix reduction theory | — |
| 7 | concrete index generalisation | inverted | the predicate is *already* index-general (`[Preorder ι]`) — more general than the literature; the mathlib-right move is to TIGHTEN to `Fin n` or `[LinearOrder ι] [Fintype ι]` so the det/uniqueness API is statable | `det_of_upperTriangular` needs `LinearOrder`; avoids a vacuously-general binder |
| 8 | concrete-via-abstract (proof-body diagnostic) | n/a | structure definition — no proof body to run the diagnostic on | — |
| 9 | false-generalisation guard | **yes — fires on Q5's widening** | the ordered-ring widening is REJECTED: it would be a different object sharing symbols (no canonicity, no existence/uniqueness); documented in 4a row 2 | prevents ship-then-revert |
| — | **carrier respelling (the caller-flagged question)** | **yes** | restate field 1 as `blockTriangular : A.BlockTriangular id` (or keep the field and add the rfl-level bridge lemma `IsColumnHermiteNormalForm.blockTriangular`), per step4-lattice :55–59 | unlocks `Matrix.det_of_upperTriangular` → `det_eq : A.det = ∏ i, A i i`, `det_pos`, `BlockTriangular.mul` closure, `invertibleToBlock`; kills the three ad-hoc `det_fin_two` computations at CyclicSublattice.lean:387, Classification.lean:43, CyclicSublattice.lean:582 and "scales past rank two"; verified defeq-level (lean_run_code, both directions + direct `det_of_upperTriangular` application) |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — two-part.
(a) CHEAP and decision-independent: carry the triangularity component on
`Matrix.BlockTriangular id` (restated field or rfl-bridge lemma + `det_eq`/`det_pos`),
verified compiling; real improvement: three hand-rolled determinant computations
collapse and the det API scales past rank 2.
(b) EXPENSIVE and decision-dependent: the rectangular staircase predicate (the
literature-standard shape) — a redesign that only makes sense inside the sibling
reports' rank-n scope commitment, hence feeds Phase 7's questions rather than a
self-resolving `YES-but-generalise-first`.
Cost: (a) CHEAP, (b) EXPENSIVE.
Real mathematical improvement (not just "looks cooler"): (a) removes duplicated
determinant reasoning and reuses a canonical mathlib carrier; (b) is the
literature-standard scope.

---

### Proof strategy — `Matrix.IsColumnHermiteNormalForm` (Phase 4.6a)

| # | Question | Applies? | Idiomatic alternative | Cost of switch |
|---|----------|----------|------------------------|----------------|
| 1 | ε-δ vs filters | no — definition, no proof body; no topology | — | — |
| 2 | element-wise vs point-free algebra | partially | the triangularity condition is stated entrywise where mathlib's `BlockTriangular` carrier abstracts it (the 4c(a) respelling); the pivot/residue conditions are intrinsically entrywise | CHEAP |
| 3 | sequences vs nets | no | — | — |
| 4 | construction vs universal property | no | — | — |
| 5 | missing mathlib helpers | yes | mathlib SHOULD have (and lacks): the HNF predicate itself at rectangular/rank-n scope, `det_eq`/`det_pos` consequences, and ultimately the existence/uniqueness pair — the file-level dev-ticket already recorded by the sibling reports | (upstream ticket) |

### Proof strategy verdict (Phase 4.6b)

Current strategy: REFACTOR-RECOMMENDED (definition-shape refactor, not a proof
refactor): restate the triangularity field as `A.BlockTriangular id` — or, non-invasively,
add the rfl-bridge `blockTriangular` + derived `det_eq`, `det_pos` lemmas — per
step4-lattice :55–59. Cost: CHEAP. Would make downstream strictly shorter: yes (three
ad-hoc determinant computations collapse; verified the mathlib det lemma applies
directly through the field).

---

### Diamond / defeq risk — `Matrix.IsColumnHermiteNormalForm` (Phase 4.5)

Declaration kind is `structure` — phase runs.

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | Prop-valued structure, not a class; grep of HermiteNormalForm.lean: zero `instance` declarations; nothing enters typeclass search |
| 2 | Reducibility leak | none | no `@[reducible]`; a Prop structure's "body" is its constructor — nothing computes; consumers only destruct fields |
| 3 | Non-canonical unfolding | low | `simp`/`rfl` do not unfold structure predicates; all 15+ external uses go through named fields (`.diagonal_pos`, `.belowDiagonal_eq_zero`, `.reduced`) or the intro lemma `isColumnHermiteNormalForm_fin_two` — the intended discipline, empirically confirmed. Residual "low": an anonymous-constructor `⟨…⟩` site fixes field order, a normal structure cost |
| 4 | Instance priority collision | none | not an instance; no priorities involved |
| 5 | Universe-polymorphism issues | none | `ι : Type*`, target `Prop`; no universe constraints forced (probe: instantiated at `Fin 2 : Type` and arbitrary `ι` without annotation) |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort` (grep: none); Prop predicate consumed as hypothesis |

### Risk verdict (Phase 4.5)

Overall risk: NONE (one row "low" at the ordinary cost of any structure).
Top risks: none. Same infrastructure profile as mathlib's own Prop-structure
predicates; the only design risk is convention/naming lock-in, which is a Phase 7
question, not a defeq/diamond risk.

---

### Mathlib search-status: `Matrix.IsColumnHermiteNormalForm` (Phase 5)

[A] Lean-Finder    (sibling reports, this pin, 2026-07-18) "Hermite normal form … triangular basis/inclusion matrix" → **no HNF hits**; nearest are SNF-side (`Module.Basis.SmithNormalForm`, `Submodule.smithNormalForm*`) — none a matrix-shape predicate
[B] Loogle         (sibling reports) `"Hermite"` → only `NumberField.hermiteTheorem.*` (discriminant finiteness) + Hermite polynomials; no HNF predicate
[C] LeanSearch     (sibling reports) HNF/triangular-basis phrasings → SNF family only; no matrix normal-form predicate
[D] Grep mathlib   **fresh at this pin**: `grep -rli "echelon\|IsHermite\|hermiteNormal" Mathlib/` → **zero files** (mathlib has NO echelon-form or Hermite-form predicate of any kind); `grep "def.*Triangular" LinearAlgebra/Matrix/Block.lean` → only `Matrix.BlockTriangular` (Block.lean:61, `∀ ⦃i j⦄, b j < b i → M i j = 0`) with det API `det_of_upperTriangular` (:324, needs `[LinearOrder m]`), `det_of_lowerTriangular` (:329), `BlockTriangular.mul`, `.submatrix`, `invertibleToBlock`; **no companion pivot-positivity or reduced-entries predicate anywhere**; step4-lattice :119 (verified grep): `Matrix.IsUpperTriangular` does not exist
[E] Name pattern   `grep IsColumnHermiteNormalForm` project-wide → project-only (declaring file + CoxMatrices/Basic.lean + CyclicSublattice{,/Classification}.lean); lean_local_search via siblings: `hermiteNormalForm*` project-only

Searched for both:
- the user's current form (square column-HNF predicate over ℤ) — not in mathlib
- the literature-standard forms (rectangular staircase HNF predicate; row-HNF variant;
  residue-parametrised ring form; any echelon predicate at all) — none in mathlib; the
  ONLY overlapping fragment is `Matrix.BlockTriangular`, which covers exactly one of the
  three defining conditions (triangularity) and none of the normal-form content
  (pivot positivity, residue reduction)

Concluded: **"found a partial match (`Matrix.BlockTriangular`); covers part of what we
want"** — the triangularity component only. The predicate as a whole is not in mathlib
in any form (all 5 methods, both forms; consistent with all four sibling verdicts and
step4-lattice :119).

---

### Normal-form check — Phase 5.5a

Equivalent formalisms this definition could take:
1. Prop structure with three named fields (current)
2. `def … : Prop := A.BlockTriangular id ∧ (∀ i, 0 < A i i) ∧ (∀ i j, i < j → A i j ∈ Set.Ico 0 (A i i))` — ∧-chain
3. Prop structure with field 1 restated as `blockTriangular : A.BlockTriangular id` (4c(a))

Does mathlib already have a canonical form for this idea? Not for HNF (none exists).
For the *triangularity component* mathlib's canonical carrier is `BlockTriangular` —
the normal-form principle therefore recommends formalism 3: state the component
against the canonical carrier rather than a raw quantification (this is precisely the
caller-flagged step4-lattice recommendation, verified interconvertible). The named-field
structure beats the ∧-chain (15+ dot-notation consumers). RHS convention: n/a (def).

### Syntactic generality — Phase 5.5b

Alternative restatements attempted:
- current three-field structure — matches every call site (fields consumed by name)
- ∧-chain def — strictly worse ergonomics at all 15+ consuming sites
- formalism 3 (BlockTriangular field) — same ergonomics, plus the mathlib det/mul API
  applies to the field directly; existing consumers of `belowDiagonal_eq_zero i j h`
  would migrate to `h.blockTriangular hij` or keep a bridge lemma

Chosen restatement: formalism 3 (or current + rfl-bridge lemma) — easiest to apply at
call sites because the expensive consumers are determinant computations, which become
one `det_of_upperTriangular` application.
Justification: verified — `Matrix.det_of_upperTriangular` applies through the field
with a one-token eta-expansion (lean_run_code clean).

### Superfluous-argument audit — Phase 5.5c

| # | Argument / typeclass | Essentially used? | Notes |
|---|----------------------|-------------------|-------|
| 1 | `[Preorder ι]` | partially | only `<` is used — `[LT ι]` compiles (verified); but the useful downstream (det API, uniqueness) needs `[LinearOrder ι] [Fintype ι]`, so the public form should tighten, not loosen (ChatGPT + literature). Not "superfluous" so much as mis-calibrated for a PR |
| 2 | `A : Matrix ι ι ℤ` (squareness) | yes | the diagonal-indexed fields presuppose square |
| 3 | ring ℤ | yes | the order-based normalisation is the ℤ-standard convention; genuine for this form |

### Statement-shape verdict (Phase 5.5d)

Normal form: REFACTOR (state the triangularity component against mathlib's canonical
`BlockTriangular` carrier — formalism 3 or the rfl-bridge)
Syntactic generality: RESTATE (same change; plus tighten the index binder for any PR)
Superfluous arguments: NONE to drop (one binder to *tighten* for a PR)

Overall: RESTATE-BEFORE-SHIP — the BlockTriangular carrier change (CHEAP, verified) and
the index-binder tightening are named in the Phase 7 next-action list; both are
worthwhile project-locally regardless of the upstreaming decision.

---

### Call sites — `Matrix.IsColumnHermiteNormalForm` (Phase 6.0)

Internal use count: **21** usage lines (excluding the declaring file)
External-to-file callers: **3 distinct files**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| XYin/PhD/Cox/CoxMatrices/Basic.lean:60–61 | `σ.inclusionMatrix.IsColumnHermiteNormalForm := by apply Matrix.isColumnHermiteNormalForm_fin_two` |
| XYin/PhD/Cox/CoxMatrices/Basic.lean:286 | `(hA : A.IsColumnHermiteNormalForm) (hB : B.IsColumnHermiteNormalForm)` — hypothesis of an injectivity/uniqueness lemma |
| XYin/PhD/Cox/CoxMatrices/Basic.lean:410, 950 | `have hHhnf : H.IsColumnHermiteNormalForm := hH` |
| XYin/PhD/Cox/CoxMatrices/Basic.lean:891 | `∃ U : SL(2, ℤ), (A * U.1).IsColumnHermiteNormalForm` — SL₂-flavoured existence restatement |
| XYin/PhD/Cox/CoxMatrices/Basic.lean:905 | `(hH : H.IsColumnHermiteNormalForm)` |
| XYin/PhD/Cox/CyclicSublattice.lean:93, 95, 97, 365, 368, 372 | field consumers: `h.isColumnHermiteNormalForm.belowDiagonal_eq_zero 1 0 …`, `.diagonal_pos 0/1` |
| XYin/PhD/Cox/CyclicSublattice/Classification.lean:31–36, 76–82 | field consumers: `.diagonal_pos`, `.reduced 0 1`, `.belowDiagonal_eq_zero` |
| (in-file, structural) HermiteNormalForm.lean:222 | the `Module.Basis.HermiteNormalForm` bundle carries it as its defining field — every sibling decl is stated against it |

Inline-derivation grep (equivalent re-derived elsewhere without using the predicate?):
(none) — no site re-states the three conditions raw; every triangular/positive/reduced
fact in the project flows through the predicate's fields. (The three ad-hoc determinant
computations noted in step4 :56 are *downstream* of the fields, not re-derivations of
the predicate.)

Signal (per 6.0.1): K = 21 ≥ 3 across 3 files, no inline re-derivation → real,
load-bearing API; it is the foundational predicate of the entire HNF + CoxMatrices +
CyclicSublattice development. Strong YES-leaning composability signal — tempered, as
with all siblings, by the shippability coupling.

### Composition check (Phase 6)

Can `Matrix.IsColumnHermiteNormalForm` be derived from mathlib in ≤3 chained calls?

Attempt 1 (conjunction of mathlib predicates):
`A.BlockTriangular id ∧ (∀ i, 0 < A i i) ∧ (∀ i j, i < j → A i j ∈ Set.Ico 0 (A i i))`
  - Mathlib decls used: `Matrix.BlockTriangular` (Block.lean:61) — and nothing else
    exists: mathlib has NO pivot-positivity predicate and NO reduced-entries/echelon
    predicate (Phase 5 [D], fresh grep: zero files)
  - Result: **fails as a composition** — 2 of the 3 conjuncts are raw quantified
    conditions, not mathlib calls; per the composition heuristics an ∧ of mostly-raw
    conditions is a new definition, not a composition. (And a named, documented
    predicate is required regardless: the bundle field, 21 call sites, and the
    existence/uniqueness theorems all need a stable name.)

Attempt 2 (via SNF or any normal-form machinery): mathlib's SNF is a *bundle of bases*
(`Module.Basis.SmithNormalForm`), not a matrix-shape predicate; there is no matrix-side
normal-form predicate to specialise.
  - Result: fails.

Conclusion: **NOT-COMPOSABLE** (one component reusable as a carrier — the Phase 4c(a)
respelling — but the predicate as a whole is genuinely new).

---

## Verdict: `Matrix.IsColumnHermiteNormalForm`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the three-condition shape is the standard HNF predicate;
  conventions (row/column action, upper/lower, residue window, reduction position) are
  a documented free choice — the project's combination is the polynomial-matrix
  column-Hermite style, internally coherent (in-file rank-2 uniqueness proves
  canonicity) but not the dominant integer-matrix "column" convention; the
  literature-standard *scope* is rectangular staircase, and ring-generalisation goes
  via residue parametrisation, not order (AFP; ChatGPT: ordered-ring widening is a
  false generalisation).
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD in shape
  (square vs rectangular), with zero sound mechanical widenings (both compiling probes
  rejected: `LT` is the wrong direction, ordered-ring fails the Q9 guard) — verdict-gate
  false-positive class 5 excludes `YES-but-generalise-first`; plus one verified CHEAP
  modern-idiom respelling (triangularity via `Matrix.BlockTriangular id`, step4 :55–59,
  lean_run_code-verified).
- Phase 4.5 risk: NONE.
- Mathlib search (Phase 5): partial match only — `Matrix.BlockTriangular` covers the
  triangularity component; mathlib has NO echelon or Hermite-form predicate of any kind
  (fresh grep, zero files), consistent with all four sibling verdicts.
- Composition check (Phase 6): NOT-COMPOSABLE (2 of 3 conjuncts have no mathlib name);
  K = 21 call sites across 3 files — the foundational predicate of the whole
  development.

**Rationale:**

Both NO buckets fail on the evidence: mathlib verifiably has no Hermite normal form in
any formulation (re-confirmed fresh: no echelon predicate, no `IsUpperTriangular`, no
pivot/residue predicate — only `BlockTriangular`, which covers one of three
conditions), and the predicate is not a composition (two conditions have no mathlib
carrier, and the bundle field + 21 call sites + existence/uniqueness theorems require a
named predicate regardless). Both YES buckets also fail as self-resolving verdicts, for
reasons that mirror and inherit the sibling BORDERLINEs but add predicate-specific
judgment calls. `YES-add-as-is` fails because a defining predicate cannot ship bare:
ChatGPT MCP is explicit that "a predicate plus only 2×2 existence/uniqueness theorems
is unlikely to be accepted as a standalone mathlib contribution", and the attached
theory is exactly the rank-2 pilot whose scope question the sibling reports already
routed to the user; moreover the Phase 5.5 verdict is RESTATE-BEFORE-SHIP
(BlockTriangular carrier; index binder). `YES-but-generalise-first` fails the gate: the
literature-standard scope (rectangular staircase; residue-parametrised ring form) is a
redesign, not a compile-verifiable widening — the two widenings that DO compile were
both rejected (wrong direction; Q9 false generalisation). What is genuinely new versus
the sibling reports: (1) the predicate is the one decl in the file that is *already*
index-general (arbitrary `Preorder ι` — in fact looser than the literature wants), so
its narrowness is in shape (square) and convention, not rank; (2) the caller-flagged
carrier question resolves affirmatively — the triangularity field is verified
interconvertible with `A.BlockTriangular id` and restating it (or adding the rfl-bridge
plus `det_eq`/`det_pos`) is CHEAP, kills three ad-hoc determinant computations, and is
worth doing project-locally regardless of any upstreaming decision; (3) the
convention/naming choice ("Column" + upper triangular + row-wise residues) is coherent
but nonstandard-dominant, and locking it into a mathlib name is a taste decision
reviewers will engage with. These are judgment calls the skill may not self-resolve.

**Numbered questions (≤5):**

1. (= sibling reports' shared Q1, decisive) Are you committing to the mathlib-right HNF
   development (rank-n existence + uniqueness over ℤ, matrix + basis forms)? The
   predicate ships only as the foundation of that unit; if no, it stays project-local
   with everything else. (yes/no)
2. Decision-independent refactor, recommended now: restate the triangularity field as
   `blockTriangular : A.BlockTriangular id` (or keep the field and add the rfl-bridge
   lemma) plus derived `det_eq : A.det = ∏ i, A i i` and `det_pos`, per
   step4-lattice :55–59 — verified CHEAP, collapses the three ad-hoc `det_fin_two`
   computations at CyclicSublattice.lean:387/582 and Classification.lean:43, and scales
   past rank 2. Apply? (yes/no)
3. Shape scope for the public predicate: square-nonsingular first (with rectangular as
   a later extension — must then be clearly a specialisation) or rectangular staircase
   from day one (ChatGPT: "avoid a public square-only 'main' definition")?
   (square-first / rectangular)
4. Convention + naming: keep the current combination (right action, upper triangular,
   row-wise nonnegative residues — Cox-matching, poly-matrix column-Hermite style) and
   document it explicitly, or align with the dominant Cohen row convention / rename
   (the literature's integer-matrix "column" HNF is usually lower triangular, so the
   current name will draw reviewer comment)? (keep+document / align / rename)
5. Index binder for the public form: tighten `[Preorder ι]` to `Fin n` or
   `[LinearOrder ι] [Fintype ι]` (needed by the det/uniqueness API; ChatGPT: Preorder
   is "too loose"), keeping the loose form project-local if desired? (yes/no)

**Next action:** answer Q1 jointly with the four sibling reports (all five resolve as a
unit — the predicate is the foundation the others are stated against). Q2 can be acted
on immediately regardless (project-local improvement; `/generalise` or a small refactor
ticket). Yes to Q1 ⇒ fold Q3–Q5 into the `/develop` ticket the sibling reports specify
("n×n integer column HNF: existence + uniqueness + chooser, matrix + basis forms,
SNF-template layout"), with the predicate's convention/naming/carrier decisions settled
first since every other decl is stated against it.
