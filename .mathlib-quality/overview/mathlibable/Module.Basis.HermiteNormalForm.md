# /mathlibable report — `Module.Basis.HermiteNormalForm`

Assessed 2026-07-18 against mathlib pin 2026-05-28 (`2abc2425`). Mode A, full exhaustive
protocol. This is the ninth (and central) verdict of the HermiteNormalForm.lean family;
the eight stored sibling reports in this directory were read first and are cited where
concept-level coverage genuinely overlaps (HNF literature landscape, mathlib-has-no-HNF,
scope question). Everything structure-specific — the bundling design versus mathlib's
`Module.Basis.SmithNormalForm`, the redundant-`matrix`-field question, the
square-vs-rectangular shape of the *bundle*, and the mechanical-widening probes — was
verified fresh.

---

### Baseline (Phase 0)

- lake build:               ✓ clean ("Build completed successfully (3909 jobs)"; only an informational style-linter note)
- decl `Module.Basis.HermiteNormalForm`: ✓ resolved at `XYin/PhD/Cox/HermiteNormalForm.lean:213`
- kind:                      structure (data-carrying, in `Module.Basis` namespace)
- has sorry:                 no
- module docstring summary:  Hermite-normal-form API for full-rank integer submodules (Cox Ch. 11); "Unlike Smith normal form, Hermite normal form is canonical only after fixing the ambient basis, so that basis is an explicit parameter of `Module.Basis.HermiteNormalForm`. The bundled definition is available in arbitrary finite rank; the constructive existence theorem currently supplies the rank-two case."

---

### Statement (Phase 1)

`Module.Basis.HermiteNormalForm` is a definition (bundling structure) of the following:

For a free ℤ-module M with a *fixed* ambient basis bM indexed by Fin n, and a submodule
N ≤ M, an HNF datum for N relative to bM is: a basis bN of N (also indexed by Fin n, so
full rank is built in), together with the n×n integer matrix of the inclusion N ↪ M in
the bases (bN, bM), such that that matrix is in column Hermite normal form (upper
triangular, positive pivots, above-pivot entries reduced into [0, pivot)). This is the
lattice-theory package "the HNF basis of a sublattice relative to a chosen coordinate
system" — the object whose uniqueness (proved in-file at rank 2: `matrix_eq` :278,
`bN_eq` :338) gives the classical bijection between index-m sublattices and HNF matrices
of determinant m (Cox Ch. 11; arXiv 2310.12519).

Variables / typeclasses involved (Lean side):
- `M : Type*` `[AddCommGroup M]` — ambient abelian group (ℤ-module)
- `{n : ℕ}` `(bM : Basis (Fin n) ℤ M)` — the fixed ambient basis, a **parameter** (not a field) — the load-bearing design choice; HNF is basis-relative
- `(N : Submodule ℤ M)` — the sublattice

Fields (the bundled data):
- `bN : Basis (Fin n) ℤ N` — the HNF basis of the submodule
- `matrix : Matrix (Fin n) (Fin n) ℤ` — the inclusion matrix, stored as data
- `toMatrix_eq : LinearMap.toMatrix bN bM N.subtype = matrix` — the propositional link
- `isColumnHermiteNormalForm : matrix.IsColumnHermiteNormalForm` — the normal-form property

Conclusion (math): "an HNF datum for N relative to bM" — the basis-level packaging of
column Hermite normal form.

Conclusion (Lean): n/a — definition (structure).

**Design comparison with mathlib's direct precedent (verified fresh).**
`Module.Basis.SmithNormalForm` (`Mathlib/LinearAlgebra/FreeModule/PID.lean:408`) is:
`structure SmithNormalForm (N : Submodule R M) (ι : Type*) (n : ℕ)` with fields
`bM : Basis ι R M`, `bN : Basis (Fin n) R N`, `f : Fin n ↪ ι`, `a : Fin n → R`,
`snf : ∀ i, (bN i : M) = a i • bM (f i)`. Three deltas:
1. **Ambient basis:** SNF stores `bM` as a field (SNF chooses both bases); the HNF bundle
   takes `bM` as a parameter (HNF is canonical only relative to a fixed basis). This
   delta is *mathematically correct* — confirmed by ChatGPT design review (Phase 3 row 4)
   and by the AFP precedent (matrix-first, ambient coordinates fixed externally).
2. **Shape:** SNF is rectangular (`bN` indexed `Fin n`, `bM` indexed `ι`, related by an
   embedding — arbitrary-rank submodule); the HNF bundle is square/full-rank-only (both
   `Fin n`). Here the project is *narrower than its own precedent*.
3. **Matrix representation:** SNF stores the minimal data (`a`, `f`) with one defining
   relation; the HNF bundle stores the full `matrix` as a redundant field with the
   propositional link `toMatrix_eq` (the matrix is determined by `bN`, `bM`, `N.subtype`).

---

### Size classification (Phase 2a)

Verdict: BIG
Reason: it introduces a new mathematical structure (the HNF bundle — the file's central
type, named in the module docstring) packaging a concept named after a person (Hermite).
(Literature width EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 4 fields (structure declaration; not a one-line def)
One-liner verdict: MULTI-LINE — check skipped. (Note: even under a strict reading the
structure bundles four fields with two propositional constraints; nothing one-line-ish.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

Concept-level channels were run exhaustively earlier the same day by the sibling
assessments at this pin; rows marked [SIB:decl] cite those stored tables verbatim rather
than re-spending rate-limited channels on identical queries. Structure-specific rows are
fresh.

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form, fresh) | "Hermite normal form" basis sublattice "fixed basis" canonical unique lattice ℤ^n definition | yes | For any lattice L ⊂ ℤⁿ there is a **unique basis in HNF**; fixing a basis of Λ gives a bijection {index-m sublattices} ↔ {HNF matrices of det m}, with "for every basis B of Λ a unique basis B′ of Λ′ with B′ = BH" | Wikipedia HNF; Shmonin EPFL lattice notes; Nguyen MPRI Lecture 2; arXiv 2310.12519 — the *bundle content* (basis + matrix + HNF property, relative to fixed ambient basis) is exactly the literature's package |
|  2 | WebSearch (general form)         | HNF existence uniqueness PID/Bézout, rectangular scope | yes | Rectangular m×n over ℤ is standard; PID/Bézout via chosen associate+residue representatives | [SIB:Submodule.exists_hermiteNormalForm row 2] — Storjohann thesis, arXiv 2502.10416 |
|  3 | WebSearch (formalisation precedent, fresh) | Isabelle AFP Hermite normal form Divasón Aransay formalization uniqueness echelon form | yes | AFP "Hermite" (Divasón–Aransay): HNF via elementary row ops on the Echelon Form entry, **matrix-first** (no basis-level bundle), uniqueness formalised; general setting incl. ℤ and K[x] matrices | isa-afp.org/entries/Hermite.html; Springer 978-3-319-99957-9_3; also Modular_arithmetic_LLL_and_HNF_algorithms AFP entry. **No formalisation bundles HNF at the submodule-basis level** — the project's bundle would be the first |
|  4 | ChatGPT MCP (gpt-5.4, high, fresh) | full design review of this exact structure vs `Basis.SmithNormalForm` (bundling, matrix field, square vs rectangular, coupling to existence) | yes | (i) ambient-basis-as-**parameter** is the mathematically right bundling for HNF ("bM is part of the context of the notion, not the choice data") — unlike SNF; (ii) the `matrix` field is **redundant data** — recommended minimal bundle: `bN` + `isHNF : (LinearMap.toMatrix bN bM N.subtype).IsColumnHermiteNormalForm`, with `matrix` a projection def; (iii) **"design the bundle rectangular from day one"** — SNF is rectangular at its core and specialises to full-rank later (`smithNormalFormOfRankEq`); retrofitting structure fields breaks all consumers; keep `Fin` indices (HNF needs an order); ℤ-only is more acceptable for a first PR than square-only; (iv) the bundle is "not logically coupled to a general-rank existence theorem, but its chances in mathlib are partly coupled to one … a top-level bundle whose only existence theorem is rank 2 is much more likely to be seen as too project-specific"; predicate + uniqueness can land earlier | The structure-specific channel this report exists for |
|  5 | Local references                 | `.mathlib-quality/references/` grep "hermite" | n/a | directory absent/empty at this path | recorded n/a (consistent with all 8 sibling reports) |
|  6 | nLab                             | "Hermite normal form" | yes | dedicated page: canonical representative of unimodular-equivalence classes; conventions vary, each gives uniqueness | [SIB:Submodule.exists_hermiteNormalForm row 6] |
|  7 | nCatLab (if categorical)         | n/a — not a categorical concept; the nLab page itself is elementary | n/a | — | [SIB: same row 7] |
|  8 | Stacks Project (if alg geom)     | n/a — not an algebraic-geometry concept; no HNF tag in Stacks' modules-over-PID material | n/a | — | [SIB: same row 8] |
|  9 | MathOverflow / Math.StackExchange| sublattice HNF basis generality | yes | unique HNF basis for every sublattice of ℤⁿ; index-m bijection | [SIB: same row 9] — Straub notes, UCSD CSE 206A |
| 10 | recent arXiv (last 5 years)      | via rows 1–3 result sets | yes | arXiv 2310.12519 (sublattice ↔ HNF bijection — the bundle's raison d'être), 2502.10416, 2605.07784 (Labahn–Storjohann lattice formulation) | contemporary usage rectangular over ℤ, ring-generalised in research |

### Literature summary (Phase 3)

Concept identified as: the Hermite-normal-form basis of a sublattice relative to a fixed
ambient basis (the object underlying the sublattice ↔ HNF-matrix bijection).
Sources agree on the standard form: yes on content (basis + triangular positive reduced
inclusion matrix, canonical after fixing the ambient basis); conventions (upper/lower,
row/column, residue window) are a documented free choice [SIB:Matrix.IsColumnHermiteNormalForm].
Most general standard form: arbitrary-rank (rectangular) sublattices of ℤⁿ; ring-
generalised to Bézout/PID with chosen associate + residue representatives (AFP does the
general-setting matrix version).
Generality dimensions where the literature varies:
  - rank/shape: full-rank square (Cox, crypto lecture notes) to arbitrary-rank rectangular (standard) — most general: rectangular
  - ring: ℤ (dominant) to Bézout domain with normalisation data (AFP, research) — most general: Bézout + representatives
  - packaging: matrix-first (AFP, all formalisations, most textbooks) vs basis-level bundle (this project — **no precedent bundles at the basis level**; mathlib's own SNF bundle is the only analogous object anywhere)
Disagreement with the literature: none on content; the *bundling itself* is novel
packaging (mathlib-idiomatic, SNF-templated) rather than a literature form.

---

### Generality analysis — `Module.Basis.HermiteNormalForm` (Phase 4)

Literature-standard form (from Phase 3): HNF datum for an arbitrary-rank submodule
(rectangular n×m inclusion matrix) over ℤ, conventions fixed; ring axis Bézout-ready.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `bM : Basis (Fin n) ℤ M` (parameter) | fixed ambient basis, explicit parameter | same — HNF is basis-relative | NO (and shouldn't) | mathematically load-bearing; ChatGPT + AFP confirm parameter (not field) is the right polarity; this is the correct delta from SNF |
| 2 | `bN : Basis (Fin n) ℤ N` (same index as bM) | full-rank square only | `Basis (Fin m) ℤ N`, m ≤ n (rectangular) | yes in the literature, **NO mechanically** | verified failing probe: the rectangular bundle does not typecheck — `matrix : Matrix (Fin n) (Fin m) ℤ` cannot satisfy `IsColumnHermiteNormalForm`, which is square-only (`Matrix ι ι ℤ`). Requires redesigning the predicate first (itself BORDERLINE) → false-positive class 5 |
| 3 | ring ℤ | ℤ-hard-coded (inherited from the predicate) | Bézout domain + normalisation data | yes in the literature, NO mechanically | predicate-level redesign (residue parametrisation, not ordered-ring widening — the ordered-ring probe was rejected by the Q9 guard in [SIB:Matrix.IsColumnHermiteNormalForm]) |
| 4 | index `Fin n` | concrete ordered index | `ι` finite + order | yes — **verified compiling** (probe A: the bundle re-declared over `[Fintype ι] [DecidableEq ι] [Preorder ι]` typechecks) | but NOT endorsed: ChatGPT explicitly recommends keeping `Fin` ("HNF needs an order; Fin m, Fin n are the natural ordered indices"); SNF also uses `Fin n` for the submodule side. Compiling ≠ improving |
| 5 | `matrix` field + `toMatrix_eq` | redundant data field with propositional link | n/a (packaging question, see 4c) | — | see Phase 4c Q3/Q8-analogue |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (shape: square/full-rank vs
rectangular; ring: ℤ vs Bézout) — but **neither narrowness is mechanically reachable**:
- Rectangular probe (probe B, `lean_run_code`): FAILS — "Application type mismatch:
  matrix has type Matrix (Fin n) (Fin m) ℤ but is expected to have type Matrix ?m ?m ℤ
  in matrix.IsColumnHermiteNormalForm". The bundle cannot be widened without first
  redesigning the square-only predicate → verdict-gate false-positive class 5 (multi-decl
  redesign, not a single mechanical edit).
- Ring probe: not attempted fresh; the predicate report verified the ordered-ring
  widening is a false generalisation (Q9 guard) and the sound route (residue
  parametrisation à la AFP) is a redesign. Class 5 by inheritance.
- Index probe (probe A): COMPILES, but is not a literature- or reviewer-endorsed
  improvement (Fin is the recommended carrier for an ordered pivot structure).

Number of weakening opportunities found: 1 compiling (index, not endorsed), 2 real but
non-mechanical (shape, ring). `YES-but-generalise-first` is therefore unavailable.
Cost of the real restatement (rectangular predicate + bundle): EXPENSIVE — predicate
redesign + all four in-file consumers + uniqueness/existence reproofs. (Cost noted for
sequencing only, not as a verdict factor.)

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|---|---|---|---|
| 1 | Typeclasses instead of bundled hypotheses? | no | — | the bundle's fields are choice data (a basis), not properties; a class would be wrong (HNF data is not propositional) |
| 2 | Filters/nets vs sequences? | no | — | no topology; finite combinatorial-algebraic object |
| 3 | Universal property instead of construction? | partially | the bundle IS the mathlib-idiomatic packaging (SNF template); but the **minimal-field variant** applies: drop `matrix`+`toMatrix_eq`, keep `bN` + `isHNF : (LinearMap.toMatrix bN bM N.subtype).IsColumnHermiteNormalForm`, define `matrix` as a projection | removes a redundant-data field; every consumer stops rewriting through `toMatrix_eq`; matches SNF's minimal-data style (`a`, `f`, one relation). Counter-argument (real): the stored field lets constructors carry a *literal* matrix definitionally (Classification.lean:136–145 builds the bundle with `σ.inclusionMatrix` directly), a defeq-control benefit the minimal bundle loses |
| 4 | Bundled substructure vs set-with-predicate? | no | already bundled — that's the point | — |
| 5 | Weaken concrete typeclass via hierarchy? | no (not mechanically) | ring axis is a predicate redesign (4a row 3) | — |
| 6 | Higher-categorical generalisation? | no | elementary lattice theory; nLab offers no categorical abstraction [SIB row 7] | — |
| 7 | Concrete index generalises? | formally yes (probe A compiles) | not endorsed — Fin is the right ordered index (ChatGPT, SNF precedent) | none identified |
| 8 | Concrete-via-abstract? | no | the structure has no proof body; its parameters are already abstract (any M, any bM, any N). The concrete narrowness (ℤ, square) is the 4a/4b axis, not a proof-body artifact | — |
| 9 | False-generalisation guard | yes, applied | the rectangular reformulation preserves meaning (it IS the literature object) — not a false generalisation, just not mechanically reachable; the index widening is meaning-preserving but valueless; the ordered-ring ring-widening was already rejected as a false generalisation at the predicate level | safeguard recorded |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — the **minimal-field bundle** (drop `matrix`/`toMatrix_eq`,
ChatGPT-recommended, SNF-style) and the **rectangular shape** (SNF-templated
`{m n : ℕ}` with `bN : Basis (Fin m) ℤ N`, full-rank case as a later specialisation à la
`smithNormalFormOfRankEq`).
  - Cost: MODERATE (minimal-field: touches every consumer's constructor/rewrites) to
    EXPENSIVE (rectangular: predicate redesign first).
  - Mathlib downstream enabled: alignment with the SNF file's API shapes
    (`Submodule.smithNormalForm` returning a sigma over rank; `smithNormalFormTopBasis`/
    `BotBasis`/`Coeffs` projections); arbitrary-rank sublattice applications
    (kernels, non-saturated submodules) that the square bundle cannot state.
  - Real mathematical improvement: yes for rectangular (states the actual literature
    scope); genuinely debatable for the matrix field (redundant data vs defeq-control —
    a maintainer-taste call, surfaced as a BORDERLINE question rather than self-resolved).

### Proof strategy — `Module.Basis.HermiteNormalForm` (Phase 4.6)

| # | Question | Applies? | Idiomatic alternative | Cost of switch |
|---|---|---|---|---|
| 1 | Topology ε-δ vs filters | no — no proof body (structure) | — | — |
| 2 | Element-wise vs point-free | no | — | — |
| 3 | Sequences vs nets | no | — | — |
| 4 | Construction vs universal property | no — the bundle is the SNF-templated packaging, mathlib's own idiom for exactly this situation | — | — |
| 5 | Missing mathlib helpers | yes (for the family, not this decl): mathlib lacks the HNF predicate, any echelon predicate, and rectangular-HNF API — the whole family is the missing API | file as the HNF-development PR series | — |

### Proof strategy verdict (Phase 4.6)

Current strategy: MATHLIB-IDIOMATIC (a definition with no proof; its packaging follows
mathlib's own `Basis.SmithNormalForm` template, with one deliberate, mathematically
justified polarity flip — ambient basis as parameter).

---

### Diamond / defeq risk — `Module.Basis.HermiteNormalForm` (Phase 4.5)

| # | Risk | Verdict | Evidence / rationale |
|---|---|---|---|
| 1 | Typeclass diamond | none | plain `structure`, not a class; no instances declared for it anywhere in the project (grep: zero `instance … HermiteNormalForm`); its fields synthesize nothing |
| 2 | Reducibility leak | none | no `@[reducible]`; structures are opaque; fields accessed by projection only |
| 3 | Non-canonical unfolding | low | the `matrix` field is redundant relative to `bN` (linked by `toMatrix_eq`); two bundles for the same N are provably but not definitionally equal in `matrix` — mitigated in-file by the uniqueness theorems `matrix_eq`/`bN_eq` (rank 2). This is the data-redundancy design question, not a simp trap; no `simp` lemma unfolds the structure |
| 4 | Instance priority collision | none | not an instance |
| 5 | Universe-polymorphism issues | none | single universe on `M`; `Fin n`-indexed throughout; no forced annotations (probe A re-declared it over general `ι` without universe complaint) |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort`; consumers use named projections (`h.bN`, `h.matrix`, `h.isColumnHermiteNormalForm`) |

### Risk verdict (Phase 4.5)

Overall risk: LOW (single low: the redundant-field defeq surface, carried into the
BORDERLINE questions). Top risks: none HIGH. Mitigations: the minimal-field variant
(4c Q3) removes row 3 entirely.

---

### Mathlib search-status: `Module.Basis.HermiteNormalForm` (Phase 5)

[A] Lean-Finder       (via sibling five-method searches, same day, same pin)   no hits for any HNF concept [SIB:Submodule.exists_hermiteNormalForm, Matrix.IsColumnHermiteNormalForm]
[B] Loogle            `"Hermite"` (fresh)                                       hits: only `NumberField.hermiteTheorem.*` (finiteness of number fields of bounded discriminant) and Hermite polynomials — no normal form
[C] LeanSearch        "basis of a submodule such that the matrix of the inclusion map is upper triangular Hermite normal form" (fresh)   no HNF hit; top results are exactly the SNF family (`Submodule.smithNormalForm`, `smithNormalFormOfLE`, `smithNormalFormTopBasis/BotBasis`, `basisOfPidOfLE`) — confirming SNF is the nearest object and there is no HNF analogue
[D] Grep mathlib src  `-i "hermite"` over Mathlib/ (fresh)                      3 files only: Hermite polynomials (2), Hermite's discriminant theorem (1); `echelon|HermiteForm` over LinearAlgebra/: only PID.lean (SNF); no HNF, no echelon predicate
[E] Name pattern      `HermiteNormalForm`, `hermiteNormalForm` (fresh grep)     zero matches in mathlib

Searched for both:
  - the user's current form (basis-level HNF bundle): absent
  - the literature-standard form (rectangular HNF, matrix or basis formulation): absent —
    mathlib has no Hermite normal form in any formulation (consistent with all eight
    sibling verdicts; the nearest partial artifacts are `Basis.SmithNormalForm`
    (PID.lean:408, the direct structural template) and `FixedDetMatrices.reduce_mem_reps`
    (a differently-normalised 2×2 near-HNF reduction, [SIB:Matrix.exists_right_mul_…]))

Concluded: "not in mathlib (all 5 methods exhausted, plus the literature-standard form);
nearest object is `Module.Basis.SmithNormalForm`, which forgets exactly the fixed-ambient-
basis information this structure exists to retain"

---

### Statement shape (Phase 5.5)

### Normal-form check

Equivalent formalisms this structure could take:
1. current: bundle (bN, matrix, toMatrix_eq, isHNF) with bM a parameter
2. minimal bundle: (bN, isHNF-of-toMatrix) with `matrix` a projection def (ChatGPT-recommended)
3. unbundled: `∃ bN, (LinearMap.toMatrix bN bM N.subtype).IsColumnHermiteNormalForm` (existence-statement only, no reusable datum)
4. SNF-style both-bases bundle (bM as field) — REJECTED: mathematically wrong for HNF (basis-relativity lost)

Does mathlib already have a canonical form for this idea? No HNF form at all; for the
*idiom*, mathlib's canonical packaging of "basis of a submodule in normal form" is the
`Basis.SmithNormalForm` bundle → a bundle (1 or 2) is the canonical shape, not (3).
RHS convention respected: n/a (definition, not an iff).

### Syntactic generality

Alternative restatements attempted: (1) vs (2) above; probe A (general ι) compiles but
is unendorsed. Chosen restatement: the bundle with bM as parameter — easiest to apply at
call sites needing the datum repeatedly (the project's `S.hermiteNormalForm.…` chains).
Justification: parameter-bM lets distinct HNF data over the *same* coordinate system be
compared — precisely what the uniqueness theorems (`matrix_eq h h'`) and the
classification (Classification.lean:175) need; a field-bM (SNF-style) could not even
state them.

### Superfluous-argument audit

| # | Argument / typeclass | Essentially used? | Notes |
|---|---|---|---|
| 1 | `[AddCommGroup M]` | yes | needed for `Submodule ℤ M`, `Basis … ℤ M` |
| 2 | `bM` (parameter) | yes | basis-relativity is the definition's content |
| 3 | `N` | yes | the object being put in normal form |
| 4 | `matrix` field + `toMatrix_eq` | debatable | redundant data (determined by bN, bM); kept for defeq control at construction sites — the standing design question |

### Statement-shape verdict (Phase 5.5)

Normal form: OK (bundle is the mathlib-canonical idiom, per SNF)
Syntactic generality: OK for parameter-bM; RESTATE candidates exist (minimal-field,
rectangular) but are judgment/redesign, not syntax
Superfluous arguments: 0 parameters to drop; 1 field pair (`matrix`/`toMatrix_eq`)
flagged as possibly redundant
Overall: SHIP-AS-STATED **only if** the human resolves the field-redundancy and shape
questions the other way; otherwise RESTATE-BEFORE-SHIP (minimal rectangular bundle) —
carried into the Phase 7 questions.

---

### Call sites — `Module.Basis.HermiteNormalForm` (Phase 6.0)

Internal use count: 15+ distinct declarations consume the bundle (NOT counting the
declaring file: 2 external files; counting the declaring file's own downstream API:
3 files).
External-to-file callers: 2 distinct files (plus heavy in-file API).

| Caller file:line | Usage pattern (one-line excerpt) |
|---|---|
| XYin/PhD/Cox/CyclicSublattice.lean:56 | return type `Module.Basis.HermiteNormalForm L.latticeBasis S.carrier` (def `CyclicSublattice.hermiteNormalForm`) |
| XYin/PhD/Cox/CyclicSublattice.lean:93–97 | field access `h.isColumnHermiteNormalForm.belowDiagonal_eq_zero/diagonal_pos` |
| XYin/PhD/Cox/CyclicSublattice.lean:365–372 | `S.hermiteNormalForm.isColumnHermiteNormalForm.…` (pivot positivity/triangularity of the chosen bundle) |
| XYin/PhD/Cox/CyclicSublattice.lean:595 | `open Module.Basis.HermiteNormalForm in` (namespace-level API use) |
| XYin/PhD/Cox/CyclicSublattice/Classification.lean:31–36, 76–82 | field accesses on a bundle `h` (diagonal_pos, reduced, belowDiagonal) |
| XYin/PhD/Cox/CyclicSublattice/Classification.lean:136–145 | constructor use: `⟨bN, σ.inclusionMatrix, …, σ.inclusionMatrix_isColumnHermiteNormalForm⟩ : Module.Basis.HermiteNormalForm L.latticeBasis …` |
| XYin/PhD/Cox/CyclicSublattice/Classification.lean:158, 175 | uniqueness applied: `S.hermiteNormalForm.matrix_eq (σ.inclusionHermiteNormalForm L)` — the classification's key step |
| (declaring file) HermiteNormalForm.lean:230–470 | the whole in-file API: `repr_apply`, `range_toLin_matrix_eq`, `matrix_eq`, `bN_eq`, `index_eq_natAbs_det`, `quotient_isAddCyclic_…`, `exists_hermiteNormalForm`, `hermiteNormalForm` |

Inline-derivation grep (equivalent re-derived without the bundle?): (none) — every
consumer of "an HNF basis datum" goes through the structure; no site re-carries the
(basis, matrix, property) triple by hand.

Pattern: K ≥ 3 internal uses across multiple files, no inline re-derivation → real API,
the type on which the file's two main theorems (uniqueness) and the sublattice
classification are stated. Phase 7 leaning: YES-* family, blocked only by the scope/shape
questions.

### Composition check (Phase 6)

Can `Module.Basis.HermiteNormalForm` be derived from mathlib in ≤3 chained calls?

Attempt 1: express the type via mathlib primitives — fails immediately: the field type
`Matrix.IsColumnHermiteNormalForm` does not exist in mathlib (Phase 5), and mathlib has
no echelon/triangular-normal-form predicate to substitute (`Matrix.BlockTriangular`
covers only the first of the three conditions [SIB:Matrix.IsColumnHermiteNormalForm]).
  - Mathlib decls used: n/a
  - Result: fails — the type is not expressible, let alone composable
Attempt 2: substitute `Basis.SmithNormalForm` — fails mathematically: SNF stores its own
`bM` field and forgets the fixed ambient basis; the HNF bundle's content (canonicity
relative to bM, uniqueness `matrix_eq`) cannot be stated through SNF (confirmed by two
independent channels in [SIB:Submodule.exists_hermiteNormalForm Phase 6] and fresh
ChatGPT row 4: SNF-derivability explicitly denied).

Conclusion: NOT-COMPOSABLE.

---

## Verdict: `Module.Basis.HermiteNormalForm`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the bundle's *content* (unique HNF basis of a sublattice
  relative to a fixed ambient basis) is the standard package behind the index-m
  sublattice bijection; no formalisation bundles it at the basis level (AFP is
  matrix-first) — mathlib's own `Basis.SmithNormalForm` is the only structural precedent,
  and this structure follows it with one deliberate, *verified-correct* polarity flip
  (ambient basis as parameter, per basis-relativity; ChatGPT concurs explicitly).
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD on shape
  (square/full-rank vs rectangular) and ring (ℤ vs Bézout), with **zero sound mechanical
  widenings**: the rectangular probe fails to typecheck against the square-only predicate
  (verified, `lean_run_code`), the ring axis is a predicate redesign, and the one
  compiling widening (index `ι`) is explicitly not endorsed by the design review —
  verdict-gate false-positive class 5 excludes `YES-but-generalise-first`. Phase 4c found
  two real modern-idiom candidates (minimal-field bundle; rectangular-from-day-one), both
  judgment calls or redesigns, not mechanical restatements.
- Phase 4.5 risk: LOW (one low row: the redundant `matrix` field's defeq surface).
- Mathlib search (Phase 5): no Hermite normal form in mathlib in any formulation (fresh
  Loogle/LeanSearch/grep + all sibling five-method searches); LeanSearch's top hits for
  the concept are precisely the SNF family — the template, not a substitute.
- Composition check (Phase 6): NOT-COMPOSABLE — the type is not even expressible in
  mathlib (predicate absent; SNF forgets the ambient basis). K ≥ 15 uses across 3 files,
  no inline re-derivation: this is the central type of the development.

**Rationale:**

Both NO buckets fail on the evidence: mathlib verifiably has no HNF anywhere, and nothing
in mathlib can express — let alone compose to — a structure whose fields mention a
predicate mathlib lacks and whose content (fixed-ambient-basis canonicity) mathlib's SNF
deliberately forgets. Both YES buckets also fail as self-resolving verdicts.
`YES-add-as-is` fails because the bundle is strictly narrower than both the literature
scope and mathlib's own SNF template on the same axis: `Basis.SmithNormalForm` is
rectangular at its core (arbitrary-rank submodule via `Fin n ↪ ι`) and specialises to
full rank later (`smithNormalFormOfRankEq`), whereas this bundle hard-codes the square
full-rank case — and since retrofitting structure fields breaks every consumer, shape is
exactly the axis that must be right on day one (fresh ChatGPT review, verbatim: "design
the bundle rectangular from day one"; "ℤ-only is more acceptable for a first PR than
square-only"). `YES-but-generalise-first` fails the verdict gate: the rectangular
restatement is not a verified mechanical weakening — the probe errors because the
square-only predicate `IsColumnHermiteNormalForm` cannot accept a rectangular matrix, so
the generalisation is a multi-declaration redesign (predicate + bundle + uniqueness +
existence), i.e. false-positive class 5, routed to a human as a dev-ticket question.

What remains is the family's shared judgment call, now sharpened by structure-specific
evidence. In favour of eventual inclusion: the packaging idiom is mathlib-approved (SNF
template), the ambient-basis-as-parameter delta is mathematically forced and
independently endorsed, the type is heavily consumed real API, and mathlib's HNF gap is
genuine and verified. Against shipping this exact declaration: (a) the square shape
should become rectangular before the structure fossilises; (b) the redundant `matrix`
field + `toMatrix_eq` is flagged by the design review as data mathlib would rather
project than store — but the project's constructor at Classification.lean:136–145
demonstrates the defeq-control benefit of storing it (a literal `σ.inclusionMatrix` in
the bundle), so this is maintainer taste, not a mechanical fix; (c) per the sibling
verdicts and the fresh review, the bundle's fate is coupled to the existence theorem,
whose only current instance is rank 2 ("a good pilot, not a good endpoint"). The
declaration is the right *kind* of object for mathlib — the questions are scope and
field-design, which the skill cannot self-resolve.

For BORDERLINE-needs-human:
  Numbered questions (≤5):
    1. **Shape (the blocking question, shared family-wide):** do you commit to the
       rectangular redesign before any mathlib PR — i.e. first generalise
       `Matrix.IsColumnHermiteNormalForm` to rectangular `Matrix (Fin n) (Fin m) ℤ`
       (or `{ι κ}` with an order-embedding pivot function, AFP-style), then restate this
       bundle as `{m n : ℕ} (bM : Basis (Fin n) ℤ M)` with `bN : Basis (Fin m) ℤ N`,
       keeping the full-rank square case as a specialisation à la
       `Submodule.smithNormalFormOfRankEq`? (yes/no; "yes" makes this decl a
       YES-but-generalise-first in spirit, executed as a dev ticket)
    2. **Matrix field:** keep `matrix : Matrix … ℤ` + `toMatrix_eq` as stored data (defeq
       control for literal-matrix constructors, cf. Classification.lean:136–145), or
       adopt the reviewer-recommended minimal bundle (`bN` + `isHNF` on
       `LinearMap.toMatrix bN bM N.subtype`, with `matrix` a projection def)? (short
       answer; affects every constructor and rewrite in 3 files)
    3. **Sequencing:** do you accept the review's landing order — predicate + matrix-level
       existence/uniqueness first, basis-level bundle only together with (at least
       API-ready-for) general-rank existence — meaning this structure ships in the second
       PR of the series, not the first? (yes/no)
    4. **Rank-n existence commitment:** is generalising `exists_hermiteNormalForm` from
       `Fin 2` to `Fin n` (induction on columns / AFP-style reduction) in scope for this
       project, or is the rank-2 pilot the project's endpoint (in which case the whole
       family stays project-local until someone does the rank-n work)? (yes/no/defer)
    5. **Index carrier:** confirm `Fin n` (not general ordered `ι`) as the intended
       mathlib carrier — the general-`ι` widening compiles (verified) but both the design
       review and the SNF precedent favour `Fin`; a "yes" closes the index axis
       permanently. (yes/no)
  Next action: user answers the questions; re-run `/mathlibable Module.Basis.HermiteNormalForm`
  to resolve the verdict (a yes on Q1+Q3+Q4 converts the family into a staged
  mathlib PR series: predicate → matrix theorems → rectangular bundle + existence).

---

## Next step

User answers the five numbered questions above (Q1 — rectangular redesign commitment —
is the one that unblocks the whole nine-declaration family; it is the same scope question
every sibling verdict surfaced, now backed by a failing-probe verification and an
explicit external design review). Until then the structure stays project-local; it is
correct, heavily used, mathlib-templated API whose only defects are scope-of-ambition,
not mathematics.
