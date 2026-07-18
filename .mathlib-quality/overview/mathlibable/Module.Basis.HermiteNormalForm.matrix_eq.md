# /mathlibable report — `Module.Basis.HermiteNormalForm.matrix_eq`

Assessed 2026-07-18 against mathlib pin 2026-05-28. Mode A. This is the eleventh verdict
of the HermiteNormalForm.lean family. Per protocol, the ten stored sibling reports in
this directory were read FIRST. The family's landscape facts — mathlib verifiably has no
Hermite normal form in any formulation (three independent five-method searches at this
pin); the HNF literature is settled (existence + uniqueness always proved as a pair,
rank-n/rectangular scope, Bézout-ready ring axis); and the family shares one blocking
scope question (rectangular/rank-n redesign, parent report Q1) — are established in
[SIB:Module.Basis.HermiteNormalForm], [SIB:Submodule.exists_hermiteNormalForm],
[SIB:Matrix.IsColumnHermiteNormalForm], [SIB:Module.Basis.HermiteNormalForm.bN_eq] and
are cited rather than re-searched. Everything decl-specific — the mechanical-widening
probe, the call-sites grep, the uniqueness-vs-existence generalisation asymmetry, the
matrix-level-extraction analysis, and a fresh literature + ChatGPT channel on the
uniqueness half specifically — was verified fresh this session.

Family verdict landscape (all ten stored): 8 × BORDERLINE-needs-human (predicate,
2×2-predicate lemma, matrix existence, bundle, basis existence, choice-def, cyclicity
criterion, `bN_eq`), 2 × NO-composable-from-mathlib (`rankTwoContent`,
`index_eq_natAbs_det`).

---

### Baseline (Phase 0)

- lake build:               ✓ clean ("Build completed successfully (3909 jobs)"; verified fresh this session; only informational `qexp` prints)
- decl `Module.Basis.HermiteNormalForm.matrix_eq`: ✓ resolved at `XYin/PhD/Cox/HermiteNormalForm.lean:278`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Hermite-normal-form API for full-rank integer sublattices (Cox Ch. 11), templated on `Module.Basis.SmithNormalForm` with the ambient basis as an explicit parameter.

---

### Statement (Phase 1)

`Module.Basis.HermiteNormalForm.matrix_eq` is a theorem stating the following:

In rank two, the Hermite-normal-form matrix of a fixed submodule relative to a fixed
ambient basis is unique: if h and h′ are two HNF data for the same finite-index
submodule N ≤ M relative to the same ambient basis bM (each bundling a basis of N, the
2×2 integer inclusion matrix, and the column-HNF property), then h.matrix = h′.matrix.
This is THE uniqueness theorem of the HNF development — the matrix-level face of the
classical statement "for every basis B of a lattice Λ and every finite-index sublattice
Λ′ there is a *unique* HNF matrix H with Λ′ = Λ·H" — i.e. the injectivity half of the
bijection {index-m sublattices} ↔ {HNF matrices of determinant m} (Cox Ch. 11; arXiv
2310.12519). The basis-level face is the sibling `bN_eq` (:338), a 7-line transport of
this theorem through `Basis.repr` injectivity.

Variables / typeclasses involved (Lean side):
- `M : Type*` `[AddCommGroup M]` — ambient ℤ-module
- `{bM : Basis (Fin 2) ℤ M}` — the fixed ambient basis (rank 2, pinned by the variable block at :262)
- `{N : Submodule ℤ M}` — the sublattice

Hypotheses (Lean side):
- `h h' : HermiteNormalForm bM N` — two HNF data for the same N over the same bM

Conclusion (math): the HNF inclusion matrix of a rank-two sublattice relative to a fixed
ambient basis is unique.

Conclusion (Lean): `h.matrix = h'.matrix`

Proof body (57 lines, :278–335), the classical transition-matrix argument at n = 2:
let U = `h.bN.toMatrix h'.bN` and V the reverse transition; the private
`matrix_mul_toMatrix_eq` (:264, a change-of-basis application of
`linearMap_toMatrix_mul_basis_toMatrix`) gives h.matrix·U = h′.matrix and
h′.matrix·V = h.matrix. Then, by entrywise chase (`congrFun` + `Matrix.mul_apply` +
`Fin.sum_univ_two`): triangularity + positive pivots force U 1 0 = V 1 0 = 0;
divisibility both ways + `Int.le_of_dvd` antisymmetry force equal diagonals and
U 1 1 = 1; and the reduced-remainder condition forces the off-diagonal entries equal via
the private `reduced_eq_of_eq_add_mul` (:269, uniqueness of the nonneg residue mod d).
Close with `ext i j; fin_cases i <;> fin_cases j`. Notably, after :281–282 the proof
never uses h, h′ except through the fields `.matrix` and `.isColumnHermiteNormalForm` —
the core is a bundle-free matrix fact (see Phase 4c Q8).

---

### Size classification (Phase 2a)

Verdict: BIG
Reason: it is a main result of the file — the uniqueness half of a normal form named
after a person (Hermite), and per the file's own docstring ("Hermite normal form is
canonical only after fixing the ambient basis") canonicity is the development's stated
point; the sibling report [SIB:bN_eq Phase 2a] independently lists `matrix_eq` among the
docstring's headline results. Every literature treatment of HNF proves existence and
uniqueness as a pair; this is the uniqueness member of that pair. (Literature width
EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

One-liner verdict: n/a — kind is theorem, not def. (Body is a 57-line tactic proof of
genuine content.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

The concept — uniqueness of the HNF matrix of a sublattice relative to a fixed ambient
basis — is row-by-row the concept covered by the parent's and `bN_eq`'s exhaustive
tables at this same pin ([SIB:Module.Basis.HermiteNormalForm rows 1–10],
[SIB:bN_eq rows 1–10]); those rows are cited rather than re-spent. The two genuinely
decl-specific literature questions — (i) what is the standard rank-n uniqueness
*argument* and does it match this proof; (ii) is the uniqueness half the mathematically
more valuable half, and does it generalise more easily than existence — were answered by
two FRESH channels this session (rows 1 and 4).

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form, FRESH) | Hermite normal form uniqueness proof "upper triangular" unimodular "identity matrix" lattice fixed basis | yes | rank-n uniqueness proof is the transition-matrix argument: if H, G both HNF with G = WH (W unimodular), triangularity forces W triangular, monic/positive pivots force diag W = 1, reduction condition forces W = I; "HNF is unique: two HNF matrices generating the same lattice are equal" | UCSD CSE 206A Lecture 4; Damer, "Computing the HNF: A Survey" (eprint 2024/2089); MathWorld HNF; Tourloupis thesis — **the file's rank-2 proof is verbatim the n = 2 instance of the standard argument** |
|  2 | WebSearch (general form)         | [SIB:parent row 2 / exists_hermiteNormalForm row 2] HNF uniqueness rectangular, PID/Bézout | yes | uniqueness holds for rectangular m×n over ℤ (canonical representative of one-sided unimodular class); over PID needs chosen associate + residue representatives | Storjohann thesis; arXiv 2502.10416 |
|  3 | WebSearch (aliases/formalisation) | [SIB:parent row 3 / bN_eq row 3] AFP "Hermite" (Divasón–Aransay) uniqueness | yes | **matrix-level uniqueness formalised in Isabelle AFP** (echelon form over Bézout domains, uniqueness under their convention); no Lean/Coq HNF uniqueness anywhere | every HNF formalisation treats existence + uniqueness as a pair — the precedent bar includes uniqueness |
|  4 | ChatGPT MCP (gpt-5.4, high, FRESH) | uniqueness-half-specific review: value vs existence; rank-n machinery asymmetry; matrix-level vs bundle-level statement; Subsingleton packaging; hypothesis form | yes | (i) "**uniqueness is the more conceptually valuable theorem**, existence the more operational … without uniqueness a bundled `HermiteNormalForm bM N` is just another choice object; with uniqueness it becomes a genuine normal form"; (ii) "**rank-n uniqueness generalises with much less new machinery than rank-n existence**" — no Euclidean recursion, no measure-decreasing reduction; "moderate theorem-engineering" vs "major development"; standard proof = triangular W, diag divisibility antisymmetry, descending column induction on the reduction condition (exactly this file's argument at n = 2); (iii) primary mathlib statement should be **matrix-level**: public form "H, H′ column-HNF with equal column lattices (`LinearMap.range (Matrix.toLin' H) = …`) → H = H′", helper form "H·U = H′ with U unimodular → H = H′"; bundle `matrix_eq` a corollary; **`Subsingleton (HermiteNormalForm bM N)` is the right final packaging**; (iv) pitfalls: no separate nonsingularity hypothesis needed (positive pivots already give det ≠ 0); rank-deficient rectangular uniqueness is true but delicate (pivots can skip); `Matrix.isUnit_iff_isUnit_det` and `Matrix.range_toLin'` are the key existing mathlib bridges | the decl-specific channel this report exists for |
|  5 | Local references                 | `.mathlib-quality/references/` | n/a | directory absent at this path (consistent with all ten sibling reports) | — |
|  6 | nLab                             | [SIB:parent row 6] Hermite normal form | yes | canonical representative per unimodular-equivalence class; each convention gives uniqueness | uniqueness IS the page's framing |
|  7 | nCatLab                          | n/a — not a categorical concept [SIB:parent row 7] | n/a | — | — |
|  8 | Stacks Project                   | n/a — not an algebraic-geometry concept [SIB:parent row 8] | n/a | — | — |
|  9 | MathOverflow / Math.SE           | [SIB:parent row 9] sublattice HNF uniqueness | yes | unique HNF basis/matrix for every sublattice of ℤⁿ | Straub notes, UCSD CSE 206A |
| 10 | recent arXiv (last 5 years)      | [SIB:parent row 10] | yes | arXiv 2310.12519: sublattice ↔ HNF-matrix bijection — **injectivity of that bijection IS `matrix_eq`** | contemporary form is rank-n/rectangular |

### Literature summary (Phase 3)

Concept identified as: uniqueness of the Hermite normal form (matrix-level face) — the
canonicity half of the HNF existence/uniqueness pair, and the property that
distinguishes HNF from Smith normal form (SNF representatives are not unique; HNF's
raison d'être is canonicity after fixing the ambient basis).
Sources agree on the standard form: yes — every HNF treatment (textbook, lecture notes,
survey, AFP formalisation) proves existence and uniqueness as a pair; uniqueness is
stated at rank n (indeed rectangular), matrix-level first.
Most general standard form: two m×n integer matrices in (column) HNF with equal column
lattices are equal; Bézout/PID versions under chosen representatives.
Generality dimensions where the literature varies:
  - rank: rank n / rectangular (standard) vs rank 2 (this decl) — strictly narrower
  - level: matrix-level (all sources and formalisations) vs bundle-level (this decl;
    no formalisation has a basis-level bundle, [SIB:parent])
  - decl-specific asymmetry (FRESH, row 4): the uniqueness argument generalises to
    rank n with materially LESS machinery than existence — moderate vs major
Disagreement with the literature: none on content; the rank-2 pin and the
bundle-entangled statement are both narrower than every source.

---

### Generality analysis — `Module.Basis.HermiteNormalForm.matrix_eq` (Phase 4)

Literature-standard form (from Phase 3): for any n (rectangular in full generality), two
column-HNF matrices presenting the same sublattice relative to the same ambient basis
are equal; stated matrix-level, with basis/bundle corollaries.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `bM : Basis (Fin 2) ℤ M` | rank 2 pinned (variable block :262) | rank n | yes in the literature, **NO mechanically — probe verified failing** | fresh `lean_run_code` probe: the widened statement's FIRST proof line already fails to elaborate — `h.isColumnHermiteNormalForm.belowDiagonal_eq_zero 1 0` errors with "failed to synthesize `OfNat (Fin n) 1`/`OfNat (Fin n) 0`" (the index literals do not exist at general `Fin n` without `NeZero`); a second probe variant shows `omega` cannot prove `(0 : Fin n) < 1` (false at n = 1) and `Fin.sum_univ_two` is inapplicable (unused-simp-arg). Every one of the ~15 entrywise steps is Fin-2-specific (`Fin.sum_univ_two` ×6, literal indices, closing `fin_cases`). The rank-n form needs the descending-column-induction proof — new work, verdict-gate false-positive class 5 |
| 2 | `h h' : HermiteNormalForm bM N` | statement quantifies over the project-local bundle | matrix-level statement (H, H′ column-HNF, equal column lattices → H = H′) | restatement, not a weakening | the mathlib-standard form is a *different declaration* (matrix-level lemma with the bundle version as corollary), not a hypothesis drop on this one; and it is still stated against `IsColumnHermiteNormalForm`, itself project-local and BORDERLINE [SIB:Matrix.IsColumnHermiteNormalForm] |
| 3 | ring ℤ | ℤ (inherited from predicate) | Bézout/PID + representatives | yes in the literature, NO mechanically | predicate-level redesign, inherited ([SIB:Matrix.IsColumnHermiteNormalForm]: ordered-ring widening rejected by the Q9 guard; sound route is residue parametrisation) |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (rank 2 vs rank n; bundle-level vs
matrix-level; ℤ vs Bézout) — with **zero mechanically-reachable weakenings, probe-verified
fresh**: the Fin-2 → Fin-n widening fails at elaboration on the first proof line (two
independent failure modes recorded above), the matrix-level form is a new declaration
rather than a weakening, and the ring axis is the family's predicate redesign. No
compiling weakening exists → `YES-but-generalise-first` is unavailable per the verdict
gate (false-positive class 5).
Number of weakening opportunities found: 0 mechanical; 2 real-but-redesign (rank-n,
matrix-level extraction) + 1 inherited (ring).
Cost of the real restatement — **the decl-specific finding**: MODERATE, not EXPENSIVE.
Unlike existence (rank-n graded High/major: a full column-reduction algorithm with no
mathlib support, [SIB:Submodule.exists_hermiteNormalForm 4a row 1]), rank-n uniqueness
is the classical finite argument (triangular transition matrix, diagonal divisibility
antisymmetry, descending induction per column on the reduction window) — fresh ChatGPT
channel: "moderate theorem-engineering" vs existence's "major development"; and mathlib
already has partial triangularity support (`Matrix.det_of_upperTriangular`,
`Matrix.blockTriangular_inv_of_blockTriangular` in `Mathlib/LinearAlgebra/Matrix/Block.lean`,
verified fresh at this pin — though stated with `[Invertible M]` over a comm-ring, so an
ℤ-unimodular adaptation is still needed). **Uniqueness is the cheaper half to bring to
literature scope.** (Cost noted for sequencing only, per skill policy.)

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|---|---|---|---|
| 1 | Typeclasses instead of bundled hypotheses? | no | hypotheses are two structure instances; that is the idiom | — |
| 2 | Filters/nets? | no | finite algebra, no topology | — |
| 3 | Universal property? | partially | the uniqueness pair (`matrix_eq`, `bN_eq`) repackages as `Subsingleton (HermiteNormalForm bM N)` — mathlib's canonical spelling of "the datum is unique" (shared finding with [SIB:bN_eq 4c Q3]; independently endorsed by the fresh ChatGPT channel: "a canonical normal-form bundle should usually be subsingleton") | `Subsingleton.elim` discharges every "two HNF data agree" obligation |
| 4 | Bundled substructure? | no | already about the bundle | — |
| 5 | Typeclass-hierarchy weakening? | no (not mechanically) | ring axis is the predicate redesign (4a row 3) | — |
| 6 | Higher-categorical? | no | elementary lattice theory [SIB:parent row 7] | — |
| 7 | Concrete index generalises? | yes in principle (Fin 2 → Fin n) | probe-verified NOT mechanical (4a row 1); a dev ticket — but the MODERATE one of the family (4b) | rank-n uniqueness is the literature form |
| 8 | Concrete-via-abstract (adversarial diagnostic run)? | **yes — fires** | diagnostic: after the two `have hmul`/`hmul'` lines (:281–282) the proof body never mentions `h`, `h'` except through the projections `.matrix` and `.isColumnHermiteNormalForm` — lines :283–335 are a pure matrix argument about two column-HNF matrices linked by transition factors U, V with H·U = H′, H′·V = H. The real content is the bundle-free matrix lemma `Matrix.IsColumnHermiteNormalForm.eq_of_mul_eq (hA : A.IsColumnHermiteNormalForm) (hA' : A'.IsColumnHermiteNormalForm) (hU : A * U = A') (hV : A' * V = A) : A = A'` (or, public form per ChatGPT: equal column ranges via `Matrix.range_toLin'`, with the two-sided-factor form as helper). The bundle `matrix_eq` becomes a ≤4-line corollary via `matrix_mul_toMatrix_eq` | the abstract matrix lemma is the AFP-precedented, mathlib-facing statement — reusable for any two HNF presentations (not just bundle instances), and it is the layer at which the rank-n generalisation should be done; `Matrix.isUnit_iff_isUnit_det` / `Matrix.range_toLin'` are the existing mathlib bridges |
| 9 | False-generalisation guard | applied — no false generalisation | the matrix-level extraction, the rank-n form, and the `Subsingleton` packaging all preserve the mathematical content exactly (same uniqueness fact, same objects); note the extraction's hypothesis must keep BOTH factor equations (or unimodularity) — a one-sided `A * U = A'` alone is false | safeguard recorded |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — three layered targets, all contingent on the family
shipping: (i) **matrix-level extraction** of the proof core (Q8; CHEAP–MODERATE at rank
2 — the argument at :283–335 transplants nearly verbatim); (ii) **rank-n statement** at
the matrix level (MODERATE — the decl-specific asymmetry finding); (iii)
**`Subsingleton (HermiteNormalForm bM N)`** as the bundle-level packaging (CHEAP given
(i) + `bN_eq`). Real improvement: (i) separates the reusable mathematical content from
the project-local bundle exactly as the AFP and every literature source state it;
(ii) is the literature scope; (iii) is mathlib's uniqueness idiom. None converts this
verdict to YES-but-generalise-first on its own: (i) is a restatement (new decl), not a
verified hypothesis weakening, and all three are gated on the BORDERLINE parent
predicate/bundle.

### Proof strategy — `matrix_eq` (Phase 4.6)

| # | Question | Applies? | Idiomatic alternative | Cost of switch |
|---|---|---|---|---|
| 1 | ε-δ vs filters | no — algebraic | — | — |
| 2 | Element-wise vs point-free | partially — the entrywise `congrFun`/`Fin.sum_univ_two` chase is acceptable and standard at 2×2 (fully general point-free machinery does not exist for this argument); the real strategic gap is layering, not pointfree-ness | extract the matrix-level core (4c Q8) so the bundle theorem is a corollary | CHEAP |
| 3 | Sequences vs nets | no | — | — |
| 4 | Construction vs universal property | no | — | — |
| 5 | Missing mathlib helpers | yes | (a) family-level: mathlib lacks the HNF predicate and all HNF API [SIB:parent 4.6 row 5]; (b) decl-specific: an ℤ-unimodular triangular toolkit — "triangular + IsUnit det + positive diagonal ⇒ diagonal = 1", building on the existing `BlockTriangular` det/inverse API (`Mathlib/LinearAlgebra/Matrix/Block.lean:324,406` — currently `[Invertible M]` over comm-rings) — would carry the rank-n uniqueness proof | file with the HNF PR series |

### Proof strategy verdict (Phase 4.6)

Current strategy: REFACTOR-RECOMMENDED (mild)
  - Proposed strategy: extract the bundle-free matrix-level core
    (`IsColumnHermiteNormalForm.eq_of_mul_eq`-style helper, per 4c Q8); keep the
    entrywise argument inside it; `matrix_eq` becomes a short corollary. The rank-2
    entry chase itself is idiomatic at 2×2 and needs no rewrite.
  - Cost: CHEAP
  - Missing mathlib API: the ℤ-unimodular triangular lemmas above (for the eventual
    rank-n version; not needed for the rank-2 refactor)
  - Would refactoring make the proof strictly cleaner? yes — it isolates the reusable
    content and is the layer every literature source and the AFP state uniqueness at.
(For a non-YES verdict this is recorded for the follow-up, per skill policy.)

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is theorem.

---

### Mathlib search-status: `Module.Basis.HermiteNormalForm.matrix_eq` (Phase 5)

[A] Lean-Finder    (via the family's three independent five-method runs at this pin) no HNF hits in any formulation [SIB:parent, Submodule.exists_hermiteNormalForm, Matrix.IsColumnHermiteNormalForm]
[B] Loogle         [SIB:parent B] `"Hermite"` — only Hermite polynomials + `NumberField.hermiteTheorem.*`; no normal form
[C] LeanSearch     FRESH this session: "two matrices in Hermite normal form generating the same lattice are equal uniqueness" → zero relevant hits (noise: `Matrix.unique` instance, `LatticeHom.noConfusion`, `Matrix.uniqueEquiv` — nothing HNF, nothing normal-form-uniqueness)
[D] Grep mathlib   FRESH this session: `Mathlib/LinearAlgebra/Matrix/Block.lean` full lemma inventory — the `BlockTriangular` API has det lemmas (:285,:324,:329) and inverse-triangularity (:353–:406) but **no uniqueness/canonical-form theorem of any kind**; `unimodular` over all of Mathlib → only `TotallyUnimodular` (combinatorial optimisation) and a Haar-measure file — no unimodular-equivalence normal-form API. Plus [SIB:bN_eq D, fresh same day]: `hermiteNormalForm|HermiteNormalForm` zero matches; SNF-uniqueness grep over `LinearAlgebra/FreeModule/PID.lean` zero matches — **mathlib has no "normal form is unique" lemma of ANY kind** (SNF is genuinely non-unique, so none can exist there)
[E] Name pattern   `matrix_eq` under a `HermiteNormalForm` namespace cannot exist in mathlib (zero `HermiteNormalForm` matches, [D])

Searched for both:
  - the user's current form (bundle-level rank-2 HNF-matrix uniqueness): absent —
    inexpressible in mathlib (bundle and predicate do not exist there)
  - the literature-standard form (matrix-level rank-n HNF uniqueness, equal-lattice or
    unimodular-factor hypothesis): absent — mathlib has no HNF and no
    canonical-form-uniqueness statement for any matrix normal form; the nearest
    partial artifacts (`BlockTriangular` inverse API, `FixedDetMatrices.reduce_mem_reps`
    [SIB:Matrix.exists_right_mul_…]) contain no uniqueness content

Concluded: "not in mathlib (family five-method searches + fresh LeanSearch + two fresh
decl-specific greps exhausted, both forms); mathlib has no analogue of any
normal-form-uniqueness theorem"

---

### Statement shape (Phase 5.5)

### Normal-form check

Equivalent formalisms:
1. current: `h.matrix = h'.matrix` (paired with sibling `bN_eq : h.bN = h'.bN`)
2. matrix-level pair (ChatGPT-recommended primary): public
   `A.IsColumnHermiteNormalForm → A'.IsColumnHermiteNormalForm →`
   `LinearMap.range (Matrix.toLin' A) = LinearMap.range (Matrix.toLin' A') → A = A'`
   + helper with two-sided factor hypotheses (`A * U = A'`, `A' * V = A`) — the form the
   current proof core (:283–335) already proves
3. `Subsingleton (HermiteNormalForm bM N)` — subsumes 1 and `bN_eq` (remaining fields
   are propositions), mathlib's canonical uniqueness idiom [shared with SIB:bN_eq 5.5]

Does mathlib already have a canonical form for this idea? No HNF form at all; for the
*idiom*, mathlib states matrix↔submodule facts through `Matrix.range_toLin'`-style
bridges and bundle-uniqueness through `Subsingleton`/`Unique` instances → the canonical
target is 2 (primary) + 3 (packaging), with 1 as the transitional corollary. RHS
convention: n/a (not an iff).

### Syntactic generality

Alternative restatements attempted: (1)/(2)/(3) above. Chosen for the project as it
stands: (1) — it is the form actually consumed (direct term-mode application at
Classification.lean:175 and rewrite in `bN_eq`), easiest to apply at both existing call
sites. Chosen for mathlib: (2)+(3). Justification: (2)'s equal-range hypothesis is
supplyable from `range_toLin_matrix_eq` (:236, already in-file); (1) requires
constructing bundle instances first, which non-bundle consumers cannot.

### Superfluous-argument audit

| # | Argument / typeclass | Essentially used? | Notes |
|---|---|---|---|
| 1 | `[AddCommGroup M]` | yes | needed for `Submodule ℤ M`, `Basis` |
| 2 | `bM : Basis (Fin 2) ℤ M` | yes | HNF canonicity is relative to bM — the theorem's content; rank-2 pin is the 4a row-1 axis, not a superfluous hypothesis |
| 3 | `h h' : HermiteNormalForm bM N` | yes | the objects compared; note h.bN, h′.bN are only used to build the transition factors — which is exactly why the matrix-level extraction (4c Q8) exists |

### Statement-shape verdict (Phase 5.5)

Normal form: REFACTOR candidate — matrix-level primary + `Subsingleton` packaging is the
target if the family ships (carried into Phase 7 questions).
Syntactic generality: OK for project use; RESTATE (matrix-level + Subsingleton) for
mathlib.
Superfluous arguments: NONE.
Overall: RESTATE-BEFORE-SHIP, contingent on the family's BORDERLINE questions —
consistent with a non-YES verdict.

---

### Call sites — `Module.Basis.HermiteNormalForm.matrix_eq` (Phase 6.0)

Internal use count: **2** (fresh grep, whole project, excluding `.lake`; excluding the
declaring line; the like-named but distinct `hermiteNormalForm_matrix_eq_inclusionMatrix`
and `range_toLin_matrix_eq` filtered out).
External-to-file callers: 1 distinct file.

| Caller file:line | Usage pattern (one-line excerpt) |
|---|---|
| XYin/PhD/Cox/HermiteNormalForm.lean:345 | `rw [h.repr_apply, h'.repr_apply, h.matrix_eq h']` — the closing rewrite of sibling `bN_eq` (all of `bN_eq`'s content transports through `matrix_eq`) |
| XYin/PhD/Cox/CyclicSublattice/Classification.lean:175 | `S.hermiteNormalForm.matrix_eq (σ.inclusionHermiteNormalForm L)` — **the key uniqueness step of the cyclic-sublattice classification**: identifies the canonical HNF of S with the explicitly-constructed parametrised HNF, powering `hermiteNormalForm_matrix_eq_inclusionMatrix` (:71) whose own fan-out is 4 further sites (:97, :176, :189, :345) |

Inline-derivation grep (equivalent re-derived without using `matrix_eq`?): (none) — no
site proves equality of two HNF matrices by hand; all uniqueness reasoning in the
project flows through this theorem.

Pattern read-off (6.0.1): K = 2 with one external caller that is the linchpin of the
classification file, plus the in-file sibling it powers, and no inline re-derivation →
real API, the file's uniqueness payoff actually consumed (contrast [SIB:bN_eq]: K = 0 —
of the uniqueness pair, `matrix_eq` is the load-bearing member). Phase 7 leaning: YES-*
family, blocked only by the family gate.

### Composition check (Phase 6)

Can `matrix_eq` be derived from mathlib in ≤3 chained calls?

Attempt 1: the statement quantifies over `HermiteNormalForm bM N`, which does not exist
in mathlib, nor does its field predicate `Matrix.IsColumnHermiteNormalForm` (Phase 5:
zero matches, three independent five-method runs + fresh probes). The statement is not
expressible in mathlib, so no composition can produce it.
  - Mathlib decls used: n/a
  - Result: fails — inexpressible; inherited from the parent's NOT-COMPOSABLE
    ([SIB:parent Phase 6], incl. the verified SNF-cannot-substitute argument)
Attempt 2: could the *content* (normal-form uniqueness) come from an SNF-side mathlib
uniqueness fact? No such fact exists — SNF representatives are genuinely non-unique
(fresh-verified grep [SIB:bN_eq D]: zero uniqueness lemmas in PID.lean), and uniqueness
is precisely what HNF adds over SNF. No mathlib building block contains any part of the
argument (the `BlockTriangular` API stops at det/inverse-triangularity, fresh grep [D]).

Conclusion: NOT-COMPOSABLE.

---

## Verdict: `Module.Basis.HermiteNormalForm.matrix_eq`

**Category:** BORDERLINE-needs-human (inherited: quantifies over the parent structure
`Module.Basis.HermiteNormalForm` → BORDERLINE; same routing as `bN_eq` and
`isColumnHermiteNormalForm_fin_two` — but see the rationale: this is the family member
with the strongest decl-specific case for eventual inclusion)

**Evidence:**
- Literature search (Phase 3): HNF uniqueness is a genuinely standard literature result
  — every treatment proves existence + uniqueness as a pair, and the file's 57-line
  rank-2 proof is verbatim the n = 2 instance of the classical transition-matrix
  argument (fresh WebSearch: UCSD CSE 206A, Damer survey, MathWorld). Fresh ChatGPT
  channel: uniqueness is "the more conceptually valuable theorem" — it is what makes
  the HNF bundle a normal form rather than a choice object, and what SNF cannot offer.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD (rank 2, bundle-level,
  ℤ) with **zero mechanical weakenings, probe-verified fresh** — the Fin-n widening
  fails at elaboration on the first proof line (`OfNat (Fin n) 1` unsynthesizable;
  `omega` counterexample at n = 1; `Fin.sum_univ_two` inapplicable) → verdict-gate
  false-positive class 5 excludes YES-but-generalise-first. Decl-specific asymmetry:
  the rank-n uniqueness redesign is MODERATE (classical finite argument, partial
  `BlockTriangular` support in mathlib) whereas rank-n existence is major — uniqueness
  is the cheaper half to bring to literature scope. Phase 4c Q8 fires: the proof core
  (:283–335) is bundle-free, and the matrix-level extraction is the mathlib-facing form.
- Mathlib search (Phase 5): not in mathlib in either form; mathlib has no HNF and no
  normal-form-uniqueness lemma of any kind (fresh LeanSearch + fresh `BlockTriangular`/
  `unimodular` greps + family five-method runs).
- Composition check (Phase 6): NOT-COMPOSABLE — statement inexpressible in mathlib;
  no building block contains any of the argument. Call sites: K = 2, including the
  classification's key uniqueness step (Classification.lean:175) — the load-bearing
  member of the uniqueness pair.

**Rationale:**

This theorem cannot receive a standalone YES: its statement quantifies over the
project-local bundle `HermiteNormalForm bM N` — a type mathlib cannot express (no HNF
predicate, no bundle; three independent five-method searches plus three fresh probes
this session) — so it ships if and only if the parent structure ships, and the parent's
fully-argued verdict is BORDERLINE on the family's shared scope questions (rectangular
shape before the structure fossilises, redundant `matrix` field, rank-n commitment, PR
sequencing). Both NO buckets fail on the evidence: mathlib has neither the result, nor
the vocabulary to state it, nor any analogue (there is no uniqueness lemma for ANY
matrix normal form in mathlib — SNF is non-unique by nature). YES-but-generalise-first
fails the verdict gate mechanically: the only literature-direction widenings are a
rank-n redesign (probe-verified non-compiling — the Fin-2 pin is baked into every
entrywise step) and a matrix-level restatement (a new declaration, not a hypothesis
drop), i.e. false-positive class 5, routed to the human as dev-ticket questions.

What is decl-specific — and strengthens the case for answering the family questions
"yes" — is that `matrix_eq` is the *mathematically valuable half* of the HNF pair, and
the *cheap half to generalise*. Uniqueness/canonicity is HNF's entire selling point over
mathlib's existing Smith normal form (the fresh design review is explicit: "without
uniqueness a bundled HermiteNormalForm is just another choice object; with uniqueness it
becomes a genuine normal form"), it is the injectivity half of the sublattice ↔
HNF-matrix bijection the development exists for, and unlike existence — whose rank-n
version needs a full column-reduction algorithm with no mathlib support (graded High in
[SIB:Submodule.exists_hermiteNormalForm]) — rank-n uniqueness is a moderate finite
argument (triangular transition matrix, divisibility antisymmetry on positive pivots,
descending induction per column) with partial mathlib support already present
(`Matrix.det_of_upperTriangular`, `Matrix.blockTriangular_inv_of_blockTriangular`).
Moreover the current proof already contains its own mathlib-facing refactor: after line
:282 it never touches the bundle except through `.matrix`/`.isColumnHermiteNormalForm`,
so the matrix-level lemma (equal-column-range public form + two-sided-factor helper, per
the AFP precedent and the design review) is a near-verbatim extraction, with `matrix_eq`
a ≤4-line corollary and `Subsingleton (HermiteNormalForm bM N)` the final packaging
(subsuming `bN_eq`). These riders answer the two decl-specific questions posed for this
assessment: yes, the uniqueness argument generalises more easily than existence; and
yes, it is the mathematically valuable half — which is an argument for sequencing
uniqueness EARLY in any HNF PR series (predicate + matrix-level uniqueness can land
before any existence theorem), not for shipping this bundle-level rank-2 form as-is.

For BORDERLINE-needs-human:
  Numbered questions (≤4 — Q1 defers to the parent's question set rather than re-asking):
    1. **Family gate (defer to parent):** the verdict resolves with the parent
       structure's five questions ([SIB:Module.Basis.HermiteNormalForm] Q1–Q5,
       especially Q1 rectangular redesign and Q4 rank-n commitment). Track this theorem
       as part of that same decision, with no separate action? (yes/no)
    2. **Matrix-level extraction (decl-specific, CHEAP, beneficial even project-locally):**
       extract the proof core (:283–335) as a matrix-level lemma
       (`IsColumnHermiteNormalForm.eq_of_mul_eq`-style helper + optionally the
       equal-column-range public form via `Matrix.range_toLin'`), making `matrix_eq` a
       short corollary? This is the layer at which the literature, the AFP, and the
       design review all state uniqueness, and the layer at which the rank-n
       generalisation should happen. (yes/no)
    3. **Uniqueness-first sequencing:** if the family ships, adopt the review's landing
       order with uniqueness EARLY — predicate + matrix-level uniqueness in the first
       PR (both independent of any existence theorem), existence and the bundle later?
       This inverts the naive existence-first instinct and plays to the asymmetry that
       uniqueness is the moderate half. (yes/no)
    4. **Packaging:** if the bundle ships, adopt
       `instance : Subsingleton (HermiteNormalForm bM N)` as the shipped form of the
       uniqueness pair, demoting `matrix_eq`/`bN_eq` to corollaries? (yes/no; shared
       with [SIB:bN_eq] Q2)
  Next action: user answers the parent report's five questions plus Q2–Q4 above. A yes
  on parent-Q1/Q4 plus Q2–Q3 here converts the uniqueness side into a concrete dev
  ticket: extract the matrix-level rank-2 lemma (cheap), then generalise IT to rank n
  (moderate — the descending-column induction), then `matrix_eq`/`bN_eq`/`Subsingleton`
  follow as corollaries.

---

## Next step

No standalone action. The theorem inherits the parent structure's
BORDERLINE-needs-human and ships if and only if the `HermiteNormalForm` bundle (and its
predicate) ship. Three decl-specific riders to carry into that resolution: (1) this is
the mathematically valuable half of the HNF pair — canonicity is the development's
selling point over mathlib's SNF, and mathlib has no uniqueness lemma for any normal
form; (2) the rank-n generalisation of uniqueness is MODERATE (vs existence's major) —
sequence uniqueness early in any PR series; (3) the proof already factors: extract the
bundle-free matrix-level core (:283–335) now — it is cheap, project-locally beneficial,
and is exactly the statement a mathlib PR would lead with.
