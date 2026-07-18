# /mathlibable report — `Matrix.exists_right_mul_isColumnHermiteNormalForm`

Assessed 2026-07-18 against mathlib pin 2026-05-28 (`2abc2425`). Mode A, full exhaustive
protocol. Landscape shared with the five stored sibling verdicts in this directory
(`Matrix.IsColumnHermiteNormalForm` → BORDERLINE, `Submodule.exists_hermiteNormalForm` →
BORDERLINE, `Submodule.hermiteNormalForm` → BORDERLINE, `…index_eq_natAbs_det` →
NO-composable, `…quotient_isAddCyclic_iff…` → BORDERLINE). Concept-level searches are
cited from those reports where they genuinely cover this theorem; everything specific to
this existence statement (matrix-side reduction theorems in mathlib, witness packaging,
call sites, the `FixedDetMatrices` connection) was verified fresh. **This assessment adds
one landscape fact none of the siblings caught:** mathlib's
`Mathlib.LinearAlgebra.Matrix.FixedDetMatrices` contains a 2×2 integer-matrix reduction
theorem (`reduce_mem_reps`) adjacent to this decl, invisible to the siblings'
"hermite/echelon" greps because it never uses those words.

---

### Baseline (Phase 0)

- lake build:               ✓ clean ("Build completed successfully (3909 jobs)"; only informational q-expansion output in qExpansion_tactic/Examples.lean)
- decl `Matrix.exists_right_mul_isColumnHermiteNormalForm`: ✓ resolved at `XYin/PhD/Cox/HermiteNormalForm.lean:194`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Hermite-normal-form API for full-rank integer submodules (Cox Ch. 11); bundled HNF structure in arbitrary finite rank, "the constructive existence theorem currently supplies the rank-two case used by Cox".

---

### Statement (Phase 1)

`Matrix.exists_right_mul_isColumnHermiteNormalForm` is a theorem stating the following:

Every nonsingular 2×2 integer matrix A can be brought to column Hermite normal form by a
unimodular change of columns: there exists B ∈ GL₂(ℤ) (spelled as an integer matrix with
`IsUnit B.det`, i.e. det B = ±1) such that A·B is upper triangular with strictly positive
diagonal pivots and top-right entry in [0, (A·B)₀₀). This is the matrix-side existence
half of the Hermite normal form theorem (Hermite 1851) in the rank-two case — the
Euclidean/Bézout column-reduction — used in Cox, *Primes of the Form x²+ny²*, Chapter 11
to normalise sublattice inclusion matrices.

Variables / typeclasses involved (Lean side):
- `A : Matrix (Fin 2) (Fin 2) ℤ` — the matrix to reduce

Hypotheses (Lean side):
- `hdet : A.det ≠ 0` — nonsingularity (necessary: the HNF shape forces det(A·B) = product of positive pivots > 0)

Conclusion (math): ∃ B unimodular with A·B in column HNF.

Conclusion (Lean): `∃ B : Matrix (Fin 2) (Fin 2) ℤ, IsUnit B.det ∧ (A * B).IsColumnHermiteNormalForm`

Proof route (Phase 1 read, verified in source): the public theorem is a thin wrapper
(lines 194–203) rewriting A as `!![A 0 0, A 0 1; A 1 0, A 1 1]` and delegating to the
private core `exists_hnf_transform` (lines 133–190), which computes with explicit
`!![a, b; c, d]` literals: g = gcd(c,d) via `Int.gcd_eq_gcd_ab` (Bézout coefficients
`c.gcdA d`, `c.gcdB d`), exact divisions `Int.ediv_mul_cancel`, a sign unit s from
`exists_unit_mul_pos_aux`, and one division-with-remainder (`Int.emod_nonneg`,
`Int.emod_lt_of_pos`, `Int.emod_add_mul_ediv`) to reduce the top-right entry; two
private `ring`-checked identities (`hnf_transform_det_aux`, `hnf_transform_mul_aux`)
certify det B = s and the product shape `!![pivot·s, r; 0, g]`; the shape is closed by
`isColumnHermiteNormalForm_fin_two`. The `Fin 2` restriction is essential to every step
of the core (literals, `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Fin.sum_univ_two`).

---

### Size classification (Phase 2a)

Verdict: BIG
Reason: it is the constructive existence theorem the module docstring names as the file's
supply line ("the constructive existence theorem currently supplies the rank-two case
used by Cox") and the matrix-side half of a theorem named after a person (Hermite normal
form, Hermite 1851); in the literature the matrix formulation is the *primary* form
(sibling `Submodule.exists_hermiteNormalForm.md` Phase 3 row 4). (Literature width
EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: n/a
One-liner verdict: n/a (kind is theorem, not def) — check skipped. (The public wrapper
is 8 lines but the content is the ~60-line private Euclidean core it fronts; genuine
content, not glue.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

The nine-channel concept-level protocol for **exactly this theorem's mathematics** — HNF
existence, with the matrix formulation explicitly identified as the primary literature
form — was run in full by `Submodule.exists_hermiteNormalForm.md` (rows 1–10, assessed
2026-07-18 at this pin) and, for the predicate/convention axes, by
`Matrix.IsColumnHermiteNormalForm.md` (rows 1–10, same date). Those searches genuinely
cover this decl: the sibling's ChatGPT row 4 states the primary literature form verbatim
("∀ A ∈ M_{m,n}(ℤ) ∃ V ∈ GL_n(ℤ), AV in column HNF; square nonsingular is a special
case") and its rows 1–3/10 establish the generality landscape (rectangular over ℤ;
Bézout-domain existence as the strongest formalised precedent, Isabelle AFP
Divasón–Aransay; Kannan–Bachem/Cohen algorithmic tradition). Incorporated by citation.
Decl-specific rows searched fresh:

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | (cited: sibling exists report rows 1, 9 — Micciancio, Shmonin, Straub: for any nonsingular/rectangular integer matrix there is a unimodular column transformation to HNF; unique) | yes | A = H·V resp. A·V = H with V unimodular, H triangular w/ positive pivots + reduced entries | The matrix theorem IS the textbook statement; basis form is the corollary |
|  2 | WebSearch (general form)         | (cited: sibling rows 2–3 — HNF over PID/Bézout; AFP formalises Bézout-domain echelon existence with parametrised associates/residues) | yes | rectangular m×n, any rank; ring-generalised via residue systems, not order | Generality target for any mathlib PR |
|  3 | WebSearch (aliases/formalisation) | (cited: sibling row 3 — Isabelle AFP "Hermite" entry: existence + uniqueness over Bézout domains; no Lean/Coq HNF found) | yes | formal-precedent bar: Bézout-domain generality, arbitrary size | No Lean formalisation of HNF exists anywhere public (consistent with Phase 5) |
|  4 | ChatGPT MCP (gpt-5.4, high) — FRESH, decl-specific | (i) is this theorem shortly derivable from mathlib's `FixedDetMatrices.reduce_mem_reps` (transpose/J-conjugation bridge)? (ii) right relationship of an HNF PR to `FixedDetMatrices`? (iii) witness packaging: `∃ B, IsUnit B.det` vs `GL (Fin 2) ℤ` vs SL₂? | yes | (i) **agrees NOT short**: "the obstruction is structural" — reps is a left-action SL₂ row form with no sign normalisation of the second pivot; no orbit-witness lemma exists in the file; the route is necessarily multi-step (reduce on the conjugate, transport reps across J, fix the negative pivot for det < 0, re-reduce) — "I do not think there is a hidden one-line route"; (ii) **develop HNF independently, add a bridging lemma later**: building HNF on FixedDetMatrices "would bake in the wrong asymmetries: SL instead of GL, left instead of right, and the wrong sign convention"; coexistence + bridge is "completely acceptable, and in my view preferable"; (iii) primary statement with a `Matrix.GeneralLinearGroup (Fin 2) ℤ` witness preferred, the `IsUnit B.det` matrix form "also perfectly idiomatic" and aligns with `Matrix.toLinearEquiv` / `GeneralLinearGroup.mk''` — recommend GL primary + IsUnit-det corollary (or vice versa); do NOT package as SL₂ ("For HNF over ℤ, GL₂(ℤ) is the natural group") | Confirms the fresh Phase 5/6 analysis below |
|  5 | Local references                 | `.mathlib-quality/references/` absent (n/a — recorded); substituted `.mathlib-quality/overview/analysis/step6-generalization.md` §A1 via siblings | yes | proof core is Bézout-generic (Bézout identity + exact division), reduction step ℤ-specific; mathlib-right form "n×n over ℤ first, Bézout follow-up", difficulty **High** (rank-n needs a column-reduction induction the file does not have) | The narrowness is a known, graded development gap |
|  6 | nLab                             | (cited: sibling row 6 — HNF page: canonical representative of one-sided unimodular equivalence; convention variants each yield uniqueness) | yes | existence+uniqueness under any fixed coherent convention | — |
|  7 | nCatLab (if categorical)         | n/a — not a categorical concept (matrix reduction theory; sibling row 7 verified the nLab page offers no categorical abstraction) | n/a | — | — |
|  8 | Stacks Project (if alg geom)     | n/a — not an algebraic-geometry concept (sibling row 8 verified: no HNF tag) | n/a | — | — |
|  9 | MathOverflow / Math.StackExchange| (cited: sibling row 9 — unique HNF basis per sublattice; index-m sublattices ↔ HNF matrices) | yes | the matrix existence theorem underlies the sublattice↔matrix bijection | — |
| 10 | recent arXiv (last 5 years)      | (cited: sibling row 10 — arXiv 2310.12519, 2405.19302, 2605.07784 Labahn–Storjohann) | yes | contemporary research states the matrix theorem rectangular over ℤ / ring-generalised | — |

### Literature summary (Phase 3)

Concept identified as: **Hermite normal form existence, matrix formulation** (Hermite
1851) — every integer matrix is one-sidedly unimodular-equivalent to a matrix in HNF;
the primary form in the literature, of which the sublattice-basis theorem is the
standard corollary.

Sources agree on the standard form: yes (up to the interchangeable convention package:
row vs column action, upper vs lower triangular, residue window — see the predicate
sibling's Phase 3 for the full convention analysis; the project's combination is
coherent, canonicity proved in-file via `matrix_eq`).

Most general standard form: for A ∈ M_{m,n}(ℤ): ∃ V ∈ GL_n(ℤ) with A·V in column HNF —
**rectangular, any rank**, uniqueness as companion; over Bézout domains existence holds
with residue-parametrised normalisation (AFP precedent). The square-nonsingular 2×2 case
is the user's specialisation.

Generality dimensions where the literature varies:
- rank/shape: 2×2 square nonsingular (user) → n×n nonsingular → m×n rectangular any-rank (standard)
- ring: ℤ (user; textbook standard) → Euclidean → Bézout (AFP precedent)
- group packaging: unimodular matrix (det = ±1) — GL_n(ℤ); SL₂ only under det > 0 (the project derives that variant downstream)

Disagreement with the literature: none on truth; the user's form is the rank-2, square,
ℤ specialisation of the standard rectangular theorem.

---

### Generality analysis — `Matrix.exists_right_mul_isColumnHermiteNormalForm` (Phase 4a)

Literature-standard form (from Phase 3): for any m×n integer matrix A, ∃ V unimodular
with A·V in (column) HNF; nonsingularity not required in the rectangular staircase form.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|--------------------------------|
| 1 | size `Fin 2` | 2×2 hard-coded | n×n (ultimately m×n) | NO (not mechanically) | the entire proof is the private core `exists_hnf_transform`, which computes with explicit `!![a, b; c, d]` literals, `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Fin.sum_univ_two` (verified by reading lines 103–190); a `Fin n` binder change has no proof — rank n needs a column-reduction induction absent from the file (step6 §A1: difficulty High). Verdict-gate false-positive class 5 |
| 2 | ring ℤ | ℤ | Bézout/Euclidean with residue system | NO (not mechanically) | proof uses `Int.gcd_eq_gcd_ab`, `Int.emod_*`, sign normalisation via ℤ's order; moreover the target predicate `IsColumnHermiteNormalForm` is ℤ-order-specific (`0 < pivot`, `Set.Ico`) — the sibling predicate report's Q9 guard rejects the ordered-ring widening as a false generalisation; the honest ring form is a statement-level redesign |
| 3 | `hdet : A.det ≠ 0` | nonsingular | rectangular form drops it (staircase, zero columns allowed) | NO for THIS predicate | essential: the conclusion forces det(A·B) = ∏ pivots > 0 and det(A·B) = det A · (±1), so det A ≠ 0 is *implied by* the conclusion — dropping it makes the statement false. The any-rank version requires the rectangular staircase predicate, i.e. the shape redesign of row 1 |
| 4 | witness `∃ B, IsUnit B.det` | matrix + unit-det side condition | V ∈ GL_n(ℤ) | no (equivalent packaging) | ChatGPT (fresh, row 4): GL-witness preferred as the primary PR spelling, `IsUnit B.det` "also perfectly idiomatic" and the right fit for the project's consumers (`Matrix.toLinearEquiv` at :456 consumes exactly `IsUnit B.det`); not SL₂ (needs det > 0, which the project handles as a derived variant at CoxMatrices/Basic.lean:889) |

### Generality verdict (Phase 4b)

Verified-weakening note: no proposed weakening is a compilable edit — row 1 and row 2
are statement-level re-developments (verified against the proof body: the 2×2 literals
and ℤ-order facts are load-bearing in every step of `exists_hnf_transform`), and row 3
is a *false* weakening (the hypothesis is implied by the conclusion, so no compile probe
is meaningful — the weakened statement is mathematically false for singular A). There is
no hypothesis to drop and compile-check; per the skill's routing this is
**false-positive class 5** ("real but not a single mechanical edit"), which excludes
`YES-but-generalise-first` and routes the narrowness question to BORDERLINE — exactly as
it did for the basis-side sibling, whose narrowness lives in *this* decl's core.

The current form is: STRICTLY NARROWER THAN STANDARD (2×2 vs n×n/rectangular; ℤ vs
Bézout), but the standard form is NOT mechanically reachable — it requires a genuine
n-column Euclidean induction (new mathematical development, graded High).

Number of weakening opportunities found: 0 mechanical; 2 real-but-expensive
re-developments (rank n over ℤ: High; Bézout: Medium–High, per step6 §A1); 1 cosmetic
equivalent repackaging (GL witness, CHEAP).

Cost of the true generalisation: EXPENSIVE. (Does not downgrade any verdict; it is the
scoping decision — Phase 7 questions, shared with the siblings.)

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|--------------------------------|
| 1 | typeclasses instead of bundled hypotheses | no | an existence theorem with one hypothesis; nothing to typeclass-ify | — |
| 2 | filters/nets | no | finite algebra; no topology | — |
| 3 | universal property instead of construction | no | HNF is a canonical representative; the characterisation is the uniqueness theorem (separate decl `matrix_eq`) | — |
| 4 | bundled substructure | no | matrix-side statement; the bundled form is the sibling `Module.Basis.HermiteNormalForm` | — |
| 5 | typeclass-hierarchy weakening | yes (in principle) | ℤ → Bézout/Euclidean — a redesign of predicate + proof, not a restatement (rejected as a mechanical move by 4a row 2) | F[x]-HNF, computational algebra |
| 6 | higher-categorical | no | matrix reduction theory | — |
| 7 | concrete index generalisation | **yes** | `theorem Matrix.exists_right_mul_isColumnHermiteNormalForm (A : Matrix (Fin n) (Fin n) ℤ) (hdet : A.det ≠ 0) : ∃ B, IsUnit B.det ∧ (A * B).IsColumnHermiteNormalForm` — the predicate already takes `{ι} [Preorder ι]`, so the *statement* generalises verbatim; only the proof is missing (the rank-n induction) | the mathlib-right form per every literature channel; sits beside `Submodule.smithNormalForm` in LinearAlgebra/FreeModule; supplies the basis corollary the sibling report specifies |
| 8 | concrete-via-abstract (proof-body diagnostic) | no — diagnostic run, does NOT fire | grep of the proof body: the `Fin 2`/literal content (`!![..]`, `det_fin_two_of`, `mul_fin_two`, `Fin.sum_univ_two`, entrywise `fin_cases`) is used essentially in every step after the first rewrite; there is no abstract property the proof secretly runs on — the proof IS the 2×2 instance of the missing general theorem (same conclusion as the basis-side sibling's Q8) | n/a |
| 9 | false-generalisation guard | no false generalisation on Q7 | the rank-n/rectangular target is the *same* theorem (HNF existence) at standard generality; (the ordered-ring widening of the predicate was already rejected by the sibling's Q9 and is not proposed here) | safe |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — but it coincides with the literature-standard
generalisation (Q7: rank-n statement, which generalises *verbatim* at the statement
level while the proof requires EXPENSIVE new development). It therefore feeds the
Phase 7 scoping question rather than a self-resolving `YES-but-generalise-first`.
Decl-specific modernisation beyond that is limited to the CHEAP GL-witness repackaging
(4a row 4; ChatGPT-recommended primary spelling for a PR) — a real ergonomic
improvement (intrinsically unimodular witness, matches the symmetry group) but not a
mathematical generalisation.

---

### Proof strategy — `Matrix.exists_right_mul_isColumnHermiteNormalForm` (Phase 4.6a)

| # | Question | Applies? | Idiomatic alternative | Cost of switch |
|---|----------|----------|------------------------|----------------|
| 1 | ε-δ vs filters | no — no topology | — | — |
| 2 | element-wise vs point-free algebra | no — entry-level Bézout computation is unavoidable in the 2×2 Euclidean core; the wrapper delegates cleanly | — | — |
| 3 | sequences vs nets | no | — | — |
| 4 | construction vs universal property | no — existence theorems are constructions | — | — |
| 5 | missing mathlib helpers | **yes** | (a) the n×n (ultimately m×n) matrix HNF theorem — the real gap this decl works around by hard-coding 2×2 (the shared upstream dev-ticket); (b) considered and REJECTED as a strategy: routing through mathlib's `FixedDetMatrices.reduce`/`induction_on` — ChatGPT (fresh): building HNF on it "would bake in the wrong asymmetries: SL instead of GL, left instead of right, and the wrong sign convention"; the direct Bézout construction is the right proof | (a) upstream ticket; (b) n/a |

### Proof strategy verdict (Phase 4.6b)

Current strategy: MATHLIB-IDIOMATIC — the direct 2×2 Bézout/Euclid construction is the
literature-standard proof of the rank-2 case and the right architecture (public wrapper +
private literal core + shape-intro lemma); the alternative strategy via mathlib's
`FixedDetMatrices` machinery was explicitly evaluated and rejected (wrong action side,
wrong group, wrong sign convention — Phase 5/6 and ChatGPT row 4). No refactor
recommended at rank 2; the strategic gap is the missing rank-n induction, recorded as
the shared upstream ticket.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is theorem.

---

### Mathlib search-status: `Matrix.exists_right_mul_isColumnHermiteNormalForm` (Phase 5)

[A] Lean-Finder    **fresh**: "bring an integer matrix to Hermite normal form / column echelon form by multiplying by an invertible integer matrix (Euclidean algorithm on columns, Bezout)" → **no HNF hits**; surfaced instead: `FixedDetMatrices.reduce/reduceStep/reduce_mem_reps/reduce_rec` (2×2 fixed-det reduction — analysed below) and `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal` (transvection diagonalisation — **field-only** `[Field 𝕜]`, no ℤ analogue)
[B] Loogle         **fresh**: `|- ∃ _, IsUnit (Matrix.det _) ∧ _` → **zero hits** (no theorem in mathlib concludes with a unit-det matrix witness); sibling: `"Hermite"` → only Hermite polynomials + `NumberField.hermiteTheorem.*`
[C] LeanSearch     **fresh**: "there exists a unimodular integer matrix U such that A * U is upper triangular with positive diagonal" → no reduction theorem; only `IsTotallyUnimodular` API (matroid-theoretic, unrelated) and `PosDef` conjugation lemmas
[D] Grep mathlib   **fresh at this pin**: `grep -rli "unimodular\|triangulariz\|echelon" Mathlib/` → `TotallyUnimodular.lean` (matroid theory), `Eigenspace/Triangularizable.lean` (field/eigenvalue theory), no echelon anywhere — no unimodular-reduction theorem; sibling greps: no "hermite normal", no `IsHermite`, `BlockTriangular` has no reduction/existence theorem; **fresh find**: `Mathlib/LinearAlgebra/Matrix/FixedDetMatrices.lean` (read in full at the pin) — `reps m = {A : Δm | A 1 0 = 0 ∧ 0 < A 0 0 ∧ 0 ≤ A 0 1 ∧ |A 0 1| < |A 1 1|}` (:69), `reduce : Δm → Δm` from the S/T generators (:99), `reduce_mem_reps (hm : m ≠ 0) : reduce A ∈ reps m` (:175), eliminator `induction_on` (:238) — a 2×2 integer reduction to near-HNF representatives under the **left SL₂(ℤ)** action, with **no sign normalisation of the second pivot** (for m < 0 the (1,1) entry is negative), the (0,1) entry reduced against the **column** pivot |A 1 1|, and **no orbit-witness lemma** (`∃ γ, reduce A = γ • A` is not exported; only the eliminator)
[E] Name pattern   `grep exists_right_mul_isColumnHermiteNormalForm` project + mathlib → project-only (declaring file + CoxMatrices/Basic.lean); no name-adjacent mathlib decl

Searched for both:
- the user's current form (2×2, right action, GL-witness, column HNF) — not in mathlib
- the literature-standard forms (n×n/rectangular HNF reduction; any one-sided unimodular
  triangularisation over ℤ; echelon existence over any ring) — none in mathlib; the ONLY
  overlapping content is `FixedDetMatrices.reduce_mem_reps`, which is rank-2-only,
  left-action, SL₂-only, differently normalised, and stated on the `FixedDetMatrix`
  subtype rather than matrices

Concluded: **"found a partial match (`FixedDetMatrices.reduce_mem_reps`); covers part of
what we want"** — a genuinely adjacent 2×2 reduction engine (built for the modular-forms
/ Hecke-operator development) that neither contains nor shortly yields this theorem
(Phase 6). The HNF statement itself is not in mathlib in any form (all 5 methods, both
forms; consistent with all five sibling verdicts, which this finding refines but does
not contradict — the siblings' claim "no HNF anywhere" remains true; what exists is an
unnamed near-HNF reduction in a different normalisation).

---

### Normal-form check — Phase 5.5a

Equivalent formalisms this statement could take:
1. `∃ B : Matrix (Fin 2) (Fin 2) ℤ, IsUnit B.det ∧ (A * B).IsColumnHermiteNormalForm` (current)
2. `∃ U : Matrix.GeneralLinearGroup (Fin 2) ℤ, (A * (U : Matrix _ _ ℤ)).IsColumnHermiteNormalForm` — GL-witness form
3. `∃ U : SL(2, ℤ), (A * U.1).IsColumnHermiteNormalForm` — SL₂ form, valid only for det A > 0 (the project derives exactly this at CoxMatrices/Basic.lean:889–903 as `exists_sl_right_mul_isColumnHermiteNormalForm_aux`)
4. reps-membership form on `FixedDetMatrix` (mathlib's `reduce_mem_reps` shape) — different convention, not equivalent without sign renormalisation

Does mathlib already have a canonical form for this idea? No canonical HNF form exists;
the adjacent `FixedDetMatrices.reps` uses a different (left/SL₂/unsigned-second-pivot)
convention, so the canonical-form choice is open — a genuine PR-design question (which
convention becomes mathlib's named HNF, and how `reps` bridges to it). ChatGPT (fresh):
GL-witness (form 2) as the primary spelling, form 1 as the corollary aligned with
`Matrix.toLinearEquiv`; never form 3 as primary. RHS convention: n/a (existence
statement).

### Syntactic generality — Phase 5.5b

Alternative restatements attempted:
- form 1 (current) — both consumers destructure `⟨B, hBunit, hH⟩` and feed either
  `Matrix.toLinearEquiv bN₀ B hBunit` (HermiteNormalForm.lean:456, consuming exactly
  `IsUnit B.det`) or build an SL₂ element from it (CoxMatrices/Basic.lean:897); easiest
  to apply at the project's call sites
- form 2 (GL witness) — better as the mathlib-primary statement; project-locally would
  force coercion unpacking at both sites
- hypothesis spelling `A.det ≠ 0` — matches mathlib's nonsingularity idiom for ℤ-matrices
  (`Matrix.toLinearEquiv` precondition); nothing to change

Chosen restatement: form 1 for the project; for a PR, form 2 primary with form 1 as the
one-line corollary (ChatGPT-recommended, cosmetic cost).
Justification: verified against both call sites — `IsUnit B.det` is consumed directly.

### Superfluous-argument audit — Phase 5.5c

| # | Argument / typeclass | Essentially used? | Notes |
|---|----------------------|-------------------|-------|
| 1 | `A : Matrix (Fin 2) (Fin 2) ℤ` | yes | the subject |
| 2 | `hdet : A.det ≠ 0` | yes | necessary, not just used: the conclusion implies det A ≠ 0 (det(A·B) = ∏ positive pivots ≠ 0 and det B a unit), so the hypothesis is the exact nonsingularity the statement needs |

None superfluous.

### Statement-shape verdict (Phase 5.5d)

Normal form: OK locally / OPEN for a PR (no mathlib HNF canonical form exists; the
convention-vs-`FixedDetMatrices.reps` relationship must be settled in the PR design)
Syntactic generality: OK locally; RESTATE for a PR (GL-witness primary + IsUnit-det
corollary)
Superfluous arguments: NONE
Overall: SHIP-AS-STATED locally; the PR-facing restatement (GL packaging, plus the
rank-n statement of 4c Q7) is named in the Phase 7 next-action list and subsumed by the
scoping questions.

---

### Call sites — `Matrix.exists_right_mul_isColumnHermiteNormalForm` (Phase 6.0)

Internal use count: **2** (excluding the declaring file); **3** total consumers
External-to-file callers: 1 distinct file

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| XYin/PhD/Cox/HermiteNormalForm.lean:455 (in-file) | `obtain ⟨B, hBunit, hAB⟩ := Matrix.exists_right_mul_isColumnHermiteNormalForm A hAdet` — the engine of `Submodule.exists_hermiteNormalForm` (basis transport via `Matrix.toLinearEquiv bN₀ B hBunit`) |
| XYin/PhD/Cox/CoxMatrices/Basic.lean:407 | `obtain ⟨B, hBunit, hH⟩ := Matrix.exists_right_mul_isColumnHermiteNormalForm (coxInput m γ) …` — Cox-matrix orbit reduction (`exists_coxMatrix_reduction`) |
| XYin/PhD/Cox/CoxMatrices/Basic.lean:893 | `obtain ⟨B, hBunit, hH⟩ := Matrix.exists_right_mul_isColumnHermiteNormalForm A hdet.ne'` — derives the SL₂ variant `exists_sl_right_mul_isColumnHermiteNormalForm_aux` (det > 0 ⇒ B ∈ SL₂) |

Inline-derivation grep (equivalent re-derived elsewhere without using the decl?):
(none) — `grep gcdA\|gcdB` over the project outside the declaring file: zero hits; no
other site performs Bézout column reduction; every HNF-producing step in the project
flows through this theorem.

Signal (per 6.0.1): K = 3 consumers across 2 files (basis existence, Cox-matrix
classification, SL₂ variant), no inline re-derivation → real, load-bearing API; this is
the supply line of the entire HNF + CoxMatrices development. Strong YES-leaning
composability signal — tempered, as with all siblings, by the shippability coupling.

### Composition check (Phase 6)

Can `Matrix.exists_right_mul_isColumnHermiteNormalForm` be derived from mathlib in ≤3
chained calls?

Attempt 1 (via `FixedDetMatrices.reduce_mem_reps` — the fresh partial match, analysed
in detail): conjugating by the antidiagonal J = `!![0,1;1,0]` converts the left-action
row form to a right-action column form (J·(γA)ᵀ·J = (JγᵀJ)·(JAᵀJ), and J·Mᵀ·J maps the
project's HNF shape `!![d,r;0,a]` to reps-shape `!![a,r;0,d]`). But three structural
gaps make this a real proof, not a composition: (a) no orbit-witness lemma exists —
`∃ γ : SL(2,ℤ), γ • A ∈ reps m` must itself be proved from the eliminator
`induction_on` (or by recursion along `reduce_rec`); (b) reps does not normalise the
second pivot's sign — for det A < 0 the representative has a negative (1,1) entry, and
fixing it by a right unit-diagonal multiplication un-reduces the off-diagonal entry,
requiring a re-reduction step with fresh `Set.Ico` bookkeeping; (c) reps is SL₂-only
while the target needs the GL witness precisely to absorb the sign. Independently
confirmed by ChatGPT MCP (fresh, high effort): "the obstruction is structural, not just
presentational … I do not think there is a hidden one-line route."
  - Mathlib decls used: `FixedDetMatrices.reduce`, `reduce_mem_reps`, `induction_on`
  - Result: **fails as a ≤3-call composition** (multi-step proof with nontrivial
    reasoning between steps — the "multiple haves" NO pattern of the heuristics table)

Attempt 2 (via transvection/elimination machinery):
`Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal` is **field-only**
(`[Field 𝕜]` — division by pivots is essential); mathlib has no Gaussian/Euclidean
elimination over ℤ, no echelon form over a ring (fresh grep [D]). SNF cannot substitute
(sibling report verified: SNF forgets the one-sided restriction).
  - Result: fails.

Conclusion: **NOT-COMPOSABLE** — but with the material refinement that mathlib now
contains an *adjacent* rank-2 reduction engine (`FixedDetMatrices`) that any HNF PR must
position itself against (ChatGPT: independent HNF development + a later bridging lemma
relating `reps` to rank-2 HNF up to transpose/J and sign normalisation is the preferred
design).

---

## Verdict: `Matrix.exists_right_mul_isColumnHermiteNormalForm`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the matrix formulation is the PRIMARY literature form of
  HNF existence ("∀ A ∈ M_{m,n}(ℤ) ∃ V ∈ GL_n(ℤ), AV in column HNF" — sibling ChatGPT
  channel, verbatim), standard at rectangular/rank-n scope over ℤ and at Bézout-domain
  scope in the strongest formalised precedent (Isabelle AFP); the sibling verdict
  "Fin 2 is a good pilot, not a good endpoint" applies to this decl most directly of
  all — it IS the 2×2 pilot.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD (2×2, ℤ), with zero
  mechanical weakenings — the `Fin 2` restriction is load-bearing in every line of the
  `!![..]`-literal core (verified by reading the proof body), `hdet` is implied by the
  conclusion hence essential, and the ring axis is a predicate-level redesign; verdict-
  gate false-positive class 5 excludes `YES-but-generalise-first`. Uniquely among the
  siblings, the *statement* generalises to `Fin n` verbatim (the predicate is already
  index-general) — only the proof is missing.
- Mathlib search (Phase 5): partial match only — **fresh finding**:
  `FixedDetMatrices.reduce_mem_reps` (LinearAlgebra/Matrix/FixedDetMatrices.lean:175,
  in the pin) is a 2×2 integer reduction to near-HNF representatives under the left
  SL₂-action, invisible to the siblings' keyword greps; it is differently normalised
  (no second-pivot sign, column-pivot reduction, SL₂-only, subtype carrier) and exports
  no orbit witness. No HNF statement exists in mathlib in any form.
- Composition check (Phase 6): NOT-COMPOSABLE — the `FixedDetMatrices` route requires a
  genuine multi-step proof (orbit-witness extraction + J-conjugation + sign
  renormalisation + re-reduction; ChatGPT concurs "no hidden one-line route"); the
  field-only transvection machinery does not apply over ℤ. K = 3 call sites across 2
  files, no inline re-derivation — the supply line of the whole development.

**Rationale:**

Both NO buckets fail on the evidence. Mathlib has no Hermite normal form in any
formulation, and the one genuinely adjacent result — `FixedDetMatrices.reduce_mem_reps`,
found fresh in this assessment — neither contains this theorem (different action side,
different group, different sign convention, no orbit witness) nor yields it in ≤3 calls
(the sign renormalisation for det < 0 alone re-does part of the reduction; confirmed
structurally and by an independent ChatGPT check). Both YES buckets also fail as
self-resolving verdicts. `YES-add-as-is` fails because every literature channel and the
formalisation precedent put the standard form at rank-n/rectangular — and this decl,
unlike its siblings, is exactly the place where that narrowness lives: it is the
2×2-literal Euclidean core the basis-side sibling report identified as the reason ITS
generalisation is blocked. It also cannot ship alone: its conclusion is stated against
the project-local `IsColumnHermiteNormalForm` predicate (itself BORDERLINE), so the unit
of contribution is the HNF development as a whole. `YES-but-generalise-first` fails the
verdict gate: the rank-n form is not a compile-verifiable weakening — the statement
generalises verbatim but the proof does not exist (a column-reduction induction graded
High), which is precisely false-positive class 5's mandated BORDERLINE routing. What
this assessment adds to the shared sibling landscape: (1) the `FixedDetMatrices` partial
match, which any future HNF PR must position itself against — the recommended design
(per ChatGPT, and consistent with the sibling reports' plan) is independent HNF
development plus a later bridging lemma to `reps`, NOT building HNF on the SL₂/left
machinery; (2) the witness-packaging decision (GL primary vs IsUnit-det) as a concrete
PR-design point; (3) the observation that this decl's statement is already rank-n-ready,
so under a yes-to-rank-n answer this theorem's *name and statement* survive unchanged
and only the proof is rewritten — the cleanest upgrade path in the whole file.

**Numbered questions (≤5):**

1. (= the siblings' shared decisive Q1) Are you committing to the mathlib-right HNF
   development — this theorem at `Fin n` (column-reduction induction, difficulty High)
   plus the basis corollary and the uniqueness pair, per the
   `Submodule.exists_hermiteNormalForm` report's plan? This decl is the exact place the
   work lands: the statement already generalises verbatim; only the induction is new.
   (yes/no)
2. If yes to 1: witness packaging for the public form — GL-witness primary
   (`∃ U : Matrix.GeneralLinearGroup (Fin n) ℤ, …`) with the `IsUnit B.det` matrix form
   as corollary (ChatGPT-recommended), or keep the matrix form primary (it is what
   `Matrix.toLinearEquiv` and both current call sites consume)? (GL-primary /
   matrix-primary)
3. If yes to 1: should the PR series include the bridging lemma relating rank-2 HNF to
   mathlib's existing `FixedDetMatrices.reps` (via transpose/J-conjugation + sign
   normalisation)? Reviewers who know the modular-forms development will ask how the two
   reduction theories relate; the recommended design is coexistence + bridge, not
   building one on the other. (yes/no)
4. If no to 1: keep this theorem project-local as-is (it is correct, idiomatic, and the
   load-bearing supplier of all HNF data), recording the rank-n matrix HNF theorem as
   the missing-mathlib-API note? (yes/no)

**Next action:** answer Q1 jointly with the five sibling reports — all six resolve as a
unit (this decl is the constructive engine; the predicate is the foundation; the basis
theorem, chooser, and corollaries ride on both). Yes to Q1 ⇒ fold Q2–Q3 into the
`/develop` ticket the sibling reports specify ("n×n integer column HNF: existence +
uniqueness + chooser, matrix + basis forms, SNF-template layout"), adding the
`FixedDetMatrices` bridge as an explicit ticket item. No ⇒ no further action; the decl
stays project-local.
