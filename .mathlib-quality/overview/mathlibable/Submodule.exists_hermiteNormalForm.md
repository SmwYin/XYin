# /mathlibable report — `Submodule.exists_hermiteNormalForm`

Assessed 2026-07-18 against mathlib pin 2026-05-28 (`2abc2425`). Mode A, full exhaustive protocol.

---

### Baseline (Phase 0)

- lake build:               ✓ clean ("Build completed successfully (3909 jobs)"; one unrelated style warning in QExpSimpConditionTests.lean)
- decl `Submodule.exists_hermiteNormalForm`: ✓ resolved at `XYin/PhD/Cox/HermiteNormalForm.lean:431`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Hermite-normal-form API for full-rank integer submodules (Cox Ch. 11); bundled HNF structure in arbitrary finite rank, "the constructive existence theorem currently supplies the rank-two case used by Cox".

---

### Statement (Phase 1)

`Submodule.exists_hermiteNormalForm` is a theorem stating the following:

Let M be a free ℤ-module with a fixed basis bM indexed by Fin 2 (so M ≅ ℤ²), and let
N ≤ M be a submodule of full rank (finrank ℤ N = 2, equivalently finite index). Then
there exists a Hermite-normal-form datum for N relative to bM: a basis bN of N together
with the 2×2 integer matrix A of the inclusion N ↪ M in the bases (bN, bM), such that A
is in column Hermite normal form — upper triangular, strictly positive diagonal pivots,
and each above-pivot entry the canonical nonnegative remainder in [0, pivot). This is the
sublattice-basis form of the classical Hermite normal form existence theorem (Hermite
1851), in the rank-two case needed for Cox, *Primes of the Form x²+ny²*, Chapter 11.

Variables / typeclasses involved (Lean side):
- `M : Type*` `[AddCommGroup M]` — the ambient abelian group (a rank-2 ℤ-lattice via `bM`)
- `bM : Basis (Fin 2) ℤ M` — the fixed ambient basis (explicit; HNF is basis-relative)
- `N : Submodule ℤ M` — the sublattice

Hypotheses (Lean side):
- `hN : Module.finrank ℤ N = 2` — full rank (⟺ finite index)

Conclusion (math): N admits a basis whose inclusion matrix w.r.t. bM is in column HNF.

Conclusion (Lean): `Nonempty (Module.Basis.HermiteNormalForm bM N)` — the bundle carries
`bN : Basis (Fin 2) ℤ N`, `matrix`, `toMatrix_eq : LinearMap.toMatrix bN bM N.subtype = matrix`,
`isColumnHermiteNormalForm : matrix.IsColumnHermiteNormalForm`.

Proof route (Phase 1 read): pick any basis `bN₀ := finBasis` of N; show the inclusion
matrix A has det ≠ 0 (via injectivity of `N.subtype ∘ bM.equiv bN₀`); apply the file's
matrix theorem `Matrix.exists_right_mul_isColumnHermiteNormalForm` (2×2 Euclidean/Bézout
column reduction: `Int.gcd_eq_gcd_ab`, `Int.ediv_mul_cancel`, `Int.emod_*`, sign
normalization); transport `bN₀` along `Matrix.toLinearEquiv bN₀ B hBunit` to get the HNF
basis. The Fin 2 restriction is inherited from `exists_hnf_transform` (lines 133–190),
which computes with explicit `!![a, b; c, d]` literals.

---

### Size classification (Phase 2a)

Verdict: BIG
Reason: it is a main result of the file (the module docstring names "the constructive
existence theorem" explicitly) and it is the existence half of a theorem named after a
person (Hermite normal form, Hermite 1851). (Literature width EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: n/a
One-liner verdict: n/a (kind is theorem, not def) — check skipped. (The 34-line proof is
genuine content, not glue.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | Hermite normal form existence theorem every full-rank sublattice basis upper triangular | yes | For sublattice Λ′ ≤ Λ and any basis B of Λ there is a **unique** basis B′ of Λ′ with B′ = BH, H in HNF (upper triangular, positive pivots, 0 ≤ h_ij < h_j) | Micciancio CSE 206A; Shmonin EPFL "Lattices and HNF" (Theorem 5); Nguyen MPRI notes; Straub "HNF: Introduction & Basic Applications" |
|  2 | WebSearch (general form)         | HNF existence uniqueness PID Bézout domain n×n matrix | yes | HNF exists and is unique for n×m matrices over ℤ (A = UH, U ∈ GL); over general PIDs canonical form needs chosen associate + residue representatives; over Bézout rings triangular reduction exists; "every rectangular matrix over R has SNF ⇒ R Bézout" | Grokipedia HNF; ACM SIGSAM "Hermite canonical form … over a PID"; Storjohann thesis; arXiv 2502.10416 "Arithmetic of matrices over rings" |
|  3 | WebSearch (aliases/formalisation) | "Hermite normal form" formalization Isabelle Coq Lean | yes | Isabelle AFP: Divasón–Aransay, "A Formal Proof of the Computation of Hermite Normal Form in a General Setting" — echelon/HNF **over Bézout domains**, with uniqueness; no Coq/Lean HNF found | Springer 10.1007/978-3-319-99957-9_3; AFP Hermite entry. Formal-library precedent sets the bar at Bézout-domain generality |
|  4 | ChatGPT MCP (gpt-5.4, high)      | standard form + generality (rectangular vs square, ℤ/PID/Bézout, row vs column), submodule-basis vs matrix formulation, historical evolution, mathlib-right statement, SNF-derivability | yes | (i) primary literature form: **matrix theorem, rectangular** — ∀ A ∈ M_{m,n}(ℤ) ∃ V ∈ GL_n(ℤ), AV in column HNF; square nonsingular is a special case; (ii) submodule-basis form is the exact basis-language translation and is the mathlib-shaped statement (matches the Smith API); (iii) Hermite 1851 → Newman → Kannan–Bachem 1979 / Domich–Kannan–Trotter 1987 / Cohen 1993 (algorithmic, rectangular, uniqueness conventions); (iv) **"A rank-2-only existence theorem is probably too narrow for core mathlib … `Fin 2` is a good pilot, not a good endpoint"**; if added seriously, want BOTH matrix and basis theorems + equivalence; (v) **HNF is NOT a 1–3-step corollary of SNF** — SNF changes both bases and forgets the ambient-basis information HNF retains | References: Hermite 1851 (Crelle 41), Newman *Integral Matrices*, Cohen §2.4, Kannan–Bachem, Labahn–Storjohann 2026 (arXiv 2605.07784) |
|  5 | Local references                 | `.mathlib-quality/references/` absent (n/a — recorded); substituted `.mathlib-quality/overview/analysis/step4-lattice.md` + `step6-generalization.md` §A1/A3 | yes | step6 §A1: proof core is Bézout-generic (Bézout identity + exact division), reduction step ℤ-specific (Euclidean residues + order); "what mathlib would want is n×n over ℤ first … Bézout-domain existence as follow-up"; difficulty **High** (n×n needs an induction the file does not have; 2×2→Bézout alone Medium). step4: mathlib has NO HNF (verified at pin) | Prior audits agree with channels 1–4 |
|  6 | nLab                             | "Hermite normal form" | yes | Dedicated page ncatlab.org/nlab/show/Hermite+normal+form: canonical representative of unimodular-equivalence classes of integer matrices; pivots positive, entries above pivot reduced (sign conventions vary, each gives uniqueness) | Confirms uniqueness-under-convention is part of the standard package |
|  7 | nCatLab (if categorical)         | n/a — not a categorical concept (integer-matrix / lattice reduction theory; the nLab page (#6) itself is elementary, no categorical abstraction offered) | n/a | — | — |
|  8 | Stacks Project (if alg geom)     | n/a — not an algebraic-geometry concept; Stacks' modules-over-PID material has no HNF tag (verified in the sibling assessments at this pin; SNF appears only incidentally) | n/a | — | — |
|  9 | MathOverflow / Math.StackExchange| every sublattice of ℤⁿ has basis in HNF, generality | yes | Standard: bijection between HNF matrices with det m and index-m sublattices; unique HNF basis for every full-rank (indeed every) sublattice | Straub notes, UCSD CSE 206A lecture 4, aggregated MSE-adjacent results |
| 10 | recent arXiv (last 5 years)      | (via #1–#3 result sets) | yes | arXiv 2310.12519 (2023) "Unimodular equivalence of sublattices" (HNF ↔ sublattice bijection); arXiv 2502.10416 (2025) "Arithmetic of matrices over rings"; arXiv 2605.07784 Labahn–Storjohann (2026) lattice-formulation restatement; arXiv 2405.19302 (HNF over Hermitian lattices) | Contemporary usage: rectangular over ℤ, ring-generalised in current research |

### Literature summary (Phase 3)

Concept identified as: **Hermite normal form existence** (Hermite 1851) — every integer
matrix is one-sidedly unimodular-equivalent to a unique HNF matrix; equivalently, every
sublattice of ℤⁿ has a unique basis in HNF relative to a fixed ambient basis.

Sources agree on the standard form: yes (up to interchangeable conventions: row vs column
HNF, sign/residue normalization).

Most general standard form: for A ∈ M_{m,n}(R): over ℤ (and any Euclidean domain with a
canonical residue system), ∃ unimodular V with AV in column HNF, **rectangular, any
rank**, and the HNF representative is **unique**; over any Bézout domain, triangular
(echelon) reduction exists (Isabelle AFP formalises exactly this level); over a general
PID the *canonical* form additionally requires chosen associate and residue
representatives. The sublattice-basis formulation (fixed ambient basis, basis of N with
triangular inclusion matrix) is the standard equivalent translation and is the form
matching mathlib's Smith API.

Generality dimensions where the literature varies:
- rank/shape: 2×2 square full-rank (user) → n×n nonsingular → **m×n rectangular, any rank** (standard)
- ring: ℤ (user, and most textbooks) → Euclidean domains → **Bézout domains** (existence; AFP precedent) → PID with residue system (canonical form)
- packaging: matrix theorem (primary in the literature) vs sublattice-basis theorem (standard corollary; the mathlib-shaped form)
- companion: uniqueness is part of the standard package (HNF's raison d'être vs SNF is canonicity after fixing the ambient basis); this file has rank-2 uniqueness (`matrix_eq`, `bN_eq`) as separate decls

Disagreement with the literature: none on truth; the user's form is the rank-2, square,
full-rank, ℤ specialisation of a theorem whose standard form is rectangular over ℤ (and
Bézout-generic in existing formalisation precedent).

---

### Generality analysis — `Submodule.exists_hermiteNormalForm` (Phase 4a)

Literature-standard form (from Phase 3): free ℤ-module M with basis indexed by arbitrary
finite ι; ANY submodule N (full rank not required in the rectangular form); ∃ basis of N
whose inclusion matrix is in (column) HNF; over ℤ at minimum, Bézout-domain existence in
the strongest formalised precedent.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|--------------------------------|
| 1 | index type `Fin 2` | rank 2 hard-coded | arbitrary finite rank n (rectangular m×n in full generality) | NO (not mechanically) | the proof calls `Matrix.exists_right_mul_isColumnHermiteNormalForm`, whose core `exists_hnf_transform` computes with explicit `!![a, b; c, d]` literals, `Matrix.det_fin_two_of`, `Fin.sum_univ_two`; a `Fin n` binder change has no proof — rank n needs a column-reduction induction the file does not contain (step6 §A1: difficulty High). Verdict-gate false-positive class 5: real generalisation, not a single mechanical edit |
| 2 | ring ℤ | ℤ | Bézout domain (existence) / Euclidean-with-residues (canonical form) | NO (not mechanically) | proof uses `Int.gcd_eq_gcd_ab`, `Int.emod_nonneg`, `Int.emod_lt_of_pos`, sign normalization via ℤ's linear order; the `IsColumnHermiteNormalForm` predicate itself (`0 < pivot`, `Set.Ico 0 pivot`) is ℤ-order-specific — the abstract version needs a residue-transversal/associate-choice reformulation of the *statement*, not a hypothesis drop |
| 3 | `hN : finrank ℤ N = 2` (full rank) | full-rank only | any submodule (rectangular HNF) | NO (not mechanically) | the bundle `HermiteNormalForm bM N` fixes a square `Fin n × Fin n` inclusion matrix and a `Fin n`-indexed basis of N; dropping full-rank forces rectangular matrices and a different structure — a restatement, not a weakening. (Spelling note: `finrank ℤ N = finrank ℤ M` would be the uniform mathlib spelling, cf. `Submodule.exists_smith_normal_form_of_rank_eq`; with `bM : Basis (Fin 2)` the two are equal, a cosmetic difference) |
| 4 | conclusion `Nonempty (HermiteNormalForm bM N)` | bundled structure | ∃ basis + triangularity | no (equivalent packaging) | mirrors mathlib's own `Module.Basis.SmithNormalForm` bundle + `Submodule.smithNormalForm : (n : ℕ) × Basis.SmithNormalForm N ι n` pattern; fine |

### Generality verdict (Phase 4b)

Verified-weakening note: no proposed weakening is a compilable edit — rows 1–3 are all
statement-level re-developments (`Fin 2` is baked into the `!![..]`-literal computation
`exists_hnf_transform`; the ℤ-order is baked into the `IsColumnHermiteNormalForm`
predicate; full-rank is baked into the square bundle). There is no hypothesis to drop and
compile-check; per the skill's routing this is **false-positive class 5** ("real but not
a single mechanical edit"), which excludes `YES-but-generalise-first` and routes the
narrowness question to BORDERLINE.

The current form is: STRICTLY NARROWER THAN STANDARD (rank 2 vs rank n / rectangular;
ℤ vs Bézout), but the standard form is NOT mechanically reachable — it requires a genuine
n-column reduction induction (and, for full literature generality, a Bézout-abstracted
predicate), i.e. new mathematical development, not a signature edit.

Number of weakening opportunities found: 0 mechanical; 2 real-but-expensive
re-developments (rank n over ℤ: High; Bézout existence: Medium–High, per step6 §A1).

Cost of the true generalisation: EXPENSIVE. (Does not downgrade any verdict; it is a
scoping decision — Phase 7 questions.)

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|--------------------------------|
| 1 | typeclasses instead of bundled hypotheses | no | the HNF datum is data (chosen basis + matrix), correctly a structure; mirrors mathlib's `Module.Basis.SmithNormalForm` bundle | — |
| 2 | filters/nets instead of sequences | no | finite algebra; no topology | — |
| 3 | universal property instead of construction | no | HNF is a normal form/canonical representative, not a universal object | — |
| 4 | bundled substructure instead of set-with-predicate | no | already `Submodule` | — |
| 5 | typeclass-hierarchy weakening | **yes** | ℤ → `EuclideanDomain` + residue conventions, or Bézout-domain existence form (AFP precedent); requires re-designing `IsColumnHermiteNormalForm` around a residue/associate choice rather than `Set.Ico 0 pivot` | would serve F[x]-HNF (Popov-form adjacent), general computational-algebra users |
| 6 | higher-categorical generalisation | no | none; this is matrix reduction theory | — |
| 7 | concrete index generalisation (`Fin 2` → `Fin n` / rectangular) | **yes** | `theorem Matrix.exists_right_mul_isColumnHermiteNormalForm (A : Matrix (Fin n) (Fin n) ℤ) (hdet : A.det ≠ 0) : ∃ B, IsUnit B.det ∧ (A * B).IsColumnHermiteNormalForm` (the predicate already takes `{ι} [Preorder ι]` — good) + the basis corollary for `Basis (Fin n) ℤ M`; ultimately rectangular m×n | the mathlib-right form per the literature AND per ChatGPT MCP ("Fin 2 is a good pilot, not a good endpoint"); would sit beside `Submodule.smithNormalForm` in LinearAlgebra/FreeModule |
| 8 | concrete-via-abstract (proof-body diagnostic) | no — diagnostic run and does NOT fire | grep of the proof body for `Fin 2`-specific content: the rank-2 restriction is used essentially throughout (`finBasis` cast via `hN ▸`, the 2×2 matrix theorem); there is no abstract property the proof secretly runs on — the proof IS the 2×2 instance of the missing general theorem | n/a |
| 9 | false-generalisation guard | no false generalisation | the rank-n / rectangular / Bézout targets from Q5/Q7 are the *same* mathematical theorem (HNF existence) at standard generality, not symbol-sharing different objects; (contrast: no analogue of the rank-n content trap from the sibling assessment arises here — HNF existence generalises truthfully to all n) | safe |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — but it coincides with the literature-standard
generalisation (Q7: rank-n/rectangular matrix theorem + basis corollary pair, per the
mathlib SNF template; Q5: Bézout/Euclidean abstraction as follow-up). It is EXPENSIVE
re-development, not a restatement of this decl — so it feeds the Phase 7 scoping
question rather than a self-resolving `YES-but-generalise-first`.
- Mathlib downstream: pairs with `Submodule.smithNormalForm*` (same file
  LinearAlgebra/FreeModule/PID.lean); gives lattice-enumeration API (index-m sublattices
  ↔ HNF matrices, cf. arXiv 2310.12519) that SNF cannot express since SNF forgets the
  ambient basis; supplies the canonical-representative story (uniqueness) mathlib's SNF
  lacks by design.
- Real mathematical improvement: yes — the ambient-basis-relative canonical form is
  genuinely new content relative to SNF (confirmed independent, Phase 6).

---

### Proof strategy — `Submodule.exists_hermiteNormalForm` (Phase 4.6a)

| # | Question | Applies? | Idiomatic alternative | Cost of switch |
|---|----------|----------|------------------------|----------------|
| 1 | ε-δ vs filters | no — no topology | — | — |
| 2 | element-wise vs point-free algebra | no — the proof works through `LinearMap.toMatrix`, `Basis.equiv`, `Matrix.toLinearEquiv`, i.e. the bundled API, not entries (entry-level work is confined to the 2×2 matrix lemma where it is unavoidable) | — | — |
| 3 | sequences vs nets | no | — | — |
| 4 | construction vs universal property | no | — | — |
| 5 | missing mathlib helpers | **yes** | (a) the n×n (ultimately m×n) matrix HNF theorem itself — the real gap this decl works around by hard-coding 2×2; (b) minor: `LinearMap.toMatrix_eq_basisToMatrix` (mathlib HEAD, postdates pin) would shave the `hmatrix`-style bridges | (a) is the upstream dev-ticket; (b) resolves at the next mathlib bump |

### Proof strategy verdict (Phase 4.6b)

Current strategy: MATHLIB-IDIOMATIC — the architecture (matrix reduction theorem +
basis-transport corollary via `Matrix.toLinearEquiv`) is exactly how mathlib would
structure it, and mirrors the SNF development's matrix/basis split. No refactor
recommended at rank 2; the strategic gap is the missing rank-n induction, recorded as
the upstream ticket, not a rewrite of this proof.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is theorem.

---

### Mathlib search-status: `Submodule.exists_hermiteNormalForm` (Phase 5)

[A] Lean-Finder    "existence of a triangular (Hermite normal form) basis for a finite-index sublattice … fixed ambient basis" → **no HNF hits**; nearest: `IsZLattice.basis`, `Submodule.smithNormalFormBotBasis/TopBasis/Coeffs`, `Submodule.exists_smith_normal_form_of_rank_eq/of_le` — all SNF-side (ambient basis changed, diagonal form), none triangular-relative-to-fixed-basis
[B] Loogle         `"Hermite"` → only `NumberField.hermiteTheorem.*` (Hermite's discriminant-finiteness theorem — unrelated) and Hermite polynomials; no HNF
[C] LeanSearch     "every full rank submodule of a free integer module has a basis whose inclusion matrix is upper triangular Hermite normal form" → only the SNF family (`Submodule.smithNormalForm*`, `Module.Basis.SmithNormalForm`); no HNF
[D] Grep mathlib   `-i hermite` over all of Mathlib → exactly 3 files: `RingTheory/Polynomial/Hermite/{Basic,Gaussian}.lean` (Hermite polynomials), `NumberTheory/NumberField/Discriminant/Basic.lean` (Hermite/Hermite–Minkowski discriminant theorems) — **no Hermite normal form anywhere**; grep for triangular-basis statements in `LinearAlgebra` (`exists.*Basis.*Triangular`, `BlockTriangular.*Basis`) → zero (the `BlockTriangular` API has no reduction/existence theorem)
[E] Name pattern   `lean_local_search "hermiteNormalForm"` → project-only (`Submodule.hermiteNormalForm`, `PeriodPair.CyclicSublattice.hermiteNormalForm`, `…_matrix_eq_inclusionMatrix`)

Searched for both:
- the user's current form (rank-2 sublattice-basis HNF existence) — not in mathlib
- the literature-standard forms (n×m matrix HNF under one-sided unimodular equivalence;
  rank-n sublattice HNF basis; Bézout-domain triangular reduction) — none in mathlib;
  the closest analogue is the SNF family (`Submodule.exists_smith_normal_form_of_rank_eq`
  etc.), which is a *different* normal form (two-sided, ambient basis not fixed)

Concluded: **"not in mathlib (all 5 methods exhausted, plus the literature-standard
forms)"** — mathlib has NO Hermite normal form in any formulation; the building blocks
present (SNF, `BlockTriangular` predicate API, `Matrix.toLinearEquiv`) do not contain the
reduction content (see Phase 6).

---

### Normal-form check — Phase 5.5a

Equivalent formalisms this statement could take:
1. `Nonempty (Module.Basis.HermiteNormalForm bM N)` — bundled-structure form (current)
2. `∃ (bN : Basis (Fin 2) ℤ N), (LinearMap.toMatrix bN bM N.subtype).IsColumnHermiteNormalForm` — unbundled ∃-form (mathlib's `exists_smith_normal_form_of_rank_eq` style)
3. matrix-side only: `∃ B, IsUnit B.det ∧ (A * B).IsColumnHermiteNormalForm` — already present as the file's `Matrix.exists_right_mul_isColumnHermiteNormalForm`

Does mathlib already have a canonical form for this idea? No (no HNF at all). The
proposed canonical pair, following the SNF template in the same would-be file, is
(matrix theorem, basis theorem) with the bundle for downstream API — which is exactly
the file's architecture. RHS convention: n/a (existence statement, no iff).

### Syntactic generality — Phase 5.5b

Alternative restatements attempted:
- `Nonempty (bundle)` + `Classical.choice` def (current) — matches how the project consumes it (a single canonical `hermiteNormalForm` def, justified by the file's uniqueness theorems `matrix_eq`/`bN_eq`)
- unbundled `∃ bN, …` + `.choose` defs — mathlib SNF's spelling; equivalent, marginally more idiomatic for mathlib
- `hN : finrank ℤ N = 2` vs `finrank ℤ N = finrank ℤ M` — the latter is the uniform mathlib spelling (cf. `smithNormalFormBotBasis`)

Chosen restatement: current form is right for the project; for a mathlib PR, restate the
hypothesis as `finrank ℤ N = finrank ℤ M` and consider the ∃-form alongside the bundle.
Justification: the sole consumer is the `Classical.choice` packaging; the bundle is what
every downstream site uses.

### Superfluous-argument audit — Phase 5.5c

| # | Argument / typeclass | Essentially used? | Notes |
|---|----------------------|-------------------|-------|
| 1 | `[AddCommGroup M]` | yes | needed for `Submodule ℤ M` |
| 2 | `bM : Basis (Fin 2) ℤ M` | yes | HNF is relative to the fixed ambient basis — the point of the theorem |
| 3 | `hN : finrank ℤ N = 2` | yes | supplies the `Fin 2`-indexed basis of N (`finBasis` cast) and det ≠ 0; without full rank the square bundle is unpopulatable |

None superfluous.

### Statement-shape verdict (Phase 5.5d)

Normal form: OK (no mathlib canonical form exists to align with; the file's
matrix/basis/bundle triple IS the proposed canonical architecture, mirroring SNF)
Syntactic generality: OK locally; RESTATE for a PR (hypothesis spelling
`finrank N = finrank M`; consider ∃-form)
Superfluous arguments: NONE
Overall: SHIP-AS-STATED locally; the PR-facing restatement is subsumed by the
generalisation scoping question (Phase 7).

---

### Call sites — `Submodule.exists_hermiteNormalForm` (Phase 6.0)

Internal use count: **1** direct (excluding the declaring file: 0; within the project:
the `Classical.choice` packaging def in the same file)
External-to-file callers: 0 direct — but the packaging def fans out massively.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| XYin/PhD/Cox/HermiteNormalForm.lean:470 | `Classical.choice (N.exists_hermiteNormalForm bM hN)` — the canonical-HNF def `Submodule.hermiteNormalForm` |
| (transitive) XYin/PhD/Cox/CyclicSublattice.lean:55–57 | `S.carrier.hermiteNormalForm L.latticeBasis S.carrier_finrank` — 25+ downstream uses across CyclicSublattice.lean and CyclicSublattice/Classification.lean (`.matrix`, `.bN`, `.isColumnHermiteNormalForm.diagonal_pos`, `index_eq_natAbs_det`, cyclicity criterion, …) |

Inline-derivation grep (equivalent re-derived elsewhere without using the decl?): (none)
— no other site constructs an HNF basis; all HNF data in the project flows through this
existence theorem via the choice def.

Signal (per 6.0.1): K = 1 direct is the *expected* pattern for an existence theorem
consumed via its canonical-choice packaging — identical to mathlib's own
`Submodule.exists_smith_normal_form_of_rank_eq`, whose only consumers are the `.choose`
projections `smithNormalFormTopBasis/BotBasis/Coeffs`. The transitive fan-out (25+ sites,
3 files) shows this is the load-bearing supplier of the entire CyclicSublattice
development, not a wrapper or dead code. YES-leaning composability signal.

### Composition check (Phase 6)

Can `Submodule.exists_hermiteNormalForm` be derived from mathlib in ≤3 chained calls?

Attempt 1 (via Smith normal form): `Submodule.smithNormalFormBotBasis bM hN` gives a
basis bN of N with `bN i = c i • (smithNormalFormTopBasis bM hN) i` — diagonal inclusion
matrix, but **relative to the NEW ambient basis** `smithNormalFormTopBasis`, not the
fixed `bM`. The inclusion matrix w.r.t. `bM` is `(bM.toMatrix bS) * diagonal c` for an
arbitrary unimodular change-of-basis factor — not triangular, and no mathlib lemma
triangularises it (grep [D]: `BlockTriangular` has no reduction theorem).
  - Mathlib decls used: `Submodule.smithNormalFormBotBasis/TopBasis/Coeffs`
  - Result: **fails** — SNF structurally forgets the ambient basis that HNF must retain
    (independently confirmed by ChatGPT MCP: "HNF should be treated as genuinely new
    content, not a short corollary of the existing Smith API")

Attempt 2 (via `Submodule.basisOfPid` + triangularisation): `basisOfPid` yields some
basis of N; making its `bM`-inclusion matrix triangular is precisely the missing
column-reduction theorem — mathlib has no Gaussian/Euclidean elimination over ℤ, no LU
over rings, no echelon form (only field-side `Matrix.LDL`/rref-adjacent tools).
  - Result: **fails** — the reduction step IS the theorem's content.

Conclusion: **NOT-COMPOSABLE**.

---

## Verdict: `Submodule.exists_hermiteNormalForm`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): standard form identified — HNF existence for rectangular
  integer matrices / arbitrary-rank sublattices, uniqueness as companion; Bézout-domain
  existence is the strongest formalised precedent (Isabelle AFP); ChatGPT MCP verbatim:
  "a rank-2-only existence theorem is probably too narrow for core mathlib … a good
  pilot, not a good endpoint".
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD along rank (2 vs n /
  rectangular) and ring (ℤ vs Bézout), but NOT mechanically reachable — the `Fin 2`
  restriction is baked into the `!![..]`-literal core `exists_hnf_transform`; verdict-gate
  false-positive class 5 excludes `YES-but-generalise-first`.
- Mathlib search (Phase 5): NO Hermite normal form anywhere in mathlib, in any
  formulation (all 5 methods, both the user's and literature-standard forms; only Hermite
  polynomials and Hermite's discriminant theorem exist under the name).
- Composition check (Phase 6): NOT-COMPOSABLE — SNF cannot substitute (it forgets the
  fixed ambient basis; confirmed by two independent channels); K = 1 direct call site is
  the canonical existence-theorem-consumed-via-choice pattern with 25+ transitive users.

**Rationale:**

The mathematical content is a genuine, verified mathlib gap: mathlib has no Hermite
normal form in any form, HNF is not derivable from the existing Smith normal form API
(SNF changes both bases and forgets exactly the ambient-basis-relative information HNF
exists to retain), and the file's architecture (matrix reduction theorem + basis-transport
corollary + bundled `HermiteNormalForm` structure) mirrors mathlib's own SNF template, so
both NO buckets are ruled out on the evidence. But the skill cannot self-resolve a YES
either. `YES-add-as-is` fails because the decl is not at the literature-standard
generality (rank 2 hard-coded, square, ℤ-only) and every literature channel — including
the formalisation precedent (AFP: Bézout domains, general size) and the ChatGPT MCP
second opinion — agrees mathlib reviewers would demand at least rank-n over ℤ, with the
matrix and basis statements as a pair. `YES-but-generalise-first` fails the verdict gate:
the generalisation is not a mechanical weakening that can be compile-verified — the rank-2
restriction lives in the 2×2-literal Euclidean core, so reaching rank n means writing a
column-reduction induction that does not exist in the file (step6 §A1 grades it High),
and the Bézout form additionally means re-designing the `IsColumnHermiteNormalForm`
predicate around residue choices. That is new mathematical development whose scope only
the user can commit to — exactly false-positive class 5's mandated BORDERLINE routing,
and consistent with the sibling HNF-file verdicts already on record (the quotient-
cyclicity criterion: BORDERLINE for the same structural reason; `index_eq_natAbs_det`:
NO-composable). Additionally, this decl cannot ship alone under any answer: it is stated
against the project-local `Module.Basis.HermiteNormalForm` bundle and
`Matrix.IsColumnHermiteNormalForm` predicate, so the unit of contribution is the
HNF development as a whole, not this theorem.

**Numbered questions (≤5):**

1. Scope commitment: are you willing to develop the mathlib-right existence theorem —
   `Matrix.exists_right_mul_isColumnHermiteNormalForm` for n×n nonsingular integer
   matrices (column-reduction induction; the predicate already takes `{ι} [Preorder ι]`)
   plus the `Basis ι ℤ M` sublattice corollary, with the current rank-2 results becoming
   instances? (This is the "n×n over ℤ first" plan step6 §A1 recommends; difficulty
   High.) (yes/no)
2. If yes to 1: should the uniqueness pair (`matrix_eq` / `bN_eq`, currently rank-2) be
   generalised and shipped in the same PR series? Uniqueness is HNF's selling point over
   SNF (canonical representative), and reviewers will likely expect it; the rank-n
   uniqueness induction is also graded High. (yes/no)
3. Ring generality: target ℤ only (mathlib-pragmatic first PR), or invest in the
   Bézout-domain existence form now (the Isabelle AFP precedent level, requiring a
   residue/associate-choice redesign of `IsColumnHermiteNormalForm`)? (ℤ-first /
   Bézout-now)
4. Shape: square nonsingular only (matches the bundle and the project's needs), or
   rectangular m×n any-rank (the full literature form, requiring a rectangular
   restatement of the predicate and bundle)? (square-first / rectangular)
5. If no to 1: keep the whole HNF file project-local as-is (it is internally coherent,
   mathlib-idiomatic, and load-bearing for CyclicSublattice), and record the n×n HNF as
   a "missing mathlib API" note rather than a planned contribution? (yes/no)

**Next action:** user answers the questions. Answering 1 = yes turns this into a
`/develop` ticket ("n×n integer column HNF: existence + uniqueness, matrix + basis
forms, SNF-template file layout beside LinearAlgebra/FreeModule/PID.lean"), after which
this decl inherits "specialise from the general form" status. Answering 1 = no keeps the
decl project-local with no further action.
