# /mathlibable report — `Submodule.hermiteNormalForm`

Assessed 2026-07-18 against mathlib pin 2026-05-28 (`2abc2425`). Mode A, full exhaustive
protocol. Fate coupled to `Submodule.exists_hermiteNormalForm` (stored verdict:
BORDERLINE-needs-human, same directory) — overlapping searches cite that report where the
concept coincides; everything def-specific was verified fresh.

---

### Baseline (Phase 0)

- lake build:               ✓ clean ("Build completed successfully (3909 jobs)"; one unrelated style warning in QExpSimpConditionTests.lean)
- decl `Submodule.hermiteNormalForm`: ✓ resolved at `XYin/PhD/Cox/HermiteNormalForm.lean:467`
- kind:                      noncomputable def
- has sorry:                 no
- module docstring summary:  Hermite-normal-form API for full-rank integer submodules (Cox Ch. 11); HNF is canonical only after fixing the ambient basis; bundled structure in arbitrary finite rank, constructive existence in rank two.

---

### Statement (Phase 1)

`Submodule.hermiteNormalForm` is a definition of the following:

For a free ℤ-module M with a fixed basis bM indexed by Fin 2 and a full-rank submodule
N ≤ M (finrank ℤ N = 2), it selects **the** canonical Hermite-normal-form datum of N
relative to bM — a basis bN of N together with the 2×2 inclusion matrix in bases
(bN, bM), in column HNF — by applying `Classical.choice` to the existence theorem
`Submodule.exists_hermiteNormalForm`. The word "the" is mathematically justified by the
file's rank-2 uniqueness theorems (`HermiteNormalForm.matrix_eq` at :278,
`HermiteNormalForm.bN_eq` at :338): the HNF datum is unique, so the choice is canonical
up to provable equality of components. This is the "HNF basis of a sublattice" as a
well-defined assignment, the sublattice form of the HNF(A) function of computer algebra.

Variables / typeclasses involved (Lean side):
- `M : Type*` `[AddCommGroup M]` — ambient abelian group (rank-2 ℤ-lattice via `bM`)
- `bM : Basis (Fin 2) ℤ M` — the fixed ambient basis (HNF is basis-relative)
- `N : Submodule ℤ M` — the sublattice

Hypotheses (Lean side):
- `hN : Module.finrank ℤ N = 2` — full rank (⟺ finite index)

Conclusion (math): the canonical HNF datum of N relative to bM.

Conclusion (Lean): n/a — definition; type `Module.Basis.HermiteNormalForm bM N`, body
`Classical.choice (N.exists_hermiteNormalForm bM hN)`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a packaging/chooser def over the file's BIG existence theorem — it introduces no
new mathematical structure itself (the structure `Module.Basis.HermiteNormalForm` and the
existence/uniqueness theorems carry the content); it is the ergonomic entry point.
(Literature width EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`Classical.choice (N.exists_hermiteNormalForm bM hN)`)
One-liner verdict: ONE-LINER

| Exemption                        | Applies? | Evidence |
|----------------------------------|----------|----------|
| Avoid defeq abuse                | no       | no downstream proof depends on the RHS spelling; `Classical.choice` is opaque anyway, so there is nothing to seal |
| Avoid typeclass diamonds         | no       | not an instance; no typeclass-search path involved |
| Mark semantic intent / API name  | **yes**  | the stable name is the API surface: the sole direct consumer `PeriodPair.CyclicSublattice.hermiteNormalForm` (CyclicSublattice.lean:55–57) fans out to 40+ uses across CyclicSublattice.lean and CyclicSublattice/Classification.lean (`.bN`, `.matrix`, `.isColumnHermiteNormalForm.diagonal_pos`, `.matrix_eq`, `.index_eq_natAbs_det`, …); the name encodes canonicity ("THE HNF"), formally backed by the uniqueness theorems `matrix_eq`/`bN_eq` — exactly mathlib's own pattern of naming `.choose`-packagings of existence proofs (`Submodule.smithNormalForm`, `smithNormalFormBotBasis/TopBasis/Coeffs`, `Ideal.ringBasis/selfBasis/smithCoeffs`, all in Mathlib/LinearAlgebra/FreeModule/PID.lean:601–730) |

Conclusion: ONE-LINER WITH-EXEMPTION (semantic intent / API name).

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

The parent report (`Submodule.exists_hermiteNormalForm.md`, same directory, assessed
2026-07-18 at this pin) ran the full nine-channel protocol on the identical underlying
concept (Hermite normal form for sublattices); its table is incorporated by citation for
the concept-level rows. The def-specific question — is "the HNF" a standard *canonical
assignment/function*, and how is the choice packaged — was searched fresh (rows 1–4).

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Hermite normal form" unique basis sublattice canonical fixed basis | yes | "For any lattice contained in ℤⁿ, there exists a **unique** basis H in HNF, **called the HNF basis** of the lattice"; for sublattice Λ′ ≤ Λ and every basis B of Λ there is a unique basis B′ = BH with H in HNF; index-m sublattices ↔ HNF matrices of det m | Shmonin EPFL notes; arXiv 2310.12519; scispace/numberanalytics HNF surveys — the *definite article* is standard, i.e. the canonical-assignment reading is the literature norm |
|  2 | WebSearch (general form / function packaging) | HermiteForm function Sage Magma PARI canonical form of lattice basis matrix | yes | HNF universally shipped as a **function**: MATLAB `hermiteForm`, PARI `mathnf`, Sage `hermite_form`, Magma `HermiteForm()` — "a canonical representation of a matrix over ℤ" | Sage reference manual, Wikipedia/HandWiki HNF; the computational literature treats HNF(A) as a total function on full-rank input, exactly what a chooser def formalises |
|  3 | WebSearch (formalisation precedent) | Isabelle AFP Hermite uniqueness Divasón canonical | yes | AFP `Hermite` entry (Divasón–Aransay): HNF is "a well-known **canonical** matrix analogue of reduced echelon form" over Bézout domains; **uniqueness of the HNF is formalised** — the canonicity claim is part of the formal package | isa-afp.org/entries/Hermite.html; Springer 10.1007/978-3-319-99957-9_3 — precedent: formal libraries ship uniqueness alongside existence precisely to justify "the" HNF |
|  4 | ChatGPT MCP (gpt-5.4, high)      | is "the HNF" standardly a well-defined function; mathlib idiom for chosen-datum defs; `Classical.choice`+`Nonempty` vs `∃`+`.choose`; coupling to the existence theorem; noncomputable vs algorithmic | yes | (i) yes — once conventions (row/column, positivity, remainder, ambient basis) are fixed, uniqueness makes HNF(·) a canonical assignment (MathWorld, AFP, ACM); (ii) chosen-datum defs are standard mathlib idiom once existence is accepted — precedent `Submodule.smithNormalForm/…TopBasis/…BotBasis/…Coeffs`, `Ideal.ringBasis/selfBasis/smithCoeffs`; reviewers indifferent between `Classical.choice`-of-`Nonempty` and `∃`+`.choose`; the strongest API adds a `Subsingleton (HermiteNormalForm bM N)` instance from uniqueness; (iii) **"it should not go in ahead of the existence theorem … its fate is coupled"** — same PR or a later small PR, never before; (iv) noncomputable-first is mathlib's accepted order; an algorithmic HNF is a later layer, not a prerequisite | Confirms coupling and the packaging idiom |
|  5 | Local references                 | `.mathlib-quality/references/` absent (n/a — recorded); substituted `.mathlib-quality/overview/analysis/step4-lattice.md` + `step6-generalization.md` (as in the sibling reports) | yes | step4: mathlib has NO HNF (verified at pin); step6 §A1: mathlib-right form is n×n over ℤ first, Bézout follow-up, difficulty High — the chooser def rides whichever form ships | Cited from parent report; re-verified mathlib absence fresh in Phase 5 below |
|  6 | nLab                             | "Hermite normal form" (parent report row 6, same concept) | yes | HNF as **canonical representative** of unimodular-equivalence classes; sign conventions vary, each yielding uniqueness | Canonical-representative framing is exactly the def's mathematical content |
|  7 | nCatLab (if categorical)         | n/a — not a categorical concept (matrix/lattice reduction theory; parent report row 7 verified the nLab page offers no categorical abstraction) | n/a | — | — |
|  8 | Stacks Project (if alg geom)     | n/a — not an algebraic-geometry concept (parent report row 8 verified: no HNF tag; SNF only incidental) | n/a | — | — |
|  9 | MathOverflow / Math.StackExchange| every sublattice has unique HNF basis (parent row 9, same concept) | yes | bijection index-m sublattices ↔ HNF matrices det m; **unique** HNF basis for every sublattice | Uniqueness ⇒ the chooser is canonical, not arbitrary |
| 10 | recent arXiv (last 5 years)      | (parent row 10 + fresh hits from row 1) | yes | arXiv 2310.12519 (sublattice ↔ HNF bijection), 2405.19302 (HNF over Hermitian lattices), 2605.07784 Labahn–Storjohann | Contemporary usage treats HNF(·) as the canonical-form map |

### Literature summary (Phase 3)

Concept identified as: **the canonical Hermite-normal-form basis of a sublattice** — the
function/assignment form of HNF existence + uniqueness (Hermite 1851). The literature
uses the definite article ("the HNF basis of the lattice") and computer algebra ships it
as a function (`hermiteForm`, `mathnf`, `hermite_form`, `HermiteForm`).

Sources agree on the standard form: yes — canonical assignment once conventions are
fixed; uniqueness is the justification (formalised as such in Isabelle AFP).

Most general standard form: HNF(·) as a canonical-form function on m×n integer matrices
(rectangular, any rank) / arbitrary-rank sublattices relative to a fixed ambient basis;
Bézout-domain existence in the strongest formalised precedent. The rank-2, square,
full-rank, ℤ chooser is the specialisation matching this project's needs.

Generality dimensions where the literature varies: identical to the parent report
(rank/shape, ring, matrix-vs-basis packaging) plus one def-specific dimension:
**how the canonical datum is packaged** — algorithmic function (CAS, AFP) vs
choice-from-existence (mathlib's SNF idiom, `.choose`-projections). Mathlib precedent is
noncomputable-choice-first, algorithm later.

Disagreement with the literature: none on content; the narrowness (rank 2, ℤ) is
inherited verbatim from the existence theorem it packages.

---

### Generality analysis — `Submodule.hermiteNormalForm` (Phase 4a)

Literature-standard form (from Phase 3): canonical HNF chooser for arbitrary finite rank
over ℤ (ultimately rectangular / Bézout), relative to a fixed ambient basis.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|--------------------------------|
| 1 | index type `Fin 2` | rank 2 hard-coded | arbitrary finite rank n | NO (not mechanically) | inherited from `exists_hermiteNormalForm`: the `Fin 2` restriction is baked into the `!![..]`-literal core `exists_hnf_transform`; the def cannot be more general than the existence theorem it `Classical.choice`s. Parent report verified this is false-positive class 5 (real generalisation, not a signature edit) |
| 2 | ring ℤ | ℤ | Bézout/Euclidean | NO (not mechanically) | same inheritance; also the `IsColumnHermiteNormalForm` predicate is ℤ-order-specific (`Set.Ico 0 pivot`) |
| 3 | `hN : finrank ℤ N = 2` | full rank, rank-2 spelling | any submodule (rectangular); mathlib spelling `finrank ℤ N = finrank ℤ M` | NO (not mechanically) / cosmetic respelling only | full-rank is baked into the square bundle (parent row 3); the `= finrank ℤ M` respelling (cf. `smithNormalFormBotBasis`) is cosmetic and equal here since `bM : Basis (Fin 2)` |
| 4 | body `Classical.choice (Nonempty …)` | choice of `Nonempty` bundle | mathlib SNF idiom: `∃` + `.choose` projections | no (equivalent packaging) | ChatGPT MCP: reviewers indifferent; determined by how the existence theorem is spelled, which is a parent-level decision |

### Generality verdict (Phase 4b)

Verified-weakening note: there is no hypothesis to drop and compile-check — every
narrowness dimension lives in the *parent existence theorem* (whose report verified,
with the proof body in hand, that no weakening is a mechanical edit: the 2×2 Euclidean
core is `!![..]`-literal computation). The def is a 1-line wrapper; weakening it without
weakening the parent is type-incorrect by construction (`Classical.choice` needs the
parent's `Nonempty` at exactly the parent's generality). Per the verdict-gate routing
this is false-positive class 5 (via inheritance), excluding `YES-but-generalise-first`.

The current form is: STRICTLY NARROWER THAN STANDARD (rank 2, ℤ, full-rank vs rank-n /
rectangular / Bézout), narrowness inherited from and only fixable through the parent —
new mathematical development (rank-n column-reduction induction, graded High in step6
§A1), not a signature edit.

Number of weakening opportunities found: 0 mechanical; the real generalisations are the
parent's (rank n over ℤ: High; Bézout: Medium–High).

Cost of the true generalisation: EXPENSIVE (scoping decision — Phase 7 questions,
shared with the parent).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|--------------------------------|
| 1 | typeclasses instead of bundled hypotheses | no | chosen data is correctly a def returning a structure; mirrors `Submodule.smithNormalForm` | — |
| 2 | filters/nets | no | finite algebra; no topology | — |
| 3 | universal property instead of construction | no | HNF is a canonical representative, not a universal object; the "characterisation" is uniqueness, best expressed as `Subsingleton (HermiteNormalForm bM N)` (see Q8 row and Phase 5.5) | — |
| 4 | bundled substructure | no | already `Submodule` | — |
| 5 | typeclass-hierarchy weakening | yes (inherited) | ℤ → Euclidean/Bézout — parent-level redevelopment of predicate + existence; the chooser follows for free once the parent moves | F[x]-HNF, computational algebra |
| 6 | higher-categorical | no | matrix reduction theory | — |
| 7 | concrete index generalisation | yes (inherited) | `Fin 2` → `Fin n`/rectangular at the parent; the chooser def is then verbatim the same one line | the mathlib-right form; sits beside `Submodule.smithNormalForm` in LinearAlgebra/FreeModule |
| 8 | concrete-via-abstract (proof-body diagnostic) | no — diagnostic run, does not fire | the body is `Classical.choice (N.exists_hermiteNormalForm bM hN)`: 1 line, wholly the named parent; there is no hidden abstract content to extract — the def *is* its packaging | n/a. Def-specific idiom note instead: given uniqueness (`matrix_eq`/`bN_eq`), a `Subsingleton (HermiteNormalForm bM N)` instance would formally justify canonicity (ChatGPT MCP recommendation) — an *addition*, not a restatement |
| 9 | false-generalisation guard | no false generalisation | the rank-n/Bézout targets are the same theorem-package (HNF) at standard generality; the chooser generalises truthfully alongside | safe |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — but it is the parent's generalisation (Q5/Q7), which is
EXPENSIVE new development, so it feeds the Phase 7 scoping question, not a
self-resolving `YES-but-generalise-first`. Def-specific modernisation is limited to
(a) `∃`+`.choose` respelling (cosmetic, reviewer-indifferent) and (b) adding a
`Subsingleton` instance for canonicity (an addition riding the uniqueness pair).
- Real mathematical improvement: canonicity-as-`Subsingleton` is a genuine API
  improvement (users reason by uniqueness instead of unfolding `Classical.choice`);
  everything else is parent-coupled.

---

### Proof strategy — `Submodule.hermiteNormalForm` (Phase 4.6a)

| # | Question | Applies? | Idiomatic alternative | Cost of switch |
|---|----------|----------|------------------------|----------------|
| 1 | ε-δ vs filters | no — no topology | — | — |
| 2 | element-wise vs point-free | no — body is a single `Classical.choice` | — | — |
| 3 | sequences vs nets | no | — | — |
| 4 | construction vs universal property | no — the chooser is the right shape; canonicity via `Subsingleton` is an add-on, not a rewrite | — | — |
| 5 | missing mathlib helpers | yes (inherited) | the missing helper is the rank-n HNF existence theorem itself (the parent's upstream dev-ticket); the chooser needs nothing else | (parent ticket) |

### Proof strategy verdict (Phase 4.6b)

Current strategy: MATHLIB-IDIOMATIC — `Classical.choice` of a `Nonempty` bundle is the
exact analogue of mathlib's `.choose`-packaging of `exists_smith_normal_form_of_rank_eq`
(PID.lean:601–634); the `Nonempty`-vs-`∃` difference is cosmetic and determined by the
parent's spelling. No refactor recommended.

---

### Diamond / defeq risk — `Submodule.hermiteNormalForm` (Phase 4.5)

Declaration kind is `def` — phase runs.

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | not a `class`/`instance`; returns a plain structure (`Module.Basis.HermiteNormalForm bM N`), which itself declares no instances (grep of HermiteNormalForm.lean: zero `instance` declarations); nothing enters typeclass search |
| 2 | Reducibility leak | none | not `@[reducible]`; body is `Classical.choice _`, which is opaque — no computation can leak into defeq checking. (Reducibility probe: `rfl` between the def and its body cannot reduce through `Classical.choice` anyway; the def is semi-reducible with an irreducible core, the safest configuration) |
| 3 | Non-canonical unfolding | none | `simp`/`rfl` cannot unfold through `Classical.choice`; downstream code (40+ transitive sites) reasons exclusively via projections (`.bN`, `.matrix`) and the uniqueness lemmas `matrix_eq`/`bN_eq` — the intended discipline, empirically confirmed at every call site |
| 4 | Instance priority collision | none | not an instance; no priority involved |
| 5 | Universe-polymorphism issues | none | `M : Type*` with the structure in `Type (max …)` as usual for basis-bundles; identical universe shape to mathlib's `Submodule.smithNormalForm` (parametrised the same way); no forced annotations, and the sole consumer instantiates `M = ↥L.lattice : Type` without friction |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort` on the def or on `HermiteNormalForm` (grep: none); field access only |

### Risk verdict (Phase 4.5)

Overall risk: NONE
Top risks: none. The def is a noncomputable chooser returning a bundle consumed by
projection — the same infrastructure profile as `Submodule.smithNormalForm`, which has
lived in mathlib without incident.

---

### Mathlib search-status: `Submodule.hermiteNormalForm` (Phase 5)

[A] Lean-Finder    "canonical choice of Hermite normal form basis for a finite index sublattice of the integer lattice relative to a fixed ambient basis" → **no HNF hits**; nearest: `IsZLattice.basis`, `Module.Basis.ofZLatticeBasis`, `PeriodPair.latticeBasis` (basis-existence choosers, none HNF/triangular)
[B] Loogle         `"hermite"` → only `NumberField.hermiteTheorem.*` (discriminant-finiteness, unrelated) and Hermite polynomials; no HNF, no HNF chooser
[C] LeanSearch     "canonical choice of a Smith normal form basis for a full rank submodule of a free module" → the SNF chooser family (`Submodule.smithNormalForm`, `smithNormalFormTopBasis/BotBasis`, `Module.Basis.SmithNormalForm(.mk/.bN)`) — confirming the packaging *idiom* exists in mathlib, for SNF only; no HNF analogue
[D] Grep mathlib   `grep -ril hermite Mathlib/` (fresh, this pin) → exactly 3 files: `RingTheory/Polynomial/Hermite/{Basic,Gaussian}.lean`, `NumberTheory/NumberField/Discriminant/Basic.lean` — **no Hermite normal form anywhere in mathlib**; grep of `LinearAlgebra/FreeModule/PID.lean` confirms the `.choose`-packaging precedent at lines 601–634 (`smithNormalFormTopBasis/BotBasis/Coeffs`) and 698–730 (`Ideal.ringBasis/selfBasis/smithCoeffs`)
[E] Name pattern   `lean_local_search "hermiteNormalForm"` (fresh) → project-only: `Submodule.hermiteNormalForm`, `PeriodPair.CyclicSublattice.hermiteNormalForm`, `…hermiteNormalForm_matrix_eq_inclusionMatrix`

Searched for both:
- the user's current form (rank-2 canonical HNF chooser) — not in mathlib
- the literature-standard form (rank-n / rectangular HNF canonical-form function;
  Bézout-domain form) — not in mathlib in any formulation; the analogous *idiom*
  exists only on the SNF side (`Submodule.smithNormalForm` etc.), which is a different
  normal form (two-sided, forgets the ambient basis — parent report Phase 6 verified
  non-substitutability)

Concluded: **"not in mathlib (all 5 methods exhausted, plus the literature-standard
form)"** — mathlib has no HNF and hence no HNF chooser; it does have the exact
packaging idiom this def instantiates, on the SNF side.

---

### Normal-form check — Phase 5.5a

Equivalent formalisms this def could take:
1. `Classical.choice` of the `Nonempty` bundle (current)
2. `.choose`-style projections of an `∃`-spelled existence theorem (mathlib SNF idiom: separate `hermiteNormalFormBasis`, `hermiteNormalFormMatrix` defs)
3. a `Unique`/`Subsingleton`-mediated "the unique element of" definition (possible here because of `matrix_eq`/`bN_eq`; not mathlib's usual pattern)

Does mathlib already have a canonical form for this idea? Not for HNF (no HNF at all);
the canonical *pattern* is the SNF chooser family, and form 1 is its direct analogue
(one bundled chooser rather than three projections — arguably cleaner than SNF's
triple, since the bundle keeps `toMatrix_eq` attached). RHS convention: n/a (def).

### Syntactic generality — Phase 5.5b

Alternative restatements attempted:
- current: `(bM) (N) (hN : finrank ℤ N = 2)` returning the bundle — matches every call site (the sole consumer passes `L.latticeBasis`, `S.carrier`, `S.carrier_finrank` and projects fields)
- mathlib-facing: hypothesis respelled `finrank ℤ N = finrank ℤ M` (the `smithNormalFormBotBasis` convention), `∃`+`.choose` packaging — cosmetic here, right for a PR
- `Subsingleton`-backed variant — an addition (instance + `eq_hermiteNormalForm` lemma), not a restatement

Chosen restatement: current form for the project; for a PR, the respelling rides the
parent's restatement (subsumed by the Phase 7 scoping questions).
Justification: all consumers hold a concrete rank-2 `finrank = 2` proof; the bundle
projection pattern is used at every site.

### Superfluous-argument audit — Phase 5.5c

| # | Argument / typeclass | Essentially used? | Notes |
|---|----------------------|-------------------|-------|
| 1 | `[AddCommGroup M]` | yes | needed for `Submodule ℤ M` |
| 2 | `bM : Basis (Fin 2) ℤ M` | yes | HNF is relative to the fixed ambient basis — the definitional point |
| 3 | `hN : finrank ℤ N = 2` | yes | feeds the parent existence theorem; without full rank the bundle type is empty |

None superfluous.

### Statement-shape verdict (Phase 5.5d)

Normal form: OK (instantiates mathlib's SNF-chooser pattern; no existing HNF form to align with)
Syntactic generality: OK locally; PR-facing respelling subsumed by the parent's scoping question
Superfluous arguments: NONE
Overall: SHIP-AS-STATED locally; PR-facing shape decided with the parent.

---

### Call sites — `Submodule.hermiteNormalForm` (Phase 6.0)

Internal use count: **1** direct (excluding the declaring file)
External-to-file callers: 1 distinct file (with massive transitive fan-out)

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| XYin/PhD/Cox/CyclicSublattice.lean:55–57 | `noncomputable def hermiteNormalForm (S : CyclicSublattice L m) : … := S.carrier.hermiteNormalForm L.latticeBasis S.carrier_finrank` — re-exported as `PeriodPair.CyclicSublattice.hermiteNormalForm` |
| (transitive, via the re-export) | 40+ uses across CyclicSublattice.lean (:60–:590: `.bN`, `.matrix`, `.isColumnHermiteNormalForm.diagonal_pos/.belowDiagonal_eq_zero`, `.repr_apply`, `.index_eq_natAbs_det`, `.quotient_isAddCyclic_iff_rankTwoContent_eq_one`) and CyclicSublattice/Classification.lean (:29–:345: `.matrix_eq` against `inclusionHermiteNormalForm`, `hermiteNormalForm_matrix_eq_inclusionMatrix`, `.range_toLin_matrix_eq`) |

Inline-derivation grep (equivalent re-derived elsewhere without using the decl?): (none)
— no site applies `Classical.choice` to the existence theorem directly; every HNF datum
in the project flows through this def (the parent report's inline-grep, re-run here,
agrees).

Signal (per 6.0.1): K = 1 direct with a single project-level re-export fanning to 40+
sites — the canonical existence-chooser consumption pattern, identical to mathlib's SNF
choosers (whose direct consumers are also thin wrappers/projections). Real API,
YES-leaning composability signal; but the def is only as shippable as its parent.

### Composition check (Phase 6)

Can `Submodule.hermiteNormalForm` be derived from mathlib in ≤3 chained calls?

Attempt 1 (from mathlib primitives): the def's type is `Module.Basis.HermiteNormalForm
bM N` — a **project-local structure mathlib does not have**; no mathlib composition can
even state it, and the only inhabitant-producer is the project's existence theorem.
Mathlib's SNF choosers (`smithNormalFormBotBasis` etc.) produce SNF data, which the
parent report verified (two independent channels) cannot be converted to HNF data —
SNF forgets the fixed ambient basis.
  - Mathlib decls used: (none applicable)
  - Result: fails
Attempt 2 (from the project's own parent): `Classical.choice (N.exists_hermiteNormalForm
bM hN)` — 1 call, succeeds trivially, **but the parent is not a mathlib decl** (it is
the BORDERLINE sibling); composability-from-mathlib is what the bucket requires.
  - Result: not a mathlib composition

Conclusion: **NOT-COMPOSABLE** (from mathlib). Within the project it is a 1-call
packaging of the parent — which is precisely why its verdict is inherited rather than
independent.

---

## Verdict: `Submodule.hermiteNormalForm`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): "the HNF basis" is the standard canonical assignment
  (definite article in the lattice literature; CAS function precedent `hermiteForm`/
  `mathnf`/`hermite_form`/`HermiteForm`; AFP formalises uniqueness to justify
  canonicity); ChatGPT MCP verbatim: the chooser "should not go in ahead of the
  existence theorem … its fate is coupled".
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD, with zero mechanical
  weakenings — all narrowness is inherited from the parent existence theorem
  (false-positive class 5 by inheritance), excluding `YES-but-generalise-first`.
- Phase 4.5 risk: NONE (noncomputable chooser, no instances/coercions/reducibility).
- Mathlib search (Phase 5): no HNF (hence no HNF chooser) anywhere in mathlib, all five
  methods, both forms; mathlib has the exact packaging idiom on the SNF side
  (`Submodule.smithNormalForm`, PID.lean:601–634), so the def's *shape* is
  mathlib-approved.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (its type is a project-local
  structure); 1-call composable from the project's own BORDERLINE parent; K = 1 direct
  call site re-exported to 40+ transitive uses — the canonical chooser pattern.

**Rationale:**

This def is the canonical-choice packaging of `Submodule.exists_hermiteNormalForm`, and
its verdict is structurally forced to be the parent's. Both NO buckets fail on the
evidence: mathlib has no HNF in any formulation (Phase 5, re-verified fresh at this
pin), and no mathlib composition can even type-check the def (its codomain is the
project-local `Module.Basis.HermiteNormalForm` bundle) — so nothing in mathlib replaces
it and nothing in mathlib composes to it. Both YES buckets also fail as self-resolving
verdicts: the def cannot ship ahead of, or separately from, the existence theorem it
`Classical.choice`s (confirmed independently by the ChatGPT channel and by the obvious
dependency), and that theorem's own full assessment landed BORDERLINE-needs-human —
rank-2/ℤ/square is below the literature-standard generality, and reaching the standard
form is EXPENSIVE new development (rank-n column reduction, graded High), a scope
commitment only the user can make. What this assessment adds beyond the parent's: the
def itself is exactly what mathlib would want *once the parent ships* — it instantiates
mathlib's own SNF-chooser idiom (`Submodule.smithNormalForm` and the `.choose` family
in PID.lean), the one-liner check passes on the semantic-intent/API-name exemption
(named canonical datum, uniqueness-backed, 40+ transitive consumers), and the
diamond/defeq risk audit is clean across all six rows. So the def contributes no
independent mathlib question; it inherits the parent's five scoping questions, plus two
packaging decisions that only matter if the parent's answer is "upstream".

**Numbered questions (≤4):**

1. (= parent Q1, decisive for this def) Are you committing to the mathlib-right
   development — n×n integer HNF existence (+ uniqueness) with the basis corollary —
   per the parent report's plan? If yes, this def becomes the rank-n chooser in the
   same PR series; if no, it stays project-local. (yes/no)
2. If yes to 1: package as one bundled chooser (current shape — arguably cleaner, keeps
   `toMatrix_eq` attached) or as SNF-style split projections
   (`hermiteNormalFormBasis` / `hermiteNormalFormMatrix`, `.choose`-based)?
   (bundled / split)
3. If yes to 1: add the canonicity API the ChatGPT channel recommends — a
   `Subsingleton (Module.Basis.HermiteNormalForm bM N)` instance derived from
   `matrix_eq`/`bN_eq`, so "the canonical HNF" is formally justified and users never
   unfold `Classical.choice`? (yes/no)
4. If no to 1: keep the def project-local as-is (it is idiomatic, risk-free, and the
   sole supplier of HNF data to the CyclicSublattice development) — agreed? (yes/no)

**Next action:** answer question 1 together with the parent report's questions — the
two reports resolve as a unit. Yes ⇒ one `/develop` ticket ("n×n integer column HNF:
existence + uniqueness + chooser + Subsingleton, matrix + basis forms, SNF-template
layout beside LinearAlgebra/FreeModule/PID.lean"); no ⇒ no further action, decl stays
project-local.
