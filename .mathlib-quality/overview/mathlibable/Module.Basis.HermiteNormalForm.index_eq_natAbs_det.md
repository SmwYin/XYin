# /mathlibable report — `Module.Basis.HermiteNormalForm.index_eq_natAbs_det`

Assessed 2026-07-17 against mathlib pin 2026-05-28 (plus Loogle/LeanSearch on mathlib HEAD).

---

### Baseline (Phase 0)
- lake build:               ✓ clean ("Build completed successfully (3909 jobs)")
- decl `Module.Basis.HermiteNormalForm.index_eq_natAbs_det`: ✓ resolved at `XYin/PhD/Cox/HermiteNormalForm.lean:351`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Hermite-normal-form API for full-rank integer submodules (Cox Ch. 11); bundled HNF structure in arbitrary finite rank, constructive existence in rank two.

---

### Statement (Phase 1)

`Module.Basis.HermiteNormalForm.index_eq_natAbs_det` is a theorem stating the following:

Let M be a free ℤ-module with a basis b_M indexed by Fin n, and let N ≤ M be a
submodule equipped with a Hermite-normal-form datum h relative to b_M — i.e. a
basis b_N of N together with the n×n integer matrix A of the inclusion N ↪ M in
the bases (b_N, b_M), where A is in column Hermite normal form. Then the index
of N as an additive subgroup of M equals |det A|. This is Cox, *Primes of the
Form x²+ny²*, Exercise 7.15 in the rank-two case ([M : N] = |ad − bc|).

Variables / typeclasses involved (Lean side):
- `M : Type*` `[AddCommGroup M]` — the ambient abelian group (a rank-n ℤ-lattice via `bM`)
- `n : ℕ`, `bM : Basis (Fin n) ℤ M` — the fixed ambient basis
- `N : Submodule ℤ M` — the full-rank submodule

Hypotheses (Lean side):
- `h : HermiteNormalForm bM N` — the bundled HNF datum: fields `bN : Basis (Fin n) ℤ N`,
  `matrix : Matrix (Fin n) (Fin n) ℤ`, `toMatrix_eq : LinearMap.toMatrix bN bM N.subtype = matrix`,
  `isColumnHermiteNormalForm : matrix.IsColumnHermiteNormalForm`

Conclusion (math): [M : N] = |det A| where A is the HNF inclusion matrix.

Conclusion (Lean): `N.toAddSubgroup.index = h.matrix.det.natAbs`

**Key structural observation (drives everything below):** the proof body uses only
`h.bN` and `h.toMatrix_eq`. The field `isColumnHermiteNormalForm` is never used —
the statement is true for *any* basis of N and *any* matrix representing the
inclusion; HNF-ness is mathematically irrelevant to index = |det|.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a corollary/specialisation of a general index-determinant principle, attached
as convenience API to the project's bundled `HermiteNormalForm` structure; it is not a
new structure, not a named theorem, and not a listed main result of the file (the main
results are the HNF existence and uniqueness theorems).
(Note: literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: n/a
One-liner verdict: n/a (kind is theorem, not def) — check skipped.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Hermite normal form determinant equals index of sublattice lattice quotient" | yes | 1–1 correspondence: sublattices of Λ of index m ↔ HNF matrices H with det H = m; for L' = LM, [L : L'] = \|det M\| | Micciancio CSE 206A lecture notes; Shmonin EPFL notes; arXiv:2310.12519 |
|  2 | WebSearch (general form)         | "index of finite-index subgroup of Z^n equals absolute value of determinant proof" | yes | For torsion-free abelian M of rank r and full-rank N ≤ M: [M : N] = \|det(transition matrix)\| for ANY pair of bases — no normal form needed | Keith Conrad SL₂(ℤ) notes; Lubotzky counting-subgroups notes |
|  3 | WebSearch (named-after / aliases)| Cox "Primes of the form" exercise sublattice index determinant Hermite | yes | Cox 3rd ed. (AMS 2022) with published solutions; Armin Straub "Hermite Normal Form: Introduction & Basic Applications"; [Γ : Γ(A)] = \|det A\| | Confirms the Cox-exercise identification |
|  4 | ChatGPT MCP (gpt-5.4, high)      | standard name/generality of [M:N]=\|det A\|; is HNF hypothesis needed; historical evolution; content of Cox Ex. 7.15 | yes | (i) det(Λ') = [Λ:Λ']·det(Λ); (ii) modern standard form is SNF/elementary divisors: ℤⁿ/Aℤⁿ ≅ ⊕ ℤ/dᵢℤ, \|ℤⁿ/Aℤⁿ\| = ∏dᵢ = \|det A\|; (iii) **HNF hypothesis is NOT mathematically needed — it only provides canonicity of the matrix**; (iv) over a PID: SNF statement; over Dedekind domains: index ideal / ideal norm; (v) Cox Ex. 7.15 asks exactly \|M/AM\| = \|det A\| for 2×2 integer A via an adjugate argument | Textbook anchors: Newman *Integral Matrices*, Cohen §2.4, Neukirch |
|  5 | Local references                 | `.mathlib-quality/references/` absent (n/a — recorded); substituted `.mathlib-quality/overview/analysis/step4-lattice.md` + `step6-generalization.md` | yes | step4 line 121: "Index = \|det\| API — already optimal" in mathlib CardQuotient; step4 line 119: HNF itself NOT in mathlib (grep empty); step6 A1 cites Wikipedia HNF, Cohen, Newman, Isabelle AFP Hermite entry (Divasón–Aransay, Bézout domains) | Prior analyses agree with channels 1–4 |
|  6 | nLab                             | index of sublattice / free abelian group determinant (via site-scoped search) | no dedicated page | index=\|det\| appears only as folklore inside "free abelian group"-adjacent material; nLab has no page for this fact | Elementary structure-theory fact; absence is itself informative |
|  7 | nCatLab (if categorical)         | n/a — not a categorical concept; the statement is a finite-abelian-group cardinality identity with no categorical content beyond the cokernel viewpoint (which is the SNF form, channel 4) | — | — | — |
|  8 | Stacks Project (if alg geom)     | n/a — not an algebraic-geometry concept; Stacks treats f.g. modules over rings but has no tag for lattice-index = determinant | — | — | — |
|  9 | MathOverflow / Math.StackExchange| "index of sublattice determinant free abelian group quotient elementary divisors" | yes | Standard answer everywhere: [L : L'] = \|det M\|; proved via SNF; det of lattice = product of elementary divisors | Dummit lecture notes, Voutsadakis, Vince "Elementary Divisors" |
| 10 | recent arXiv (last 5 years)      | sublattice index HNF (surfaced by channels 1, 9) | yes | arXiv:2310.12519 (2023) "Unimodular equivalence of sublattices": index-m sublattices ↔ HNF matrices of determinant m; arXiv:2306.17764 free sublattices of bounded index | Contemporary usage matches the classical form |

### Literature summary (Phase 3)

Concept identified as: the **sublattice index–determinant formula** ([M : N] = |det A|);
no personal name; classically Hermite (1851, triangular reduction) / Smith (1861,
elementary divisors); in Cox it is Exercise 7.15.
Sources agree on the standard form: yes.
Most general standard form: for a free module M of finite rank n over ℤ (more generally
the SNF statement over any PID; over Dedekind domains, the module-index ideal / ideal
norm), and ANY full-rank submodule N with ANY basis, [M : N] = |det A| where A is the
matrix of the inclusion in any pair of bases. **The HNF condition plays no role in this
statement** — it only canonicalises the matrix (uniqueness), and makes |det| = product
of pivots visible.
Generality dimensions where the literature varies:
  - base ring: ℤ (most sources) → PID via SNF (modern algebra) → Dedekind via index ideal (number theory)
  - normal form: none needed (general statement) → HNF (algorithmic texts) → SNF (structure theory)
  - index expression: |det A| → ∏ elementary divisors → ∏ HNF pivots
Disagreement with the literature: none on content; the project form carries a
superfluous HNF hypothesis relative to the literature-standard statement.

---

### Generality analysis — `Module.Basis.HermiteNormalForm.index_eq_natAbs_det` (Phase 4a)

Literature-standard form (from Phase 3): free ℤ-module M, finite index type ι, any basis
bM of M, any full-rank N ≤ M with any basis bN: `N.index = |det(matrix of inclusion)|`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|--------------------------------|
| 1 | index type `Fin n` | `Basis (Fin n) ℤ M` | arbitrary `[Fintype ι] [DecidableEq ι]` | yes | forced only by the project's `HermiteNormalForm` structure design (`Fin n` + `Preorder` for triangularity); mathlib's general lemma already uses arbitrary ι |
| 2 | `h : HermiteNormalForm bM N` | bundled basis + matrix + toMatrix_eq + **HNF property** | just a basis bN (matrix then determined) | yes — **verified** | proof uses only `h.bN` and `h.toMatrix_eq`; the `isColumnHermiteNormalForm` field is unused. Verified by compiling the statement with a proof that consumes only those two fields (lean_run_code, clean) |
| 3 | conclusion `N.toAddSubgroup.index` | `AddSubgroup.index` | same | no (already standard) | matches mathlib's `AddSubgroup.index_eq_natAbs_det` LHS exactly |
| 4 | conclusion RHS `h.matrix.det.natAbs` | det of the stored inclusion matrix | `(bM.det (bN ·)).natAbs` (basis.det form) | yes | the two are equal via `Basis.det_apply` + the HEAD bridge `LinearMap.toMatrix_eq_basisToMatrix`; mathlib's spelling is the canonical one |

### Generality verdict (Phase 4b)

Verified weakening: the composition proof compiled clean (lean_run_code, zero
diagnostics) using **none** of the HNF-specific content — this is the mechanical
verification that hypothesis 2 weakens.

The current form is: STRICTLY NARROWER THAN STANDARD — **but the fully general form
already exists in mathlib** (`AddSubgroup.index_eq_natAbs_det`, and
`Submodule.natAbs_det_basis_change` / `Submodule.natAbs_det_equiv`). This is
false-positive class 4 of the verdict-gate catalogue ("general form already in
mathlib"): the correct routing is a NO bucket, **not** YES-but-generalise-first.
Number of weakening opportunities found: 2 (both land exactly on the existing
mathlib lemma, so there is nothing new to contribute by generalising).
Proposed restatement: none — the generalisation *is* `AddSubgroup.index_eq_natAbs_det`.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|--------------------------------|
| 1 | typeclasses instead of bundled hypotheses | no | — | the bundle (`HermiteNormalForm`) mirrors mathlib's own `Module.Basis.SmithNormalForm` bundle pattern; bundling is the mathlib idiom here |
| 2 | filters/nets instead of sequences | no | — | no topology involved (finite combinatorial identity) |
| 3 | universal-property class instead of construction | no | — | no construction being characterised |
| 4 | bundled substructure instead of set-with-predicate | no | — | already uses `Submodule`/`AddSubgroup` |
| 5 | typeclass-hierarchy weakening (field→ring etc.) | yes (in principle) | PID/Dedekind version via SNF or index ideal | mathlib already realises this: `Module.Basis.SmithNormalForm.toAddSubgroup_index_eq_pow_mul_prod` (Mathlib/LinearAlgebra/FreeModule/Int.lean) states index = ∏ ideal-indices over any `CommRing` for its SNF bundle — the generalised road is built, on the SNF side |
| 6 | higher-categorical generalisation | no | — | none in scope |
| 7 | concrete index type generalisation (Fin n → ι) | yes | arbitrary `[Fintype ι]` | already how mathlib's `AddSubgroup.index_eq_natAbs_det` is stated; subsumed by the NO routing |
| 8 | concrete-via-abstract (proof ignores the named object) | **yes — the diagnostic fires** | grep of the proof body: `isColumnHermiteNormalForm` occurs 0 times in the proof of this theorem (only `h.bN`, `h.toMatrix_eq`); the "concrete" datum (HNF-ness) is never consumed | the abstract form is precisely mathlib's `AddSubgroup.index_eq_natAbs_det`; the concrete result is a one-rw corollary (verified) |
| 9 | false-generalisation guard | no false generalisation | Q7/Q8 targets are the *same* mathematical statement (index = \|det\| of the inclusion matrix), not a symbol-sharing different object | safe |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — but the modern-idiom form **is an existing mathlib
declaration**, so it feeds the NO-composable routing rather than
YES-but-generalise-first. No restatement to propose: nothing would be added to mathlib
that it does not already state more generally.

---

### Proof strategy — `Module.Basis.HermiteNormalForm.index_eq_natAbs_det` (Phase 4.6a)

| # | Question | Applies? | Idiomatic alternative | Cost of switch |
|---|----------|----------|------------------------|----------------|
| 1 | ε-δ vs filters | no | — (no topology) | — |
| 2 | element-wise vs point-free algebra | no | proof is already a rewrite chain to a mathlib primitive | — |
| 3 | sequences vs nets | no | — | — |
| 4 | construction vs universal property | no | — | — |
| 5 | missing mathlib helpers | yes (resolved at HEAD) | the bridge `LinearMap.toMatrix bN bM f = bM.toMatrix (⇑f ∘ ⇑bN)` is `LinearMap.toMatrix_eq_basisToMatrix` at mathlib HEAD (Mathlib/LinearAlgebra/Matrix/Basis.lean); absent from the 2026-05-28 pin, which is why the local proof carries a 4-line `ext` (`hmatrix`) | CHEAP — after a mathlib bump the local proof shrinks to one `rw` |

### Proof strategy verdict (Phase 4.6b)

Current strategy: MATHLIB-IDIOMATIC (rewrite to the mathlib primitive
`AddSubgroup.index_eq_natAbs_det`; the only non-call step, `hmatrix`, exists solely
because the pin predates `LinearMap.toMatrix_eq_basisToMatrix`). No refactor needed
beyond the post-bump one-liner noted above.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is theorem.

---

### Mathlib search-status: `Module.Basis.HermiteNormalForm.index_eq_natAbs_det` (Phase 5)

[A] Lean-Finder    "index of full-rank subgroup of free abelian group = |det| of basis matrix; Hermite normal form" → **hits**: `AddSubgroup.index_eq_natAbs_det`, `AddSubgroup.relIndex_eq_natAbs_det`, `AddSubgroup.relindex_eq_abs_det`, `Submodule.natAbs_det_basis_change`, and the SNF-bundle analogues `Module.Basis.SmithNormalForm.toAddSubgroup_index_eq_pow_mul_prod` / `_eq_ite`
[B] Loogle         `Module.Basis.toMatrix, LinearMap.toMatrix` → **hit**: `LinearMap.toMatrix_eq_basisToMatrix : toMatrix b c f = c.toMatrix (⇑f ∘ ⇑b)` (HEAD, Mathlib/LinearAlgebra/Matrix/Basis.lean) — the missing bridge for the composition
[C] LeanSearch     "index of a submodule equals absolute value of determinant of the matrix of the inclusion" → **hits**: `Submodule.natAbs_det_equiv`, `AddSubgroup.index_eq_natAbs_det`, `AddSubgroup.relIndex_eq_natAbs_det`, `Ideal.natAbs_det_basis_change` (Dedekind/absNorm version), `ZLattice.covolume_eq_det`
[D] Grep mathlib   `natAbs_det|index_eq_natAbs|hermite` over `.lake/packages/mathlib` → **hits**: CardQuotient.lean (`Submodule.natAbs_det_equiv` :35, `Submodule.natAbs_det_basis_change` :85, `AddSubgroup.index_eq_natAbs_det` :98, `AddSubgroup.relIndex_eq_natAbs_det` :106), plus AbsNorm/FractionalIdeal/Discriminant consumers; "hermite" matches ONLY Hermite *polynomials* (RingTheory/Polynomial/Hermite) — no Hermite normal form anywhere in mathlib
[E] Name pattern   `lean_local_search "index_eq_natAbs_det"` → exactly two decls: the project's and mathlib's `AddSubgroup.index_eq_natAbs_det` — a name collision that is itself evidence the project decl is a wrapper

Searched for both:
  - the user's current form (HNF-bundled, `h.matrix.det.natAbs` RHS) — not in mathlib
    (mathlib has no HNF structure at all; the caller's suggested name
    `Submodule.natCard_quotient_eq_natAbs_det` does not exist in this pin — the actual
    decls are `Submodule.natAbs_det_equiv` / `natAbs_det_basis_change` /
    `AddSubgroup.index_eq_natAbs_det`)
  - the literature-standard form (any basis, index = |det|) — **in mathlib**, more
    general (arbitrary `ι`, no normal-form hypothesis)

Concluded: "found building blocks (`AddSubgroup.index_eq_natAbs_det`,
`Basis.det_apply`, `LinearMap.toMatrix_eq_basisToMatrix` [HEAD]); composition
yields our form" — and the general mathematical content is fully covered by
`AddSubgroup.index_eq_natAbs_det`.

---

### Normal-form check — Phase 5.5a

Equivalent formalisms this statement could take:
1. `N.toAddSubgroup.index = (bM.det (bN ·)).natAbs` — mathlib's canonical spelling (basis.det)
2. `N.toAddSubgroup.index = h.matrix.det.natAbs` — the project's spelling (stored inclusion matrix)
3. `Nat.card (M ⧸ N) = (…).natAbs` — the `Submodule.natAbs_det_basis_change` spelling

Does mathlib already have a canonical form for this idea? **yes** — form 1
(`AddSubgroup.index_eq_natAbs_det`). Our statement is `canonical ∘ (matrix-representation
rewrite)`; it is stated against the canonical form's LHS (`AddSubgroup.index`) with a
project-specific RHS. Not an orthogonal A↔B equivalence, so no O(n²) violation.
RHS convention respected? yes (index on the LHS, determinant data on the RHS, matching
mathlib's own convention in CardQuotient.lean).

### Syntactic generality — Phase 5.5b

Alternative restatements attempted:
- `(bM.det (bN ·)).natAbs` RHS (mathlib spelling) — most general, but forces callers holding an HNF bundle to convert matrix↔basis-det themselves
- `h.matrix.det.natAbs` RHS (current) — directly usable at the project's call sites, which all reason about the stored HNF matrix (e.g. `det = d·a` for `!![d, r; 0, a]`)

Chosen restatement: current form is the right *local* convenience spelling; the mathlib
spelling is the right *library* form and already exists.
Justification: every project call site consumes `h.matrix.det`, never `bM.det (bN ·)`.

### Superfluous-argument audit — Phase 5.5c

| # | Argument / typeclass | Essentially used? | Notes |
|---|----------------------|-------------------|-------|
| 1 | `[AddCommGroup M]` | yes | needed for `Submodule ℤ M` / index |
| 2 | `bM : Basis (Fin n) ℤ M` | yes | the determinant is relative to bM |
| 3 | `h.bN`, `h.toMatrix_eq` (fields) | yes | supply the basis and the matrix identification |
| 4 | `h.isColumnHermiteNormalForm` (field) | **no** | the conclusion holds for any inclusion matrix; the HNF field is dead weight in this hypothesis (unavoidable only because it rides inside the bundle) |

### Statement-shape verdict (Phase 5.5d)

Normal form: OK (stated against mathlib's canonical `AddSubgroup.index`)
Syntactic generality: OK for its role as bundle-projection convenience API
Superfluous arguments: 1 (the HNF property inside the bundle — the structural reason
this cannot ship to mathlib standalone)
Overall: SHIP-AS-STATED locally / not-shippable-standalone to mathlib (see verdict).

---

### Call sites — `Module.Basis.HermiteNormalForm.index_eq_natAbs_det` (Phase 6.0)

Internal use count: **3** (excluding the declaring file)
External-to-file callers: 2 distinct files

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `XYin/PhD/Cox/CyclicSublattice.lean:391` | `exact S.hermiteNormalForm.index_eq_natAbs_det.symm` |
| `XYin/PhD/Cox/CyclicSublattice/Classification.lean:40` | `h.index_eq_natAbs_det.symm` |
| `XYin/PhD/Cox/CyclicSublattice/Classification.lean:162` | `h.matrix.det.natAbs := h.index_eq_natAbs_det` |

Inline-derivation grep (equivalent re-derived elsewhere without using the decl?):
  - `XYin/PhD/Cox/CyclicSublattice.lean:572` calls mathlib's
    `AddSubgroup.index_eq_natAbs_det (transportedBasis S) …` directly — a sibling
    computation in a transported-basis setting (different basis, not the HNF bundle),
    demonstrating that call sites without an HNF bundle in hand already go straight to
    the mathlib primitive.

Signal (per 6.0.1): K = 3 internal uses → real *project-local* API; but the inline
mathlib-direct use at CyclicSublattice.lean:572 confirms the mathlib primitive is the
underlying workhorse and the decl is a convenience projection of the bundle.

### Composition check (Phase 6)

Can the decl be derived from mathlib in ≤3 chained calls?

Attempt 1 (**verified by lean_run_code — compiles with zero diagnostics**, modulo the
bridge lemma which exists at mathlib HEAD but postdates the project's pin):

```lean
example (h : Basis.HermiteNormalForm bM N) :
    N.toAddSubgroup.index = h.matrix.det.natAbs := by
  rw [AddSubgroup.index_eq_natAbs_det bM N.toAddSubgroup h.bN, Basis.det_apply,
    show bM.toMatrix (fun x => ((h.bN x : M))) = h.matrix from
      (LinearMap.toMatrix_eq_basisToMatrix h.bN bM N.subtype).symm.trans h.toMatrix_eq]
```

  - Mathlib decls used: `AddSubgroup.index_eq_natAbs_det`
    (Mathlib/LinearAlgebra/FreeModule/Finite/CardQuotient.lean:98), `Basis.det_apply`,
    `LinearMap.toMatrix_eq_basisToMatrix` (Mathlib/LinearAlgebra/Matrix/Basis.lean, HEAD)
    + the structure field `h.toMatrix_eq`
  - Result: **succeeds** (single `rw` chain, three mathlib lemmas + one field access)
  - Notes: on the 2026-05-28 pin the bridge lemma is missing, so the local proof
    simulates it with a 4-line `ext` (`hmatrix`) — still the same composition, just
    with the bridge inlined.

Conclusion: **COMPOSABLE**.

---

## Verdict: `Module.Basis.HermiteNormalForm.index_eq_natAbs_det`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): index = |det| is basis-independent and standard at
  greater generality (SNF over PIDs, index ideals over Dedekind domains); the HNF
  hypothesis is explicitly *not* part of the standard statement (ChatGPT MCP + Conrad +
  Micciancio + Cohen/Newman all agree) — HNF matters only for canonicity/uniqueness.
- Generality analysis (Phase 4): STRICTLY NARROWER, and the general form is an existing
  mathlib decl (false-positive class 4 → NO routing, not generalise-first). Q8
  diagnostic fired: the proof never consumes the HNF field.
- Mathlib search (Phase 5): found building blocks — `AddSubgroup.index_eq_natAbs_det`
  covers the entire mathematical content; `LinearMap.toMatrix_eq_basisToMatrix` (HEAD)
  bridges the matrix spelling. (No Hermite normal form of any kind in mathlib; the
  name `Submodule.natCard_quotient_eq_natAbs_det` suggested upstream does not exist —
  the real names are `Submodule.natAbs_det_equiv` / `natAbs_det_basis_change`.)
- Composition check (Phase 6): COMPOSABLE — verified compiling 1-`rw` / 3-lemma
  composition.

**Rationale:**

The declaration adds no mathematical content beyond mathlib's
`AddSubgroup.index_eq_natAbs_det`: its proof uses only the bundle's basis and
matrix-representation fields, never the Hermite-normal-form property, and the whole
statement was verified to compile as a single `rw` chaining three mathlib lemmas (one
of which, `LinearMap.toMatrix_eq_basisToMatrix`, landed at mathlib HEAD after this
project's pin). The literature is unanimous that index = |det| is a basis-independent
fact for which HNF is irrelevant; mathlib states it at strictly greater generality
(arbitrary finite index type, no normal-form hypothesis, plus relIndex, Nat.card,
Dedekind/absNorm variants). A standalone PR of this lemma is impossible anyway — it is
stated about `Module.Basis.HermiteNormalForm`, a structure mathlib does not have.

Caveat recorded for the *file-level* contribution plan: the HNF development itself
remains a genuine mathlib gap (prior analyses confirmed; re-verified here — mathlib's
only "Hermite" is Hermite polynomials), and mathlib has precedent for bundling exactly
this kind of convenience corollary with a normal-form structure
(`Module.Basis.SmithNormalForm.toAddSubgroup_index_eq_pow_mul_prod` in
Mathlib/LinearAlgebra/FreeModule/Int.lean). If/when `HermiteNormalForm` is upstreamed,
a companion index lemma could ride along — but reviewers would likely prefer the form
that genuinely *uses* HNF-ness, `index = ∏ i, (h.matrix i i).natAbs` (index = product
of pivots, via triangularity `det = ∏ diag`), with the |det| version as the one-rw
bridge. That is a question for the future structure PR, not for this declaration today.

**WHY not (refactor-actionable detail):**
Mathlib has the building blocks; the form is a 1-`rw`, 3-lemma composition.

Mathlib building blocks:
- `AddSubgroup.index_eq_natAbs_det` — Mathlib/LinearAlgebra/FreeModule/Finite/CardQuotient.lean:98
- `Module.Basis.det_apply` — Mathlib/LinearAlgebra/Determinant.lean
- `LinearMap.toMatrix_eq_basisToMatrix` — Mathlib/LinearAlgebra/Matrix/Basis.lean (HEAD only; not in the 2026-05-28 pin)

Composition sketch (verified compiling; see Phase 6):
```lean
example : N.toAddSubgroup.index = h.matrix.det.natAbs := by
  rw [AddSubgroup.index_eq_natAbs_det bM N.toAddSubgroup h.bN, Basis.det_apply,
    show bM.toMatrix (fun x => ((h.bN x : M))) = h.matrix from
      (LinearMap.toMatrix_eq_basisToMatrix h.bN bM N.subtype).symm.trans h.toMatrix_eq]
```

Belongs-elsewhere check: keep **project-local** (XYin/PhD/Cox/HermiteNormalForm.lean)
as convenience API for the HNF bundle — it has 3 real call sites and mirrors mathlib's
own SNF-bundle pattern; it is not mathlib material on its own.

Call sites in our project (from Phase 6.0): K = 3
Refactor plan (if inlining is preferred over keeping the local wrapper):
- `CyclicSublattice.lean:391`: replace `S.hermiteNormalForm.index_eq_natAbs_det.symm`
  with the composition above applied to `S.hermiteNormalForm`, `.symm`-ed.
- `CyclicSublattice/Classification.lean:40`: same, `.symm`-ed, for the local `h`.
- `CyclicSublattice/Classification.lean:162`: same, forward direction.
(Not recommended: the wrapper is cheaper than three inlined compositions; the NO
verdict concerns mathlib-worthiness, not local hygiene. After the next mathlib bump,
shrink the local proof to the 1-`rw` composition.)

Next action: do NOT propose this declaration for mathlib. Keep it as project-local
bundle API. Fold the "index = ∏ pivots vs |det|" statement-design question into the
eventual `HermiteNormalForm`-structure upstreaming plan (the file-level candidate),
and after bumping mathlib past `LinearMap.toMatrix_eq_basisToMatrix`, golf the local
proof to the verified one-liner.
