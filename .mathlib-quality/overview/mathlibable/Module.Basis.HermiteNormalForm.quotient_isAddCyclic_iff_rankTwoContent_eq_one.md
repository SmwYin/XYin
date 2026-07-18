# /mathlibable report — `Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`

Date: 2026-07-18. Mathlib pin: 2026-05-28 (`2abc2425`). Mode A, full exhaustive protocol.

---

### Baseline (Phase 0)

- lake build:               ✓ clean ("Build completed successfully (3909 jobs)")
- decl:                      ✓ resolved at `XYin/PhD/Cox/HermiteNormalForm.lean:414`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Hermite-normal-form API for full-rank rank-two ℤ-submodules (Cox Ch. 11); HNF is basis-relative, unlike Smith normal form.

---

### Statement (Phase 1)

`Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one` is a theorem stating:

Let M be a free ℤ-module with a fixed basis bM indexed by Fin 2, N ≤ M a submodule, and
h a Hermite-normal-form structure for N relative to bM (bundling a basis bN of N, the 2×2
integer inclusion matrix A = [N.subtype]_{bN→bM}, and the property that A is in column HNF).
Then the quotient group M/N is cyclic (as an additive group) if and only if the gcd of the
four entries of A equals 1. This is Cox, *Primes of the Form x²+ny²*, Exercise 11.16: a
sublattice N ⊆ M has cyclic quotient iff its inclusion matrix is primitive.

Variables / typeclasses (Lean side):
- `M : Type*`, `[AddCommGroup M]` — the ambient rank-2 ℤ-module
- `bM : Basis (Fin 2) ℤ M` (implicit) — fixed ambient basis
- `N : Submodule ℤ M` (implicit) — the sublattice
- `h : HermiteNormalForm bM N` — project-local bundle (bN, matrix, toMatrix_eq, isColumnHermiteNormalForm)

Hypotheses: none beyond the bundle `h`.

Conclusion (math): M/N is a cyclic abelian group ⟺ gcd of the entries of the HNF inclusion matrix is 1.

Conclusion (Lean): `IsAddCyclic (M ⧸ N) ↔ Matrix.rankTwoContent h.matrix = 1`

**Structural note.** The proof body is 2 lines: `simpa only [h.toMatrix_eq] using
quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one bM N h.bN`. The full mathematical
content lives in the sibling `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one`
(same file, line 363), which is basis-free (any bN, no HNF property needed) and is proved
in ~50 lines via mathlib's Smith normal form (`Submodule.smithNormalFormTopBasis/BotBasis/
Coeffs`, `Submodule.quotientEquivPiZMod`), content-invariance under unimodular multiplication
(project-local `rankTwoContent_dvd_mul_left/right`), `RingEquiv.piFinTwo`,
`AddGroup.isAddCyclic_prod_iff`, and `Nat.coprime_iff_gcd_eq_one`. The target decl is a
glue/dot-notation convenience over the sibling; its verdict is coupled to the sibling's and
to the two project-local defs it mentions (`HermiteNormalForm`, `Matrix.rankTwoContent`).

---

### Size classification (Phase 2a)

Verdict: BIG
Reason: it formalises a named-source main result of the file (Cox Ex. 11.16, the cyclicity
criterion driving the whole `CyclicSublattice` development), even though the decl itself is
a wrapper. (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 2 (single `simpa … using …`)
One-liner verdict: n/a — kind is theorem (the one-liner gate applies to `def`/`abbrev`/
`structure`). Noted for Phase 7: as a theorem it is glue over the project sibling.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|----------------------|-------|
|  1 | WebSearch (specific form)        | quotient Z^2 by sublattice cyclic iff gcd of matrix entries 1         | yes  | r = gcd of generator entries governs the cyclic part of ℤ²/Λ | arXiv 1506.02830 (cyclic coverings of the torus); "Enumeration of integer lattices by quotient group" (Morfismos 21); Fukshansky WR-sublattices |
|  2 | WebSearch (general form)         | determinantal divisors Smith normal form cyclic quotient invariant factors gcd of minors | yes  | dₖ = Δₖ/Δₖ₋₁ with Δₖ = gcd of k×k minors; coker ≅ ⊕ R/(sᵢ), s₁∣s₂∣… | Stanley "SNF in Combinatorics" survey; NIST "On the Smith normal form"; Wikipedia SNF |
|  3 | WebSearch (aliases)              | "first determinantal divisor" matrix content gcd entries "Smith normal form" d1 | yes  | d₁ = gcd of all entries = first determinantal divisor = matrix content | Kaltofen–Krishnamoorthy; Sin "SNF of incidence matrices"; the alias set is {content, d₁, first invariant factor} |
|  4 | ChatGPT MCP (gpt-5.4)            | standard name/form + generality + right mathlib formulation           | yes  | ℤⁿ/Aℤⁿ cyclic ⟺ d_{n−1}(A)=1 ⟺ s₁,…,s_{n−1} units; rank-2 case is d₁ = d_{n−1} coincidence | Confirms: PID is the classical level; determinantal ideals/Fitting ideals beyond PIDs; recommends Smith-coefficient formulation for mathlib ("cyclic iff all but at most one Smith coeff is a unit", because mathlib's `smithNormalFormCoeffs` has no ordered divisibility chain); rank-2 gcd form as downstream corollary once minors/content theory exists. Reference: Newman, *Integral Matrices* (equivalence/SNF/determinantal-divisor chapters; edition-dependent numbering) |
|  5 | Local references                 | `.mathlib-quality/overview/analysis/step4-lattice.md`, `step6-generalization.md` (no `references/` PDF dir — recorded) | yes  | step6 §A4: content = D₁(A); n×n criterion is via D_{n−1}, NOT D₁ ("a naive content = 1 ⇒ cyclic is false for n ≥ 3"); Newman Thm II.9 cited | Prior mathlib audit (step4 line 123) already verified the decl's mathlib composition is optimal and "no shortcut exists in mathlib" |
|  6 | nLab                             | Smith normal form / invariant factor theorem                          | no   | (no dedicated nLab page surfaced; content covered by Wikipedia/Wstein/Grokipedia hits) | Concept is classical module theory; nLab's angle would be via f.g. modules over PIDs — no cleaner abstract form found than #2/#4 |
|  7 | nCatLab (if categorical)         | n/a — not a categorical concept (finitely generated ℤ-module structure theory; the categorical generalisation is Fitting ideals, noted in #4) | n/a  | — | — |
|  8 | Stacks Project (if alg geom)     | n/a — not an algebraic-geometry concept; Stacks' SNF appearances (Tag 0ASP area) are incidental to modules-over-PID prerequisites, no cyclicity criterion | n/a  | — | — |
|  9 | MathOverflow / Math.SE           | when is Z^n / A Z^n cyclic gcd minors determinantal divisor           | partial | k-th determinantal divisor = gcd of k×k minors; quotient structure from invariant factors | No single canonical MSE thread surfaced by search, but the standard-form facts were reconfirmed via the aggregated results |
| 10 | recent arXiv (last 5 years)      | (via #1–#3 result sets)                                               | yes  | arXiv 2209.11441 (torsion points, uses d_{n−1} criteria), arXiv 1910.12502 (SNF and determinantal ideals), arXiv 2505.00484 (zeta functions of quadratic lattices); also arXiv 1601.07472: Coq formalisation of elementary divisor rings (formal-library precedent: SNF over EDRs, no cyclicity-criterion lemma either) | Current research states the criterion via SNF/determinantal ideals, never via gcd-of-entries except in rank 2 |

### Literature summary (Phase 3)

Concept identified as: **cyclicity criterion for the cokernel of an integer matrix**, an
instance of the invariant-factor/Smith-normal-form theorem; the rank-2 gcd-of-entries form
is Cox Ex. 11.16, and the gcd of entries is the **first determinantal divisor d₁(A)**
(alias: matrix content).

Sources agree on the standard form: yes.
Most general standard form: for A ∈ Mₙ(R), R a PID, det A ≠ 0: Rⁿ/ARⁿ ≅ ⊕ᵢ R/(sᵢ) with
invariant factors s₁ ∣ … ∣ sₙ, sₖ = dₖ/dₖ₋₁ (dₖ = gcd of k×k minors); the quotient is a
cyclic R-module ⟺ s₁, …, s_{n−1} are units ⟺ d_{n−1}(A) is a unit. Beyond PIDs the right
objects are determinantal/Fitting ideals, not gcds.

Generality dimensions where the literature varies:
- ring: ℤ → PID → elementary divisor domain → (Fitting ideals over any commutative ring)
- rank: 2 → n; **the gcd-of-entries (d₁) form is correct ONLY for n = 2** (d₁ = d_{n−1}
  coincidence); for n ≥ 3 the naive generalisation via d₁ is FALSE
- formulation: determinantal divisors (classical, Newman) vs Smith/invariant factors
  (modern, and what formal libraries produce)

Disagreement with the literature: none on truth; the user's form is the rank-2
specialisation, and the literature-standard general form uses different data (d_{n−1} or
Smith coefficients) that mathlib does not currently expose.

---

### Generality analysis — Phase 4a

Literature-standard form (from Phase 3): over a PID, M free of finite rank n, N ≤ M of
full rank: M/N is a cyclic module ⟺ all but at most one invariant factor is a unit
(⟺ d_{n−1}(inclusion matrix) is a unit).

| # | Parameter / hypothesis                | Current Lean form              | Literature-standard form           | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|--------------------------------|-------------------------------------|---------------------|----------------------------------|
| 1 | index type `Fin 2`                    | rank 2                         | arbitrary finite rank n             | NO (not mechanically) | `Matrix.rankTwoContent` is only defined for `Fin 2`, and the gcd-of-entries criterion is **false** for n ≥ 3; the general statement needs d_{n−1} (gcds of (n−1)-minors) or Smith coefficients — new machinery, new RHS, not a binder change |
| 2 | ring ℤ                                | ℤ, `IsAddCyclic`               | PID R, cyclic R-module              | NO (not mechanically) | `IsAddCyclic` and `ZMod`/`quotientEquivPiZMod` are ℤ-specific; the PID version replaces the conclusion by "quotient is a principal/cyclic R-module" — a restatement, not a weakening |
| 3 | `h : HermiteNormalForm bM N`          | project-local HNF bundle       | any inclusion matrix (no HNF needed) | YES — and the project already has it | the sibling `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` (same file, line 363) is exactly the HNF-free form, already stated and proved; the target decl is its dot-notation corollary. The HNF property is never used in the proof |
| 4 | `[AddCommGroup M]` + basis            | free rank-2 ℤ-module           | same                                | no                  | matches literature |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL within its own statement shape** — no proposed
hypothesis-weakening is even statable without changing the meaning of the RHS
(`rankTwoContent` forces `Fin 2`; `IsAddCyclic` forces ℤ), so there is nothing to
compile-verify; the literature-standard general form (rank n / PID / d_{n−1} or Smith
coefficients) is **STRICTLY MORE GENERAL BUT NOT MECHANICALLY REACHABLE** — it is a
restatement against different data requiring new API (see 4c), i.e. verdict-gate
false-positive class 5 ("real but not a single mechanical edit").

Number of weakening opportunities found: 1 mechanical (row 3: drop the HNF bundle — but
that lemma already exists in the file as the sibling; the target decl is deliberate
convenience glue), 0 further.

Cost of the true generalisation: EXPENSIVE (new mathlib API: finite-product cyclicity
criterion, matrix content / determinantal divisors; does not downgrade any verdict, but
it is a scoping decision — see Phase 7 questions).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | typeclasses instead of bundled hypotheses | no | the `HermiteNormalForm` bundle is data (a chosen basis + matrix), correctly a structure, not a class | — |
| 2 | filters/nets instead of sequences | no | finite algebra; no topology | — |
| 3 | universal property instead of construction | no | the statement is a criterion, not a construction | — |
| 4 | bundled substructure instead of set-with-predicate | no | already uses `Submodule` | — |
| 5 | typeclass-hierarchy weakening (ℤ → PID) | **yes** | over a PID R: `M ⧸ N` is a cyclic R-module ⟺ all but at most one `Submodule.smithNormalFormCoeffs b h i` is a unit; over ℤ specialise to `IsAddCyclic` via `quotientEquivPiZMod` | composes with `Submodule.quotientEquivPiSpan` (PID), `Ideal.quotientEquivPiSpan`; number-field applications (cyclicity of O_K/I) |
| 6 | higher-categorical generalisation | no | none relevant (Fitting-ideal language is a different development, not a mathlib direction here) | — |
| 7 | concrete index generalisation | **yes** (same as Q5) | index `Fin 2` → arbitrary `Finite ι`, with RHS "at most one non-unit Smith coefficient"; requires the missing lemma `isAddCyclic_pi_iff` (finite product of cyclic groups is cyclic iff pairwise coprime cards) — mathlib has only the binary `AddGroup.isAddCyclic_prod_iff` | unifies rank-2/rank-n; the rank-2 gcd corollary then follows from content-invariance |
| 8 | concrete-via-abstract (proof-body diagnostic) | **yes** | Diagnostic run: the target decl's 2-line proof never uses `h.isColumnHermiteNormalForm` — after `simpa only [h.toMatrix_eq]` the argument is entirely about an arbitrary basis matrix. The abstract form is the sibling `_toMatrix_` theorem (already in the file); the deeper abstract form is the Smith-coefficient criterion, of which the sibling's ~50-line proof is a specialisation-plus-content-bridge | the Smith-coefficient criterion + a separate "content = gcd of Smith coeffs in rank 2" lemma make the Cox form a one-line corollary |
| 9 | false-generalisation guard | no false generalisation | the Smith-coefficient restatement is the *same* mathematical object (invariant-factor criterion); the rank-n gcd-of-entries "generalisation" WOULD be a false generalisation (false for n ≥ 3) and is rejected — the correct target is Smith coefficients / d_{n−1} | prevents the known trap documented in step6 §A4 |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — the Smith-coefficient criterion
`IsAddCyclic (M ⧸ N) ↔ ∀ᶠ-free: at most one i with (smithNormalFormCoeffs b h i).natAbs ≠ 1`
(over ℤ; PID version with `IsUnit`), with the rank-2 gcd form as corollary.
- Cost: EXPENSIVE (needs `isAddCyclic_pi_iff` for finite products — absent from mathlib —
  plus, for the corollary, matrix content over a GCD monoid with unimodular invariance).
- Mathlib downstream: `Submodule.quotientEquivPiZMod` / `quotientEquivPiSpan` /
  `Ideal.quotientEquivPiSpan` consumers get a cyclicity API; number-theoretic cyclicity
  statements (O_K/I cyclic) compose directly.
- Real mathematical improvement: eliminates the rank-2/gcd coincidence from the primary
  statement and states the criterion against the data mathlib's SNF actually produces.
- Honesty note: whether to do this EXPENSIVE development now is a scoping judgment → Phase 7.

---

### Proof strategy — Phase 4.6

| # | Question | Applies? | Idiomatic alternative | Cost of switch |
|---|----------|----------|------------------------|----------------|
| 1 | ε-δ vs filters | no — no topology | — | — |
| 2 | element-wise vs ideal/submodule abstraction | no — the sibling's proof already argues via basis-change matrices and equivs, not elements | — | — |
| 3 | sequences vs nets | no | — | — |
| 4 | construction vs universal property | no | — | — |
| 5 | helper lemmas mathlib SHOULD have | **yes** | (a) `isAddCyclic_pi_iff` (finite products; mathlib has only binary `AddGroup.isAddCyclic_prod_iff`, forcing the `RingEquiv.piFinTwo` detour); (b) matrix content + invariance under unimodular multiplication (the file's private `rankTwoContent_dvd_mul_left/right`) | file as follow-up dev-tickets / PRs |

### Proof strategy verdict (Phase 4.6)

Current strategy: MATHLIB-IDIOMATIC (verified independently by step4-lattice.md line 123:
the SNF-composition route "correctly composes … No shortcut exists in mathlib").
Missing-API notes (a), (b) recorded for the follow-up.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is theorem.

---

### Mathlib search-status: `quotient_isAddCyclic_iff_rankTwoContent_eq_one` (Phase 5)

[A] Lean-Finder    "determinantal divisor of a matrix, gcd of all entries of an integer matrix, invariant factors from minors" → **no hits** (nearest: `Matrix.den` = lcm of ℚ-entry denominators — unrelated)
[B] Loogle         `IsAddCyclic (_ ⧸ _)` → only `isAddCommutative_of_isAddCyclic_quotient_center_self` (unrelated); `Matrix (Fin 2) (Fin 2) ℤ, Nat.gcd` → **empty**
[C] LeanSearch     "quotient of free module by submodule is cyclic iff gcd condition on matrix" → only the building blocks `Submodule.quotientEquivPiZMod`, `quotientEquivPiSpan`, `quotientEquivDirectSum` — no cyclicity criterion
[D] Grep mathlib   `determinantal|hermite normal|matrix.*content` over LinearAlgebra/Data/Matrix/RingTheory → **zero files** (only Hermite *polynomials* under RingTheory/Polynomial/Hermite); `isAddCyclic_prod_iff` exists only in binary form (GroupTheory/SpecificGroups/Cyclic.lean:812); `smithNormalFormCoeffs` appears only in FreeModule/{PID, Finite/Quotient, Finite/CardQuotient} with no cyclicity lemma; `Finset.gcd` unused in LinearAlgebra/Data/Matrix
[E] Name pattern   `lean_local_search "smithNormalFormCoeffs"` → only `Submodule.smithNormalFormCoeffs`, `…_ne_zero` (no `_dvd`, no divisibility chain, no cyclicity); `rankTwoContent` → project-only

Searched for both:
- the user's current form (rank-2 gcd-of-entries criterion) — not in mathlib
- the literature-standard forms (determinantal divisors; "all but one invariant factor a
  unit"; matrix content) — none in mathlib; mathlib's SNF API stops at the quotient
  decomposition `quotientEquivPiZMod` and never states a cyclicity criterion

Concluded: **"found building blocks (`Submodule.smithNormalFormTopBasis/BotBasis/Coeffs`,
`Submodule.quotientEquivPiZMod`, `RingEquiv.piFinTwo`, `AddGroup.isAddCyclic_prod_iff`,
`Nat.coprime_iff_gcd_eq_one`); composition would NOT yield our form in ≤3 calls (see
Phase 6); not in mathlib in either the user's or the literature-standard form (all 5
methods exhausted)"**

---

### Normal-form check — Phase 5.5a

Equivalent formalisms: (i) `IsAddCyclic (M ⧸ N)` ↔ content = 1 (current); (ii) via
`AddSubgroup.index`/exponent equality (cyclic ⟺ exponent = card); (iii) via existence of
a generator; (iv) Smith-coefficient form.
Does mathlib have a canonical form? yes — `IsAddCyclic` is the canonical cyclicity
predicate. Our statement is stated against it: OK.
RHS convention: the equation `rankTwoContent h.matrix = 1` on the RHS of the iff is the
computable/checkable side — respected (matches `Nat.coprime_iff_gcd_eq_one` style).

### Syntactic generality — Phase 5.5b

Alternative restatements attempted:
- `(h : HermiteNormalForm bM N) : IsAddCyclic (M ⧸ N) ↔ h.matrix.rankTwoContent = 1` (current)
- basis-free: `(bN : Basis (Fin 2) ℤ N) : IsAddCyclic (M ⧸ N) ↔ (toMatrix bN bM N.subtype).rankTwoContent = 1` — **already exists as the sibling** (line 363)
Chosen restatement: keep both — the sibling is the easy-to-apply general form; the target
decl is the dot-notation form call sites actually use (`h.quotient_….mp S.cyclic`).
Justification: 3 of the 4 project call sites go through the bundle `h`; supplying `h.bN`
manually at each site is strictly noisier.

### Superfluous-argument audit — Phase 5.5c

| # | Argument / typeclass | Essentially used? | Notes |
|---|----------------------|-------------------|-------|
| 1 | `h.isColumnHermiteNormalForm` (inside the bundle) | **no** | the conclusion holds for ANY basis matrix (the sibling proves it); the HNF field rides along only because `h` is the bundle. Acceptable for a convenience corollary; would be superfluous in a mathlib primary statement |
| 2 | `h.toMatrix_eq`, `h.bN`, `h.matrix` | yes | the actual data the proof transports along |
| 3 | `[AddCommGroup M]`, `bM` | yes | freeness/rank via the basis |

### Statement-shape verdict (Phase 5.5)

Normal form: OK. Syntactic generality: OK (paired with the sibling). Superfluous
arguments: none removable without dissolving the bundle (and the HNF-free form already
exists as the sibling).
Overall: SHIP-AS-STATED **within the project**; for mathlib the primary statement should
be the Smith-coefficient criterion (Phase 4c), with this as downstream corollary.

---

### Call sites — `quotient_isAddCyclic_iff_rankTwoContent_eq_one` (Phase 6.0)

Internal use count: **3** (excluding the declaring file); external-to-file callers: 2 files.

| Caller file:line | Usage pattern |
|---|---|
| XYin/PhD/Cox/CyclicSublattice.lean:590 | `S.hermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one.mp S.cyclic` |
| XYin/PhD/Cox/CyclicSublattice/Classification.lean:48 | `h.quotient_isAddCyclic_iff_rankTwoContent_eq_one.mp S.cyclic` |
| XYin/PhD/Cox/CyclicSublattice/Classification.lean:165 | `h.quotient_isAddCyclic_iff_rankTwoContent_eq_one.mpr` |

(The sibling `_toMatrix_` form is additionally used directly at CyclicSublattice.lean:598.)

Inline-derivation grep (equivalent re-derived elsewhere without the lemma): (none) — all
`IsAddCyclic`-consuming sites route through this lemma or the sibling.

Signal: K = 3 ≥ 3 across 2 files, no inline re-derivation → real API with consumers
(YES-leaning composability signal).

### Composition check (Phase 6)

Can the statement be derived from mathlib in ≤3 chained calls?

Attempt 1 (SNF route): `(N.quotientEquivPiZMod bM hRank).isAddCyclic` +
`RingEquiv.piFinTwo` + `AddGroup.isAddCyclic_prod_iff` + `Nat.coprime_iff_gcd_eq_one`
reduces `IsAddCyclic (M ⧸ N)` to `Nat.Coprime (c 0).natAbs (c 1).natAbs` for the Smith
coefficients c.
  - Result: **partial** — this is already 4 calls and lands at a statement about Smith
    coefficients, NOT about `rankTwoContent h.matrix`. The bridge
    `rankTwoContent A = gcd (c 0).natAbs (c 1).natAbs` requires content-invariance under
    unimodular multiplication (`rankTwoContent_dvd_mul_left/right` + the double-divisibility
    argument hDA/hAD via `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`) —
    ~30 further lines of real proof; mathlib has no matrix-content API at all.

Attempt 2 (index/exponent route): cyclic ⟺ exponent = card = |det| — no mathlib lemma
chain produces gcd-of-entries from this either; dead end.

Conclusion: **NOT-COMPOSABLE** (the multiple-`have`s-with-real-reasoning pattern; per the
composition heuristics table this is "a proof, not a composition"). Independently
confirmed by step4-lattice.md line 123: "No shortcut exists in mathlib."

---

## Verdict: `Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): standard form identified — invariant-factor cyclicity
  criterion; user's form = rank-2 specialisation where d₁ = d_{n−1}; the naive rank-n
  gcd-of-entries generalisation is FALSE (Q9 guard).
- Generality analysis (Phase 4): MAXIMALLY GENERAL within its statement shape; the
  literature/modern-idiom general form (Smith-coefficient criterion, rank n, PID) is
  strictly more general but NOT mechanically reachable — new RHS data + missing mathlib
  API (`isAddCyclic_pi_iff`, matrix content). Verdict-gate false-positive class 5.
- Mathlib search (Phase 5): not in mathlib in any form; building blocks only; no matrix
  content, no determinantal divisors, no HNF, no finite-product cyclicity criterion.
- Composition check (Phase 6): NOT-COMPOSABLE (content-invariance bridge is a real proof);
  K = 3 call sites in 2 files, genuine project API.

**Rationale:**

The mathematical content (Cox Ex. 11.16) is genuinely missing from mathlib and is not a
composition of mathlib primitives — mathlib's Smith normal form API stops at the quotient
decomposition and states no cyclicity criterion whatsoever, and mathlib has neither matrix
content nor determinantal divisors nor Hermite normal form. So the NO buckets are ruled
out. But a YES verdict cannot be self-resolved either, for three linked reasons. (1) The
declaration is stated against two project-local objects mathlib lacks
(`Module.Basis.HermiteNormalForm`, `Matrix.rankTwoContent`), so it cannot ship alone: it
ships with (and after) the HNF-structure and content-def decisions, which prior project
analysis (step6 §A1/A4) grades High/Med-High difficulty for the mathlib-right n×n forms.
(2) The literature- and mathlib-idiomatic primary statement is the Smith-coefficient
criterion ("M ⧸ N is cyclic iff all but at most one Smith coefficient is a unit", any
finite rank, PID-ready) — an EXPENSIVE restatement, not a mechanical weakening, requiring
the also-missing `isAddCyclic_pi_iff`; per the skill's own routing (false-positive class 5
and verdicts-reference: "if the mechanical weakening isn't reachable, that's a BORDERLINE
call — is the more general form worth the work?"), this is a scoping question for the
user, not a verdict the skill may pick alone. (3) The rank-2 gcd form is a mathematically
attractive corollary but must NOT be shipped as the general-looking primary form, since
its naive generalisation is false for n ≥ 3.

**Numbered questions (≤5):**

1. Scope: are you willing to develop the mathlib-primary form — the Smith-coefficient
   cyclicity criterion `IsAddCyclic (M ⧸ N) ↔ (at most one i with
   ¬IsUnit (smithNormalFormCoeffs b h i))` for arbitrary `Finite ι` over ℤ (PID variant
   alongside) — plus the missing `isAddCyclic_pi_iff` (finite product of additive groups
   is cyclic iff each factor is cyclic with pairwise coprime cards)? This is the form
   ChatGPT-MCP and the literature both point at, and it needs no HNF and no matrix
   content. (yes/no)
2. If yes to 1: should the rank-2 gcd-of-entries corollary also go to mathlib, which
   additionally requires upstreaming a matrix-content definition (as `Finset.gcd` over
   entries, per step4's refactor recommendation) with its unimodular-invariance lemmas —
   or should the gcd form stay project-local as the Cox-facing corollary? (mathlib /
   project-local)
3. Sequencing: this decl's statement mentions `Module.Basis.HermiteNormalForm`; do you
   intend to upstream the HNF development at all (step6 §A1 grades the mathlib-right n×n
   form High)? If not, this exact decl (the HNF-bundled wrapper) necessarily stays
   project-local regardless of 1–2, with only the basis-free sibling
   `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` (restated per 1–2) being
   upstream material. (yes/no)
4. Before any upstreaming: accept step6 §A4's documentation action now — rename/document
   `rankTwoContent` as the first determinantal divisor D₁ with an explicit warning that
   the correct n×n generalisation is via D_{n−1}, not D₁? (yes/no)

**Next action:** user answers the questions; re-run `/mathlibable` on the chosen primary
form (or commit directly: answering 1 = yes turns this into a `/develop` ticket for the
Smith-coefficient criterion + `isAddCyclic_pi_iff`, with this decl inheriting
"project-local corollary" status).
