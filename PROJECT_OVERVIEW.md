# Project Overview: `NumberField/FieldExamples`

Generated: 2026-06-15

> Full per-declaration inventories (every `def`/`lemma`/`theorem`/`instance` with
> What / How / Hypotheses / Uses-from-project / Used-by / Lines / Notes) live in
> [`.overview/`](.overview/): one file per case study —
> `CubeRootThree.md`, `CyclotomicEight.md`, `CyclotomicFive.md`, `CyclotomicThree.md`,
> `SqrtFive.md`, `SqrtNegSix.md`, `SqrtTwo.md`. This document is the **synthesis**:
> inventory summary + cross-file analysis + action plan.

---

## Executive Summary

`FieldExamples` is a library of **eight worked number-field case studies**, each computing the
full classical invariants of one field: degree, Galois group, signature, ring of integers,
discriminant, prime splitting, class number/group, unit group + regulator, Euclideanity, and
a local–global / adelic epilogue. The eight fields are three quadratic-by-`QuadraticAlgebra`
(`ℚ(√2)`, `ℚ(√5)`, `ℚ(√−6)`), two quadratic-by-cyclotomic (`ℚ(ζ₃)=ℚ(√−3)`, plus the
non-abelian-closure cubic `ℚ(∛3)`), and two higher cyclotomic (`ℚ(ζ₅)`, `ℚ(ζ₈)`). A single
shared file `Common.lean` (10 helpers) holds the genuinely field-agnostic lemmas.

The folders are deliberately **structurally parallel**: the same ten file names recur
(`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting → ClassGroup
→ Units → Euclidean → LocalGlobal`), with special-topic add-ons (`CMField`, `Subfields`,
`QuadraticSubfield`, `UniqueFactorization`). This parallelism is the project's defining
feature — and the source of its single biggest issue. **The headline finding is pervasive
cross-twin duplication of generic machinery that should live in `Common.lean`** (or, in two
cases, in mathlib). The most acute instance is the *Kummer–Dedekind reduction-mod-`p`
machinery* (`residueHom`, `ker_residueHom`, `residueHom_surjective`, `isMaximal_span_pair`,
`absNorm_span_pair`), reproduced near-verbatim in **6 files** and even copy-pasted across the
`PrimeSplitting → ClassGroup` import boundary inside one folder because it was marked
`private`.

The mathematics is in good shape: of ~1100 declarations only **11 `sorry`s** remain, and they
fall into exactly **two well-understood blocked classes** — (a) the *fundamental-unit/regulator*
results that need an Artin-type unit-index bound (`isFundamental` + `regulator_eq`), and
(b) three `normEuclidean` proofs needing a geometry-of-numbers covering argument. Two folders
(`CyclotomicThree`, `SqrtNegSix`) are entirely `sorry`-free because they have unit rank 0.
`SqrtTwo` and `SqrtFive` discharge the unit-generation step via the Pell/`Zsqrtd` route, so
only their `regulator_eq` remains. **No `set_option` workarounds anywhere** — a good sign.

**Top priorities:** (1) hoist the duplicated reduction-mod-`p` and Galois-automorphism
machinery into `Common.lean` as a minpoly-parametrized API; (2) de-`private` and de-duplicate
within folders (two exact-duplicate `private` lemmas, one cross-import copy-paste block of
~115 lines); (3) add the small generic helpers (`absNorm_span_natCast`,
`abs_norm_int_lt_of_remainder_eq`, a prime-card-cyclic-group wrapper) to `Common`; (4) remove
the handful of dead lemmas; (5) close the two `sorry` classes.

---

## Statistics

- **Files:** 78 (`Common.lean` + 7 case studies × ~11 files); **~20,700 lines**.
- **Declarations:** ~1,100 (≈ 230 defs/abbrevs, ≈ 800 lemmas/theorems, ≈ 40 instances,
  ≈ 60 anonymous `example` smoke-tests; 0 user `structure`/`class`).
- **`sorry`s:** 11, across 5 files, in 2 blocked classes (see below).
- **`set_option`:** 0.
- **Moral duplications found:** 9 cross-twin families + 2 exact within-folder duplicates.
- **Generalization opportunities:** 6.
- **Missing-API / hoist-to-Common items:** 10.
- **Junk / dead / removable:** ~8 declarations + ~60 demonstrative `example`s (intentional).

### The 11 `sorry`s (2 blocked classes, both expected)

| File | Declaration | Class | Why blocked |
|---|---|---|---|
| CubeRootThree/Units | `fundamentalUnitSystem_isFundamental` | unit-index | needs Artin-type bound that `θ²−2` generates mod torsion |
| CubeRootThree/Euclidean | `normEuclidean` | covering | geometry-of-numbers covering argument |
| CyclotomicEight/Units | `fundamentalUnitSystem_isFundamental` | unit-index | Artin-type cyclotomic-unit index |
| CyclotomicEight/Units | `regulator_eq` | unit-index | downstream of isFundamental |
| CyclotomicEight/Euclidean | `normEuclidean` | covering | covering argument |
| CyclotomicFive/Units | `fundamentalUnitSystem_isFundamental` | unit-index | `[𝓞ˣ : cyclotomic units] = h⁺ = 1` |
| CyclotomicFive/Units | `regulator_eq` | unit-index | identify abstract fund. unit with `1+ζ` |
| CyclotomicFive/Euclidean | `normEuclidean` | covering | covering argument |
| SqrtFive/Units | `fundamentalUnit_generates` | unit-index | bridge Pell-±4 / Fibonacci eqn to half-integral order `ℤ[(1+√5)/2]` |
| SqrtFive/Units | `regulator_eq` | unit-index | analytic fundamentality |
| SqrtTwo/Units | `regulator_eq` | unit-index | identify regulator with `log(1+√2)` |

`CyclotomicThree` and `SqrtNegSix` are **`sorry`-free** (unit rank 0 ⇒ `regulator_eq_one`
trivially, no fundamental unit to certify). Every `unitGroupStructure` is `sorry`-free even
in the blocked folders — it routes through mathlib's abstract `fundSystem`, not through the
sorried concrete-fundamental-unit lemma.

---

## Part 1: Declaration Inventory

Full inventories in [`.overview/`](.overview/). Headline public results per case study:

| Field | [K:ℚ] | Sig | 𝓞K | disc | h | Units | Splitting law | Euclidean |
|---|---|---|---|---|---|---|---|---|
| **SqrtTwo** `ℚ(√2)` | 2 | (2,0) | ℤ[√2] | 8 | 1 | μ₂×ℤ, fund `1+√2` | split ⇔ p≡±1 (8); 2 ram | yes |
| **SqrtFive** `ℚ(√5)` | 2 | (2,0) | ℤ[φ] | 5 | 1 | μ₂×ℤ, fund `φ` | split ⇔ p≡±1 (5); 5 ram | yes |
| **SqrtNegSix** `ℚ(√−6)` | 2 | (0,1) | ℤ[√−6] | −24 | **2** | μ₂ (rank 0) | split ⇔ p≡1,5,7,11 (24); 2,3 ram | **no** (not even PID) |
| **CyclotomicThree** `ℚ(ζ₃)` | 2 | (0,1) | ℤ[ζ₃] | −3 | μ₆ (rank 0) | split ⇔ p≡1 (3); 3 ram | yes |
| **CubeRootThree** `ℚ(∛3)` | 3 | (1,1) | ℤ[∛3] | −243 | 1 | μ₂×ℤ, fund `∛9−2` | cubic-residue law; 3 tot. ram | sorry |
| **CyclotomicFive** `ℚ(ζ₅)` | 4 | (0,2) | ℤ[ζ₅] | 125 | 1 | μ₁₀×ℤ, fund `1+ζ` | split ⇔ p≡1 (5); 5 ram (e=4) | sorry |
| **CyclotomicEight** `ℚ(ζ₈)` | 4 | (0,2) | ℤ[ζ₈] | 256 | 1 | μ₈×ℤ, fund `1+√2` | split ⇔ p≡1 (8); 2 ram (e=4) | sorry |

Special-topic files: `CyclotomicEight/Subfields` (the three quadratic subfields √2, i, √−2),
`CyclotomicFive/QuadraticSubfield` (Gauss sum ⇒ ℚ(√5) ⊂ ℚ(ζ₅)),
`CyclotomicEight/Five/Three` & `SqrtNegSix` `CMField` (CM structure),
`SqrtNegSix/UniqueFactorization` (`not_uniqueFactorizationMonoid`).

---

## Part 2: Cross-File Dependencies

Each folder imports **linearly**: `Basic → Galois → Embeddings → RingOfIntegers →
Discriminant → PrimeSplitting → ClassGroup → Units → Euclidean → LocalGlobal`. Special-topic
files hang off the late chain. All folders depend only on `Common.lean` and mathlib — **there
is no cross-folder dependency**, even between the two `…Three` fields and even between the two
real-quadratic `QuadraticAlgebra` fields. That independence is what forces the duplication
documented in Part 4: identical machinery is re-proved in each silo rather than shared.

`Common.lean` usage (files referencing each helper, excluding `Common` itself):

| Helper | # files |
|---|---|
| `not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ` | 7 |
| `not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow` | 7 |
| `eq_of_le_of_absNorm_eq` | 5 |
| `torsionPowerHom` | 5 |
| `rankOnePowerHom` | 5 |
| `eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq` | 3 |
| `left_eq_prime_of_mul_eq_prime_sq_of_ne_one` | 3 |
| `natAbs_lt_of_abs_ratCast_lt` | 3 |
| `exists_int_inverse_mod_prime` | 2 |
| `two_le_ramificationIdx…` / `ramificationIdx_ne_one…` | 0 (internal to the `not_isUnramified` wrapper) |

`Common` is genuinely shared and load-bearing — the problem is that **it is not big enough**:
the items in Part 4 are exactly the lemmas that *should* be in this table but aren't.

---

## Part 3: Mathlib API Audit

This is a case-study project: most "definitions" are concrete instantiations (the field `K`,
its generator, defining polynomial, integral basis), so there is little scope to "replace a
custom abstraction with a mathlib one" — the field models already sit on mathlib's
`QuadraticAlgebra`, `AdjoinRoot`, `IsCyclotomicExtension`, `PowerBasis`,
`HeightOneSpectrum`, `Algebra.norm`, `Ideal.absNorm`, `fundSystem`, etc. The API issues are
about **hand-rolled proof patterns** that duplicate mathlib (or `Common`) capability.

### 3a. Reduction mod `p` re-implements Kummer–Dedekind

The `residueHom`/`ker_residueHom`/`isMaximal_span_pair`/`absNorm_span_pair` block builds, by
hand, the reduction map `𝓞K → 𝓞K/P ≅ 𝔽_{p^f}` and its kernel from a power basis with known
minimal polynomial mod `p`. Mathlib has the **Kummer–Dedekind** theorem
(`Mathlib.RingTheory.DedekindDomain.KummerDedekind`:
`normalizedFactorsMapEquivNormalizedFactorsMinPolyMk`, and the `Ideal.factors_…` API) which
relates the prime factorization of `(p)` to the factorization of the minimal polynomial mod
`p` — exactly what these files reprove per-prime.
- **Action (investigate, medium difficulty):** assess whether the per-prime splitting facts
  can be derived from `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` instead of the
  bespoke `residueHom` machinery. Even if a full switch is too invasive, the machinery should
  be **hoisted to `Common` as one minpoly-parametrized API** (see Part 4.1).

### 3b. `absNorm (span {(p:𝓞K)}) = p^[K:ℚ]` re-derived per field

Stated as `absNorm_span_natCast` in 4 quadratic folders and re-derived inline elsewhere
(≥5× in `SqrtNegSix` alone). This is `Ideal.absNorm_span_singleton` composed with the
`finrank` of the order. **Action:** search mathlib for an existing
`absNorm_span_singleton_natCast`/`absNorm_span_intCast`; if absent, add one generic lemma to
`Common` parametrized by `finrank ℤ (𝓞K)`.

### 3c. `intNorm` of small integer constants re-derived inline

`SqrtNegSix` proves `Algebra.norm ℤ (2:𝓞K) = 4`, `… 3 = 9`, `… 5 = 25`, `… 13 = 169` inline
≥8 times, each via the same `intNorm_eq_normForm n 0; simp` ritual, even though private
`intNorm_two/three/five` exist. **Action:** one `intNorm_natCast` lemma
(`norm ℤ (n:𝓞K) = n^[K:ℚ]` for the quadratic case `= n²`), public, in `RingOfIntegers`.

### 3d. "Group of prime cardinality ≅ ℤ/p" boilerplate

The `Gal ≅ ℤ/2`, `Cl ≅ ℤ/2`, `𝓞ˣ_tors ≅ ℤ/2` proofs re-run the same
`isCyclic_of_prime_card` + `mulEquiv…ZMod` argument in `Galois`, `ClassGroup`, `Units`
across folders (found in 6 files). **Action:** a `Common` wrapper
`mulEquivZModOfCard (h : Nat.card G = p) : G ≃* Multiplicative (ZMod p)` (or reuse
`zmodEquivZPowers`/`isCyclic_of_card_eq_prime` directly).

### 3e. Genuinely good mathlib usage (no change)

`fundSystem` + `closure_fundSystem_sup_torsion_eq_top` for the unit group (keeps
`unitGroupStructure` `sorry`-free), `QuadraticAlgebra.lift`/`AdjoinRoot.liftAlgHom` for model
equivalences, `Polynomial.irreducible_of_degree_le_three_of_not_isRoot`, `PowerBasis.map`,
`HeightOneSpectrum`, `Pell.Solution₁`/`Zsqrtd` for `SqrtTwo` units — all appropriate.

---

## Part 4: Moral Duplications

Pairwise comparison of the recurring families (A = canonical/representative occurrence):

| Decl A | Decl B (… and N more) | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `residueHom` &c (CubeRootThree/PrimeSplitting) | same names in CyclEight, CyclFive, CyclThree, SqrtNegSix PrimeSplitting **+ CyclEight/ClassGroup** | yes, modulo minpoly | yes (verbatim mod the defining relation) | **HOIST to Common** (6 files) |
| `gen_eq_zetaInt`,`minpoly_gen_eq`,`residueHom_zetaInt`,`ker_residueHom`,`span_one_sub_zetaInt_eq_pair` (CyclEight/PrimeSplitting, `private`) | identical copies in CyclEight/ClassGroup (~115 lines, L72–186) | yes | yes (copy-paste across import barrier) | **DE-PRIVATE + dedupe now** |
| `sigmaTwo`/`sigmaThree`/`aut_eq` (Galois, public) | `sig2`/`sig3`/`autEq'` (PrimeSplitting, `private`) in CyclEight, CyclFive, CyclThree | yes | yes (same `fromZetaAut` proof) | **reuse public; delete private** |
| `absNorm_span_natCast` (SqrtNegSix, SqrtTwo, SqrtFive, CyclThree) | inline re-derivations in the other PrimeSplitting files | yes | yes | **HOIST to Common** |
| `abs_norm_int_lt_of_remainder_eq` (SqrtTwo, SqrtFive, CyclThree Euclidean) | each other | yes | yes (real/imag quad remainder bound) | **HOIST to Common** |
| `goldenIntO_sq` (SqrtFive/PrimeSplitting:117) | `goldenIntO_sq` (SqrtFive/Units:36) | **identical** | **identical** | **EXACT DUP — make one public lemma** |
| `zeta_pow_three` (CyclThree/PrimeSplitting:36) | `zeta_pow_three` (CyclThree/Units:34) | **identical** | **identical** | **EXACT DUP — make one public lemma** |
| `mulEquivOfPrimeCardEq`-style cyclic proof (Galois) | same in ClassGroup, Units (6 files) | yes (G of card p) | yes | **HOIST wrapper to Common** |
| `heightOne*` finite-place defs (LocalGlobal) | 21 defs across 7 LocalGlobal files | yes (asIdeal+isPrime+ne_bot) | yes | **HOIST `HeightOneSpectrum.ofAbsNormNeZero`** |
| `ringOfIntegersLinearMap`(+`_injective`) (CubeRootThree) | `ringOfIntegersLinearMap` (SqrtNegSix) &c | yes (𝓞K →ₗ[ℤ] K) | yes | **HOIST to Common** (fully field-free) |
| `exists_intCast_norm` / `algebraNorm_eq_quadraticNorm` | per-quadratic-twin copies | yes | yes | **HOIST** (quadratic-norm bridge) |
| `ramified_iff_eq_three`(CubeRootThree) ↔ `ramified_iff_eq_three`(CyclThree); `span_three_eq`; `prime_dvd_differentIdeal_iff_…` | the two `…Three` folders | yes, modulo relation `r³=3` vs `r²+r+1=0` | structurally yes | unify only if Common machinery (4.1) lands |

The last row records the strongest *mathematical* twinning: `CubeRootThree` and
`CyclotomicThree` share the entire `PrivateMachinery` block and several splitting theorems,
differing only by the defining relation. Full unification is gated on the Part 4.1 hoist.

---

## Part 5: Generalization Opportunities

1. **Reduction-mod-`p` machinery → minpoly-parametrized `Common` API** *(medium)*.
   `residueHom`/`ker_residueHom`/`isMaximal_span_pair`/`absNorm_span_pair` only need: a monic
   `minpoly` of the power-basis generator, and its reduction mod `p`. Parametrize over
   `(pb : PowerBasis ℤ (𝓞K))` (or the integral basis) and the prime `p`. Standard generality
   in the literature is exactly Kummer–Dedekind (Neukirch I.8.3). Collapses 6 copies.

2. **`absNorm_span_natCast` → `Common` for any order** *(low)*.
   `absNorm (span {(n:𝓞K)}) = n ^ finrank ℤ (𝓞K)` needs no field data. Generalizes from the
   quadratic `n²` to all degrees, covering the cubic and cyclotomic folders too.

3. **`abs_norm_int_lt_of_remainder_eq` → `Common`** *(low)*.
   The "remainder has strictly smaller norm" step of a norm-Euclidean argument is generic for
   any quadratic order given the `|N(e)| ≤ 1/2`(ish) bound on the fractional remainder.

4. **`heightOne*` place constructor → `Common`** *(low)*.
   `HeightOneSpectrum.ofAbsNormNeZero (P) (hP : P.IsPrime) (h : absNorm P ≠ 0)` bundling
   `asIdeal := P`, `isPrime`, `ne_bot` (via `absNorm`-nonzero ⇒ `≠ ⊥`). Removes 21 boilerplate
   defs.

5. **`ringOfIntegersLinearMap` / quadratic-norm bridge → `Common`** *(low)*.
   `(𝓞K →ₗ[ℤ] K)` is `(Algebra.linearMap _ _).restrictScalars ℤ` for any number field;
   `algebraNorm_eq_quadraticNorm` is a pure `QuadraticAlgebra` fact.

6. **Prime-card cyclic-group wrapper → `Common`** *(low)*.
   `Nat.card G = p ⇒ G ≃* Multiplicative (ZMod p)`; used for Galois, class, and torsion
   groups alike.

---

## Part 6: API Improvements

### Missing lemmas (would simplify many proofs)
1. **`Common.residue` API** (Part 5.1) — the single highest-impact addition; un-blocks
   deduplication of 6 PrimeSplitting files and the CyclotomicEight ClassGroup copy-paste.
2. **`Common.absNorm_span_natCast`** — replaces ≥4 named + ≥5 inline copies.
3. **`Common.abs_norm_int_lt_of_remainder_eq`** — 3 Euclidean files.
4. **`Common.mulEquivZModOfCard`** — 6 group-structure proofs.
5. **`Common.heightOneOfAbsNormNeZero`** — 21 LocalGlobal defs.
6. **`RingOfIntegers.intNorm_natCast`** (per field, or generic in Common) — ≥8 inline
   `norm ℤ (n:𝓞K)` derivations in SqrtNegSix alone.

### Visibility / structure fixes
7. **De-`private`** the reduction machinery and the `*_sq`/`zeta_pow_three` generator
   relations so siblings can reuse them instead of re-declaring (this is the direct cause of
   the two exact duplicates and the 115-line cross-import copy-paste).
8. **Move misplaced lemmas to their natural home**: `ClassGroup.thetaInt_ne_zero` (SqrtNegSix)
   belongs in `RingOfIntegers` next to `thetaInt`; `realEmb` (SqrtFive/Units) duplicates
   `exists_realEmbedding_goldenRatio` (Embeddings).

### Completeness
9. The `cubePolynomial_ne_zero` lemma (CubeRootThree) exists but the inline
   `by intro h; simpa using congrArg natDegree h` is copy-pasted ~7× instead — finish wiring
   the lemma in. Same pattern for the repeated inline `finrank ℤ (𝓞K) = d` re-proofs in the
   cyclotomic PrimeSplitting files (extract one named `finrank_ringOfIntegers` per field).

---

## Part 7: Junk / Removable

1. **`goldenIntO_sq`** — duplicate definition (SqrtFive `PrimeSplitting:117` **and**
   `Units:36`). Keep one, make public, in `RingOfIntegers`.
2. **`zeta_pow_three`** — duplicate `private` definition (CyclThree `PrimeSplitting:36` **and**
   `Units:34`). Same fix.
3. **`orderOf_unitOfCoprime_five_eq_four_iff`** (CyclotomicFive/PrimeSplitting, ~94 lines) —
   **unused**. Either wire into the splitting law or delete.
4. **`zetaFivePolynomialMod_eq_cyclotomic`** (CyclotomicFive) — **unused**.
5. **`intNorm_eq`** (CyclotomicThree/PrimeSplitting:86) — **unused**.
6. **CyclotomicThree dead Kummer–Dedekind helpers**:
   `zetaThreePolynomialMod_eq_cyclotomic`,
   `orderOf_unitOfCoprime_eq_{one,two}_of_mod_three_eq_*`,
   `not_dvd_three_of_prime_ne_three` (L778–829) — no consumer.
7. **Empty `Discriminant.lean`** in SqrtFive, SqrtNegSix, SqrtTwo (the discriminant result
   lives in `RingOfIntegers`); and the empty trailing `Regulator` section in
   CyclotomicThree/Units. Remove the empty skeletons or fold the header note elsewhere.
8. **Demonstrative `example`s** (~60 total, mostly LocalGlobal + a few Discriminant/RingOf-
   Integers) — *intentional smoke-tests*, not junk, but worth a one-line comment marking them
   as such so they aren't mistaken for load-bearing API. The Basic-file alternative-presentation
   blocks (SqrtTwo `KUnitModel`, SqrtFive radical model, CyclThree √−3 identifications) are
   likewise pedagogical and unused downstream — keep, but document as "presentation only".

---

## Recommended Action Plan

### Priority 1 — Quick wins (mechanical, do now)
- Delete the two exact-duplicate `private` lemmas (`goldenIntO_sq`, `zeta_pow_three`); promote
  one copy each to a public `RingOfIntegers` lemma.
- Delete the ~5 confirmed-dead lemmas (Part 7.3–7.6).
- Remove empty `Discriminant.lean` skeletons / empty `Regulator` section.
- Replace the CyclotomicEight ClassGroup 115-line copy-paste with `import`/de-`private` of the
  PrimeSplitting originals.

### Priority 2 — `Common` API additions (high leverage)
- Add `absNorm_span_natCast`, `abs_norm_int_lt_of_remainder_eq`, `mulEquivZModOfCard`,
  `heightOneOfAbsNormNeZero`, `ringOfIntegersLinearMap` to `Common.lean`; refactor call sites.
  Each removes 3–21 copies. No new mathematics.

### Priority 3 — The reduction-mod-`p` hoist (the big one)
- Design `Common.ResidueAPI` parametrized by the integral power basis + prime; port the 6
  PrimeSplitting folders onto it. **First** spend a focused session checking whether mathlib's
  `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` (Kummer–Dedekind) can replace the
  machinery outright — if so the hoist becomes a thin wrapper.

### Priority 4 — Close the `sorry`s (mathematical)
- **Class A (unit-index, 8 sorries):** the `isFundamental`/`regulator_eq` family. SqrtFive is
  closest — it only needs the Pell-±4 ↔ `ℤ[(1+√5)/2]` bridge (SqrtTwo already has the
  template via `Zsqrtd`/`Pell.Solution₁`). The cyclotomic ones need the cyclotomic-unit index
  `h⁺ = 1`. These are genuine research-grade obligations; track as known blockers.
- **Class B (covering, 3 sorries):** the `normEuclidean` proofs for CubeRootThree,
  CyclotomicEight, CyclotomicFive. SqrtFive and SqrtTwo already prove their analogues — adapt
  that fractional-norm covering argument. Lower-risk than Class A.

---

### Top 5 action items
1. **Hoist the Kummer–Dedekind `residueHom` machinery to `Common`** (6-file dedup; check
   mathlib's `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` first).
2. **Kill the 2 exact-duplicate `private` lemmas + the 115-line CyclotomicEight copy-paste**
   (de-`private` the reduction block).
3. **Add 5 small generic helpers to `Common`** (`absNorm_span_natCast`,
   `abs_norm_int_lt_of_remainder_eq`, `mulEquivZModOfCard`, `heightOneOfAbsNormNeZero`,
   `ringOfIntegersLinearMap`) and refactor — removes 30+ copies.
4. **Remove ~5 dead lemmas + empty skeleton files.**
5. **Port SqrtTwo's Pell unit-generation template to SqrtFive** to clear 1 of the 2 `sorry`
   classes there; adapt the SqrtTwo/SqrtFive `normEuclidean` covering proof to the 3 open
   cyclotomic/cubic cases.
