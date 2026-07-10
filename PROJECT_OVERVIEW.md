# Project Overview: `NumberField/FieldExamples`

Generated: 2026-06-15 (rewrite)

> Full per-declaration inventories (every `def`/`lemma`/`theorem`/`instance` with
> What / How / Hypotheses / Uses-from-project / Lines / Notes) live in
> [`.overview/`](.overview/): one file per case study —
> [`CubeRootThree.md`](.overview/CubeRootThree.md), [`CyclotomicEight.md`](.overview/CyclotomicEight.md),
> [`CyclotomicFive.md`](.overview/CyclotomicFive.md), [`CyclotomicThree.md`](.overview/CyclotomicThree.md),
> [`SqrtFive.md`](.overview/SqrtFive.md), [`SqrtNegSix.md`](.overview/SqrtNegSix.md),
> [`SqrtTwo.md`](.overview/SqrtTwo.md). This document is the **synthesis**: the headline
> NumberField-API-maturity assessment requested for the project, plus inventory summary,
> cross-file analysis, and action plan.

---

## Executive Summary

`FieldExamples` is a library of **seven worked number-field case studies**, each computing the
full classical invariant package of one field — degree, Galois group, signature, ring of
integers, integral basis, discriminant, prime splitting, class number/group, unit group +
regulator, Euclideanity, and a local–global / adelic epilogue. The seven fields are three
quadratic-by-`QuadraticAlgebra` (`ℚ(√2)`, `ℚ(√5)`, `ℚ(√−6)`), one quadratic-by-cyclotomic
(`ℚ(ζ₃)=ℚ(√−3)`), one non-Galois cubic (`ℚ(∛3)`, the only degree > 2 with infinite unit
rank and the only field with a non-trivial Galois *closure*), and two higher cyclotomic
(`ℚ(ζ₅)`, `ℚ(ζ₈)`). A single shared file [`Common.lean`](XYin/NumberField/FieldExamples/Common.lean)
holds the genuinely field-agnostic machinery.

Because every field is taken all the way through the same invariant checklist, the project is
in effect a **stress-test of Mathlib's `NumberField` API**: it shows precisely which classical
invariants Mathlib lets you state and prove the way a mathematician would, which it forces into
an awkward encoding, and which it cannot yet support at all. **That assessment is the headline
deliverable and is [Part 3](#part-3-numberfield-api-maturity-the-headline-assessment) below.**

The short version: **arithmetic invariants are in excellent shape** — degree, signature, ring of
integers, integral basis, discriminant, per-prime ramification/inertia, class number, the
*abstract* Dirichlet unit structure, CM structure, and the adelic/local-global layer all sit on
mature, well-matched Mathlib API. The **structural group statements are formalisable but
stylistically unnatural** — finite group/Galois/class-group/unit isomorphisms are all delivered
as `Nonempty (… ≃* Multiplicative (ZMod n))` rather than via cyclicity/structure typeclasses,
and the *congruence splitting laws* and *quadratic subfields of cyclotomic fields* are rebuilt
by hand for lack of turnkey API. The remaining gaps are now down to **6 `sorry`s in two
families**: (a) certifying an *explicit* unit as fundamental (`fundamentalUnitSystem_isFundamental`),
and (b) **norm-Euclideanity** (`normEuclidean`).

**A key qualification — and the analytical spine of [Part 3](#part-3-numberfield-api-maturity-the-headline-assessment).**
When an invariant is hard to formalise, the difficulty has two distinct possible causes, and they
must not be conflated: **(1) immature API** — Mathlib lacks an abstraction a mathematician takes for
granted, so the proof is padded with work a paper would never show; or **(2) intrinsic mathematical
difficulty** — the theorem is genuinely hard *in ordinary mathematics too*, and the long formal
proof merely follows the long informal one faithfully, which is **not the API's fault**. Five sorries
were just closed, and they sharpen this distinction decisively:

- The **regulator** values (`SqrtTwo`, `SqrtFive`, `ζ₅`, `ζ₈`) were *misdiagnosed by the previous
  overview as a missing "`regulator = log(unit)`" API bridge.* They are not: that step is **mature
  Mathlib API** (`regOfFamily_div_regulator` + `regOfFamily_eq_det` + `Matrix.det_eq_elem_of_subsingleton`).
  The regulator was only ever blocked *downstream of fundamentality* — once the fundamental unit is
  certified, the value follows mechanically. Cause: neither (1) nor (2) — it was simply a dependency.
- **`SqrtFive`'s fundamental unit** is now proved by a self-contained **real-embedding
  window-reduction** — the standard textbook argument, formalised with existing API and *no* Pell-±4
  / half-integral-order machinery (which the previous overview wrongly called a missing-API blocker).
  Cause: **(2)** — the difficulty was real mathematics, faithfully discharged, not an API gap.

So the **honest reading of the 6 remaining sorries is that they are dominated by cause (2)**: proving
a *specific* unit fundamental, and exhibiting a norm-Euclidean covering, are hard theorems whose
formal proofs are long because the mathematics is long. Mathlib's abstract `fundSystem`/`regulator`
API is in fact *adequate to state and connect* them. There is a secondary cause-(1) component only in
the **totally-complex cyclotomic** cases (`ζ₅`, `ζ₈`), where — lacking any real embedding to run a
window-reduction — a *cyclotomic-units library* (which Mathlib does not have) would be the natural
tool; and a mild one for norm-Euclidean (Mathlib has no predicate to even state it cleanly).

Two folders (`CyclotomicThree`, `SqrtNegSix`) are entirely `sorry`-free — both have unit rank 0,
which dissolves the fundamental-unit/regulator blocker. **`SqrtTwo` and `SqrtFive` are now fully
`sorry`-free too** (SqrtTwo certifies its fundamental unit via `Pell`/`Zsqrtd`, SqrtFive via the
window-reduction; both then get the regulator from `regOfFamily_eq_det`). **No `set_option`
workarounds of substance anywhere.**

---

## Statistics

- **Files:** 78 (`Common.lean` + 7 case studies × ~11 files); **≈ 19,900 lines** in
  `FieldExamples` proper.
- **Declarations:** ~1,100 (≈ 230 defs/abbrevs, ≈ 800 lemmas/theorems, ≈ 40 instances,
  ≈ 60 anonymous `example` smoke-tests; 0 user `structure`/`class`).
- **`sorry`s:** 6, across 6 files, in **2 families** (table below) — down from 11 after the
  2026-06-15 unit-theory pass (all 4 `regulator_eq` bodies + `SqrtFive`'s fundamental unit closed).
- **`set_option`:** effectively 0 (one `linter.flexible false` in a discriminant proof).
- **`Common.lean`:** 255 lines, 13 shared declarations including the **hoisted Kummer–Dedekind
  `ResidueHom` section** (`genResidueHom`, `ker_genResidueHom`, `isMaximal_span_gen_sub`,
  `absNorm_span_gen_sub`) and the **Euclidean-step lemma** `abs_intNorm_lt_of_abs_norm_le` —
  both of which were the *previous* overview's top recommendations and are now done.

### The 6 remaining `sorry`s (2 families), and the 5 just closed

| File | Declaration | Family | Why it is still open | Dominant cause |
|---|---|---|---|---|
| CubeRootThree/Units | `fundamentalUnitSystem_isFundamental` | **A: explicit-fundamental-unit** | certify `∛9−2` fundamental: rule out smaller units (Artin-type index `[𝓞ˣ:⟨−1,θ²−2⟩]=1`) | (2) intrinsic; a real cubic argument |
| CyclotomicFive/Units | `fundamentalUnitSystem_isFundamental` | A | certify `1+ζ` fundamental: cyclotomic-unit index `h⁺=1`; no real embedding for a window-reduction | (2)+(1): hard *and* wants cyclotomic-units API |
| CyclotomicEight/Units | `fundamentalUnitSystem_isFundamental` | A | certify `1+√2` fundamental (same `h⁺=1` obstruction) | (2)+(1) |
| CubeRootThree/Euclidean | `normEuclidean` | **B: norm-Euclidean covering** | geometry-of-numbers covering bound for the cubic form | (2) intrinsic; (1) no predicate |
| CyclotomicFive/Euclidean | `normEuclidean` | B | covering bound for the `ℤ[ζ₅]` lattice | (2)+(1) |
| CyclotomicEight/Euclidean | `normEuclidean` | B | covering bound for the `ℤ[ζ₈]` lattice | (2)+(1) |

**Closed in the 2026-06-15 pass (5):** `SqrtTwo/regulator_eq`, `SqrtFive/fundamentalUnit_generates`,
`SqrtFive/regulator_eq`, `CyclotomicFive/regulator_eq`*, `CyclotomicEight/regulator_eq`*. The four
`regulator_eq` proofs all go through the **mature** `regOfFamily_div_regulator` → `regOfFamily_eq_det`
chain (so "`regulator = log(unit)`" was never a missing bridge); `SqrtFive`'s fundamental unit fell to
a real-embedding window-reduction, *not* the previously-blamed Pell-±4 / half-integral bridge.
(*The two cyclotomic `regulator_eq` bodies are complete but still *call* the open `isFundamental`, so
they hold only modulo Family A; they carry no `sorry` token of their own.)

`CyclotomicThree` and `SqrtNegSix` are `sorry`-free (unit rank 0 ⇒ regulator trivially 1, no
fundamental unit to certify); `SqrtTwo` and `SqrtFive` are now `sorry`-free too. Every
`unitGroupStructure` is `sorry`-free even in the open folders — it routes through Mathlib's abstract
`fundSystem`, not through the sorried concrete-fundamental-unit lemma. **`SqrtTwo`/`SqrtFive` were the
diagnostic cases:** they show that once the fundamental unit is certified — by Pell or by a faithful
window-reduction — the regulator value follows from existing Mathlib API, so the *only* real
bottleneck is Family A (certify the explicit unit) and Family B (the covering bound).

---

## Part 1: Declaration Inventory (headline results)

Full inventories in [`.overview/`](.overview/). Public invariant results per case study:

| Field | [K:ℚ] | Sig | 𝓞K | disc | h | Units | Splitting law | Euclidean |
|---|---|---|---|---|---|---|---|---|
| **SqrtTwo** `ℚ(√2)` | 2 | (2,0) | ℤ[√2] | 8 | 1 | μ₂×ℤ, fund `1+√2` ✓ | split ⇔ p≡±1 (8); 2 ram | **yes** |
| **SqrtFive** `ℚ(√5)` | 2 | (2,0) | ℤ[φ] | 5 | 1 | μ₂×ℤ, fund `φ` ✓ | split ⇔ p≡±1 (5); 5 ram | yes |
| **SqrtNegSix** `ℚ(√−6)` | 2 | (0,1) | ℤ[√−6] | −24 | **2** | μ₂ (rank 0) | split ⇔ p≡1,5,7,11 (24); 2,3 ram | **no** (not even PID/UFD) |
| **CyclotomicThree** `ℚ(ζ₃)` | 2 | (0,1) | ℤ[ζ₃] | −3 | 1 | μ₆ (rank 0) | split ⇔ p≡1 (3); 3 ram | yes |
| **CubeRootThree** `ℚ(∛3)` | 3 | (1,1) | ℤ[∛3] | −243 | 1 | μ₂×ℤ, fund `∛9−2` (sorry) | cubic-residue law; 3 tot. ram | sorry |
| **CyclotomicFive** `ℚ(ζ₅)` | 4 | (0,2) | ℤ[ζ₅] | 125 | 1 | μ₁₀×ℤ, fund `1+ζ` (sorry) | split ⇔ p≡1 (5); 5 ram (e=4) | sorry |
| **CyclotomicEight** `ℚ(ζ₈)` | 4 | (0,2) | ℤ[ζ₈] | 256 | 1 | μ₈×ℤ, fund `1+√2` (sorry) | split ⇔ p≡1 (8); 2 ram (e=4) | sorry |

Special-topic files: `CyclotomicEight/Subfields` (the three quadratic subfields √2, i, √−2 — as
generator relations), `CyclotomicEight/Galois` (Klein-four group + S₃-free), `CubeRootThree/Galois`
(non-normal field; `SplittingField` closure with `Gal ≅ S₃`),
`CyclotomicFive/QuadraticSubfield` (Gauss sum ⇒ ℚ(√5) ⊂ ℚ(ζ₅)),
`{CyclotomicEight,CyclotomicFive,CyclotomicThree,SqrtNegSix}/CMField` (CM structure via
`NumberField.IsCMField`), `SqrtNegSix/UniqueFactorization` (`¬ UniqueFactorizationMonoid` + the
explicit `6 = 2·3 = √−6·(−√−6)` counterexample).

---

## Part 2: Cross-File Dependencies

Each folder imports **linearly**: `Basic → Galois → Embeddings → RingOfIntegers →
Discriminant → PrimeSplitting → ClassGroup → Units → Euclidean → LocalGlobal`, with
special-topic files hanging off the late chain. All folders depend only on `Common.lean` and
Mathlib — **there is no cross-folder dependency**, even between the two `…Three` fields and even
between the two real-quadratic `QuadraticAlgebra` fields. That independence is deliberate (each
folder is a self-contained worked example) but it is also the source of the residual duplication
in [Part 4](#part-4-moral-duplications).

`Common.lean` is now genuinely load-bearing: every folder uses the ramification helpers and the
torsion/rank power-homs, and five of seven use the hoisted `ResidueHom` Kummer–Dedekind block
(`isMaximal_span_gen_sub` / `absNorm_span_gen_sub`, typically via thin `…_span_pair` wrappers).
The headline cleanup since the last overview: **`CubeRootThree`, `CyclotomicThree`, `CyclotomicFive`
and `CyclotomicEight/PrimeSplitting` now call the Common ResidueHom** instead of re-deriving a
residue map per field. The one straggler is `CyclotomicEight/ClassGroup.lean`, which still carries
a ~115-line `private` copy (lines 72–186) — now duplicating *Common*, mechanically replaceable by
one `isMaximal_span_gen_sub 2 1` call.

---

## Part 3: NumberField API Maturity — the Headline Assessment

> *With the current Mathlib `NumberField` API, as exercised across all seven case studies: which
> invariants can be formalised easily and in a mathematically natural way; which can be formalised
> but only in a way unnatural compared to ordinary mathematics; and which would require further API
> development?*

The table below classifies each classical invariant by the **best outcome achieved anywhere in the
project**, then the prose explains the qualifications. "Mathlib def" names the key API the proof
rests on.

| Invariant | Verdict | Mathlib API it rests on |
|---|---|---|
| Degree `[K:ℚ]` | **Natural** | `Module.finrank`, `PowerBasis.finrank`, `IsCyclotomicExtension.finrank` |
| Signature / # real & complex places | **Natural** | `InfinitePlace`, `IsTotallyReal`/`IsTotallyComplex`, `nrRealPlaces`/`nrComplexPlaces`, `card_add_two_mul_card_eq_rank` |
| Ring of integers `𝓞 K` | **Natural** (cyclotomic) / **Natural-with-work** (radical) | `IsIntegralClosure`, `𝓞 K`; cyclotomic free via `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`; radical via `IsEisensteinAt` + `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt` |
| Integral basis | **Natural** (power basis) / **Unnatural** (displayed family) | `PowerBasis`, `IsPrimitiveRoot.integralPowerBasis`; matching to a displayed `Basis` & to `NumberField.integralBasis` is manual |
| Discriminant | **Natural** | `NumberField.discr`, `Algebra.discr`, `discr_powerBasis_eq_norm`; cyclotomic closed forms `discr_prime`/`discr_prime_pow` |
| Per-prime ramification / inertia / residue | **Natural** | `Ideal.absNorm`, `inertiaDeg`, `ramificationIdx`, `Algebra.IsUnramifiedAt`, `differentIdeal`, `HeightOneSpectrum`, `absNorm_eq_pow_inertiaDeg'` |
| Class number / PID / UFD (and their negations) | **Natural** frame / **Unnatural** witness | `NumberField.classNumber`, `ClassGroup`, `IsPrincipalIdealRing`, `UniqueFactorizationMonoid`, Minkowski-bound PID criterion |
| Unit group — *abstract* Dirichlet structure `μ × ℤ^r` | **Natural** (math) / **Unnatural** (encoding) | `fundSystem`, `closure_fundSystem_sup_torsion_eq_top`, `basisModTorsion`, `Units.rank`, `torsionOrder` |
| Regulator, rank-0 case | **Natural** | `Units.regulator`, `det_eq_one_of_card_eq_zero` |
| CM structure | **Natural** | `NumberField.IsCMField`, `maximalRealSubfield`, `IsCMField.units_rank_eq_units_rank` |
| Local–global / adelic layer | **Natural** | `HeightOneSpectrum.adicCompletion`, `AdeleRing`, `InfiniteAdeleRing`, `FinitePlace`, `canonicalEmbedding`, `mixedEmbedding`, `convexBodyLT`, `dedekindZeta` |
| Euclideanity, small-disc quadratic & `ℚ(ζ₃)` | **Natural** | direct remainder bound by `nlinarith` (no covering needed) |
| Galois group as `Gal ≅ (ℤ/n)ˣ` (cyclotomic) / `IsGalois` | **Natural** | `IsGalois`, `IsCyclotomicExtension.autEquivPow`, `galEquivZMod` |
| Galois group as a *named finite group* (`ℤ/n`, `V₄`, `S₃`) | **Unnatural** | `Nonempty (… ≃* Multiplicative (ZMod n))`, `IsKleinFour.nonempty_mulEquiv`, `Polynomial.Gal.galActionHom_bijective_of_prime_degree` |
| Galois group of a *non-normal* field / its closure | **Unnatural** | no "Gal of non-normal ext" notion; via `Polynomial.SplittingField` |
| Congruence **splitting law** (`p ≡ … mod n`) | **Unnatural** | rebuilt by hand from `orderOf` in `(ℤ/p)ˣ` + Kummer–Dedekind; reciprocity inputs (`ZMod.exists_sq_eq_two_iff`, `jacobiSym`) exist |
| Kummer–Dedekind reduction map per prime | **Unnatural** (project supplies it) | project's `Common.genResidueHom`; Mathlib's `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` not turnkey for this |
| Quadratic subfields of a cyclotomic field | **Unnatural** | exhibited as generator-square relations, not `IntermediateField` lattice objects |
| Gauss sum / explicit subfield embedding | **Unnatural** | bespoke `AdjoinRoot.liftAlgHom`; Mathlib `gaussSum` (additive characters) doesn't connect to subfields |
| Regulator **value** `= log(fundamental unit)` | **Natural** *(corrected)* | mature `regOfFamily_div_regulator` + `regOfFamily_eq_det` + `Matrix.det_eq_elem_of_subsingleton`; *not* a missing bridge — only downstream of fundamentality |
| **Explicit** fundamental unit certification (`isFundamental`), real quadratic | **Hard math, not an API gap** | provable today (`SqrtFive` window-reduction / `SqrtTwo` Pell); `fundSystem`/`regulator` API suffices to state & use it |
| **Explicit** fundamental unit certification, cubic `ℚ(∛3)` | **Hard math (intrinsic)** | genuinely a real argument (rule out smaller units); no API shortcut, but none conceptually missing either |
| **Explicit** fundamental unit certification, cyclotomic `ζ₅`,`ζ₈` | **Hard math + secondary API gap** | totally complex ⇒ no real-embedding window-reduction; wants a *cyclotomic-units / `h⁺`* library (`cyclotomicUnit`, unit-index) Mathlib lacks |
| **Norm-Euclideanity** (cubic/cyclotomic) | **Hard math + mild API gap** | the covering bound is genuine geometry-of-numbers content; Mathlib also lacks a norm-Euclidean predicate to even state it cleanly |

### 3.1 Easy *and* natural — Mathlib's `NumberField` API matches the mathematics

For the bulk of the classical invariant package, the Lean statement reads the way a textbook
would, and the proof rests on one or a few dedicated Mathlib lemmas:

- **Degree, signature, discriminant, ring of integers, integral basis** are essentially turnkey,
  and *strikingly so in the cyclotomic model*: `IsCyclotomicExtension.Rat.*` gives finrank `φ(n)`,
  the closed-form discriminant, the integral closure `ℤ[ζ]`, total-complexity, and the place
  counts as one-liners. `CyclotomicThree` is the cleanest illustration — the *same field* `ℚ(√−3)`
  is much harder to set up through the radical `QuadraticAlgebra ℚ (−3) 0` model (where `ℤ[√−3]`
  is **not** maximal, index 2), confirming that the right *presentation* is half the battle.
- **Per-prime arithmetic** — ramification index, inertia degree, the different ideal, whether a
  given prime is (un)ramified — is fully and naturally supported (`Ideal.absNorm`,
  `Ideal.inertiaDeg`, `Ideal.ramificationIdx`, `Algebra.IsUnramifiedAt`, `differentIdeal`,
  `absNorm_differentIdeal`, `HeightOneSpectrum`). Every "what does `p` do in `𝓞 K`" question is
  answered idiomatically.
- **Class number 1 / PID / UFD** sit naturally on `NumberField.classNumber` + the Minkowski-bound
  PID criterion. Crucially the **negative** results are equally natural: `SqrtNegSix` states
  `¬ IsPrincipalIdealRing` and `¬ UniqueFactorizationMonoid` with the *canonical* Mathlib
  predicates (and additionally formalises the textbook `6 = 2·3 = √−6·(−√−6)` irreducible-but-not-
  unique counterexample, with `Irreducible`/`Prime` and a norm-form non-attainment witness).
- **The abstract Dirichlet unit structure** `(𝓞 K)ˣ ≅ μ_w × ℤ^r` is *proved sorry-free in every
  folder*, including the ones whose explicit fundamental unit is sorried, because it routes through
  Mathlib's abstract `fundSystem` + `closure_fundSystem_sup_torsion_eq_top` + `basisModTorsion`.
  The **rank-0 case** (`CyclotomicThree`, `SqrtNegSix`) is fully natural end to end — the regulator
  is the empty determinant `= 1`, and there is simply no fundamental unit to certify.
- **CM fields** are first-class: `NumberField.IsCMField` + `maximalRealSubfield` give the CM
  predicate, the quadratic-over-real-subfield instance, and the unit-rank equality as one-liners.
- **The local–global / adelic layer** (completions, finite/infinite places, product formula,
  canonical & mixed embeddings, convex bodies, Dedekind zeta and its residue) is all present and
  cited directly — though, see 3.2, mostly as `example` smoke-tests rather than named theorems.

### 3.2 Formalisable, but unnatural compared to ordinary mathematics

These invariants *are* established, but the Lean rendering diverges from how a mathematician writes
or thinks about them — usually because Mathlib has the *ingredients* but not the *concept* as a
reusable object:

- **Finite group structure as `Nonempty (G ≃* Multiplicative (ZMod n))`.** The single most pervasive
  unnaturalness. Galois groups, class groups, and unit torsion are all delivered this way (and the
  free part of the unit group as `Multiplicative (Fin r → ℤ)`), assembled by hand from the project's
  `torsionPowerHom`/`rankOnePowerHom` and `MulEquiv.ofBijective`. A mathematician would say "the
  Galois group is cyclic of order 2" (`IsCyclic` + order) or "the unit group is `μ_w × ℤ^r`"; the
  encoding instead exhibits a bespoke isomorphism to a `Multiplicative (ZMod n)` model, and renders
  the trivial group as `Multiplicative (ZMod 1)`. The root cause is that **Mathlib has no
  off-the-shelf "unit group ≅ `μ_w × ℤ^r`" structure equivalence** and no turnkey "group of prime
  order is `≅ ZMod p`" packaging.
- **Non-cyclic / named Galois groups.** For `ℚ(ζ₈)` the canonical `Gal ≅ (ℤ/8)ˣ` is clean, but
  landing the *named* Klein-four form requires manually proving `Nat.card = 4` and
  `Monoid.exponent = 2` to invoke `IsKleinFour.nonempty_mulEquiv` — there is no "the Galois group is
  `V₄`" API. For the **non-normal** `ℚ(∛3)`, Mathlib has (correctly) no notion of "Galois group of a
  non-normal extension"; the project instead names the closure as `Polynomial.SplittingField (X³−3)`
  and gets `Gal ≅ S₃` from `Polynomial.Gal.galActionHom_bijective_of_prime_degree`. This works and
  is idiomatic, but every such structural fact is hand-built.
- **The congruence splitting law.** "`p` splits in `K` ⟺ `p ≡ … (mod n)`" has **no Mathlib API**;
  each field reconstructs it from `orderOf` computations in `(ℤ/p)ˣ` plus the project's Kummer–
  Dedekind engine. The reciprocity inputs exist (`ZMod.exists_sq_eq_two_iff`, `jacobiSym.mod_right`),
  but assembling them into the splitting *law* is bespoke every time.
- **Kummer–Dedekind reduction itself.** The project had to build its own residue map
  `Common.genResidueHom : 𝓞 K → ZMod p` (kernel `(p, gen − r)`, norm `p`) to read off splitting
  from `minpoly mod p`. Mathlib's `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` is the
  relevant theorem but is not in a form that discharges the per-prime maximal-ideal/norm facts
  directly — so a custom (now shared) abstraction was necessary.
- **Subfields of cyclotomic fields.** The three quadratic subfields of `ℚ(ζ₈)` and the
  `ℚ(√5) ⊂ ℚ(ζ₅)` Gauss-sum subfield are exhibited as *generator-square relations*
  (`(ζ+ζ⁷)² = 2`, `gaussSum² = 5`) and bespoke `AdjoinRoot.liftAlgHom` embeddings — **not** as
  `IntermediateField`/`Subfield` lattice objects connected through the Galois correspondence.
  Mathlib has the subfield lattice but no convenient way to *exhibit* "the index-2 subfields of a
  `V₄` extension", and its `gaussSum` API (additive characters / quadratic reciprocity) does not
  connect to subfields. There is also a "soft" gap: nothing links the abstract `maximalRealSubfield K`
  to the explicit `ℚ(√5)`/`ℚ(√2)` models.
- **Euclideanity stated as a raw `∀…∃…`.** There is no Mathlib "is-norm-Euclidean" predicate, so
  both the positive results and `SqrtNegSix`'s `not_normEuclidean` spell the property out inline and
  never register a `EuclideanDomain` instance — the "norm-Euclidean ⇒ PID" upgrade is then stated
  separately rather than via Mathlib's Euclidean→PID path.
- **Minkowski-bound numerics and class-group witnesses.** The PID/class-number proofs invoke the
  right Mathlib criterion, but the numeric bound check (`(2/π)√|disc| < N`, then enumerate primes
  `≤ ⌊N⌋`) is a manual `nlinarith`/`norm_num`/`Nat.floor` ritual each time, and **exhibiting a
  non-trivial class** (`SqrtNegSix`'s `Cl ≅ ℤ/2`) is entirely bespoke ideal arithmetic — Mathlib
  gives the frame (`exists_ideal_in_class_of_norm_le`) but not the witness.
- **`example` smoke-tests standing in for theorems.** The `LocalGlobal` files pin ~60 local-global
  facts (product formula, completion `≅ ℝ`, convex-body measurability, zeta residue, every `e`/`f`
  check) as anonymous `example`s rather than named, reusable lemmas — they verify the API wiring but
  contribute no statement another file can use.

### 3.3 The hard cases — and *whose fault* the difficulty is

The 6 remaining `sorry`s live in two families. The important methodological point — and the reason
the 2026-06-15 pass is so clarifying — is that "hard to formalise" has **two causes that must be
told apart**:

> **(1) Immature API.** Mathlib lacks an abstraction a mathematician takes for granted, so the
> formal proof is *longer or uglier than the informal one* — work appears that a paper would never
> show. Here the difficulty **is the API's fault**, and the right response is to build the API.
>
> **(2) Intrinsic mathematical difficulty.** The theorem is genuinely hard *in ordinary mathematics
> too*; the formal proof is long because the informal proof is long, and the formalisation simply
> **follows the mathematics faithfully.** Here the difficulty is **not the API's fault** — no amount
> of library engineering removes it, only mathematical work does.

The previous overview conflated the two and over-charged Mathlib. The five just-closed sorries force
the correction:

- **The regulator value is cause-*neither* — it was a mis-diagnosis.** The previous overview listed
  "`regulator = log(fundamental unit)`" as a missing API bridge, citing `SqrtTwo` (where the unit is
  Pell-certified yet `regulator_eq` was a sorry). That was wrong: the bridge is **mature Mathlib
  API** — `regOfFamily_div_regulator` (index 1 ⇒ `regulator = regOfFamily`), `regOfFamily_eq_det`,
  and `Matrix.det_eq_elem_of_subsingleton` on the rank-1 `1×1` log-matrix. All four `regulator_eq`
  sorries closed through exactly this chain. The regulator was never an API gap; it was only ever
  *downstream of fundamentality*.
- **The real-quadratic fundamental unit is cause (2), now discharged.** `SqrtFive`'s
  `fundamentalUnit_generates` was blamed on a missing **Pell-`±4` / half-integral-order** bridge.
  But it is provable *with existing API* by a faithful **real-embedding window-reduction**: map
  units into `ℝ` (`φ ↦ Φ`), reduce into `[1, Φ)` by a power of `φ`, and let the norm form
  `x²+xy−y² = ±1` force the only such unit to be `1`. This is the textbook proof; the difficulty was
  honest mathematics, not Mathlib's fault. (`SqrtTwo` reaches the same end via `Pell`/`Zsqrtd` — a
  second, equally API-supported route.)

That leaves the genuinely-open work, classified honestly:

- **Family A — certify the *explicit* fundamental unit (`fundamentalUnitSystem_isFundamental`):
  `∛9−2` (`ℚ(∛3)`), `1+ζ` (`ℚ(ζ₅)`), `1+√2` (`ℚ(ζ₈)`).** Mathlib's abstract `fundSystem` is
  *adequate to state and use* fundamentality (the whole `unitGroupStructure ≅ μ_w × ℤ^r` is
  sorry-free through it); what is missing is the *mathematical certificate* that a given unit
  generates `𝓞ˣ/torsion`. For the **cubic** this is **purely cause (2)** — it is a real argument
  (rule out smaller units), with no conceptually-missing abstraction; a `SqrtFive`-style reduction is
  in principle adaptable since `ℚ(∛3)` has a real place. For the **totally-complex cyclotomics**
  `ζ₅`,`ζ₈` it is **cause (2) with a real cause-(1) component**: with no real embedding there is no
  window to reduce into, and the natural tool — a *cyclotomic-units / class-number-plus (`h⁺=1`)*
  library — **does not exist in Mathlib**. So here, and only here, "build more API" genuinely *would*
  help, though the underlying theorem is still deep.

  > **What `h⁺ = 1` means, and why it is the right thing to build API around.** `h⁺` is the class
  > number of the **maximal real subfield** `K⁺ = ℚ(ζ + ζ⁻¹)` (the fixed field of complex
  > conjugation); the full class number factors as `h = h⁻·h⁺`. There is a distinguished, *explicit*
  > subgroup `C ⊆ 𝓞ˣ` of **cyclotomic units** (generated by elements like `1+ζ`, `(1−ζᵃ)/(1−ζ)`),
  > and the classical theorem (Kummer / the analytic class-number formula for `K⁺`) is
  > `[𝓞ˣ : C] = h⁺`. So `h⁺ = 1` says exactly that the cyclotomic units are the *whole* unit group
  > mod torsion — i.e. the explicit `1+ζ` (resp. `1+√2`, since `K⁺ = ℚ(√5)`, resp. `ℚ(√2)`, both of
  > class number 1) really *is* fundamental, with nothing finer between it and 1. **This is a
  > genuinely reusable abstraction worth developing**: a `cyclotomicUnit` definition + the index
  > theorem `[𝓞ˣ : C] = h⁺` would discharge `isFundamental` for *every* cyclotomic field at once
  > (not just ζ₅/ζ₈), feed regulator and class-number-formula computations, and is a standard,
  > well-understood piece of theory (Washington, *Cyclotomic Fields*, Ch. 8). It is the **one**
  > sorry-driving gap where new Mathlib API is clearly the right investment.
- **Family B — norm-Euclideanity (`normEuclidean`): `ℚ(∛3)`, `ℚ(ζ₅)`, `ℚ(ζ₈)`.** Primarily
  **cause (2)**: the proof needs an *effective geometry-of-numbers covering bound* (every `x ∈ K`
  within field-norm `< 1` of the lattice), which is genuine mathematical content — the small-disc
  quadratics and `ℚ(ζ₃)` discharge their analogues by a direct `nlinarith` remainder bound only
  because the bound there is *elementary*, not because of any API. There is a **secondary cause (1)**:
  Mathlib has no norm-Euclidean predicate to state the property cleanly (it is written as a raw
  `∀…∃…`) and exposes no effective covering lemma — its convex-body machinery is abstract
  existence/measure, not an effective radius.

**The same lens applied to the *unnatural* (Part 3.2) items** sharpens them too: the
`Nonempty (… ≃* Multiplicative (ZMod n))` group encodings, the per-prime Kummer–Dedekind residue map,
the subfields-as-generator-relations, and the absent norm-Euclidean predicate are **cause (1)** —
the mathematics is easy, the encoding is awkward, and packaging API would fix it. By contrast,
**exhibiting `ℚ(√−6)`'s non-trivial ideal class** (find a concrete non-principal ideal and prove its
norm-form value unattainable) and the **reciprocity content** of the splitting laws are **cause (2)**
— Mathlib gives the frame, but producing the witness is irreducibly mathematical work that no API
removes.

**Net.** The *arithmetic* of number fields is well served by Mathlib today. The *structural group
theory* is provable but stylistically awkward — a genuine but shallow **cause-(1)** debt fixable with
a few packaging lemmas. The remaining `sorry`s are dominated by **cause (2)**: they are hard theorems
faithfully formalised, not API failures. The one place where new API would materially help the open
problems is a **cyclotomic-units library** (and, more cosmetically, a norm-Euclidean predicate);
everything else awaits mathematics, not Mathlib.

---

## Part 4: Moral Duplications

Pairwise comparison of the recurring families (A = canonical/representative occurrence). The big
Kummer–Dedekind hoist recommended by the previous overview **has largely happened** (it now lives
in `Common.ResidueHom`); what remains is one straggler and the inevitable per-field concrete work.

| Decl A | Decl B (… and more) | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `Common.isMaximal_span_gen_sub` / `absNorm_span_gen_sub` (the hoisted engine) | per-field `isMaximal_span_pair` / `absNorm_span_pair` wrappers | yes (specialisation) | thin wrappers | **OK — already shared; wrappers are fine** |
| `CyclotomicEight/ClassGroup` private residue stack (L72–186, ~115 lines) | `Common.genResidueHom` & the migrated `PrimeSplitting` | yes | yes (copy predates the hoist) | **REPLACE with `Common.isMaximal_span_gen_sub 2 1`** |
| `mulEquivOfPrimeCardEq`-style cyclic-group proof (Galois) | same shape in ClassGroup, Units across folders | yes (G of card p) | yes | **HOIST a `mulEquivZModOfCard` wrapper to Common** |
| `heightOne*` finite-place defs (LocalGlobal) | ~21 defs across 7 LocalGlobal files | yes (asIdeal+isPrime+ne_bot) | yes | **HOIST `HeightOneSpectrum.ofAbsNormNeZero`** |
| `absNorm_span_natCast` / `intNorm_natCast` inline norm-of-integer derivations | per-field copies (≥8× in SqrtNegSix alone) | yes | yes | **HOIST a degree-parametrised lemma to Common** |
| `ringOfIntegersLinearMap` (CubeRootThree) | same in SqrtNegSix &c | yes (`𝓞K →ₗ[ℤ] K`) | yes | **HOIST (fully field-free)** |
| `ramified_iff_eq_three` (CubeRootThree) ↔ (CyclotomicThree); `span_three_eq` | the two `…Three` folders | yes mod relation `r³=3` vs `r²+r+1=0` | structurally yes | unify only if it stays readable |

The two **exact within-folder** duplicates flagged previously (`goldenIntO_sq`, `zeta_pow_three`)
should be re-checked against current code and collapsed if still present (promote one copy to a
public `RingOfIntegers` lemma).

---

## Part 5: Generalization & API Opportunities

1. **`Common.mulEquivZModOfCard`** *(low)* — `Nat.card G = p ⇒ G ≃* Multiplicative (ZMod p)`,
   used for Galois, class, and torsion groups alike. Directly attacks the most common unnatural
   encoding from Part 3.2.
2. **`Common.heightOneOfAbsNormNeZero`** *(low)* — bundle `asIdeal`/`isPrime`/`ne_bot` for the
   ~21 boilerplate finite-place defs in `LocalGlobal`.
3. **`Common.absNorm_span_natCast` / `intNorm_natCast`** *(low)* — `absNorm (span {(n:𝓞K)}) =
   n ^ finrank ℤ (𝓞K)` and `norm ℤ (n:𝓞K) = n^[K:ℚ]`; field-free, removes ≥10 inline copies.
4. **`Common.ringOfIntegersLinearMap`** *(low)* — `(𝓞K →ₗ[ℤ] K)` is
   `(Algebra.linearMap _ _).restrictScalars ℤ` for any number field.
5. **A norm-Euclidean predicate + Euclidean→PID hook** *(medium, upstream-able)* — even just a
   `def IsNormEuclidean (𝓞 K) := …` with the `EuclideanDomain` instance would remove the raw
   `∀…∃…` phrasing project-wide and is a plausible Mathlib contribution.
6. **★ A cyclotomic-units library (`cyclotomicUnit` + the index theorem `[𝓞ˣ : C] = h⁺`)**
   *(high value, upstream-able)* — **the single most worthwhile new API to develop.** Unlike the
   other open sorries, which are intrinsic mathematical difficulty (see below), this is a standard,
   reusable theory (Washington Ch. 8) whose absence is what blocks `isFundamental` for the
   totally-complex cyclotomic fields `ζ₅`, `ζ₈`. Once built it would certify the explicit
   fundamental unit (`1+ζ`) for *every* cyclotomic field at once, and feed regulator and
   class-number-formula computations — payoff far beyond this project. See the boxed explanation in
   Part 3.3.
7. **Norm-Euclidean predicate + Euclidean→PID hook** *(medium, upstream-able)* — a
   `def IsNormEuclidean (𝓞 K) := …` with the `EuclideanDomain` instance would remove the raw
   `∀…∃…` phrasing project-wide. *Cosmetic for the sorries, though:* it makes them stateable, not
   provable — the `normEuclidean` covering bounds remain intrinsic mathematical work.
8. **The remaining sorries are *not* API requests.** `ℚ(∛3)`'s `isFundamental` and all three
   `normEuclidean` are **mathematical-difficulty** problems (Part 3.3, cause (2)) — they await a
   real argument (a window-reduction / an effective covering bound), not a library. Do not file them
   as Mathlib feature requests; only the cyclotomic-units library (#6) genuinely is one.

---

## Part 6: Junk / Removable

1. **`CyclotomicEight/ClassGroup` private residue stack** (L72–186) — replace with `Common`
   (Part 4). Top mechanical win.
2. **Dead-code recheck** — re-verify the previously-flagged unused lemmas
   (`orderOf_unitOfCoprime_five_eq_four_iff`, `zetaFivePolynomialMod_eq_cyclotomic`,
   `intNorm_eq` in CyclThree, the CyclThree dead Kummer–Dedekind helpers) against current code;
   delete any with no consumer.
3. **Empty skeletons** — `Discriminant.lean` in SqrtFive/SqrtNegSix/SqrtTwo (content lives in
   `RingOfIntegers`) and empty trailing sections; remove or fold the header note elsewhere.
4. **Demonstrative `example`s** (~60, mostly LocalGlobal + a few Basic-file alternative-presentation
   blocks like SqrtTwo's `KUnitModel`) — *intentional* smoke-tests / pedagogy, not junk, but mark
   them as "presentation only" so they aren't mistaken for load-bearing API.

---

## Recommended Action Plan

### Priority 1 — Quick wins (mechanical, do now)
- Replace the `CyclotomicEight/ClassGroup` 115-line private residue stack with a `Common`
  `isMaximal_span_gen_sub` call (finishes the ResidueHom hoist — the last straggler).
- Collapse any remaining exact-duplicate `private` generator-relation lemmas; promote one copy
  each to a public `RingOfIntegers` lemma.
- Delete confirmed-dead lemmas and empty `Discriminant.lean` skeletons.

### Priority 2 — `Common` API additions (attack the unnatural encodings)
- Add `mulEquivZModOfCard`, `heightOneOfAbsNormNeZero`, `absNorm_span_natCast`/`intNorm_natCast`,
  `ringOfIntegersLinearMap`; refactor call sites. Each removes 4–21 copies, no new mathematics,
  and `mulEquivZModOfCard` directly improves the Part 3.2 group-structure ergonomics.

### Priority 3 — Reduce the structural unnaturalness (medium, partly upstream-able)
- Where a Galois/class/unit group is cyclic, prefer `IsCyclic` + an explicit generator-order
  statement over the `Nonempty (… ≃* Multiplicative (ZMod n))` packaging where readability allows.
- Consider a norm-Euclidean predicate + `EuclideanDomain` hook (Part 5.5).

### Priority 4 — The two `sorry` families (mostly mathematical, not API)
- **Family A (3 sorries): certify the explicit fundamental unit.** No longer "needs a regulator
  bridge" — that was closed via `regOfFamily_eq_det`. **`ℚ(∛3)`** is the most tractable: it has a
  real place, so adapt `SqrtFive`'s real-embedding window-reduction (intrinsic math, existing API,
  no new library needed). **`ℚ(ζ₅)`, `ℚ(ζ₈)`** are harder: totally complex, no window to reduce
  into — these genuinely want a **cyclotomic-units / `h⁺=1`** library, the one place a Mathlib
  contribution would unblock open work. Track as research-grade.
- **Family B (3 sorries): `normEuclidean` for `ℚ(∛3)`, `ℚ(ζ₅)`, `ℚ(ζ₈)`.** Needs an effective
  geometry-of-numbers covering bound — intrinsic content. `SqrtFive`/`SqrtTwo`/`ℚ(ζ₃)` prove their
  analogues by elementary `nlinarith` remainder estimates; for the higher-degree cases that elementary
  route does not suffice, so this is real mathematical work (optionally packaged behind a new
  norm-Euclidean predicate).
- **Already done (was Priority 4 in the last overview):** all four `regulator_eq` and `SqrtFive`'s
  fundamental unit — closing them is what revealed the regulator "API gap" to be a mis-diagnosis.

### Top 5 action items
1. **Finish the ResidueHom hoist** — kill the `CyclotomicEight/ClassGroup` 115-line private copy
   via `Common.isMaximal_span_gen_sub`.
2. **Add `mulEquivZModOfCard` + `heightOneOfAbsNormNeZero` to `Common`** and refactor — removes
   ~25 copies and softens the biggest stylistic unnaturalness (the `Multiplicative (ZMod n)`
   group encoding).
3. **Add the small norm/linear-map helpers** (`absNorm_span_natCast`, `intNorm_natCast`,
   `ringOfIntegersLinearMap`) to `Common`.
4. **Clear dead lemmas + empty skeletons; mark the `example` smoke-tests as presentation-only.**
5. **Close `ℚ(∛3)`'s `isFundamental`** by adapting `SqrtFive`'s real-embedding window-reduction
   (it has a real place; intrinsic math, no new API) — and track the **cyclotomic-units / `h⁺=1`
   library** as the one principled Mathlib feature request that would unblock the remaining
   totally-complex `isFundamental` (and, secondarily, a norm-Euclidean predicate for Family B).
