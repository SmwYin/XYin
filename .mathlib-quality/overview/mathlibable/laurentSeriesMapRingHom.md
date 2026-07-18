# /mathlibable report — `Cox.laurentSeriesMapRingHom`

Date: 2026-07-18. Project: XYin (mathlib pin 2026-05-28).

### Baseline (Phase 0)
- lake build:               ✓ clean (`lake build XYin.PhD.Cox.LaurentPolynomialEvaluation` — "Build completed successfully (2468 jobs)")
- decl `Cox.laurentSeriesMapRingHom`: ✓ resolved at `XYin/PhD/Cox/LaurentPolynomialEvaluation.lean:22`
- kind:                      def
- has sorry:                 no
- module docstring summary:  lowest-term argument behind Hasse's q-expansion principle; injectivity of polynomial substitution at a Laurent series with a pole.

### Statement (Phase 1)

`Cox.laurentSeriesMapRingHom` is **a definition** bundling the following:

Given a ring homomorphism f : R → S between commutative rings, applying f
coefficientwise to a formal Laurent series (an element of R((t)) = HahnSeries ℤ R)
yields a formal Laurent series over S; this coefficientwise map R((t)) → S((t)) is
itself a ring homomorphism. Mathematically: the Laurent-series construction is
functorial in the coefficient ring, and this def packages the induced map on a
morphism as a bundled `→+*`.

Variables / typeclasses (Lean side):
- `{R S : Type*} [CommRing R] [CommRing S]` — coefficient rings
- `(f : R →+* S)` — the coefficient ring homomorphism

Hypotheses: none beyond the typeclasses.

Conclusion (math): the coefficientwise map is a ring homomorphism R((t)) → S((t)).

Conclusion (Lean): `LaurentSeries R →+* LaurentSeries S`, with
`toFun F := F.map f` (mathlib's unbundled `HahnSeries.map`) and the four
structure fields discharged by mathlib's `HahnSeries.map_zero / map_one /
map_add / map_mul`.

### Size classification (Phase 2a)

Verdict: SMALL
Reason: not a new mathematical structure (it bundles mathlib's existing
`HahnSeries.map` as a `RingHom`), not a project main result, not a named theorem.
(Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 5 substantive lines (a `where` structure instance: `toFun` plus
four proof fields).
One-liner verdict: MULTI-LINE (structure-instance def, not a one-line alias).
The one-liner exemption table is not required; noted anyway that the def carries
the "mark semantic intent / API name" property — 25+ call sites across
Kronecker.lean and LevelThree.lean depend on the stable bundled name.

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                           | Query | Hit? | Standard form found | Notes |
|----|-----------------------------------|-------|------|---------------------|-------|
| 1  | WebSearch (specific form)         | "Hahn series" functorial ring homomorphism coefficients "base change" | yes | Hahn series R⟦Γ⟧ over ordered cancellative comm. monoid Γ; coefficientwise map induced by zero-preserving map | hit nLab "Hahn series" + mathlib docs pages; functoriality in coefficients treated as immediate |
| 2  | WebSearch (general form)          | Laurent series induced map coefficientwise ring homomorphism reduction mod p q-expansion | yes | reduction hom of a DVR extends to Laurent series over the residue field; Sage constructs induced morphisms between Laurent series rings from a base-ring hom | exactly the project's use case (ℤ((q)) → ZMod p ((q)) / ℂ((q)) descent) |
| 3  | WebSearch (named-after / aliases) | "Malcev-Neumann" OR "Hahn series" construction functor category of rings | yes | Hahn–Mal'cev–Neumann rings R((G,ω)); "Hahn series with real coefficients" is a functor (nLab); Ribenboim's "generalized power series" over strictly ordered monoids | history: Hahn 1907, Krull 1932, Mal'cev 1948 / Neumann 1949, Higman 1952, Ribenboim 1990s |
| 4  | ChatGPT MCP (gpt-5.4)             | standard form + generality + historical evolution of coefficientwise map on Hahn/Laurent series | yes | "standard but usually left implicit": coefficientwise map is a ring hom for any ring hom f, exponents in strictly ordered monoids, semiring coefficients suffice; libraries bundle the analog (`Polynomial.map`, `PowerSeries.map`, Coq `map_poly` for `{rmorphism}`) | confirms maximal generality = ZeroHom on underlying sets, ring hom once convolution ring structure exists |
| 5  | Local references                  | ls `.mathlib-quality/references/` | n/a | (directory absent) | recorded n/a — no references dir in this project |
| 6  | nLab                              | "Hahn series" (via channel 1/3 hits: ncatlab.org/nlab/show/Hahn+series) | yes | Hahn series over ordered abelian groups; the construction is treated functorially (surreals as fixed point of the Hahn-series functor) | clean abstract statement of the construction |
| 7  | nCatLab (categorical)             | same page as #6 | yes | functor perspective explicit ("Hahn series with real coefficients" functor) | nLab = nCatLab; no higher-categorical refinement relevant |
| 8  | Stacks Project                    | (checked via search sweep) | n/a | — | Hahn/Mal'cev–Neumann series are not a Stacks Project topic (Stacks covers formal completions, not ordered-exponent generalized series) |
| 9  | MathOverflow / Math.SE            | mathoverflow OR math.stackexchange Hahn series generalized power series ring homomorphism coefficients functorial | partial | no dedicated Q&A found; sweep surfaced arXiv 1710.07304 (factorisation theory for generalised power series) | absence of a Q&A consistent with "routine, unnamed" status |
| 10 | recent arXiv (last 5 yrs)         | "On Rings of Mal'cev-Neumann Series" (2404.18473, 2024); "Hahn series and Mahler equations" (2412.04928, 2024) | yes | active use of R((S;σ;τ)) with ring coefficients; exponent-side functoriality also noted (morphisms of ordered cancellative monoids with antichain fibers induce ring homs) | both coefficient-side and exponent-side functoriality are live; mathlib has only the exponent-side bundled (`embDomainRingHom`) |

### Literature summary (Phase 3)

Concept identified as: **functoriality of the Hahn (Mal'cev–Neumann / generalized
power) series construction in the coefficient ring**; specialization Γ = ℤ is
base change of formal Laurent series.
Sources agree on the standard form: yes — coefficientwise application of f, a ring
hom whenever f is; usually stated implicitly/routinely rather than as a named theorem.
Most general standard form: for Γ a strictly ordered cancellative commutative
monoid and f : R → S a homomorphism of (semi)rings, the coefficientwise map
R⟦Γ⟧ → S⟦Γ⟧ is a (semi)ring homomorphism.
Generality dimensions where the literature varies:
- exponents: ℤ (Laurent) → ordered abelian group (Hahn) → strictly ordered cancellative monoid (Ribenboim) → ordered non-abelian group (Mal'cev–Neumann)
- coefficients: field → commutative ring → ring/semiring
Disagreement with the literature: none — the user's form is a (Γ = ℤ, CommRing)
specialization of the standard form.

### Generality analysis — `Cox.laurentSeriesMapRingHom` (Phase 4a)

Literature-standard form: `HahnSeries.mapRingHom : (R →+* S) → R⟦Γ⟧ →+* S⟦Γ⟧`
for arbitrary ordered-cancellative exponent monoid Γ and (non-assoc) semiring
coefficients.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | exponent group (implicit via `LaurentSeries` = `HahnSeries ℤ`) | Γ = ℤ | `{Γ} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]` | yes — VERIFIED | all four field-proofs (`HahnSeries.map_zero/one/add/mul`) already hold at this generality |
| 2 | `[CommRing R]` | commutative ring | `[NonAssocSemiring R]` | yes — VERIFIED | commutativity/negation never used; `map_mul` needs only `→ₙ+*`, `map_one` provable by `ext g; simp [coeff_one, apply_ite f]` |
| 3 | `[CommRing S]` | commutative ring | `[NonAssocSemiring S]` | yes — VERIFIED | same |

### Generality verdict (Phase 4b)

**Verified weakening (mandatory): PASSED.** The generalised declaration was
compiled via `lean_run_code` against the project's mathlib pin with **zero
diagnostics**:

```lean
def HahnSeries.mapRingHom {Γ R S : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) : HahnSeries Γ R →+* HahnSeries Γ S where
  toFun F := F.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := by ext g; simp [HahnSeries.coeff_one, apply_ite f]
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
```

Also verified in the same run: the project's form is the definitional
specialization (`example ... : LaurentSeries R →+* LaurentSeries S :=
HahnSeries.mapRingHom f` typechecks at `[CommRing R] [CommRing S]`), and the
companion simp lemma `(mapRingHom f F).coeff g = f (F.coeff g)` remains `rfl`
at full generality. A Semiring-level variant using
`HahnSeries.map_one f.toMonoidWithZeroHom` (exact `PowerSeries.map` precedent)
also compiled clean.

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: 3 (Γ=ℤ → general Γ; CommRing R → NonAssocSemiring R; CommRing S → NonAssocSemiring S)
Proposed restatement: as above (`HahnSeries.mapRingHom`), with
`laurentSeriesMapRingHom f := HahnSeries.mapRingHom f` (or direct use) as the
Laurent specialization.
Cost of restatement: **CHEAP** — mechanical; the general proof already compiles.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream |
|---|----------|----------|------------------------|--------------------|
| 1 | typeclass preambles | no | already fully typeclass-driven | — |
| 2 | filters/nets vs sequences | no | purely algebraic; no topology | — |
| 3 | universal property vs construction | no | the bundled hom *is* the idiomatic packaging; a categorical `(HahnSeries Γ ·)` functor is not mathlib's pattern for `PowerSeries`/`Polynomial` either | — |
| 4 | bundled substructure | no | not a substructure situation | — |
| 5 | typeclass-hierarchy weakening | **yes** | CommRing → NonAssocSemiring (verified, Phase 4b) | matches `Polynomial.mapRingHom` (Semiring) and `MvPowerSeries.map` (Semiring); every semiring-level HahnSeries lemma now composes |
| 6 | higher-categorical generalisation | no | out of scope for HahnSeries files | — |
| 7 | concrete index generalises | **yes** | ℤ (LaurentSeries) → arbitrary `[IsOrderedCancelAddMonoid Γ]` (verified, Phase 4b) | unifies with `HahnSeries.embDomainRingHom` (exponent-side functoriality) giving both functorialities bundled; applies to `HahnSeries ℚ`, transseries-style iterated constructions, `PowerSeries` via `Γ = ℕ` |
| 8 | concrete-via-abstract (proof-body diagnostic) | **yes** | proof body uses only `HahnSeries.map_*` at general Γ — grep shows zero ℤ-specific or CommRing-specific steps; the abstract form is the real content, the Laurent form a specialization | the four `HahnSeries.map_*` lemmas stop being an "assembly kit" users re-bundle by hand |
| 9 | false-generalisation guard | **no false generalisation** | `HahnSeries ℤ R` with the ℤ-instance ring structure IS `LaurentSeries R` definitionally (`LaurentSeries` is notation-level `abbrev` for `HahnSeries ℤ`); verified: the specialization example typechecks with no coercion | safe |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — but it coincides with the literature-standard
generalisation (rows 5, 7, 8 all point at the same target `HahnSeries.mapRingHom`).
Cost: CHEAP. Mathlib downstream enabled: `Polynomial.mapRingHom`-style `_id`/`_comp`
functoriality lemmas, interoperation with `HahnSeries.embDomainRingHom`,
`HahnSeries.C` naturality (`map_C` already exists unbundled), and the
`ofPowerSeries` square (`mapRingHom φ ∘ ofPowerSeries = ofPowerSeries ∘ PowerSeries.map φ`
— flagged in the project's step7-api.md as a missing commuting square).
Real mathematical improvement: one canonical bundled witness of coefficient
functoriality instead of a four-lemma assembly kit every consumer re-bundles.

### Proof strategy — `Cox.laurentSeriesMapRingHom` (Phase 4.6)

| # | Question | Applies? | Idiomatic alternative | Cost |
|---|----------|----------|-----------------------|------|
| 1 | topology / ε-δ vs filters | no — no topology | — | — |
| 2 | element-wise vs point-free algebra | no — fields delegate directly to mathlib's `HahnSeries.map_*` lemmas | — | — |
| 3 | sequences vs nets | no | — | — |
| 4 | construction vs universal property | no — bundling, not construction | — | — |
| 5 | helper lemmas mathlib SHOULD have | **yes** — the missing helper IS this def (`HahnSeries.mapRingHom`); mathlib's four protected `map_*` lemmas are visibly an assembly kit awaiting the bundling | file it as the mathlib PR | — |

### Proof strategy verdict (Phase 4.6)

Current strategy: **MATHLIB-IDIOMATIC** (the four fields cite exactly the four
mathlib lemmas designed for this; identical shape to `MvPowerSeries.map`'s own
definition). Missing mathlib API: the bundled def itself — which is the PR.

### Diamond / defeq risk — `Cox.laurentSeriesMapRingHom` (Phase 4.5)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | plain `def`, not an `instance`; adds no typeclass-search path |
| 2 | Reducibility leak | none | sealed def (no `@[reducible]`); `toFun` is `F.map f`, so applied form reduces to mathlib's `map` — the `coeff` lemma being `rfl` (verified) shows the defeq is the intended one |
| 3 | Non-canonical unfolding | low | same unfolding behaviour as `MvPowerSeries.map` / `Polynomial.mapRingHom` (structure-literal RingHom whose `toFun` is the unbundled map); `simp`-normal form controlled by the `@[simp] rfl` coeff lemma |
| 4 | Instance priority collision | none | n/a — not an instance |
| 5 | Universe polymorphism | none | `Type*` throughout; verified the general def elaborates with unconstrained universes (compiled with `{Γ R S : Type*}`) |
| 6 | Coercion ambiguity | none | uses the standard `RingHom` FunLike coercion; no new `CoeFun` |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**. Top risks: none. No mitigations needed.

### Mathlib search-status: `Cox.laurentSeriesMapRingHom` (Phase 5)

[A] Lean-Finder   "bundled ring homomorphism mapping Hahn series coefficientwise along a ring homomorphism" — no bundled hit; returned `HahnSeries.embDomainRingHom` (exponent-side, wrong axis), unbundled `HahnSeries.map`, `HahnSeries.map_mul`, `HahnSeries.C`
[B] Loogle        `HahnSeries ?Γ ?R →+* HahnSeries ?Γ ?S` — **zero results** (the decisive probe: no ring hom of this shape exists in mathlib at all, on the coefficient axis or otherwise with matching Γ)
[C] LeanSearch    "ring homomorphism between Laurent series rings induced by a ring homomorphism on coefficients" — no hit; nearest: `PowerSeries.map` (the ℕ-exponent analog, bundled `→+*`), `Polynomial.toLaurent`, `RatFunc.laurentAux` (all different maps)
[D] Grep mathlib  `mapRingHom` over `Mathlib/RingTheory/HahnSeries/` + `LaurentSeries.lean` — zero hits; `map_map`/`map_id` also absent; `def map` in HahnSeries/Basic.lean:143 is the unbundled ZeroHomClass version; `map_zero` (Basic:148), `map_add` (Addition:128), `map_one` (Multiplication:103), `map_mul` (Multiplication:406), `map_C` (Multiplication:823), `map_single`, `map_sub`, `map_neg`, `map_smul` all unbundled
[E] Name pattern  `lean_local_search "mapRingHom"` — 8 mathlib `mapRingHom`s (`Polynomial`, `MonoidAlgebra`, `RatFunc`, `LocallyConstant`, `UniformSpace.Completion`, …) — none for HahnSeries/LaurentSeries; confirms both the gap and the naming convention

Searched for both: the user's Laurent/CommRing form AND the literature-standard
Hahn/NonAssocSemiring form (Loogle pattern covers both since `LaurentSeries` is
`HahnSeries ℤ`).

Concluded: **"not in mathlib (all 5 methods exhausted, plus the literature-standard
form)"** — mathlib has the unbundled `HahnSeries.map` + a four-lemma assembly kit,
and bundled `map`s for every neighbouring construction (`Polynomial.mapRingHom`,
`PowerSeries.map`, `MvPowerSeries.map`, `MonoidAlgebra.mapRingHom`), but no bundled
coefficient-map ring hom for HahnSeries/LaurentSeries. (`HahnSeries.embDomainRingHom`
is functoriality in the *exponent* group, not the coefficients.)

### Normal-form check (Phase 5.5a)

Equivalent formalisms: (i) bundled `→+*` whose `toFun` is `HahnSeries.map`
(current); (ii) keep only unbundled `map` + the four `map_*` lemmas (mathlib's
current state); (iii) an `AlgHom`/`RingEquiv` variant.
Canonical mathlib form for this idea: yes — the bundled-`→+*` pattern of
`MvPowerSeries.map` / `Polynomial.mapRingHom` (with `mapAlgHom` as a layer above).
Our statement is stated against the canonical form: YES — it is the canonical
form, instantiated at Γ = ℤ. RHS convention respected: yes (the `coeff` simp
lemma rewrites `(mapRingHom f F).coeff k` → `f (F.coeff k)`, pushing toward the
primitive form).

### Syntactic generality (Phase 5.5b)

Alternative restatements attempted: `RingHom.mk'` over a `MonoidHom`;
`{F : Type*} [RingHomClass F R S] (f : F)` parameterisation.
Chosen restatement: plain `(f : R →+* S)` structure literal — matches every
neighbouring `map`/`mapRingHom` in mathlib; `RingHomClass` parameterisation is
not used by `PowerSeries.map` either and would complicate the `rfl` coeff lemma.
Justification: call sites (e.g. `laurentSeriesMapRingHom (Int.castRingHom ℂ)`)
supply concrete `→+*` terms; nothing is easier to apply than the direct form.

### Superfluous-argument audit (Phase 5.5c)

| # | Argument / typeclass | Essentially used? | Notes |
|---|----------------------|-------------------|-------|
| 1 | `[CommRing R]` | NO | superfluous — `[NonAssocSemiring R]` suffices (verified) |
| 2 | `[CommRing S]` | NO | superfluous — `[NonAssocSemiring S]` suffices (verified) |
| 3 | `(f : R →+* S)` | yes | the data being bundled |
| 4 | Γ = ℤ (baked into `LaurentSeries`) | NO | any `[AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]` works (verified) |

### Statement-shape verdict (Phase 5.5d)

Normal form: OK. Syntactic generality: OK. Superfluous arguments: 3 to drop
(the two CommRing instances and the ℤ specialization).
Overall: **RESTATE-BEFORE-SHIP** — ship as `HahnSeries.mapRingHom` at the
verified general signature; the Laurent form is then free.

### Call sites — `Cox.laurentSeriesMapRingHom` (Phase 6.0)

Internal use count: **31** (grep, excluding the declaring file's own definition
lines). External-to-file callers: **2 distinct files**.

| Caller file:line | Usage pattern (excerpt) |
|------------------|-------------------------|
| XYin/PhD/Cox/Kronecker.lean:520,523 | `laurentSeriesMapRingHom (Int.castRingHom (ZMod p))` — mod-p descent of J-series |
| XYin/PhD/Cox/Kronecker.lean:535,540,554 | `laurentSeriesMapRingHom (Int.castRingHom ℂ)` — complex base change |
| XYin/PhD/Cox/Kronecker.lean:631,635,650,654 | `laurentSeriesMapRingHom (phaseEvalComplex p / phaseEvalMod p)` + `laurentSeriesMapRingHom_coeff` rewrites |
| XYin/PhD/Cox/Kronecker.lean:675–787 (10 more sites) | `Polynomial.map (laurentSeriesMapRingHom …)` naturality chains |
| XYin/PhD/Cox/LevelThree.lean:641,642,644,648,682 | descent hypotheses `laurentSeriesMapRingHom f T = T'` and `let L := laurentSeriesMapRingHom f` |
| (declaring file) LaurentPolynomialEvaluation.lean:34,47–61,72,83,92,95 | `_coeff` simp lemma + `bivariateSpecializeLaurent_map` machinery |

Inline-derivation grep: (none) — no site re-bundles `HahnSeries.map` + the four
lemmas by hand; all descent goes through this def. Pattern: **K ≥ 3, real API →
YES-\* leaning.**

### Composition check (Phase 6)

Can `Cox.laurentSeriesMapRingHom` be derived from mathlib in ≤3 chained calls?

Attempt 1: use an existing bundled hom directly — **fails**: Loogle
`HahnSeries ?Γ ?R →+* HahnSeries ?Γ ?S` returns zero results; there is nothing
to specialise or compose (`embDomainRingHom` fixes the coefficients and moves Γ;
`PowerSeries.map` lives on `HahnSeries ℕ` only via a ring *equiv* detour that
does not reach negative exponents).

Attempt 2: assemble via `RingHom.mk'` / structure literal from
`HahnSeries.map` + `map_zero` + `map_one` + `map_add` + `map_mul` — **partial**:
this is exactly the current 5-field definition. Per the composition heuristics,
a structure literal discharging four proof fields is a *definition*, not a
≤3-call composition; inlining it at 31 call sites would replicate the bundling
everywhere and lose the stable name that `Polynomial.map (laurentSeriesMapRingHom …)`
chains and the `= T'` descent hypotheses depend on.

Conclusion: **NOT-COMPOSABLE** (mathlib has the assembly kit, not the assembled hom).

## Verdict: `Cox.laurentSeriesMapRingHom`

**Category:** YES-but-generalise-first

**Evidence:**
- Literature search (Phase 3): 9-channel exhaustive protocol; concept = functoriality of the Hahn/Mal'cev–Neumann series construction in the coefficient ring (Hahn 1907 → Neumann 1949 → Ribenboim); standard at strictly-ordered-cancellative-monoid exponents and (semi)ring coefficients; nLab treats the construction as a functor.
- Generality analysis (Phase 4): **STRICTLY NARROWER** — 3 verified weakenings (Γ=ℤ → general Γ; both CommRing → NonAssocSemiring); the generalised def **compiled with zero diagnostics** against the project's mathlib pin, the Laurent/CommRing form typechecks as a direct specialization, and the coeff lemma stays `rfl`.
- Mathlib search (Phase 5): not in mathlib in either form (all 5 methods; Loogle type-pattern probe returned zero ring homs of shape `HahnSeries Γ R →+* HahnSeries Γ S`).
- Composition check (Phase 6): NOT-COMPOSABLE — mathlib ships the four `map_*` lemmas as an unassembled kit.
- Phase 4.5 risk: NONE. Phase 4.6: MATHLIB-IDIOMATIC. Phase 5.5: RESTATE-BEFORE-SHIP (the restatement *is* the generalisation).

**Rationale:**

Mathlib demonstrably wants this declaration: it already provides the bundled
coefficient-map ring hom for every neighbouring graded construction —
`Polynomial.mapRingHom`, `MvPowerSeries.map` / `PowerSeries.map` (both `→+*`),
`MonoidAlgebra.mapRingHom`, `RatFunc.mapRingHom` — and for HahnSeries it provides
the *exponent-side* bundled functoriality (`HahnSeries.embDomainRingHom`) plus the
four protected lemmas `HahnSeries.map_zero/map_one/map_add/map_mul` whose only
purpose is to let users discharge exactly the four fields of this bundling. That
four-lemma assembly kit with no assembled hom is the named gap. The project's form,
however, is a (Γ = ℤ, CommRing) specialization; the correct mathlib statement is
`HahnSeries.mapRingHom` at `[IsOrderedCancelAddMonoid Γ]` + `[NonAssocSemiring R/S]`,
and this generalisation is not speculative — it was compiled clean during this
assessment (Phase 4b), so the regeneralisation cost is CHEAP and mechanical.

Reason for the generalisation: **LITERATURE-WEAKENING** (Phase 4b: verified
strictly-narrower on 3 axes; the literature-standard form is the Hahn-level one)
— coinciding with MODERN-IDIOM rows 5/7/8 of Phase 4c.

Proposed restatement (verified compiling):
```lean
/-- Coefficientwise application of a ring homomorphism to Hahn series, bundled as a
ring homomorphism. -/
def HahnSeries.mapRingHom {Γ R S : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) : HahnSeries Γ R →+* HahnSeries Γ S where
  toFun F := F.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := by ext g; simp [HahnSeries.coeff_one, apply_ite f]
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom

@[simp] theorem HahnSeries.coeff_mapRingHom {Γ R S : Type*} [AddCommMonoid Γ]
    [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ] [NonAssocSemiring R]
    [NonAssocSemiring S] (f : R →+* S) (F : HahnSeries Γ R) (g : Γ) :
    (mapRingHom f F).coeff g = f (F.coeff g) := rfl
```

Estimated cost of regeneralisation: **CHEAP** (already compiles; the project then
replaces `laurentSeriesMapRingHom f` by `HahnSeries.mapRingHom f` at its 31 call
sites, or keeps a local abbreviation until the mathlib PR lands).

Mathlib downstream this enables:
- `mapRingHom_id` / `mapRingHom_comp` functoriality lemmas in the `Polynomial.mapRingHom` pattern (also wanted project-side per step4-computation.md item "add `_id`/`_comp`").
- The `ofPowerSeries` naturality square `mapRingHom φ ∘ ofPowerSeries ℤ = ofPowerSeries ℤ ∘ PowerSeries.map φ` (flagged missing in the project's step7-api.md).
- `HahnSeries.map_C` upgrades from an unbundled equation to `(mapRingHom f).comp C = C.comp f`.
- A `mapAlgHom` layer per the `MvPowerSeries.mapAlgHom` precedent, and interop with `embDomainRingHom` (both functorialities of R⟦Γ⟧ bundled).
- Downstream q-expansion arguments (reduction mod p of integral Laurent expansions — this project's Kronecker/LevelThree descent chains) become mathlib-native.

Proposed mathlib location:  `Mathlib/RingTheory/HahnSeries/Multiplication.lean`
(beside `HahnSeries.map_mul`/`map_C` and `embDomainRingHom`; `coeff_mapRingHom`
simp lemma alongside).
Proposed PR title:  "feat(RingTheory/HahnSeries): add `HahnSeries.mapRingHom`"
PR grouping:  ship with `mapRingHom_id`, `mapRingHom_comp`, and the
`ofPowerSeries` naturality square as one small PR; the project's
`bivariateSpecializeLaurent`* lemmas stay project-side (they are Cox-specific glue).

Next action: run `/generalise Cox.laurentSeriesMapRingHom` (target form above,
already verified), then `/cleanup XYin/PhD/Cox/LaurentPolynomialEvaluation.lean`
and `/pre-submit` before opening the mathlib PR.
