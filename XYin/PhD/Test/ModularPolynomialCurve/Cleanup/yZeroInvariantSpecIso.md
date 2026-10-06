# Single-declaration cleanup: `yZeroInvariantSpecIso`

Scope: only `ModularPolynomialCurveTest.AINTLIB.yZeroInvariantSpecIso`, at lines
152–155 of `AINTLIBDrafts/YZeroCoarseInvariantSpec.lean` (docstring at line 151).
This is Mode A of `mathlib-quality-for-codex:cleanup`, dispatched by the parent agent as
one bounded declaration worker. No Lean source change was necessary. The definition,
signature, universes, visibility and implementation remain byte-identical to the
start-of-worker snapshot `/private/tmp/yzeroInvariantSpecIso-cleanup-before.lean`.

The declaration identifies the **actual** AINTLIB `YZeroCoarse` with the spectrum of
the literal Borel-invariant subring of global regular sections on its actual full-level
representing scheme. It uses the preceding object-independent affine quotient API.
It does not assert that the full-level scheme or its section ring is a domain.

## Runtime, references and scope

The pinned external build uses AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`,
Lean `v4.35.0-rc3`, and mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`, in
`/private/tmp/xyin-y0-aintlib-work`, with
`ELAN_HOME=/private/tmp/xyin-y0-elan`. The target library has both
`autoImplicit=false` and `relaxedAutoImplicit=false`. The local XYin 4.30 environment
was not changed; these external drafts remain outside its import aggregate.

Read: cleanup `SKILL.md`; the Codex runtime contract; cleanup workflow Mode A and the
complete Phase 4 worker contract; `golfing-rules.md`, `proof-patterns.md`,
`mathlib-search.md`, `generalisation-patterns.md`, and `cleanup-gates.md` in full;
applicable definition, formatting, documentation, syntax and module sections of
`style-rules.md`; naming conventions; the normal-form, syntactic-generality and
documentation sections of `mathlib-review-stages.md`; buzz `SKILL.md`, its workflow,
and `profiling.md`. The Lean editing skill had already been read in this session.

Mode A skips the filewide structure/import rewriting phases. No shared
`.mathlib-quality` sidecar was written, as the parent explicitly scoped the report to
this file. No rename record was needed. Existing agent settings were preserved.

The Lean MCP is configured for the local XYin toolchain. It cannot be substituted for
the pinned external 4.35 module without changing that setup. The parent explicitly
authorized equivalent pinned compiler diagnostics and build evidence. Actual MCP
diagnostics for this external file were **not run** and are not called passed below.
Pinned compilation of the exact source and its strict target build supply the supported
equivalent checks; no declaration was left unelaborated.

## Full audit

| # | Check | Concrete result |
|---|---|---|
| 1 | LINT | No warnings or errors in the target declaration or target source during the pinned compiler pass or strict target build. The build replays pre-existing upstream warnings, which are outside this worker's scope. |
| 2 | HAVE SCAN | n/a: the two-line term body contains zero `have` declarations. |
| 3 | SET_OPTION | None in the declaration. No limit was added or raised. Temporary profiling options occur only in a separate file under `/private/tmp`. |
| 4 | SIMP SQUEEZE | n/a: there is no `simp` or tactic proof in this definition. |
| 5 | NAMING | `yZeroInvariantSpecIso` is descriptive lowerCamelCase for data: the object, invariant spectrum, and isomorphism are named. It contains none of `whomog`, `mvpoly`, `wt`, `soln`, `imp`, `eqn`, `thm`, numeric section prefixes, `multipass_`, numeric `_aux`, or a single-letter public name. `Spec` and `Iso` follow the existing categorical object/API vocabulary. No rename is needed. |
| 6 | LINE PACKING | Every signature line is measured in Unicode codepoints in the table below. The result-type group cannot fit on the keyword line: 27 + 1 + 85 = 113. No repack row remains. |
| 7 | BY PLACEMENT | n/a: there is no `by`; the definition directly supplies a term. |
| 8 | FORMAT | The body uses two-space indentation, with its continued argument line at four spaces; the result type uses the standard four-space continuation. No internal blank line, sequential tactics, `haveI`, or `letI` occurs in the declaration. |
| 9 | COMMENTS | No inline proof comments occur. The existing docstring is preserved verbatim. |
| 10 | DOCSTRING | Present, one sentence. It distinguishes a concrete identification of the actual upstream `YZeroCoarse` from the nearby generic relative quotient construction; no proof sketch needs relocation. The module prose and companion compatibility lemmas supply the usage context. |
| 11 | VISIBILITY | n/a: module file, with leading `module` and `@[expose] public section`; no visibility rewrite. The definition is used by downstream modules. |
| 12 | STRUCTURE | Body is two lines, with no conjunction in its result type, branch, local subproof, or repeated construction. Extraction would only re-wrap the generic construction already immediately above it. |
| 13 | MATHLIB | Five-method search completed; partial matches are `Scheme.isoSpec` and `IsAffineOpen.isoSpec`, which identify an affine scheme with its own section spectrum. They do not provide this actual moduli quotient/invariant-ring identification. See the search block below. |
| 14 | JUNK DEF | Retain: a named actual-object isomorphism is used in affine, projection, section-ring, over-base and j-coordinate APIs in multiple declarations/files. Inlining would make those public statements substantially less readable. |
| 15 | EXISTS LEMMA | n/a: this is neither an existential lemma nor a private single-use constructor witness. |
| 16 | SHOW vs CHANGE | n/a: no `show` occurs in the declaration. |
| 17 | PUSH_NEG | n/a: no negation tactic occurs. |
| 18 | GENERALISE | Every explicit or section hypothesis and the universe were inspected. No supported weakening was applied. The all-commutative-ring base is already preserved; the level conditions are the exact requirements for the actual upstream representing object. See the drop tests and literature analysis below. |
| 19 | INEQUALITY | No reversed inequality in the signature; the inherited hypothesis is already `3 ≤ (N : ℤ)`. No `_ge_`/`_gt_` name occurs. See the occurrence table below. |
| 20 | NORMAL-FORM | Canonical bundled categorical isomorphism `actual quotient ≅ Spec actual invariant ring`. A proposition asserting mere existence, a ring equivalence to an unspecified ring, or an identity with `Spec Γ(Y₀)` would lose this concrete map and the projection compatibility. |
| 21 | SYNTAX-GEN | OK: implicit arbitrary base `R`, explicit level/proof arguments, and the actual target ring permit `.hom`, `.inv`, `Spec.map`, and section pullback to compose directly. No equivalent restatement is easier for the demonstrated call sites. |
| 22 | IMPORT-FANOUT | n/a: no production import was added or changed. |
| 23 | CASTS | 0 dropped / 0 kept as cross-type / 0 kept as load-bearing in the diff, because the diff is empty. The inherited natural-to-integer level comparison and natural-to-base-ring unit hypothesis are genuine type changes and remain upstream parameters. |
| 24 | INSTANCE-NAME | n/a: this declaration is a definition, not an instance; no instance is introduced by its body. |

Issues to fix: none. Refactoring needed: none within this bounded declaration.

## Five-method mathlib search status

| Method | Query/evidence | Result |
|---|---|---|
| A — Lean-Finder | “An affine quotient scheme by a finite group is isomorphic to the spectrum of the invariant subring of its global regular sections”; “affine scheme quotient by finite group spectrum invariant ring” | Hits included affine-space `isoOfIsAffine`, `homOverEquiv`, and `AffineScheme`; no exact actual-quotient identification. |
| B — Loogle | `"isoSpec"` | Partial hits for affine spectra, including `primeSpectrumOrderIsoSpec` and `basicOpenIsoSpecAway`; none instantiate AINTLIB's moduli quotient. |
| C — LeanSearch | “quotient affine scheme finite group spectrum invariant subring” | `AffineScheme`, a subgroup quotient instance, and `Representation.quotientToInvariants`; no exact scheme-quotient statement. |
| D — pinned mathlib source | Exact `yZeroInvariantSpecIso`; invariant/affine/quotient combinations in `Mathlib/AlgebraicGeometry`; `isoSpec` | Exact-name search completed untruncated with exit 1 and no hits. `Scheme.isoSpec` and `IsAffineOpen.isoSpec` are useful partial APIs. The actual `relQuotient` engine belongs to AINTLIB. |
| E — name-pattern MCP | `lean_local_search` for `isoSpec` | Returned actual `Scheme.isoSpec` and `IsAffineOpen.isoSpec`. The search index reported warming, so this is evidence of presence of partial hits, not a claim of exhaustive absence. |

Auxiliary variants checked: affine scheme `isoSpec`, affine-open `isoSpec`, basic-open
`isoSpecAway`, prime-spectrum isomorphisms, invariant-ring quotient descriptions, and
representation quotient-to-invariants. The common-equivalents lookup does not identify
a theorem over the AINTLIB-specific moduli datatype.

Search classification: **partial match**. Retain the actual specialization, already
implemented by the generic `AffineInvariantQuotient.invariantSpecIso`; do not replace
its target with `Spec Γ(Y₀)` and then hide the needed invariant-ring comparison.

## Generalisation status

| Parameter/hypothesis | Mechanical weakening/drop test | Resolution |
|---|---|---|
| Universe `u` | No fixed small universe is imposed; `R : CommRingCat.{u}` and schemes retain that universe. | Already polymorphic. |
| `R : CommRingCat` | Candidate non-Noetherian or non-domain base is already allowed. A noncommutative ring or semiring does not preserve the current `Spec`/scheme datatype or the moduli problem. | Retain arbitrary commutative ring; no domain, reducedness, characteristic or Noetherian assumption added. |
| `N : ℕ` | Changing the level to an integer or abstract group changes the represented moduli datatype. The preceding quotient lemma already isolates the group-independent argument. | Retain actual upstream natural-number level. |
| `[NeZero N]` | With this class omitted, the actual `YZeroCoarse ...` application reports `failed to synthesize NeZero N`. Mathematically `3 ≤ (N : ℤ)` implies nonzero, so the class is redundant mathematical information. Eliminating it requires choosing a derived instance before elaborating the upstream moduli target, or normalizing the upstream API, rather than simply weakening this definition. | Preserve the exact upstream class binder for transparent actual-object specialization. A redesign of the level-data API would be a separate change, not a new quotient theorem. |
| `hN : 3 ≤ (N : ℤ)` | Replacing it with `2 ≤ (N : ℤ)` reports an application type mismatch against the actual `YZeroCoarse` argument. At smaller levels the chosen full-level representing construction is different; declaring an arbitrary coarse object would no longer be the same specialization. | Retain; no claim that the mathematical coarse curve requires level ≥3 intrinsically. This is a limitation of the upstream construction being instantiated. |
| `hinv : IsUnit (N : R)` | The actual representing object and quotient parameters directly use the invertible-level hypothesis. Removing or weakening it would require a different integral moduli construction; no existing unit-free representation API was found. | Retain; do not substitute a field or characteristic-zero assumption. |

The negative tests use the actual compiled primary module, not a surrogate definition.
Their expected failures are recorded in
`/private/tmp/yzeroInvariantSpecIso-hypothesis-probe.log`. They are candidate-rejection
evidence, not a failing production gate. Positive `#check` of the actual signature and
generic construction and `#print axioms` also occur in that probe.

Mathematical generalisation search used primary references:

- [Stacks 39.23, tag 03BE](https://stacks.math.columbia.edu/tag/03BE): affine finite flat
  groupoids yield an invariant-ring/equalizer description of the affine quotient.
- [Stacks 39.24, tag 03JD](https://stacks.math.columbia.edu/tag/03JD): invariant affine
  neighbourhoods for suitable finite locally free groupoids enable broader gluing.
- [Stacks 83.8, tag 04A9](https://stacks.math.columbia.edu/tag/04A9): the invariant-function
  condition is meaningful for more general groupoids and algebraic-space quotients.

Inference from these references: the abstract quotient comparison has useful extensions
to suitable finite flat groupoids beyond finite constant groups. This does not weaken
the level-data requirements of this actual AINTLIB specialization. The generic API
already separates the quotient mathematics from this actual object. No configured
mathematical second-opinion MCP was available; that optional literature channel was not
run and is not reported as a completed review.

## Line packing

The signature has exactly two physical lines. Lengths below are Unicode codepoints,
including leading indentation. A result-type group is kept intact when testing whether
it can follow the declaration colon. A `#check @yZeroInvariantSpecIso` at
`format.width := 100` is additionally recorded in the hypothesis probe; for a
definition this reference is optional under the worker contract.

| Signature line | Chars | Next signature group | Arithmetic | Action |
|---|---:|---|---|---|
| 152: `def yZeroInvariantSpecIso :` | 27 | Complete result type and `:=` (85 chars excluding its continuation indentation) | 27 + 1 + 85 = 113 > 100 | ok |
| 153: actual quotient `≅ Spec ... :=` | 89 | No next signature line; body follows | n/a | ok |

Initial and final tables coincide; no repack is necessary. Both body lines are also
below 100 codepoints.

## Inequality orientation scan

| # | Location | Original | Rewrite | Rename? |
|---|---|---|---|---|
| — | Entire signature | n/a: zero `≥` or `>` | none | No `_ge_`/`_gt_` name |
| 1 | Inherited `hN` | `3 ≤ (N : ℤ)` | Already smaller-side-left | none |

## Golfing pass: every rule

No tactic script should replace a direct data construction merely to invoke automation.
The following rule-by-rule applicability checks are against the complete two-line term
body, not a selected fragment.

| Rule | Status and reason |
|---|---|
| 1.1 Remove `by exact` | n/a: body is already the bare constructor API term. |
| 1.2 Remove `by rfl` | n/a: no `by` or `rfl`. |
| 1.3 `rw` + `exact` → `rwa` | n/a: no rewriting. |
| 1.4 `simp` + `exact` → `simpa using` | n/a: no simplification. |
| 1.5 Remove trailing `rfl` | n/a: no `rfl`. |
| 1.6 Anonymous constructor | n/a: the existing generic API supplies a bundled isomorphism directly. |
| 1.7 `apply` + `exact` | n/a: no tactic application. |
| 1.8 `by_contra!` | n/a: the definition has no propositional contradiction proof. |
| 1.9 Eta-reduce lambdas | n/a: no lambda. |
| 1.10 Inline single-use `have` | n/a: no `have`. |
| 1.11 `refine` + `fun` | n/a: no quantified proof or refinement. |
| 1.12 Remove redundant `show` | n/a: no `show`. |
| 1.13 `have` + projections → `obtain` | n/a: no intermediate pair or conjunction. |
| 1.14 Merge `rw` | n/a: no `rw`. |
| 1.15 Unsqueeze terminal `simp only` | n/a: no `simp`. |
| 1.16 Squeeze nonterminal `simp` | n/a: no `simp`. |
| 1.17 Dot notation | n/a: the function's first explicit argument is a scheme action, not a quotient isomorphism receiver. The qualified generic namespace makes the provenance useful; shortening it requires unrelated namespace changes. |
| 1.18 `<\|` for trailing parentheses | n/a: the only parentheses select necessary structure/object arguments; there is no nested terminal function call to simplify. |
| 1.19 `push_neg` → `push Not` | n/a: no negation tactic. |
| 1.20 Inline trivial existential helper | n/a: no existential helper. |
| 2.1 Whole-proof `grind` | n/a: the target is a specific isomorphism datum, not a proposition; its chosen maps matter downstream. |
| 2.2 Delete tactics before `grind` | n/a: no tactics. |
| 2.3 `simpa` consolidation | n/a: no proof steps to consolidate. |
| 2.4 `fun_prop` | n/a: no analytic/property goal. |
| 2.5 `positivity` | n/a: no sign goal. |
| 2.6 `gcongr` | n/a: no monotonicity goal. |
| 2.7 `lia`/`omega` | n/a: constructing a categorical isomorphism is not integer arithmetic. |
| 2.8 `aesop` | n/a: direct data construction already supplies the intended maps; proof search would add cost and obscure them. |
| 2.9 `norm_num`/`norm_cast` | n/a: no arithmetic or cast normalization in the body. |
| 2.10 `decide` | n/a: a scheme isomorphism datum is not a decidable proposition. |
| 2.11 `field_simp; ring` | n/a: no rational-function identity. |
| 2.12 `linear_combination` | n/a: no linear equality goal. |
| 2.13 `wlog` | n/a: no symmetric cases. |
| 2.14 Collapse `calc` | n/a: already a direct term with no `calc`. |
| 2.15 `<;>` | n/a: no multiple goals. |
| 3.1 `erw` → `rw` | n/a: no `erw`. |
| 3.2 Analytic tactics → `fun_prop` | n/a: no such tactic. |
| 3.3 `omega` → `lia` | n/a: no arithmetic tactic. |
| 3.4 `rcases ... with rfl` | n/a: no `rcases`. |
| 3.5 Register automation lemmas | n/a: this is a datum construction. Its companion projection/section equalities, rather than the definition itself, form the rewriting API; changing their attributes is outside this declaration. |
| 3.6 `simp_all` | n/a: no simplification context. |
| 3.7 Remove `maxHeartbeats` | Already satisfied: no override occurs. |

Step back: the complete body is already one application of the best matching generic
API. Introducing `by exact`, `exact?`, an alternate arbitrary `Scheme.isoSpec`, or a
fresh constructor proof would add scaffolding or lose the actual projection maps.
There is no shorter proof strategy whose implementation preserves the demonstrated API
more clearly. No rule was applied merely to produce a nonempty diff.

## Verification gates

The actual target invocation was:

```text
ELAN_HOME=/private/tmp/xyin-y0-elan lake build AINTLIBDrafts.YZeroCoarseInvariantSpec
```

It exited **0**, ending “Build completed successfully (9376 jobs)”. The log is
`/private/tmp/yzeroInvariantSpecIso-cleanup-build.log`. It replays the built target and
records the actual declaration's axiom check as
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` or custom axiom occurs.

The supported equivalent compiler pass of the exact source, with the module setup
generated by Lake, also exited 0. Its log is
`/private/tmp/yzeroInvariantSpecIso-profile-before.log`.

| Gate | Result | Evidence |
|---|---|---|
| `lake_build_file` | pass | Actual invocation above, exit 0; target has no warning/error. |
| `definition_protected` | pass | Whole production source equals the start-of-worker snapshot byte-for-byte. |
| `theorem_statement_protected` | pass | No source diff and no theorem signature changed. |
| `structure_gate` | pass | Two-line body, no conjunction or branch. |
| `naming_gate` | pass | Descriptive lowerCamelCase; all forbidden strings/patterns explicitly scanned. |
| `line_packing_gate` | pass | Complete two-row codepoint table; 113-character merge exceeds the limit. |
| `inequality_orientation_gate` | pass | Occurrence table covers the signature and inherited hypothesis; zero reversed inequalities. |
| Trust | pass | Actual declaration has only the standard three axioms. |
| No limit raise / scaffolding | pass | Snapshot equality; no production profiling or limit option. |
| Cumulative breakage | pass for this worker | Empty source diff cannot alter call sites; the strict combined j/invariants target had also passed independently with 9379 jobs. |
| Pinned diagnostics equivalent | pass | Exact production source successfully elaborated by pinned Lean using its Lake module setup. |
| Actual external-file MCP diagnostics | not run | MCP remains configured for XYin 4.30; parent authorized pinned CLI equivalent. This row is not called an MCP pass. |

Overall applicable diff/build gates: **pass**. A full default-package rebuild was not
run by this single-declaration worker; it is outside Mode A. The parent had already
completed the actual coarse-space baseline with 9375 jobs.

## Buzz: bounded single-declaration performance check

Budget: 1000ms. The exact-source module profile has total own-file elaboration **188ms**
and total own-file type checking **82.4ms**. Thus the target is already bounded above
by 188ms of elaboration in that run. The separately reported **109s import time** is
the pinned environment's large cached import graph, not target-declaration elaboration.
It is not used as a declaration performance measurement.

Single-target trace/heartbeat measurement compiled successfully, exit 0, using the same
Lake-generated module setup. The temporary probe
`/private/tmp/xyin-y0-aintlib-work/YZeroInvariantSpecIsoTimingProbe.lean` contains an
otherwise identical copy of the production source, with a temporary
`Mathlib.Util.CountHeartbeats` import and a trace/heartbeat wrapper only around the
target declaration. Its log is `/private/tmp/yzeroInvariantSpecIso-target-profile.log`.
The actual target `Elab.command` node is **26.848ms**; kernel checking is **3.469ms**;
the deterministic counter reports **300 heartbeats** against the ordinary maximum of
200000. The outer measuring wrapper takes 33.549ms, and is not mistaken for the
definition itself. There are no errors or warnings in this clean final probe.

| Declaration | Location | Target elaboration | Heartbeats | Over 1000ms? |
|---|---|---:|---:|---|
| `yZeroInvariantSpecIso` | Primary file:152 | 26.848ms, including its docstring | 300 | No |

**FAST BOARD — nothing over 1000ms.** The trace shows ordinary elaboration of the existing
generic API term and a small kernel check; no performance root cause requiring a fix
was found. No deeper targeted trace, optimization, same-issue propagation or post-fix
resweep is needed, since the board has one declaration and no fix. A first temporary
probe had a docstring/wrapper parser-placement error; it was corrected and rerun to
exit 0. Neither that failed probe nor its timing is used as gate evidence.

No optimization was proposed and no new limits, public instances, global attributes or
scaffolding were introduced. Because no source fix is being made, there is no claimed
before/after speedup or fabricated post-fix heartbeat delta.

### Buzz-pass status

- Scope: `AINTLIBDrafts/YZeroCoarseInvariantSpec.lean`, `yZeroInvariantSpecIso` only.
- Budget: 1000ms per declaration; measured declaration: 26.848ms / 300 heartbeats.
- Result: **FAST BOARD**, 0 slow declarations; no edits or deferrals.
- `maxHeartbeats` raises removed: 0; added: 0. Deferred: none.
- Statements/definitions protected: production file byte-identical to snapshot.
- No limit raises or profiling scaffolding in retained source.
- Strict build: exit 0, 9376 jobs; exact-source compiler pass: exit 0.
- Re-sweep after fixes: n/a, because no fix or source change was made.
- Flagged global changes: none. Performance-motivated style exceptions: none.

## Result and phase receipt

Before: 4 declaration lines; after: 4; saved: 0. Audit issues found: 0; fixed: 0;
refactoring deferred: 0. Rules applied: none; all applicability checks are recorded.
Renames queued: none. Comments preserved: docstring 1/1, inline comments none.
Refactoring needed: none.

| Phase 4 step | Status |
|---|---|
| 1 references | completed, including the full required five-reference set |
| 2 full audit | all 24 items recorded |
| 2.5 search | all five methods, partial-match status and index limitation recorded |
| 2.6 generalisation | every hypothesis checked; actual negative probes and primary-source analysis recorded |
| 2.7 packing | every signature line measured |
| 2.8 inequalities | occurrence table recorded |
| 3 golfing | every rule 1.1–1.20, 2.1–2.15, 3.1–3.7 given a status |
| 4 reflection | direct generic application retained for concrete-map API |
| 5a diagnostics | pinned compiler equivalent passed; actual MCP not run |
| 5b gates | actual strict build and all applicable diff gates passed |
| 6a rename queue | n/a: no rename required; shared sidecar untouched |
| buzz | completed: single-target trace and heartbeat count, 26.848ms / 300 hb, FAST BOARD; exact-source compiler/build clean |

This receipt concerns only this declaration. It does not claim normality, a modular
polynomial relation, normalization of its plane curve, target-j descent, or analytic
uniformization of `Y₀(N)`.
