# Single-declaration cleanup: smooth algebras over a domain are reduced

Scope: `ModularPolynomialCurveTest.AINTLIB.ReducednessDescent.isReduced_of_smooth_over_domain`
in `AINTLIBDrafts/YZeroCoarseReduced.lean`, cleanup Mode A / Phase 4, followed by the
single-declaration buzz pass. File-wide cleanup phases were not invoked. No shared sidecar was
modified.

The proof now finishes by embedding the algebra into a product of reduced principal
localizations, using the existing `isReduced_of_injective` API. This replaces the hand-written
nilpotent-element argument. The mathematical signature, name, universes, and conclusion are
unchanged. No helper, import, global instance, or fine-ring domain assumption was added.

The body decreased from 25 to 20 lines, including the relocated mathematical signpost.
Every other declaration and all file content outside this declaration (including its docstring) are
byte-identical to the before snapshot.

## Setup and baseline

- AINTLIB: `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`.
- mathlib: `300d0e535721bc098547106fc297d8ba2a63f6bb`.
- Lean: `leanprover/lean4:v4.35.0-rc3`.
- Actual isolated package: `/private/tmp/xyin-y0-aintlib-work`.
- Parent's unified baseline: exit 0, 9400 jobs, three standard axioms only, no `sorryAx`.
  This built the ten retained bridge modules and their actual dependencies; it was not a claim
  that all unrelated AINTLIB projects were built.
- Strict module setup: `.lake/build/ir/AINTLIBDrafts/YZeroCoarseReduced.setup.json`, with
  `autoImplicit = false` and `relaxedAutoImplicit = false`.
- LSP initialization on the exact isolated file timed out after 30 seconds. The supported
  compiler fallback was used for diagnostics, probes, and profiling; no LSP/environment
  configuration was changed.
- The final target-module build, `lake build AINTLIBDrafts.YZeroCoarseReduced`, exited 0:
  9393 jobs, target module 40 seconds including import loading. There are zero warnings/errors
  originating in this owned file. Upstream warning replay is not described as zero warnings.

Before snapshot and evidence logs are in `/private/tmp/xyin-smooth-reduced-cleanup/`:
`Before.lean`, `focused.diff`, `after-build.log`, `benchmark.log`, `generalisation.log`, and
`search-golf-final.log`. The retained final source SHA-256 is
`e0031ac120a0273284cc0c0e19ddb58f046026f896b1e2d10a0c8d513c843424`.

## Full declaration audit

| Item | Finding and action |
|---|---|
| 1. Lint | No diagnostics in the target's baseline/final range, using the strict compiler fallback. |
| 2. Have scan | Complete inventory below; proof-local typeclass facts remain explicitly typed. |
| 3. Set option | None in the retained declaration; no limits were raised. |
| 4. Simp squeeze | No `simp` calls in the target. The former `change` / `rw [map_zero]` exit was removed by the injection API. |
| 5. Naming | `isReduced` follows the existing mathlib predicate name; `_of_smooth_over_domain` states the precise hypothesis. No forbidden abbreviation, numbering, `_auxN`, or single-letter public name. No rename is needed. |
| 6. Line packing | Signature packed; exhaustive before/after width tables below. |
| 7. By placement | `by` remains on the final signature line. |
| 8. Format | Two-space proof indentation, no empty proof lines, one tactic per line, no `haveI` / `letI`. Local contradiction hypothesis `H` became `h`. |
| 9. Comments | No old inline comments existed. The local-chart proof strategy was relocated from the docstring to one inline signpost. |
| 10. Docstring | Now states the result and explains that the target algebra may be disconnected; proof strategy is in the proof comment. |
| 11. Visibility | n/a: module-system file with `@[expose] public section`; visibility scaffolding was preserved. |
| 12. Structure | Body 20 lines, local chart block eight lines, span-top block five lines; no conjunction in the statement and no branch over ten lines. No helper extraction or decomposition flag needed. |
| 13. Mathlib | Five-method search and compiled generic-route probe below. Existing product reducedness and localization injectivity replace the manual constructor exit. |
| 14. Junk def | n/a: theorem, not a definition. |
| 15. Exists lemma | n/a: public reducedness theorem; its local chart witness uses substantive étale data rather than a trivial single-use witness helper. |
| 16. Show/change | No `show`; the old `change` step disappeared with the manual nilpotent exit. |
| 17. Push neg | None. |
| 18. Generalise | Every parameter audited; thirteen cloned-signature weakening attempts recorded below. Original signature preserved. |
| 19. Inequality | No `≥` or `>` in the signature or hypotheses; scan table below. |
| 20. Normal form | Canonical class `_root_.IsReduced A`; no custom predicate or equivalence lattice added. |
| 21. Syntactic generality | Typeclass `Algebra.Smooth R A` composes with the existing scalar-algebra API. A `RingHom.Smooth` forwarding lemma is not needed in this scope. |
| 22. Import fanout | n/a: no imports added or changed. |
| 23. Casts | Zero redundant ascriptions/coercions introduced in the diff. The existing explicit `p : PrimeSpectrum A` is load-bearing for the maximal-ideal construction. |
| 24. Instance name | No instance declaration added. Both proof-local class facts remain anonymous. |

### Have scan

| Location in final file | Binding | Use and action |
|---|---|---|
| 66 | `hloc ... := by` | Contains the local-chart proof and is used by `choose`; keep proof content. |
| 71 | anonymous `Algebra.IsStandardEtale ... := he` | Installs the class required to infer étaleness at the following theorem application; retain the explicitly typed local instance. It is not a removable named expression alias. |
| 75 | `hspan ... := by` | Contains the prime/maximal-ideal cover argument; keep proof content. |
| 80 | anonymous `∀ c : Set.range f, IsReduced ...` | Supplies the class family required by product reducedness; use `Set.forall_subtype_range_iff.mpr hf` instead of manually destructing each range witness. Retain the explicitly typed local instance. |

### Signature width table

Widths are Unicode codepoints. Reference: the final `#check @benchmark_after` at
`format.width = 100` prints independent universes `Type u_1` and `Type u_2`, and the same
class arguments/conclusion as the retained target.

| Before signature line | Width | Next complete signature token | Arithmetic | Action |
|---|---:|---|---|---|
| 62 | 39 | `(R A : Type*)` (13) | 39 + 1 + 13 = 53 ≤ 100 | repack |
| 63 | 70 | `[Algebra.Smooth R A]` (20) | 70 + 1 + 20 = 91 ≤ 100 | repack |
| 64 | 51 | no next signature line | n/a | ok |

| Final signature line | Width | Next complete signature token | Arithmetic | Action |
|---|---:|---|---|---|
| 62 | 92 | `[Algebra R A]` (13) | 92 + 1 + 13 = 106 > 100 | ok |
| 63 | 65 | no next signature line | n/a | ok |

### Inequality scan

| Location | Original | Rewrite | Rename |
|---|---|---|---|
| Entire signature and hypotheses | No `≥` / `>` occurrences | n/a | n/a |

## Mathlib search-status

| Method | Queries | Result |
|---|---|---|
| A. Lean-Finder | “A smooth commutative algebra over an integral domain is reduced” | Partial hits: `Algebra.FormallyUnramified.isReduced_of_field`, multivariate-polynomial reducedness, geometric reducedness. Remote index is not the pinned-source authority. |
| B. Loogle | `Algebra.Smooth, IsReduced` | No hits. |
| C. LeanSearch | “smooth algebra over reduced ring is reduced” | Partial hits: unramified-over-field reducedness, `Algebra.Smooth.flat`, geometric reducedness. |
| D. Pinned source | Full target/helper names; `smooth.*isReduced`, `isReduced.*smooth`, smooth/reduced variants, localization reducedness | No direct target replacement. Found `isReduced_ofLocalizationMaximal`, local standard-étale charts, product `IsReduced`, and localization-product injectivity. Full-name searches were untruncated. |
| E. Local name search | `isReduced_of` | Source hits include the above and AINTLIB's localization-at-prime domain descent. Symbol index returned `unavailable`; its empty portions were not counted as indexed absence. |

Auxiliary variants checked: `isReduced_of_injective`, `isReduced_ofLocalizationMaximal`,
`isReduced_localizationPreserves`, `Algebra.FormallyUnramified.isReduced_of_field`,
`Algebra.isReduced_of_isGeometricallyReduced`, smooth flatness, and
`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`.
Common-equivalents table: no discrete/finiteness/separation/analysis bucket applies.

The compiled `SearchGolfProbe.lean` imports only pinned mathlib and the independently proved
étale helper, not the smooth target. Its final guards try `infer_instance`, `exact?`, `grind`,
`aesop`, and `simp`, and explicitly check that each leaves the goal unsolved before using the
retained proof. It exited 0 with only the three standard axioms. Five expected scratch-only
unreachable-tactic warnings refer to `done` after a tactic that already fails; six unused-tactic
warnings refer to diagnostic `trace` labels. The five successful
guards prove that those tactics did not close the target. `apply?` was inspected separately: it supplies partial reducedness characterizations,
and its implementation intentionally calls `admitGoal` after suggestions. It is therefore excluded
from the clean guard probe and is not counted as a closed proof.
Final probe completion is recorded in the gate evidence below.

Conclusion: no direct replacement was found at this pin. Keep the local theorem and use
mathlib's standard-étale chart, product reducedness, injectivity, and reducedness descent APIs.
The early idea of extracting a generic local-cover helper was unnecessary after the product
API removed the long constructor branch.

## Generalisation status

Candidate substitutions were made in temporary clones, because the parent's scope explicitly
protects this declaration's mathematical signature. `GeneralisationProbes.lean` is intentionally
a negative experiment: its exit 1 consists of the listed expected rejection diagnostics. None
of these failing clones is retained as library source or used by a proved theorem.

| Parameter | Use | Candidates tested | Verified result |
|---|---|---|---|
| `R : Type*` | Base ring for smoothness and polynomial charts | Universe audit; dropping R cannot express the dependent class binders | Already independent `Type u_1`; no weakening required. |
| `A : Type*` | Target ring and prime spectrum | Universe audit; dropping A cannot express the conclusion | Already independent `Type u_2`; no weakening required. |
| `[CommRing R]` | Ring/algebra/smooth API | Drop; `Ring R`; `CommSemiring R` | Rejected at clone lines 35, 60, 84: missing `Semiring R`, `CommSemiring R`, `CommRing R`, respectively. |
| `[IsDomain R]` | Domain polynomial base for étale helper | Drop; `NoZeroDivisors R`; `IsReduced R` | Rejected at clone lines 117, 141, 165: missing `IsDomain (MvPolynomial (Fin n) R)`. This diagnoses the current proof, not mathematical impossibility of the reduced-base generalisation. |
| `[CommRing A]` | Spectrum/localization/smooth API | Drop; `Ring A`; `CommSemiring A` | Rejected at clone lines 180, 204, 228: missing `Semiring A` or `CommRing A`. |
| `[Algebra R A]` | Smoothness and local-chart scalar structure | Drop; `Module R A` | Rejected at clone lines 252, 276: missing `Algebra R A`. |
| `[Algebra.Smooth R A]` | Finite presentation and smoothness at every prime | Drop; `Algebra.FormallySmooth R A` | Rejected at clone lines 306, 330: missing `Algebra.FinitePresentation R A`. A property at only one prime cannot give this global conclusion. |

No small signature weakening was applied. The concrete-object inversion diagnostic is n/a:
the theorem is already abstract over rings and algebras; it contains no concrete moduli object.

### Literature search

Queries: `site:stacks.math.columbia.edu smooth morphism reduced base reduced source` and
`site:stacks.math.columbia.edu etale reduced ring reduced algebra`. Relevant primary findings:

- [Stacks 033B](https://stacks.math.columbia.edu/tag/033B): a smooth algebra over any reduced
  base is reduced. This is strictly broader than the current domain-base statement.
- [Stacks 034E](https://stacks.math.columbia.edu/tag/034E): reducedness is local in the smooth
  topology; its proof points to 033B for ascent.
- [Stacks 025O](https://stacks.math.columbia.edu/tag/025O): reducedness for étale homomorphisms
  of Noetherian local rings. This is a relevant local variant, not the most general formulation.

Configured mathematical second-opinion tool: n/a; none was exposed in this session. The
earlier independent agent review checked this actual proof route, but is not reported as a
configured external mathematical consultation.

Flagged future generalisation: replace the base-domain requirement by `IsReduced R`, together
with a genuinely general étale/reduced-base ascent lemma. This needs a different base argument
and is not applied in this unchanged-signature cleanup. Handling the zero base could separately
weaken `IsDomain R` to `NoZeroDivisors R`; the current fraction-field helper requires nontriviality.

## Golfing-rule pass

| Rule | Status |
|---|---|
| 1.1 `by exact` wrapper | n/a: none. |
| 1.2 `by rfl` | n/a: none. |
| 1.3 `rw` + `exact` | Old `rw [map_zero]` exit replaced entirely by injection API. |
| 1.4 `simp` + `exact` | n/a: no simp chain. |
| 1.5 trailing rfl | n/a: none. |
| 1.6 constructor compression | Removed the manual class constructor via `isReduced_of_injective`. |
| 1.7 apply + exact | Replaced the manual localization-injection exit by direct theorem application. |
| 1.8 by_contra + push_neg | n/a: contradiction block has no negation-pushing step. |
| 1.9 eta reduction | n/a: no eta-expanded lambda. |
| 1.10 single-use have | No removable named expression alias; explicitly typed local class facts are required for inference. |
| 1.11 apply + intro | Old constructor/intro block removed; no applicable residual chain. |
| 1.12 redundant show | n/a: none. |
| 1.13 have + projections | Already uses `obtain`; no residual projection alias. |
| 1.14 merge rw | n/a: no consecutive rewrites. |
| 1.15 terminal simp only | n/a: none. |
| 1.16 nonterminal simp | n/a: none. |
| 1.17 dot notation | Existing `Set.forall_subtype_range_iff.mpr` is used; no reducible composition boilerplate. |
| 1.18 trailing parentheses | n/a: remaining parentheses delimit the ring map and injectivity proof. |
| 1.19 push_neg | n/a: none. |
| 1.20 trivial existential helper | n/a: no such declaration. |
| 2.1 whole grind | Compiled guard confirms it does not close the target. |
| 2.2 tactics before grind | n/a: no retained grind. |
| 2.3 simpa consolidation | The old goal-normalization exit was superseded by the product-injection API. |
| 2.4 fun_prop | n/a: no analytic/topological function-property goal. |
| 2.5 positivity | n/a: no positivity goal. |
| 2.6 gcongr | n/a: no monotonicity/order goal. |
| 2.7 lia / omega | n/a: the finite polynomial index has no arithmetic goal. |
| 2.8 aesop | Compiled guard confirms it does not close the target. |
| 2.9 norm_num / norm_cast | n/a: no numeric/cast goal. |
| 2.10 decide | n/a: reducedness of an arbitrary ring is not a finite computable proposition. |
| 2.11 field_simp / ring | n/a: no rational identity. |
| 2.12 linear_combination | n/a: no ring/ring_nf exit. |
| 2.13 wlog | n/a: no symmetric case branches. |
| 2.14 collapse calc | n/a: no calc. |
| 2.15 multiple goals | n/a: no repeated goal family. |
| 3.1 erw | n/a: none. |
| 3.2 continuity / measurability | n/a: none. |
| 3.3 omega → lia | n/a: none. |
| 3.4 rcases rfl | n/a: no substitution pattern. |
| 3.5 automation registration | Considered; no global instance/automation attribute added in this one-declaration proof-only scope. |
| 3.6 simp_all | n/a: none. |
| 3.7 heartbeat limit | No override to remove; none added. |

Step-back reflection: direct typeclass/search/automation routes were tried. Partial nilradical
or radical characterizations merely restate the remaining mathematics. A localization-at-maximal
route would introduce additional localization-tower setup. The existing principal-open chart
argument followed by one product injection is clear and uses the pinned API directly.

## Buzz pass — one declaration, budget 1000 ms

Outcome: **FAST-BOARD**. The declaration was already under budget; no performance-driven source
edit, trace option, limit change, global attribute, or instance was introduced.

| Version | Command elaboration | Heartbeats | Over budget |
|---|---:|---:|---|
| Before | 205.791 ms | 2912 | no |
| After | 181.758 ms | 4408 | no |

Both versions were checked in the same temporary module context with the actual strict setup,
`trace.profiler`, and `#count_heartbeats in`. The profiler's theorem-command nodes are used, not
the wrapper time or import-loading time. Heartbeats increased; the small wall-clock difference
is not claimed as a deterministic speedup. The final-state measurement is comfortably outside
the ±25% budget boundary, so the workflow does not require a borderline remeasurement.

Dominant categories remain ordinary elaboration/kernel work: before value elaboration 128.758 ms,
kernel 66.067 ms; after value elaboration 97.215 ms, kernel 78.745 ms. No slow declaration required
diagnosis/fix/propagation. Scope contains one declaration; same-issue propagation is n/a.

Heartbeat raises removed: 0; added to retained source: 0. Deferrals: none. Big performance
changes: none. Profiling wrappers exist only in the temporary benchmark file, not the retained
source.

Two temporary probe repairs are recorded transparently: an initial appended `pp.width` option
was invalid and corrected to `format.width`; and the initial guards around `apply?` accepted
its admitted partial-suggestion exit. The pinned implementation
`Lean/Elab/Tactic/LibrarySearch.lean` was read: it calls `admitGoal` after printing suggestions.
`apply?` is therefore inspected separately and removed from the clean proof probe; other final
guards explicitly run `done` to require a closed proof.
Neither issue affected a retained proof or a successful library build.

## Gates and phase checklist

| Gate | Result and evidence |
|---|---|
| `lake_build_file` | Pass: exact pinned `lake build AINTLIBDrafts.YZeroCoarseReduced`, exit 0, `after-build.log`. |
| `definition_protected` | Pass: all definitions/abbreviations and all code outside this declaration are byte-identical to `Before.lean`. |
| `theorem_statement_protected` | Pass: complete signature tokens are identical; only line packing changed. Buzz made no retained-source edits after that cleanup. |
| `structure_gate` | Pass: body 20 lines, no statement conjunction, no branch over ten lines. |
| `naming_gate` | Pass: mathematical name with no forbidden pattern; no rename required. |
| `line_packing_gate` | Pass: both final signature lines covered by the measured table, no repack row. |
| `inequality_orientation_gate` | Pass: exhaustive scan has zero reversed inequalities. |
| Compiler diagnostics | Pass: zero owned warnings/errors from the final target module. LSP fallback is explicitly documented. |
| Axiom audit | Pass: all ten printed results have exactly `[propext, Classical.choice, Quot.sound]`. |
| No limit / scaffolding / trust change | Pass: no new option, heartbeat wrapper, `sorry`, `admit`, `axiom`, or `native_decide` in retained source. |
| Cumulative consumers | The actual fine/coarse and complex-specialization consumers in the same file all compile. Parent's final joint ten-module build remains a separate receipt after all sibling edits. |
| Generic-route/golf probe | Pass: final strict probe exit 0, five successful guards, exactly the three standard axioms; scratch-only expected unreachable warnings are documented above. |

### Worker result

Before: 25 proof lines; after: 20; saved: 5. The signature also decreased from three to two
lines. Applied changes: existing injection API in place of the constructor/normalization exit,
subtype-range class-family API, signature packing, local hypothesis naming, and docstring/comment
separation. Four audit issues fixed; no in-scope refactoring left. Comments preserved: none
originally inline; one proof-strategy phrase relocated from the docstring. Renames queued: none.
Future generalisation flags are listed above and were not applied.

- [✓] Step 1: required reference documents read completely; applicable style references read.
- [✓] Step 2: all 24 declaration-audit items recorded.
- [✓] Step 2.5: all five search methods and the compiled generic-route check recorded.
- [✓] Step 2.6: every parameter, candidate diagnostic, universe audit, and literature status recorded.
- [✓] Width artifact: every signature line measured before and after.
- [✓] Inequality artifact: complete zero-occurrence scan recorded.
- [✓] Step 3: every golfing rule has a status.
- [✓] Step 4: alternative proofs/search/automation considered and tested where applicable.
- [✓] Step 5a: strict compiler fallback gives clean diagnostics on the retained source.
- [✓] Step 5b: actual build, signature/definition protection, structure/naming/width/orientation gates pass.
- [✓] Step 6a: no renames; no shared sidecar changes.
- [✓] Mode A buzz: measured final state under 1000 ms, no deferral or retained scaffolding.

All local gates pass. The parent will supply the separate final joint-build receipt after the
other owned edits. No shared sidecar was touched.
