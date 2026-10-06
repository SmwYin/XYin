# Single-declaration cleanup: `yZeroSourceJ`

Status: scoped cleanup, strict target build and before/after definition-identity checks completed.
The parent owns the final affected joint build; its result is recorded separately below.
Scope: only `ModularCurves.YZeroCoarseJ.yZeroSourceJ` in `AINTLIBDrafts/YZeroCoarseJ.lean`.
Mode A; file-wide Phases 0–3/5 are outside this assignment. The parent supplied the strict
module baseline and its standard-three-axiom receipt. No shared sidecar is edited.

I have read golfing-rules.md, proof-patterns.md, mathlib-search.md,
generalisation-patterns.md, and cleanup-gates.md in full. Also read Mode A/Phase 4,
applicable style/naming/review-stages sections, and buzz workflow/profiling.

## Completed change and definition protection

Removed the duplicate local affine-structure instance and expressed the definition directly
with `coarseJMap`. Packed the signature and explained the chosen Borel quotient in its
one-sentence docstring. Name, binder types/order/implicitness, universe, target scheme,
noncomputability and visibility stay the same. Compiled `rfl` comparisons before and after the edit show that
the new expression denotes the same chosen descent, rather than an alternative quotient map.
This is authorized cleanup of this data definition; no generalisation will be applied.

## 24-item audit

| Item | Concrete finding/action |
|---|---|
| 1 LINT | LSP initialization timed out after 30s; exact pinned setup compiler and Lake are the supported substitute. Strict target and positive-fixture compilers completed with zero target warnings. |
| 2 HAVE SCAN | Only L86 `haveI : IsAffineHom ...`; no `by`; used implicitly once at `coarseJMap`. Existing `fullObject_structMap_isAffineHom` has the same type through an abbrev. Removal compiled using the existing imported instance; no local instance is retained. |
| 3 SET_OPTION | None in this declaration; introduce no limits or options. |
| 4 SIMP SQUEEZE | n/a: no simp call. |
| 5 NAMING | Data-valued `yZeroSourceJ` is descriptive lowerCamelCase, with no forbidden scheme number, abbreviation or single-letter public name. No rename needed. |
| 6 LINE PACKING | Original widths 68/29/68; pack to 94/65; required measured table below. |
| 7 BY PLACEMENT | Original `by` is on the signature line; direct term removes it. |
| 8 FORMAT | Remove `haveI`, use a two-space term body, no empty body line or tactic chain. |
| 9 COMMENTS | No inline proof comment exists; no signpost removed. |
| 10 DOCSTRING | Explain descending the universal curve’s j map through the chosen Borel quotient, which distinguishes the concrete entrance from generic `coarseJMap`. |
| 11 VISIBILITY | n/a: module file with `@[expose] public section`; no visibility rewrite. |
| 12 STRUCTURE | Original body four lines, final body one; no conjunction, cases or branches; below both headline and ordinary bounds. |
| 13 MATHLIB | Five-method receipts below. Partial Weierstrass matches and existing generic descent; retain the concrete API definition. |
| 14 JUNK DEF | Keep: multiple independent callers and projection/base/X/chart API equations. The named definition fixes the actual chosen AINTLIB quotient. It is not a private single-use convenience. |
| 15 EXISTS LEMMA | n/a: data definition, no private existential lemma. |
| 16 SHOW vs CHANGE | n/a: neither occurs. |
| 17 PUSH_NEG | n/a: no negation tactic. |
| 18 GENERALISE | Every parameter considered below; no mathematical/signature changes applied. |
| 19 INEQUALITY | `3 ≤ (N : ℤ)` already has smaller side left; no reversed inequality. |
| 20 NORMAL-FORM | Standard categorical `⟶`, `Spec (.of (Polynomial R))` j-line and upstream actual `YZeroCoarse`; no alternate predicate/equivalence network. |
| 21 SYNTACTIC-GENERALITY | Targeting the actual `YZeroCoarse` makes the projection equations directly applicable. Generic representability/group quotient construction is already `coarseJMap`. Nat bound convenience would need coordinated API work; not done here. |
| 22 IMPORT-FANOUT | No added/removed/reordered import. |
| 23 CASTS | Zero dropped; two retained cross-type coercions: `N : ℤ` for upstream level bound and `N : R` for level invertibility. No new `↑` or type ascription. |
| 24 INSTANCE-NAME | n/a: this declaration creates no named instance; the local anonymous instance is removed, the primary module’s existing instance is not edited. |

## Mathlib search-status

| Method | Query and observed receipt |
|---|---|
| A Lean-Finder | “A j-invariant morphism on the coarse modular curve, obtained by descending the j morphism from the universal elliptic curve”: `WeierstrassCurve.j`, `map_j`, `ofJ`, `ofJ_j`, `ofJNe0Or1728_j`. |
| B Loogle | `WeierstrassCurve.j` and application-pattern `WeierstrassCurve.j _`: j value and `j_eq_zero*` statements; no direct actual-quotient candidate in these results. |
| C LeanSearch | “The j-invariant of an elliptic curve defines a scheme morphism invariant under isomorphism which descends to a coarse moduli quotient”: `j`, j congruence, `exists_variableChange_of_j_eq`, `ofJ`; unrelated `SlashInvariantForm.quotientFunc`. |
| D pinned source rg | Untruncated full-name/variant scan for `yZeroSourceJ`, `coarseJMap`, `YZeroCoarse`, affine source instance; exact source has Weierstrass j/map_j and downstream generic quotient descent. Actual curve constructor is external AINTLIB. |
| E name-pattern tool | `coarseJMap` in pinned project finds generic map and `coarseJMap_comp_base`; tool says `index: unavailable`, so this is source fallback, not a ready LSP index. |

Auxiliary variants: `map_j`, `jSection_naturality`, `jMap_naturality`,
`coarsePr_existsUnique_lift`, `gammaFullNaive_isAffineHom_structMap`,
`fullObject_structMap_isAffineHom`. Common-equivalents buckets: none applies.
Conclusion: partial match; build on existing mathlib Weierstrass j and the existing
AINTLIB/local generic descent API. No unsupported theorem-absence claim is made, and no
new theorem is introduced. The compiled positive region verified direct construction, implicit instance inference
and `directSourceJ = baselineSourceJ` by `rfl`, with zero errors/warnings and std3
axioms for both data definitions. The subsequent intentional-failure region verifies
the weakening tests; it is not a green whole-module gate.

## Generalisation status

| Parameter | Class / actual use | Candidate and reason | Verification / disposition |
|---|---|---|---|
| `{R : CommRingCat.{u}}` | Bundled commutative base; both `Spec R` and Polynomial R | Dropping loses the base; RingCat/CommSemiRingCat would change scheme geometry rather than safely weaken a hypothesis. Universe already polymorphic. | Source type dependency; no applicable safe parent-class weakening. |
| `N : ℕ` | Discrete level, ZMod N, Borel subgroup | Drop would lose the object; arbitrary ordered type changes the modular level construction. | Source type dependency, not a safe generalisation. |
| `[NeZero N]` | Required by upstream constructors/Borel | Literal drop-test; mathematically redundant given the bound, but the constructor still requires a class. | Verified literal drop fails at fixture L32–33 (`NeZero N`). The bound mathematically implies nonzero, so deriving the class remains a coordinated API restatement; not applied inline. |
| `hN : 3 ≤ (N : ℤ)` | Fine representability and exact chosen quotient type | Drop; weaken to `0 ≤ (N : ℤ)`; Nat-bound equivalent is possible convenience, not mathematical weakening. | Verified weakening fails at L36–37 (expected `3 ≤ ↑N`, got `0 ≤ ↑N`); literal witness drop fails L44 (unknown hN). Lower levels would require a different geometric construction. |
| `hinv : IsUnit (N : R)` | Fine moduli representation and exact target choice | Drop; weaken to `N ≠ 0` in the ring. | Verified nonzero replacement fails at L40–41 (expected `IsUnit ↑N`); literal witness drop fails L46 (unknown hinv). Nonzero is not a unit in general CommRingCat. |
| Universe `u` | Scheme and coefficient ring live in matching universe | Already arbitrary `u`; no Type-zero restriction to weaken. | No change. |

Inversion check: satisfied by existing generic `coarseJMap` for an affine represented
moduli problem and a finite group action. This declaration supplies the actual
full-level representation and Borel action. No repeated abstract proof is left here.
Literature: [Stacks 072K](https://stacks.math.columbia.edu/tag/072K) describes the
j-invariant as a natural morphism from the elliptic-curve moduli stack to the affine
line over the integers, supporting the generic geometric layer rather than restricting
to complex points. Level-specific constructor hypotheses belong to AINTLIB’s fine
representability, not to the mathematical j-invariant itself.

Refactoring needed (not applied): a coordinated API can derive `[NeZero N]` from hN,
and expose a Nat-bound convenience wrapper. Extending actual coarse construction to
N=1,2 is separate moduli work. No approval question or shared rename/learnings entry is
created for these observations.

## Signature widths (codepoints, including indentation)

| State / line | Width | First next signature token | Arithmetic | Action |
|---|---:|---|---|---|
| before L83 | 68 | `(hinv : IsUnit (N : R))` (23) | 68+1+23=92 ≤100 | repack |
| before L84 | 29 | `YZeroCoarse` (11) | 29+1+11=41 ≤100 | repack |
| before L85 | 68 | none: signature ends | terminal | ok |
| after L84 | 94 | `YZeroCoarse` (11) | 94+1+11=106 >100 | ok |
| after L85 | 65 | none: signature ends | terminal | ok |

## Inequality scan

| Location | Occurrence | Action | Rename |
|---|---|---|---|
| hN | `3 ≤ (N : ℤ)` | already oriented; no `≥` or `>` in signature | n/a |

## Golfing-rule status

| Rule | Status / specific reason |
|---|---|
| 1.1 Remove by-exact wrapper | Applicable after redundant have removal: use the single `coarseJMap` term. |
| 1.2 Remove by-rfl | n/a: no rfl in this definition. |
| 1.3 rw+exact → rwa | n/a: no rewrite. |
| 1.4 simp+exact → simpa | n/a: no simplification. |
| 1.5 trailing rfl after simp | n/a: neither tactic. |
| 1.6 constructor+exact → tuple | n/a: no constructor. |
| 1.7 apply+exact → term | n/a: no apply; direct exact-to-term simplification handled by 1.1. |
| 1.8 by_contra! | n/a: no propositional contradiction. |
| 1.9 eta-reduce lambda | n/a: no lambda. |
| 1.10 inline single-use have | Applicable: remove redundant anonymous instance, rather than reintroduce its proof as an explicit argument. |
| 1.11 apply+intro → refine+fun | n/a: no intro/apply. |
| 1.12 redundant show | n/a: no show. |
| 1.13 have projections → obtain | n/a: no local tuple projection. |
| 1.14 merge rw | n/a: no rw. |
| 1.15 unsqueeze terminal simp | n/a: no simp only. |
| 1.16 squeeze nonterminal simp | n/a: no simp. |
| 1.17 dot notation | n/a: `coarseJMap` has no useful receiver that would improve this explicit specialization; actual representation and Borel hom remain its two arguments. |
| 1.18 use <| | n/a: both parenthesized arguments must be delimited; replacing either with <| would absorb the other argument. |
| 1.19 push Not | n/a: no push_neg. |
| 1.20 inline private existential lemma | n/a: no such lemma. |
| 2.1 grind whole proof | n/a: this is a data-valued chosen morphism; propositional closure is not a replacement preserving the specific value. |
| 2.2 remove tactics before grind | n/a: no grind. |
| 2.3 simpa consolidation | n/a: there is no proposition/equality subgoal or simp. |
| 2.4 fun_prop | n/a: no function-property proposition. |
| 2.5 positivity | n/a: no ordered scalar goal. |
| 2.6 gcongr | n/a: no inequality goal. |
| 2.7 lia/omega | n/a: no arithmetic proof in the body. |
| 2.8 aesop | n/a: proof search for a Scheme.Hom would not specify the same chosen quotient descent; use the known API term. |
| 2.9 norm_num/norm_cast | n/a: no numerical calculation or cast-normalization proof. |
| 2.10 decide | n/a: constructing the noncomputable chosen morphism is not a decidable proposition. |
| 2.11 field_simp/ring | n/a: no scalar equation or field denominator. |
| 2.12 linear_combination | n/a: no ring equation. |
| 2.13 wlog | n/a: no symmetric case split. |
| 2.14 calc→term | n/a: no calc; the whole body is directly a term. |
| 2.15 <;> | n/a: no multiple tactic goals. |
| 3.1 erw→rw | n/a: no erw. |
| 3.2 continuity/measurability→fun_prop | n/a: neither tactic. |
| 3.3 omega→lia | n/a: no omega. |
| 3.4 rcases-with-rfl | n/a: no rcases. |
| 3.5 register automation lemma | n/a: a concrete data definition adds no proof rule, and no automation API change is needed. |
| 3.6 simp_all | n/a: no simp_all. |
| 3.7 remove maxHeartbeats | n/a: no override exists. |

Step-back conclusion: the known generic descent term is the shortest expression which
retains the specified mathematical value. The `inferInstance` probe targets exactly the
only scaffolding; the `rfl` probe checks preservation of the old choice. No terminal
proof search or alternate morphism construction is introduced.

## Verification and scoped buzz

LSP receipt: `Failed to start Lean language server ... initialize timed out after 30.0s`.
Two initial shim invocations produced no output and were interrupted (exit130).
Both the direct installed v4.35.0-rc3 Lake baseline and the direct Lean baseline
with the existing strict setup exited0, printed standard-three axioms and no warnings.
Their import times were 91.4s and 59.2s; the first whole-module elaboration was 142ms,
so no declaration can be near the 1000ms budget. Do not mistake dependency loading for
yZeroSourceJ elaboration. The second baseline was already running when its redundancy
was established; no further baseline repetition is requested. Only one compiler check runs at a time after the
parent’s resource-coordination instruction. Other chats’ larger Lean tasks remain
untouched. Benchmark wall-clock is subject to concurrent external load; no timing
improvement is claimed before measurements.

## Scoped buzz receipt (budget 1000ms)

| Declaration variant | Trace command time | Heartbeats | Budget result |
|---|---:|---:|---|
| Original body, `baselineSourceJ` | 30.962ms | 508 | FAST |
| Direct body, `directSourceJ` | 20.130ms | 475 | FAST |

Exact single-process fixture command used the installed pinned `bin/lean`,
`/private/tmp/YZeroSourceJCleanupHB.lean`, its matching `/private/tmp` setup JSON,
and scoped trace wrappers with `-Dtrace.profiler.threshold=0`. The fixture was moved
out of the library directory before the final target build.
The trace wrappers were scoped to the two data declarations. Trace collection has
substantial overhead; the original untraced profiled module elaborated in 142ms total,
with its source-j portion around a few ms. These are measurements, not a claim of
significant speed improvement. The separate untraced positive fixture reports 302 heartbeats for the old body
and 280 for the direct body; the trace-instrumented 508/475 counts include trace overhead.
Both comparisons show a small reduction in work, not a substantive speedup claim. No timing is near the 1000ms threshold.

FAST BOARD — nothing over 1000ms. Buzz stops before optimization; there is no SLOW
root-cause ticket, no attempt to manufacture an optimization, and no propagation target
in this single-declaration scope. No maxHeartbeats raise removed or added; no big buzz
API change. Temporary profiler/count wrappers exist only in /private/tmp fixtures,
never in retained source. LSP profiling is unavailable following the initialization
failure, so direct exact-pin profiler is the supported replacement.

Positive-only receipt `/private/tmp/yZeroSourceJ-cleanup-positive.log`: exit0, no warnings,
302/280 heartbeats, both variants std3. In addition to the instance probe and the
variant-to-variant rfl, two examples compare each variant directly with the actual
imported `yZeroSourceJ`; both are `rfl`. This is the explicit preservation receipt for
the actual chosen map, not merely a comparison with an unverified mock.

Negative-test receipt `/private/tmp/yZeroSourceJ-cleanup-HB.log`: no errors before L30, both
variants std3, rfl and inferInstance accepted. Exactly ten diagnostics occur at the
intentional failing checks L32–46: four NeZero inference errors, two lower-bound type
mismatches, two invertibility type mismatches, and two missing witness identifiers.
The fixture therefore exited1 intentionally. It is not presented as a green build. Compiler error recovery may print synthetic
`sorry` terms after failed #check expressions; no sorry appears in the fixture source,
no failed candidate is retained, and no error-recovered declaration is used downstream.
Temporary files have been moved out of the isolated project's library directory to
/private/tmp so future library globs cannot pick up these intentional failure tests.

## Final scoped gates

The parent’s pre-edit strict baseline completed all ten retained targets, exit0, 9400 jobs,
with only the standard three axioms. The approved production edit was then applied to
exactly the declaration/docstring span. The signature token sequence is identical;
line packing changes signature bytes but no binder name, type, order, implicitness,
universe, target, visibility or noncomputability. Every other declaration is byte-identical.

`lake build AINTLIBDrafts.YZeroCoarseJ` completed exit0 (9378 jobs), with zero target
warnings. The target’s printed chart, global-section, naturality, base, pullback, actual
coarse and explicit complex-instance declarations all have only
`propext`, `Classical.choice`, `Quot.sound`; specifically this includes `yZeroSourceJ`.
Receipt: `/private/tmp/yZeroSourceJ-cleanup-build.log`. Cached upstream warning replay
was outside the target and was not edited.

After rebuilding the actual public module, the positive-only fixture compiled exit0 again,
with zero warnings. Both the former explicit-instance body and the new direct body are
`rfl` equal to the actual newly imported definition. Receipt:
`/private/tmp/yZeroSourceJ-cleanup-after-positive.log`. The final untraced profiler sweep
reported 8.32ms for the whole fixture’s elaboration, no declaration reached the 100ms
profiler threshold, and heartbeat counts remained 302/280. Its 18.3s import time is
excluded from the declaration budget.

Naming, declaration visibility, signature widths, inequality orientation and structure
are checked above. The one-line term has no branches, conjunctions or tactic blocks.
No imports changed, and no `sorry`, new axiom, `native_decide`, option override,
profiler trace or heartbeat-count scaffolding is retained. The direct existing API term
is the final simplify pass: further automation or a wrapper would add structure without
improving the definition. Data-value preservation is established by the actual imported
`rfl` fixtures, not merely by equal signatures or equal theorem statements.

Scoped gates are green. The parent’s final joint build, covering this edit together with
its separate ComplexPoints change, is pending its own receipt; this report does not
claim an unrun cumulative build passed.

## Reusable preservation probe (core of compiled positive fixture)

The exact positive fixture at `/private/tmp/YZeroSourceJCleanupHB.lean` compiled exit0
against the pinned public module and strict setup before and after the edit. The core
below omits the count/profiler wrappers and their utility import for presentation. It
deliberately preserves the former body as a separate value to test the actual chosen
map. Keep it as a standalone probe rather than adding another project module or public
wrapper API.

```lean
module
public import AINTLIBDrafts.YZeroCoarseJ
@[expose] public section
open AlgebraicGeometry CategoryTheory ModularCurves ModularCurves.YZeroCoarseJ
universe u
variable {R : CommRingCat.{u}}
example (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R)) :
    IsAffineHom (xFullNaive (R := R) N hN hinv).structMap := inferInstance
noncomputable def baselineSourceJ (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) :
    YZeroCoarse (R := R) N hN hinv ⟶ Spec (.of (Polynomial R)) := by
  haveI : IsAffineHom (xFullNaive (R := R) N hN hinv).structMap :=
    ModuliProblem.gammaFullNaive_isAffineHom_structMap N hN hinv
      (xFullNaiveRepr (R := R) N hN hinv)
  exact coarseJMap (xFullNaiveRepr (R := R) N hN hinv) (gammaHAut R N (borel N))
noncomputable def directSourceJ (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) :
    YZeroCoarse (R := R) N hN hinv ⟶ Spec (.of (Polynomial R)) :=
  coarseJMap (xFullNaiveRepr (R := R) N hN hinv) (gammaHAut R N (borel N))
example (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R)) :
    directSourceJ N hN hinv = baselineSourceJ N hN hinv := rfl
#print axioms baselineSourceJ
#print axioms directSourceJ


example (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R)) :
    baselineSourceJ N hN hinv = yZeroSourceJ N hN hinv := rfl
example (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R)) :
    directSourceJ N hN hinv = yZeroSourceJ N hN hinv := rfl
```
