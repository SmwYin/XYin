# Point bridge review

Review scope: `YZeroCoarseFineComplexPoints.lean`, the upstream-reuse patch in
`FieldGeometricJ.lean`, `YZeroCoarseMarkedComplexCurves.lean`, and
`YZeroCoarseConstantAxis.lean`, followed by the separately authorized generic model-j,
source-j-surjectivity, and divisor-generator deltas recorded below.
This pass is read-only for Lean source; only this report
is written. No competing build, profiler, source edit, or environment change was started.

Starting snapshot UTC: **2026-10-03T23:19:17.201165+00:00**. Complete copies and the hash manifest are in
`/private/tmp/xyin-point-bridge-review-start`.

| Module | Lines | Maximum width | SHA-256 |
| --- | ---: | ---: | --- |
| YZeroCoarseFineComplexPoints.lean | 257 | 95 | `1ba0db31b8273ae6a42f37e45dcb2ef1e3642718d491ad721d5e83225c02c9b3` |
| FieldGeometricJ.lean | 75 | 88 | `992743897a441e98d94799d3b12cc134a0d99ce6c24014a35fa7bc4974a4a9a3` |
| YZeroCoarseMarkedComplexCurves.lean | 157 | 99 | `f8bb25f74e3b3d10868794d02e2c09be90f56738361570602733213116c28bda` |
| YZeroCoarseConstantAxis.lean | 249 | 91 | `26bcd959a0837f8ed2651f40f44911b6a6b252052b3822b668fc1ad463460d77` |

## Simplify pass — current point bridge snapshot

Outcome: PASS-THROUGH for all four final reviewed source snapshots and the separately
reviewed model-j, source-j-surjectivity and divisor-generator deltas below. The parent's
final cumulative import-graph build is a separate project-level verification step.
Review: local fresh read-only review of other owners' source. A new independent child
reviewer was unavailable because all four collaboration slots were occupied. The root
and other owners retain their independent checks; this report does not claim another
new subagent was spawned.

Issues identified by `$mathlib-quality-for-codex:simplify`:
- None in the reviewed mathematical statements and proofs.
- No uncompiled proof-golf or import-demotion suggestion is presented as a verified fix.

Fixes applied by `$mathlib-quality-for-codex:simplify`:
- None — read-only pass-through.

Files modified:
- `Cleanup/PointBridgeReview.md` only. Temporary snapshot copies were also saved.

Verification:
- Read the complete four module snapshots and the actual upstream types below.
- Read the actual MarkedComplexCurves and ConstantAxis strict logs, including every
  printed axiom result; both have no warning/error lines. Their owners report exit 0.
- No new compiler invocation was made by this reviewer, as directed by the parent.
- Exact current FieldGeometricJ reuse patch: parent-reported strict Lake leaf exit 0,
  4151 jobs; this reviewer read its six standard-three-axiom checks and zero own
  warning/error lines in `/private/tmp/yzero-field-model-reuse-build.log`.
- Cumulative downstream build receipt remains the parent's serialized final check.

Unresolved or reverted:
- None in the reviewed code; no source fix or revert. The parent's later cumulative
  build and the further Γ₀/Φ mathematical work are outside this read-only pass.

## Mathematical and API review

### Fine complex points

The fine-point subtype is the literal morphism `Spec ℂ → fullObject.base` with its
triangle to the identity of `Spec ℂ`. Both conversion directions respect the actual
coefficient map; neither equips the same abstract ring with an unrelated complex algebra.
`Spec.map_preimage` and `Spec.preimage_map` prove the inverse laws after the actual
`isoSpec` triangle is cancelled. Projection compatibility uses the same chosen `yZeroPr`
and `yZeroInvariantSpecIso` as the invariant-ring bridge.

`fullComplexPointEllObj` pulls back the actual universal elliptic curve along the point.
`pullbackAlongπ` has the given point as its base morphism, and the chosen representation's
`homEquiv` supplies a genuine full marking on this pullback. The displayed pullback
formula uses `homEquiv_eq`; no assumption that a supplied function is a moduli object is
inserted. The point's base condition gives the native object's original complex structure.

The source-j triangle is the compiled descent triangle followed by `jMap_naturality`.
The scalar coordinate theorem uses `ΓSpecIso_inv_naturality` and the actual pullback of
`Polynomial.X`. Its explicitly typed `Spec ℂ → Spec (ℂ[X])` alias handles the opaque
native base without expanding `jPolynomialHom`; that is a sound elaboration boundary,
not a new mathematical assumption. The chosen field Weierstrass model is elliptic and
its algebraic j computes this exact coarse source-j coordinate.

### Field model and upstream reuse

Pinned upstream `EllipticCurve/GlobalChartOverField.lean:46` proves
`nonempty_localPresentation_top` for **arbitrary `Field k`**; at line 56,
`localPresentationTop` chooses the same top-open presentation type. The retained
`fieldTopAffineOpen` is definitionally that affine open. Both wrappers now use those
existing declarations directly; no second atlas-restriction argument remains.

At upstream line 62, `globalWeierstrassModel` is a curve over `Γ(Spec k, ⊤)`, whereas
`fieldWeierstrassModel` is over `k`. Mapping coefficients through `ΓSpecIso.hom.hom`
is consequently necessary. The ellipticity instance and j equation are valid for any
chosen top presentation. There is no characteristic-zero, algebraic-closedness, full-level,
or coarse assumption in this layer.

The upstream-reuse change can change the noncomputably chosen chart relative to the
old independent atlas choice. It preserves all displayed types and j-value conclusions;
it does not claim that the two old/new chosen Weierstrass coefficient tuples are
literally equal. Keeping the small wrappers presently preserves the accepted API names.
This is an intentional compatibility boundary, not a claim that upstream lacks a chart.

### Marked native complex curves

`complexFullMarking` is exactly `gammaFullNaiveProblem.obj` on the supplied native curve.
The classifier is `xFullNaiveRepr.homEquiv.symm α`, so its base morphism gives an actual
fine point. Upstream `EllObj.isoPullbackAlong` is a pointed cartesian comparison
isomorphism over the identity; the module does not substitute j equality for a curve
isomorphism. The marking-transport proof has the correct contravariant direction and
uses `homEquiv_comp` plus `toPullbackAlong_pullbackAlongπ` before the inverse law.

The source-j morphism and scalar value agree with the **given** curve, by pointed j
naturality, independently of the chosen marking. The exact upstream theorem
`exists_isNaiveFullLevel_of_isAlgClosed` at `Moduli/LevelThreeTorsor.lean:293` assumes
`Field k`, `IsAlgClosed k`, `[NeZero N]`, and `(N : k) ≠ 0`; it supplies sections and
`IsNaiveFullLevel` itself. The new nonemptiness theorem properly needs no `3 ≤ N`.
The actual representable/coarse point existence theorem needs that bound through the
chosen full-level representation. Both raw marked-section and unmarked E-only level-3
fixtures use the actual classifier API.

### Constant first-coordinate axis: reviewed initial layer

The axis morphism is the coproduct inclusion with label `![a, 0]`. Its composite with
upstream `fullLevelHom` and `torsionι` equals the explicitly defined section-axis map.
For arbitrary test schemes, `constSchemePointsEquiv` identifies constant-scheme points
with locally constant labels. Restriction to each label piece computes the section-axis
point. The additive proof uses the product-label cover and upstream `val_smul_add`;
there is no reduction to geometric points or reduced test schemes.

In `axisPoint_range_iff_factoring`, a factorization initially lacks an explicit base
triangle. The proof derives it from `sectionAxis_π`, the factorization equation, and
`Q.property`, which is exactly what is needed. The range of the additive hom is a
subgroup on every test scheme. `torsionAxis` is the literal factorization into `E[N]`,
and upstream `torsionι_factors_iff` proves N-killing without the rank-kills theorem
(which has unrelated upstream dependency issues). The actual complex instantiations
use the full marking already proved for the native pullback. Their uniquely named
canonical point-group instance is local to the actual-complex section.

At this starting snapshot the file honestly does **not** bundle a finite locally free
subgroup or prove `IsCyclic`. A subgroup of test-scheme points plus N-killing alone
would not fill those omitted scheme and divisor properties.

### Closed-axis delta: checked separately

The next ConstantAxis snapshot is 312 lines, maximum width 92, SHA-256
`c62ac496fda9b1f1cc027dc0649bc5fa6517b8d3981551d26dcd89c5280b1f82`,
with a complete copy in `/private/tmp/xyin-point-bridge-review-closed`.

`axisRestriction` is literal restriction of functions to `![a,0]`; extension
`v ↦ f (v 0)` is its right inverse. The `constSchemeSpecIso` triangle has the correct
contravariant direction. Cancelling its target isomorphism expresses the geometric
axis inclusion as `Spec.map axisRestriction`, so ring-map surjectivity proves a closed
immersion over arbitrary `CommRingCat R`. The section axis is then the composite with
the actual `fullLevelIso` and `torsionι`. Its displayed statement explicitly fixes
`N`, and the complex specialization transports `IsUnit (N : ℂ)` through
`ΓSpecIso.inv.hom`, the correct direction for a global-section unit.

I read the complete delta, its exact upstream `constSchemeSpecIso` and `fullLevelIso`
types, and `/private/tmp/xyin-y0-constant-axis-closed.log`: fifteen printed checks are
all the standard three axioms, with no warnings/errors. The owner reports strict direct
exit 0. No mathematical issue was found. This establishes an actual closed axis;
At this intermediate checkpoint, finite/flat/lfp/rank and the bundle were not yet added;
the final delta below supplies and verifies them.

### Final projection and subgroup bundle delta

The final stable ConstantAxis snapshot is 440 lines, maximum width 94, SHA-256
`9e12d3f519116c86e09e9d52cdf5f22caa3f6eaf11c6e1c916b27960fe8a3072`,
with its reviewed complete copy in `/private/tmp/xyin-point-bridge-review-bundle`.
The other three final source hashes match the starting table unchanged. All four retained
files are byte-identical to their corresponding isolated-checkout sources.

The projection is finite by the diagonal product algebra's finite module, flat by the
constant-scheme instances, and locally of finite presentation by the source-local
coproduct theorem. Its rank is transported through the actual `constSchemeSpecIso` to
`Module.rankAtStalk_pi`; the finite sum of self-module ranks is `card (ZMod N) = N`.
The local `Nontrivial R` comes from the supplied prime, so this theorem does not add a
ring-wide nontriviality, domain, reducedness, field, or prime-level assumption. The empty
spectrum case remains vacuous. I checked the exact mathlib rank theorem signatures.

`sectionAxisSubgroup` fills every native `FiniteLocallyFreeSubgroup` field: its source
is the literal constant cyclic scheme, its immersion is the actual section axis,
closedness is the checked composition through `fullLevelIso`, and all projection
properties reduce through `sectionAxis_π`. The subgroup field quantifies over arbitrary
test schemes and uses the already checked point-image theorem. `HasRank N` consequently
computes the rank of this exact morphism.

The new low `SubgroupQuotientInterface` import contributes `HasKillingInt`, whose precise
field is a nonzero integer and an equality `G.ι ≫ E.mulByHom N = G.π ≫ E.zero`.
`sectionAxis_mulByHom` proves that equality directly from `pullback.condition` and
`torsionAxis_π`, so neither the bundle nor its killing datum uses the upstream generic
rank-kills theorem. The actual complex bundle is instantiated with the native marking,
and its immersion is definitionally the existing actual section axis (`rfl`).

I re-read the complete added delta and the exact native structure/class types. The owner
reports strict direct exit 0; I inspected `/private/tmp/xyin-y0-constant-axis-bundle.log`
and independently counted 28 printed declarations, every one with exactly
`[propext, Classical.choice, Quot.sound]`, and no warning/error lines. The only preceding
binder repair was `intro T g` for the structure's implicit test-scheme parameter; the
final reviewed source is the compiled snapshot. No mathematical or source issue remains
in this delta. This ConstantAxis-only bundle delta does not assert `IsCyclic`; the
later AxisGenerator module reviewed below supplies that proof.

## Exact upstream API anchors checked

- `EllipticCurve/GlobalChartOverField.lean`: `nonempty_localPresentation_top`,
  `localPresentationTop`, `globalWeierstrassModel`, and its ellipticity instance.
- `Moduli/CoarseSpace.lean:295`: the literal selected `xFullNaiveRepr`.
- `Moduli/Representability.lean:642`: the actual section-pair moduli functor and pullback.
- `Moduli/QuotientProblem.lean:64,78,114,284`: `pullbackAlongπ`,
  `toPullbackAlong`, the composition theorem, and `isoPullbackAlong`.
- `GroupScheme/GLSchemeAction.lean:48,80`: the actual `fullLevelHom` and base triangle.
- `Moduli/GammaH.lean:234`: additive `ZMod.val`-smul under N-killing.
- `GroupScheme/Subgroup.lean:132,451`: all fields of `FiniteLocallyFreeSubgroup` and
  the torsion factoring/killing equivalence.
- `GroupScheme/CyclicSubgroup.lean:86`: `IsCyclic` is the actual
  `IsGammaZeroFppf N G.toRelEffCartierDiv` divisor-generator predicate, not a point-count
  or rank predicate.
- `GroupScheme/GLSchemeAction.lean:59`: `sectionsEquivRingHomUnder` already supplies
  an instance-free ring-map-under dictionary. The retained fine/coarse algebra-point
  dictionaries additionally expose the fixed complex algebra and literal projection.
  No standalone exact replacement was compile-tested in this read-only pass, so this
  is recorded as reuse context rather than an actionable unverified rewrite.

## Receipts inspected and final deltas

- FineComplexPoints exact source is unchanged from the previously accepted compiler
  snapshot. The quotient leaf log `/private/tmp/yzero-complex-point-orbits-build.log`
  replayed its eleven standard-three-axiom checks and completed successfully (9403 jobs).
- MarkedComplexCurves final direct log:
  `/private/tmp/xyin-y0-marked-complex-curves-check.log`: nine axiom checks, all
  `[propext, Classical.choice, Quot.sound]`, no warnings/errors. The owner reports strict
  exit 0 and an emitted `.olean` of 37640 bytes. Its final source hash equals the
  starting snapshot hash above, so no later delta was missed.
- Literal MarkedComplexCurves compiler invocation (cwd
  `/private/tmp/xyin-y0-aintlib-work`, tool session 58159, exit 0):

  ```sh
  /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/YZeroCoarseMarkedComplexCurves.lean --setup YZeroCoarseMarkedComplexCurves.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseMarkedComplexCurves.olean > /private/tmp/xyin-y0-marked-complex-curves-check.log 2>&1
  ```

  The exact setup uses `autoImplicit=false`, `relaxedAutoImplicit=false`, and
  `pp.unicode.fun=true`. This receipt is from the owner; this reviewer additionally
  inspected its output and matching final source bytes, without rerunning the compiler.

- ConstantAxis initial direct log:
  `/private/tmp/xyin-y0-constant-axis-strict.log`: eleven axiom checks, all standard three,
  no warnings/errors; owner reports strict exit 0. The subsequent closed and final bundle
  receipts are separately reviewed above: respectively fifteen and 28 checks, all
  standard three axioms, zero warnings/errors and owner-reported strict exit 0.
  The owner's durable command/receipt record is `YZeroCoarseConstantAxis.md`.
- Literal ConstantAxis direct compiler invocation (cwd
  `/private/tmp/xyin-y0-aintlib-work`; owner-reported final exit 0), as also persisted
  verbatim in the owner's durable record:

  ```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean --setup .lake/build/ir/AINTLIBDrafts/YZeroCoarseConstantAxis.setup.json AINTLIBDrafts/YZeroCoarseConstantAxis.lean -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseConstantAxis.olean
  ```

  I independently read the strict setup JSON: `autoImplicit=false`,
  `relaxedAutoImplicit=false`, `pp.unicode.fun=true`, and no dynamic libraries.
  This reviewer did not rerun the command.

- FieldGeometricJ reuse patch: source hash remains `992743897a441e98d94799d3b12cc134a0d99ce6c24014a35fa7bc4974a4a9a3`; parent
  reports strict Lake target exit 0 (4151 jobs, own module 23s). I read all six own
  standard-three-axiom checks and zero own warnings/errors in
  `/private/tmp/yzero-field-model-reuse-build.log`.
- Parent cumulative import graph: pending final receipt.

## What is established and what remains

All actual fine/coarse statements here are at `[NeZero N]` and `3 ≤ (N : ℤ)`.
Only native full-marking nonemptiness drops the level bound. At the initial four-module
snapshot, the existence of a coarse point for each given elliptic curve did not yet prove
that every complex number is attained by the source-j map. The separately checked
model-j and source-j-surjectivity deltas below now prove this additional conclusion.

Already established by the reviewed checked bridge and the separately checked orbit
module: actual coarse complex points lift to actual fine points; their coarse fibers
are exactly the literal Borel orbits; the explicit Borel orbit quotient is equivalent
as a **set** to the actual coarse complex points. Each fine point gives a native elliptic
curve, a genuine full marking, and a genuine elliptic Weierstrass model with exactly the
same coarse source-j. Its first-coordinate axis is now an actual finite locally free
rank-N subgroup with a directly proved nonzero killing integer, native exact-order
generator and exact fppf cyclicity. Each actual coarse complex point has a full lift
carrying the resulting native Γ₀ structure. Conversely each given
native complex elliptic curve has a full marking and supplies an actual coarse point
with its j. The later source-j-surjectivity module realizes every complex value by such
an actual coarse point and hence also by an actual complex algebra point of the
literal invariant coordinate ring.

These are substantial bridges to actual AINTLIB objects, but they do not yet assert:

1. Borel orbit equivalence is precisely isomorphism of pairs `(E, C)` with a cyclic
   order-N subgroup. The subsequently reviewed divisor-generator delta below supplies
   exact-order/cyclicity for the actual first axis, but not this classification.
2. A quotient elliptic curve `E/C`, its regular target-j coordinate, or compatibility
   with classical degree-N cyclic isogenies.
3. An analytic `Γ₀(N)`/lattice classification of the actual coarse curve.
4. `Φ_N(j(E), j(E/C)) = 0` for those actual points, nor its promoted identity in the
   actual invariant ring or an isomorphism with a modular-polynomial plane curve.

A concrete pinned upstream boundary is `LevelStructure/ExactOrder.lean:922–926`:
`Section.hasExactOrder_of_geometric` is defined by `by sorry`. The derived
`hasExactOrder_of_isNaiveGammaOne` and `hasExactOrder_fst_of_isNaiveFullLevel` at
`LevelStructure/FullLevelGammaOne.lean:108,116` inherit that dependency. I read these
actual source declarations. They are not used by the present standard-three-axiom axis
layer. The subsequent divisor-generator delta supplies an independent honest proof for
the full-marked invertible-base case; it does not discharge the more general upstream
geometric-to-exact-order theorem.

The reviewed point bridge also makes no domain/integrality conclusion for the actual
coarse coordinate ring. Its earlier reducedness and finite-type inputs suffice for
point separation; they alone do not identify a function field or prove a scheme
isomorphism from the set-level orbit equivalence.

The compiled point-separation infrastructure can promote a **proved** pointwise Φ
identity to a ring identity once these source/target comparisons exist. No such desired
identity is assumed or built into the present point bridge.

## Additional generic model-j delta

Read-only review of the green temporary `ModelGeometricJProbe.lean`,
`/private/tmp/ModelGeometricJProbe.log`, and the retained minimal-import
`AINTLIBDrafts/ModelGeometricJ.lean` found no mathematical issue. The retained snapshot
is 121 lines, maximum width 87, SHA-256
`2c852d800ab7ba165e1eef8d879b41a76d555bbb82b22c43a8165b85ef939ef7`.
Its complete review copy is in `/private/tmp/xyin-point-bridge-review-model`.
The two retained declaration bodies are byte-identical to the green probe; imports,
namespace and documentation are the only differences. The probe's two printed axiom
results are both exactly the standard three. The owner is responsible for the retained
module's minimal-import strict build; no such build was started by this reviewer.

The actual upstream `ModelRecord.lean:77` defines `modelEllipticCurve W` with literal
`E := projModel W`, `π := projModelπ W`, and `zero := projModelZero W`.
`modelTopPresentation` extracts the explicit whole-base construction that is otherwise
inside `Comparison.lean:273`'s `locallyWeierstrass_projModel` proof; it does not choose an
unrelated model whose j is postulated to agree. Its coefficient curve is exactly
`W.map ΓSpecIso.inv.hom`. The chart isomorphism goes from the top-open pullback to the
original projective model, then to the coefficient-ring pullback, then to the projective
model of those mapped coefficients. This is the correct direction of the actual
`isPullback_projModelBaseChange` isomorphism (`WeierstrassModel.lean:2670`).

The `compat_π` proof cancels the genuine `Spec` isomorphism of the canonical coefficient
ring identification. The `compat_zero` proof is exactly the pointed base-change
compatibility and uses `projModelZero_baseChange` at upstream line 2925. All three
non-Prop fields and both compatibility requirements agree with the actual
`LocalPresentation` structure at `InvariantDifferential.lean:90`.

Finally `model_jSection` applies `jSection_res` to this explicit pointed top chart and
then `WeierstrassCurve.map_j`. The result is the canonical section
`ΓSpecIso.inv.hom W.j` on the actual projective curve. The generic hypotheses are only
`CommRing A` and `W.IsElliptic`; no field, nontriviality, algebraic-closedness or
characteristic restriction enters. Thus this removes the model-to-geometric-j seam for
the honest source-j surjectivity proof in the following delta. This generic delta
itself asserts no surjectivity or Φ identity.

There is deliberate construction reuse from a Prop-valued upstream local-model proof.
For an eventual upstream cleanup, exposing that pointed whole-base presentation as data
would avoid copying the same compatibility bookkeeping. No uncompiled refactor is
claimed as a verified fix here, and the present explicit chart is mathematically sound.

## Additional actual source-j surjectivity delta

The retained `AINTLIBDrafts/YZeroCoarseSourceJSurjective.lean` snapshot is 78 lines,
SHA-256 `9c7d77aba7b8d1b5bd6aa5ef4739194f75d9bb391d437d38e70a11c0690d8760`.
I read all of its code, the actual `ModelsWithJ.lean` APIs, the already reviewed
given-curve classifier/source-j theorem, and the complete strict log
`/private/tmp/xyin-y0-source-j-surjective-check.log`. The owner reports direct strict
exit 0, no warnings/errors, and successful emission of a 15616-byte `.olean`.
All three printed declarations use exactly the standard three axioms; both literal
level-three sanity examples are present in that checked file.

The generic `fieldWeierstrassModel_model_j` uses the geometric model-j theorem, then
cancels `ΓSpecIso.inv ≫ ΓSpecIso.hom`. It concludes equality of j, without identifying
the chosen field model's coefficients with the original curve. The actual mathlib
`WeierstrassCurve.ofJ` at `ModelsWithJ.lean:134` constructs an elliptic curve for every
field element; its ellipticity instance at line 164 and `ofJ_j` at line 183 have no
additional characteristic hypothesis. In particular these APIs apply over ℂ.

For each `z : ℂ`, the proof applies the genuine native full-level classifier to the
actual projective curve `modelEllipticCurve (WeierstrassCurve.ofJ z)`. The existing
source-j theorem gives its field-model j, the generic cancellation gives `ofJ z`'s j,
and `ofJ_j` gives `z`. Thus `yZeroComplexSourceJValue_surjective` is a theorem about
the already constructed actual coarse source-j; it does not assume a moduli relation or
select an unrelated surjective function. The algebra-point corollary transports this
same equality through `yZeroComplexSourceJValue_eq` in the correct symmetric direction.

This proves surjectivity of the source-j value on complex points for nonzero `N ≥ 3`.
It does not assert that the j morphism is finite, a scheme isomorphism, or a quotient
classification of cyclic subgroups, and does not give a target-j or a Φ relation.
Read-only review result: no concrete issue; no source edit or compiler invocation.

## Additional actual divisor-generator delta

The retained `AINTLIBDrafts/YZeroCoarseAxisGenerator.lean` snapshot is 307 lines,
maximum width 100,
SHA-256 `d102529f57067ea5c5bb5eb2478551c2097c32a102cea007284aa233dd43b31f`.
I read the complete retained source, its earlier green temporary
`YZeroDivisorAxisProbe.lean` (SHA-256
`6e318cc9f5618a635a44afe61fb7e08b9e084f748b221e841b7fc9459d28d8ed`), and the actual
upstream definitions and proof primitives. No Lean source change or compiler run was
made by this reviewer. The temporary exact-order and cyclicity logs each contain only
the standard three axioms; the latter has all fourteen printed declarations, including
the nine generic declarations and five upstream primitives. The retained named strict
Lake target is now green: the owner reports exit 0, and I independently read the actual
success receipt for 9410 jobs (own module 67s) in
`/private/tmp/xyin-y0-axis-generator.log`. I parsed all 26 retained printed checks:
each is exactly `[propext, Classical.choice, Quot.sound]`. There are zero warnings
at this module's own path and zero error lines; pinned dependencies replay their
existing warnings. Its four level-three examples passed in the same strict target.
The unchanged 440-line ConstantAxis dependency also rebuilt green in 52s with all
28 of its printed checks standard-three. The retained/build source hashes match.
I read the generated setup JSON: `autoImplicit=false`, `relaxedAutoImplicit=false`,
`pp.unicode.fun=true`, and no dynamic libraries.

The `orderIndex` shift is essential: the order divisor contains `P, …, NP`, while the
literal constant axis is labelled by `0, …, (N−1)P`. Its label zero selects the `NP`
constituent. `orderIndex_multiple` proves the correct equality modulo `N` using the
actual hypothesis `N • P = 0`; there is no assumption that the shifted natural-number
coefficients agree literally. The constituent factorization uses the actual product
ideal containment in `Factorization.lean:640`, under the required separated/smooth
relative-dimension-one hypotheses supplied by the native elliptic curve.

The coproduct lift `j` satisfies the literal immersion and base triangles. For a full
marking over `Spec R` with `N` invertible, its composite with the divisor immersion is
the already checked closed constant axis, so `j` is itself a closed immersion. The
target divisor's finite/flat/lfp hypotheses are its actual record fields. The source
properties are transported through the base triangle from the actual constant
projection. The rank comparison uses the native sections divisor's degree `N` and
the independently checked constant projection's rank `N` at every point of `Spec R`.
`isIso_of_isClosedImmersion_of_finrank_eq_isAffineBase` requires exactly these facts;
it introduces no reducedness, domain, field, characteristic or nontrivial-ring
hypothesis. The only affine restriction is the declared base `Spec R`.

The divisor comparison is a literal ideal-sheaf equality. Since the bundled subgroup's
divisor has ideal `axis.ker`, substituting the immersion triangle gives
`(j ≫ divisorImmersion).ker`; `ker_comp_of_isIso` removes the actual isomorphism `j`,
and `ker_subschemeι` recovers the defining divisor ideal. This is stronger than merely
equal underlying point sets or equal fiber cardinalities.

Native `HasExactOrder` is the all-test-schemes subgroup predicate in
`ExactOrder.lean:103–118`. For every `T → Spec R`, the proof retains the already
constructed additive subgroup of native `T`-points. A factor through the constant
axis gives a factor through the divisor by `h ≫ j`; conversely a divisor factor gives
an axis factor by `h ≫ inv j`. The immersion triangle and the actual inverse law give
both equations. There is no restriction to geometric, reduced or affine test schemes,
and no use of the upstream geometric-to-exact-order `sorry`.

For `IsCyclic`, the fppf cover is the identity on `Spec R`, with actual surjectivity,
flatness and local finite presentation. The generator is the actual section
`asSection E id (pull E id P)` of `E.baseChange id`. The checked
`HasExactOrder.baseChange` supplies its native exact order. `RelEffCartierDiv.ext`
turns the proved ideal equality into a divisor equality, and the checked
`orderDivisor_baseChange` supplies the generator-ideal equation required by
`isCyclic_of_generator`. At no point is the `E.baseChange id` record identified with
`E`; the proof uses the intended base-change APIs throughout.

The final wrappers construct the native `GammaZeroStructure` with
`GammaZeroStructure.ofIsCyclic`; their subgroup and immersion equations are literal
`rfl`. The actual complex specialization uses exactly the previously proved native
curve and full marking, including the native first-section exact-order theorem.
The coarse existence wrapper applies the already checked actual fine-point lift and
packages this structure on that lift's native curve. Its conclusion is only an
existential lift carrying a native Γ₀ datum, accurately matching its documentation.
The four level-three examples test the literal immersion, rank, native cyclicity and
actual coarse-lift statement.

Thus the mathematical review finds no concrete issue, and the retained strict leaf
has passed. The native first-axis subgroup is cyclic in AINTLIB's exact fppf/divisor sense,
and each actual coarse complex point has an honest cyclic-subgroup lift. Neither
lift-independence nor classification of pairs `(E, C)` is asserted. Construction of
`E/C`, the regular target-j, analytic/classical isogeny comparison and the Φ relation
remain separate mathematical work.
