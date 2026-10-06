### Simplify pass — `AINTLIBDrafts/` (10 retained Lean companions)

Outcome: ISSUES-FOUND-NOT-FIXED
Review: fresh independent reviewer, read-only relative to the implementation/cleanup workers

This review inspected all 1,426 lines of the ten actual source files, their relevant callers,
and pinned AINTLIB/mathlib definitions. It did not rely on the implementation summaries.
No correctness defect or hidden fine-ring domain assumption was found. The outstanding item
is a small cross-file API consolidation referral, not a failed mathematical gate.

Issues identified by `$mathlib-quality-for-codex:simplify`:

- **Low priority — duplicated invariant-ring scalar construction.**
  `YZeroCoarseFiniteType.lean:64` defines `yZeroInvariantCoefficientHom` as the ring-hom
  view of `ΓSpecIso.inv ≫ yZeroStruct.appTop ≫ yZeroSectionsIso.hom`.
  `YZeroCoarseJInvariants.lean:99–104` reconstructs the same map through
  `yZeroCoefficientSections` and `yZeroInvariantCoefficients`. Both inclusion proofs
  (`yZeroInvariantCoefficientHom_comp_inclusion` and
  `yZeroInvariantCoefficients_comp_inclusion`) rewrite the same projection/section
  compatibility square. This agreement is visible in the definitions and associativity;
  no compiled alternative is asserted here. A common base-coefficient construction in
  `YZeroCoarseInvariantSpec.lean`, with categorical and ring-hom views, would remove the
  independent reconstruction and expose the scalar alignment used by
  `YZeroCoarseComplexPoints.yZeroComplexAlgebraPointOfScheme`.
  The best reason for the current arrangement is that finite-type and geometric-j files
  remain independent import branches; preserve that property when consolidating.
  Do not make finite-type descent import geometric j merely to remove this duplication.

Fixes applied by `$mathlib-quality-for-codex:simplify`:

- None. The parent authorized a read-only review while its strict build and two bounded
  declaration workers run. Definitions, theorem statements, instances and comments were
  left untouched by this reviewer.

Files modified:

- This report only: `XYin/PhD/Test/ModularPolynomialCurve/Cleanup/SimplifyReview.md`.
- No Lean source, shared `.mathlib-quality` sidecar, global configuration, or task process.

Verification:

- `wc -l XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/*.lean` — exit 0; 10 files,
  1,426 lines at the reviewed snapshot.
- `git diff --no-color -- XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts` — exit 0,
  empty. These files are untracked, so this is **not** evidence of source identity by
  itself; the snapshots and SHA-256 values below provide that evidence.
- `shasum -a 256 XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/*.lean` — exit 0 on
  both read passes; every value agreed. A byte snapshot and `manifest.json` were saved to
  `/private/tmp/yzero-simplify-readonly-snapshot` without modifying the originals.
- Direct reads/source searches completed for AINTLIB `CoarseSpace.lean`,
  `RelativeInvariantSpec.lean`, `EllCategory.lean`, `YFullSmoothAffine.lean`,
  `InvariantDifferential.lean`, and relevant pinned mathlib algebra/affine APIs.
- **Builds and compiler probes: not run by this worker**, as explicitly directed by the
  parent. Baseline/final strict builds, axiom output, diagnostics, and profiling belong to
  the parent's central verification receipt. No untested tactic, import reduction, or
  shortening is presented as a verified replacement.
- `definition_protected`, `theorem_statement_protected`, and comment preservation are
  vacuous for this reviewer's empty Lean patch. Cumulative builds are not claimed here.

Unresolved or reverted:

- Refer the scalar-construction consolidation to the parent for a sequential cross-file
  refactor, compiled scalar-equality probes and downstream builds. It is outside the
  current bounded declaration edits. No failed change needed reverting.
- The comparison gaps below remain mathematical work; this review does not convert
  them into proved claims or silently broaden cleanup scope.

### Mathematical and API evidence

| File / declarations | Independent source assessment |
|---|---|
| `UpstreamAudit` | Audits the actual upstream object and quotient lift separately. Source `#print axioms` commands are not their output; the central receipt must verify them. |
| `YZeroCoarseInvariantSpec.fullObject`, `borelAction`, `yZeroInvariantSpecIso` | `fullObject` is exactly `xFullNaive`; upstream `xFullNaive`, `xFullNaiveRepr`, and `YHCoarse` use the same representability proof and `Functor.reprX` / `representableBy`. The action comes from the same representation and `gammaHAut` Borel action. No independent chosen representing object is substituted. |
| `AffineInvariantQuotient.invariantSections`, `sectionsIso_hom_comp_inclusion` | The invariant ring is a literal fixed-point subtype of actual fine global sections. The top affine quotient chart has whole opens range and hence is an isomorphism. Projection pullback is identified with the literal inclusion, not inferred merely from point surjectivity. |
| `GeometricJ.chartJ_eq`, `chartJ_transport`, `existsUnique_jSection`, `jSection_res`, `jMap_naturality` | `chartJ` uses an actual elliptic pointed Weierstrass presentation; chart equality uses its actual comparison variable change. Restrictions and pointed cartesian transport supply sheaf gluing and naturality. `jSection_res` covers any local pointed presentation, so the selected atlas does not impose an extra chart hypothesis. |
| `YZeroCoarseJ.action_jSection`, `coarseJMap`, `yZeroSourceJ` | Invariance comes from cartesian pointed `EllHom`s transported from moduli automorphisms. The source-j map descends by the actual quotient's uniqueness property. Its defining equation, base triangle and chart pullback identify the actual section. The duplicate local affine instance in the original `yZeroSourceJ` is already owned by the parent's declaration worker; it is not independently edited or re-reported as a new issue here. |
| `YZeroCoarseJInvariants.yZeroJPolynomialHom_X`, `yZeroJPolynomial_C` | The polynomial variable maps to the actual invariant geometric j section. Constants agree with the actual structure-map coefficient pullback. Neither injectivity nor transcendence of this polynomial map is assumed or proved. |
| `YZeroCoarseFiniteType.finiteType_of_injective_integral`, `yZeroInvariantRing_finiteType` | Artin–Tate uses a Noetherian **base**, an injective invariant inclusion, integral inclusion and finite-type fine algebra. The scalar algebra is explicit and local. `fullCoefficientHom` also repeats the formula of `GeometricJ.coeffHom (fullObject ...)`; the independent import branches justify retaining that specialization until a common lightweight scalar API is available. |
| `YZeroCoarseProjection.yZeroInvariantRingι_finite`, `yZeroPr_isFinite`, `yZeroPr_appTop_injective` | Finiteness uses integral plus finite-type inclusion; it adds neither Noetherian nor domain assumptions. Surjectivity uses upstream coarse projection. Despite the upstream name `surjective_relQuotientπ_of_free`, that declaration has no `include hfree` and its actual proof uses integral invariant inclusion; freeness is not a hidden hypothesis. |
| `YZeroCoarseReduced.isReduced_of_etale_over_domain`, `isReduced_of_smooth_over_domain`, `fullSections_isReduced` | The generic-fibre embedding uses flatness of the étale algebra and injectivity of `R → FractionRing R`. Local standard-étale polynomial charts then detect nilpotence. Only `R` is a domain; no domain, connectedness or nontriviality hypothesis is added to fine sections. The injective invariant inclusion transfers reducedness. |
| `ComplexPointSeparation.exists_algHom_ker_eq_of_isMaximal`, `eq_zero_of_forall_algHom_eq_zero` | Maximal residue fields are finite/algebraic over the algebraically closed base; their lifts give points. Finite-type Jacobson property and reducedness make their kernels detect zero. The proof remains valid for products and the trivial algebra. It detects values at **all** algebra homomorphisms, not a specified analytic parametrization. |
| `YZeroCoarseComplexPoints.yZeroComplexAlgebraSchemePointEquiv` | The base triangle proves the inverse ring map is complex-linear for the same actual structural scalar algebra. The equivalence is with actual morphisms `Spec ℂ → YZeroCoarse` over `Spec ℂ`, not with the underlying prime spectrum or assumed moduli classes. |

### Exact limits of the proved connection

- Regular source j is a global section/morphism on the actual open coarse curve; the
  geometric construction and naturality currently use affine bases. No cusp extension or
  compactified coarse curve is asserted.
- Point separation is proved for the actual reduced, finite-type invariant algebra and
  its actual complex scheme points. There is no theorem identifying those points with
  elliptic curves plus cyclic subgroups, lattices, or the independent `planePoints`.
- `yZeroJPolynomial` is a one-variable source-coordinate map. No target-j section,
  bivariate `Φ_N` relation in actual coarse sections, comparison with the independent
  plane scheme, normalization theorem, coarse domain theorem, or actual coarse
  function-field equivalence is proved by these files.
- The existing XYin aggregate imports only its independent analytic/plane-model
  modules. The AINTLIB companions are intentionally checked in the pinned 4.35 runtime;
  they do not become local XYin 4.30 imports merely by existing in this directory.

### Reviewed source snapshot

Pinned runtime: AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, Lean `4.35.0-rc3`, under
`/private/tmp/xyin-y0-aintlib-work`. These hashes identify this review's input; a later
owned cleanup edit needs its own final gate and review delta.

```text
ComplexPointSeparation.lean       406bd753e4276a1395e86231462eff211d81b767c29cf6b66106cf0f6e84e185
GeometricJ.lean                   793f538cbce3c240093eb813612ce0fe03d801a478730198bdd487206435a9b9
UpstreamAudit.lean                ac4045a15f6f917dcefa7705421313be1ba87817bd9307a47068e72e758648cf
YZeroCoarseComplexPoints.lean     e4d32e1771d965eb6c7d3e1c4f2e4a0edce198d58e740e3e47ebebbc5720008d
YZeroCoarseFiniteType.lean        bccad4edd7456c4b5f1f43111fab1a2e1829e5a4aca6651f57e4c0c67a0bec22
YZeroCoarseInvariantSpec.lean     12da3edb94512c89cd04f3ee9826595ca22bee77632e2e6c021bf34e10ebb0cf
YZeroCoarseJ.lean                 cf9cc72904eb34675d14934973d7d9b354d5b433ccd62928e78ca51115610a88
YZeroCoarseJInvariants.lean       e97b21ce1b4e88f2a68b0d0354294c8f7ee7923409a8967a240253088abde2e5
YZeroCoarseProjection.lean        c1ea5d95caa335e73d896e8a513339c0be83d74df4325041b29b08f189d874b0
YZeroCoarseReduced.lean           cc0276b108442f9267ebe9a6f2b6d023eb6a863a3ff59bd465c049e1189054a0
```

Skill workflow status: actual declarations/callers, independent holistic review, reuse,
structure, hypotheses, scalar/choice alignment and relevant shared references reviewed.
Pinned source searches established concrete reuse; no exhaustive mathlib-absence claim
was made. Compiler-based replacement probes and efficiency measurements were deferred
to the parent as directed. This is an honest read-only simplify receipt, not a completed
full-directory cleanup, final build or buzz pass.

### Parent disposition

The parent read the actual scalar-map definitions and retained the separate adapters:
finite-type descent must remain independent of the geometric-j import branch. The actual
complex point equivalence already checks scalar alignment through its `commutes'` proof.
Moving the shared construction to the invariant-spectrum module is a useful future API
refactor, but is not needed to establish the current mathematical statements. This is an
accepted low-priority structural referral, with no unresolved correctness issue. The two
owned declaration cleanups were reviewed separately and compiled; subsequent point-lifting
and native-elliptic-point additions need their own review and final joint receipt.
