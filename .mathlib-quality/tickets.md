# Ticket board: Cox §11.B–C and report extensions

## 2026-09-21 Cox migration (user-authorized)

### [CX001] Bundled theorem inputs and generators
- **Status:** done
- **Files:** `Cox/ModularFunction.lean`, `ModularFunctions/Congruence.lean`, Cox callers.
- **Result:** new `ModularFunction` inputs, bundled `levelJModularFunction`, shared cusp API;
  raw intermediate data explicitly distinguished from canonical representatives.
- **Validation:** focused `ModularFunction` and `Congruence` build passed.

### [CX002] Meromorphic ambient field and direct field equalities
- **Status:** done
- **Files:** `Cox/UpperHalfPlaneFunctionField.lean`, `Cox/ModularFunctionField.lean`.
- **Result:** removed legacy holomorphic FractionRing and Represents relation; proofs use
  `ModularFunction.toMeromorphicField`. General field infrastructure moves to the shared library.

### [CX003] Remove duplication and integrate polynomial proofs
- **Status:** done
- **Files:** `Cox/LatticeJ.lean`, `Cox/CoxMatrices/LaurentExpansion.lean`, polynomial modules.
- **Result:** shared j holomorphy/periodicity; genuinely bundled Cox-product coefficients;
  all dependent names and interfaces migrated.

### [CX-CLEANUP] Final verification
- **Status:** done
- **Acceptance:** source review, no placeholder axioms, focused and full build, key axiom checks,
  profiling and a migration verification report with generated-field semantics made explicit.
- **Validation:** full build passed (3918 jobs), 11 key axiom audits passed, 7 modules profiled;
  independent final review passed. See `cox-modular-functions-migration.md`.


## 2026-09-20 modular functions extension (user-authorized)

### [MF001] Codiscrete field and canonical upper-half-plane representatives
- **Status:** done
- **Files:** `ModularFunctions/MeromorphicField.lean`
- **Statement:** `Field (MeromorphicOn.germRing ℂ U)` for connected nontrivial U;
  `UpperHalfPlane.MeromorphicField.toFun` with normal-form range and holomorphic inclusion.
- **Source:** ProjectVD commit `9c218722ad71e9bd2ba357892bc835c8c648aaa8`, `VD/Field`.
- **Proof sketch:** image of meromorphic subring in `Germ (codiscreteWithin U) ℂ`;
  identity theorem implies a nonzero class has codiscrete nonzero locus; inverse is pointwise.
  Normalize representatives with `toMeromorphicNFOn`; use uniqueness on open sets.
- **Progress:** completed pinned codiscrete field port, canonical representative API, and Field/Algebra checks.

### [MF002] Exponential growth and cusp meromorphy
- **Status:** done
- **Files:** `ModularFunctions/CuspGrowth.lean`, `ModularFunctions/NormalFormGrowth.lean`
- **Statement:** for h>0 and h-periodic f eventually holomorphic,
  `IsOfExponentialGrowth f ↔ MeromorphicAt (cuspFunction h f) 0`;
  normal meromorphic f with this bound is eventually holomorphic.
- **Source:** linked growth conversation, proposition and proof; Mathlib meromorphic order,
  removable singularities, normal forms, and QExpansion source.
- **Proof sketch:** q has norm exp(-2π Im τ/h); choose N>ρh/(2π), regularize by q^N,
  remove the singularity. Reverse implication uses the analytic regularization's local bound.
  For NF regularity, locally bounded functions cannot tend to cobounded at a pole.
- **Progress:** proved both directions and derived eventual holomorphy from normal form plus growth.

### [MF003] Bundled definition and cusp comparison
- **Status:** done
- **Depends on:** MF001, MF002
- **Files:** `ModularFunctions/Basic.lean`, `ModularFunctions/GrowthAtCusp.lean`
- **Statement:** `structure ModularFunction (Γ : Subgroup (GL (Fin 2) ℝ))
  extends SlashInvariantForm Γ 0` with canonical field membership and period-free growth
  at every `IsCusp`; prove comparison with cusp-function meromorphy using positive periods.
- **Source:** user's requested structure; Mathlib ModularForm/BoundedAtCusp definitions.
- **Proof sketch:** use range of canonical representatives as the first Prop field;
  second field quantifies cusp transforms just like ModularForm. Apply MF002 at each transform.
- **Progress:** implemented all-GL growth transport, positive cusp periods, bundled API, and all-cusp equivalence.

### [MF004] Bundle the classical j-function
- **Status:** done
- **Depends on:** MF003
- **Files:** `ModularFunctions/JInvariant.lean`, `XYin.lean`
- **Statement:** `jModularFunction : ModularFunction 𝒮ℒ` with underlying function `j`.
- **Source:** existing jfunction.lean `j_slash_invariant`, `j_cuspFunction_meromorphicAt`.
- **Proof sketch:** j holomorphic since Δ is nowhere zero; use MF001 holomorphic inclusion;
  meromorphy in width 1 gives exponential growth; transport to every rational cusp.
- **Validation:** `jModularFunction` compiles, underlying function is definitionally `j`, standard axioms only.

### [MF-CLEANUP] Review, simplify, profile, and verify new modules
- **Status:** done
- **Depends on:** MF001, MF002, MF003, MF004
- **Files:** all newly changed Lean files
- **Acceptance:** independent review of mathematical statements, actual focused/full builds,
  source attribution and no-sorry audit, standard axioms on new principal declarations,
  cleanup/simplify and elaboration performance evidence recorded.
- **Validation:** full build passed (3916 jobs), 12 principal axiom audits passed, all 9 modules profiled;
  see `modular-functions-verification.md` for source, review, and timing evidence.

## Summary

- Original Cox §11.B–C board: complete (`T001`–`T029`).
- Takeover extension: complete (`T030`–`T037`).
- Modular functions extension: complete (`MF001`–`MF004`, `MF-CLEANUP`).
- Cox migration: complete (`CX001`–`CX003`, `CX-CLEANUP`).
- Execution status: **beastmode complete**.
- Open tickets with met dependencies: none.
- Source mappings and adversarial attacks: `.mathlib-quality/decomposition.md`.

Status vocabulary:

- `done/planning`: statement skeleton or baseline task completed without proving a target;
- `open`: may begin only after approval;
- `blocked`: reserved for a demonstrated external/API blocker, not ordinary difficulty.

## Phase 0 — planning baseline

### [T000] Restore a buildable root import graph

- **Status:** done/planning
- **Files:** `XYin.lean`, `XYin/PhD/Cox/Section11BC.lean`
- **Depends on:** none
- **Work completed:** removed imports of modules deleted in commit `614b160`, added the Cox
  umbrella import, and verified full `lake build`.
- **Validation:** full repository build succeeds (warnings/sorries only).
- **Guard:** do not restore the deleted `XYin/PhD/Test/` tree.

## Phase 1 — lattice `j`

### [T001] Port the scaling and lattice-invariance API

- **Status:** done (started 2026-07-12T02:06:05Z; finished 2026-07-12T02:29:03Z)
- **File:** `LatticeJ.lean`
- **Depends on:** T000
- **Declarations:** `mem_smul_lattice`, `G_smul`, `g₂_smul`, `g₃_smul`,
  `discriminant_smul`, `j_smul`, `g₂_congr`, `g₃_congr`, `j_congr`.
- **Source:** Cox printed p. 206 / PDF p. 218.
- **Proof sketch:** port the already axiom-clean proofs from
  `main:XYin/Workshop/L_L_bar_real.lean`; use a lattice equivalence induced by multiplication by
  `a : ℂˣ` to reindex the Eisenstein sum.
- **Mathlib:** `Equiv.tsum_eq`, `PeriodPair.G`, `mul_pow`, `Submodule.span`.
- **Validation:** focused build; axiom audit of `PeriodPair.j_smul`; test scaling by `-1`, `I`,
  and a non-root-of-unity unit.
- **Progress:**
  - 2026-07-12T02:06:05Z: picked by beastmode; source port and local API audit started.
  - 2026-07-12T02:21:00Z: all nine declarations proved; focused build and axiom audit pass.
    Scaling sanity checks pass for `-1`, `I`, and the non-torsion unit `2`; post-proof cleanup
    started sequentially.
  - 2026-07-12T02:29:03Z: DONE — all nine declarations are sorry-free; focused build,
    standard-axiom audit, diff gates, simplify pass, and buzz FAST-BOARD pass. Cleanup record:
    `.mathlib-quality/cleanup-t001.md`.


### [T002] Repair the analytic/lattice invariant bridge

- **Status:** done (started 2026-07-12T02:29:25Z; finished 2026-07-12T02:45:04Z)
- **File:** `LatticeJ.lean`
- **Depends on:** T001
- **Declarations:** `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`, `Delta_eq_E4_E6`,
  `j_eq_periodPair_j`.
- **Source:** Cox printed pp. 220–221 / PDF pp. 232–233.
- **Proof sketch:** reindex `PeriodPair.G` by `ℤ²`; compare with mathlib's Eisenstein series;
  evaluate `ζ(4)` and `ζ(6)`; identify project `Delta` with
  `ModularForm.discriminant`; apply mathlib's cubic relation and nonvanishing.
- **Must not use:** old `Delta_E4_eqn` (transitive `sorryAx`).
- **Validation:** `#print axioms j_eq_periodPair_j` contains no `sorryAx`; numerical constant
  checks reduce by `ring`.
- **Progress:**
  - 2026-07-12T02:29:25Z: picked by beastmode after T001; auditing historical bridge and
    sorry-free mathlib discriminant API.
  - 2026-07-12T02:36:00Z: repaired the latent `π` scope bug (`open Real`), proved the two
    lattice/Eisenstein comparisons by a `ℤ²` tsum reindexing, and replaced the contaminated
    `Delta_E4_eqn` route with mathlib's eta/discriminant identity.
  - 2026-07-12T02:39:00Z: `j_eq_periodPair_j` closes by cancelling only the fixed nonzero
    factor `64π¹²/27`; no discriminant nonvanishing assumption or T003 dependency is needed.
  - 2026-07-12T02:45:04Z: DONE — all four declarations are sorry-free; focused build,
    standard-axiom audit, diff/style gates, simplify pass, and buzz FAST-BOARD pass. Cleanup
    record: `.mathlib-quality/cleanup-t002.md`.

### [T003] Prove discriminant nonvanishing and lattice `j` classification

- **Status:** done (started 2026-07-12T02:45:24Z; finished 2026-07-12T02:55:56Z)
- **File:** `LatticeJ.lean`
- **Depends on:** T001, T002, existing `XYin/uniqueness.lean`
- **Declarations:** `discriminant_ne_zero`, `j_eq_of_homothetic`, `homothetic_of_j_eq`,
  `j_eq_iff_homothetic`, `exists_homothetic_periodPair`.
- **Source:** Proposition 10.7 and Theorem 10.9, printed pp. 206–208 / PDF pp. 218–220.
- **Proof sketch:** normalize any period pair to `[1,τ]` for nonvanishing; for classification,
  split `g₂=0`, `g₃=0`, and the generic case, choose fourth/sixth roots in `ℂ`, then apply
  `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq`.
- **Validation:** explicit tests cover `j=0` and `j=1728`; axiom audit excludes `sorryAx`.
- **Progress:**
  - 2026-07-12T02:45:24Z: picked by beastmode after T002; split API/axiom research across
    discriminant nonvanishing, homothety classification, and period-pair normalization.
  - 2026-07-12T02:50:00Z: normalized every period pair to `[1,τ]`, transferred modular
    discriminant nonvanishing to arbitrary lattices, and completed the three classification
    branches (`j = 0`, `j = 1728`, and generic).
  - 2026-07-12T02:55:56Z: DONE — all five declarations are sorry-free; focused build,
    standard-axiom audit, two exceptional-branch tests, diff/style gates, simplify pass, and buzz
    FAST-BOARD pass. Cleanup record: `.mathlib-quality/cleanup-t003.md`.

### [T004] Port homothety iff `SL₂(ℤ)` orbit

- **Status:** done (started 2026-07-12T02:56:15Z; finished 2026-07-12T03:02:59Z)
- **File:** `LatticeJ.lean`
- **Depends on:** T001
- **Declaration:** `periodPair_homothetic_iff_exists_sl2_smul_eq`.
- **Source:** Cox equation (7.8), printed p. 138 / PDF p. 150.
- **Proof sketch:** port the existing axiom-clean theorem from `main`; read integral basis-change
  matrices in both directions, prove determinant `±1`, exclude `-1` by imaginary-part
  positivity, and construct the reverse scaling from the modular denominator.
- **Validation:** test the `S` and `T` generators and action direction; axiom audit.
- **Progress:**
  - 2026-07-12T02:56:15Z: picked by beastmode after T003; started a statement-direction audit,
    historical clean-proof port, and independent `S`/`T` generator tests.
  - 2026-07-12T02:59:00Z: ported the integer change-of-basis proof; checked determinant `-1`
    exclusion and the inverse-denominator scaling direction independently.
  - 2026-07-12T03:02:59Z: DONE — theorem is sorry-free; focused build, standard-axiom audit,
    independent `S`/`T` homothety and direction tests, diff/style gates, simplify pass, and buzz
    FAST-BOARD pass. Cleanup record: `.mathlib-quality/cleanup-t004.md`.

### [T005] Finish analytic `j` injectivity and surjectivity

- **Status:** done (started 2026-07-12T03:03:16Z; finished 2026-07-12T03:13:40Z)
- **File:** `LatticeJ.lean`
- **Depends on:** T002, T003, T004
- **Declarations:** `j_eq_iff_exists_sl2_smul_eq`, `j_surjective`.
- **Source:** Theorem 11.2(ii)–(iii), printed p. 221 / PDF p. 233.
- **Proof sketch:** injectivity is a three-line composition of the requested bridge,
  homothety classification, and T004.  Adapt the existing surjectivity proof to the current `j`,
  using its pole at infinity and fundamental-domain topology.
- **Validation:** axiom audit; test that every chosen preimage lies in `ℍ`; no duplicate global
  definition of `j`.
- **Progress:**
  - 2026-07-12T03:03:16Z: picked by beastmode after T004; injectivity composition and all
    available surjectivity implementations are being audited separately for transitive
    `sorryAx` dependencies.
  - 2026-07-12T03:07:00Z: injectivity reduced to the four requested bridges; selected the clean
    weight-zero cusp-form contradiction for surjectivity and rebuilt the missing analytic and
    `qj → 1` interfaces without the contaminated q-expansion coefficient theorem.
  - 2026-07-12T03:13:40Z: DONE — both declarations and the entire file are sorry-free; focused
    and full builds, standard-axiom audits, `S`/`T` and upper-half-plane witness tests,
    diff/style gates, simplify pass, and buzz FAST-BOARD pass. Cleanup record:
    `.mathlib-quality/cleanup-t005.md`.

## Phase 2 — Hermite normal form

### [T006] Prove HNF coordinate API and rank-two existence

- **Status:** done (started 2026-07-12T03:14:34Z; finished 2026-07-12T03:37:12Z)
- **File:** `HermiteNormalForm.lean`
- **Depends on:** T000
- **Declarations:** `HermiteNormalForm.repr_apply`, `Submodule.exists_hermiteNormalForm`.
- **Source:** Exercise 11.17, printed p. 247 / PDF p. 259.
- **Proof sketch:** first prove the `Fin 2` case: choose the least positive first coordinate in
  the full-rank submodule, choose a second basis vector, make both pivots positive, and use
  Euclidean division to reduce the upper entry.  If the induction is clean, generalize to `Fin n`;
  otherwise specialize the public existence theorem compatibly and postpone arbitrary rank.
- **Validation:** examples for `⊤`, diagonal submodules, and a matrix requiring reduction.
- **Progress:**
  - 2026-07-12T03:14:34Z: picked by beastmode after T005; comparing the bundled definition
    field-by-field with `Module.Basis.SmithNormalForm`, auditing whether general-rank existence
    is supportable, and developing the rank-two construction and examples in parallel.
  - 2026-07-12T03:25:00Z: generalized the HNF predicate to preorder-indexed matrices with named
    fields, retained the Smith-style fixed-ambient-basis bundle, and specialized only the public
    existence/choice API to the Cox-required rank-two case after confirming mathlib has no
    arbitrary-rank fixed-basis HNF reducer.
  - 2026-07-12T03:37:12Z: DONE — gcd/Bézout column reduction, positive pivots, Euclidean remainder,
    and the induced submodule basis are sorry-free; top/diagonal/nontrivial-reduction examples,
    focused and full builds, standard-axiom audit, diff/style gates, and buzz FAST-BOARD pass.
    Cleanup record: `.mathlib-quality/cleanup-t006.md`.

### [T007] Prove HNF uniqueness and determinant/index

- **Status:** done (started 2026-07-12T03:38:04Z; finished 2026-07-12T03:44:48Z)
- **File:** `HermiteNormalForm.lean`
- **Depends on:** T006
- **Declarations:** `HermiteNormalForm.matrix_eq`, `bN_eq`, `index_eq_natAbs_det`.
- **Source:** Exercises 7.15 and 11.17.
- **Proof sketch:** compare least positive pivots, then reduced residues; derive basis equality
  from equal coordinate columns.  Apply `Submodule.natAbs_det_basis_change` or the corresponding
  `AddSubgroup.index_eq_natAbs_det` theorem for the index.
- **Validation:** two independently constructed HNFs of the same test submodule have identical
  matrices; audit no quotient-cardinality finiteness assumption is smuggled in.
- **Progress:**
  - 2026-07-12T03:38:04Z: picked immediately after the T006 board rescan; rank-two uniqueness
    and determinant/index proofs are being developed and axiom-audited independently.
  - 2026-07-12T03:41:00Z: compared the two HNF bases through integral transition matrices in
    both directions, fixed both positive pivots by mutual divisibility, and fixed the reduced
    residue by Euclidean remainder uniqueness; basis equality then follows coordinatewise.
  - 2026-07-12T03:44:48Z: DONE — rank-two matrix/basis uniqueness and arbitrary-rank index are
    sorry-free; the concrete `!![5,4;0,2]` example has unique HNF and index ten; focused/full
    builds, standard-axiom audit, diff/style gates, independent proof review, and buzz FAST-BOARD
    pass. Cleanup record: `.mathlib-quality/cleanup-t007.md`.

### [T008] Prove primitive matrix iff cyclic quotient

- **Status:** done (started 2026-07-12T03:45:22Z; finished 2026-07-12T03:55:53Z)
- **File:** `HermiteNormalForm.lean`
- **Depends on:** T006, T007
- **Declaration:** `quotient_isAddCyclic_iff_rankTwoContent_eq_one`.
- **Source:** equation (11.25) and Exercise 11.16, printed pp. 235,247 / PDF pp. 247,259.
- **Proof sketch:** use Bézout coefficients of the four entries to construct a generator of the
  quotient when the content is one.  Conversely, a common divisor gives a quotient surjection
  onto `(ZMod d)²`, which is noncyclic for `d>1`.
- **Do not assume:** mathlib's `SmithNormalForm` coefficients are invariant-factor normalized.
- **Validation:** matrices `diag(2,2)` (noncyclic) and `diag(1,m)` (cyclic).
- **Progress:**
  - 2026-07-12T03:45:22Z: picked immediately after the T007 board rescan; quotient structure,
    Smith-normal-form alternatives, and direct Bézout constructions are being audited in
    parallel before fixing the proof route.
  - 2026-07-12T03:50:00Z: transported the quotient to two arbitrary Smith `ZMod` factors and
    proved entry-content invariant under both ambient and submodule basis changes, deliberately
    avoiding any invariant-factor normalization assumption.
  - 2026-07-12T03:55:53Z: DONE — the primitive-content/cyclic-quotient equivalence is sorry-free,
    and the entire HNF file is now clean; `diag(2,2)` and `diag(1,m)` validations, focused/full
    builds, standard-axiom audit, independent review, diff/style gates, and buzz FAST-BOARD pass.
    Cleanup record: `.mathlib-quality/cleanup-t008.md`.

## Phase 3 — modular functions and Theorem 11.9(i)

### [T009] Establish the modular-function base API

- **Status:** done (started 2026-07-12T03:56:54Z; finished 2026-07-12T04:37:46Z)
- **File:** `ModularFunction.lean`
- **Depends on:** T005
- **Declarations:** `periodic_comp_sl2`, `cusp_laurent_finitePrincipalPart`,
  `j_isLevelOneModularFunction`, `j_isGamma0ModularFunction`,
  `levelJ_isGamma0ModularFunction`.
- **Source:** printed pp. 225–226 / PDF pp. 237–238 and the matrix calculation on printed p. 228.
- **Proof sketch:** conjugate the translation matrix by `γ`, use subgroup membership, then the
  existing cusp/Laurent API.  Reuse `j_slashInvariant`, `jN_slashInvariant`, and existing
  meromorphicity facts.
- **Validation:** check all widths are `N`, not `1`; test cusp precomposition by `S` and `T`.
- **Progress:**
  - 2026-07-12T03:56:54Z: picked immediately after the T008 board rescan; auditing the exact
    periodicity conjugation, cusp Laurent-order API, and clean analytic/invariance interfaces for
    `j` and `j(Nτ)` in parallel.
  - 2026-07-12T04:15:00Z: the four periodicity/Laurent/analytic-`j` declarations were proved;
    the remaining arbitrary-cusp case for `j(Nτ)` was reduced by
    `δ⁻¹ diag(N,1) γ = [[g,r],[0,s]]`, with `g*s=N` and q-coordinate exponent `g^2`.
  - 2026-07-12T04:37:46Z: DONE — all five targets are sorry-free and standard-axiom clean;
    `S`/`T` cusp regressions, focused and full builds, proof-length/style gates, independent
    matrix/q-coordinate review, simplify, and FAST-BOARD buzz pass. Cleanup record:
    `.mathlib-quality/cleanup-t009.md`.

### [T010] Prove Cox Lemma 11.10

- **Status:** done (started 2026-07-12T04:38:07Z; finished 2026-07-12T05:04:19Z)
- **File:** `ModularFunction.lean`
- **Depends on:** T009
- **Declarations:** `levelOne_constant_of_holomorphic`,
  `levelOne_polynomialInJ_of_holomorphic`.
- **Source:** printed pp. 226–227 / PDF pp. 238–239.
- **Proof sketch:** reduce every point to mathlib's standard fundamental domain.  Split bounded
  and unbounded imaginary parts for compactness and cusp convergence; apply maximum modulus.
  For part (ii), recursively subtract a polynomial in `j` matching the finite principal part.
- **Validation:** constants and `j^n+c` examples; ensure the theorem rejects functions with an
  internal pole.
- **Progress:**
  - 2026-07-12T04:38:07Z: picked immediately after T009 completion and board rescan; auditing
    existing fundamental-domain compactness/maximum-principle APIs and Laurent principal-part
    operations before choosing the shortest standard-axiom proof route.
  - 2026-07-12T04:46:00Z: packaged the bounded level-one function as a weight-zero modular form
    and applied mathlib's maximum-principle theorem; built a trailing-coefficient cancellation
    lemma giving strict descent of the cusp pole order.
  - 2026-07-12T05:04:19Z: DONE — both parts are sorry-free and standard-axiom clean; repaired the
    old `j_poleOrder` dependency on `E4_q_exp`, checked constants and `j^n+c`, passed focused/full
    builds, independent review, diff/style gates, simplify, and FAST-BOARD buzz. Cleanup record:
    `.mathlib-quality/cleanup-t010.md`.

### [T011] Prove finite pole orbits and pole clearing

- **Status:** done (started 2026-07-12T05:05:21Z; finished 2026-07-12T05:27:00Z)
- **File:** `ModularFunction.lean`
- **Depends on:** T009, T010
- **Declaration:** `levelOne_exists_polynomial_clearing_poles`.
- **Source:** printed pp. 227–228 / PDF pp. 239–240; Exercise 11.7.
- **Proof sketch:** use a meromorphic divisor/locally finite pole support on a compact truncated
  fundamental region.  For each orbit, clear an ordinary pole by `j-j(τ₀)`; at `i` prove even
  order, and at the order-three elliptic point prove divisibility by three.
- **Validation:** explicit local stabilizer equations; `P ≠ 0`; no assumption that `j'` is
  nonzero at elliptic points.
- **Progress:**
  - 2026-07-12T05:05:21Z: picked immediately after T010 completion and board rescan; auditing
    compact fundamental-domain pole finiteness, meromorphic divisor APIs, and local stabilizer
    order formulas in parallel.
  - 2026-07-12T05:15:00Z: replaced exact order cancellation by a uniform extra-power dslope
    argument, because `MeromorphicAt` permits arbitrary stored values at removable singularities;
    compactness now tracks every non-differentiable point, not only negative-order poles.
  - 2026-07-12T05:27:00Z: DONE — the finite correction polynomial is nonzero and makes the
    product globally differentiable; focused/full builds, standard-axiom audit, independent
    review, diff/style gates, simplify, and FAST-BOARD buzz pass. Cleanup record:
    `.mathlib-quality/cleanup-t011.md`.

### [T012] Assemble Theorem 11.9(i)

- **Status:** done (started 2026-07-12T05:27:00Z; finished 2026-07-12T05:34:49Z)
- **File:** `ModularFunction.lean`
- **Depends on:** T010, T011
- **Declaration:** `theorem_11_9_i`.
- **Source:** Theorem 11.9(i), printed p. 226 / PDF p. 238.
- **Proof sketch:** apply Lemma 11.10(ii) to `P(j)f`, then divide by nonzero `P(j)` using the
  guarded `RationalIn` predicate.
- **Validation:** rational functions with denominators vanishing at ordinary and elliptic values.
- **Progress:**
  - 2026-07-12T05:27:00Z: picked immediately after T011 completion and board rescan; auditing
    modular-function closure under products and polynomial evaluation before applying Lemma
    11.10(ii).
  - 2026-07-12T05:30:00Z: generalized product and polynomial-evaluation closure to arbitrary
    `Γ₀(N)` and packaged both as chainable `IsGamma0ModularFunction` methods.
  - 2026-07-12T05:34:49Z: DONE — T011 and Lemma 11.10(ii) now assemble to the guarded rational
    representation with numerator `Q` and nonzero denominator `P`; focused/full builds,
    standard-axiom audit, ordinary/elliptic denominator tests, independent review, diff/style
    gates, simplify, and FAST-BOARD buzz pass. Cleanup record:
    `.mathlib-quality/cleanup-t012.md`.

## Phase 4 — Cox representatives and q-expansions

### [T013] Finish `CoxMatrix` elementary and HNF links

- **Status:** done (started 2026-07-12T05:34:49Z; finished 2026-07-12T05:43:48Z)
- **File:** `CoxMatrices.lean`
- **Depends on:** T006, T008
- **Declarations:** positivity/bounds, `toFin_injective`, inclusion-HNF/determinant/content
  theorems, `sigmaZero`, `j_act_sigmaZero`.
- **Source:** definition of `C(m)`, printed p. 228 / PDF p. 240.
- **Proof sketch:** arithmetic with `ad=m`; unfold matrix notation; use T008 for the semantic
  primitive interpretation.
- **Validation:** enumerate `C(1)`, `C(2)`, `C(3)` and check `sigmaZero`.
- **Progress:**
  - 2026-07-12T05:34:49Z: picked immediately after T012 completion and board rescan; auditing the
    existing `CoxMatrix` skeleton, arithmetic invariants, HNF bridge, and small-level enumeration
    in parallel.
  - 2026-07-12T05:39:00Z: proved positivity/bounds, HNF/determinant/content, and bounded-encoding
    injectivity; defined the computable distinguished representative `diag(m,1)` and checked the
    action direction against `levelJ`.
  - 2026-07-12T05:43:48Z: DONE — all nine targets are sorry-free; structural enumerations of
    `C(1)`, `C(2)`, and `C(3)`, focused/full builds, standard-axiom audit, independent reviews,
    diff/style gates, simplify, and FAST-BOARD buzz pass. Cleanup record:
    `.mathlib-quality/cleanup-t013.md`.

### [T014] Prove Lemma 11.11 (right-coset equivalence)

- **Status:** done (started 2026-07-12T05:43:48Z; finished 2026-07-12T06:29:55Z)
- **File:** `CoxMatrices.lean`
- **Depends on:** T007, T013, T009
- **Declarations:** `coxMatrixEquivRightCosets`, `rightCosetEval`, `rightCosetTranslate`,
  `rightCosetEval_equiv`, `rightCosetTranslate_sigmaZero`.
- **Source:** Lemma 11.11 and Exercise 11.8, printed pp. 228,245 / PDF pp. 240,257.
- **Proof sketch:** associate to a right coset the unique primitive determinant-`m` HNF matrix;
  prove independence and inverse laws.  Define quotient lifts using `Γ₀(m)` invariance.
- **Validation:** explicit right/left orientation test; bijection cardinal check for levels 2,3.
- **Progress:**
  - 2026-07-12T05:43:48Z: picked immediately after T013 completion and board rescan; auditing
    quotient orientations, HNF normalization, representative independence, and the distinguished
    identity coset in parallel.
  - 2026-07-12T06:10:00Z: proved the exact right-coset kernel of the canonical column-HNF map;
    a primitive Smith normalization using finite prime avoidance closed its surjectivity.
  - 2026-07-12T06:20:00Z: constructed the quotient equivalence and quotient lifts, then derived
    the analytic evaluation formula from `δ⁻¹ diag(m,1) γ = σ.mobiusMatrix`.
  - 2026-07-12T06:29:55Z: DONE — all five targets and their representative computation API are
    sorry-free; focused/full builds, standard-axiom audits, identity-coset/inverse-law tests,
    independent direction reviews, diff/style gates, simplify, and FAST-BOARD buzz pass.
    Cleanup record: `.mathlib-quality/cleanup-t014.md`.

### [T015] Prove the `C(m)` cardinal formula

- **Status:** done (started 2026-07-12T06:30:47Z; finished 2026-07-12T06:54:29Z)
- **File:** `CoxMatrices.lean`
- **Depends on:** T013
- **Declaration:** `card_coxMatrix`.
- **Source:** Exercise 11.9, printed pp. 245–246 / PDF pp. 257–258.
- **Proof sketch:** count `b` for each divisor `d`, prove multiplicativity, evaluate prime powers,
  and rewrite as the Euler product.
- **Validation:** native/norm-num checks for `m≤20` against direct `Fintype.card`.
- **Progress:**
  - 2026-07-12T06:30:47Z: picked immediately after T014 completion and board rescan; direct
    divisor/totient counting and the existing `Γ₀(m)` index formula are being audited in
    parallel, with small-level enumeration reserved as an independent check.
  - 2026-07-12T06:42:00Z: decomposed `CoxMatrix m` into fixed-`d` fibers of cardinality
    `(d/g) * φ(g)`, where `g = gcd (m/d) d`, and proved the resulting divisor sum
    multiplicative on coprime inputs.
  - 2026-07-12T06:48:00Z: evaluated the prime-power sum as `p^e + p^(e-1)` by totient
    telescoping and converted multiplicative factorization into the rational Euler product.
  - 2026-07-12T06:54:29Z: DONE — the cardinal formula is sorry-free; direct bounded-triple
    counts agree for levels 1 through 20, and focused/full builds, standard-axiom audit,
    independent arithmetic review, diff/style gates, simplify, and FAST-BOARD buzz pass.
    Cleanup record: `.mathlib-quality/cleanup-t015.md`.

### [T016] Prove exact transformed-root Laurent expansion and Galois reindexing

- **Status:** done (started 2026-07-12T06:54:29Z; finished 2026-07-12T07:44:26Z)
- **File:** `CoxMatrices.lean`
- **Depends on:** T002, T013, T014
- **Declarations:** `zeta_isPrimitiveRoot`, `jIntCoeff_spec`, `jIntCoeff_neg_one`,
  `laurentqExpansion_coxAction`, `reindex`, `reindex_bijective`.
- **Source:** equations (11.12), (11.13), printed p. 229 / PDF p. 241.
- **Proof sketch:** prove the width-`m` cusp identity under `τ↦(aτ+b)/d`; substitute the
  integral Laurent expansion of `j`; establish coefficient equality and support.  For reindexing,
  use a modular inverse of `k` modulo every `d|m`.
- **Validation:** coefficient `-a²` equals `ζ^(-ab)`; zero below `-a²`; compare `m=2` roots.
- **Progress:**
  - 2026-07-12T06:54:29Z: picked immediately after T015 completion and board rescan; the
    primitive-root leaf is already clean, while the tainted integral-q-expansion dependency,
    exact Laurent substitution, and modular-inverse reindexing are being attacked separately.
  - 2026-07-12T07:15:00Z: replaced the native q-expansion dependency by mathlib's Eisenstein
    coefficient formula and discriminant identity, making the complete integral Laurent chain
    standard-axiom clean; constructed the residue permutation `b ↦ b*k mod d`.
  - 2026-07-12T07:31:00Z: proved the exact identity
    `q₁(σ τ)=ζ_m^(ab) q_m(τ)^(a²)`, computed pole order `a²`, and identified the pole-removed
    series by `rescale` plus `expand` using q-expansion uniqueness.
  - 2026-07-12T07:44:26Z: DONE — all six targets are sorry-free and standard-axiom clean;
    leading coefficient/support checks, the three level-two roots with phases `1,1,-1`, focused
    and 3883-job full builds, independent reviews, diff/style/import gates, simplify, and
    FAST-BOARD buzz pass. Cleanup record: `.mathlib-quality/cleanup-t016.md`.

## Phase 5 — modular equation and Theorem 11.9(ii)

### [T017] Construct the complex modular polynomial

- **Status:** done (started 2026-07-12T07:45:30Z; finished 2026-07-12T08:30:17Z)
- **File:** `ModularPolynomial.lean`
- **Depends on:** T010, T014, T016
- **Declarations:** `coxPhiFunction_coeff_isLevelOne`,
  `coxPhiFunction_coeff_polynomialInJ`, `existsUnique_modularPolynomialC`, monicity, product
  formulas, distinguished root, degree.
- **Source:** equations (11.14), (11.15), printed pp. 229–230 / PDF pp. 241–242.
- **Proof sketch:** product coefficients are holomorphic on `ℍ`, invariant by coset permutation,
  and meromorphic at the cusp via T016; apply Lemma 11.10.  Use `j_surjective` and monicity for
  uniqueness.
- **Validation:** semantic evaluation order `(x,y)`; `m=1` gives the expected linear equation;
  degree equals `Fintype.card (CoxMatrix m)`.
- **Progress:**
  - 2026-07-12T07:45:30Z: picked immediately after T016 completion and board rescan; auditing
    the existing polynomial skeleton, finite-product coefficient API, coset permutation
    invariance, and cusp holomorphy interfaces in parallel.
  - 2026-07-12T08:10:00Z: completed the right-coset permutation, holomorphy, width-`m` cusp
    analysis, and the open-power-map descent to width one; every coefficient is now a level-one
    modular function and hence polynomial in `j`.
  - 2026-07-12T08:30:17Z: DONE — constructed the unique monic complex modular polynomial and
    proved its product formulas, distinguished root, and degree.  The `m=1` equation is `X-Y`;
    30 public declarations are standard-axiom clean; focused and 3885-job full builds, linters,
    diff/import gates, simplify, and FAST-BOARD buzz pass. Cleanup record:
    `.mathlib-quality/cleanup-t017.md`.

### [T018] Prove interpolation and Theorem 11.9(ii)

- **Status:** done (started 2026-07-12T10:29:27Z; finished 2026-07-12T11:02:26Z)
- **File:** `ModularPolynomial.lean`, `ModularFunction.lean`
- **Depends on:** T012, T014, T017, T021
- **Declarations:** `interpolation_coeff_isLevelOne`, `recoveryFormula`, `theorem_11_9_ii`.
- **Source:** equations (11.16), (11.17), Exercise 11.11, printed pp. 230–231,246 /
  PDF pp. 242–243,258.
- **Proof sketch:** prove coset-permutation invariance and cusp meromorphicity coefficientwise;
  apply Theorem 11.9(i).  Evaluate the Lagrange sum at the distinguished root and use
  irreducibility/separability for the derivative denominator.
- **Validation:** formula is guarded at specialized collisions; final result uses
  `RationalInTwo` rather than unconditional pointwise division.
- **Progress:**
  - 2026-07-12T08:30:17Z: preflight found that T021 is a genuine unmet dependency and that the
    current `RationalInTwo` denominator condition permits a vacuous zero-on-the-curve witness.
    The ticket remains open until T019--T021 are complete; its final implementation must
    strengthen that condition and move `theorem_11_9_ii` above the import cycle.
  - 2026-07-12T10:29:27Z: resumed after T021; strengthened `RationalInTwo` to require a
    denominator that is nonzero as a function along the modular curve and removed the cyclic
    theorem stub from `ModularFunction.lean`.
  - 2026-07-12T10:47:00Z: proved coefficientwise level-one modularity by right-coset
    reindexing, upper-half-plane meromorphicity, width-`m` cusp control, and width-one descent;
    proved the guarded Lagrange recovery formula.
  - 2026-07-12T11:02:26Z: DONE — assembled the nonvacuous bivariate denominator and
    `theorem_11_9_ii`; strict/focused/full builds, standard-axiom audits, levels `1`--`3`, a CM
    collision regression, style gates, and the threshold-1000 ms profile pass. Cleanup record:
    `.mathlib-quality/cleanup-t018.md`.

## Phase 6 — Theorem 11.18(i),(ii)

### [T019] Galois descent to integer Laurent coefficients

- **Status:** done (started 2026-07-12T08:32:12Z; finished 2026-07-12T09:07:53Z)
- **File:** `ModularPolynomial.lean`
- **Depends on:** T016, T017
- **Declaration:** `coxPhiFunction_coeff_integerLaurent`.
- **Source:** proof of 11.18(i), printed pp. 231–232 / PDF pp. 243–244.
- **Proof sketch:** model roots over a cyclotomic field; use `reindex_bijective` to show every
  Galois automorphism permutes them; fixed coefficients are rational.  Combine root-of-unity and
  integer `j` coefficients for algebraic integrality, then use period one to eliminate fractional
  exponents.
- **Validation:** test constant/leading symmetric coefficients and `m=2,3`; distinguish rational
  from integral steps explicitly.
- **Progress:**
  - 2026-07-12T08:32:12Z: picked after the T018 dependency audit; the cyclotomic Galois
    permutation, algebraic-integrality descent, and period-one elimination of fractional
    exponents are being audited independently.
  - 2026-07-12T08:52:00Z: constructed the formal Cox product over a concrete cyclotomic field;
    Galois automorphisms reindex its roots, so fixed-field and integrality descent put every
    formal Laurent coefficient in `ℤ`.
  - 2026-07-12T09:07:53Z: DONE — proved the analytic/formal product bridge and exact width-`m`
    coefficient scaling, hence every analytic Cox coefficient has integral Laurent coefficients.
    Levels `1,2,3`, monicity, standard axioms, linters, focused and 3888-job full builds,
    diff/import gates, simplify, and FAST-BOARD buzz pass. Cleanup record:
    `.mathlib-quality/cleanup-t019.md`.

### [T020] Prove Hasse q-expansion principle and integer descent

- **Status:** done (started 2026-07-12T09:07:53Z; finished 2026-07-12T09:28:58Z)
- **File:** `ModularPolynomial.lean`, `Arithmetic.lean`
- **Depends on:** T010, T019
- **Declarations:** `hasse_qExpansion_principle`, `exists_modularPolynomialZ`,
  `modularPolynomial_map_complex`, `theorem_11_18_i`.
- **Source:** Exercise 11.12 and 11.18(i), printed pp. 232,246 / PDF pp. 244,258.
- **Proof sketch:** prove the lowest Laurent coefficient of `P(j)` is `P.leadingCoeff`; induct on
  degree, subtracting integer multiples of `X^d`.  Assemble coefficient polynomials and use
  injectivity of nested `Polynomial.map` for uniqueness.
- **Validation:** Hasse on degree 0 and zero polynomial; coefficientwise map injectivity; axiom
  audit of part (i).
- **Progress:**
  - 2026-07-12T09:07:53Z: picked immediately after T019 completion and board rescan; the
    triangular Laurent-coefficient lemma, degree induction, and nested polynomial descent are
    being developed independently.
  - 2026-07-12T09:18:00Z: proved `[q^(-deg P)]P(j)=leadingCoeff P`, packaged exact integer
    Laurent coefficients as a subring, and closed the Hasse induction by stripping `eraseLead`.
  - 2026-07-12T09:28:58Z: DONE — descended every outer coefficient through Hasse and assembled
    the integral bivariate polynomial with `Polynomial.lifts`; proved the comparison theorem and
    Theorem 11.18(i). Zero/constant cases, nested-map injectivity, levels `1,2,3`, standard axioms,
    linters, focused and 3888-job full builds, diff/import gates, simplify, and FAST-BOARD buzz
    pass. Cleanup record: `.mathlib-quality/cleanup-t020.md`.

### [T021] Prove irreducibility in `ℂ(Y)[X]`

- **Status:** done (started 2026-07-12T09:28:58Z; finished 2026-07-12T10:29:27Z)
- **File:** `ModularPolynomial.lean`, `Arithmetic.lean`
- **Depends on:** T014, T016, T017
- **Declarations:** `modularPolynomialC_irreducibleInX`, `theorem_11_18_ii`.
- **Source:** Exercise 11.10, printed p. 246 / PDF p. 258.
- **Proof sketch:** define the function field `ℂ(j,j_m)` and its embeddings by precomposition
  with coset representatives.  T016 proves the conjugates are distinct, giving at least
  `|C(m)|` embeddings; the root polynomial gives the opposite degree bound, hence it is minimal.
  Transport to the formal coefficient field `ℂ(Y)` via evaluation/transcendence.
- **Validation:** variable direction outer `X`; degree matches T017; no use of symmetry.
- **Progress:**
  - 2026-07-12T09:28:58Z: picked immediately after T020 completion and board rescan; function-field
    embeddings, conjugate distinctness, and transport to `ℂ(Y)` are being audited independently.
  - 2026-07-12T10:05:00Z: realized `ℂ(Y)` inside the fraction field of holomorphic functions on
    `ℍ`; precomposition gives base-field automorphisms acting transitively on the right-coset
    roots. Laurent leading terms prove that the roots are distinct as functions, avoiding the
    false fixed-point injectivity statement at CM points.
  - 2026-07-12T10:29:27Z: DONE — the mapped Cox product equals the minimal polynomial of its
    base-coset root and is irreducible; Theorem 11.18(ii) is proved. Levels `1,2,3`, the CM
    collision regression, standard axioms, linters, warning-as-error, focused and 3889-job full
    builds, diff/import gates, generalization, simplify, and FAST-BOARD buzz pass. Cleanup record:
    `.mathlib-quality/cleanup-t021.md`.

## Phase 7 — cyclic sublattices and Theorem 11.23

### [T022] Construct canonical period pairs and scaling/dual operations

- **Status:** done (started 2026-07-12T11:02:26Z; finished 2026-07-12T11:37:25Z)
- **File:** `CyclicSublattice/Classification.lean`
- **Depends on:** T003, T006–T008
- **Declarations:** `toPeriodPair`, `toPeriodPair_lattice`, `hermiteNormalForm`, `scale`,
  `j_scale`, `dual`, `dual_sub_j`, `dual_base_j`.
- **Source:** definition before Theorem 11.23 and the dual-inclusion argument used for symmetry.
- **Proof sketch:** obtain a rank-two HNF basis, map it into `ℂ`, and prove real linear
  independence from finite index.  Transport carriers through `PeriodPair.smulLatticeEquiv`.
  In HNF coordinates, show `mL⊂L'` and compute both quotients.
- **Validation:** constructions depend only on carrier; scale by two different units; dual of a
  diagonal cyclic inclusion.
- **Progress:**
  - 2026-07-12T11:02:26Z: picked immediately after T018; finite-index rank, HNF period-pair
    construction, scaling transport, and the dual inclusion are being prototyped independently.
  - 2026-07-12T11:20:00Z: the canonical HNF periods, exact carrier lattice, scaling equivalence,
    quotient transport, and `j_scale` were completed; the arbitrary-basis primitive-matrix
    criterion was extracted from T008 for duality.
  - 2026-07-12T11:37:25Z: DONE — the adjugate inclusion matrix constructs the cyclic dual of
    index `m`, its carrier is exactly `mL`, and both dual `j` identities hold. Standard-axiom
    audits, unit/top regressions, focused/full builds, style gates, and the optimized
    threshold-1000 ms profile pass. Cleanup record: `.mathlib-quality/cleanup-t022.md`.

### [T023] Prove Lemma 11.24 by HNF

- **Status:** done (started 2026-07-12T11:38:00Z; finished 2026-07-12T11:59:32Z)
- **File:** `CyclicSublattice.lean`
- **Depends on:** T013, T022
- **Declarations:** `CoxMatrix.sublattice`, `toCyclicSublattice`,
  `cyclicSublatticeEquivCoxMatrix`, `cyclicSublattice_hnf_matrix`,
  `coxMatrix_toPeriodPair_lattice`.
- **Source:** Lemma 11.24 and Exercise 11.17, printed pp. 235–236,247 /
  PDF pp. 247–248,259.
- **Proof sketch:** use HNF existence to extract `d,b,a`; determinant/index yields `ad=m`, T008
  yields gcd-one, and HNF uniqueness yields the unique `σ`.  Conversely construct the carrier
  from the inclusion matrix.
- **Validation:** round-trip both equivalence directions; verify lattice equality
  `[d,aτ+b]=d[1,στ]`.
- **Progress:**
  - 2026-07-12T11:38:00Z: picked immediately after T022; HNF extraction, the converse
    column-range construction, both equivalence round trips, and the explicit lattice identity
    are being integrated from independently strict-compiled prototypes.
  - 2026-07-12T11:49:00Z: the arbitrary-period-pair equivalence and both round trips were
    completed; cleanup replaced `Int.toNat` by `Int.natAbs`, generalized HNF column-range
    semantics to arbitrary rank, and replaced bounded encodings by carrier/matrix extensionality.
  - 2026-07-12T11:59:32Z: DONE — the required five declarations and the generalized backend are
    sorry-free and standard-axiom clean; `m = 1`, non-diagonal `m = 2`, HNF, and
    `[d,aτ+b]=d[1,στ]` regressions pass. Focused/strict/full builds, style/diff gates,
    independent reviews, and threshold-1000 ms profiling pass. Cleanup record:
    `.mathlib-quality/cleanup-t023.md`.

### [T024] Prove Theorem 11.23

- **Status:** done (started 2026-07-12T12:00:00Z; finished 2026-07-12T12:21:54Z)
- **Files:** `CyclicSublattice.lean`, `CyclicSublattice/Classification.lean`
- **Depends on:** T005, T017, T022, T023
- **Declarations:** `modularPolynomialC_zero_iff_normalizedCyclicSublattice`, `theorem_11_23`.
- **Source:** Theorem 11.23 and Exercise 11.18, printed pp. 235–236,248 /
  PDF pp. 247–248,260.
- **Proof sketch:** normalized result is exactly the product roots plus Lemma 11.24 and `j_smul`.
  Globally, use `j_surjective` forward; normalize/scale both lattices reverse.
- **Validation:** no import of `Arithmetic.lean`; semantic `(u,v)` order checked; both directions
  preserve index and cyclicity.
- **Progress:**
  - 2026-07-12T12:00:00Z: picked immediately after T023; the normalized product-root
    classification and the global scale/normalization argument are being developed and audited
    independently.
  - 2026-07-12T12:10:00Z: completed the normalized root classification and global theorem;
    introduced a general lattice-equivalence transport and verified that the reverse direction
    scales by `a` in the required `(u,v) = (S.j,L.j)` order.
  - 2026-07-12T12:21:54Z: DONE — both targets and all transport bridges are sorry-free and
    standard-axiom clean. Split classification from the 674-line cyclic-sublattice core; strict,
    adversarial, scale-direction, style, profile, and 3891-job full-build gates pass. Cleanup
    record: `.mathlib-quality/cleanup-t024.md`.

## Phase 8 — Theorem 11.18(iii)–(v)

### [T025] Prove symmetry from Theorem 11.23

- **Status:** done (started 2026-07-12T12:21:54Z; finished 2026-07-12T12:52:32Z)
- **Files:** `Arithmetic.lean`, `ModularPolynomial.lean`, `CoxMatrices.lean`
- **Depends on:** T020, T021, T022, T024
- **Declarations:** `modularPolynomial_dvd_swap`, `theorem_11_18_iii`.
- **Source:** 11.18(iii), printed p. 231 / PDF p. 243; internal replacement for Lang.
- **Proof sketch:** T022 duality makes the zero locus symmetric.  T021 yields divisibility;
  swapping twice makes the quotient a unit.  Reduce units of `ℤ[Y][X]` to `±1`; eliminate `-1`
  using diagonal invariance and degree `>1`/irreducibility.
- **Validation:** `m=1` excluded; test `m=2`; check dependency graph is non-circular.
- **Progress:**
  - 2026-07-12T12:21:54Z: picked immediately after T024; duality-induced zero-locus symmetry,
    polynomial divisibility, and the final integral sign are being audited separately.
  - 2026-07-12T12:38:00Z: dual cyclic inclusions proved the complex zero-locus symmetry; the
    distinguished function-field root and T021 irreducibility gave divisibility, which was
    descended first to `ℂ[Y][X]` and then to `ℤ[Y][X]`.
  - 2026-07-12T12:52:32Z: DONE — divisibility was strengthened to all positive levels. Mutual
    divisibility reduces the quotient to `±1`; the negative sign is excluded for `m > 1` by a
    diagonal linear factor, RatFunc irreducibility, and `|C(m)| > 1`. Strict axioms, level-one
    counterexample, level-two regression, style/profile gates, independent review, focused and
    3891-job full builds pass. Cleanup record: `.mathlib-quality/cleanup-t025.md`.

### [T026] Prove the diagonal theorem

- **Status:** done (started 2026-07-12T12:52:32Z; finished 2026-07-12T13:31:25Z)
- **Files:** `DiagonalLaurent.lean`, `Arithmetic.lean`
- **Depends on:** T016, T020, T025
- **Declarations:** `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`,
  `modularPolynomialDiagonal_leadingCoeff_pow_two_mul`, `theorem_11_18_iv_degree`,
  `theorem_11_18_iv_leadingCoeff`.
- **Source:** equation (11.19) and 11.18(iv), printed p. 233 / PDF p. 245.
- **Proof sketch:** compare Laurent orders `-m` and `-a²`; nonsquare prevents equality.  Use
  leading-coefficient multiplicativity for finite products.  The resulting integer root of unity
  is `±1`.  For the degree, use the fixed point `i/√m` to obtain a root, then use T025 symmetry to
  make the diagonal linear coefficient even and exclude degree one.
- **Validation:** nonsquare levels 2,3,5; a square-level regression demonstrates why the
  hypothesis is needed.
- **Progress:**
  - 2026-07-12T12:52:32Z: picked immediately after T025; Laurent-order separation, diagonal
    degree, and the integral root-of-unity leading coefficient are being audited independently.
  - 2026-07-12T13:31:25Z: DONE — the width-`m` orders are `-m` and `-a²`; nonsquareness separates
    every factor, whose leading coefficient has explicit `2m`-th power one.  A formal-product
    substitution bridge transfers the product to `Φ_m(X,X)` and descends the identity to `ℤ`.
    The fixed point `i/√m` and symmetry/evenness exclude degrees zero and one.  Strict axiom,
    `m=2,3,5`, square-boundary, style/profile, independent-review, focused, and 3892-job full-build
    gates pass. Cleanup record: `.mathlib-quality/cleanup-t026.md`.

### [T027] Prove Kronecker's congruence

- **Status:** done (started 2026-07-12T13:31:25Z; finished 2026-07-12T14:31:45Z)
- **Files:** `LaurentPolynomialEvaluation.lean`, `Kronecker.lean`,
  `KroneckerFrobenius.lean`, `Arithmetic.lean`, `LaurentQExpansion/Algebra.lean`
- **Depends on:** T016, T020
- **Declarations:** `primeCoxMatrixEquiv`, `jLaurentSeriesMod`, `specializeJMod`,
  `specializeJMod_injective`, `kronecker_after_specializeJ`, `theorem_11_18_v`.
- **Source:** equations (11.20), (11.21), Exercises 11.13–11.15, printed pp. 233–234,247 /
  PDF pp. 245–246,259.
- **Proof sketch:** enumerate `C(p)`; work modulo `1-ζ_p`; apply Frobenius to integer
  coefficients; use the cyclotomic norm to pass to modulo `p`; construct the substitution ring
  hom and prove Hasse injectivity via lowest Laurent terms.
- **Validation:** explicit `p=2` and `p=3`; coefficientwise reduction; no odd-prime lemma used
  without a case split.
- **Progress:**
  - 2026-07-12T13:31:25Z: picked immediately after T026; prime Cox-matrix enumeration,
    reduction/Frobenius of Laurent series, and the Hasse specialization injection are being
    decomposed and audited in parallel.
  - 2026-07-12T13:51:51Z: the explicit equivalence sends the first `p` indices to
    `(1,i;0,p)` and the last to `sigmaZero`; Exercise 11.13 now descends through the integral
    cyclotomic polynomial, and the generic lowest-Laurent-term lemma proves injectivity of
    substitution at every unit-leading series of negative order. All three strict subleaves
    compile with standard axioms; the width-`p` Frobenius/product bridge remains in progress.
  - 2026-07-12T14:31:45Z: DONE — cyclotomic descent identifies the reduced canonical
    specialization with the phase-one formal product; explicit prime enumeration and Frobenius
    turn it into `(X^p-Y)(X-Y^p)`, and generic lowest-term injectivity removes the specialization.
    The `p=2,3` regressions, standard-axiom audit, proof-length/style gates, strict and focused
    builds, independent reviews, threshold-1000 ms profiles, and 3895-job full build pass.
    Cleanup record: `.mathlib-quality/cleanup-t027.md`.

### [T028] Verify the explicit `Φ₃` formula

- **Status:** done (started 2026-07-12T14:31:45Z; finished 2026-07-12T16:31:10Z)
- **Files:** `SymmetricCubicLaurent.lean`, `LevelThree.lean`, `Arithmetic.lean`,
  `ModularPolynomial.lean`
- **Depends on:** T017, T020, optionally T027
- **Declaration:** `modularPolynomial_three`.
- **Source:** equation (11.22), printed p. 234 / PDF p. 246.
- **Proof sketch:** preferred: prove the explicit polynomial is monic and has the same
  specialization/product as the canonical one, then use uniqueness.  Alternative: certified
  finite q-expansion comparison once a degree/height bound is established.
- **Validation:** final integer `22973`; symmetry; Kronecker mod 3; distinguished-root check.
- **Progress:**
  - 2026-07-12T14:31:45Z: picked after T027; direct finite coefficient comparison and a
    cyclotomic quadratic-algebra computation were prototyped as fallback routes.
  - 2026-07-12T16:31:10Z: DONE — a kernel-certified width-three/width-nine Laurent jet proves
    the ten necessary coefficients of the explicit candidate vanish.  A reusable symmetric
    bidegree-three detector, monic degree cancellation, the formal `sigmaZero` Cox root, and
    injective base change identify the candidate with `Φ₃`.  The `22973` term, symmetry,
    Kronecker mod 3, distinguished root, standard-axiom, strict, proof-length, style, subsecond
    profile, and independent-review gates pass. Cleanup record:
    `.mathlib-quality/cleanup-t028.md`.

## Phase 9 — cleanup and final audit

### [T029] Cleanup, documentation, and axiom audit

- **Status:** done (started 2026-07-12T16:31:10Z; finished 2026-07-12T16:58:11Z)
- **Files:** all `XYin/PhD/Cox/*.lean`, `XYin.lean`
- **Depends on:** T001–T028
- **Work:** run `/cleanup` and `/cleanup-all`; narrow imports; resolve linters; add tests and source
  docstrings; run full build and public-theorem axiom audit; confirm no dependency on deleted
  `Test` modules.
- **Validation:** zero `sorry` under `XYin/PhD/Cox/`; zero new `sorryAx`; full `lake build`;
  source/statement recheck against `.mathlib-quality/decomposition.md`.
- **Progress:**
  - 2026-07-12T16:31:10Z: picked after T028.  Began three disjoint cleanup batches covering the
    analytic/arithmetic leaves, HNF/lattice/classification leaves, and the two oversized core
    modules.
  - 2026-07-12T16:50:00Z: split `CoxMatrices.lean` and `ModularPolynomial.lean` at mathematical
    layer boundaries while retaining both original paths as compatibility umbrellas.  Every
    resulting Cox source file is below 1000 lines; final strict, axiom, style, and full-build
    gates are in progress.
  - 2026-07-12T16:58:11Z: DONE — all 25 Cox files pass strict compilation and the style checker
    has zero errors.  A 45-endpoint axiom audit reports only the standard axioms; the independent
    source/API review finds the complete §11.B–C target list with no orientation or statement
    defect; the final 3906-job `lake build` succeeds.  Cleanup record:
    `.mathlib-quality/cleanup-t029.md`.

## Milestones

| Milestone | Tickets | Result |
|---|---|---|
| M1 | T001–T008 | axiom-clean lattice `j` and HNF |
| M2 | T009–T018, T021 | complete Theorem 11.9 and complex modular equation |
| M3 | T019–T024 | 11.18(i),(ii), Lemma 11.24, Theorem 11.23 |
| M4 | T025–T029 | 11.18(iii)–(v), `Φ₃`, final quality gate |

## Completion

All tickets T001–T029 are done.  The implementation, source review, public-axiom audit, and final
repository build are complete.

## Takeover extension — elliptic `j`, singular moduli, and bundled Theorem 11.9(ii)

### [T030] Take over, audit sources, and freeze the API

- **Status:** done
- **Files:** `.mathlib-quality/plan.md`, `.mathlib-quality/decomposition.md`, this board
- **Depends on:** T029
- **Work completed:** full report/Cox source review, visual PDF verification, Mathlib API audit,
  clean 3906-job baseline build, exact declaration design, and dependency-cycle review.
- **Source:** Report §§5.3, 6.3; Cox Theorem 11.9 and §11.C.
- **Validation:** the elliptic-curve candidate and bundled-field architecture were separately
  compiled in scratch files; the remaining declarations are first installed as a buildable
  skeleton.

### [T031] Link Mathlib elliptic-curve `j` to lattice and analytic `j`

- **Status:** done (started 2026-07-17; finished 2026-07-17T00:00:20Z)
- **File:** `XYin/PhD/jFunction/jInvariantLink.lean`
- **Depends on:** T030, T002–T003
- **Declarations:** `PeriodPair.weierstrassCurve`, its short-normal-form and elliptic instances,
  `weierstrassCurve_c₄`, `weierstrassCurve_c₆`, `weierstrassCurve_Δ`,
  `weierstrassCurve_j`, `UpperHalfPlane.ellipticCurve`, `ellipticCurve_j`.
- **Source:** Report Proposition 6.12 and Definition 6.13, PDF pp. 39–40 / printed pp. 36–37.
- **Validation:** exact normalization checks (`12`, `216`, no missing `1728`), focused build,
  and public axiom audit.
- **Progress:** the short model `Y² = X³ - (g₂/4)X - g₃/4` now computes to
  `c₄ = 12g₂`, `c₆ = 216g₃`, and the period discriminant.  Its Mathlib invariant is
  `PeriodPair.j`; composition with `j_eq_periodPair_j` gives analytic `j`.  Focused compilation
  succeeds and the endpoint axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

### [T032] Factor primitive determinant matrices through Cox representatives

- **Status:** done (finished 2026-07-17T00:00:20Z)
- **File:** `XYin/PhD/Cox/CoxMatrices/Basic.lean`
- **Depends on:** T006–T008, T013–T014
- **Declaration:** a public HNF factorization for any integer `2×2` matrix of positive
  determinant and rank-two content one, producing `γ : SL(2,ℤ)` and `σ : CoxMatrix N`.
- **Source:** Report Lemma 5.8, PDF pp. 33–34 / printed pp. 30–31.
- **Validation:** determinant/content hypotheses are both necessary; test a non-upper-triangular
  primitive matrix and confirm action orientation.
- **Progress:** applied column HNF to `matrixStar M`, transported primitivity under the right
  `SL₂(ℤ)` action, constructed the Cox matrix from the positive HNF entries, and applied
  `matrixStar` again to obtain the required left action.  Focused compilation and the direct
  `sorry` scan pass.

### [T033] Construct a nonsquare fixed matrix for a primitive quadratic point

- **Status:** done (finished 2026-07-17T00:16:32Z)
- **File:** `XYin/PhD/Cox/SingularModuli.lean`
- **Depends on:** T032
- **Declarations:** primitive quadratic-equation data, imaginary-quadratic/singular-modulus
  predicates, `fixingMatrix`, determinant/fixed-point/primitivity lemmas, and existence of a
  positive nonsquare level with a Cox transform having equal `j`.
- **Source:** Report equations (5.5)–(5.10), PDF pp. 34–36 / printed pp. 31–33.
- **Proof route:** explicit parity choice for `2n+B`, documented in `plan.md`.
- **Validation:** examples `τ=i` and a nontrivial odd-`B` equation; `N` is positive and genuinely
  nonsquare, not merely `N≠0`.
- **Progress:** the even/odd discriminant split now gives determinants `k²+k` and `k²+2k`,
  each strictly between consecutive squares, and matrix content one follows from the primitive
  gcd hypothesis.
- **Progress:** entrywise expansion of the HNF factorization identifies the Cox action with an
  `SL₂(ℤ)` translate of the quadratic fixed point; modular invariance then gives equal `j`.
  The complete file compiles with no direct `sorry`.

### [T034] Prove singular moduli are algebraic integers

- **Status:** done (finished 2026-07-17T00:16:32Z)
- **File:** `XYin/PhD/Cox/SingularModuli.lean`
- **Depends on:** T033, T019–T020, T025–T026
- **Declarations:** diagonal-root lemma, `isIntegral_j_of_isImaginaryQuadratic`, and
  `singularModulus_isIntegral`.
- **Source:** Report Theorem 5.9, PDF p. 36 / printed p. 33.
- **Proof sketch:** product factor zero → integral diagonal root → leading coefficient `±1` →
  choose the polynomial or its negation as the monic witness.
- **Validation:** inspect the explicit monic witness in both leading-coefficient branches and
  audit `IsIntegral ℤ` uses the intended `ℤ → ℂ` algebra map.
- **Progress:** the Cox product formula supplies a zero factor in `Φ_N(j(τ),j(τ))`.  If the
  integral diagonal polynomial has leading coefficient `1` it is used directly; if it has
  leading coefficient `-1`, its negation is the explicit monic witness.  Focused compilation
  and the direct `sorry` scan pass.

### [T035] Bundle meromorphic-function representatives in the ambient function field

- **Status:** done (finished 2026-07-17T00:00:20Z)
- **File:** `XYin/PhD/Cox/ModularFunctionField.lean`
- **Depends on:** T018, `UpperHalfPlaneFunctionField.lean`
- **Declarations:** representation predicate and uniqueness, bundled `levelJ`, bivariate
  evaluation, modular representative set, `gamma0ModularFunctionField`, and
  `jLevelFunctionField`.
- **Source:** Cox printed pp. 230–231 / full-PDF pp. 242–243.
- **Guard:** raw `ℍ → ℂ` is not a domain; a fixed field under `Γ₀(N)` is too large because it
  admits functions with essential cusp singularities.
- **Validation:** zero-denominator and CM collision attacks; representations are nonvacuous and
  unique as ambient fraction-field elements.
- **Progress:** bundled `levelJ`, bivariate evaluation, guarded fraction representatives, and
  both intermediate fields.  Representation uniqueness is proved by cross multiplication in
  the domain of holomorphic functions; focused compilation passes with no direct `sorry`.

### [T036] Upgrade Theorem 11.9(ii) to an intermediate-field equality

- **Status:** done (finished 2026-07-17T00:00:20Z)
- **Files:** `XYin/PhD/Cox/ModularPolynomial/Interpolation.lean`,
  `XYin/PhD/Cox/ModularFunctionField.lean`
- **Depends on:** T035
- **Declarations:** rename old endpoint to `theorem_11_9_ii_pointwise`; new
  `theorem_11_9_ii (N) : gamma0ModularFunctionField N = jLevelFunctionField N`.
- **Source:** Cox Theorem 11.9(ii), printed p. 226 and proof printed pp. 230–231 / full-PDF
  pp. 238, 242–243.
- **Validation:** both field inclusions checked independently; RHS contains exactly the existing
  base `ℂ(j)` plus `j_N`; level `1` regression.
- **Progress:** preserved the prior theorem as `theorem_11_9_ii_pointwise` and proved both
  inclusions between `gamma0ModularFunctionField N` and `jLevelFunctionField N` using the
  pointwise rational expression and modularity of `levelJ`.  Focused compilation passes.

### [T037] Cleanup and final quality/axiom audit

- **Status:** done (started 2026-07-17T00:16:32Z; finished 2026-07-17T00:31:23Z)
- **Files:** all files touched by T031–T036, `Section11BC.lean`, `XYin.lean`
- **Depends on:** T031–T036
- **Work:** mandatory cleanup, source/docstring review, focused and full builds, direct-sorry
  scan, and public endpoint axiom audit.
- **Validation:** no new `sorryAx`, no direct sorry in Cox, no import cycle, and final ticket-board
  rescan has no open ticket with met dependencies.
- **Progress:** whole-file cleanup preserved every public theorem statement, target linting found
  no new-file issues, and an independent review found no mathematical or API semantic gap in the
  three `j` normalizations, fraction-field representation layer, or either field inclusion.
- **Progress:** strict focused compilation, two concrete CM regressions, nine-endpoint axiom
  audit, source scans, and `git diff --check` pass.  Final `lake build` succeeds for all 3909 jobs;
  the detailed record is `cleanup-t037.md`.

## Takeover completion

All tickets T030–T037 are done.  The three requested endpoints are implemented, independently
reviewed, axiom-clean modulo the standard axioms, regression-tested, and included in the project
umbrella.  There is no open ticket with met dependencies.
