# Ticket board: Cox §11.B–C

## Summary

- Planning baseline: complete.
- Proof tickets: 29 open.
- Execution status: **not started; awaiting user approval**.
- Hardest leaves: T006–T008 (HNF), T011 (meromorphic pole orbits), T016 (analytic/formal
  q-expansion), T019–T021 (Galois/Hasse/irreducibility), T027 (Kronecker).
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

- **Status:** open
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

### [T002] Repair the analytic/lattice invariant bridge

- **Status:** open
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

### [T003] Prove discriminant nonvanishing and lattice `j` classification

- **Status:** open
- **File:** `LatticeJ.lean`
- **Depends on:** T001, T002, existing `XYin/uniqueness.lean`
- **Declarations:** `discriminant_ne_zero`, `j_eq_of_homothetic`, `homothetic_of_j_eq`,
  `j_eq_iff_homothetic`, `exists_homothetic_periodPair`.
- **Source:** Proposition 10.7 and Theorem 10.9, printed pp. 206–208 / PDF pp. 218–220.
- **Proof sketch:** normalize any period pair to `[1,τ]` for nonvanishing; for classification,
  split `g₂=0`, `g₃=0`, and the generic case, choose fourth/sixth roots in `ℂ`, then apply
  `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq`.
- **Validation:** explicit tests cover `j=0` and `j=1728`; axiom audit excludes `sorryAx`.

### [T004] Port homothety iff `SL₂(ℤ)` orbit

- **Status:** open
- **File:** `LatticeJ.lean`
- **Depends on:** T001
- **Declaration:** `periodPair_homothetic_iff_exists_sl2_smul_eq`.
- **Source:** Cox equation (7.8), printed p. 138 / PDF p. 150.
- **Proof sketch:** port the existing axiom-clean theorem from `main`; read integral basis-change
  matrices in both directions, prove determinant `±1`, exclude `-1` by imaginary-part
  positivity, and construct the reverse scaling from the modular denominator.
- **Validation:** test the `S` and `T` generators and action direction; axiom audit.

### [T005] Finish analytic `j` injectivity and surjectivity

- **Status:** open
- **File:** `LatticeJ.lean`
- **Depends on:** T002, T003, T004
- **Declarations:** `j_eq_iff_exists_sl2_smul_eq`, `j_surjective`.
- **Source:** Theorem 11.2(ii)–(iii), printed p. 221 / PDF p. 233.
- **Proof sketch:** injectivity is a three-line composition of the requested bridge,
  homothety classification, and T004.  Adapt the existing surjectivity proof to the current `j`,
  using its pole at infinity and fundamental-domain topology.
- **Validation:** axiom audit; test that every chosen preimage lies in `ℍ`; no duplicate global
  definition of `j`.

## Phase 2 — Hermite normal form

### [T006] Prove HNF coordinate API and rank-two existence

- **Status:** open
- **File:** `HermiteNormalForm.lean`
- **Depends on:** T000
- **Declarations:** `HermiteNormalForm.repr_apply`, `Submodule.exists_hermiteNormalForm`.
- **Source:** Exercise 11.17, printed p. 247 / PDF p. 259.
- **Proof sketch:** first prove the `Fin 2` case: choose the least positive first coordinate in
  the full-rank submodule, choose a second basis vector, make both pivots positive, and use
  Euclidean division to reduce the upper entry.  If the induction is clean, generalize to `Fin n`;
  otherwise specialize the public existence theorem compatibly and postpone arbitrary rank.
- **Validation:** examples for `⊤`, diagonal submodules, and a matrix requiring reduction.

### [T007] Prove HNF uniqueness and determinant/index

- **Status:** open
- **File:** `HermiteNormalForm.lean`
- **Depends on:** T006
- **Declarations:** `HermiteNormalForm.matrix_eq`, `bN_eq`, `index_eq_natAbs_det`.
- **Source:** Exercises 7.15 and 11.17.
- **Proof sketch:** compare least positive pivots, then reduced residues; derive basis equality
  from equal coordinate columns.  Apply `Submodule.natAbs_det_basis_change` or the corresponding
  `AddSubgroup.index_eq_natAbs_det` theorem for the index.
- **Validation:** two independently constructed HNFs of the same test submodule have identical
  matrices; audit no quotient-cardinality finiteness assumption is smuggled in.

### [T008] Prove primitive matrix iff cyclic quotient

- **Status:** open
- **File:** `HermiteNormalForm.lean`
- **Depends on:** T006, T007
- **Declaration:** `quotient_isAddCyclic_iff_rankTwoContent_eq_one`.
- **Source:** equation (11.25) and Exercise 11.16, printed pp. 235,247 / PDF pp. 247,259.
- **Proof sketch:** use Bézout coefficients of the four entries to construct a generator of the
  quotient when the content is one.  Conversely, a common divisor gives a quotient surjection
  onto `(ZMod d)²`, which is noncyclic for `d>1`.
- **Do not assume:** mathlib's `SmithNormalForm` coefficients are invariant-factor normalized.
- **Validation:** matrices `diag(2,2)` (noncyclic) and `diag(1,m)` (cyclic).

## Phase 3 — modular functions and Theorem 11.9(i)

### [T009] Establish the modular-function base API

- **Status:** open
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

### [T010] Prove Cox Lemma 11.10

- **Status:** open
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

### [T011] Prove finite pole orbits and pole clearing

- **Status:** open
- **File:** `ModularFunction.lean`
- **Depends on:** T009, T010
- **Declaration:** `levelOne_exists_polynomial_clearing_poles`.
- **Source:** printed pp. 227–228 / PDF pp. 239–240; Exercise 11.7.
- **Proof sketch:** use a meromorphic divisor/locally finite pole support on a compact truncated
  fundamental region.  For each orbit, clear an ordinary pole by `j-j(τ₀)`; at `i` prove even
  order, and at the order-three elliptic point prove divisibility by three.
- **Validation:** explicit local stabilizer equations; `P ≠ 0`; no assumption that `j'` is
  nonzero at elliptic points.

### [T012] Assemble Theorem 11.9(i)

- **Status:** open
- **File:** `ModularFunction.lean`
- **Depends on:** T010, T011
- **Declaration:** `theorem_11_9_i`.
- **Source:** Theorem 11.9(i), printed p. 226 / PDF p. 238.
- **Proof sketch:** apply Lemma 11.10(ii) to `P(j)f`, then divide by nonzero `P(j)` using the
  guarded `RationalIn` predicate.
- **Validation:** rational functions with denominators vanishing at ordinary and elliptic values.

## Phase 4 — Cox representatives and q-expansions

### [T013] Finish `CoxMatrix` elementary and HNF links

- **Status:** open
- **File:** `CoxMatrices.lean`
- **Depends on:** T006, T008
- **Declarations:** positivity/bounds, `toFin_injective`, inclusion-HNF/determinant/content
  theorems, `sigmaZero`, `j_act_sigmaZero`.
- **Source:** definition of `C(m)`, printed p. 228 / PDF p. 240.
- **Proof sketch:** arithmetic with `ad=m`; unfold matrix notation; use T008 for the semantic
  primitive interpretation.
- **Validation:** enumerate `C(1)`, `C(2)`, `C(3)` and check `sigmaZero`.

### [T014] Prove Lemma 11.11 (right-coset equivalence)

- **Status:** open
- **File:** `CoxMatrices.lean`
- **Depends on:** T007, T013, T009
- **Declarations:** `coxMatrixEquivRightCosets`, `rightCosetEval`, `rightCosetTranslate`,
  `rightCosetEval_equiv`, `rightCosetTranslate_sigmaZero`.
- **Source:** Lemma 11.11 and Exercise 11.8, printed pp. 228,245 / PDF pp. 240,257.
- **Proof sketch:** associate to a right coset the unique primitive determinant-`m` HNF matrix;
  prove independence and inverse laws.  Define quotient lifts using `Γ₀(m)` invariance.
- **Validation:** explicit right/left orientation test; bijection cardinal check for levels 2,3.

### [T015] Prove the `C(m)` cardinal formula

- **Status:** open
- **File:** `CoxMatrices.lean`
- **Depends on:** T013
- **Declaration:** `card_coxMatrix`.
- **Source:** Exercise 11.9, printed pp. 245–246 / PDF pp. 257–258.
- **Proof sketch:** count `b` for each divisor `d`, prove multiplicativity, evaluate prime powers,
  and rewrite as the Euler product.
- **Validation:** native/norm-num checks for `m≤20` against direct `Fintype.card`.

### [T016] Prove exact transformed-root Laurent expansion and Galois reindexing

- **Status:** open
- **File:** `CoxMatrices.lean`
- **Depends on:** T002, T013, T014
- **Declarations:** `zeta_isPrimitiveRoot`, `jIntCoeff_spec`, `jIntCoeff_neg_one`,
  `laurentqExpansion_coxAction`, `reindex`, `reindex_bijective`.
- **Source:** equations (11.12), (11.13), printed p. 229 / PDF p. 241.
- **Proof sketch:** prove the width-`m` cusp identity under `τ↦(aτ+b)/d`; substitute the
  integral Laurent expansion of `j`; establish coefficient equality and support.  For reindexing,
  use a modular inverse of `k` modulo every `d|m`.
- **Validation:** coefficient `-a²` equals `ζ^(-ab)`; zero below `-a²`; compare `m=2` roots.

## Phase 5 — modular equation and Theorem 11.9(ii)

### [T017] Construct the complex modular polynomial

- **Status:** open
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

### [T018] Prove interpolation and Theorem 11.9(ii)

- **Status:** open
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

## Phase 6 — Theorem 11.18(i),(ii)

### [T019] Galois descent to integer Laurent coefficients

- **Status:** open
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

### [T020] Prove Hasse q-expansion principle and integer descent

- **Status:** open
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

### [T021] Prove irreducibility in `ℂ(Y)[X]`

- **Status:** open
- **File:** `ModularPolynomial.lean`, `Arithmetic.lean`
- **Depends on:** T014, T016, T017
- **Declarations:** `modularPolynomialC_irreducibleInX`, `theorem_11_18_ii`.
- **Source:** Exercise 11.10, printed p. 246 / PDF p. 258.
- **Proof sketch:** define the function field `ℂ(j,j_m)` and its embeddings by precomposition
  with coset representatives.  T016 proves the conjugates are distinct, giving at least
  `|C(m)|` embeddings; the root polynomial gives the opposite degree bound, hence it is minimal.
  Transport to the formal coefficient field `ℂ(Y)` via evaluation/transcendence.
- **Validation:** variable direction outer `X`; degree matches T017; no use of symmetry.

## Phase 7 — cyclic sublattices and Theorem 11.23

### [T022] Construct canonical period pairs and scaling/dual operations

- **Status:** open
- **File:** `CyclicSublattice.lean`
- **Depends on:** T003, T006–T008
- **Declarations:** `toPeriodPair`, `toPeriodPair_lattice`, `hermiteNormalForm`, `scale`,
  `j_scale`, `dual`, `dual_sub_j`, `dual_base_j`.
- **Source:** definition before Theorem 11.23 and the dual-inclusion argument used for symmetry.
- **Proof sketch:** obtain a rank-two HNF basis, map it into `ℂ`, and prove real linear
  independence from finite index.  Transport carriers through `PeriodPair.smulLatticeEquiv`.
  In HNF coordinates, show `mL⊂L'` and compute both quotients.
- **Validation:** constructions depend only on carrier; scale by two different units; dual of a
  diagonal cyclic inclusion.

### [T023] Prove Lemma 11.24 by HNF

- **Status:** open
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

### [T024] Prove Theorem 11.23

- **Status:** open
- **File:** `CyclicSublattice.lean`
- **Depends on:** T005, T017, T022, T023
- **Declarations:** `modularPolynomialC_zero_iff_normalizedCyclicSublattice`, `theorem_11_23`.
- **Source:** Theorem 11.23 and Exercise 11.18, printed pp. 235–236,248 /
  PDF pp. 247–248,260.
- **Proof sketch:** normalized result is exactly the product roots plus Lemma 11.24 and `j_smul`.
  Globally, use `j_surjective` forward; normalize/scale both lattices reverse.
- **Validation:** no import of `Arithmetic.lean`; semantic `(u,v)` order checked; both directions
  preserve index and cyclicity.

## Phase 8 — Theorem 11.18(iii)–(v)

### [T025] Prove symmetry from Theorem 11.23

- **Status:** open
- **File:** `Arithmetic.lean`
- **Depends on:** T020, T021, T022, T024
- **Declarations:** `modularPolynomial_dvd_swap`, `theorem_11_18_iii`.
- **Source:** 11.18(iii), printed p. 231 / PDF p. 243; internal replacement for Lang.
- **Proof sketch:** T022 duality makes the zero locus symmetric.  T021 yields divisibility;
  swapping twice makes the quotient a unit.  Reduce units of `ℤ[Y][X]` to `±1`; eliminate `-1`
  using diagonal invariance and degree `>1`/irreducibility.
- **Validation:** `m=1` excluded; test `m=2`; check dependency graph is non-circular.

### [T026] Prove the diagonal theorem

- **Status:** open
- **File:** `Arithmetic.lean`
- **Depends on:** T016, T020
- **Declarations:** `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`,
  `theorem_11_18_iv_degree`, `theorem_11_18_iv_leadingCoeff`.
- **Source:** equation (11.19) and 11.18(iv), printed p. 233 / PDF p. 245.
- **Proof sketch:** compare Laurent orders `-m` and `-a²`; nonsquare prevents equality.  Use
  leading-coefficient multiplicativity for finite products.  The resulting integer root of unity
  is `±1`.  Use `sigmaZero` to prove degree `>1` independently.
- **Validation:** nonsquare levels 2,3,5; a square-level regression demonstrates why the
  hypothesis is needed.

### [T027] Prove Kronecker's congruence

- **Status:** open
- **File:** `Arithmetic.lean`
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

### [T028] Verify the explicit `Φ₃` formula

- **Status:** open
- **File:** `Arithmetic.lean`
- **Depends on:** T017, T020, optionally T027
- **Declaration:** `modularPolynomial_three`.
- **Source:** equation (11.22), printed p. 234 / PDF p. 246.
- **Proof sketch:** preferred: prove the explicit polynomial is monic and has the same
  specialization/product as the canonical one, then use uniqueness.  Alternative: certified
  finite q-expansion comparison once a degree/height bound is established.
- **Validation:** final integer `22973`; symmetry; Kronecker mod 3; distinguished-root check.

## Phase 9 — cleanup and final audit

### [T029] Cleanup, documentation, and axiom audit

- **Status:** open
- **Files:** all `XYin/PhD/Cox/*.lean`, `XYin.lean`
- **Depends on:** T001–T028
- **Work:** run `/cleanup` and `/cleanup-all`; narrow imports; resolve linters; add tests and source
  docstrings; run full build and public-theorem axiom audit; confirm no dependency on deleted
  `Test` modules.
- **Validation:** zero `sorry` under `XYin/PhD/Cox/`; zero new `sorryAx`; full `lake build`;
  source/statement recheck against `.mathlib-quality/decomposition.md`.

## Milestones

| Milestone | Tickets | Result |
|---|---|---|
| M1 | T001–T008 | axiom-clean lattice `j` and HNF |
| M2 | T009–T018, T021 | complete Theorem 11.9 and complex modular equation |
| M3 | T019–T024 | 11.18(i),(ii), Lemma 11.24, Theorem 11.23 |
| M4 | T025–T029 | 11.18(iii)–(v), `Φ₃`, final quality gate |

## Approval

All proof tickets remain open pending user approval of this board and
`plan-cox11bc.md`.
