# Development plan: Cox §11.B–C

## Mode and boundary

- Workflow: `mathlib-quality:develop`.
- Current phase: statement design, decomposition, and tickets only.
- Proof execution begins only after user approval.
- Existing user work is preserved.  The deleted experimental `XYin/PhD/Test/` tree will not be
  restored wholesale.

## Goal

Produce an axiom-clean Lean formalization of all mathematical results needed for Cox §11.B–C,
including:

1. the lattice/analytic `j` bridge and `SL₂(ℤ)` orbit classification requested by the user;
2. a reusable fixed-basis column Hermite normal form API over `ℤ`;
3. Lemma 11.10 and Theorem 11.9;
4. Lemma 11.11 and equations (11.12)–(11.17);
5. Theorem 11.18(i)–(v) and the explicit `Φ₃` formula (11.22);
6. Lemma 11.24 and Theorem 11.23.

Completion means:

- no `sorry` in `XYin/PhD/Cox/`;
- no new `sorryAx` in the transitive axiom audit of any public target;
- `lake build` succeeds;
- declarations use stable, non-`Test` namespaces and the outer variable convention documented in
  `ModularPolynomial.lean`;
- the implementation is covered by focused tests/examples for HNF, `m=1`, `m=2`, `m=3`, and
  prime reduction.

## API architecture

```text
XYin/uniqueness.lean
        │
        ▼
LatticeJ.lean ───────────────────────────────────────────┐
        │                                                │
        ▼                                                │
ModularFunction.lean                                    │
        │                                                │
HermiteNormalForm.lean                                  │
        │                                                │
        ▼                                                │
CoxMatrices.lean                                        │
        │                                                │
        ▼                                                │
ModularPolynomial.lean                                  │
        │                                                │
        ▼                                                │
CyclicSublattice.lean ◄──────────────────────────────────┘
        │
        ▼
Arithmetic.lean
        │
        ▼
Section11BC.lean
```

The layering is intentional:

- Theorem 11.23 is proved in `CyclicSublattice.lean` from the complex root product and does not
  import arithmetic symmetry.
- `Arithmetic.lean` may then derive symmetry from Theorem 11.23 without a dependency cycle.
- HNF is independent of complex analysis and can later be proposed for mathlib on its own.

## Generality decisions

### Positive levels

All levels use `m : ℕ+`.  This removes repeated `m≠0` obligations and matches the actual source
hypothesis “positive integer.”  Bridges to existing `jN (N : ℕ) [NeZero N]` are isolated in
`Cox.levelJ`.

### Hermite normal form

The base ring is `ℤ`, but the ambient additive group is arbitrary with a finite integer basis.
This is the reusable generality supported by the source and mathlib's quotient/index API.

The ambient basis is a parameter:

```lean
Module.Basis.HermiteNormalForm (bM : Basis (Fin n) ℤ M) (N : Submodule ℤ M)
```

This differs deliberately from Smith normal form.  Smith normal form may change both bases;
Hermite normal form is canonical only relative to a fixed ambient basis.

### Modular functions

`IsGamma0ModularFunction` is a predicate rather than a bundled ring element.  It records:

- meromorphicity on the upper half-plane;
- exact weight-zero invariance under `Γ₀(N)`;
- meromorphicity at every cusp after `SL₂(ℤ)` precomposition.

Closure lemmas can later support a bundle if needed, but a predicate minimizes migration and is
sufficient for Cox.

### Meromorphic equality

`RationalIn` and `RationalInTwo` state pointwise equality away from denominator zeros.  This
avoids false equalities at poles or specialized multiple roots and remains easy to consume.

### Bivariate variables

For `BivariatePolynomial R = Polynomial (Polynomial R)`:

- outer variable = Cox's root variable `X`;
- inner coefficient variable = Cox's parameter variable `Y`;
- semantic evaluation is `Φ.eval x y = Φ.evalEval y x`.

Consequently, Theorem 11.18(ii) is literally irreducibility of an outer polynomial over
`ℂ(Y)`.

## Implementation phases

### Phase 0 — stabilize the baseline

1. Keep the already-applied removal of stale imports from `XYin.lean`; those modules were deleted
   in the current branch and prevented any full build.
2. Keep the umbrella `XYin.PhD.Cox.Section11BC` import.
3. Record the pre-existing project warnings/sorries separately from this development.
4. Add focused build targets so later tickets do not require a full 3,800-job rebuild.

Exit criterion: `lake build` succeeds before any proof ticket changes semantics.

### Phase 1 — lattice invariants and analytic `j`

1. Port the axiom-clean scaling API from `main:XYin/Workshop/L_L_bar_real.lean` into
   `LatticeJ.lean`.
2. Prove the normalized Eisenstein comparisons using
   `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`, `riemannZeta_four`, and the even-zeta
   formula for six.
3. Replace the historical `Delta_E4_eqn` route by a direct pointwise equality with mathlib's
   modular discriminant and its sorry-free cubic theorem.
4. Port the special-case-safe proof that equal lattice `j` values imply homothety, ending with
   `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq`.
5. Port the existing axiom-clean normalized-lattice/change-of-basis theorem.
6. Adapt the existing surjectivity proof to the current global `j` and audit it.

Exit criterion: `j_eq_periodPair_j`, `j_eq_iff_exists_sl2_smul_eq`, and `j_surjective` have no
`sorryAx`.

### Phase 2 — Hermite normal form

1. Prove projection lemmas from `LinearMap.toMatrix`.
2. Implement rank-two HNF existence constructively using Euclidean division and unimodular
   column operations; only then decide whether the same proof naturally extends to all `Fin n`.
3. Prove uniqueness relative to `bM` by comparing least positive pivots and reduced residues.
4. Prove index equals absolute determinant through mathlib's basis-change determinant API.
5. Prove the rank-two cyclic quotient criterion by a Bézout map to `ZMod (det.natAbs)` or by an
   explicit equivalence, not by assuming mathlib's unnormalized SNF has invariant factors.

Risk control: if arbitrary-rank existence would delay the Cox path, first specialize the theorem
to `Fin 2`, use it in Cox, and leave a compatible general declaration for a later mathlib PR.

Exit criterion: HNF file has no sorries and includes examples for diagonal, nonprimitive, and
reduced/nonreduced matrices.

### Phase 3 — modular functions and Theorem 11.9(i)

1. Establish closure/invariance/cusp transport lemmas for `IsGamma0ModularFunction`.
2. Prove `j` and `levelJ` are the claimed modular functions using existing project facts.
3. Prove Lemma 11.10(i) with the mathlib fundamental domain and maximum modulus.
4. Prove Lemma 11.10(ii) by principal-part subtraction.
5. Build a finite-pole-orbit lemma from meromorphic divisors on compact truncated domains.
6. Clear ordinary poles and separately prove stabilizer divisibility at `i` and
   `exp(2πi/3)`.
7. Assemble Theorem 11.9(i).

Exit criterion: every level-one modular function satisfies `RationalIn f j`.

### Phase 4 — Cox representatives, right cosets, and (11.13)

1. Finish the elementary finite API for `CoxMatrix`.
2. Relate its inclusion matrix to the HNF API.
3. Prove Lemma 11.11 as an explicit equivalence with right cosets; test left/right orientation on
   generators `S` and `T`.
4. Prove the cardinal formula multiplicatively, with the prime-power count
   `p^r+p^(r-1)`.
5. Define representative-independent right-coset translates.
6. Prove (11.12).
7. Prove exact equation (11.13) as equality of width-`m` Laurent series.
8. Prove Galois reindexing and its bijectivity.

Exit criterion: transformed analytic roots, formal Laurent series, right cosets, and HNF
representatives are all connected by proved equivalences/equalities.

### Phase 5 — modular equation and Theorem 11.9(ii)

1. Form the right-coset/Cox product and prove coefficient invariance and cusp meromorphicity.
2. Apply Lemma 11.10 to construct the unique monic `modularPolynomialC`.
3. Prove both (11.14) and (11.15), the distinguished root, and the degree formula.
4. Implement `interpolationAt`, prove Exercise 11.11 for its coefficients, and apply Theorem
   11.9(i).
5. Prove the guarded recovery formula (11.17) and package it as `RationalInTwo`.

Exit criterion: Theorem 11.9(ii) is complete independently of integral descent.

### Phase 6 — Theorem 11.18(i) and (ii)

1. Prove the Galois permutation theorem over a cyclotomic Laurent-series field and transport it
   through the analytic/formal bridge.
2. Show symmetric coefficients have integral width-one Laurent expansions.
3. Add the Laurent-series algebra lemmas needed for Hasse's leading-term induction.
4. Prove integer descent and uniqueness of the chosen `modularPolynomial`.
5. Formalize Exercise 11.10 using the function field `ℂ(j,j_m)`, distinct base-field embeddings,
   and the degree count; state the result over `ℂ(Y)[X]` first.

Exit criterion: `theorem_11_18_i` and `theorem_11_18_ii` are axiom-clean.

### Phase 7 — cyclic sublattices and Theorem 11.23

1. Construct `CyclicSublattice.toPeriodPair` from its HNF basis and prove its lattice equation.
2. Transport cyclic sublattices under scaling.
3. Prove Lemma 11.24 as `cyclicSublatticeEquivCoxMatrix`, including its HNF matrix formula.
4. Prove the normalized root classification from (11.15).
5. Use `j_surjective` for the forward global direction and lattice normalization/scaling for the
   reverse direction.
6. Construct the dual cyclic inclusion `mL⊂L'` for symmetry.

Exit criterion: `theorem_11_23` and the dual-j lemmas are complete without importing
`Arithmetic.lean`.

### Phase 8 — Theorem 11.18(iii)–(v) and (11.22)

1. Use Theorem 11.23 plus dual inclusions to prove `Φ ∣ swap Φ`; use irreducibility and
   normalization for equality.
2. Formalize Laurent-series order/leading-coefficient multiplicativity and prove (11.19)'s
   root-of-unity conclusion; derive both parts of (iv).
3. Enumerate `C(p)`, establish (11.20)–(11.21), prove the cyclotomic norm/divisibility leaf, and
   build `specializeJMod_injective` for Exercise 11.15.
4. Derive Kronecker's congruence for every prime, with an explicit `p=2` branch if required by the
   cyclotomic API.
5. Prove the explicit `Φ₃` identity by uniqueness/root comparison or certified q-expansion
   computation.

Exit criterion: all five parts of Theorem 11.18 and (11.22) are complete.

### Phase 9 — quality and axiom audit

1. Run `/cleanup` file by file, then `/cleanup-all` on the module family.
2. Replace broad imports with the narrowest stable imports.
3. Run linters and add docstrings/source locators.
4. Run `lake build` and `#print axioms`/the project's axiom-audit mechanism for every public
   theorem.
5. Confirm no declaration in `XYin/PhD/Cox/` depends on deleted `Test` modules.

## Dependency DAG

```text
P1 lattice j ───────────────┬───────────────┐
                            │               │
P2 HNF ───────► P4 reps/q ──┼──► P5 Φ/11.9ii ──► P6 int/irr
                            │               │          │
P3 11.9i ───────────────────┘               │          │
                                            ▼          │
                                      P7 11.23 ◄───────┘
                                            │
                                            ▼
                                      P8 symmetry/iv/v
                                            │
                                            ▼
                                         P9 audit
```

Parallel work after approval:

- Phase 1 and Phase 2 are independent.
- In Phase 3, fundamental-domain rigidity and local elliptic stabilizer lemmas can proceed in
  parallel.
- In Phase 4, cardinal arithmetic and analytic/formal q-expansion work are independent after the
  `CoxMatrix` base API.
- In Phase 8, diagonal analysis, Kronecker congruence, and the `Φ₃` computation can proceed in
  parallel after their common prerequisites.

## Validation strategy

Every ticket closes only after:

1. its focused module builds;
2. direct dependents build;
3. any public theorem receives an axiom audit;
4. the statement still matches the source locator in `decomposition.md`;
5. new helper APIs have at least one nontrivial use or test.

Milestones additionally require full `lake build`:

- M1: lattice `j` + HNF;
- M2: Theorem 11.9;
- M3: Theorem 11.18(i),(ii) + Theorem 11.23;
- M4: all §11.B–C targets and final cleanup.

## Approval gate

This plan is ready for review.  No proof ticket should be started until the user approves the
scope, API conventions, and ordering—especially the fixed-basis column HNF and the outer-`X`
bivariate convention.
