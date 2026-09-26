## 2026-09-21 Cox migration to bundled modular functions

User-authorized scope: migrate Cox's modular-function and function-field proofs to the new
`ModularFunction` and codiscrete meromorphic field; remove redundant Cox implementations.

- Public Theorem 11.9 inputs use the new bundle. Auxiliary raw `CuspData` remains only for
  intermediate pole-clearing/interpolation expressions whose removable values are not normalized.
- Replace the holomorphic fraction field and `Represents` by actual `MeromorphicField` elements.
- Bundle `j(Nτ)` and the holomorphic Cox-product coefficients, reuse shared j and cusp APIs.
- Move general congruence and field-action infrastructure to `ModularFunctions`.
- Verify the Cox import graph, full project, key axioms, independent review, and profiling.

# Development plan: elliptic `j`, singular moduli, and the bundled function field

## 2026-09-20 extension: bundled modular functions

The user authorizes implementing `ModularFunction Γ` extending `SlashInvariantForm Γ 0`,
with membership in the codiscrete meromorphic field through its canonical representative,
and at most exponential growth at every cusp. The previous Cox implementation is preserved.
New files live in `XYin/PhD/ModularFunctions`. Source: the user-linked conversation
`6a673539-8210-83ee-8462-6c7adf3b4774` (growth uniform on high half-planes, equivalent
to meromorphy in a positive-period q-coordinate), and Stefan Kebekus's ProjectVD `VD/Field`
at commit `9c218722ad71e9bd2ba357892bc835c8c648aaa8` (Apache 2.0 attribution retained).

The proof follows the supplied argument: a meromorphic cusp function becomes bounded after
multiplication by a power of q; conversely choose an integer exceeding ρh/(2π), show the
regularized cusp function tends to zero, and apply removable singularities. Normal forms
are essential: bounded raw representatives may have isolated exceptional values accumulating
at the cusp. First prove local boundedness excludes poles for normal forms, then obtain
eventual holomorphy. The final modular definition has a period-free growth predicate;
periods are hypotheses of the comparison theorem and come from slash invariance.

Parallel ownership: MeromorphicField files (field worker), CuspGrowth (q-coordinate worker),
NormalFormGrowth (local regularity worker), Basic/GrowthAtCusp/JInvariant (root).
Acceptance: no new sorry or axioms, field instance and canonical representative verified,
growth/cusp equivalence and bundled j compiled, full build and focused axiom audit,
independent review plus cleanup of new files.

## Takeover boundary

This plan extends the completed Cox §11.B–C board (`T001`–`T029`).  It preserves the existing
outer-`X`, inner-`Y` convention for bivariate polynomials and reuses the already axiom-clean
lattice bridge, modular polynomial, diagonal leading-coefficient theorem, and interpolation
theorem.  The baseline at takeover is a clean `PhD_Experiment` worktree and a successful
3906-job `lake build`.

The requested implementation has three public outcomes:

1. the short Weierstrass curve attached to a period lattice has Mathlib `j` equal to
   `PeriodPair.j`, hence the normalized curve at `τ` has Mathlib `j` equal to analytic `j τ`;
2. every singular modulus, defined by a primitive negative-discriminant quadratic equation, is
   integral over `ℤ`;
3. Cox Theorem 11.9(ii) is exposed as an equality of bundled intermediate fields, not merely the
   pointwise predicate `RationalInTwo`.

## Chosen source route

For singular moduli we use Report Theorem 5.9 (PDF pp. 34–36 / printed pp. 31–33), rather than
the proper-ideal route in Cox printed pp. 235–237.  The report route depends only on infrastructure
already present in the repository: primitive rank-two matrix reduction, the Cox product formula,
integrality of `Φ_N`, and the diagonal leading coefficient `±1` for nonsquare `N`.

The report chooses a sufficiently large `n` for which

```text
N_n = n² + Bn + AC
```

is positive and nonsquare.  The Lean implementation uses the same matrix family but chooses `n`
explicitly after splitting the parity of `B`.  If `B=2b`, put `k=AC-b²` and `n=k-b`; negative
discriminant gives `k>0` and `N_n=k²+k`.  If `B=2b+1`, put `k=AC-b(b+1)` and again `n=k-b`;
then `k>0` and `N_n=k²+2k`.  In both cases `k²<N_n<(k+1)²`.  This replaces a finite-divisor-set
argument by elementary `omega`/`nlinarith` arithmetic without changing the source's fixed-point
or modular-polynomial argument.

## API architecture

```text
Cox/LatticeJ.lean
  └─ jFunction/jInvariantLink.lean
       PeriodPair.weierstrassCurve
       PeriodPair.weierstrassCurve_j
       UpperHalfPlane.ellipticCurve_j

Cox/HermiteNormalForm.lean
  └─ Cox/CoxMatrices/Basic.lean
       primitive determinant-N matrix → SL₂(ℤ) × CoxMatrix N
          └─ Cox/SingularModuli.lean
               PrimitiveQuadraticEquation
               IsImaginaryQuadratic / IsSingularModulus
               singularModulus_isIntegral

Cox/ModularPolynomial/Interpolation.lean
  theorem_11_9_ii_pointwise
     └─ Cox/ModularFunctionField.lean
          meromorphic-function representation in FunctionField
          gamma0ModularFunctionField N
          jLevelFunctionField N
          theorem_11_9_ii : gamma0ModularFunctionField N = jLevelFunctionField N
```

The bundled field lives inside
`UpperHalfPlaneFunctionField.FunctionField = FractionRing HolomorphicFunction`.  Raw function
space `ℍ → ℂ` is deliberately not used as a field because it has zero divisors.  The left-hand
side is generated by the unique ambient fraction-field elements representing
`Γ₀(N)`-modular functions.  The base field is the existing embedded `RatFunc ℂ = ℂ(j)`, and the
right-hand side adjoins the element represented by `levelJ N`.

## Ordered proof decomposition

### Elliptic/lattice/analytic `j`

1. Define the short model `Y² = X³ -(g₂/4)X-g₃/4`.
2. Compute `c₄=12g₂`, `c₆=216g₃`, and Mathlib discriminant `Δ=g₂³-27g₃²`.
3. Use `PeriodPair.discriminant_ne_zero` to synthesize `IsElliptic`.
4. Unfold Mathlib's `j = Δ⁻¹c₄³` and identify it with `PeriodPair.j`.
5. Compose with `j_eq_periodPair_j` for the normalized period pair `[1,τ]`.

### Singular moduli

1. Package a primitive quadratic equation and its negative discriminant.
2. Prove the explicit parity construction of a positive nonsquare determinant in the family
   `M_n = [[n,-C],[A,n+B]]`.
3. Prove `M_n` is primitive from `gcd(A,B,C)=1`.
4. Generalize the existing HNF reduction to factor any primitive determinant-`N` matrix through
   a unique Cox representative up to left multiplication by `SL₂(ℤ)`.
5. Prove the resulting Cox transform has the same analytic `j` at the quadratic fixed point.
6. Use the Cox product formula to make `j(τ)` a root of `Φ_N(X,X)`.
7. Use `theorem_11_18_iv_leadingCoeff`; choose the diagonal polynomial or its negation as a
   monic integral polynomial and conclude `IsIntegral ℤ (j τ)`.

### Bundled function field

1. Define when a raw meromorphic function is represented by a fraction of global holomorphic
   functions and prove representation uniqueness by analytic no-zero-divisors.
2. Bundle `levelJ` and bivariate evaluation in the ambient function field.
3. Rename the existing guarded result to `theorem_11_9_ii_pointwise`.
4. Define the intermediate field generated by representatives of all level-`N` modular
   functions and the field `ℂ(j)(j_N)`.
5. The easy inclusion uses modularity of `levelJ`; the hard inclusion applies the pointwise
   theorem, turns its guarded equality into equality of fraction-field elements, and closes by
   `IntermediateField.adjoin_induction`.

## Completion gates

- Every new declaration is free of `sorry`; no existing sorry outside this scope is counted as
  new work.
- Focused builds for all edited modules and a final `lake build` succeed.
- Public endpoints have only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- The Cox subtree remains free of direct `sorry`/`admit`; the `#check` placeholders in
  `jInvariantLink.lean` are removed.
- Mandatory cleanup reviews imports, namespace/API naming, proof length, and source docstrings.
