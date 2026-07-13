# Cleanup record: T016

## Baseline and scope

- Targets: `zeta_isPrimitiveRoot`, `jIntCoeff_spec`, `jIntCoeff_neg_one`,
  `laurentqExpansion_coxAction`, `reindex`, and `reindex_bijective` in
  `XYin/PhD/Cox/CoxMatrices.lean`.
- The implementation formalizes Cox equations (11.12)--(11.13), including the exact
  width-`m` local parameter and the Galois permutation of the HNF representatives.
- The focused Cox build and the 3883-job full-repository build both pass.

## Integral coefficient repair

- The old integral-q-expansion chain passed through native q-expansion computations.  The
  repaired `E4IsIntegralPowerSeries` and `E6IsIntegralPowerSeries` instead use mathlib's
  `EisensteinSeries.E_qExpansion_coeff` formula directly.
- `Deltaaux` now follows from mathlib's pointwise discriminant identity and the generic
  analytic `UpperHalfPlane.qExpansion_smul` theorem.  It no longer uses the contaminated
  project equations `Delta_E4_eqn` or `qExpansion_smul2`.
- Consequently `Delta/q`, its formal inverse `q/Delta`, `qj`, and
  `jLaurentqExpansion_isIntegral` are all standard-axiom clean.
- The constant coefficient theorem `qj_qExpansion_coeff_zero` is public and gives the clean
  proof `jIntCoeff (-1) = 1` without importing `qexp_coeffs.lean`.
- The upstream import was narrowed from `DimensionFormulas` to `Eisenstein`; the mathlib
  `LevelOne.GradedRing` import is explicit because it supplies the discriminant identity.

## Analytic/formal bridge

- For `eta = zeta m ^ (a*b)` and `t = qParam m tau`, the exact coordinate identity is
  `qParam 1 (sigma.act tau) = eta * t^(a^2)`.  This fixes both the phase direction and the
  required cusp width.
- Composition of meromorphic orders with `q |-> eta*q^(a^2)` proves that the transformed
  function has pole order `a^2`; no coefficient argument is used circularly.
- Removing that pole gives `eta^(-1) * qj(sigma.act tau)`.  Its power series is identified as
  `eta^(-1) • expand (a^2) (rescale eta (qExpansion 1 qj))`.
- The power-series identity is analytic, not merely formal: `hasSum_qExpansion_qj` is
  reindexed along the injection `n |-> a^2*n`, and
  `UpperHalfPlane.qExpansion_coeff_unique` identifies the coefficients at the cusp.
- Laurent coefficients are then proved by the three exhaustive cases `k < -a^2`,
  `a^2 ∤ k`, and `k = a^2*t`.  The boundary `t = -1` is handled explicitly before using
  `Int.toNat`; the phase simplifies to `zeta m ^ ((a*b)*t)`.

## Galois reindexing

- `reindex k hk` fixes `a,d` and sends `b` to `b*k mod d`.  Since `d | m`, coprimality of
  `k` and `m` gives coprimality of `k` and every such `d`, preserving the primitive HNF
  condition.
- Modular multiplication cancellation proves injectivity on each finite fiber; finiteness
  upgrades it to a bijection.  The definition is computable, so the obsolete
  `noncomputable` marker was removed.

## Validation

- `/tmp/T016AllAudit.lean` audits all six public targets.  Each depends only on `propext`,
  `Classical.choice`, and `Quot.sound`; none contains `sorryAx`.
- `/tmp/T016LaurentValidation.lean` proves the coefficient at `-a^2` is
  `zeta m ^ (-(a*b))`, proves all lower coefficients vanish, and enumerates the three
  representatives at level two.  Their leading phases are exactly `1, 1, -1`.
- The level-two enumeration, the two residue permutations at levels two and three, and all
  analytic corollaries are standard-axiom clean and use no `native_decide`.
- The target files compile silently, all new Cox lines are at most 100 characters, and
  `git diff --check` passes.  Independent reviews checked the cusp width, phase inversion,
  meromorphic-order composition, HasSum reindexing, Euclidean-division boundary, and HNF
  permutation.

## Buzz

- Outcome: FAST-BOARD.  Threshold-100 ms profiled compiles found no declaration above the
  1000 ms budget in `CoxMatrices.lean` or `Deltaqexpansions.lean`.  A borderline pre-existing
  `refine` in `jfunction.lean` measured 1.05 s once and 0.945 s on the required rerun, so it is
  below budget; the T016 declarations are well below it.
- No heartbeat override, profiler scaffold, native-decision axiom, or deferral remains.

## Phase checklist

- [x] Doctor
- [x] Prepare and read references
- [x] Style/API audit
- [x] File-level import audit
- [x] Per-declaration golf and generality audit
- [x] Non-rename refactoring
- [x] Rename pass
- [x] Final diagnostics and gates
- [x] Simplify pass
- [x] Buzz pass
- [x] Report
