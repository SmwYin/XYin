# Cleanup record: T023

## Scope

- Target: Cox Lemma 11.24, classifying cyclic index-`m` sublattices by the canonical
  representatives `CoxMatrix m`.
- Supporting APIs: carrier extensionality, injectivity of the Cox inclusion matrix, and the
  column-range semantics of a bundled HNF.
- The classification implementation now lives in `CyclicSublattice/Classification.lean`; the
  reusable carrier, HNF-period, transport, scaling, and duality API remains in
  `CyclicSublattice.lean`.

## HNF extraction

- `CyclicSublattice.toCoxMatrix` reads the canonical HNF matrix as `!![d,b;0,a]`.
  Positive diagonal entries and the reduced upper entry give `0 < a`, `0 ≤ b < d`.
- All three natural-number fields use `Int.natAbs`, matching the determinant/index and matrix
  content APIs without introducing truncation through `Int.toNat`.
- The index formula gives `ad = m`; the arbitrary-basis primitive-matrix theorem from T022
  identifies cyclicity of the quotient with the gcd-one field of `CoxMatrix`.
- `toCoxMatrix_inclusionMatrix` is the simp-oriented matrix identity. Its reverse is retained as
  the semantic HNF theorem used by the public T023 statement.

## Converse construction and equivalence

- For any period pair `L`, `CoxMatrix.sublatticeOfPeriodPair` is the range of the endomorphism
  whose matrix in `L.latticeBasis` is `!![d,b;0,a]`.
- A private explicit HNF witness proves its index is `m` and its quotient is cyclic. HNF
  uniqueness proves that extracting the representative returns the original Cox matrix.
- Conversely, the generalized column-range theorem identifies the range of an extracted HNF
  matrix with the original carrier. `CyclicSublattice.ext` then proves the other round trip.
- The arbitrary-period-pair equivalence is exposed as
  `cyclicSublatticeEquivCoxMatrixOfPeriodPair`; the requested upper-half-plane API is its exact
  specialization to `UpperHalfPlane.periodPair τ`.

## Lattice identity

- The range carrier is proved equal to the span of the two inclusion-matrix columns. After
  embedding into `ℂ`, these columns are `d` and `b + aτ`.
- The periods of `d • UpperHalfPlane.periodPair (σ.act τ)` simplify to the same pair because
  `σ.act τ = (aτ+b)/d` and `d ≠ 0`.
- Therefore `coxMatrix_toPeriodPair_lattice` proves the exact identity
  `[d,aτ+b] = d[1,στ]` in the direction required by T024.

## Generalized HNF support

- `Module.Basis.HermiteNormalForm.range_toLin_matrix_eq` is stated for arbitrary `Fin n`, not
  just rank two: interpreting the HNF inclusion matrix in the ambient basis recovers its
  represented submodule exactly.
- `CoxMatrix.inclusionMatrix_injective` records that `(d,b,a)` determines a Cox representative,
  avoiding dependence on the bounded `toFin` implementation used only for finiteness.

## Validation and quality gates

- `/tmp/T023Audit.lean` checks both equivalence round trips, `m = 1`, the non-diagonal
  `m = 2` representative `(a,b,d) = (1,1,2)`, the public HNF theorem, and the explicit lattice
  identity under `-DwarningAsError=true`.
- All audited T023 declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`;
  none depends on `sorryAx`.
- `HermiteNormalForm.lean`, `CoxMatrices.lean`, and the split classification file pass direct
  warning-as-error builds; the classification file is now entirely sorry-free after T024.
- The post-split 3891-job full repository build, `git diff --check`, the 100-character gate,
  forbidden-code
  checks, public-signature checks, and independent mathematical/API reviews pass.
- Threshold-1000 ms profiling reports no slow declaration in any of the three touched files.

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
