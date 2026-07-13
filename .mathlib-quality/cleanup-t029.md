# Cleanup record: T029

## Scope

- Target: final cleanup, documentation, statement/source review, axiom audit, and full build for
  the Cox §11.B–C formalization.
- Source surface: every Lean file under `XYin/PhD/Cox/`, the umbrella import in `XYin.lean`, and
  the development metadata in `.mathlib-quality/`.
- Public endpoints audited include the lattice `j` bridge, HNF, Theorem 11.9, Lemma 11.11,
  Theorem 11.18(i)–(v), Lemma 11.24, Theorem 11.23, and equation (11.22).

## API and module cleanup

- `CoxMatrices.lean` remains a compatibility umbrella and now delegates to `Basic`,
  `Cardinality`, and `LaurentExpansion` modules.
- `ModularPolynomial.lean` remains a compatibility umbrella and now delegates to
  `AnalyticSupport`, `Construction`, `Interpolation`, `Irreducibility`, and `IntegralDescent`.
- The five analytic-support declarations exposed by the split have mathematical names and
  docstrings.  Every pre-existing public declaration keeps its full name and statement.
- All 25 Cox source files have a standard copyright header and module docstring.  Every
  implementation file is below 1000 lines; the two umbrella files are intentionally minimal.
- Temporary axiom-print markers and commands were removed.  No Cox source imports the deleted
  `XYin.PhD.Test` tree.

## Mathematical review

- `PeriodPair.discriminant` and `PeriodPair.j` use Cox's normalization, including the factor
  `1728`.
- The analytic injectivity route follows the requested three steps: analytic/lattice equality,
  lattice-`j` equality iff homothety, and normalized homothety iff an `SL₂(ℤ)` change of basis.
- `Module.Basis.HermiteNormalForm` fixes the ambient basis, bundles the submodule basis and full
  inclusion matrix, records column-HNF, and supplies rank-two existence and canonical
  matrix/basis uniqueness, parallel to mathlib's Smith-normal-form API.
- An independent declaration-by-declaration comparison against `decomposition.md` found every
  §11.B–C target present with the correct hypotheses, variable orientation, and conclusion.
  In particular, (11.22) contains the visually checked factor `22973`.
- The dependency graph remains non-circular: Theorem 11.23 precedes symmetry, and the level-three
  certificate consumes complex symmetry without importing `Arithmetic`.

## Validation and quality gates

- The 25 Cox files pass direct `-DwarningAsError=true` compilation in disjoint cleanup batches;
  the final `Section11BC.lean` umbrella strict compile also passes.
- The local style checker reports zero errors.  Its remaining findings are conservative
  bare-`simp` suggestions, not linter or build failures.
- Forbidden-code and scaffolding scans find no `sorry`, `admit`, `sorryAx`, `native_decide`,
  unsafe declaration, resource-limit override, debug command, temporary axiom command, TODO, or
  FIXME in the Cox subtree.
- `/tmp/T029Audit.lean` audits 45 representative public definitions and theorems.  Every one
  depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- Final profiling has no declaration above the one-second threshold.  One finite level-three
  table certificate showed a single 1.07-second boundary fluctuation; its two subsequent runs
  were 653 ms and below the reporting threshold.
- `git diff --check`, long-line, header, module-docstring, trailing-whitespace, and deleted-Test
  dependency scans pass for the scoped files.
- Final `lake build` succeeds for all 3906 jobs.  It replays pre-existing warnings and sorries in
  unrelated project modules, but the Cox subtree is clean.

## Phase checklist

- [x] Doctor
- [x] Prepare and recheck references
- [x] Style/API audit
- [x] File-level import and dependency-DAG audit
- [x] Per-declaration cleanup and generality audit
- [x] Mathematical-boundary file split
- [x] Public-name compatibility check
- [x] Final diagnostics and gates
- [x] Source-to-statement review
- [x] Public axiom audit
- [x] Full repository build
