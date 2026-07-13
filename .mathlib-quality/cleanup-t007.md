# Cleanup record: T007

## Baseline and scope

- Targets: `Module.Basis.HermiteNormalForm.matrix_eq`, `bN_eq`, and
  `index_eq_natAbs_det` in `XYin/PhD/Cox/HermiteNormalForm.lean`.
- Matrix and basis uniqueness are specialized to the rank-two API supplied by T006; the
  determinant/index theorem remains valid and implemented in arbitrary finite rank.
- Both focused and full-repository `lake build` pass.

## API and mathematical audit

- For two HNF bases of the same submodule, `Basis.toMatrix` gives transition matrices `U` and
  `V` with `A * U = A'` and `A' * V = A`.
- The lower-left HNF zeros force `U 1 0 = V 1 0 = 0`.  The two lower-right equations show the
  positive lower pivots divide each other, hence are equal; cancellation then gives `U 1 1 = 1`.
- The same mutual-divisibility argument fixes the positive upper-left pivots.  The upper-right
  equation says the two reduced entries differ by a multiple of that pivot, and uniqueness of
  Euclidean remainders in `[0,d)` makes them equal.
- Equal matrices give equal basis vectors coordinatewise through `repr_apply`; injectivity of the
  ambient basis representation then gives basis equality.
- The index proof is the direct `AddSubgroup.index_eq_natAbs_det` theorem followed by conversion
  from `Basis.toMatrix` to the bundle's recorded inclusion matrix.  It assumes no pre-existing
  quotient-finiteness instance.

## Cleanup and simplify

- Used explicit `simpa only` lists when extracting the four scalar transition equations, avoiding
  flexible simplification and making the row/column direction visible.
- Kept the matrix-transition and Euclidean-remainder facts private; no unnecessary public API was
  introduced.
- Removed transitive duplicate imports after adding the direct card-quotient theorem import.
- Documented explicitly that matrix/basis uniqueness is currently the rank-two theorem.

## Validation

- `#print axioms` for all three public targets reports exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- `/tmp/T007Validation.lean` constructs the concrete HNF `!![5,4;0,2]` in `Fin 2 → ℤ`, proves
  arbitrary HNF matrices and bases for that submodule equal the concrete ones, and computes the
  subgroup index as `10`.
- An independent coordinate-expansion proof and an independent kernel/pivot proof both confirm
  the change-of-basis argument and its multiplication direction.
- `git diff --check`, line-packing, focused/downstream builds, and the full repository build pass.

## Buzz

- Outcome: FAST-BOARD.  A threshold-100 ms profiled compile reports `matrix_eq` at roughly
  0.12 s; `bN_eq` and `index_eq_natAbs_det` do not reach the threshold.
- No heartbeat override, profiler scaffold, or deferral remains.

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
