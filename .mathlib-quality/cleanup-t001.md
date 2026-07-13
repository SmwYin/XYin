# Cleanup record: T001

## Baseline and scope

- Target: `XYin/PhD/Cox/LatticeJ.lean`, declarations `PeriodPair.mem_smul_lattice` through
  `PeriodPair.j_congr`.
- Baseline and final command: `lake build XYin.PhD.Cox.LatticeJ` (pass, 3824 jobs).
- Diagnostics: only the planned sorries belonging to later tickets; no warning in the T001 range.
- References read: cleanup command, golfing rules, proof patterns, search, generalisation, style,
  naming, cleanup gates, review stages, buzz, and profiling.

## Per-declaration audit

| Declaration | Body lines | Naming | Packing | Inequalities | Structure | Search/generalisation |
|---|---:|---|---|---|---|---|
| `mem_smul_lattice` | 6 | pass | pass | none | pass | project-specific; no weakening |
| `G_smul` | 14 | pass | pass | none | pass | no mathlib scale API; no weakening |
| `g₂_smul` | 2 | pass | pass | none | pass | derived invariant weight; no weakening |
| `g₃_smul` | 2 | pass | pass | none | pass | derived invariant weight; no weakening |
| `discriminant_smul` | 2 | pass | pass | none | pass | derived invariant weight; no weakening |
| `j_smul` | 5 | pass | pass | none | pass | homothety invariance; no weakening |
| `g₂_congr` | 2 | pass | pass | none | pass | direct dependence on lattice; no weakening |
| `g₃_congr` | 2 | pass | pass | none | pass | direct dependence on lattice; no weakening |
| `j_congr` | 1 | pass | pass | none | pass | direct dependence on lattice; no weakening |

The search pass used the local mathlib declaration index, direct source grep, project-name search,
the Weierstrass source, and the checked historical implementation. Mathlib defines `PeriodPair.G`,
`g₂`, and `g₃`, but has no scalar action or corresponding scaling/congruence API.

## Fixes and golfing

- Preserved the explicit `mem_smul_lattice` proof after `aesop`, `grind [mem_lattice]`, and
  terminal `simp [mem_lattice]` failed to close it.
- Kept the local lattice equivalence inside `G_smul`, avoiding a single-use wrapper definition.
- Replaced lambda `=>` with mathlib-style `↦`.
- Added missing one-sentence docstrings to the public scaling and `j_congr` declarations.
- Unsqueezed the terminal `simp only` in `j_congr` to terminal `simp`.
- No rename, decomposition, generalisation, import, or new helper was needed.

## Gates

| Gate | Result |
|---|---|
| `lake_build_file` | pass |
| `definition_protected` | pass |
| `theorem_statement_protected` | pass |
| `structure_gate` | pass |
| `naming_gate` | pass |
| `line_packing_gate` | pass; all combined signatures would exceed 100 characters |
| `inequality_orientation_gate` | pass; no `≥` or `>` in scope |
| `cumulative_no_unintended_breakage` | pass |
| axiom audit | pass; only `propext`, `Classical.choice`, `Quot.sound` |
| scaling sanity tests | pass for `-1`, `I`, and the non-torsion unit `2` |

## Simplify and buzz

- Simplify outcome: issues found and fixed (lambda syntax, missing docstrings, terminal simp).
- Buzz outcome: FAST-BOARD. A threshold-1 ms profiled compile found every T001 declaration far
  below 1 second; the largest observed tactic node in scope was about 16 ms.
- No heartbeat limit, profiling scaffold, or performance deferral remains.

## Phase checklist

- [x] Doctor
- [x] Prepare
- [x] Style audit
- [x] File-level fixes
- [x] Per-declaration cleanup
- [x] Non-rename refactoring
- [x] Rename pass (empty queue)
- [x] Final verification and gates
- [x] Simplify pass
- [x] Buzz pass
- [x] Report
