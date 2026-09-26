# Lattice j and cyclic sublattice proof cleanup

Scope: `XYin/PhD/Cox/LatticeJ.lean` and `XYin/PhD/Cox/CyclicSublattice.lean`.
Both files were read fully, including every proof body. Baseline is
`/tmp/xyin-proof-cleanup-before/XYin`, after the structural refactor. This pass preserves
all declarations, signatures, data fields, documentation, namespace boundaries and imports.
No new helper or abstraction, axiom, admission, or raised limit was introduced.

| File | Before | After | Reduction |
|---|---:|---:|---:|
| LatticeJ | 691 | 632 | 59 |
| CyclicSublattice | 671 | 551 | 120 |

## LatticeJ audit

- Scaling: `map_lattice_mulLeftLinearEquiv` now reduces map membership and uses equality
  symmetry directly. `G_smul` reuses the already defined `smulLatticeEquiv`, removing an
  independently constructed bijection. The other scaling/congruence proofs are retained:
  they already use tsum scaling and invariant formulas directly.
- Period pair and Eisenstein comparisons: retained `periodPair_G_eq_aux`, zeta-six,
  `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`, `Delta_eq_E4_E6`, and
  `j_eq_periodPair_j`; their finite scaling/ring calculations and established analytic
  identities have no redundant large subproof or matching stronger local API.
- `exists_homothetic_periodPair`: both orientation branches now simplify the two period
  generators directly. Removed explicit generator equalities and transport chains.
- Nonvanishing and homothety classification: `j_eq_zero_iff_g₂_eq_zero_aux` is a direct
  simplification; `j_eq_1728_iff_g₃_eq_zero_aux` uses an explicit linear combination of
  the cross-multiplied identity. Three nonzero-root arguments use `div_ne_zero` rather
  than separate power-zero scaffolding. Retained the substantive sixth/fourth root and
  generic root compatibility arguments, discriminant transport, and final case split.
- SL2 orbit classification: inspected all integer-combination, determinant, orientation,
  and lattice-transport arguments; retained them. They carry the actual extraction of an
  integral determinant-one change of basis, and broader automation would obscure it.
- Surjectivity: `inv_j_sub_slashInvariant_aux` now applies `SL_slash_apply` and
  `j_modularGroup_smul` directly. `qj_tendsto_atImInfty_aux` rewrites the existing
  product identity once and uses the product limit. The weight-zero cusp-form and
  removable reciprocal arguments remain explicit and unchanged.

## CyclicSublattice audit

- Extensionality, finite rank, HNF choice, and real independence: retained direct existing
  rank/index and determinant APIs. `hnfPeriod_eq` now applies `sum_repr` and `repr_apply`
  once, replacing repeated local coercion lemmas and a two-step calc.
- `toPeriodPair_lattice`: uses basis `span_eq`, `Submodule.map_span`, and map/range
  composition. This replaces both manually constructed membership witnesses. The Fin 2
  range is identified by `Fin.exists_fin_two`.
- Transport along lattice equivalence: retained index/quotient equivalences and cyclicity
  transport. `ofLatticeEq_carrier_map_subtype` uses `Submodule.map_comp` and congruence,
  removing the forward/reverse subtype witnesses. Scalar transport likewise uses map
  composition; `scale_toPeriodPair_lattice` is the resulting short rewrite chain.
- Carrier equivalence and transported basis: retained their explicit definitions and
  bijectivity, which are useful typed interfaces for the dual construction.
- Dual HNF arithmetic: retained the determinant-to-index conversion, torsion-free
  injectivity, and basis-equality proofs. The two second-column coordinate lemmas and
  all four dual matrix coordinate lemmas now use established simp facts rather than
  long generated simp-only lists. The key identity `d*a=m` remains visible.
- Dual index and cyclicity: retained determinant/content reasoning and Smith/HNF API;
  these are mathematically distinct from lattice equality and not redundant.
- `dualCarrier_map_subtype_aux`: uses range composition and equality of the underlying
  linear maps, replacing another pair of membership-witness constructions.
- Final public dual/scaling/j consequences: retained direct API applications.

Unused old private coercion lemmas remain because this proof-focused batch preserves the
existing declaration set. All newly shortened proofs use existing lemmas; no new one-use
wrapper is introduced.

## Searches and rejected alternatives

Read relevant primary local mathlib sources for `Submodule.map_comp`, `map_span`,
`LinearMap.range_comp`, basis `span_eq`, finite vector ranges and `Fin.exists_fin_two`,
plus existing project lattice/scaling and modular slash APIs.

- There is no `Submodule.map_map` or `Set.range_fin_two` in this revision; final code uses
  `map_comp` and `Fin.exists_fin_two`.
- Rewriting a lattice to its subtype range on both sides can alter a dependent domain;
  `dualCarrier_map_subtype_aux` confines that rewrite to the right-hand side with `conv`.
- Broad simp on the SL2 slash action unfolds its coercion into GL2 and loses the useful
  syntactic match; final proof uses a directed `simp only` followed by modular invariance.
- Replacing classification algebra by blanket search/automation, or changing mathematical
  generality, was rejected: it would change the requested API or make essential arguments
  harder to review. No nontrivial unchanged proof was treated as automatically clean.

## Validation

Final direct Lean checks and profiled checks for both files exit 0 with no diagnostics.
Before/after snapshots were compiled against the same stable dependency cache; parent owns
cumulative builds after reviewing actual diffs. Logs:

- `/tmp/xyin-lattice-cleanup-profile-before.log`, `...-after.log`
- `/tmp/xyin-sublattice-cleanup-profile-before.log`, `...-after.log`
- `/tmp/xyin-lattice-cleanup-axioms.log`
- `/tmp/xyin-sublattice-cleanup-axioms.log`

Single-run profile, not a stable benchmark:

| File | Tactic execution before → after | Typeclass inference before → after |
|---|---:|---:|
| LatticeJ | 857 → 787 ms | 2.80 → 3.05 s |
| CyclicSublattice | 1.16 s → 749 ms | 9.73 → 10.1 s |

CyclicSublattice cumulative simp and type-checking costs increased slightly (1.54→1.81 s,
1.84→2.14 s) while tactic/interpretation costs fell. No individual reported proof operation
exceeds one second. These proof-length improvements are not claimed as runtime speedups.

Nine final-source axiom checks (not stale oleans) cover `G_smul`, homothety and SL2 orbit
classification, `j_surjective`, the sublattice lattice/scaling identities, `dual`, its lattice
identity and `dual_sub_j`. All depend only on `propext`, `Classical.choice`, and `Quot.sound`.
No sorry/admit/axiom/limit addition was found. Final simplify review checked mathematical
visibility, API reuse, duplication and changed-proof elaboration.

## Final independent-review follow-up

The coordinator removed the now-unused private `coe_carrier_add` and `coe_carrier_zsmul`
wrappers after confirming their lack of callers and automation attributes. Final
`CyclicSublattice.lean` is 541 lines (baseline 671); its direct profiler run and cumulative
`lake build` pass. See `final-followup-profiler.json` and `independent-review.md`.
