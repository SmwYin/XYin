# Source: /Users/dfa25dxu/Projects/Lean/XYin/ScratchGS.lean — Project-internal imports: [`XYin.PhD.Cox.LatticeJ`]

This file contains **no declarations whatsoever**. It is a scratch/exploration file consisting of one project-internal import followed by ten `#check` commands probing mathlib API, apparently while hunting for the right equivalence/tsum lemmas for a lattice rescaling argument (matching the homothety work in `XYin/PhD/Cox/LatticeJ.lean`):

- `#check Equiv.ofBijective`
- `#check DistribMulAction.toAddEquiv`
- `#check AddEquiv.ofBijective`
- `#check AddSubgroup.equivMapOfInjective`
- `#check AddEquiv.addSubgroupMap`
- `#check Equiv.Set.image`
- `#check Equiv.Set.preimage`
- `#check Equiv.tsum_eq`
- `#check tsum_mul_left`

`#check` commands elaborate an expression and print its type; they create no environment declarations. The file contributes nothing to the project's mathematical content and is a candidate for deletion (its import does pull `XYin.PhD.Cox.LatticeJ` into any build target that includes this root-level file).

### File Summary
- Total declarations: 0 (0 defs, 0 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): []
- Unused declarations (not used by anything in this file): []
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: []
