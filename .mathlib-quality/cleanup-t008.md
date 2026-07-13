# Cleanup record: T008

## Baseline and scope

- Target: `Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`
  in `XYin/PhD/Cox/HermiteNormalForm.lean`.
- This ticket completes the whole HNF file: it is now entirely sorry-free.
- Both focused and full-repository `lake build` pass.

## API and mathematical audit

- A full-rank submodule is diagonalized using mathlib's Smith bases, giving an additive equivalence
  from the quotient to `ZMod |c₀| × ZMod |c₁|`.
- The product is cyclic exactly when `|c₀|` and `|c₁|` are coprime, by
  `AddGroup.isAddCyclic_prod_iff` and `Nat.card_zmod`.
- The gcd of all four entries is invariant under integral changes of both ambient and submodule
  bases: one direction follows because every entry after left or right multiplication is an
  integer linear combination of the old entries; the reverse basis changes give the converse
  divisibility.
- Therefore the HNF entry content is `gcd |c₀| |c₁|`, proving the desired equivalence.
- Crucially, the proof never assumes Smith coefficients satisfy an invariant-factor divisibility
  chain.  It uses only the diagonal quotient decomposition and content invariance.

## Cleanup and simplify

- Kept the four elementary content-divisibility lemmas private, avoiding an unnecessary public
  matrix API while making the invariance proof explicit.
- Used direct `Int.natCast_dvd`, two-term matrix sums, and `Nat.dvd_antisymm`; no ideal abstraction
  or ad hoc quotient generator was needed.
- Added a theorem doc note recording the non-use of normalized Smith coefficients and retained
  direct imports only.
- The focused build emits no warning, flexible-tactic diagnostic, or long-line diagnostic.

## Validation

- `#print axioms` for the public target reports exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- `/tmp/T008Validation.lean` constructs the diagonal quotient equivalence explicitly.  It proves
  `diag(2,2)` has noncyclic quotient and content two, while `diag(1,m)` has cyclic quotient and
  content one for every `m`.
- Independent proof review confirmed both basis-change directions, the nested gcd computation,
  and the absence of any invariant-factor normalization assumption.
- `git diff --check`, no-sorry, line-packing, focused build, and full repository build pass.

## Buzz

- Outcome: FAST-BOARD.  A threshold-100 ms profiled compile reports the target at roughly 0.24 s,
  far below the 1000 ms budget.
- No heartbeat override, profiler scaffold, native decision axiom, or deferral remains.

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
