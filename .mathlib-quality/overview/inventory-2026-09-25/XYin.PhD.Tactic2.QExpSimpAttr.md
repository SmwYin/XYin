# Inventory: XYin/PhD/Tactic2/QExpSimpAttr.lean  (3 lines)

Registers the custom simp attribute `qexp_simps` used by `qexp_simp.lean`'s simp set and `qexp_simp` tactic. Separate file because `register_simp_attr` must be in a different module from the first `@[qexp_simps]` use. Imports `Mathlib.Tactic.Attr.Register`.

## Declarations

### `attribute registration qexp_simps` (`register_simp_attr qexp_simps`)
- **Type**: simp attribute / simp extension `qexp_simps`
- **What**: Declares an empty custom simp set named `qexp_simps`.
- **How**: `register_simp_attr` (mathlib `Mathlib/Tactic/Attr/Register.lean` re-exports core `register_simp_attr`).
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: unused in file; populated in `XYin/PhD/Tactic2/qexp_simp.lean` (29 `@[qexp_simps]` lemmas L20–154 and 4 `attribute [qexp_simps]` lines L158–163) and consumed by the `qexp_simp` macros there (L165–207)
- **Visibility**: public (global attribute)
- **Lines**: 3
- **Notes**: No docstring on the attribute (`register_simp_attr` accepts a doc comment: `/-- … -/ register_simp_attr qexp_simps`). No copyright header / module docstring.

## File Summary
- Total declarations: 1 (0 defs, 0 lemmas/theorems, 0 instances, 1 other: attribute registration)
- Key API (used by 3+ others in the file): none
- Unused declarations (not used by anything in this file): `qexp_simps` (used only in `qexp_simp.lean`)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations (evidence for the analysis phases)
### Mathlib API candidates
- Not applicable: this is the idiomatic mathlib way to declare a simp set (`register_simp_attr`, as used by e.g. `Mathlib/Tactic/Attr/Register.lean` itself for `mfld_simps`, `nontriviality`, etc.). Nothing to replace.

### Missing API / repeated patterns
- Missing docstring on the attribute.

### Junk candidates
- The file is required only because `qexp_simp.lean` exists; if the Tactic2 layer is retired, this goes with it. Imported by the library root (`XYin.lean:30`) although nothing in the library uses the attribute (grep-verified: all `qexp_simps` occurrences are in `Tactic2/qexp_simp.lean`).

### Moral duplicates within this batch
- None.

### Generalization notes
- None.
