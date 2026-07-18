# XYin/PhD/Tactic2/QExpSimpAttr.lean
Project-internal imports: (none — only `Mathlib.Tactic.Attr.Register`)

### `command register_simp_attr qexp_simps`
- **Type**: n/a (attribute-registration command; creates the simp attribute `@[qexp_simps]` and the simp set `qexp_simps`)
- **What**: Registers a custom simp-lemma attribute/simp set named `qexp_simps`, which serves as the lemma pool for the project's experimental q-expansion simplifier tactic.
- **How**: Direct invocation of mathlib's `register_simp_attr` command; no mathematics involved — it is pure meta infrastructure kept in its own file so the attribute exists before any file tags lemmas with it (Lean requires attribute registration in an earlier module).
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: unused in file (used by every `@[qexp_simps]` tag and both `qexp_simp` macros in `XYin/PhD/Tactic2/qexp_simp.lean`)
- **Visibility**: public
- **Lines**: 3, no proof
- **Notes**: none

### File Summary
- Total declarations: 1 (0 defs, 0 lemmas/theorems, 0 instances, 1 tactic/meta decls)
- Key API (used by 3+ others): [`qexp_simps` attribute — tagged onto 27 lemmas plus ~15 mathlib lemmas in `qexp_simp.lean`, and consumed by both `qexp_simp` macros]
- Unused declarations (not used by anything in this file): [`register_simp_attr qexp_simps` (used only downstream)]
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: []
