# XYin/PhD/Tactic2/LaurentQExpSimpTests.lean
Project-internal imports: XYin.PhD.LaurentQExpansion.LaurentQExpansion

Pure test file: 8 anonymous `example`s (two of them literally identical) exercising the Laurent q-expansion coefficient API from `XYin/PhD/LaurentQExpansion/LaurentQExpansion.lean`. Despite the file name, the `qexp_simp` tactic is NOT used anywhere — every proof is a direct `simpa using` application of a `laurentqExpansion` lemma. The file does not import `XYin.PhD.Tactic2.qexp_simp`.

### `example (test 1, coefficient above pole order via named pole order)`
- **Type**: `(hM : poleOrder h f = M) (hn : n ≥ -(M : ℤ)) : (laurentqExpansion h f).coeff n = (to_qExpansion h f).coeff (Int.toNat (n + M))`
- **What**: For n ≥ −M (M the pole order of f at the cusp), the n-th Laurent coefficient of f equals the (n+M)-th coefficient of the ordinary power-series q-expansion of the pole-removed function — i.e. the Laurent expansion is the power series shifted by the pole order.
- **How**: Transports the hypothesis n ≥ −M to n ≥ −poleOrder h f by rewriting with hM, then applies the project lemma `laurentqExpansion.coeff_of_geq` (which expresses laurentqExpansion as qᵖᵒˡᵉᴼʳᵈᵉʳ-shifted `to_qExpansion`) and rewrites back with `simpa [hM]`.
- **Hypotheses**: poleOrder h f = M; n ≥ −M.
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.laurentqExpansion`, `UpperHalfPlane.to_qExpansion`, `laurentqExpansion.coeff_of_geq`]
- **Used by**: unused in file
- **Visibility**: public (anonymous example)
- **Lines**: 9–14, 4-line proof
- **Notes**: none

### `example (test 2, coefficient above pole order via named pole-removed function)`
- **Type**: `(hn : n ≥ -(poleOrder h f : ℤ)) (hpr : poleRemoved h f = g) : (laurentqExpansion h f).coeff n = (qExpansion h g).coeff (Int.toNat (n + poleOrder h f))`
- **What**: Same shift identity as test 1, but phrased through a named pole-removed function g: above the pole order, Laurent coefficients of f are ordinary q-expansion coefficients of g = poleRemoved h f.
- **How**: Applies `laurentqExpansion.coeff_of_geq` and unfolds the definition `to_qExpansion h f = qExpansion h (poleRemoved h f)` via `simpa [to_qExpansion, hpr]`.
- **Hypotheses**: n ≥ −poleOrder h f; poleRemoved h f = g.
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.poleRemoved`, `UpperHalfPlane.laurentqExpansion`, `UpperHalfPlane.to_qExpansion`, `laurentqExpansion.coeff_of_geq`]
- **Used by**: unused in file
- **Visibility**: public (anonymous example)
- **Lines**: 16–19, 2-line proof
- **Notes**: none

### `example (test 3, simple-pole specialization)`
- **Type**: `(h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g) (hn : n ≥ -(1 : ℤ)) : (laurentqExpansion h f).coeff n = (qExpansion h g).coeff (Int.toNat (n + 1))`
- **What**: Specializes the shift identity to a simple pole (pole order 1): for n ≥ −1 the n-th Laurent coefficient of f is the (n+1)-st q-expansion coefficient of the pole-removed g.
- **How**: Rewrites the bound to n ≥ −poleOrder h f using h1, applies `laurentqExpansion.coeff_of_geq`, and normalizes with `simpa [to_qExpansion, h1, hpr]`.
- **Hypotheses**: poleOrder h f = 1; poleRemoved h f = g; n ≥ −1.
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.poleRemoved`, `UpperHalfPlane.laurentqExpansion`, `UpperHalfPlane.to_qExpansion`, `laurentqExpansion.coeff_of_geq`]
- **Used by**: unused in file
- **Visibility**: public (anonymous example)
- **Lines**: 21–26, 4-line proof
- **Notes**: none

### `example (test 4, vanishing below pole order)`
- **Type**: `(hM : poleOrder h f = M) (hn : n < -(M : ℤ)) : (laurentqExpansion h f).coeff n = 0`
- **What**: Below −M the Laurent coefficients vanish: the Laurent q-expansion has pole order at most poleOrder h f.
- **How**: Transports n < −M to n < −poleOrder h f via hM and applies the project lemma `laurentqExpansion.coeff_eq_zero_of_lt`.
- **Hypotheses**: poleOrder h f = M; n < −M.
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.laurentqExpansion`, `laurentqExpansion.coeff_eq_zero_of_lt`]
- **Used by**: unused in file
- **Visibility**: public (anonymous example)
- **Lines**: 28–33, 4-line proof
- **Notes**: none

### `example (test 5, vanishing below pole order — duplicate)`
- **Type**: `(hM : poleOrder h f = M) (hn : n < -(M : ℤ)) : (laurentqExpansion h f).coeff n = 0`
- **What**: Character-for-character duplicate of test 4 (same statement, same proof).
- **How**: Identical to test 4: rewrite via hM, apply `laurentqExpansion.coeff_eq_zero_of_lt`.
- **Hypotheses**: as test 4.
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.laurentqExpansion`, `laurentqExpansion.coeff_eq_zero_of_lt`]
- **Used by**: unused in file
- **Visibility**: public (anonymous example)
- **Lines**: 35–40, 4-line proof
- **Notes**: exact duplicate of the example at lines 28–33 — likely a copy-paste artifact; one copy should be deleted

### `example (test 6, principal-part coefficient c₋₁ for a simple pole)`
- **Type**: `(h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g) (hcoeff0 : (qExpansion h g).coeff 0 = c0) : (laurentqExpansion h f).coeff (-1) = c0`
- **What**: For a simple pole, the residue-type coefficient a₋₁ of the Laurent q-expansion equals the constant term c₀ of the q-expansion of the pole-removed function.
- **How**: Instantiates the project lemma `laurentqExpansion.coeff_neg_poleOrder_add` at n = 0 (coefficient at index −poleOrder + 0) and rewrites with `to_qExpansion`, h1, hpr, hcoeff0 via `simpa`.
- **Hypotheses**: poleOrder h f = 1; poleRemoved h f = g; (qExpansion h g).coeff 0 = c₀.
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.poleRemoved`, `UpperHalfPlane.laurentqExpansion`, `UpperHalfPlane.to_qExpansion`, `laurentqExpansion.coeff_neg_poleOrder_add`]
- **Used by**: unused in file
- **Visibility**: public (anonymous example)
- **Lines**: 48–51, 2-line proof
- **Notes**: none

### `example (test 7, constant coefficient a₀ for a simple pole)`
- **Type**: `(h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g) (hcoeff1 : (qExpansion h g).coeff 1 = c1) : (laurentqExpansion h f).coeff 0 = c1`
- **What**: For a simple pole, the constant Laurent coefficient a₀ of f equals the linear coefficient c₁ of the q-expansion of the pole-removed g.
- **How**: `laurentqExpansion.coeff_neg_poleOrder_add` at n = 1 (index −1 + 1 = 0), then `simpa [to_qExpansion, h1, hpr, hcoeff1]`.
- **Hypotheses**: poleOrder h f = 1; poleRemoved h f = g; (qExpansion h g).coeff 1 = c₁.
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.poleRemoved`, `UpperHalfPlane.laurentqExpansion`, `UpperHalfPlane.to_qExpansion`, `laurentqExpansion.coeff_neg_poleOrder_add`]
- **Used by**: unused in file
- **Visibility**: public (anonymous example)
- **Lines**: 53–56, 2-line proof
- **Notes**: none

### `example (test 8, linear coefficient a₁ for a simple pole)`
- **Type**: `(h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g) (hcoeff2 : (qExpansion h g).coeff 2 = c2) : (laurentqExpansion h f).coeff 1 = c2`
- **What**: For a simple pole, the Laurent coefficient a₁ of f equals the quadratic coefficient c₂ of the q-expansion of g (continuing the shift-by-one pattern of tests 6–7; this is the j-function-style setup where a₋₁ = 1, a₀ = 744, a₁ = 196884, ...).
- **How**: `laurentqExpansion.coeff_neg_poleOrder_add` at n = 2 (index −1 + 2 = 1), then `simpa [to_qExpansion, h1, hpr, hcoeff2]`.
- **Hypotheses**: poleOrder h f = 1; poleRemoved h f = g; (qExpansion h g).coeff 2 = c₂.
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.poleRemoved`, `UpperHalfPlane.laurentqExpansion`, `UpperHalfPlane.to_qExpansion`, `laurentqExpansion.coeff_neg_poleOrder_add`]
- **Used by**: unused in file
- **Visibility**: public (anonymous example)
- **Lines**: 58–61, 2-line proof
- **Notes**: none

### File Summary
- Total declarations: 8 (0 defs, 0 lemmas/theorems, 0 instances, 0 tactic/meta decls; 8 anonymous examples)
- Key API (used by 3+ others): [] (test file; heaviest external dependencies: `laurentqExpansion.coeff_of_geq` used by 3 examples, `laurentqExpansion.coeff_neg_poleOrder_add` used by 3, `laurentqExpansion.coeff_eq_zero_of_lt` used by 2 — all from XYin.PhD.LaurentQExpansion.LaurentQExpansion)
- Unused declarations (not used by anything in this file): [all 8 examples — anonymous tests by design]
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: []
- Additional findings: tests 4 and 5 (lines 28–33 and 35–40) are exact duplicates; despite the file name, the `qexp_simp` tactic is never invoked — the file neither imports `XYin.PhD.Tactic2.qexp_simp` nor uses the tactic, so it tests the LaurentQExpansion coefficient API directly with `simpa`.
