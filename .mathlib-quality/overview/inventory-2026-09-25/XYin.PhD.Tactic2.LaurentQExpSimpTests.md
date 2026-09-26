# Inventory: XYin/PhD/Tactic2/LaurentQExpSimpTests.lean  (63 lines)

Eight anonymous `example`s exercising the project's Laurent q-expansion coefficient API (`laurentqExpansion.coeff_of_geq`, `coeff_eq_zero_of_lt`, `coeff_neg_poleOrder_add` from `XYin/PhD/LaurentQExpansion/LaurentQExpansion.lean`) by `simpa`. Despite its name and location it does NOT import or use `qexp_simp`/`qexp_simps` (it imports only `XYin.PhD.LaurentQExpansion.LaurentQExpansion`). Contains NO declarations. Imported by the library root `XYin.lean:29`.

## Declarations

(none — only `open`, `variable`, `section` and `example`s; no copyright header, no module docstring)

Common context (L7, L46): `{h : ℝ} {f g : ℍ → ℂ} {M : ℕ} {n : ℤ}` / `{c0 c1 c2 : ℂ}`. Project names used: `UpperHalfPlane.poleOrder` (LaurentQExpansion.lean:236), `UpperHalfPlane.poleRemoved` (:316), `UpperHalfPlane.to_qExpansion` (:321), `laurentqExpansion` (:447), `laurentqExpansion.coeff_eq_zero_of_lt` (:457), `laurentqExpansion.coeff_neg_poleOrder_add` (:465), `laurentqExpansion.coeff_of_geq` (:469).

### `example` — L9–14
- **Type**: `(hM : poleOrder h f = M) (hn : n ≥ -(M:ℤ)) : (laurentqExpansion h f).coeff n = (to_qExpansion h f).coeff (Int.toNat (n + M))`
- **What**: Above the pole order, Laurent coefficients are shifted power-series coefficients (pole order given as a variable).
- **How**: `laurentqExpansion.coeff_of_geq` after rewriting `poleOrder h f = M`.
- **Hypotheses**: pole order M, n ≥ −M
- **Uses from project**: `poleOrder`, `laurentqExpansion`, `to_qExpansion`, `laurentqExpansion.coeff_of_geq`
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 9–14
- **Notes**: —

### `example` — L16–19
- **Type**: `(hn : n ≥ -(poleOrder h f : ℤ)) (hpr : poleRemoved h f = g) : (laurentqExpansion h f).coeff n = (qExpansion h g).coeff (Int.toNat (n + poleOrder h f))`
- **What**: Same, with the pole-removed function named `g`.
- **How**: `coeff_of_geq` + unfold `to_qExpansion`.
- **Hypotheses**: n ≥ −poleOrder, `poleRemoved h f = g`
- **Uses from project**: `poleOrder`, `poleRemoved`, `to_qExpansion`, `laurentqExpansion`, `laurentqExpansion.coeff_of_geq`
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 16–19
- **Notes**: —

### `example` — L21–26
- **Type**: `(h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g) (hn : n ≥ -1) : (laurentqExpansion h f).coeff n = (qExpansion h g).coeff (Int.toNat (n + 1))`
- **What**: Simple-pole instance of the previous.
- **How**: same.
- **Hypotheses**: pole order 1, n ≥ −1
- **Uses from project**: as above
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 21–26
- **Notes**: —

### `example` — L28–33
- **Type**: `(hM : poleOrder h f = M) (hn : n < -(M:ℤ)) : (laurentqExpansion h f).coeff n = 0`
- **What**: Below the pole order the Laurent coefficient vanishes.
- **How**: `laurentqExpansion.coeff_eq_zero_of_lt`.
- **Hypotheses**: pole order M, n < −M
- **Uses from project**: `poleOrder`, `laurentqExpansion`, `laurentqExpansion.coeff_eq_zero_of_lt`
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 28–33
- **Notes**: —

### `example` — L35–40
- **Type**: identical to L28–33
- **What/How/Hypotheses/Uses from project**: identical to L28–33.
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 35–40
- **Notes**: BYTE-IDENTICAL DUPLICATE of the example at L28–33.

### `example` — L48–51
- **Type**: `(h1 : poleOrder h f = 1) (hpr : poleRemoved h f = g) (hcoeff0 : (qExpansion h g).coeff 0 = c0) : (laurentqExpansion h f).coeff (-1) = c0`
- **What**: Leading (q⁻¹) coefficient of a simple pole is the constant term of the pole-removed function.
- **How**: `laurentqExpansion.coeff_neg_poleOrder_add 0`.
- **Hypotheses**: pole order 1, `poleRemoved h f = g`, given constant term
- **Uses from project**: `poleOrder`, `poleRemoved`, `to_qExpansion`, `laurentqExpansion`, `laurentqExpansion.coeff_neg_poleOrder_add`
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 48–51
- **Notes**: —

### `example` — L53–56
- **Type**: same with index 0 ↔ `coeff 1 = c1`
- **What/How**: `coeff_neg_poleOrder_add 1`.
- **Hypotheses/Uses from project**: as above
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 53–56
- **Notes**: —

### `example` — L58–61
- **Type**: same with index 1 ↔ `coeff 2 = c2`
- **What/How**: `coeff_neg_poleOrder_add 2`.
- **Hypotheses/Uses from project**: as above
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 58–61
- **Notes**: —

## File Summary
- Total declarations: 0 (0 defs, 0 lemmas/theorems, 0 instances, 0 other); 8 `example`s
- Key API (used by 3+ others in the file): none
- Unused declarations: none
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations (evidence for the analysis phases)
### Mathlib API candidates
- Not applicable (no definitions; the tested API is project-specific `laurentqExpansion`). Nothing searched.

### Missing API / repeated patterns
- The three `coeff_neg_poleOrder_add` examples (L48–61) and the three `coeff_of_geq` examples (L9–26) each repeat the pattern "rewrite `poleOrder h f = 1`/`= M` via `simpa [h1/hM]`" — suggests the project API lacks versions of `coeff_of_geq`/`coeff_neg_poleOrder_add` taking `poleOrder h f = M` as an explicit hypothesis (so callers need not `simpa` the substitution). Candidate: `laurentqExpansion.coeff_of_geq' (hM : poleOrder h f = M) (hn : -M ≤ n) : … = (qExpansion h (poleRemoved h f)).coeff (n + M).toNat`.

### Junk candidates
- Whole file: test-only, no declarations, misnamed (no "QExpSimp" content, no tactic tested), misplaced (does not import `Tactic2` at all), and imported by the library root (`XYin.lean:29`) so it is built with the library. Should move to a `test/` target or be deleted (it tests nothing that `LaurentQExpansion.lean` doesn't already state).
- L35–40 duplicates L28–33 verbatim.
- No copyright header / module docstring.

### Moral duplicates within this batch
- L28–33 ≡ L35–40 (identical).
- L16–19 and L21–26 are the general and M=1 instance of the same statement.

### Generalization notes
- None.
