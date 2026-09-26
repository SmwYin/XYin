# Inventory: XYin/PhD/Modularforms/upperhalfplane.lean  (17 lines)

Two positivity lemmas: `Im(−n/z) > 0` for `z ∈ ℍ` and `n` a positive natural (as `ℕ+`) or positive integer. Imported by eta.lean (uses `pnat_div_upper 1 z` at L37) and Summability/Reciprocal.lean (uses neither name).

## Declarations

### `lemma pnat_div_upper`
- **Type**: `(n : ℕ+) (z : ℍ) : 0 < (-(n : ℂ) / z).im`
- **What**: `−n/z` lies in ℍ for `n ∈ ℕ+`.
- **How**: `im_pnat_div_pos (↑n) z`.
- **Hypotheses**: none (positivity is in the type `ℕ+`).
- **Uses from project**: []
- **Used by**: unused in file; externally eta.lean:37 (`pnat_div_upper 1 z`)
- **Visibility**: public
- **Lines**: 13, body 1 line
- **Notes**: **pure alias** of mathlib `UpperHalfPlane.im_pnat_div_pos (n : ℕ) [NeZero n] (z : ℍ)` (`Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean:180`) — the `ℕ+`→`ℕ` coercion is the only difference; the single call site `pnat_div_upper 1 z` is literally `im_pnat_div_pos 1 z`.

### `lemma pos_nat_div_upper`
- **Type**: `(n : ℤ) (hn : 0 < n) (z : ℍ) : 0 < (-(n : ℂ) / z).im`
- **What**: `−n/z ∈ ℍ` for a positive integer `n`.
- **How**: `Complex.div_im`, `neg_div`, `div_pos (mul_pos (Int.cast_pos.mpr hn) z.im_pos) z.normSq_pos` — the same proof as mathlib's `im_pnat_div_pos`/`im_inv_neg_coe_pos` (`Basic.lean:177–181`).
- **Hypotheses**: `0 < n`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 15–17, body 2 lines
- **Notes**: unused anywhere. No mathlib version for `ℤ` (searched `im_int_div_pos`, `neg_div … im` in `UpperHalfPlane/Basic.lean`); composable from `im_pnat_div_pos n.toNat` after `Int.toNat_of_nonneg`, or better stated for any real `r > 0` (`Im(−r/z) = r·Im z/normSq z`).

## File Summary
- Total declarations: 2 (0 defs; 2 lemmas; 0 instances; 0 other)
- Key API (used by 3+ others in the file): none
- Unused declarations (not used by anything in this file): both in-file; project-wide `pos_nat_div_upper` is unused
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations

### Mathlib API candidates
- `pnat_div_upper` (L13) = `UpperHalfPlane.im_pnat_div_pos` (`Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean:180`) — replace the one call in eta.lean:37 and delete.
- `pos_nat_div_upper` (L15): same proof as mathlib's `im_inv_neg_coe_pos` (:177) / `im_pnat_div_pos` (:180); a positive-real version `im_neg_real_div_pos (r : ℝ) (hr : 0 < r) (z : ℍ) : 0 < (-(r:ℂ)/z).im` would subsume both mathlib's ℕ version and this ℤ version — small upstream candidate; currently unused.

### Missing API / repeated patterns
- None.

### Junk candidates
- Whole file: `pnat_div_upper` is an alias, `pos_nat_div_upper` is unused; after fixing eta.lean:37 the file and both importers' `import XYin.PhD.Modularforms.upperhalfplane` lines (eta.lean, Summability/Reciprocal.lean) can go.
- Import `Mathlib.Data.Real.StarOrdered` (L4) and all the `open` lines (L8–11) are unused.

### Moral duplicates within this batch
- `pnat_div_upper` (ℕ+) / `pos_nat_div_upper` (ℤ) / mathlib `im_pnat_div_pos` (ℕ): three spellings of `Im(−n/z) > 0`.

### Generalization notes
- Both hold for any real `r > 0` (indeed the proof of `pos_nat_div_upper` only uses `0 < (n : ℝ)`); the ℕ+/ℤ restrictions are incidental.
