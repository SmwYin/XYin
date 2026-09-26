# Inventory: XYin/PhD/Modularforms/iteratedderivs.lean  (72 lines)

Closed forms for iterated derivatives (within the upper half-plane) of 1/(z ± d) and of exp(2πi m z), and nonvanishing of z + d on ℍ. Root of the derivative chain: imported by `tsumderivWithin.lean` and used in `Summability/QExpansion.lean`. No file header/docstring. Every result is now covered by mathlib (`Mathlib/Analysis/Calculus/Deriv/ZPow.lean`, `IteratedDeriv/WithinZpow.lean`, `SpecialFunctions/ExpDeriv.lean`, `Trigonometric/Cotangent.lean`).

## Declarations

### `theorem upper_ne_int`
- **Type**: `(x : ℍ) (d : ℤ) : (x : ℂ) + d ≠ 0`
- **What**: z + d ≠ 0 for z ∈ ℍ and integer d.
- **How**: compare imaginary parts (`x.im_pos.ne'` via `congrArg Complex.im`).
- **Hypotheses**: x ∈ ℍ.
- **Uses from project**: []
- **Used by**: `aut_contDiffOn` (47); Summability/QExpansion.lean:153,155
- **Visibility**: public
- **Lines**: 20–22, proof body ≈ 2 lines
- **Notes**: = mathlib `Complex.integerComplement_add_ne_zero (UpperHalfPlane.coe_mem_integerComplement x) d` (`Mathlib/Analysis/Complex/IntegerCompl.lean:52`, `:37`); also `UpperHalfPlane.ne_intCast` (`UpperHalfPlane/Basic.lean:187`) + `add_eq_zero_iff_eq_neg`. Moral twin of Reciprocal.lean `upp_half_not_ints`.

### `theorem aut_iter_deriv`
- **Type**: `(d : ℤ) (k : ℕ) : EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z + d)) {z | 0 < z.im}) (fun t => (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) {z | 0 < z.im}`
- **What**: d^k/dz^k [1/(z+d)] = (−1)^k k!/(z+d)^{k+1} on ℍ.
- **How**: `iteratedDerivWithin_of_isOpen` (`Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:318`) to pass to `iteratedDeriv`, `iteratedDeriv_comp_add_const` (`IteratedDeriv/Lemmas.lean:464`) to shift, then mathlib `iteratedDerivWithin_one_div` (`IteratedDeriv/WithinZpow.lean:34`) on `univ`, converting zpow `-1-k` to `1/(·)^(k+1)`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `aut_iter_deriv'` (40), `iter_div_aut_add` (57)
- **Visibility**: public
- **Lines**: 25–34, proof body ≈ 7 lines
- **Notes**: Mathlib `iter_deriv_inv_linear` (`Mathlib/Analysis/Calculus/Deriv/ZPow.lean:143`) gives the global `iteratedDeriv` formula directly (used by mathlib's `eqOn_iteratedDeriv_cotTerm`, `Cotangent.lean:252`). Re-proves `isOpen_upperHalfPlaneSet` inline (30).

### `theorem aut_iter_deriv'`
- **Type**: `(d : ℤ) (k : ℕ) : EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z - d)) {z | 0 < z.im}) (fun t => (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) {z | 0 < z.im}`
- **What**: Same for 1/(z − d).
- **How**: `aut_iter_deriv (-d)` + `sub_eq_add_neg`.
- **Hypotheses**: none.
- **Uses from project**: `aut_iter_deriv`
- **Used by**: `iter_div_aut_add` (57)
- **Visibility**: public
- **Lines**: 37–40, proof body ≈ 1 line
- **Notes**: Mathlib `iter_deriv_inv_linear_sub` (`Deriv/ZPow.lean:164`).

### `theorem aut_contDiffOn`
- **Type**: `(d : ℤ) (k : ℕ) : ContDiffOn ℂ k (fun z : ℂ => 1 / (z - d)) {z | 0 < z.im}`
- **What**: 1/(z − d) is C^k on ℍ.
- **How**: `contDiffOn_const.div (contDiffOn_id.sub contDiffOn_const)` with denominators nonzero by `upper_ne_int`.
- **Hypotheses**: none.
- **Uses from project**: `upper_ne_int`
- **Used by**: `iter_div_aut_add` (56, applied at d and −d)
- **Visibility**: public
- **Lines**: 43–47, proof body ≈ 3 lines
- **Notes**: Mathlib has the same as private `contDiffOn_inv_linear` (`Cotangent.lean:249`) on `ℂ_ℤ`.

### `theorem iter_div_aut_add`
- **Type**: `(d : ℤ) (k : ℕ) : EqOn (iteratedDerivWithin k (fun z => 1 / (z - d) + 1 / (z + d)) {z | 0 < z.im}) ((fun t => (-1)^k * k! * (1/(t - d)^(k+1))) + fun t => (-1)^k * k! * (1/(t + d)^(k+1))) {z | 0 < z.im}`
- **What**: Closed form for the k-th derivative of the cotangent term 1/(z−d) + 1/(z+d).
- **How**: `iteratedDerivWithin_fun_add` (`IteratedDeriv/Lemmas.lean:82`) with `UniqueDiffOn` from openness and `aut_contDiffOn` at ±d, then `aut_iter_deriv'`/`aut_iter_deriv` pointwise.
- **Hypotheses**: none.
- **Uses from project**: `aut_contDiffOn`, `aut_iter_deriv`, `aut_iter_deriv'`
- **Used by**: unused in file; Summability/QExpansion.lean:88,137,166,195
- **Visibility**: public
- **Lines**: 50–57, proof body ≈ 3 lines
- **Notes**: = mathlib `eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet` (`Cotangent.lean:276`) for d = n+1 ∈ ℕ+ (zpow form `(-1-k : ℤ)`); the general-d version follows from `iter_deriv_inv_linear(_sub)` + `iteratedDeriv_add`. The most-used declaration of the file (4 external sites).

### `theorem exp_iter_deriv_within`
- **Type**: `(n m : ℕ) : EqOn (iteratedDerivWithin n (fun s : ℂ => exp (2πi m s)) {z | 0 < z.im}) (fun t => (2πi m) ^ n * exp (2πi m t)) {z | 0 < z.im}`
- **What**: d^n/ds^n exp(2πi m s) = (2πi m)^n exp(2πi m s) on ℍ.
- **How**: `iteratedDerivWithin_of_isOpen` + mathlib `iteratedDeriv_cexp_const_mul` (`Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:209`).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file; Summability/QExpansion.lean:47, tsumderivWithin.lean:82,137
- **Visibility**: public
- **Lines**: 65–72, proof body ≈ 2 lines
- **Notes**: = mathlib private `iteratedDerivWithin_cexp_aux k m 1` (`EisensteinSeries/QExpansion.lean:52`) up to `/1`; its public consumers phrase things via `cexp (2πI z) ^ m`. Holds on any open set (the proof only uses openness).

## File Summary
- Total declarations: 6 (0 defs, 6 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none (`aut_iter_deriv` 2 in-file users)
- Unused declarations (not used by anything in this file): `iter_div_aut_add`, `exp_iter_deriv_within` (both used in other batch files; nothing in this file is used outside the batch — `grep -rnw` over XYin minus batch: none)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `upper_ne_int` (20) = `Complex.integerComplement_add_ne_zero` (`IntegerCompl.lean:52`) ∘ `coe_mem_integerComplement`.
- `aut_iter_deriv`/`aut_iter_deriv'` (25/37) = `iter_deriv_inv_linear`/`iter_deriv_inv_linear_sub` (`Mathlib/Analysis/Calculus/Deriv/ZPow.lean:143/164`) + `iteratedDerivWithin_of_isOpen`; the file already uses `iteratedDerivWithin_one_div` (`WithinZpow.lean:34`) and `iteratedDeriv_comp_add_const` (`Lemmas.lean:464`).
- `aut_contDiffOn` (43) = Cotangent.lean private `contDiffOn_inv_linear` (:249); public route `ContDiffOn.inv (by fun_prop) (fun x hx ↦ integerComplement_add_ne_zero …)`.
- `iter_div_aut_add` (50) = `eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet` (`Cotangent.lean:276`) for d ≥ 1.
- `exp_iter_deriv_within` (65) = `iteratedDeriv_cexp_const_mul` (`ExpDeriv.lean:209`) + `iteratedDerivWithin_of_isOpen`; mathlib private `iteratedDerivWithin_cexp_aux` (`EisensteinSeries/QExpansion.lean:52`).
- `isOpen_lt continuous_const continuous_im` at 30, 55, 71 = `isOpen_upperHalfPlaneSet` (`UpperHalfPlane/Basic.lean:266`).
### Missing API / repeated patterns
- The set `{z : ℂ | 0 < z.im}` is spelled out 12 times in 72 lines instead of `upperHalfPlaneSet`/`ℍ'` (which tsumderivWithin.lean defines *after* importing this file — the dependency order is inverted).
- `iteratedDerivWithin_of_isOpen (isOpen_lt …) hx` prelude repeated at 30 and 71.
- Dead `variable {𝕜} [NontriviallyNormedField 𝕜] {F} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜)` at 59–60 — no declaration after it uses them.
### Junk candidates
- No declaration is used outside this batch; once Summability/QExpansion.lean and tsumderivWithin.lean are retired (both dead), the whole file goes.
- Spurious imports: `Mathlib.Analysis.CStarAlgebra.Classes` (3), `Mathlib.Tactic.Cases` (10), `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` (9, nothing trigonometric here).
- Missing copyright header/docstring. Blank-line noise 23–24, 35–36, 41–42, 48–49, 61–64. Names `aut_*` (from "automorphic") are opaque.
### Moral duplicates within this batch
- `upper_ne_int` (20) vs Reciprocal.lean `upp_half_not_ints` (27) vs the inline `hsub/hadd` in Reciprocal.lean `pnat_inv_sub_squares` (37–39): three proofs of "z ∓ d ≠ 0".
- `aut_iter_deriv` vs `aut_iter_deriv'`: sign only.
- `exp_iter_deriv_within` (65) vs Summability/QExpansion.lean `exp_series_ite_deriv_uexp''` (42) and tsumderivWithin.lean `der_iter_eq_der_aux2` (76): same closed form used at three levels.
### Generalization notes
- `aut_iter_deriv`, `aut_iter_deriv'`, `exp_iter_deriv_within`: the proofs only use that the set is open (`iteratedDerivWithin_of_isOpen`), so they hold for any `IsOpen s`, and in fact as global `iteratedDeriv` statements (mathlib's `iter_deriv_inv_linear`, `iteratedDeriv_cexp_const_mul`) with no set at all.
- `aut_contDiffOn`, `iter_div_aut_add`: only `z + d ≠ 0` is used, so they hold on `ℂ_ℤ` (integer complement), as in mathlib's Cotangent.lean.
- `upper_ne_int`: `d : ℤ` could be any real `d` (`Complex.ne_ofReal`-style); the proof uses only `Im d = 0`.
