# Inventory: XYin/PhD/Modularforms/AtImInfty.lean  (27 lines)

Three small helpers about mathlib's filter `UpperHalfPlane.atImInfty`: an `∀ᶠ` unfolding, `Im → +∞` along it, and "a function with nonzero limit at i∞ is not the zero function". Header comment (L8–10) flags it as ForMathlib material for `Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean`. Imported by ResToImagAxis.lean, which uses only `Filter.eventually_atImInfty` (L353).

## Declarations

### `lemma Filter.eventually_atImInfty`
- **Type**: `{p : ℍ → Prop} : (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z`
- **What**: A property holds eventually at i∞ iff it holds on some half-plane `Im z ≥ A`.
- **How**: `atImInfty_mem (setOf p)` (mathlib `UpperHalfPlane.atImInfty_mem`, `Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean:42`).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file; externally ResToImagAxis.lean:353
- **Visibility**: public
- **Lines**: 14–16, body 1 line
- **Notes**: one-line wrapper; also available as `atImInfty_basis.eventually_iff` (`FunctionsBoundedAtInfty.lean:39`) up to `true_and`. Declared into the `Filter` namespace; the mathlib name would be `UpperHalfPlane.eventually_atImInfty`. Legitimate ForMathlib candidate (mathlib has the `mem` form but not the `eventually` form — searched `eventually_atImInfty` across `Mathlib/`).

### `lemma Filter.tendsto_im_atImInfty`
- **Type**: `Tendsto (fun x : ℍ ↦ x.im) atImInfty atTop`
- **What**: The imaginary part tends to `+∞` along `atImInfty`.
- **How**: `tendsto_iff_comap.mpr fun _ a => a` — since `atImInfty := Filter.atTop.comap im` (`FunctionsBoundedAtInfty.lean:31`), this is `Filter.tendsto_comap`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 18–19, body 1 line
- **Notes**: unused anywhere; = `Filter.tendsto_comap` (definitional). No mathlib lemma of this name (searched `tendsto_im_atImInfty`, `tendsto_im` in `UpperHalfPlane/`), but mathlib's `tendsto_coe_atImInfty`/`tendsto_comap_im_ofComplex` (:78/:85) are the neighbours.

### `lemma ne_zero_of_tendsto_ne_zero`
- **Type**: `{f : ℍ → ℂ} {c : ℂ} (hc : c ≠ 0) (hf : Tendsto f atImInfty (nhds c)) : f ≠ 0`
- **What**: If `f → c ≠ 0` at i∞ then `f` is not identically zero.
- **How**: If `f = 0` then `f → 0` (`tendsto_const_nhds`), and `tendsto_nhds_unique` (needs `atImInfty.NeBot`, mathlib instance `FunctionsBoundedAtInfty.lean:34`) forces `0 = c`.
- **Hypotheses**: `c ≠ 0`, `f → c`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 25–27, body 1 line
- **Notes**: unused anywhere; docstring (L21–24) explains the argument. Nothing about ℍ or ℂ is used: holds for any `[l.NeBot]` filter into a `T2Space` with `Zero`.

## File Summary
- Total declarations: 3 (0 defs; 3 lemmas; 0 instances; 0 other)
- Key API (used by 3+ others in the file): none
- Unused declarations (not used by anything in this file): all three in-file; project-wide `Filter.tendsto_im_atImInfty` and `ne_zero_of_tendsto_ne_zero` are unused
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations

### Mathlib API candidates
- `Filter.eventually_atImInfty` (L14): wrapper around `UpperHalfPlane.atImInfty_mem` (`FunctionsBoundedAtInfty.lean:42`) / `atImInfty_basis.eventually_iff` (:39); mathlib lacks the `∀ᶠ` spelling — upstream candidate under the name `UpperHalfPlane.eventually_atImInfty`.
- `Filter.tendsto_im_atImInfty` (L18): is `Filter.tendsto_comap` for `atImInfty = atTop.comap im` (`FunctionsBoundedAtInfty.lean:31`).
- `ne_zero_of_tendsto_ne_zero` (L25): general fact `Tendsto f l (𝓝 c) → c ≠ 0 → f ≠ 0` for `[l.NeBot]`; no mathlib lemma found in this exact shape (searched `ne_zero_of_tendsto`, `Tendsto.ne_zero`), but `Filter.Tendsto.eventually_ne` + `NeBot` gives it in one line; unused anyway.

### Missing API / repeated patterns
- None; the file is three one-liners.

### Junk candidates
- `Filter.tendsto_im_atImInfty` (L18), `ne_zero_of_tendsto_ne_zero` (L25): unused anywhere.
- Import `Mathlib.Analysis.Normed.Group.Tannery` (L3) is unrelated to the content.
- Namespace: `Filter.` prefix on ℍ-specific lemmas is wrong; should be `UpperHalfPlane.`.

### Moral duplicates within this batch
- `Filter.eventually_atImInfty` is used in ResToImagAxis.lean:353 to do what `atImInfty_mem`/`isBigO_iff` + `eventually_atImInfty` do; ResToImagAxis's private `tendsto_ofComplex_I_mul_atTop` is the natural companion of `tendsto_im_atImInfty` (composition `im ∘ (t ↦ it) = t`).

### Generalization notes
- `ne_zero_of_tendsto_ne_zero`: stated for `ℍ → ℂ` but holds for `f : α → E` with any filter `l` `[l.NeBot]` and `[T2Space E] [Zero E]` (only `tendsto_nhds_unique` and `tendsto_const_nhds` are used).
