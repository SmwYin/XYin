# Inventory: XYin/PhD/ModularFunctions/NormalFormSlash.lean  (97 lines)

Proves that the weight-0 slash action of any `g ∈ GL₂(ℝ)` preserves meromorphic normal form on ℍ. Positive determinant: precomposition by the analytic Möbius map with nonzero derivative (new lemma `MeromorphicNFAt.comp_analyticAt_of_deriv_ne_zero`). Negative determinant: factor through `J` (`τ ↦ -conj τ`), using new lemmas that conjugating source and target preserves analyticity and normal form.

## Declarations

### `lemma MeromorphicNFAt.comp_analyticAt_of_deriv_ne_zero`
- **Type**: `{f g : ℂ → ℂ} {x : ℂ} (hf : MeromorphicNFAt f (g x)) (hg : AnalyticAt ℂ g x) (hg' : deriv g x ≠ 0) : MeromorphicNFAt (f ∘ g) x`
- **What**: normal form is preserved by analytic changes of coordinate with nonzero derivative.
- **How**: `meromorphicNFAt_iff_analyticAt_or`; analytic case `AnalyticAt.comp`; pole case: `MeromorphicAt.comp_analyticAt`, order transported by `meromorphicOrderAt_comp_of_deriv_ne_zero`, the nonvanishing-value clause is unchanged.
- **Hypotheses**: `g` analytic at `x` with `g'(x) ≠ 0`; `f` normal form at `g x`.
- **Uses from project**: []
- **Used by**: `meromorphicNFOn_slash_zero_of_pos`, `meromorphicNFOn_slash_zero_J`
- **Visibility**: public
- **Lines**: 22–30, proof body ≈ 5 lines
- **Notes**: no mathlib analogue (searched `comp` in `NormalForm.lean`: only `toMeromorphicNFAt` lemmas). Ingredients: `NormalForm.lean:53`, `Order.lean:839`, `Basic.lean:438`. Upstream candidate; used cross-file by FieldAction? (no — FieldAction uses `MeromorphicAt.comp_analyticAt` directly).

### `lemma AnalyticAt.conj_conj`
- **Type**: `{f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f (conj x)) : AnalyticAt ℂ (fun z ↦ conj (f (conj z))) x`
- **What**: `conj ∘ f ∘ conj` is analytic where `f` is (at the conjugate point).
- **How**: `analyticAt_iff_eventually_differentiableAt`; pull `hf.eventually_analyticAt` back along `continuous_conj`; `DifferentiableAt.star_star`.
- **Hypotheses**: `f` analytic at `conj x`.
- **Uses from project**: []
- **Used by**: `MeromorphicNFAt.conj_conj`
- **Visibility**: public
- **Lines**: 32–37, proof body ≈ 3 lines
- **Notes**: no mathlib analogue (searched `conj|star` × `AnalyticAt` in `Mathlib/Analysis`; only `AnalyticAt.harmonicAt_conj`). Ingredients: `Mathlib/Analysis/Complex/CauchyIntegral.lean:690`, `Mathlib/Analysis/Calculus/FDeriv/Star.lean:129`.

### `lemma MeromorphicNFAt.conj_conj`
- **Type**: `{f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicNFAt f (conj x)) : MeromorphicNFAt (fun z ↦ conj (f (conj z))) x`
- **What**: normal form is preserved by conjugating source and target.
- **How**: destructures the raw inductive definition of `MeromorphicNFAt` (`hf | ⟨n, g, hg, hgzero, heq⟩`), conjugates the eventual-zero / `(z - x)^n • g z` representation with `AnalyticAt.conj_conj` and `Filter.EventuallyEq.comp_tendsto continuous_conj.continuousAt`.
- **Hypotheses**: `f` normal form at `conj x`.
- **Uses from project**: `AnalyticAt.conj_conj`
- **Used by**: `meromorphicNFOn_slash_zero_J`
- **Visibility**: public
- **Lines**: 39–50, proof body ≈ 9 lines
- **Notes**: relies on the definitional shape of `MeromorphicNFAt` rather than `meromorphicNFAt_iff_analyticAt_or` — brittle against mathlib refactors.

### `lemma UpperHalfPlane.meromorphicNFOn_slash_zero_of_pos` (private)
- **Type**: `{f} (hf : MeromorphicNFOn (f ∘ ofComplex) {z | 0 < z.im}) {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) : MeromorphicNFOn ((f ∣[(0:ℤ)] g) ∘ ofComplex) {z | 0 < z.im}`
- **What**: positive-determinant case of the main theorem.
- **How**: at `z ∈ ℍ`, `comp_analyticAt_of_deriv_ne_zero` with the Möbius map (`analyticAt_smul`, `deriv_smul_ne_zero`), then `meromorphicNFAt_mul_iff_left` absorbs the nonzero constant `|det g|⁻¹` (`slash_apply`, `σ`, `zpow_zero`).
- **Hypotheses**: `det g > 0`.
- **Uses from project**: `MeromorphicNFAt.comp_analyticAt_of_deriv_ne_zero`
- **Used by**: `meromorphicNFOn_slash_zero`
- **Visibility**: private
- **Lines**: 54–72, proof body ≈ 15 lines
- **Notes**: mathlib ingredients `UpperHalfPlane/Manifold.lean:175,182`, `NormalForm.lean:257`.

### `lemma UpperHalfPlane.meromorphicNFOn_slash_zero_J` (private)
- **Type**: `{f} (hf : MeromorphicNFOn (f ∘ ofComplex) {z | 0 < z.im}) : MeromorphicNFOn ((f ∣[(0:ℤ)] J) ∘ ofComplex) {z | 0 < z.im}`
- **What**: the reflection `J` (`J • τ = -conj τ`) preserves normal form.
- **How**: `f ∘ ofComplex ∘ Neg.neg` is normal form at `conj z` (`comp_analyticAt_of_deriv_ne_zero` with `g = -·`), then `MeromorphicNFAt.conj_conj` and `meromorphicNFAt_congr` on a neighbourhood using `J_smul`, `slash_apply`, `σ`, `ofComplex_apply_of_im_pos`.
- **Hypotheses**: none.
- **Uses from project**: `MeromorphicNFAt.comp_analyticAt_of_deriv_ne_zero`, `MeromorphicNFAt.conj_conj`
- **Used by**: `meromorphicNFOn_slash_zero`
- **Visibility**: private
- **Lines**: 74–84, proof body ≈ 9 lines
- **Notes**: `J_smul` at `Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean:189`.

### `lemma UpperHalfPlane.meromorphicNFOn_slash_zero`
- **Type**: `{f} (hf : MeromorphicNFOn (f ∘ ofComplex) {z | 0 < z.im}) (g : GL (Fin 2) ℝ) : MeromorphicNFOn ((f ∣[(0:ℤ)] g) ∘ ofComplex) {z | 0 < z.im}`
- **What**: the weight-0 slash action of any real invertible matrix preserves normal form on ℍ.
- **How**: split on the sign of `det g`; negative case writes `g = J * (J * g)` (`J² = 1`) and uses `SlashAction.slash_mul` with the two private lemmas.
- **Hypotheses**: none.
- **Uses from project**: `meromorphicNFOn_slash_zero_of_pos`, `meromorphicNFOn_slash_zero_J`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 86–95, proof body ≈ 5 lines
- **Notes**: used by Cusps.lean:55.

## File Summary
- Total declarations: 6 (0 defs, 6 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none (`comp_analyticAt_of_deriv_ne_zero` used by 2)
- Unused declarations (not used by anything in this file): `meromorphicNFOn_slash_zero` (used by Cusps.lean)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations
### Mathlib API candidates
- `MeromorphicNFAt.comp_analyticAt_of_deriv_ne_zero` (22), `AnalyticAt.conj_conj` (32), `MeromorphicNFAt.conj_conj` (39): none exist in mathlib (grep-verified as noted per entry); all three are natural additions to `Mathlib/Analysis/Meromorphic/NormalForm.lean` / `Mathlib/Analysis/Analytic/…`.
- Mathlib has the mirror statement for meromorphy: `MeromorphicAt.comp_analyticAt` (`Mathlib/Analysis/Meromorphic/Basic.lean:438`); for `MDifferentiable` slash preservation see mathlib `SlashInvariantForm` files. No mathlib lemma states that the slash action preserves `MeromorphicNFOn`.
### Missing API / repeated patterns
- The result is not exploited where it matters: FieldAction.lean defines `precomp δ` on the field but never proves `toFun (precomp δ a) = fun τ ↦ toFun a (δ • τ)`, which is exactly `meromorphicNFOn_slash_zero` + `eqOn_toNF_of_meromorphicNFOn`. Add `MeromorphicField.toFun_precomp`.
- Spelling `{z : ℂ | 0 < z.im}` (lines 55, 75, 88) vs `upperHalfPlaneSet` elsewhere in the folder; the abbrev `upperHalfPlaneSet` (`Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean:262`) should be used uniformly.
### Junk candidates
- none.
### Moral duplicates within this batch
- `meromorphicNFOn_slash_zero_of_pos` (54) vs FieldAction.lean `precompHom` meromorphy obligation (102–112): both are "precompose by the Möbius map of a positive-determinant matrix"; the FieldAction version proves only `MeromorphicOn` via `MeromorphicAt.comp_analyticAt` while this file proves the stronger `MeromorphicNFOn`.
### Generalization notes
- `comp_analyticAt_of_deriv_ne_zero`: mathlib's `meromorphicOrderAt_comp_of_deriv_ne_zero` is stated over `𝕜` with `[CompleteSpace 𝕜] [CharZero 𝕜]` and `meromorphicNFAt_iff_analyticAt_or` for `f : 𝕜 → E`; the project lemma can be stated for `f : 𝕜 → E`, `g : 𝕜 → 𝕜`.
- `meromorphicNFOn_slash_zero` extends to weight `k`: `denom g τ ^ (-k)` is analytic and nonvanishing on ℍ, so `meromorphicNFAt_mul_iff_left` applies verbatim.
