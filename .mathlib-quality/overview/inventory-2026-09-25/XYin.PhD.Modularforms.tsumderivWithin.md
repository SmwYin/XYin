# Inventory: XYin/PhD/Modularforms/tsumderivWithin.lean  (138 lines)

A hand-rolled "differentiate ∑' termwise on an open set given summable derivative majorants on compacts" theorem (`hasDerivAt_tsum_fun`) plus the explicit majorant construction for the exponential series exp(2πi n z) and its iterated derivatives. Defines the abbreviation `ℍ' := {z : ℂ | 0 < z.im}`. Only `ℍ'` and `upper_half_plane_isOpen` are used outside this file (in Summability/QExpansion.lean); the differentiation theorem and majorants are dead, and mathlib's `Mathlib/Topology/Algebra/InfiniteSum/TsumUniformlyOn.lean` + `EisensteinSeries/QExpansion.lean` supersede all of it.

## Declarations

### `abbrev ℍ'`
- **Type**: `Set ℂ := {z : ℂ | 0 < z.im}`
- **What**: The open upper half-plane as a subset of ℂ.
- **How**: set-builder abbreviation.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `upper_half_plane_isOpen`, `der_iter_eq_der_aux2`, `der_iter_eq_der2`, `der_iter_eq_der2'`, `iter_deriv_comp_bound3`, `iter_deriv_comp_bound2`; Summability/QExpansion.lean:27,50,52,56
- **Visibility**: public
- **Lines**: 30
- **Notes**: Exact duplicate of mathlib `UpperHalfPlane.upperHalfPlaneSet` (`Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean:262`, also an `abbrev`, with mathlib-local notation `ℍₒ`). Since both are abbrevs they are defeq, which is why Summability/QExpansion.lean can `change` between them (181).

### `lemma upper_half_plane_isOpen`
- **Type**: `IsOpen ℍ'`
- **What**: The upper half-plane is open in ℂ.
- **How**: `isOpen_lt` with `fun_prop`.
- **Hypotheses**: none.
- **Uses from project**: `ℍ'`
- **Used by**: `der_iter_eq_der_aux2` (83), `der_iter_eq_der2` (91); Summability/QExpansion.lean:164
- **Visibility**: public
- **Lines**: 32–34, proof body ≈ 1 line
- **Notes**: Exact duplicate of mathlib `UpperHalfPlane.isOpen_upperHalfPlaneSet` (`UpperHalfPlane/Basic.lean:266`). iteratedderivs.lean re-proves it inline three times as `isOpen_lt continuous_const continuous_im` (30, 55, 71).

### `theorem hasDerivAt_tsum_fun`
- **Type**: `{α} (f : α → ℂ → ℂ) {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n => f n y) (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖derivWithin (f n) s k‖ ≤ u n) (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) : HasDerivAt (fun z => ∑' n, f n z) (∑' n, derivWithin (fun z => f n z) s x) x`
- **What**: Termwise differentiation of a series of holomorphic functions on an open set, given a summable majorant for the derivatives on every compact subset (Weierstrass M-test + local uniform convergence of derivatives).
- **How**: mathlib `hasDerivAt_of_tendstoLocallyUniformlyOn` (`Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean:489`) applied to partial sums; local uniform convergence via `tendstoLocallyUniformlyOn_iff_forall_isCompact` (`Mathlib/Topology/UniformSpace/LocallyUniformConvergence.lean:267`) and `tendstoUniformlyOn_tsum` (`Mathlib/Analysis/Normed/Group/FunctionSeries.lean:33`); partial-sum derivatives by `HasDerivAt.fun_sum`.
- **Hypotheses**: s open, pointwise summability on s, compact-wise summable derivative bounds, termwise differentiability.
- **Uses from project**: []
- **Used by**: `derivWithin_tsum_fun'` (63), `hasDerivWithinAt_tsum_fun` (74)
- **Visibility**: public
- **Lines**: 36–55, proof body ≈ 13 lines
- **Notes**: This is the body of mathlib `derivWithin_tsum` (`Mathlib/Topology/Algebra/InfiniteSum/TsumUniformlyOn.lean:72`), whose `SummableLocallyUniformlyOn` hypothesis is produced from exactly this `hu` by `SummableLocallyUniformlyOn_of_locally_bounded` (:56). The global-majorant variant is `hasDerivAt_tsum_of_isPreconnected` (`Mathlib/Analysis/Calculus/SmoothSeries.lean:90`). Dead outside file.

### `theorem derivWithin_tsum_fun'`
- **Type**: same hypotheses; `derivWithin (fun z => ∑' n, f n z) s x = ∑' n, derivWithin (fun z => f n z) s x`
- **What**: `derivWithin` form of termwise differentiation.
- **How**: `(hasDerivAt_tsum_fun …).hasDerivWithinAt.derivWithin (hs.uniqueDiffWithinAt hx)`.
- **Hypotheses**: as above.
- **Uses from project**: `hasDerivAt_tsum_fun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 57–64, proof body ≈ 2 lines
- **Notes**: VERIFIED (scratch typecheck): this statement is exactly `derivWithin_tsum hs hx hf (SummableLocallyUniformlyOn_of_locally_bounded hs <fun K hK hKc ↦ …hu…>) (fun n r hr ↦ hf2 n ⟨r, hr⟩)`. Dead project-wide.

### `theorem hasDerivWithinAt_tsum_fun`
- **Type**: same hypotheses; `HasDerivWithinAt (fun z => ∑' n, f n z) (∑' n, derivWithin (fun z => f n z) s x) s x`
- **What**: `HasDerivWithinAt` form.
- **How**: `.hasDerivWithinAt`.
- **Hypotheses**: as above.
- **Uses from project**: `hasDerivAt_tsum_fun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 66–74, proof body ≈ 1 line
- **Notes**: Dead project-wide.

### `theorem der_iter_eq_der_aux2`
- **Type**: `(k n : ℕ) (r : ℍ') : DifferentiableAt ℂ (fun z => iteratedDerivWithin k (fun s => exp (2πi n s)) ℍ' z) ↑r`
- **What**: The k-th derivative of exp(2πi n ·) on ℍ is differentiable at each point.
- **How**: `DifferentiableOn.congr` from the closed form `(2πi n)^k exp(2πi n z)` (holomorphic by `fun_prop`) using `exp_iter_deriv_within` (iteratedderivs.lean:65), then `.differentiableAt` on the open set.
- **Hypotheses**: r ∈ ℍ.
- **Uses from project**: `ℍ'`, `exp_iter_deriv_within`, `upper_half_plane_isOpen`
- **Used by**: `der_iter_eq_der2` (90)
- **Visibility**: public
- **Lines**: 76–83, proof body ≈ 5 lines
- **Notes**: = mathlib `differentiableAt_iteratedDerivWithin_cexp` (`EisensteinSeries/QExpansion.lean:120`) modulo `exp_nat_mul` normal form.

### `theorem der_iter_eq_der2`
- **Type**: `(k n : ℕ) (r : ℍ') : deriv (iteratedDerivWithin k (fun s => exp (2πi n s)) ℍ') ↑r = derivWithin (iteratedDerivWithin k (…) ℍ') ℍ' ↑r`
- **What**: `deriv` = `derivWithin` on the open set for the iterated derivative.
- **How**: `DifferentiableAt.derivWithin` + `IsOpen.uniqueDiffWithinAt`.
- **Hypotheses**: r ∈ ℍ.
- **Uses from project**: `der_iter_eq_der_aux2`, `upper_half_plane_isOpen`, `ℍ'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 85–91, proof body ≈ 2 lines
- **Notes**: Mathlib `derivWithin_of_isOpen` (`Mathlib/Analysis/Calculus/Deriv/Basic.lean:513`) gives this without any differentiability hypothesis. Dead project-wide.

### `theorem der_iter_eq_der2'`
- **Type**: `(k n : ℕ) (r : ℍ') : derivWithin (iteratedDerivWithin k (fun s => exp (2πi n s)) ℍ') ℍ' ↑r = iteratedDerivWithin (k + 1) (…) ℍ' ↑r`
- **What**: derivWithin of the k-th iterated derivative is the (k+1)-st.
- **How**: `rw [iteratedDerivWithin_succ]`.
- **Hypotheses**: none.
- **Uses from project**: `ℍ'`
- **Used by**: `iter_deriv_comp_bound2` (137)
- **Visibility**: public
- **Lines**: 93–98, proof body ≈ 1 line
- **Notes**: Exact instance of mathlib `iteratedDerivWithin_succ` (`Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:186`) symm.

### `def cts_exp_two_pi_n`
- **Type**: `(K : Set ℂ) : ContinuousMap K ℂ` with `toFun r := exp (2πi r)`
- **What**: The map r ↦ exp(2πi r) bundled as a continuous map on K (only so that `‖·‖` gives its sup-norm on compact K).
- **How**: structure literal; `continuous_toFun` auto-filled.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `iter_deriv_comp_bound3` (109, 112, 124)
- **Visibility**: public
- **Lines**: 100–101
- **Notes**: `noncomputable`. Mathlib does the same trick inline with `BoundedContinuousFunction.mkOfCompact ⟨fun r : K ↦ cexp (2πI r / p), by fun_prop⟩` in `summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp` (`EisensteinSeries/QExpansion.lean:87–89`); alternatively `IsCompact.exists_isMaxOn` (`Mathlib/Topology/Order/Compact.lean:246`). No `_apply` simp lemma. Dead outside its one consumer.

### `theorem iter_deriv_comp_bound3`
- **Type**: `(K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) : ∃ u : ℕ → ℝ, Summable u ∧ ∀ (n : ℕ) (r : K), (2 * |π| * n) ^ k * ‖exp (2πi n r)‖ ≤ u n`
- **What**: On a compact K ⊂ ℍ, (2π n)^k |q^n| has the summable majorant (2π n)^k ρ^n where ρ = sup_K |q| < 1.
- **How**: `ContinuousMap.norm_lt_iff` with `[CompactSpace K]` and `exp_upperHalfPlane_lt_one` give ρ < 1; summability by `summable_norm_pow_mul_geometric_of_norm_lt_one` (`Mathlib/Analysis/SpecificLimits/Normed.lean:423`); the bound by `ContinuousMap.norm_coe_le_norm` and `pow_le_pow_left₀`.
- **Hypotheses**: K compact inside ℍ.
- **Uses from project**: `cts_exp_two_pi_n`, `exp_upperHalfPlane_lt_one` (exp_lems.lean:14), `ℍ'`
- **Used by**: `iter_deriv_comp_bound2` (135)
- **Visibility**: public
- **Lines**: 103–127, proof body ≈ 20 lines
- **Notes**: = the body of mathlib `summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp` (`EisensteinSeries/QExpansion.lean:80`), specialised by `summableLocallyUniformlyOn_iteratedDerivWithin_cexp k` (:110). Hand-rolled `∃ u, Summable u ∧ ∀ n r, ‖…‖ ≤ u n` majorant.

### `theorem iter_deriv_comp_bound2`
- **Type**: `(K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) : ∃ u : ℕ → ℝ, Summable u ∧ ∀ (n : ℕ) (r : K), ‖derivWithin (iteratedDerivWithin k (fun s => exp (2πi n s)) ℍ') ℍ' r‖ ≤ u n`
- **What**: Summable majorant for the (k+1)-st termwise derivatives of the q-series on compacts — the `hu` input of `hasDerivAt_tsum_fun`.
- **How**: `der_iter_eq_der2'` + `exp_iter_deriv_within (k+1)` reduce to `iter_deriv_comp_bound3 K _ _ (k+1)`.
- **Hypotheses**: K compact inside ℍ.
- **Uses from project**: `iter_deriv_comp_bound3`, `der_iter_eq_der2'`, `exp_iter_deriv_within`, `ℍ'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 129–138, proof body ≈ 4 lines
- **Notes**: Dead project-wide; mathlib `summableLocallyUniformlyOn_iteratedDerivWithin_cexp (k+1)`.

## File Summary
- Total declarations: 11 (1 def, 1 abbrev, 9 lemmas/theorems, 0 instances)
- Key API (used by 3+ others in the file): `ℍ'` (6 in-file users), `upper_half_plane_isOpen` (2 in-file + 1 external), `cts_exp_two_pi_n` (3 uses in one proof)
- Unused declarations (not used by anything in this file): `derivWithin_tsum_fun'`, `hasDerivWithinAt_tsum_fun`, `der_iter_eq_der2`, `iter_deriv_comp_bound2` — and project-wide only `ℍ'` and `upper_half_plane_isOpen` are used outside this file (Summability/QExpansion.lean)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (`iter_deriv_comp_bound3` 20)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `ℍ'` (30) = `UpperHalfPlane.upperHalfPlaneSet` (`Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean:262`); `upper_half_plane_isOpen` (32) = `isOpen_upperHalfPlaneSet` (:266). Both exact.
- `hasDerivAt_tsum_fun`/`derivWithin_tsum_fun'`/`hasDerivWithinAt_tsum_fun` (36–74) = `derivWithin_tsum` (`Mathlib/Topology/Algebra/InfiniteSum/TsumUniformlyOn.lean:72`) ∘ `SummableLocallyUniformlyOn_of_locally_bounded` (:56) — the `derivWithin` form typechecks verbatim (scratch check). `iteratedDerivWithin_tsum` (:93) is the iterated version the project reaches for in Summability/QExpansion.lean:183 anyway.
- `der_iter_eq_der_aux2` (76) = `differentiableAt_iteratedDerivWithin_cexp` (`EisensteinSeries/QExpansion.lean:120`); `iter_deriv_comp_bound3`/`bound2` (103/129) = `summableLocallyUniformlyOn_iteratedDerivWithin_cexp` (:110) / `…_smul_cexp` (:80).
- `der_iter_eq_der2` (85) = `derivWithin_of_isOpen` (`Mathlib/Analysis/Calculus/Deriv/Basic.lean:513`); `der_iter_eq_der2'` (93) = `iteratedDerivWithin_succ` (`IteratedDeriv/Defs.lean:186`).
- `cts_exp_two_pi_n` (100): replace by `BoundedContinuousFunction.mkOfCompact` (as mathlib does at `EisensteinSeries/QExpansion.lean:87`) or `IsCompact.exists_isMaxOn`.
- Hand-rolled uniform-bound patterns: the `∃ u : α → ℝ, Summable u ∧ ∀ n (k : K), ‖…‖ ≤ u n` shape at 39–40, 59–60, 70–71, 104–107, 130–134 is `SummableLocallyUniformlyOn` (TsumUniformlyOn.lean:45–60) in disguise; the sup-norm-on-compact trick at 108–113 is `TendstoUniformlyOn`/`mkOfCompact` material.
### Missing API / repeated patterns
- The hypothesis block `(hs) (x) (hx) (hf) (hu) (hf2)` is copy-pasted three times (36–41, 57–61, 66–72); a `structure`/`SummableLocallyUniformlyOn` hypothesis would remove it.
- `heq : exp(2πi n z) = exp(2πi z)^n` at 118–122 duplicates Basic.lean `exp_aux` (171) — the project has the lemma and doesn't use it.
### Junk candidates
- Dead project-wide: `hasDerivAt_tsum_fun`, `derivWithin_tsum_fun'`, `hasDerivWithinAt_tsum_fun`, `der_iter_eq_der_aux2`, `der_iter_eq_der2`, `der_iter_eq_der2'`, `cts_exp_two_pi_n`, `iter_deriv_comp_bound3`, `iter_deriv_comp_bound2` — 9 of 11. After replacing `ℍ'`/`upper_half_plane_isOpen` by the mathlib names in Summability/QExpansion.lean (4 + 1 sites), the whole file can be deleted.
- Names `der_iter_eq_der_aux2`, `der_iter_eq_der2`, `der_iter_eq_der2'`, `iter_deriv_comp_bound3/2` (numbered leftovers of an older sequence).
- Imports `Mathlib.Topology.Algebra.Module.ModuleTopology` (10) and `Mathlib.Topology.ContinuousMap.Compact` (11) — the former appears unused.
### Moral duplicates within this batch
- `iter_deriv_comp_bound2` (129) vs Summability/QExpansion.lean `aut_bound_on_comp` (120): same "majorant on compact K for derivWithin ∘ iteratedDerivWithin" shape, one for exp-series one for cot-series.
- `der_iter_eq_der_aux2` (76) vs Summability/QExpansion.lean `diff_at_aux` (158): same `DifferentiableOn.congr (closed form) |>.differentiableAt` skeleton.
- `upper_half_plane_isOpen` vs the inline `isOpen_lt continuous_const continuous_im` in iteratedderivs.lean:30,55,71.
### Generalization notes
- `hasDerivAt_tsum_fun` family: stated for `ℂ → ℂ`; the proof uses nothing specific to ℂ and mathlib's `derivWithin_tsum` is stated for `𝕜 → F` with `[IsRCLikeNormedField 𝕜] [NormedSpace 𝕜 F]`.
- `iter_deriv_comp_bound3`: only `sup_K ‖exp(2πi ·)‖ < 1` is used; holds for any compact K on which `Im > 0` (which is what `hK1` says) — no generalisation beyond mathlib's.
