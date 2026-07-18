# XYin/PhD/jFunction/jLevelN.lean
Project-internal imports: `XYin.PhD.jFunction.jfunction`

Note on provenance: `MDiff`, `upperHalfPlaneSet`, `cuspFunction`, and `UpperHalfPlane.differentiableOn_cuspFunction_ball` are Mathlib (`Mathlib.NumberTheory.ModularForms.QExpansion`, `Mathlib.Analysis.Complex.UpperHalfPlane.Basic`); `j`, `qj`, `E4`, `Delta`, `Δ_ne_zero`, `Delta_apply` and the `qj_*` lemmas are project declarations.

### `notation (local) ℍₒ`
- **Type**: `local notation "ℍₒ" => upperHalfPlaneSet`
- **What**: Local shorthand for Mathlib's set `{z : ℂ | 0 < z.im}`, the upper half-plane as a subset of ℂ.
- **How**: Plain notation macro; no content.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `jN_differentiableAt` (its binder `z : ℍₒ`)
- **Visibility**: scoped (local to this file)
- **Lines**: 28
- **Notes**: none

### `lemma natCast_mul_im_pos_aux`
- **Type**: `(N : ℕ) [NeZero N] {z : ℂ} (hz : 0 < z.im) : 0 < ((N : ℂ) * z).im`
- **What**: Multiplying a complex number of positive imaginary part by a positive natural number keeps the imaginary part positive, so `z ↦ N·z` maps ℍ to ℍ.
- **How**: `Complex.mul_im` expands `im(N·z) = N·im z` (the cross term vanishes since `N` is real), and positivity follows from `mul_pos` with `NeZero.pos N`.
- **Hypotheses**: `N ≠ 0` (as a `NeZero` instance); `0 < im z`.
- **Uses from project**: []
- **Used by**: `jN`, `natCast_smul_gamma0_comm_aux`, `qjN`, `natCast_mul_ofComplex_coe_aux`, `qjN_differentiableAt_aux`, `qjN_isBoundedAtImInfty_aux`, `jN_cuspFunction_eq_aux`, `jN_differentiableAt`
- **Visibility**: private
- **Lines**: 32–36, proof 3 lines
- **Notes**: none

### `def jN`
- **Type**: `(N : ℕ) [NeZero N] : ℍ → ℂ`
- **What**: The level-`N` transform of the analytic modular invariant: `jN N (τ) = j(N·τ)`. This is the second generator (besides `j`) of the function field of `X₀(N)`, central to the modular-equation program.
- **How**: Composes `j` with the ℍ-endomorphism `τ ↦ N·τ`, well-defined by `natCast_mul_im_pos_aux`.
- **Hypotheses**: `N ≠ 0`.
- **Uses from project**: [`j`, `natCast_mul_im_pos_aux`]
- **Used by**: `jN_slash_invariant`, `jN_cuspFunction_eq_aux`, `jN_cuspFunction_meromorphicAt`, `jN_differentiableAt`
- **Visibility**: public
- **Lines**: 38–40, def (2 lines)
- **Notes**: none

### `def gamma0Conjugate`
- **Type**: `(N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)`
- **What**: For `γ = (a b; c d) ∈ Γ₀(N)`, the conjugate matrix `(a Nb; c/N d)` — the image of `γ` under conjugation by `diag(N, 1)`, which is again integral and unimodular precisely because `N ∣ c`.
- **How**: The determinant proof extracts `N ∣ c` from the `Γ₀(N)` condition via `ZMod.intCast_zmod_eq_zero_iff_dvd` and `CongruenceSubgroup.Gamma0_mem`, cancels `N · (c/N) = c` with `Int.mul_ediv_cancel'`, and reduces `a·d − (N·b)·(c/N) = 1` to the original `det γ = 1` (`Matrix.det_fin_two`) by `linarith`.
- **Hypotheses**: `N ≠ 0`; `γ ∈ Γ₀(N)` (i.e. `N` divides the lower-left entry).
- **Uses from project**: []
- **Used by**: `natCast_smul_gamma0_comm_aux`
- **Visibility**: private
- **Lines**: 42–58, embedded proof 10 lines
- **Notes**: none

### `lemma natCast_smul_gamma0_comm_aux`
- **Type**: `(N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (hγ : γ ∈ Γ₀(N)) (z : ℍ) : ⟨N·(γ•z), _⟩ = gamma0Conjugate N γ hγ • ⟨N·z, _⟩` (as points of ℍ)
- **What**: The scaling map `τ ↦ N·τ` intertwines the Möbius action of `γ ∈ Γ₀(N)` with that of its `diag(N,1)`-conjugate: `N·(γ•z) = γ' • (N·z)` where `γ' = (a Nb; c/N d)`. This is the key equivariance behind Γ₀(N)-invariance of `jN`.
- **How**: After `ext`, both sides are Möbius quotients; the proof normalizes the ℤ → ℝ → ℂ coefficient casts (`Int.mul_ediv_cancel'` again supplies `N·(c/N) = c`, transported through `algebraMap ℤ ℝ` by `map_mul`), then the identity `(a(Nz)+Nb)/((c/N)(Nz)+d) = N·(az+b)/(cz+d)` is closed by `push_cast`, `mul_div_assoc`, and `ring`.
- **Hypotheses**: `N ≠ 0`; `γ ∈ Γ₀(N)`.
- **Uses from project**: [`gamma0Conjugate`, `natCast_mul_im_pos_aux`]
- **Used by**: `jN_slash_invariant`
- **Visibility**: private
- **Lines**: 60–84, proof 20 lines
- **Notes**: none

### `lemma jN_slash_invariant`
- **Type**: `(N : ℕ) [NeZero N] (γ : CongruenceSubgroup.Gamma0 N) : jN N ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = jN N`
- **What**: `jN N` is a weight-0 slash-invariant function for `Γ₀(N)`: `j(N·(γ•z)) = j(N·z)` for all `γ ∈ Γ₀(N)`. This is the standard first step toward `j` and `jN` generating the function field of `X₀(N)`.
- **How**: The weight-0 slash reduces to plain composition with the Möbius action; `natCast_smul_gamma0_comm_aux` rewrites `N·(γ•z)` as `γ' • (N·z)` for the conjugated matrix `γ' ∈ SL(2, ℤ)`, and the project's full modular invariance `j_modularGroup_smul` kills `γ'`.
- **Hypotheses**: `N ≠ 0`; `γ ∈ Γ₀(N)`.
- **Uses from project**: [`jN`, `natCast_smul_gamma0_comm_aux`, `j_modularGroup_smul`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 86–92, proof 5 lines
- **Notes**: none

### `def qjN`
- **Type**: `(N : ℕ) [NeZero N] : ℍ → ℂ`
- **What**: The regularized level-`N` transform `qjN N (τ) = qj(N·τ) = e^{2πiNτ}·j(N·τ)`, the pole-free companion of `jN N` (its cusp singularity is removed by the exponential factor).
- **How**: Composes the project's regularized `qj` with `τ ↦ N·τ` via `natCast_mul_im_pos_aux`.
- **Hypotheses**: `N ≠ 0`.
- **Uses from project**: [`qj`, `natCast_mul_im_pos_aux`]
- **Used by**: `qjN_periodic_aux`, `qjN_differentiableAt_aux`, `qjN_mdifferentiable_aux`, `qjN_isBoundedAtImInfty_aux`, `qjN_cuspFunction_analyticAt_aux`, `jN_cuspFunction_eq_aux`, `jN_cuspFunction_meromorphicAt`
- **Visibility**: private
- **Lines**: 94–95, def (2 lines)
- **Notes**: none

### `lemma natCast_mul_ofComplex_coe_aux`
- **Type**: `(N : ℕ) [NeZero N] {w : ℂ} (hw : 0 < w.im) : ⟨N·(ofComplex w), _⟩ = ofComplex (N·w)` (in ℍ)
- **What**: For `w` in the open upper half-plane, scaling by `N` commutes with Mathlib's section `ofComplex : ℂ → ℍ`; used to move between the ℍ-valued and ℂ-valued formulations of `qjN`.
- **How**: Both sides are compared via `UpperHalfPlane.ext` after evaluating `ofComplex` on points of positive imaginary part with `UpperHalfPlane.ofComplex_apply_of_im_pos` (applicable to `N·w` by `natCast_mul_im_pos_aux`).
- **Hypotheses**: `N ≠ 0`; `0 < im w`.
- **Uses from project**: [`natCast_mul_im_pos_aux`]
- **Used by**: `qjN_periodic_aux`, `qjN_differentiableAt_aux`
- **Visibility**: private
- **Lines**: 97–104, proof 4 lines
- **Notes**: none

### `lemma qjN_periodic_aux`
- **Type**: `(N : ℕ) [NeZero N] : Periodic (qjN N ∘ UpperHalfPlane.ofComplex) N`
- **What**: The planar extension of `qjN N` is periodic with period `N`: since `qj` has period 1, `qj(N(w+N)) = qj(Nw + N²) = qj(Nw)`.
- **How**: Derives period `N²` for `qj ∘ ofComplex` from the project lemma `qj_periodic` via `Periodic.nat_mul` with `N·N`; for `im w > 0` the substitution `w ↦ N·w` is transported through `ofComplex` by `natCast_mul_ofComplex_coe_aux`, and for `im w ≤ 0` both sides collapse to the junk value via `ofComplex_apply_of_im_nonpos`.
- **Hypotheses**: `N ≠ 0`.
- **Uses from project**: [`qjN`, `qj_periodic`, `natCast_mul_ofComplex_coe_aux`, `qj`]
- **Used by**: `qjN_cuspFunction_analyticAt_aux`
- **Visibility**: private
- **Lines**: 106–124, proof 17 lines
- **Notes**: proof splits on the sign of `im w` because `ofComplex` is a global section with junk values

### `lemma qjN_differentiableAt_aux`
- **Type**: `(N : ℕ) [NeZero N] {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℂ (qjN N ∘ UpperHalfPlane.ofComplex) z`
- **What**: The planar extension of `qjN N` is complex-differentiable at every point of the open upper half-plane.
- **How**: Chain rule: the project lemma `qj_differentiableAt_of_im_pos` gives differentiability of `qj ∘ ofComplex` at `N·z`, precomposition with the linear map `w ↦ N·w` is differentiable, and the composite agrees with `qjN N ∘ ofComplex` on the open set `{im > 0}` (via `natCast_mul_ofComplex_coe_aux`), so `DifferentiableAt.congr_of_eventuallyEq` transfers.
- **Hypotheses**: `N ≠ 0`; `0 < im z`.
- **Uses from project**: [`qjN`, `qj_differentiableAt_of_im_pos`, `natCast_mul_im_pos_aux`, `natCast_mul_ofComplex_coe_aux`]
- **Used by**: `qjN_mdifferentiable_aux`
- **Visibility**: private
- **Lines**: 126–135, proof 8 lines
- **Notes**: none

### `lemma qjN_mdifferentiable_aux`
- **Type**: `(N : ℕ) [NeZero N] : MDiff (qjN N)`
- **What**: `qjN N` is holomorphic on ℍ in the manifold sense (`MDifferentiable` for the upper half-plane's complex structure).
- **How**: Mathlib's `UpperHalfPlane.mdifferentiable_iff` reduces manifold differentiability to planar differentiability of the `ofComplex`-extension on `{im > 0}`, which is `qjN_differentiableAt_aux`.
- **Hypotheses**: `N ≠ 0`.
- **Uses from project**: [`qjN`, `qjN_differentiableAt_aux`]
- **Used by**: `qjN_cuspFunction_analyticAt_aux`
- **Visibility**: private
- **Lines**: 137–140, proof 3 lines
- **Notes**: none

### `lemma qjN_isBoundedAtImInfty_aux`
- **Type**: `(N : ℕ) [NeZero N] : IsBoundedAtImInfty (qjN N)`
- **What**: `qjN N` is bounded as `im τ → ∞`: since `im(Nτ) = N·im τ → ∞` and `qj` is bounded at i∞, so is its pullback.
- **How**: `IsBoundedAtImInfty.comp_tendsto` applied to the project's `qj_isBoundedAtImInfty` and the tendsto statement that `τ ↦ N·τ` pushes `atImInfty` into `atImInfty`; the latter is proved by unfolding `atImInfty` as `comap im atTop` and using `Filter.Tendsto.const_mul_atTop` with `N > 0`.
- **Hypotheses**: `N ≠ 0`.
- **Uses from project**: [`qjN`, `qj_isBoundedAtImInfty`, `natCast_mul_im_pos_aux`]
- **Used by**: `qjN_cuspFunction_analyticAt_aux`
- **Visibility**: private
- **Lines**: 142–157, proof 14 lines
- **Notes**: none

### `lemma qjN_cuspFunction_analyticAt_aux`
- **Type**: `(N : ℕ) [NeZero N] : AnalyticAt ℂ (cuspFunction N (qjN N)) 0`
- **What**: The period-`N` cusp function of `qjN N` (its descent to the `q`-disc, `q = e^{2πiτ/N}`) is analytic at `q = 0` — i.e. `qjN N` extends holomorphically over the cusp i∞.
- **How**: Mathlib's removable-singularity package `UpperHalfPlane.differentiableOn_cuspFunction_ball` applies given the three inputs periodicity (`qjN_periodic_aux`), holomorphy (`qjN_mdifferentiable_aux`), and boundedness at i∞ (`qjN_isBoundedAtImInfty_aux`); `DifferentiableOn.analyticAt` on the unit ball then yields analyticity at 0.
- **Hypotheses**: `N ≠ 0`.
- **Uses from project**: [`qjN`, `qjN_periodic_aux`, `qjN_mdifferentiable_aux`, `qjN_isBoundedAtImInfty_aux`]
- **Used by**: `jN_cuspFunction_meromorphicAt`
- **Visibility**: private
- **Lines**: 159–164, proof 4 lines
- **Notes**: none

### `lemma jN_cuspFunction_eq_aux`
- **Type**: `(N : ℕ) [NeZero N] {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) : cuspFunction N (jN N) q = q⁻¹ ^ (N * N) * cuspFunction N (qjN N) q`
- **What**: On the punctured unit `q`-disc, the cusp function of `jN N` factors as `q^{−N²}` times the (analytic) cusp function of `qjN N`. Mathematically: with `q = e^{2πiτ/N}`, the regularizing factor `e^{2πi(Nτ)}` equals `q^{N²}`, so `jN` has a pole of order exactly `N²` at the cusp.
- **How**: Sets `τ = invQParam N q` (well-defined in ℍ by `Periodic.im_invQParam_pos_of_norm_lt_one`), evaluates both cusp functions off 0 via `Periodic.cuspFunction_eq_of_nonzero`, and computes `exp(2πi·N·τ) = q^{N²}` from `Periodic.qParam_right_inv` together with `Complex.exp_nat_mul` after rewriting `2πi(Nτ) = N²·(2πiτ/N)`; unfolding the project definition `qj = e^{2πiτ}·j` then cancels `q^{−N²}·q^{N²} = 1`.
- **Hypotheses**: `N ≠ 0`; `q ≠ 0`; `‖q‖ < 1`.
- **Uses from project**: [`jN`, `qjN`, `qj`, `natCast_mul_im_pos_aux`]
- **Used by**: `jN_cuspFunction_meromorphicAt`
- **Visibility**: private
- **Lines**: 166–197, proof 29 lines (32-line declaration)
- **Notes**: longest proof in the file, just under 30 lines of proof body

### `lemma jN_cuspFunction_meromorphicAt`
- **Type**: `(N : ℕ) [NeZero N] : MeromorphicAt (cuspFunction N (jN N)) (0 : ℂ)`
- **What**: The cusp function of `jN N` is meromorphic at the origin of the `q`-disc — i.e. `jN N` is meromorphic at the cusp i∞, with pole order at most `N²`.
- **How**: `q ↦ q^{−N²}` is meromorphic at 0 (`MeromorphicAt.id.inv.pow`), `cuspFunction N (qjN N)` is analytic hence meromorphic at 0 (`qjN_cuspFunction_analyticAt_aux`), and their product agrees with `cuspFunction N (jN N)` on a punctured neighborhood by `jN_cuspFunction_eq_aux`; `MeromorphicAt.congr` transfers along this eventual equality (filtered on `‖q‖ < 1` and `q ≠ 0`).
- **Hypotheses**: `N ≠ 0`.
- **Uses from project**: [`jN`, `qjN`, `qjN_cuspFunction_analyticAt_aux`, `jN_cuspFunction_eq_aux`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 199–213, proof 13 lines
- **Notes**: none

### `lemma jN_differentiableAt`
- **Type**: `(N : ℕ) [NeZero N] {z : ℍₒ} : DifferentiableAt ℂ (jN N ∘ UpperHalfPlane.ofComplex) z`
- **What**: The planar extension of `jN N` is complex-differentiable at every point of the open upper half-plane (so `jN N` is holomorphic on ℍ).
- **How**: Builds differentiability of `j ∘ ofComplex = (E4)³/Δ` at `N·z` from `ModularFormClass.holo` for the project forms `E4` and `Delta` (transported to planar derivatives by `UpperHalfPlane.mdifferentiableAt_iff`), with denominator nonvanishing from `Δ_ne_zero` (via `Delta_apply`); chain rule with `w ↦ N·w` plus `congr_of_eventuallyEq` on the open set `{im > 0}` identifies the composite with `jN N ∘ ofComplex`.
- **Hypotheses**: `N ≠ 0`; `z` a point of the subtype `ℍₒ = {z : ℂ | 0 < im z}`.
- **Uses from project**: [`jN`, `natCast_mul_im_pos_aux`, `E4`, `Delta`, `Delta_apply`, `Δ_ne_zero`, `j`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 215–243, proof 26 lines
- **Notes**: none

### File Summary
- Total declarations: 16 (3 defs, 12 lemmas/theorems, 0 instances, 1 tactic/meta decls [local notation ℍₒ])
- Key API (used by 3+ others): [`natCast_mul_im_pos_aux` (used by 8), `qjN` (used by 7), `jN` (used by 4), `qjN_cuspFunction_analyticAt_aux`-cluster inputs each used once–twice]
- Unused declarations (not used by anything in this file): [`jN_slash_invariant`, `jN_cuspFunction_meromorphicAt`, `jN_differentiableAt`]
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [] (closest: `jN_cuspFunction_eq_aux`, 29-line proof / 32-line declaration)
