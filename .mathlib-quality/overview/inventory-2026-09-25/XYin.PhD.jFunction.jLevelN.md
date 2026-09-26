# Inventory: XYin/PhD/jFunction/jLevelN.lean  (193 lines)

The level-N transform `jN N : τ ↦ j(Nτ)`: Γ₀(N)-invariance (via the explicit conjugate `diag(N,1) γ diag(N,1)⁻¹`), meromorphy of its cusp function at 0 (with the period-N cusp parameter), and holomorphy on ℍ. Consumed only by `Cox/ModularFunction/LevelJ.lean` (`levelJ N := jN N`, `jN_slash_invariant`, `jN_differentiableAt`).

## Declarations

### `local notation "ℍₒ"`
- **Type**: notation for `upperHalfPlaneSet`
- **What**: the open upper half-plane as a set. **How**: `local notation`. **Hypotheses**: none. **Uses from project**: []. **Used by**: jN_differentiableAt. **Visibility**: local. **Lines**: 28. **Notes**: mathlib uses the same local notation (`Analysis/Complex/UpperHalfPlane/Basic.lean:264`).

### `private lemma natCast_mul_im_pos_aux`
- **Type**: `(N : ℕ) [NeZero N] {z : ℂ} (hz : 0 < z.im) : 0 < ((N : ℂ) * z).im`
- **What**: Scaling by a positive natural preserves the upper half-plane.
- **How**: `Complex.mul_im` + `mul_pos`.
- **Hypotheses**: N ≠ 0, im z > 0.
- **Uses from project**: []
- **Used by**: jN, natCast_smul_gamma0_comm_aux, qjN, natCast_mul_ofComplex_coe_aux, qjN_differentiableAt_aux, jN_cuspFunction_eq_aux, jN_differentiableAt
- **Visibility**: private
- **Lines**: 32–34
- **Notes**: mathlib `UpperHalfPlane.posRealAction` (`Analysis/Complex/UpperHalfPlane/Basic.lean:197`) with `coe_pos_real_smul` (:206), `pos_real_im` (:210) gives `x • z : ℍ` for positive real x; would delete this lemma, `natCast_mul_ofComplex_coe_aux`, and LevelJ.lean:29 `natScaleUpperHalfPlane` (third copy).

### `def jN`
- **Type**: `(N : ℕ) [NeZero N] : ℍ → ℂ` (:= `fun z ↦ j ⟨N * z, _⟩`)
- **What**: τ ↦ j(Nτ).
- **How**: definition.
- **Hypotheses**: N ≠ 0 (instance).
- **Uses from project**: [j (jfunction.lean:51), natCast_mul_im_pos_aux]
- **Used by**: jN_slash_invariant, jN_cuspFunction_eq_aux, jN_cuspFunction_meromorphicAt, jN_differentiableAt
- **Visibility**: public
- **Lines**: 37–38
- **Notes**: `[NeZero N]` forces LevelJ.lean:26 to write `@jN (N : ℕ) ⟨PNat.ne_zero N⟩`; `N : ℕ+` would match the consumer. 2 external uses.

### `private def gamma0Conjugate`
- **Type**: `(N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)` (:= `!![a, N b; c/N, d]`)
- **What**: The conjugate `diag(N,1)·γ·diag(N,1)⁻¹`, again in SL₂(ℤ) because N ∣ c.
- **How**: determinant `ad − (Nb)(c/N) = ad − bc = 1` using `Int.mul_ediv_cancel'` from `N ∣ c` (mathlib `CongruenceSubgroup.Gamma0_mem`, `ZMod.intCast_zmod_eq_zero_iff_dvd`), `Matrix.det_fin_two`, `linarith`.
- **Hypotheses**: γ ∈ Γ₀(N).
- **Uses from project**: []
- **Used by**: natCast_smul_gamma0_comm_aux, jN_slash_invariant
- **Visibility**: private
- **Lines**: 40–56, body 11 lines
- **Notes**: no mathlib Γ₀(N) conjugation API (grep `Gamma0` in `CongruenceSubgroups.lean`: only `Gamma0_mem`, `Gamma0Map`, `Gamma1_*`).

### `private lemma natCast_smul_gamma0_comm_aux`
- **Type**: `(N) [NeZero N] (γ) (hγ) (z : ℍ) : ⟨N * (γ • z), _⟩ = gamma0Conjugate N γ hγ • ⟨N * z, _⟩`
- **What**: Scaling by N intertwines γ and its conjugate: N·(γz) = γ'·(Nz).
- **How**: Möbius formula `coe_specialLinearGroup_apply` on both sides; key identity `(c/N)(Nz) = cz` from `Int.mul_ediv_cancel'`, pushed through `algebraMap ℤ ℝ` and `ℝ → ℂ` casts, then `mul_div_assoc`, `ring`.
- **Hypotheses**: γ ∈ Γ₀(N).
- **Uses from project**: [natCast_mul_im_pos_aux, gamma0Conjugate]
- **Used by**: jN_slash_invariant
- **Visibility**: private
- **Lines**: 58–82, body 20 lines
- **Notes**: heavy cast juggling (`hR`, `hC`, `push_cast`). With `N • z` as the action of `!![N,0;0,1] ∈ GL(2,ℝ)⁺` this is `mul_smul` + `smul_left_cancel`.

### `lemma jN_slash_invariant`
- **Type**: `(N : ℕ) [NeZero N] (γ : CongruenceSubgroup.Gamma0 N) : jN N ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = jN N`
- **What**: j(Nτ) is a weight-0 modular function for Γ₀(N).
- **How**: `SL_slash_apply` with weight 0, the intertwining lemma, then SL₂(ℤ)-invariance of j (`j_modularGroup_smul`).
- **Hypotheses**: γ ∈ Γ₀(N).
- **Uses from project**: [jN, natCast_smul_gamma0_comm_aux, j_modularGroup_smul (jfunction.lean:76)]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 85–90, body 4 lines
- **Notes**: 1 external use (LevelJ.lean:319).

### `private def qjN`
- **Type**: `(N : ℕ) [NeZero N] : ℍ → ℂ` (:= `fun z ↦ qj ⟨N * z, _⟩`)
- **What**: τ ↦ (q·j)(Nτ), the regularized transform.
- **How**: definition.
- **Hypotheses**: N ≠ 0.
- **Uses from project**: [qj (jfunction.lean:239), natCast_mul_im_pos_aux]
- **Used by**: qjN_periodic_aux, qjN_differentiableAt_aux, qjN_mdifferentiable_aux, qjN_isBoundedAtImInfty_aux, qjN_cuspFunction_analyticAt_aux, jN_cuspFunction_eq_aux, jN_cuspFunction_meromorphicAt
- **Visibility**: private
- **Lines**: 92–93
- **Notes**: —

### `private lemma natCast_mul_ofComplex_coe_aux`
- **Type**: `(N) [NeZero N] {w : ℂ} (hw : 0 < w.im) : ⟨N * (ofComplex w), _⟩ = ofComplex (N * w)`
- **What**: Scaling commutes with the `ofComplex` retraction on the open half-plane.
- **How**: `UpperHalfPlane.ext`, mathlib `ofComplex_apply_of_im_pos` (UpperHalfPlane/Topology.lean:162).
- **Hypotheses**: im w > 0.
- **Uses from project**: [natCast_mul_im_pos_aux]
- **Used by**: qjN_periodic_aux, qjN_differentiableAt_aux, jN_differentiableAt
- **Visibility**: private
- **Lines**: 95–101
- **Notes**: —

### `private lemma qjN_periodic_aux`
- **Type**: `(N) [NeZero N] : Periodic (qjN N ∘ ofComplex) N`
- **What**: (q·j)(Nτ) has period N in τ.
- **How**: `qj_periodic.nat_mul (N*N)` gives period N² for q·j; shifting τ by N shifts Nτ by N². Case split on im w as in `qj_periodic`.
- **Hypotheses**: none
- **Uses from project**: [qjN, qj_periodic (jfunction.lean:337), natCast_mul_ofComplex_coe_aux]
- **Used by**: qjN_cuspFunction_analyticAt_aux
- **Visibility**: private
- **Lines**: 103–114, body 11 lines
- **Notes**: Mathematically qjN has period **1** (j(Nτ+N) = j(Nτ)); proving only period N forces the period-N cusp parameter and the exponent `N*N` in `jN_cuspFunction_eq_aux`. Proving period 1 via `qj_periodic.nat_mul N` would make `cuspFunction 1 (jN N)` meromorphic with pole order N. Duplicates the `qj_periodic` skeleton.

### `private lemma qjN_differentiableAt_aux`
- **Type**: `(N) [NeZero N] {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℂ (qjN N ∘ ofComplex) z`
- **What**: Holomorphy of the extension on the open half-plane.
- **How**: chain rule: `qj_differentiableAt_of_im_pos` at Nz composed with `w ↦ N w`, `congr_of_eventuallyEq` on the open set `{im > 0}` (`isOpen_lt`).
- **Hypotheses**: im z > 0.
- **Uses from project**: [qjN, natCast_mul_im_pos_aux, qj_differentiableAt_of_im_pos (jfunction.lean:352), natCast_mul_ofComplex_coe_aux]
- **Used by**: qjN_mdifferentiable_aux
- **Visibility**: private
- **Lines**: 116–125, body 8 lines
- **Notes**: same skeleton as jN_differentiableAt (184).

### `private lemma qjN_mdifferentiable_aux`
- **Type**: `(N) [NeZero N] : MDiff (qjN N)`
- **What**: qjN is holomorphic on ℍ.
- **How**: mathlib `UpperHalfPlane.mdifferentiable_iff`.
- **Hypotheses**: none
- **Uses from project**: [qjN, qjN_differentiableAt_aux]
- **Used by**: qjN_cuspFunction_analyticAt_aux
- **Visibility**: private
- **Lines**: 127–129
- **Notes**: —

### `private lemma qjN_isBoundedAtImInfty_aux`
- **Type**: `(N) [NeZero N] : IsBoundedAtImInfty (qjN N)`
- **What**: qjN bounded at i∞.
- **How**: `qj_isBoundedAtImInfty.comp_tendsto` with `im(Nz) = N·im z → ∞` (`Filter.Tendsto.const_mul_atTop`, `tendsto_comap`).
- **Hypotheses**: none
- **Uses from project**: [qjN, qj_isBoundedAtImInfty (jfunction.lean:372)]
- **Used by**: qjN_cuspFunction_analyticAt_aux
- **Visibility**: private
- **Lines**: 131–138, body 7 lines
- **Notes**: —

### `private lemma qjN_cuspFunction_analyticAt_aux`
- **Type**: `(N) [NeZero N] : AnalyticAt ℂ (cuspFunction N (qjN N)) 0`
- **What**: The period-N cusp function of qjN is analytic at 0.
- **How**: mathlib `differentiableOn_cuspFunction_ball` (QExpansion.lean:95) + `.analyticAt`.
- **Hypotheses**: none
- **Uses from project**: [qjN, qjN_periodic_aux, qjN_mdifferentiable_aux, qjN_isBoundedAtImInfty_aux]
- **Used by**: jN_cuspFunction_meromorphicAt
- **Visibility**: private
- **Lines**: 140–144
- **Notes**: = mathlib `UpperHalfPlane.analyticAt_cuspFunction_zero` (`QExpansion.lean:101`) verbatim.

### `private lemma jN_cuspFunction_eq_aux`
- **Type**: `(N) [NeZero N] {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) : cuspFunction N (jN N) q = q⁻¹ ^ (N * N) * cuspFunction N (qjN N) q`
- **What**: On the punctured disc, cusp(jN) = q^{−N²} · cusp(qjN) (since e^{2πi Nτ} = q_N^{N²}).
- **How**: `key : ∀ f, cuspFunction N f q = f τ` for τ = invQParam N q (`Periodic.cuspFunction_eq_of_nonzero`, `ofComplex_apply_of_im_pos`); `cexp(2πi·N·τ) = q^{N²}` by `Complex.exp_nat_mul` + `field_simp` + `Periodic.qParam_right_inv`; cancel with `inv_mul_cancel₀`.
- **Hypotheses**: 0 < |q| < 1.
- **Uses from project**: [jN, qjN, qj, natCast_mul_im_pos_aux]
- **Used by**: jN_cuspFunction_meromorphicAt
- **Visibility**: private
- **Lines**: 146–169, body 22 lines
- **Notes**: `key` is the third copy of the "cusp function at nonzero q" gadget (jfunction.lean:152–158, LaurentQExpansion.lean:330).

### `lemma jN_cuspFunction_meromorphicAt`
- **Type**: `(N : ℕ) [NeZero N] : MeromorphicAt (cuspFunction N (jN N)) (0 : ℂ)`
- **What**: j(Nτ) is meromorphic at the cusp ∞ (in the period-N parameter).
- **How**: `q⁻¹^{N²}` meromorphic (`MeromorphicAt.id.inv.pow`), times analytic, `MeromorphicAt.congr` on the punctured nbhd via jN_cuspFunction_eq_aux.
- **Hypotheses**: none
- **Uses from project**: [jN, qjN_cuspFunction_analyticAt_aux, jN_cuspFunction_eq_aux]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 172–181, body 9 lines
- **Notes**: **0 uses project-wide**: LevelJ.lean re-proves meromorphy at every cusp independently (`affine_j_cuspFunction_meromorphicAt` :275, `levelJ_meromorphicAt_cusp` :299). Junk candidate, or LevelJ should reuse it for the cusp ∞. `hnorm` (177–179) duplicates jfunction.lean:444–446.

### `lemma jN_differentiableAt`
- **Type**: `(N : ℕ) [NeZero N] {z : ℍₒ} : DifferentiableAt ℂ (jN N ∘ ofComplex) z`
- **What**: Holomorphy of the extension of j(Nτ) on the open half-plane.
- **How**: `mdifferentiableAt_iff.mp (j_mdifferentiable _)` composed with `w ↦ N w`, `congr_of_eventuallyEq` on `{im>0}`.
- **Hypotheses**: z ∈ ℍₒ.
- **Uses from project**: [jN, natCast_mul_im_pos_aux, j_mdifferentiable (jfunction.lean:54), natCast_mul_ofComplex_coe_aux]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 184–193, body 8 lines
- **Notes**: 1 external use (LevelJ.lean:310). Same skeleton as qjN_differentiableAt_aux; no `jN_mdifferentiable : MDiff (jN N)` (LevelJ.lean:308 builds it).

## File Summary
- Total declarations: 15 (3 defs: jN, gamma0Conjugate, qjN; 12 lemmas; 0 instances; 1 local notation)
- Key API (used by 3+ others in the file): natCast_mul_im_pos_aux (7), qjN (7), jN (4), natCast_mul_ofComplex_coe_aux (3)
- Unused declarations (not used by anything in this file): jN_slash_invariant (1 ext), jN_cuspFunction_meromorphicAt (0 ext — unused project-wide), jN_differentiableAt (1 ext)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest jN_cuspFunction_eq_aux 22 lines, natCast_smul_gamma0_comm_aux 20 lines)

## Observations
### Mathlib API candidates
- `natCast_mul_im_pos_aux` (32), `natCast_mul_ofComplex_coe_aux` (95) and the subtype constructions `⟨N * z, _⟩` (38, 60–62, 93, 156): mathlib `UpperHalfPlane.posRealAction` (`Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean:197`, `coe_pos_real_smul` :206, `pos_real_im` :210) — define `jN N z := j ((⟨N, _⟩ : {x : ℝ // 0 < x}) • z)`.
- `qjN_cuspFunction_analyticAt_aux` (140) = `UpperHalfPlane.analyticAt_cuspFunction_zero` (`QExpansion.lean:101`).
- `gamma0Conjugate`/`natCast_smul_gamma0_comm_aux` (40–82): no mathlib Γ₀(N)-conjugation; searched `Gamma0`, `!![N,0;0,1]`, `diagonal` in `Mathlib/NumberTheory/ModularForms/` — nothing. Hand-rolled cast algebra (69–82) is the main cost.
### Missing API / repeated patterns
- Periodicity case split (103–114) = jfunction.lean:337–349 → lemma `periodic_comp_ofComplex_of_vadd`.
- Chain-rule-then-`congr_of_eventuallyEq` pattern (116–125 and 184–193) → lemma `differentiableAt_comp_ofComplex_natCast_mul`.
- "cusp function at nonzero q" `key` (151–154) → promote `cuspFunction_eq_of_norm_lt_one` to LaurentQExpansion/mathlib.
- `hnorm` (177–179) = jfunction.lean:444–446.
- Missing: `jN_mdifferentiable`, `jN_periodic` (period 1), `jN_cuspFunction_meromorphicAt` with the natural period-1 parameter.
### Junk candidates
- `jN_cuspFunction_meromorphicAt` (172–181): 0 uses project-wide; LevelJ.lean has its own cusp analysis.
- `local notation "ℍₒ"` used once (184).
### Moral duplicates within this batch
- `qjN_*` lemmas (103–144) are the `qj_*` lemmas of jfunction.lean composed with `z ↦ N z`; `jN_differentiableAt` ↔ `qjN_differentiableAt_aux`.
- `natScaleUpperHalfPlane` (Cox/ModularFunction/LevelJ.lean:29, private) duplicates the `⟨N * z, natCast_mul_im_pos_aux …⟩` construction.
### Generalization notes
- Everything is stated for `N : ℕ` with `[NeZero N]`; the proofs use only `0 < (N : ℝ)` — a positive real (or `ℕ+`, as LevelJ uses) suffices for jN, qjN, and the analytic lemmas; only `gamma0Conjugate` needs N ∈ ℕ.
- `qjN_periodic_aux` proves period N where period 1 holds; the weaker statement propagates the exponent N² (146–147).
