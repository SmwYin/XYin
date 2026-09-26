# Inventory: XYin/PhD/Cox/LatticeJ.lean  (632 lines)

Lattice `j`-invariant (Cox Thm 10.9, Thm 11.2(ii)(iii)): defines scaling `ℂˣ • PeriodPair` (mathlib's `PeriodPair`, `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:60`), homothety, `PeriodPair.discriminant = g₂³ − 27g₃²` and `PeriodPair.j = 1728 g₂³/Δ`; proves `g₂`, `g₃`, `Δ`, `j` have weights 4, 6, 12, 0 under scaling and depend only on the lattice; identifies the normalised pair `[1, τ]` with the analytic `j` via `E₄`, `E₆` (`g₂ = 4π⁴/3·E₄`, `g₃ = 8π⁶/27·E₆`); proves `Δ ≠ 0`, `j L = j M ↔ L, M homothetic` (using `lattice_eq_of_g₂_eq_of_g₃_eq` from `XYin/uniqueness.lean`), homothety of `[1,z],[1,w]` ↔ `SL₂(ℤ)`-orbit, hence `j τ = j τ' ↔ ∃ γ, γ•τ = τ'`, and surjectivity of `j` (weight-0 cusp form `1/(j − c)` must vanish).

## Declarations

### `protected def PeriodPair.smul`
- **Type**: `(a : ℂˣ) (L : PeriodPair) : PeriodPair` with `ω₁ := a * L.ω₁`, `ω₂ := a * L.ω₂`
- **What**: scale both periods by a nonzero complex number; ℝ-linear independence is preserved.
- **How**: `LinearIndependent.pair_iff` (mathlib `LinearAlgebra/LinearIndependent/Lemmas.lean:270`) transported through `mul_eq_zero.resolve_left a.ne_zero`.
- **Hypotheses**: `a` a unit.
- **Uses from project**: []
- **Used by**: `instance SMul ℂˣ PeriodPair`
- **Visibility**: protected
- **Lines**: 33–42
- **Notes**: mathlib `PeriodPair` has no scaling action (grep `SMul`/`smul` in `Elliptic/Weierstrass.lean` → none).

### `instance : SMul ℂˣ PeriodPair`
- **Type**: `SMul ℂˣ PeriodPair := ⟨PeriodPair.smul⟩`
- **What**: notation `a • L` for period scaling.
- **How**: wraps `PeriodPair.smul`.
- **Hypotheses**: none.
- **Uses from project**: `PeriodPair.smul`
- **Used by**: everything below using `a • L`; `CyclicSublattice.lean` (`scale`, `dual_*`), `Classification.lean:264–320`
- **Visibility**: public
- **Lines**: 44
- **Notes**: no `MulAction` instance (`one_smul`, `mul_smul` absent), no `smul_lattice` simp lemma.

### `theorem PeriodPair.smul_ω₁`
- **Type**: `(a : ℂˣ) (L : PeriodPair) : (a • L).ω₁ = a * L.ω₁`
- **What**: first period of the scaled pair.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `instance SMul ℂˣ PeriodPair`
- **Used by**: `mem_smul_lattice` (64, via simp)
- **Visibility**: public, `@[simp]`
- **Lines**: 46
- **Notes**: also fires in `Classification.lean:270` (`simp [u, UpperHalfPlane.periodPair]`).

### `theorem PeriodPair.smul_ω₂`
- **Type**: `(a : ℂˣ) (L : PeriodPair) : (a • L).ω₂ = a * L.ω₂`
- **What**: second period of the scaled pair.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `instance SMul ℂˣ PeriodPair`
- **Used by**: `mem_smul_lattice` (64)
- **Visibility**: public, `@[simp]`
- **Lines**: 48
- **Notes**: external explicit use `Classification.lean:273`.

### `def PeriodPair.Homothetic`
- **Type**: `(L M : PeriodPair) : Prop := ∃ a : ℂˣ, (a • L).lattice = M.lattice`
- **What**: `L` and `M` are homothetic: some nonzero scalar carries the lattice of `L` onto that of `M`.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: `instance SMul ℂˣ PeriodPair`
- **Used by**: `j_eq_of_homothetic`, `homothetic_of_j_eq_*_aux` (3), `homothetic_of_j_eq`, `j_eq_iff_homothetic`, `exists_homothetic_periodPair`, `exists_sl2_smul_eq_of_periodPair_homothetic_aux`, `periodPair_homothetic_of_sl2_smul_aux`, `periodPair_homothetic_iff_exists_sl2_smul_eq`
- **Visibility**: public
- **Lines**: 52–53
- **Notes**: no `refl`/`symm`/`trans` (equivalence-relation) lemmas; mathlib has no lattice-homothety notion (`grep Homothet` → only `ContinuousLinearMap.ofHomothety`).

### `def PeriodPair.discriminant`
- **Type**: `(L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2`
- **What**: Cox's lattice discriminant `Δ(L)`.
- **How**: definition on mathlib's `PeriodPair.g₂`/`g₃` (`Weierstrass.lean:951,954`).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `j`, `discriminant_smul`, `j_smul`, `j_congr`, `j_eq_periodPair_j`, `periodPair_discriminant_eq_aux`, `discriminant_ne_zero`, `j_eq_zero_iff_g₂_eq_zero_aux`, `j_eq_1728_iff_g₃_eq_zero_aux`, `homothetic_of_j_eq_*_aux`
- **Visibility**: public
- **Lines**: 56
- **Notes**: name collides (namespaced) with mathlib `ModularForm.discriminant`/`CuspForm.discriminant` (`NumberTheory/ModularForms/Discriminant.lean:233,253`); external use `jFunction/jInvariantLink.lean:51` (`weierstrassCurve_Δ`).

### `def PeriodPair.j`
- **Type**: `(L : PeriodPair) : ℂ := 1728 * L.g₂ ^ 3 / L.discriminant`
- **What**: the lattice `j`-invariant.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: `discriminant`
- **Used by**: `j_smul`, `j_congr`, `j_eq_periodPair_j`, `j_eq_of_homothetic`, `j_eq_zero_iff_g₂_eq_zero_aux`, `j_eq_1728_iff_g₃_eq_zero_aux`, `homothetic_of_j_eq_*`, `j_eq_iff_homothetic`, `j_eq_iff_exists_sl2_smul_eq`
- **Visibility**: public
- **Lines**: 59
- **Notes**: mathlib's only `def j` is `WeierstrassCurve.j` (`AlgebraicGeometry/EllipticCurve/Weierstrass.lean:385`); `jInvariantLink.lean:61` proves `L.weierstrassCurve.j = L.j`.

### `theorem PeriodPair.mem_smul_lattice`
- **Type**: `(L : PeriodPair) {a : ℂˣ} {x : ℂ} : x ∈ (a • L).lattice ↔ ∃ y ∈ L.lattice, x = (a : ℂ) * y`
- **What**: the lattice of `a • L` is `a · lattice L`.
- **How**: `PeriodPair.mem_lattice` (mathlib `Weierstrass.lean:81`) + `smul_ω₁/ω₂` + `ring` in both directions.
- **Hypotheses**: none.
- **Uses from project**: `smul_ω₁`, `smul_ω₂`, `instance SMul`
- **Used by**: `map_lattice_mulLeftLinearEquiv` (76), `exists_sl2_smul_eq_of_periodPair_homothetic_aux` (460, 462, 474, 475), `periodPair_homothetic_of_sl2_smul_aux` (522)
- **Visibility**: public
- **Lines**: 62–69, proof ≈ 6 lines
- **Notes**: —

### `theorem PeriodPair.map_lattice_mulLeftLinearEquiv`
- **Type**: `(a : ℂˣ) (L : PeriodPair) : L.lattice.map (a.mulLeftLinearEquiv ℤ ℂ : ℂ →ₗ[ℤ] ℂ) = (a • L).lattice`
- **What**: submodule image of `L.lattice` under multiplication by `a` is the scaled lattice.
- **How**: `Submodule.mem_map` + `mem_smul_lattice` + `eq_comm`; uses mathlib `Units.mulLeftLinearEquiv` (`Algebra/Module/Equiv/Basic.lean:903`).
- **Hypotheses**: none.
- **Uses from project**: `mem_smul_lattice`
- **Used by**: `smulLatticeEquiv` (84)
- **Visibility**: public
- **Lines**: 72–78, proof ≈ 4 lines
- **Notes**: external uses `CyclicSublattice.lean:213, 498`.

### `def PeriodPair.smulLatticeEquiv`
- **Type**: `(a : ℂˣ) (L : PeriodPair) : L.lattice ≃ₗ[ℤ] (a • L).lattice`
- **What**: multiplication by `a` as a ℤ-linear equivalence of period lattices.
- **How**: `LinearEquiv.ofSubmodules` (mathlib `Algebra/Module/Submodule/Equiv.lean:59`) applied to `mulLeftLinearEquiv` and `map_lattice_mulLeftLinearEquiv`.
- **Hypotheses**: none.
- **Uses from project**: `map_lattice_mulLeftLinearEquiv`
- **Used by**: `coe_smulLatticeEquiv_apply`, `coe_smulLatticeEquiv_symm_apply`, `G_smul` (102)
- **Visibility**: public
- **Lines**: 81–84
- **Notes**: external uses `CyclicSublattice.lean:192, 197`.

### `theorem PeriodPair.coe_smulLatticeEquiv_apply`
- **Type**: `(a) (L) (x : L.lattice) : ((smulLatticeEquiv a L x : (a • L).lattice) : ℂ) = (a : ℂ) * x`
- **What**: the equivalence acts as multiplication by `a`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `smulLatticeEquiv`
- **Used by**: unused in file
- **Visibility**: public, `@[simp]`
- **Lines**: 86–89
- **Notes**: unused project-wide (`G_smul` L106 uses `change` instead; `CyclicSublattice.lean:207` uses `rfl`).

### `theorem PeriodPair.coe_smulLatticeEquiv_symm_apply`
- **Type**: `(a) (L) (x : (a • L).lattice) : (((smulLatticeEquiv a L).symm x : L.lattice) : ℂ) = (a : ℂ)⁻¹ * x`
- **What**: the inverse equivalence divides by `a`.
- **How**: `LinearEquiv.ofSubmodules_symm_apply` + `Units.symm_mulLeftLinearEquiv_apply` (`Algebra/Module/Equiv/Basic.lean:915`).
- **Hypotheses**: none.
- **Uses from project**: `smulLatticeEquiv`
- **Used by**: unused in file
- **Visibility**: public, `@[simp]`
- **Lines**: 91–97, proof ≈ 2 lines
- **Notes**: unused project-wide.

### `theorem PeriodPair.G_smul`
- **Type**: `(L : PeriodPair) (a : ℂˣ) (n : ℕ) : (a • L).G n = ((a : ℂ) ^ n)⁻¹ * L.G n`
- **What**: the lattice Eisenstein sums `G_n = ∑' l, l⁻ⁿ` (mathlib `PeriodPair.G`, `Weierstrass.lean:939`) have weight `n` under scaling.
- **How**: reindex the `tsum` along `smulLatticeEquiv` (`Equiv.tsum_eq`), pull out `(a^n)⁻¹` (`tsum_mul_left`), `mul_pow`, `mul_inv`.
- **Hypotheses**: none (no summability needed: `tsum` identities are unconditional here).
- **Uses from project**: `smulLatticeEquiv`
- **Used by**: `g₂_smul` (112), `g₃_smul` (118)
- **Visibility**: public
- **Lines**: 100–107, proof ≈ 6 lines
- **Notes**: —

### `theorem PeriodPair.g₂_smul`
- **Type**: `(L) (a) : (a • L).g₂ = ((a : ℂ) ^ 4)⁻¹ * L.g₂`
- **What**: `g₂` has weight 4.
- **How**: unfold `g₂ = 60 G 4`, `G_smul`, `ring`.
- **Hypotheses**: none.
- **Uses from project**: `G_smul`
- **Used by**: `discriminant_smul`, `j_smul`, `homothetic_of_j_eq_*_aux` (329, 347, 381)
- **Visibility**: public
- **Lines**: 110–113, proof ≈ 2 lines
- **Notes**: —

### `theorem PeriodPair.g₃_smul`
- **Type**: `(L) (a) : (a • L).g₃ = ((a : ℂ) ^ 6)⁻¹ * L.g₃`
- **What**: `g₃` has weight 6.
- **How**: unfold `g₃ = 140 G 6`, `G_smul`, `ring`.
- **Hypotheses**: none.
- **Uses from project**: `G_smul`
- **Used by**: `discriminant_smul`, `homothetic_of_j_eq_*_aux` (330, 350, 384)
- **Visibility**: public
- **Lines**: 116–119, proof ≈ 2 lines
- **Notes**: —

### `theorem PeriodPair.discriminant_smul`
- **Type**: `(L) (a) : (a • L).discriminant = ((a : ℂ) ^ 12)⁻¹ * L.discriminant`
- **What**: `Δ` has weight 12.
- **How**: `g₂_smul`, `g₃_smul`, `ring`.
- **Hypotheses**: none.
- **Uses from project**: `discriminant`, `g₂_smul`, `g₃_smul`
- **Used by**: `j_smul` (130), `discriminant_ne_zero` (283)
- **Visibility**: public
- **Lines**: 122–125, proof ≈ 2 lines
- **Notes**: —

### `theorem PeriodPair.j_smul`
- **Type**: `(L) (a) : (a • L).j = L.j`
- **What**: the lattice `j` is homothety-invariant.
- **How**: `g₂_smul`, `discriminant_smul`, factor `(a^12)⁻¹` and cancel with `mul_div_mul_left`.
- **Hypotheses**: none.
- **Uses from project**: `j`, `g₂_smul`, `discriminant_smul`
- **Used by**: `j_eq_of_homothetic` (297)
- **Visibility**: public
- **Lines**: 128–133, proof ≈ 5 lines
- **Notes**: external uses `CyclicSublattice.lean:220, 534`, `Classification.lean:320`.

### `theorem PeriodPair.g₂_congr`
- **Type**: `{L M} (h : L.lattice = M.lattice) : L.g₂ = M.g₂`
- **What**: `g₂` depends only on the lattice, not the ordered basis.
- **How**: `unfold g₂ G; rw [h]`.
- **Hypotheses**: equal lattices.
- **Uses from project**: []
- **Used by**: `j_congr` (147), `discriminant_ne_zero` (282)
- **Visibility**: public
- **Lines**: 136–138, proof ≈ 2 lines
- **Notes**: —

### `theorem PeriodPair.g₃_congr`
- **Type**: `{L M} (h : L.lattice = M.lattice) : L.g₃ = M.g₃`
- **What**: `g₃` depends only on the lattice.
- **How**: `unfold g₃ G; rw [h]`.
- **Hypotheses**: equal lattices.
- **Uses from project**: []
- **Used by**: `j_congr`, `discriminant_ne_zero`
- **Visibility**: public
- **Lines**: 141–143, proof ≈ 2 lines
- **Notes**: —

### `theorem PeriodPair.j_congr`
- **Type**: `{L M} (h : L.lattice = M.lattice) : L.j = M.j`
- **What**: `j` depends only on the lattice.
- **How**: `simp [j, discriminant, g₂_congr h, g₃_congr h]`.
- **Hypotheses**: equal lattices.
- **Uses from project**: `j`, `discriminant`, `g₂_congr`, `g₃_congr`
- **Used by**: `j_eq_of_homothetic` (297)
- **Visibility**: public
- **Lines**: 146–147, proof ≈ 1 line
- **Notes**: external uses `CyclicSublattice.lean:186, 219, 532`, `Classification.lean:317`.

### `noncomputable def UpperHalfPlane.periodPair`
- **Type**: `(τ : ℍ) : PeriodPair` with `ω₁ := 1`, `ω₂ := τ`
- **What**: the normalised period pair `[1, τ]`.
- **How**: `LinearIndependent.pair_iff`; compare imaginary parts (`τ.im_ne_zero`) then real parts.
- **Hypotheses**: `τ ∈ ℍ`.
- **Uses from project**: []
- **Used by**: `periodPair_G_eq_aux`, `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`, `j_eq_periodPair_j`, `exists_homothetic_periodPair`, `periodPair_discriminant_eq_aux`, `discriminant_ne_zero`, `mem_periodPair_lattice_aux`, `int_comb_injective_aux`, `exists_sl2_smul_eq_of_periodPair_homothetic_aux`, `periodPair_homothetic_of_sl2_smul_aux`, `periodPair_homothetic_iff_exists_sl2_smul_eq`
- **Visibility**: public
- **Lines**: 154–164
- **Notes**: external uses `jFunction/jInvariantLink.lean:71–79`, `Classification.lean` (throughout). No `periodPair_ω₁`/`periodPair_ω₂` simp lemmas (proofs `simp [UpperHalfPlane.periodPair]` unfold the structure: L177, 257, 260, 405, `Classification.lean:237, 243, 270, 274`).

### `private lemma periodPair_G_eq_aux`
- **Type**: `(τ : ℍ) {k : ℕ} (hk : 3 ≤ k) : (UpperHalfPlane.periodPair τ).G k = riemannZeta k * eisensteinSeries (N := 1) 0 k τ`
- **What**: the lattice sum `G_k([1,τ])` equals `ζ(k)·E_k(τ)` (unnormalised level-1 Eisenstein series).
- **How**: mathlib `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`; reindex the lattice `tsum` through `latticeEquivProd` (mathlib `Weierstrass.lean:154`) composed with `finTwoArrowEquiv`/`Equiv.prodComm`, identify the summand via `latticeEquiv_symm_apply` (`Weierstrass.lean:157`), `ring_nf`.
- **Hypotheses**: `3 ≤ k`.
- **Uses from project**: `UpperHalfPlane.periodPair`
- **Used by**: `periodPair_g₂_eq_E4` (195), `periodPair_g₃_eq_E6` (206)
- **Visibility**: private
- **Lines**: 168–184, proof ≈ 15 lines
- **Notes**: general in `k`; deserves to be public (`PeriodPair.G_periodPair_eq`).

### `private lemma riemannZeta_six_aux`
- **Type**: `riemannZeta 6 = (π : ℂ) ^ 6 / 945`
- **What**: `ζ(6) = π⁶/945`.
- **How**: mathlib `riemannZeta_two_mul_nat` (`NumberTheory/LSeries/HurwitzZetaValues.lean:206`) at `k = 3` with project `bernoulli'_six` (`Modularforms/Eisenstein.lean:288`), `norm_num`.
- **Hypotheses**: none.
- **Uses from project**: `bernoulli'_six`
- **Used by**: `periodPair_g₃_eq_E6` (207)
- **Visibility**: private
- **Lines**: 186–190, proof ≈ 4 lines
- **Notes**: mathlib has `riemannZeta_four` (`HurwitzZetaValues.lean:220`) but no `riemannZeta_six` — mathlib-able; should be public and live next to `bernoulli'_six`.

### `theorem periodPair_g₂_eq_E4`
- **Type**: `(τ : ℍ) : (UpperHalfPlane.periodPair τ).g₂ = 4 * (π : ℂ) ^ 4 / 3 * E4 τ`
- **What**: `g₂([1,τ]) = (4π⁴/3)·E₄(τ)`.
- **How**: `periodPair_G_eq_aux`, mathlib `riemannZeta_four`, and `eisensteinSeries 0 4 τ = 2 * E4 τ` obtained by `rfl`-unfolding `E4 = (1/2) • eisensteinSeriesSIF 0 4` (mathlib `ModularForm.E`, `EisensteinSeries/Basic.lean:47`) + `eisensteinSeriesSIF_apply`; `ring`.
- **Hypotheses**: none.
- **Uses from project**: `periodPair_G_eq_aux`, `UpperHalfPlane.periodPair`, `E4` (`jFunction/Deltaqexpansions.lean:36`, abbrev of mathlib `E₄`)
- **Used by**: `j_eq_periodPair_j` (222), `periodPair_discriminant_eq_aux` (273)
- **Visibility**: public
- **Lines**: 193–201, proof ≈ 7 lines
- **Notes**: relies on definitional unfolding of mathlib's `E` through `.copy` (L198 `from rfl`) — fragile; mathlib has no `E_apply` lemma (grep).

### `theorem periodPair_g₃_eq_E6`
- **Type**: `(τ : ℍ) : (UpperHalfPlane.periodPair τ).g₃ = 8 * (π : ℂ) ^ 6 / 27 * E6 τ`
- **What**: `g₃([1,τ]) = (8π⁶/27)·E₆(τ)`.
- **How**: as for `g₂` with `riemannZeta_six_aux`.
- **Hypotheses**: none.
- **Uses from project**: `periodPair_G_eq_aux`, `riemannZeta_six_aux`, `UpperHalfPlane.periodPair`, `E6`
- **Used by**: `j_eq_periodPair_j` (223), `periodPair_discriminant_eq_aux` (273)
- **Visibility**: public
- **Lines**: 204–212, proof ≈ 7 lines
- **Notes**: same `rfl` fragility (L209).

### `theorem Delta_eq_E4_E6`
- **Type**: `(τ : ℍ) : Delta τ = (E4 τ ^ 3 - E6 τ ^ 2) / 1728`
- **What**: the project's `Delta` (cusp form of weight 12, `Modularforms/Delta.lean:170`) equals `(E₄³ − E₆²)/1728` pointwise.
- **How**: `Delta_apply`, `Delta_eq_eta_pow`, then a `change` to `ModularForm.discriminant τ` and mathlib `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq` (`NumberTheory/ModularForms/LevelOne/GradedRing.lean:59`).
- **Hypotheses**: none.
- **Uses from project**: `Delta`, `Delta_apply` (`Modularforms/Delta.lean:191`), `Delta_eq_eta_pow` (`Modularforms/Delta.lean:36`), `E4`, `E6`
- **Used by**: `j_eq_periodPair_j` (223), `E4_cube_sub_E6_sq_ne_zero_aux` (268)
- **Visibility**: public
- **Lines**: 215–218, proof ≈ 3 lines
- **Notes**: identical pointwise fact re-proved inline at `jFunction/Deltaqexpansions.lean:275–278` (`hDeltaPointwise`) and `Modularforms/DimensionFormulas.lean:120–123`; the `change` at L217 is a defeq abuse (`η^24` vs `ModularForm.discriminant`).

### `theorem j_eq_periodPair_j`
- **Type**: `(τ : ℍ) : j τ = (UpperHalfPlane.periodPair τ).j`
- **What**: the analytic `j = E₄³/Δ` (`jFunction/jfunction.lean:51`) equals the lattice `j` of `[1,τ]` (Cox Thm 10.9 link).
- **How**: unfold both; `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`, `Delta_eq_E4_E6`; factor the constant `64π¹²/27` from numerator and denominator and cancel (`mul_div_mul_left`, `div_div_eq_mul_div`, `ring`).
- **Hypotheses**: none.
- **Uses from project**: `j` (analytic), `PeriodPair.j`, `discriminant`, `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`, `Delta_eq_E4_E6`, `UpperHalfPlane.periodPair`
- **Used by**: `j_eq_iff_exists_sl2_smul_eq` (553)
- **Visibility**: public
- **Lines**: 221–232, proof ≈ 11 lines
- **Notes**: external uses `Classification.lean:321, 357, 365`, `jInvariantLink.lean:79`.

### `theorem exists_homothetic_periodPair`
- **Type**: `(L : PeriodPair) : ∃ τ : ℍ, L.Homothetic (UpperHalfPlane.periodPair τ)`
- **What**: every complex lattice is homothetic to some normalised `[1,τ]`, `τ ∈ ℍ`.
- **How**: `ω₂/ω₁` has nonzero imaginary part by ℝ-independence (`LinearIndependent.pair_iff`, `L.indep.ne_zero`); take `τ = ω₂/ω₁` scaled by `ω₁⁻¹` if `Im > 0`, else `τ = ω₁/ω₂` scaled by `ω₂⁻¹` (`Complex.inv_im`, `Complex.normSq_pos`); lattice equality by `simp [PeriodPair.lattice, …, Set.pair_comm]`.
- **Hypotheses**: none.
- **Uses from project**: `Homothetic`, `UpperHalfPlane.periodPair`, `instance SMul`
- **Used by**: `discriminant_ne_zero` (280)
- **Visibility**: public
- **Lines**: 235–261, proof ≈ 26 lines
- **Notes**: external use `Classification.lean:359`. Mathlib has no such lemma.

### `private lemma E4_cube_sub_E6_sq_ne_zero_aux`
- **Type**: `(τ : ℍ) : E4 τ ^ 3 - E6 τ ^ 2 ≠ 0`
- **What**: `E₄³ − E₆²` never vanishes on ℍ.
- **How**: `Delta τ ≠ 0` from mathlib `ModularForm.discriminant_ne_zero` (`Discriminant.lean:123`) through `Delta_apply`, `Delta_eq_eta_pow`; contradiction via `Delta_eq_E4_E6`.
- **Hypotheses**: none.
- **Uses from project**: `Delta`, `Delta_apply`, `Delta_eq_eta_pow`, `Delta_eq_E4_E6`, `E4`, `E6`
- **Used by**: `discriminant_ne_zero` (291)
- **Visibility**: private
- **Lines**: 263–268, proof ≈ 5 lines
- **Notes**: —

### `private lemma periodPair_discriminant_eq_aux`
- **Type**: `(τ : ℍ) : (UpperHalfPlane.periodPair τ).discriminant = 64 * (π : ℂ) ^ 12 / 27 * (E4 τ ^ 3 - E6 τ ^ 2)`
- **What**: `Δ([1,τ])` in terms of `E₄`, `E₆`.
- **How**: `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`, `ring`.
- **Hypotheses**: none.
- **Uses from project**: `discriminant`, `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`, `E4`, `E6`
- **Used by**: `discriminant_ne_zero` (288)
- **Visibility**: private
- **Lines**: 270–274, proof ≈ 2 lines
- **Notes**: the same factorisation is redone inline in `j_eq_periodPair_j` L226–228; make this public and use it there.

### `theorem PeriodPair.discriminant_ne_zero`
- **Type**: `(L : PeriodPair) : L.discriminant ≠ 0`
- **What**: Cox Prop 10.7: the lattice discriminant never vanishes.
- **How**: reduce to `[1,τ]` by `exists_homothetic_periodPair`, `discriminant_smul`, `g₂_congr`/`g₃_congr`, then `periodPair_discriminant_eq_aux` + `E4_cube_sub_E6_sq_ne_zero_aux` + `Real.pi_ne_zero`.
- **Hypotheses**: none.
- **Uses from project**: `discriminant`, `exists_homothetic_periodPair`, `discriminant_smul`, `g₂_congr`, `g₃_congr`, `periodPair_discriminant_eq_aux`, `E4_cube_sub_E6_sq_ne_zero_aux`
- **Used by**: `homothetic_of_j_eq_of_g₂_eq_zero_aux`, `…g₃_eq_zero_aux`, `…g₂_ne_zero_of_g₃_ne_zero_aux` (315–316, 336–337, 354–355)
- **Visibility**: public
- **Lines**: 279–292, proof ≈ 13 lines
- **Notes**: external use `jInvariantLink.lean:57`. Name collides (namespaced) with mathlib `ModularForm.discriminant_ne_zero`.

### `theorem PeriodPair.j_eq_of_homothetic`
- **Type**: `{L M} (h : L.Homothetic M) : L.j = M.j`
- **What**: Cox Thm 10.9, easy direction.
- **How**: `j_smul` + `j_congr`.
- **Hypotheses**: homothetic.
- **Uses from project**: `Homothetic`, `j_smul`, `j_congr`
- **Used by**: `j_eq_iff_homothetic` (398)
- **Visibility**: public
- **Lines**: 295–297, proof ≈ 2 lines
- **Notes**: external use `Classification.lean:365`.

### `private lemma PeriodPair.j_eq_zero_iff_g₂_eq_zero_aux`
- **Type**: `{L} (hΔ : L.discriminant ≠ 0) : L.j = 0 ↔ L.g₂ = 0`
- **What**: `j = 0` iff `g₂ = 0`.
- **How**: `simp [j, hΔ]`.
- **Hypotheses**: `Δ ≠ 0`.
- **Uses from project**: `j`, `discriminant`
- **Used by**: `homothetic_of_j_eq_of_g₂_eq_zero_aux`, `…ne_zero_aux`
- **Visibility**: private
- **Lines**: 299–301, proof ≈ 1 line
- **Notes**: `hΔ` could be discharged internally by `discriminant_ne_zero`.

### `private lemma PeriodPair.j_eq_1728_iff_g₃_eq_zero_aux`
- **Type**: `{L} (hΔ : L.discriminant ≠ 0) : L.j = 1728 ↔ L.g₃ = 0`
- **What**: `j = 1728` iff `g₃ = 0`.
- **How**: `div_eq_iff`, unfold `discriminant`, `linear_combination h / 46656` to get `g₃² = 0`, `pow_eq_zero_iff`.
- **Hypotheses**: `Δ ≠ 0`.
- **Uses from project**: `j`, `discriminant`
- **Used by**: `homothetic_of_j_eq_of_g₃_eq_zero_aux`, `…ne_zero_aux`
- **Visibility**: private
- **Lines**: 303–311, proof ≈ 7 lines
- **Notes**: —

### `private theorem PeriodPair.homothetic_of_j_eq_of_g₂_eq_zero_aux`
- **Type**: `{L M} (h : L.j = M.j) (hg₂L : L.g₂ = 0) : L.Homothetic M`
- **What**: Thm 10.9 hard direction, case `g₂(L) = 0` (so `j = 0`, `g₃ ≠ 0`).
- **How**: `g₂(M) = 0` by the `j = 0` criterion; pick `c` with `c⁶ = g₃(L)/g₃(M)` (`IsAlgClosed.exists_pow_nat_eq`, mathlib `FieldTheory/IsAlgClosed/Basic.lean:93`); then `c • L` and `M` share `g₂ = 0` and `g₃` (`g₂_smul`, `g₃_smul`, `field_simp`), and `lattice_eq_of_g₂_eq_of_g₃_eq` (`XYin/uniqueness.lean:282`) gives equal lattices.
- **Hypotheses**: `j` equal, `g₂(L) = 0`.
- **Uses from project**: `discriminant_ne_zero`, `j_eq_zero_iff_g₂_eq_zero_aux`, `discriminant`, `g₂_smul`, `g₃_smul`, `lattice_eq_of_g₂_eq_of_g₃_eq`, `Homothetic`
- **Used by**: `homothetic_of_j_eq` (391)
- **Visibility**: private
- **Lines**: 313–332, proof ≈ 19 lines
- **Notes**: —

### `private theorem PeriodPair.homothetic_of_j_eq_of_g₃_eq_zero_aux`
- **Type**: `{L M} (h : L.j = M.j) (hg₂L : L.g₂ ≠ 0) (hg₃L : L.g₃ = 0) : L.Homothetic M`
- **What**: case `g₃(L) = 0` (`j = 1728`).
- **How**: mirror of the previous with `c⁴ = g₂(L)/g₂(M)` and the `j = 1728` criterion.
- **Hypotheses**: `j` equal, `g₂ ≠ 0`, `g₃ = 0`.
- **Uses from project**: `discriminant_ne_zero`, `j_eq_1728_iff_g₃_eq_zero_aux`, `discriminant`, `g₂_smul`, `g₃_smul`, `lattice_eq_of_g₂_eq_of_g₃_eq`, `Homothetic`
- **Used by**: `homothetic_of_j_eq` (393)
- **Visibility**: private
- **Lines**: 334–350, proof ≈ 16 lines
- **Notes**: same skeleton as the `g₂ = 0` case.

### `private theorem PeriodPair.homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux`
- **Type**: `{L M} (h : L.j = M.j) (hg₂L : L.g₂ ≠ 0) (hg₃L : L.g₃ ≠ 0) : L.Homothetic M`
- **What**: generic case of Thm 10.9.
- **How**: cross-multiplying `j` gives `g₂(L)³ g₃(M)² = g₂(M)³ g₃(L)²` (`div_eq_div_iff`, `linear_combination`); choose `c` with `c² = g₃(L)g₂(M)/(g₃(M)g₂(L))`; derive `c⁴ = g₂(L)/g₂(M)`, `c⁶ = g₃(L)/g₃(M)` by `linear_combination` from the cross relation; conclude with `g₂_smul`, `g₃_smul`, `lattice_eq_of_g₂_eq_of_g₃_eq`.
- **Hypotheses**: `j` equal, `g₂, g₃ ≠ 0`.
- **Uses from project**: `discriminant_ne_zero`, `j_eq_zero_iff_g₂_eq_zero_aux`, `j_eq_1728_iff_g₃_eq_zero_aux`, `j`, `discriminant`, `g₂_smul`, `g₃_smul`, `lattice_eq_of_g₂_eq_of_g₃_eq`, `Homothetic`
- **Used by**: `homothetic_of_j_eq` (394)
- **Visibility**: private
- **Lines**: 352–386, proof ≈ 34 lines
- **Notes**: proof >30 lines.

### `theorem PeriodPair.homothetic_of_j_eq`
- **Type**: `{L M} (h : L.j = M.j) : L.Homothetic M`
- **What**: Cox Thm 10.9: equal `j` ⇒ homothetic.
- **How**: case split on `g₂ = 0`, `g₃ = 0` into the three aux theorems.
- **Hypotheses**: equal `j`.
- **Uses from project**: the three `homothetic_of_j_eq_*_aux`, `Homothetic`
- **Used by**: `j_eq_iff_homothetic` (398)
- **Visibility**: public
- **Lines**: 389–394, proof ≈ 5 lines
- **Notes**: —

### `theorem PeriodPair.j_eq_iff_homothetic`
- **Type**: `{L M} : L.j = M.j ↔ L.Homothetic M`
- **What**: Thm 10.9 in iff form.
- **How**: `⟨homothetic_of_j_eq, j_eq_of_homothetic⟩`.
- **Hypotheses**: none.
- **Uses from project**: `homothetic_of_j_eq`, `j_eq_of_homothetic`
- **Used by**: `j_eq_iff_exists_sl2_smul_eq` (553)
- **Visibility**: public
- **Lines**: 397–398
- **Notes**: —

### `private lemma mem_periodPair_lattice_aux`
- **Type**: `{τ : ℍ} {x : ℂ} : x ∈ (UpperHalfPlane.periodPair τ).lattice ↔ ∃ m n : ℤ, (m : ℂ) + n * τ = x`
- **What**: membership in `ℤ + ℤτ`.
- **How**: mathlib `PeriodPair.mem_lattice` + `simp [UpperHalfPlane.periodPair]`.
- **Hypotheses**: none.
- **Uses from project**: `UpperHalfPlane.periodPair`
- **Used by**: `exists_sl2_smul_eq_of_periodPair_homothetic_aux` (461, 465, 466, 467, 470, 473, 476, 477), `periodPair_homothetic_of_sl2_smul_aux` (525, 526, 532, 533)
- **Visibility**: private
- **Lines**: 402–405, proof ≈ 2 lines
- **Notes**: should be a public simp lemma `UpperHalfPlane.mem_periodPair_lattice`.

### `private lemma int_comb_injective_aux`
- **Type**: `{τ : ℍ} {m n m' n' : ℤ} (h : (m : ℂ) + n * τ = (m' : ℂ) + n' * τ) : m = m' ∧ n = n'`
- **What**: `1, τ` are ℤ-independent: integer coordinates in `ℤ + ℤτ` are unique.
- **How**: ℝ-linear independence of `(1, τ)` (`LinearIndependent.pair_iff` on `periodPair τ`), cast back to ℤ.
- **Hypotheses**: none.
- **Uses from project**: `UpperHalfPlane.periodPair`
- **Used by**: `exists_sl2_smul_eq_of_periodPair_homothetic_aux` (480, 487)
- **Visibility**: private
- **Lines**: 407–421, proof ≈ 13 lines
- **Notes**: this is injectivity of mathlib's `latticeEquivProd.symm` (`Weierstrass.lean:154,157`) — could ride on it.

### `private theorem exists_sl2_smul_eq_of_det_mul_eq_one_aux`
- **Type**: `{z w : ℍ} (a b c d k : ℤ) (hdet : (a * d - b * c) * k = 1) (hzval : (z : ℂ) = ((b : ℂ) + a * w) / ((d : ℂ) + c * w)) : ∃ γ : SL(2, ℤ), γ • z = w`
- **What**: if `z = (aw + b)/(cw + d)` with `ad − bc = ±1`, then `z` and `w` are in the same `SL₂(ℤ)`-orbit (and the sign `−1` is impossible by positivity of imaginary parts).
- **How**: `Int.eq_one_or_neg_one_of_mul_eq_one'` (`Algebra/Group/Int/Units.lean:54`); case `+1`: `γ' = !![a,b;c,d]`, `γ' • w = z` via `UpperHalfPlane.coe_specialLinearGroup_apply` (`Analysis/Complex/UpperHalfPlane/MoebiusAction.lean:292`), answer `γ'⁻¹` with `inv_smul_smul`; case `−1`: `!![-a,-b;c,d] • w = -z` contradicts `im_pos`.
- **Hypotheses**: as stated.
- **Uses from project**: []
- **Used by**: `exists_sl2_smul_eq_of_periodPair_homothetic_aux` (498)
- **Visibility**: private
- **Lines**: 423–452, proof ≈ 26 lines
- **Notes**: —

### `private theorem exists_sl2_smul_eq_of_periodPair_homothetic_aux`
- **Type**: `{z w : ℍ} (h : PeriodPair.Homothetic (UpperHalfPlane.periodPair z) (UpperHalfPlane.periodPair w)) : ∃ γ : SL(2, ℤ), γ • z = w`
- **What**: Cox (7.8), forward: homothetic normalised lattices are `SL₂(ℤ)`-related.
- **How**: with `α · [1,z] = [1,w]`, write `αz = b + aw`, `α = d + cw`, `1 = α(p + qz)`, `w = α(r + sz)`; `int_comb_injective_aux` gives integer identities, `linear_combination` yields `(ad − bc)(ps − qr) = 1`; then `exists_sl2_smul_eq_of_det_mul_eq_one_aux`.
- **Hypotheses**: homothetic.
- **Uses from project**: `Homothetic`, `mem_smul_lattice`, `mem_periodPair_lattice_aux`, `int_comb_injective_aux`, `exists_sl2_smul_eq_of_det_mul_eq_one_aux`, `UpperHalfPlane.periodPair`
- **Used by**: `periodPair_homothetic_iff_exists_sl2_smul_eq` (546)
- **Visibility**: private
- **Lines**: 454–498, proof ≈ 42 lines
- **Notes**: proof >30 lines.

### `private theorem periodPair_homothetic_of_sl2_smul_aux`
- **Type**: `(γ : SL(2, ℤ)) (z : ℍ) : PeriodPair.Homothetic (UpperHalfPlane.periodPair z) (UpperHalfPlane.periodPair (γ • z))`
- **What**: Cox (7.8), backward: `[1, γz]` is `(cz+d)⁻¹ · [1, z]`.
- **How**: scalar `(Units.mk0 (cz+d) _)⁻¹` (`UpperHalfPlane.denom_ne_zero`, `ModularGroup.denom_apply`, `MoebiusAction.lean:484`); both inclusions of lattices by explicit integer recombination `(m a − n b, n d − m c)` / `(m d + n b, m c + n a)` and `linear_combination` with `ad − bc = 1`.
- **Hypotheses**: none.
- **Uses from project**: `Homothetic`, `mem_smul_lattice`, `mem_periodPair_lattice_aux`, `UpperHalfPlane.periodPair`, `instance SMul`
- **Used by**: `periodPair_homothetic_iff_exists_sl2_smul_eq` (548)
- **Visibility**: private
- **Lines**: 500–539, proof ≈ 38 lines
- **Notes**: proof >30 lines.

### `theorem periodPair_homothetic_iff_exists_sl2_smul_eq`
- **Type**: `{z w : ℍ} : PeriodPair.Homothetic (UpperHalfPlane.periodPair z) (UpperHalfPlane.periodPair w) ↔ ∃ γ : SL(2, ℤ), γ • z = w`
- **What**: Cox equation (7.8): homothety of normalised lattices is the `SL₂(ℤ)`-orbit relation.
- **How**: the two private aux theorems.
- **Hypotheses**: none.
- **Uses from project**: `exists_sl2_smul_eq_of_periodPair_homothetic_aux`, `periodPair_homothetic_of_sl2_smul_aux`, `Homothetic`, `UpperHalfPlane.periodPair`
- **Used by**: `j_eq_iff_exists_sl2_smul_eq` (554)
- **Visibility**: public
- **Lines**: 542–548, proof ≈ 4 lines
- **Notes**: —

### `theorem j_eq_iff_exists_sl2_smul_eq`
- **Type**: `(τ τ' : ℍ) : j τ = j τ' ↔ ∃ γ : SL(2, ℤ), γ • τ = τ'`
- **What**: Cox Thm 11.2(ii): the analytic `j` separates `SL₂(ℤ)`-orbits.
- **How**: `j_eq_periodPair_j`, `j_eq_iff_homothetic`, `periodPair_homothetic_iff_exists_sl2_smul_eq`.
- **Hypotheses**: none.
- **Uses from project**: `j`, `j_eq_periodPair_j`, `PeriodPair.j_eq_iff_homothetic`, `periodPair_homothetic_iff_exists_sl2_smul_eq`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 551–554, proof ≈ 2 lines
- **Notes**: unused project-wide (top-level theorem; `j_modularGroup_smul` in `jfunction.lean:76` is the `←` half elsewhere).

### `private def levelOneWeightZeroCuspForm_aux`
- **Type**: `{f : ℍ → ℂ} (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hmdiff : MDiff f) (hzero : IsZeroAtImInfty f) : CuspForm (Gamma 1) 0`
- **What**: package a slash-invariant, holomorphic function vanishing at `i∞` as a level-one weight-zero cusp form.
- **How**: `slash_action_eq'` from `hslash`; `zero_at_cusps'` via project `zero_at_cusps_of_zero_at_infty` (`Modularforms/ForMathlib_Cusps.lean:9`) using `mapGL`.
- **Hypotheses**: as stated.
- **Uses from project**: `zero_at_cusps_of_zero_at_infty`
- **Used by**: `weight_zero_cuspForm_eq_zero_aux` (573)
- **Visibility**: private
- **Lines**: 556–568
- **Notes**: moral duplicate of `Modularforms/IsCuspForm.lean:101 cuspFormOfSIFTendstoZero` (same `zero_at_cusps_of_zero_at_infty` construction from a `SlashInvariantForm`).

### `private theorem weight_zero_cuspForm_eq_zero_aux`
- **Type**: `{f} (hslash) (hmdiff : MDiff f) (hzero : IsZeroAtImInfty f) : f = 0`
- **What**: a level-one weight-zero cusp form is identically zero.
- **How**: mathlib `ModularForm.eq_const_of_weight_zero` (`NumberTheory/ModularForms/NormTrace.lean:163`) gives `f = const c`; `tendsto_nhds_unique` with `IsZeroAtImInfty` forces `c = 0`.
- **Hypotheses**: as stated.
- **Uses from project**: `levelOneWeightZeroCuspForm_aux`
- **Used by**: `j_surjective` (629)
- **Visibility**: private
- **Lines**: 570–578, proof ≈ 6 lines
- **Notes**: the only reason for `import Mathlib.NumberTheory.ModularForms.NormTrace`; `ModularForm.levelOne_weight_zero_const` (`LevelOne/Basic.lean:104`) would suffice.

### `private theorem inv_j_sub_slashInvariant_aux`
- **Type**: `(c : ℂ) : letI f := fun τ => (j τ - c)⁻¹; ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f`
- **What**: `1/(j − c)` is weight-0 slash invariant.
- **How**: `SL_slash_apply` (mathlib `SlashActions.lean:162`), `zpow_zero`, project `j_modularGroup_smul` (`jFunction/jfunction.lean:76`).
- **Hypotheses**: none.
- **Uses from project**: `j`, `j_modularGroup_smul`
- **Used by**: `j_surjective` (629)
- **Visibility**: private
- **Lines**: 580–586, proof ≈ 4 lines
- **Notes**: —

### `private theorem inv_j_sub_mdiff_aux`
- **Type**: `(c : ℂ) (hc : ∀ τ : ℍ, j τ ≠ c) : MDiff (fun τ : ℍ => (j τ - c)⁻¹)`
- **What**: `1/(j − c)` is holomorphic when `j` omits `c`.
- **How**: `ModularFunction.j_mdifferentiable` (`ModularFunctions/JInvariant.lean:24`), `.sub mdifferentiableAt_const`, `.inv`.
- **Hypotheses**: `j` never takes the value `c`.
- **Uses from project**: `j`, `ModularFunction.j_mdifferentiable`
- **Used by**: `j_surjective` (630)
- **Visibility**: private
- **Lines**: 588–591, proof ≈ 2 lines
- **Notes**: replaces the private `j_mdifferentiable_aux` that existed at HEAD (removed in working tree).

### `private lemma E4_tendsto_atImInfty_aux`
- **Type**: `Tendsto (E4 : ℍ → ℂ) atImInfty (nhds 1)`
- **What**: `E₄(τ) → 1` as `Im τ → ∞`.
- **How**: `E4 ∘ ofComplex` is 1-periodic (`SlashInvariantFormClass.periodic_comp_ofComplex`, mathlib `QExpansion.lean:120`); `cuspFunction 1 E4 0 = 1` from `EisensteinSeries.E_qExpansion_coeff_zero` (`EisensteinSeries/QExpansion.lean:348`); `ModularFormClass.analyticAt_cuspFunction_zero` (`QExpansion.lean:153`) continuity composed with `qParam_tendsto_atImInfty` (`QExpansion.lean:67`) and `eq_cuspFunction`.
- **Hypotheses**: none.
- **Uses from project**: `E4`
- **Used by**: `qj_tendsto_atImInfty_aux` (606)
- **Visibility**: private
- **Lines**: 593–602, proof ≈ 9 lines
- **Notes**: same skeleton as `Modularforms/IsCuspForm.lean:113 isZeroAtImInfty_of_coeffZero` (coefficient 0 instead of 1) — a generic `ModularFormClass.tendsto_atImInfty : Tendsto f atImInfty (𝓝 ((qExpansion 1 f).coeff 0))` is missing from both mathlib and the project.

### `private lemma qj_tendsto_atImInfty_aux`
- **Type**: `Tendsto qj atImInfty (nhds 1)`
- **What**: `q·j(τ) → 1` at `i∞`.
- **How**: `E4_pow_three_mul_qOverDelta_eq_qj` (`jfunction.lean:242`), `E4_tendsto_atImInfty_aux.pow 3`, `qOverDelta_tendsto_atImInfty` (`jfunction.lean:252`).
- **Hypotheses**: none.
- **Uses from project**: `qj`, `E4_pow_three_mul_qOverDelta_eq_qj`, `qOverDelta_tendsto_atImInfty`, `E4_tendsto_atImInfty_aux`
- **Used by**: `inv_j_sub_isZeroAtImInfty_aux` (614)
- **Visibility**: private
- **Lines**: 604–606, proof ≈ 2 lines
- **Notes**: belongs in `jfunction.lean` next to `qOverDelta_tendsto_atImInfty`.

### `private theorem inv_j_sub_isZeroAtImInfty_aux`
- **Type**: `(c : ℂ) : IsZeroAtImInfty (fun τ : ℍ => (j τ - c)⁻¹)`
- **What**: `1/(j − c) → 0` at `i∞`.
- **How**: `(j − c)⁻¹ = q/(qj − c q)` eventually (`field_simp`, `q ≠ 0`); numerator `→ 0` (`qParam_tendsto_atImInfty`), denominator `→ 1` (`qj_tendsto_atImInfty_aux`), `Tendsto.congr'`.
- **Hypotheses**: none.
- **Uses from project**: `j`, `qj`, `qj_tendsto_atImInfty_aux`
- **Used by**: `j_surjective` (630)
- **Visibility**: private
- **Lines**: 608–623, proof ≈ 14 lines
- **Notes**: —

### `theorem j_surjective`
- **Type**: `Function.Surjective j`
- **What**: Cox Thm 11.2(iii): the analytic `j : ℍ → ℂ` is onto.
- **How**: if `j` omits `c`, then `1/(j − c)` is a holomorphic weight-0 slash-invariant function vanishing at `i∞`, hence `0` by `weight_zero_cuspForm_eq_zero_aux`, contradicting `inv_ne_zero` at `τ = i`.
- **Hypotheses**: none.
- **Uses from project**: `j`, `weight_zero_cuspForm_eq_zero_aux`, `inv_j_sub_slashInvariant_aux`, `inv_j_sub_mdiff_aux`, `inv_j_sub_isZeroAtImInfty_aux`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 626–632, proof ≈ 6 lines
- **Notes**: external uses `Classification.lean:352`, `Cox/UpperHalfPlaneFunctionField.lean:80`, `Cox/ModularPolynomial/Construction.lean:339`.

## File Summary
- Total declarations: 54 (8 defs [`PeriodPair.smul`, `Homothetic`, `discriminant`, `j`, `smulLatticeEquiv`, `UpperHalfPlane.periodPair`, `levelOneWeightZeroCuspForm_aux` (private)] + 1 instance, 45 lemmas/theorems, 1 instance, 0 other)
- Key API (used by 3+ others in the file): `instance SMul ℂˣ PeriodPair`, `Homothetic`, `discriminant`, `PeriodPair.j`, `UpperHalfPlane.periodPair`, `mem_smul_lattice`, `g₂_smul`, `g₃_smul`, `discriminant_ne_zero`, `mem_periodPair_lattice_aux`
- Unused declarations (not used by anything in this file): `coe_smulLatticeEquiv_apply`, `coe_smulLatticeEquiv_symm_apply` (both unused project-wide), `j_eq_iff_exists_sl2_smul_eq` (unused project-wide), `j_surjective` (used by 3 other files)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux` (≈34), `exists_sl2_smul_eq_of_periodPair_homothetic_aux` (≈42), `periodPair_homothetic_of_sl2_smul_aux` (≈38)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `PeriodPair` and its `lattice`, `latticeBasis`, `latticeEquivProd`, `latticeEquiv_symm_apply`, `mem_lattice`, `G`, `g₂`, `g₃`, `finrank_lattice` are MATHLIB (`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:60,79,81,144,151,154,157,939,951,954`); mathlib also has `instance : IsZLattice ℝ L.lattice` (`:120`) and `DiscreteTopology` (`:118`). Mathlib has NO scaling action, NO homothety, NO `discriminant`/`j` on `PeriodPair`, NO `[1,τ]` (`UpperHalfPlane.periodPair`), NO `G_k([1,τ]) = ζ(k) E_k(τ)`. All of L33–164 is genuine gap-filling and mathlib-able.
- `Delta_eq_E4_E6` (L215) is mathlib `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq` (`NumberTheory/ModularForms/LevelOne/GradedRing.lean:59`) transported through the project's `Delta`; the project's `Delta : CuspForm (Gamma 1) 12` (`Modularforms/Delta.lean:170`, `Delta_apply : Delta z = Δ z := rfl`) itself duplicates mathlib's `CuspForm.discriminant : CuspForm 𝒮ℒ 12` (`Discriminant.lean:233`, `coe_discriminant : discriminant = Δ := rfl` L253). Unlocks deleting `Delta_apply`/`Delta_eq_eta_pow` rewrites at L216, 266.
- `riemannZeta_six_aux` (L186): mathlib has `riemannZeta_four` (`HurwitzZetaValues.lean:220`) and `riemannZeta_two_mul_nat` (`:206`) but not `ζ(6)`; `bernoulli'_six` is project (`Modularforms/Eisenstein.lean:288`). Both are mathlib PR material.
- `E4_tendsto_atImInfty_aux` (L593): mathlib has only `qParam_tendsto_atImInfty` (`QExpansion.lean:67`) + `analyticAt_cuspFunction_zero` (`:153`) + `eq_cuspFunction` (`:132`); no "modular form tends to its constant term" lemma (grep `tendsto.*atImInfty` in `ModularForms/QExpansion.lean`, `BoundedAtCusp.lean`, `EisensteinSeries/*` → only `qParam_tendsto_atImInfty`).
- `weight_zero_cuspForm_eq_zero_aux` (L570) uses `ModularForm.eq_const_of_weight_zero` (`NormTrace.lean:163`); `ModularForm.levelOne_weight_zero_const` (`LevelOne/Basic.lean:104`) is the lighter import.
- `int_comb_injective_aux` (L407) and `mem_periodPair_lattice_aux` (L402) are `latticeEquivProd.symm`-injectivity and `PeriodPair.mem_lattice` specialised to `[1,τ]`.
- `exists_sl2_smul_eq_of_det_mul_eq_one_aux` / `periodPair_homothetic_of_sl2_smul_aux` correctly ride on `Int.eq_one_or_neg_one_of_mul_eq_one'` (`Algebra/Group/Int/Units.lean:54`), `UpperHalfPlane.coe_specialLinearGroup_apply` (`MoebiusAction.lean:292`), `ModularGroup.denom_apply` (`:484`), `UpperHalfPlane.denom_ne_zero`. Mathlib's fundamental domain `ModularGroup.fd` (`NumberTheory/Modular.lean:367`) and `exists_smul_mem_fd` (`:426`) are NOT needed here and not used; nothing in mathlib states "homothety of `[1,z],[1,w]` ↔ `SL₂(ℤ)`-orbit".
- `homothetic_of_j_eq_*` use `IsAlgClosed.exists_pow_nat_eq` (`FieldTheory/IsAlgClosed/Basic.lean:93`) and project `lattice_eq_of_g₂_eq_of_g₃_eq` (`XYin/uniqueness.lean:282`, the ℘-uniqueness theorem) — the latter is the deep input; mathlib has ℘ (`Weierstrass.lean:263`) but not "g₂,g₃ determine the lattice".
- `j_surjective`: no mathlib analogue (mathlib has no `j`-function on ℍ; searched `def j`, `j_surjective`).
- Imports: still `import XYin.PhD.Modularforms.ForMathlib_Cusps` (L9; used only at L565 `zero_at_cusps_of_zero_at_infty`) and `import XYin.uniqueness` (L11; used only at L328, 346, 380 `lattice_eq_of_g₂_eq_of_g₃_eq`). HEAD imported `XYin.PhD.jFunction.jfunction`; the working tree imports `XYin.PhD.ModularFunctions.JInvariant` instead (for `ModularFunction.j_mdifferentiable`, L590) and dropped the private `j_mdifferentiable_aux`. `Mathlib.NumberTheory.ModularForms.NormTrace` is imported only for `eq_const_of_weight_zero`.
### Missing API / repeated patterns
- `simp [UpperHalfPlane.periodPair]` structure-unfolding at L177, 257, 260, 405 (and `Classification.lean:237, 243, 270, 274`): add `@[simp] periodPair_ω₁ : (periodPair τ).ω₁ = 1`, `periodPair_ω₂ : (periodPair τ).ω₂ = τ`, and `mem_periodPair_lattice` (publish L402).
- `Homothetic` lacks `refl`/`symm`/`trans` (a `Setoid`); `SMul ℂˣ PeriodPair` lacks `MulAction` (`one_smul`, `mul_smul`) and `smul_lattice : (a • L).lattice = L.lattice.map (mulLeft a)` (L72 states it with `map` on the left).
- `j_eq_zero_iff_g₂_eq_zero_aux` / `j_eq_1728_iff_g₃_eq_zero_aux` (L299, 303) take `hΔ` although `discriminant_ne_zero` (L279) is available — drop the hypothesis and publish as `PeriodPair.j_eq_zero_iff`, `j_eq_1728_iff`.
- The three-way case analysis L313–394 (≈75 lines) shares the skeleton "choose `c` with `c^k = ratio`, then `g₂_smul`/`g₃_smul` + `field_simp` + `lattice_eq_of_g₂_eq_of_g₃_eq`" three times; a lemma `homothetic_of_exists_pow : (∃ c ≠ 0, c^4 • g₂ M = g₂ L ∧ c^6 • g₃ M = g₃ L) → Homothetic L M` would collapse the tails.
- The factorisation `(4π⁴/3 E₄)³ − 27(8π⁶/27 E₆)² = 64π¹²/27 (E₄³ − E₆²)` is done in `j_eq_periodPair_j` (L226–228) and again as `periodPair_discriminant_eq_aux` (L270); use the latter in the former.
### Junk candidates
- `coe_smulLatticeEquiv_apply` (L87) and `coe_smulLatticeEquiv_symm_apply` (L92): `@[simp]` but unused project-wide.
- `j_eq_iff_exists_sl2_smul_eq` (L551): unused project-wide (kept as Cox 11.2(ii) headline).
- `periodPair_discriminant_eq_aux` (L270): duplicated inline at L226–228.
- No dead `#check`/`example`s or commented-out code.
### Moral duplicates within this batch
- `Delta_eq_E4_E6` (L215) ≡ `jFunction/Deltaqexpansions.lean:275–278` (`hDeltaPointwise`) ≡ `Modularforms/DimensionFormulas.lean:120–123` (inside `Delta_E4_eqn`).
- `levelOneWeightZeroCuspForm_aux` (L556) ≡ `Modularforms/IsCuspForm.lean:101 cuspFormOfSIFTendstoZero` (identical `zero_at_cusps'` proof).
- `E4_tendsto_atImInfty_aux` (L593) ≡ skeleton of `Modularforms/IsCuspForm.lean:113 isZeroAtImInfty_of_coeffZero`.
- `homothetic_of_j_eq_of_g₂_eq_zero_aux` (L313) / `…g₃_eq_zero_aux` (L334): mirror proofs.
- `g₂_congr` (L136) / `g₃_congr` (L141): same two-line proof.
- Previously-reported private copies: `complex_mobius_scale_eq_affine` is NOT in this batch but is still privately duplicated at `Cox/ModularFunction/LevelJ.lean:72` and `Cox/CoxMatrices/Basic.lean:699` (identical statements); `periodic_comp_ofComplex_of_vadd` exists once, privately, at `ModularFunctions/Congruence.lean:36`; `j_periodic_aux` no longer exists anywhere (public `ModularFunction.j_periodic` at `JInvariant.lean:28`). None of this file's 24 private names has a namesake elsewhere (grep-verified).
### Generalization notes
- `PeriodPair.smul`, `mem_smul_lattice`, `map_lattice_mulLeftLinearEquiv`, `smulLatticeEquiv` (L33–84) only use that `a` is a unit of the field ℂ acting ℤ-linearly; they would hold for any `ℤ`-lattice in a `ℂ`-module.
- `G_smul` (L100) needs only `Equiv.tsum_eq` and `tsum_mul_left` — valid in any complete normed field; `g₂_smul`, `g₃_smul`, `discriminant_smul`, `j_smul` are then pure `ring`/`field` identities (need `a^12 ≠ 0`).
- `exists_sl2_smul_eq_of_det_mul_eq_one_aux` (L423) is genuinely ℤ-specific (units `±1`); `periodPair_homothetic_of_sl2_smul_aux` (L500) uses only `ad − bc = 1` and would hold for `SL(2, R)` over any subring `R ⊆ ℂ` with `R + Rτ` lattices.
- `j_surjective`'s argument (L556–632) is the generic "a holomorphic level-one weight-0 function vanishing at `i∞` is 0"; only `inv_j_sub_*` are `j`-specific.
