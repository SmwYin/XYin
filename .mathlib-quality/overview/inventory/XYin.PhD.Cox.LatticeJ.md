# Inventory: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/LatticeJ.lean
Project-internal imports: `XYin.PhD.Modularforms.ForMathlib_Cusps`, `XYin.PhD.jFunction.jfunction`, `XYin.uniqueness`

File purpose (module docstring): proves Cox Theorems 10.9 and 11.2 relating the analytic `j`-function to lattice invariants, classifying equal lattice invariants up to homothety, and identifying normalized homothety classes with `SL₂(ℤ)`-orbits. Note: the `PeriodPair` structure and its fields/API (`ω₁`, `ω₂`, `indep`, `lattice`, `mem_lattice`, `G`, `g₂`, `g₃`, `latticeEquivProd`) come from Mathlib (`Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass`, reached via `XYin.uniqueness`), not from this project.

### `def PeriodPair.smul` (protected)
- **Type**: `(a : ℂˣ) → PeriodPair → PeriodPair`
- **What**: Scales both periods ω₁, ω₂ of a period pair by a nonzero complex number a, giving the homothetic period pair aL.
- **How**: Linear independence of (aω₁, aω₂) over ℝ is reduced to that of (ω₁, ω₂) by factoring a out of the vanishing combination (`LinearIndependent.pair_iff`) and cancelling it via `mul_eq_zero` and `a.ne_zero`.
- **Hypotheses**: a is a unit of ℂ (nonzero).
- **Uses from project**: []
- **Used by**: `instance : SMul ℂˣ PeriodPair` (and hence every `a • L` in the file)
- **Visibility**: public (protected)
- **Lines**: 32–42 (proof of `indep` field: 7 lines)
- **Notes**: none

### `instance : SMul ℂˣ PeriodPair`
- **Type**: `SMul ℂˣ PeriodPair`
- **What**: Registers scalar multiplication of period pairs by nonzero complex numbers, enabling the `a • L` notation for homothety.
- **How**: Direct wrapper around `PeriodPair.smul`.
- **Hypotheses**: none.
- **Uses from project**: [`PeriodPair.smul`]
- **Used by**: `smul_ω₁`, `smul_ω₂`, `Homothetic`, `mem_smul_lattice`, `map_lattice_mulLeftLinearEquiv`, `smulLatticeEquiv`, `G_smul`, `g₂_smul`, `g₃_smul`, `discriminant_smul`, `j_smul`, and all downstream homothety lemmas
- **Visibility**: public
- **Lines**: 44 (term-mode, 1 line)
- **Notes**: anonymous instance

### `theorem PeriodPair.smul_ω₁`
- **Type**: `(a : ℂˣ) (L : PeriodPair) : (a • L).ω₁ = a * L.ω₁`
- **What**: The first period of the scaled pair is a times the original first period.
- **How**: Definitional equality (`rfl`) from the definition of `PeriodPair.smul`.
- **Hypotheses**: none.
- **Uses from project**: [`PeriodPair.smul` (via the `SMul` instance)]
- **Used by**: `mem_smul_lattice`, `exists_homothetic_periodPair`
- **Visibility**: public
- **Lines**: 46 (1 line)
- **Notes**: `@[simp]`

### `theorem PeriodPair.smul_ω₂`
- **Type**: `(a : ℂˣ) (L : PeriodPair) : (a • L).ω₂ = a * L.ω₂`
- **What**: The second period of the scaled pair is a times the original second period.
- **How**: Definitional equality (`rfl`) from the definition of `PeriodPair.smul`.
- **Hypotheses**: none.
- **Uses from project**: [`PeriodPair.smul` (via the `SMul` instance)]
- **Used by**: `mem_smul_lattice`, `exists_homothetic_periodPair`
- **Visibility**: public
- **Lines**: 48 (1 line)
- **Notes**: `@[simp]`

### `def PeriodPair.Homothetic`
- **Type**: `(L M : PeriodPair) : Prop`
- **What**: Two period pairs are homothetic when some nonzero complex scaling carries the period lattice of L exactly onto the lattice of M, i.e. ∃ a ∈ ℂˣ, (aL).lattice = M.lattice.
- **How**: Definition as an existential over ℂˣ using the `SMul` action and Mathlib's `PeriodPair.lattice`.
- **Hypotheses**: none.
- **Uses from project**: [`instance : SMul ℂˣ PeriodPair`]
- **Used by**: `j_eq_of_homothetic`, `homothetic_of_j_eq_of_g₂_eq_zero_aux`, `homothetic_of_j_eq_of_g₃_eq_zero_aux`, `homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux`, `homothetic_of_j_eq`, `j_eq_iff_homothetic`, `exists_homothetic_periodPair`, `exists_sl2_smul_eq_of_periodPair_homothetic_aux`, `periodPair_homothetic_of_sl2_smul_aux`, `periodPair_homothetic_iff_exists_sl2_smul_eq`
- **Visibility**: public
- **Lines**: 50–53 (definition, 1 line body)
- **Notes**: none

### `def PeriodPair.discriminant`
- **Type**: `(L : PeriodPair) : ℂ`
- **What**: Cox's lattice discriminant Δ(L) = g₂(L)³ − 27 g₃(L)².
- **How**: Direct polynomial expression in Mathlib's lattice Eisenstein invariants `g₂`, `g₃`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `j`, `discriminant_smul`, `j_congr`, `j_eq_periodPair_j`, `periodPair_discriminant_eq_aux`, `discriminant_ne_zero`, `j_eq_1728_iff_g₃_eq_zero_aux`, `homothetic_of_j_eq_of_g₂_eq_zero_aux`, `homothetic_of_j_eq_of_g₃_eq_zero_aux`, `homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux`
- **Visibility**: public
- **Lines**: 55–56 (1 line)
- **Notes**: none

### `def PeriodPair.j`
- **Type**: `(L : PeriodPair) : ℂ`
- **What**: Cox's lattice j-invariant j(L) = 1728 g₂(L)³ / Δ(L), where Δ is the lattice discriminant.
- **How**: Direct quotient of `1728 * g₂ ^ 3` by `PeriodPair.discriminant`.
- **Hypotheses**: none (division-by-zero convention when Δ = 0, though Δ ≠ 0 is later proved).
- **Uses from project**: [`PeriodPair.discriminant`]
- **Used by**: `j_smul`, `j_congr`, `j_eq_periodPair_j`, `j_eq_of_homothetic`, `j_eq_zero_iff_g₂_eq_zero_aux`, `j_eq_1728_iff_g₃_eq_zero_aux`, `homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux`, `homothetic_of_j_eq`, `j_eq_iff_homothetic`
- **Visibility**: public
- **Lines**: 58–59 (1 line)
- **Notes**: same name as the analytic `j : ℍ → ℂ` from `jfunction.lean` but in the `PeriodPair` namespace

### `theorem PeriodPair.mem_smul_lattice`
- **Type**: `(L : PeriodPair) {a : ℂˣ} {x : ℂ} : x ∈ (a • L).lattice ↔ ∃ y ∈ L.lattice, x = (a : ℂ) * y`
- **What**: Membership in the lattice of a scaled period pair is exactly being a times a member of the original lattice.
- **How**: Both directions unfold ℤ-linear combinations m·ω₁ + n·ω₂ via Mathlib's `PeriodPair.mem_lattice` together with `smul_ω₁`/`smul_ω₂`, distributing the factor a by `ring`.
- **Hypotheses**: none.
- **Uses from project**: [`smul_ω₁`, `smul_ω₂`, `instance : SMul ℂˣ PeriodPair`]
- **Used by**: `map_lattice_mulLeftLinearEquiv`, `G_smul`, `exists_sl2_smul_eq_of_periodPair_homothetic_aux`, `periodPair_homothetic_of_sl2_smul_aux`
- **Visibility**: public
- **Lines**: 61–69 (proof 7 lines)
- **Notes**: none

### `theorem PeriodPair.map_lattice_mulLeftLinearEquiv`
- **Type**: `(a : ℂˣ) (L : PeriodPair) : L.lattice.map (a.mulLeftLinearEquiv ℤ ℂ : ℂ →ₗ[ℤ] ℂ) = (a • L).lattice`
- **What**: The ℤ-linear map "multiply by a" carries the period lattice of L onto the lattice of aL (as an equality of ℤ-submodules of ℂ).
- **How**: Elementwise: `Submodule.mem_map` on the left and `mem_smul_lattice` on the right produce identical existential statements, matched directly in both directions.
- **Hypotheses**: none.
- **Uses from project**: [`mem_smul_lattice`, `instance : SMul ℂˣ PeriodPair`]
- **Used by**: `smulLatticeEquiv` (also used externally by `Cox/CyclicSublattice.lean`)
- **Visibility**: public
- **Lines**: 71–81 (proof 8 lines)
- **Notes**: uses Mathlib's `Units.mulLeftLinearEquiv`

### `def PeriodPair.smulLatticeEquiv`
- **Type**: `(a : ℂˣ) (L : PeriodPair) : L.lattice ≃ₗ[ℤ] (a • L).lattice`
- **What**: The ℤ-linear equivalence between the lattice of L and the lattice of aL given by multiplication by a.
- **How**: Restricts Mathlib's `Units.mulLeftLinearEquiv` to the two submodules via `LinearEquiv.ofSubmodules`, with the mapping property supplied by `map_lattice_mulLeftLinearEquiv`.
- **Hypotheses**: none.
- **Uses from project**: [`map_lattice_mulLeftLinearEquiv`, `instance : SMul ℂˣ PeriodPair`]
- **Used by**: `coe_smulLatticeEquiv_apply`, `coe_smulLatticeEquiv_symm_apply`
- **Visibility**: public
- **Lines**: 83–87 (term-mode, 3 lines)
- **Notes**: none

### `theorem PeriodPair.coe_smulLatticeEquiv_apply`
- **Type**: `(a : ℂˣ) (L : PeriodPair) (x : L.lattice) : ((smulLatticeEquiv a L x : (a • L).lattice) : ℂ) = (a : ℂ) * x`
- **What**: On underlying complex numbers, the lattice equivalence `smulLatticeEquiv` acts as multiplication by a.
- **How**: Definitional (`rfl`).
- **Hypotheses**: none.
- **Uses from project**: [`smulLatticeEquiv`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 89–92 (1 line)
- **Notes**: `@[simp]`

### `theorem PeriodPair.coe_smulLatticeEquiv_symm_apply`
- **Type**: `(a : ℂˣ) (L : PeriodPair) (x : (a • L).lattice) : (((smulLatticeEquiv a L).symm x : L.lattice) : ℂ) = (a : ℂ)⁻¹ * x`
- **What**: The inverse of the lattice equivalence acts as multiplication by a⁻¹ on underlying complex numbers.
- **How**: Unfolds `LinearEquiv.ofSubmodules_symm_apply` and applies Mathlib's `Units.symm_mulLeftLinearEquiv_apply`.
- **Hypotheses**: none.
- **Uses from project**: [`smulLatticeEquiv`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 94–100 (proof 2 lines)
- **Notes**: `@[simp]`

### `theorem PeriodPair.G_smul`
- **Type**: `(L : PeriodPair) (a : ℂˣ) (n : ℕ) : (a • L).G n = ((a : ℂ) ^ n)⁻¹ * L.G n`
- **What**: The lattice Eisenstein sum G_n(L) = Σ 1/ωⁿ has weight n under homothety: G_n(aL) = a⁻ⁿ G_n(L).
- **How**: Builds the explicit bijection l ↦ al between the two lattices (inverses via `inv_mul_cancel_left₀`), then reindexes the tsum by `Equiv.tsum_eq` and pulls the constant a⁻ⁿ out with `tsum_mul_left` and `mul_pow`.
- **Hypotheses**: none (both sums are over all lattice points; convergence not needed for the tsum manipulation since the equiv reindexing is unconditional).
- **Uses from project**: [`mem_smul_lattice`, `instance : SMul ℂˣ PeriodPair`]
- **Used by**: `g₂_smul`, `g₃_smul`
- **Visibility**: public
- **Lines**: 102–117 (proof 14 lines)
- **Notes**: none

### `theorem PeriodPair.g₂_smul`
- **Type**: `(L : PeriodPair) (a : ℂˣ) : (a • L).g₂ = ((a : ℂ) ^ 4)⁻¹ * L.g₂`
- **What**: The invariant g₂ = 60 G₄ has weight 4 under homothety.
- **How**: Unfolds Mathlib's `g₂` in terms of `G 4` and applies `G_smul` with n = 4, closing with `ring`.
- **Hypotheses**: none.
- **Uses from project**: [`G_smul`, `instance : SMul ℂˣ PeriodPair`]
- **Used by**: `discriminant_smul`, `j_smul`, `homothetic_of_j_eq_of_g₂_eq_zero_aux`, `homothetic_of_j_eq_of_g₃_eq_zero_aux`, `homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux`
- **Visibility**: public
- **Lines**: 119–123 (proof 2 lines)
- **Notes**: none

### `theorem PeriodPair.g₃_smul`
- **Type**: `(L : PeriodPair) (a : ℂˣ) : (a • L).g₃ = ((a : ℂ) ^ 6)⁻¹ * L.g₃`
- **What**: The invariant g₃ = 140 G₆ has weight 6 under homothety.
- **How**: Unfolds Mathlib's `g₃` in terms of `G 6` and applies `G_smul` with n = 6, closing with `ring`.
- **Hypotheses**: none.
- **Uses from project**: [`G_smul`, `instance : SMul ℂˣ PeriodPair`]
- **Used by**: `discriminant_smul`, `homothetic_of_j_eq_of_g₂_eq_zero_aux`, `homothetic_of_j_eq_of_g₃_eq_zero_aux`, `homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux`
- **Visibility**: public
- **Lines**: 125–129 (proof 2 lines)
- **Notes**: none

### `theorem PeriodPair.discriminant_smul`
- **Type**: `(L : PeriodPair) (a : ℂˣ) : (a • L).discriminant = ((a : ℂ) ^ 12)⁻¹ * L.discriminant`
- **What**: The lattice discriminant g₂³ − 27g₃² has weight 12 under homothety.
- **How**: Substitutes `g₂_smul` and `g₃_smul` into the definition of the discriminant; the weight bookkeeping (a⁻⁴·³ = a⁻⁶·² = a⁻¹²) is `ring`.
- **Hypotheses**: none.
- **Uses from project**: [`discriminant`, `g₂_smul`, `g₃_smul`, `instance : SMul ℂˣ PeriodPair`]
- **Used by**: `j_smul`, `discriminant_ne_zero`
- **Visibility**: public
- **Lines**: 131–135 (proof 2 lines)
- **Notes**: none

### `theorem PeriodPair.j_smul`
- **Type**: `(L : PeriodPair) (a : ℂˣ) : (a • L).j = L.j`
- **What**: The lattice j-invariant is invariant under homothety (weight 0): the a⁻¹² factors in numerator and denominator cancel.
- **How**: Substitutes `g₂_smul` and `discriminant_smul` into the definition of j, factors out a⁻¹² from the numerator by `ring`, and cancels it with `mul_div_mul_left` using a ≠ 0.
- **Hypotheses**: none.
- **Uses from project**: [`j`, `g₂_smul`, `discriminant_smul`, `instance : SMul ℂˣ PeriodPair`]
- **Used by**: `j_eq_of_homothetic`
- **Visibility**: public
- **Lines**: 137–143 (proof 5 lines)
- **Notes**: none

### `theorem PeriodPair.g₂_congr`
- **Type**: `{L M : PeriodPair} (h : L.lattice = M.lattice) : L.g₂ = M.g₂`
- **What**: g₂ depends only on the period lattice, not on the chosen ordered basis of periods.
- **How**: Unfolds `g₂` and `G` to a tsum over the lattice and rewrites the lattice by h.
- **Hypotheses**: L and M generate the same lattice.
- **Uses from project**: []
- **Used by**: `j_congr`, `discriminant_ne_zero`
- **Visibility**: public
- **Lines**: 145–148 (proof 2 lines)
- **Notes**: none

### `theorem PeriodPair.g₃_congr`
- **Type**: `{L M : PeriodPair} (h : L.lattice = M.lattice) : L.g₃ = M.g₃`
- **What**: g₃ depends only on the period lattice, not on the chosen ordered basis of periods.
- **How**: Unfolds `g₃` and `G` to a tsum over the lattice and rewrites the lattice by h.
- **Hypotheses**: L and M generate the same lattice.
- **Uses from project**: []
- **Used by**: `j_congr`, `discriminant_ne_zero`
- **Visibility**: public
- **Lines**: 150–153 (proof 2 lines)
- **Notes**: none

### `theorem PeriodPair.j_congr`
- **Type**: `{L M : PeriodPair} (h : L.lattice = M.lattice) : L.j = M.j`
- **What**: The lattice j-invariant depends only on the lattice, not the chosen basis.
- **How**: Since j is a rational function of g₂ and g₃, this follows from `g₂_congr` and `g₃_congr` by `simp` on the definitions of `j` and `discriminant`.
- **Hypotheses**: L and M generate the same lattice.
- **Uses from project**: [`j`, `discriminant`, `g₂_congr`, `g₃_congr`]
- **Used by**: `j_eq_of_homothetic`
- **Visibility**: public
- **Lines**: 155–157 (proof 1 line)
- **Notes**: none

### `def UpperHalfPlane.periodPair`
- **Type**: `(τ : ℍ) : PeriodPair`
- **What**: The normalized period pair [1, τ] attached to a point τ of the upper half-plane, whose lattice is ℤ + ℤτ.
- **How**: ℝ-linear independence of (1, τ) follows because a·1 + b·τ = 0 forces b·Im τ = 0 (taking imaginary parts), hence b = 0 by `τ.im_ne_zero`, then a = 0 (taking real parts); packaged with `LinearIndependent.pair_iff`.
- **Hypotheses**: τ has positive (in particular nonzero) imaginary part, built into ℍ.
- **Uses from project**: []
- **Used by**: `periodPair_G_eq_aux`, `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`, `j_eq_periodPair_j`, `exists_homothetic_periodPair`, `discriminant_ne_zero`, `periodPair_discriminant_eq_aux`, `mem_periodPair_lattice_aux`, `int_comb_injective_aux`, `exists_sl2_smul_eq_of_periodPair_homothetic_aux`, `periodPair_homothetic_of_sl2_smul_aux`, `periodPair_homothetic_iff_exists_sl2_smul_eq`, `j_eq_iff_exists_sl2_smul_eq`
- **Visibility**: public
- **Lines**: 163–174 (indep proof 8 lines)
- **Notes**: `noncomputable`

### `lemma periodPair_G_eq_aux`
- **Type**: `(τ : ℍ) {k : ℕ} (hk : 3 ≤ k) : (UpperHalfPlane.periodPair τ).G k = riemannZeta k * eisensteinSeries (N := 1) 0 k τ`
- **What**: The lattice Eisenstein sum G_k of [1, τ] equals ζ(k) times the level-1 Eisenstein series of weight k at τ — the bridge between lattice sums and modular-form Eisenstein series.
- **How**: Starts from Mathlib's `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries` and reindexes the lattice tsum along the equivalence `Fin 2 → ℤ ≃ ℤ × ℤ ≃ lattice` built from `finTwoArrowEquiv`, `Equiv.prodComm` and Mathlib's `latticeEquivProd`, identifying each lattice element with v₁ + v₀τ via `latticeEquiv_symm_apply`.
- **Hypotheses**: k ≥ 3 (absolute convergence of the Eisenstein sum).
- **Uses from project**: [`UpperHalfPlane.periodPair`]
- **Used by**: `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`
- **Visibility**: private
- **Lines**: 178–194 (proof 15 lines)
- **Notes**: none

### `lemma riemannZeta_six_aux`
- **Type**: `riemannZeta 6 = (π : ℂ) ^ 6 / 945`
- **What**: The classical special value ζ(6) = π⁶/945.
- **How**: Specializes Mathlib's `riemannZeta_two_mul_nat` at k = 3 and evaluates the Bernoulli number via `bernoulli_eq_bernoulli'_of_ne_one` and the project lemma `bernoulli'_six` (B₆' = 1/42), finishing with `norm_num`/`ring`.
- **Hypotheses**: none.
- **Uses from project**: [`bernoulli'_six` (XYin/PhD/Modularforms/Eisenstein.lean)]
- **Used by**: `periodPair_g₃_eq_E6`
- **Visibility**: private
- **Lines**: 196–200 (proof 4 lines)
- **Notes**: none

### `theorem periodPair_g₂_eq_E4`
- **Type**: `(τ : ℍ) : (UpperHalfPlane.periodPair τ).g₂ = 4 * (π : ℂ) ^ 4 / 3 * E4 τ`
- **What**: The lattice invariant g₂([1,τ]) equals (4π⁴/3)·E₄(τ), expressing g₂ through the normalized weight-4 Eisenstein series.
- **How**: Applies `periodPair_G_eq_aux` at k = 4, evaluates ζ(4) = π⁴/90 via Mathlib's `riemannZeta_four`, and converts `eisensteinSeries` to 2·E₄ using the project's definition of `E4` as ½·`eisensteinSeriesSIF` (unfolded by `rfl` and `eisensteinSeriesSIF_apply`).
- **Hypotheses**: none.
- **Uses from project**: [`UpperHalfPlane.periodPair`, `periodPair_G_eq_aux`, `E4` (abbrev for project `E₄`)]
- **Used by**: `j_eq_periodPair_j`, `periodPair_discriminant_eq_aux`
- **Visibility**: public
- **Lines**: 202–211 (proof 8 lines)
- **Notes**: none

### `theorem periodPair_g₃_eq_E6`
- **Type**: `(τ : ℍ) : (UpperHalfPlane.periodPair τ).g₃ = 8 * (π : ℂ) ^ 6 / 27 * E6 τ`
- **What**: The lattice invariant g₃([1,τ]) equals (8π⁶/27)·E₆(τ), expressing g₃ through the normalized weight-6 Eisenstein series.
- **How**: Applies `periodPair_G_eq_aux` at k = 6, evaluates ζ(6) = π⁶/945 via `riemannZeta_six_aux`, and converts `eisensteinSeries` to 2·E₆ using the definition of `E6` as ½·`eisensteinSeriesSIF`.
- **Hypotheses**: none.
- **Uses from project**: [`UpperHalfPlane.periodPair`, `periodPair_G_eq_aux`, `riemannZeta_six_aux`, `E6` (abbrev for project `E₆`)]
- **Used by**: `j_eq_periodPair_j`, `periodPair_discriminant_eq_aux`
- **Visibility**: public
- **Lines**: 213–222 (proof 8 lines)
- **Notes**: none

### `theorem Delta_eq_E4_E6`
- **Type**: `(τ : ℍ) : Delta τ = (E4 τ ^ 3 - E6 τ ^ 2) / 1728`
- **What**: The project's cusp form Δ equals (E₄³ − E₆²)/1728 pointwise — the classical discriminant identity.
- **How**: Rewrites the project's `Delta` via `Delta_apply` and `Delta_eq_eta_pow` to Mathlib's `ModularForm.discriminant` (definitional `change`), then applies Mathlib's `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`.
- **Hypotheses**: none.
- **Uses from project**: [`Delta`, `Delta_apply`, `Delta_eq_eta_pow` (XYin/PhD/Modularforms/Delta.lean), `E4`, `E6`]
- **Used by**: `j_eq_periodPair_j`, `E4_cube_sub_E6_sq_ne_zero_aux`
- **Visibility**: public
- **Lines**: 224–228 (proof 3 lines)
- **Notes**: none

### `theorem j_eq_periodPair_j`
- **Type**: `(τ : ℍ) : j τ = (UpperHalfPlane.periodPair τ).j`
- **What**: Bridge identity: the analytic modular function j(τ) = E₄³/Δ agrees with Cox's lattice invariant 1728 g₂³/Δ_lattice of the period pair [1,τ].
- **How**: Substitutes `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6` and `Delta_eq_E4_E6`; the powers of π combine into a common nonzero factor 64π¹²/27 in numerator and denominator (nonzero by `Real.pi_ne_zero`), cancelled by `mul_div_mul_left`, so 1728·g₂³/(g₂³−27g₃²) = E₄³/((E₄³−E₆²)/1728).
- **Hypotheses**: none.
- **Uses from project**: [`j` (analytic, XYin/PhD/jFunction/jfunction.lean), `PeriodPair.j`, `PeriodPair.discriminant`, `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`, `Delta_eq_E4_E6`, `UpperHalfPlane.periodPair`, `E4`, `E6`]
- **Used by**: `j_eq_iff_exists_sl2_smul_eq`
- **Visibility**: public
- **Lines**: 230–242 (proof 11 lines)
- **Notes**: none

### `theorem exists_homothetic_periodPair`
- **Type**: `(L : PeriodPair) : ∃ τ : ℍ, L.Homothetic (UpperHalfPlane.periodPair τ)`
- **What**: Every complex period lattice is homothetic to a normalized lattice [1, τ] with τ in the upper half-plane — normalization of lattices.
- **How**: The ratio ω₂/ω₁ has nonzero imaginary part (else the periods would be ℝ-dependent, contradicting `L.indep` via `LinearIndependent.pair_iff`); scaling by ω₁⁻¹ (if Im > 0) or ω₂⁻¹ (if Im < 0, using `Complex.inv_im` to flip the sign and `Set.pair_comm` to swap generators) carries {ω₁, ω₂} to {1, τ}, giving equal lattices.
- **Hypotheses**: none.
- **Uses from project**: [`Homothetic`, `UpperHalfPlane.periodPair`, `smul_ω₁`, `smul_ω₂`, `instance : SMul ℂˣ PeriodPair`]
- **Used by**: `discriminant_ne_zero`
- **Visibility**: public
- **Lines**: 244–283 (proof 37 lines)
- **Notes**: proof >30 lines

### `lemma E4_cube_sub_E6_sq_ne_zero_aux`
- **Type**: `(τ : ℍ) : E4 τ ^ 3 - E6 τ ^ 2 ≠ 0`
- **What**: The modular discriminant combination E₄³ − E₆² never vanishes on the upper half-plane.
- **How**: If it vanished then Δ(τ) = 0 by `Delta_eq_E4_E6`, contradicting Mathlib's `ModularForm.discriminant_ne_zero` (transported through the project's `Delta_apply` and `Delta_eq_eta_pow`).
- **Hypotheses**: none.
- **Uses from project**: [`Delta`, `Delta_apply`, `Delta_eq_eta_pow`, `Delta_eq_E4_E6`, `E4`, `E6`]
- **Used by**: `discriminant_ne_zero`
- **Visibility**: private
- **Lines**: 285–290 (proof 5 lines)
- **Notes**: none

### `lemma periodPair_discriminant_eq_aux`
- **Type**: `(τ : ℍ) : (UpperHalfPlane.periodPair τ).discriminant = 64 * (π : ℂ) ^ 12 / 27 * (E4 τ ^ 3 - E6 τ ^ 2)`
- **What**: The lattice discriminant of [1, τ] equals (64π¹²/27)·(E₄(τ)³ − E₆(τ)²).
- **How**: Substitutes `periodPair_g₂_eq_E4` and `periodPair_g₃_eq_E6` into the definition of the discriminant; the constants combine by `ring`.
- **Hypotheses**: none.
- **Uses from project**: [`PeriodPair.discriminant`, `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`, `UpperHalfPlane.periodPair`, `E4`, `E6`]
- **Used by**: `discriminant_ne_zero`
- **Visibility**: private
- **Lines**: 292–296 (proof 2 lines)
- **Notes**: none

### `theorem PeriodPair.discriminant_ne_zero`
- **Type**: `(L : PeriodPair) : L.discriminant ≠ 0`
- **What**: Cox Proposition 10.7: the discriminant g₂³ − 27g₃² of a complex lattice never vanishes.
- **How**: Normalizes L to some [1, τ] by `exists_homothetic_periodPair`; the discriminants agree up to the nonzero factor a⁻¹² (`discriminant_smul` with `g₂_congr`/`g₃_congr` for basis-independence), and the discriminant of [1, τ] is nonzero by `periodPair_discriminant_eq_aux` combined with `E4_cube_sub_E6_sq_ne_zero_aux` and π ≠ 0.
- **Hypotheses**: none.
- **Uses from project**: [`exists_homothetic_periodPair`, `discriminant`, `discriminant_smul`, `g₂_congr`, `g₃_congr`, `periodPair_discriminant_eq_aux`, `E4_cube_sub_E6_sq_ne_zero_aux`, `UpperHalfPlane.periodPair`]
- **Used by**: `homothetic_of_j_eq_of_g₂_eq_zero_aux`, `homothetic_of_j_eq_of_g₃_eq_zero_aux`, `homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux`
- **Visibility**: public
- **Lines**: 300–314 (proof 13 lines)
- **Notes**: none

### `theorem PeriodPair.j_eq_of_homothetic`
- **Type**: `{L M : PeriodPair} (h : L.Homothetic M) : L.j = M.j`
- **What**: Cox Theorem 10.9, easy direction: homothetic lattices have equal j-invariants.
- **How**: If (aL).lattice = M.lattice then j(L) = j(aL) by homothety-invariance (`j_smul`) and j(aL) = j(M) by basis-independence (`j_congr`).
- **Hypotheses**: L and M are homothetic.
- **Uses from project**: [`Homothetic`, `j`, `j_smul`, `j_congr`]
- **Used by**: `j_eq_iff_homothetic`
- **Visibility**: public
- **Lines**: 316–319 (proof 2 lines)
- **Notes**: none

### `lemma PeriodPair.j_eq_zero_iff_g₂_eq_zero_aux`
- **Type**: `{L : PeriodPair} (hΔ : L.discriminant ≠ 0) : L.j = 0 ↔ L.g₂ = 0`
- **What**: For a lattice with nonvanishing discriminant, j = 0 exactly when g₂ = 0 (the CM point of j-invariant 0).
- **How**: j = 0 means the fraction 1728g₂³/Δ vanishes; by `div_eq_zero_iff` and hΔ the numerator vanishes, and g₂³ = 0 gives g₂ = 0 by `pow_eq_zero_iff`. Converse is direct substitution.
- **Hypotheses**: Δ(L) ≠ 0.
- **Uses from project**: [`j`, `discriminant`]
- **Used by**: `homothetic_of_j_eq_of_g₂_eq_zero_aux`, `homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux`
- **Visibility**: private
- **Lines**: 321–331 (proof 9 lines)
- **Notes**: none

### `lemma PeriodPair.j_eq_1728_iff_g₃_eq_zero_aux`
- **Type**: `{L : PeriodPair} (hΔ : L.discriminant ≠ 0) : L.j = 1728 ↔ L.g₃ = 0`
- **What**: For a lattice with nonvanishing discriminant, j = 1728 exactly when g₃ = 0 (the CM point of j-invariant 1728).
- **How**: Cross-multiplying j = 1728 by Δ (`div_eq_iff`) gives 1728g₂³ = 1728(g₂³ − 27g₃²), so 46656·g₃² = 0 by `linear_combination`, hence g₃ = 0 by `pow_eq_zero_iff`. Conversely if g₃ = 0 then Δ = g₂³ ≠ 0 (else Δ = 0) and the fraction reduces to 1728 by `div_self`.
- **Hypotheses**: Δ(L) ≠ 0.
- **Uses from project**: [`j`, `discriminant`]
- **Used by**: `homothetic_of_j_eq_of_g₃_eq_zero_aux`, `homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux`
- **Visibility**: private
- **Lines**: 333–346 (proof 12 lines)
- **Notes**: none

### `theorem PeriodPair.homothetic_of_j_eq_of_g₂_eq_zero_aux`
- **Type**: `{L M : PeriodPair} (h : L.j = M.j) (hg₂L : L.g₂ = 0) : L.Homothetic M`
- **What**: Hard direction of Cox 10.9 in the case j = 0: if both lattices have j-invariant 0 (g₂ = 0), they are homothetic.
- **How**: g₂ = 0 for both by `j_eq_zero_iff_g₂_eq_zero_aux`, and g₃ ≠ 0 for both since Δ ≠ 0 (`discriminant_ne_zero`); choose a 6th root c of g₃(L)/g₃(M) by `IsAlgClosed.exists_pow_nat_eq`, so scaling by c matches both invariants (`g₂_smul`, `g₃_smul`), and equal invariants force equal lattices by the project uniqueness theorem `lattice_eq_of_g₂_eq_of_g₃_eq`.
- **Hypotheses**: j(L) = j(M) and g₂(L) = 0.
- **Uses from project**: [`Homothetic`, `j`, `discriminant`, `discriminant_ne_zero`, `j_eq_zero_iff_g₂_eq_zero_aux`, `g₂_smul`, `g₃_smul`, `lattice_eq_of_g₂_eq_of_g₃_eq` (XYin/uniqueness.lean)]
- **Used by**: `homothetic_of_j_eq`
- **Visibility**: private
- **Lines**: 348–373 (proof 24 lines)
- **Notes**: none

### `theorem PeriodPair.homothetic_of_j_eq_of_g₃_eq_zero_aux`
- **Type**: `{L M : PeriodPair} (h : L.j = M.j) (hg₂L : L.g₂ ≠ 0) (hg₃L : L.g₃ = 0) : L.Homothetic M`
- **What**: Hard direction of Cox 10.9 in the case j = 1728: if both lattices have g₃ = 0, they are homothetic.
- **How**: Mirror of the g₂ = 0 case: g₃ = 0 for both by `j_eq_1728_iff_g₃_eq_zero_aux`, g₂ ≠ 0 for both since Δ ≠ 0; a 4th root c of g₂(L)/g₂(M) (`IsAlgClosed.exists_pow_nat_eq`) matches both invariants and `lattice_eq_of_g₂_eq_of_g₃_eq` concludes.
- **Hypotheses**: j(L) = j(M), g₂(L) ≠ 0, g₃(L) = 0.
- **Uses from project**: [`Homothetic`, `j`, `discriminant`, `discriminant_ne_zero`, `j_eq_1728_iff_g₃_eq_zero_aux`, `g₂_smul`, `g₃_smul`, `lattice_eq_of_g₂_eq_of_g₃_eq`]
- **Used by**: `homothetic_of_j_eq`
- **Visibility**: private
- **Lines**: 375–397 (proof 21 lines)
- **Notes**: none

### `theorem PeriodPair.homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux`
- **Type**: `{L M : PeriodPair} (h : L.j = M.j) (hg₂L : L.g₂ ≠ 0) (hg₃L : L.g₃ ≠ 0) : L.Homothetic M`
- **What**: Hard direction of Cox 10.9 in the generic case g₂, g₃ both nonzero: equal j-invariants imply homothety.
- **How**: Equal j gives the cross relation g₂(L)³g₃(M)² = g₂(M)³g₃(L)² (`div_eq_div_iff` + `linear_combination`); choosing c with c² = g₃(L)g₂(M)/(g₃(M)g₂(L)) via `IsAlgClosed.exists_pow_nat_eq`, the cross relation yields c⁴ = g₂(L)/g₂(M) and c⁶ = g₃(L)/g₃(M), so scaling by c matches both invariants and `lattice_eq_of_g₂_eq_of_g₃_eq` gives equal lattices.
- **Hypotheses**: j(L) = j(M), g₂(L) ≠ 0, g₃(L) ≠ 0.
- **Uses from project**: [`Homothetic`, `j`, `discriminant`, `discriminant_ne_zero`, `j_eq_zero_iff_g₂_eq_zero_aux`, `j_eq_1728_iff_g₃_eq_zero_aux`, `g₂_smul`, `g₃_smul`, `lattice_eq_of_g₂_eq_of_g₃_eq`]
- **Used by**: `homothetic_of_j_eq`
- **Visibility**: private
- **Lines**: 399–438 (proof 38 lines)
- **Notes**: proof >30 lines

### `theorem PeriodPair.homothetic_of_j_eq`
- **Type**: `{L M : PeriodPair} (h : L.j = M.j) : L.Homothetic M`
- **What**: Cox Theorem 10.9 (hard direction): period pairs with equal lattice j-invariants are homothetic.
- **How**: Case split on g₂(L) = 0 and g₃(L) = 0, dispatching to the three auxiliary case lemmas (j = 0 case, j = 1728 case, generic case).
- **Hypotheses**: j(L) = j(M).
- **Uses from project**: [`Homothetic`, `j`, `homothetic_of_j_eq_of_g₂_eq_zero_aux`, `homothetic_of_j_eq_of_g₃_eq_zero_aux`, `homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux`]
- **Used by**: `j_eq_iff_homothetic`
- **Visibility**: public
- **Lines**: 440–446 (proof 5 lines)
- **Notes**: none

### `theorem PeriodPair.j_eq_iff_homothetic`
- **Type**: `{L M : PeriodPair} : L.j = M.j ↔ L.Homothetic M`
- **What**: Cox Theorem 10.9 in iff form: two lattices have the same j-invariant precisely when they are homothetic.
- **How**: Combines `homothetic_of_j_eq` and `j_eq_of_homothetic`.
- **Hypotheses**: none.
- **Uses from project**: [`j`, `Homothetic`, `homothetic_of_j_eq`, `j_eq_of_homothetic`]
- **Used by**: `j_eq_iff_exists_sl2_smul_eq`
- **Visibility**: public
- **Lines**: 448–450 (term-mode, 1 line)
- **Notes**: none

### `lemma mem_periodPair_lattice_aux`
- **Type**: `{τ : ℍ} {x : ℂ} : x ∈ (UpperHalfPlane.periodPair τ).lattice ↔ ∃ m n : ℤ, (m : ℂ) + n * τ = x`
- **What**: A complex number lies in the lattice of [1, τ] iff it is an integer combination m + nτ.
- **How**: Unfolds Mathlib's `PeriodPair.mem_lattice` and simplifies using ω₁ = 1, ω₂ = τ from the definition of `UpperHalfPlane.periodPair`.
- **Hypotheses**: none.
- **Uses from project**: [`UpperHalfPlane.periodPair`]
- **Used by**: `exists_sl2_smul_eq_of_periodPair_homothetic_aux`, `periodPair_homothetic_of_sl2_smul_aux`
- **Visibility**: private
- **Lines**: 454–457 (proof 2 lines)
- **Notes**: none

### `lemma int_comb_injective_aux`
- **Type**: `{τ : ℍ} {m n m' n' : ℤ} (h : (m : ℂ) + n * τ = (m' : ℂ) + n' * τ) : m = m' ∧ n = n'`
- **What**: The representation of a lattice point of ℤ + ℤτ as m + nτ is unique: {1, τ} is a ℤ-basis.
- **How**: The difference gives (m − m')·1 + (n − n')·τ = 0 as an ℝ-linear relation; ℝ-linear independence of (1, τ) (from `(UpperHalfPlane.periodPair τ).indep` via `LinearIndependent.pair_iff`) forces both coefficients to vanish, and integer casts are recovered by `exact_mod_cast`.
- **Hypotheses**: none.
- **Uses from project**: [`UpperHalfPlane.periodPair`]
- **Used by**: `exists_sl2_smul_eq_of_periodPair_homothetic_aux`
- **Visibility**: private
- **Lines**: 459–473 (proof 13 lines)
- **Notes**: none

### `theorem exists_sl2_smul_eq_of_det_mul_eq_one_aux`
- **Type**: `{z w : ℍ} (a b c d k : ℤ) (hdet : (a * d - b * c) * k = 1) (hzval : (z : ℂ) = ((b : ℂ) + a * w) / ((d : ℂ) + c * w)) : ∃ γ : SL(2, ℤ), γ • z = w`
- **What**: If z is a fractional-linear image of w by an integer matrix of determinant ±1 (det divides 1), then z and w are in the same SL₂(ℤ)-orbit; the determinant −1 case is impossible.
- **How**: `Int.eq_one_or_neg_one_of_mul_eq_one'` splits into det = ±1. For det = 1 the matrix !![a,b;c,d] is in SL₂(ℤ) and its action sends w to z (checked on complex coordinates via `UpperHalfPlane.coe_specialLinearGroup_apply`), so its inverse works. For det = −1 the sign-adjusted matrix !![-a,-b;c,d] has determinant 1 but sends w to −z̄-type point with negative imaginary part, contradicting `im_pos`.
- **Hypotheses**: (ad − bc)·k = 1 in ℤ; z = (b + aw)/(d + cw) as complex numbers.
- **Uses from project**: []
- **Used by**: `exists_sl2_smul_eq_of_periodPair_homothetic_aux`
- **Visibility**: private
- **Lines**: 475–504 (proof 26 lines)
- **Notes**: none

### `theorem exists_sl2_smul_eq_of_periodPair_homothetic_aux`
- **Type**: `{z w : ℍ} (h : PeriodPair.Homothetic (UpperHalfPlane.periodPair z) (UpperHalfPlane.periodPair w)) : ∃ γ : SL(2, ℤ), γ • z = w`
- **What**: Forward direction of Cox eq. (7.8): if the normalized lattices [1, z] and [1, w] are homothetic via α, then z and w lie in the same SL₂(ℤ)-orbit.
- **How**: Writes αz = b + aw and α = d + cw (membership of αz, α in ℤ + ℤw via `mem_smul_lattice` and `mem_periodPair_lattice_aux`), and conversely 1, w ∈ α(ℤ + ℤz); substituting and using uniqueness of integer coordinates (`int_comb_injective_aux`) yields the Bézout-type relation (ad − bc)(ps − qr) = 1, so ad − bc = ±1, and z = (b + aw)/(d + cw); `exists_sl2_smul_eq_of_det_mul_eq_one_aux` produces the SL₂(ℤ) element.
- **Hypotheses**: [1, z] and [1, w] are homothetic.
- **Uses from project**: [`Homothetic`, `UpperHalfPlane.periodPair`, `mem_smul_lattice`, `mem_periodPair_lattice_aux`, `int_comb_injective_aux`, `exists_sl2_smul_eq_of_det_mul_eq_one_aux`, `instance : SMul ℂˣ PeriodPair`]
- **Used by**: `periodPair_homothetic_iff_exists_sl2_smul_eq`
- **Visibility**: private
- **Lines**: 506–550 (proof 42 lines)
- **Notes**: proof >30 lines

### `theorem periodPair_homothetic_of_sl2_smul_aux`
- **Type**: `(γ : SL(2, ℤ)) (z : ℍ) : PeriodPair.Homothetic (UpperHalfPlane.periodPair z) (UpperHalfPlane.periodPair (γ • z))`
- **What**: Converse direction of Cox eq. (7.8): acting by γ ∈ SL₂(ℤ) on z produces a homothetic normalized lattice; the homothety factor is (cz + d)⁻¹.
- **How**: With γ = !![a,b;c,d] of determinant 1 (`Matrix.det_fin_two`) and denominator cz + d ≠ 0 (`UpperHalfPlane.denom_ne_zero`, `ModularGroup.denom_apply`), shows (cz+d)⁻¹·(ℤ+ℤz) = ℤ+ℤ(γ·z) by explicit change of ℤ-basis in both directions: (m + nz)/(cz+d) = (ma−nb) + (nd−mc)(γz) and back, verified by `linear_combination` with the determinant identity.
- **Hypotheses**: none.
- **Uses from project**: [`Homothetic`, `UpperHalfPlane.periodPair`, `mem_smul_lattice`, `mem_periodPair_lattice_aux`, `instance : SMul ℂˣ PeriodPair`]
- **Used by**: `periodPair_homothetic_iff_exists_sl2_smul_eq`
- **Visibility**: private
- **Lines**: 552–591 (proof 37 lines)
- **Notes**: proof >30 lines

### `theorem periodPair_homothetic_iff_exists_sl2_smul_eq`
- **Type**: `{z w : ℍ} : PeriodPair.Homothetic (UpperHalfPlane.periodPair z) (UpperHalfPlane.periodPair w) ↔ ∃ γ : SL(2, ℤ), γ • z = w`
- **What**: Cox equation (7.8): homothety of normalized lattices [1, z], [1, w] is exactly the SL₂(ℤ)-orbit relation on the upper half-plane.
- **How**: Combines the two directions `exists_sl2_smul_eq_of_periodPair_homothetic_aux` and `periodPair_homothetic_of_sl2_smul_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`Homothetic`, `UpperHalfPlane.periodPair`, `exists_sl2_smul_eq_of_periodPair_homothetic_aux`, `periodPair_homothetic_of_sl2_smul_aux`]
- **Used by**: `j_eq_iff_exists_sl2_smul_eq`
- **Visibility**: public
- **Lines**: 593–600 (proof 5 lines)
- **Notes**: none

### `theorem j_eq_iff_exists_sl2_smul_eq`
- **Type**: `(τ τ' : ℍ) : j τ = j τ' ↔ ∃ γ : SL(2, ℤ), γ • τ = τ'`
- **What**: Cox Theorem 11.2(ii): the analytic j-function takes equal values at τ, τ' exactly when they are SL₂(ℤ)-equivalent — j separates orbits.
- **How**: Chains the three bridges: j = lattice-j on [1,τ] (`j_eq_periodPair_j`), equal lattice-j ↔ homothety (`PeriodPair.j_eq_iff_homothetic`, Cox 10.9), and homothety of normalized lattices ↔ SL₂(ℤ)-orbit (`periodPair_homothetic_iff_exists_sl2_smul_eq`).
- **Hypotheses**: none.
- **Uses from project**: [`j` (analytic), `j_eq_periodPair_j`, `PeriodPair.j_eq_iff_homothetic`, `periodPair_homothetic_iff_exists_sl2_smul_eq`, `UpperHalfPlane.periodPair`]
- **Used by**: unused in file (top-level result)
- **Visibility**: public
- **Lines**: 602–606 (proof 3 lines)
- **Notes**: none

### `def levelOneWeightZeroCuspForm_aux`
- **Type**: `{f : ℍ → ℂ} (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hmdiff : MDiff f) (hzero : IsZeroAtImInfty f) : CuspForm (Gamma 1) 0`
- **What**: Packages a weight-0 SL₂(ℤ)-invariant holomorphic function vanishing at i∞ as a level-1 weight-0 cusp form.
- **How**: Slash invariance for Γ(1) elements reduces to SL₂(ℤ) invariance; vanishing at every cusp follows from vanishing at i∞ via the project bridge `zero_at_cusps_of_zero_at_infty`, since every SL₂(ℤ)-translate f∣γ equals f.
- **Hypotheses**: f is weight-0 slash-invariant under all of SL₂(ℤ), holomorphic (MDiff), and zero at i∞.
- **Uses from project**: [`zero_at_cusps_of_zero_at_infty` (XYin/PhD/Modularforms/ForMathlib_Cusps.lean)]
- **Used by**: `weight_zero_cuspForm_eq_zero_aux`
- **Visibility**: private
- **Lines**: 608–620 (structure instance, 11 lines)
- **Notes**: none

### `theorem weight_zero_cuspForm_eq_zero_aux`
- **Type**: `{f : ℍ → ℂ} (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hmdiff : MDiff f) (hzero : IsZeroAtImInfty f) : f = 0`
- **What**: A weight-0 level-1 modular function that is holomorphic and vanishes at i∞ is identically zero (weight-0 cusp forms of level 1 vanish).
- **How**: Packages f as a cusp form via `levelOneWeightZeroCuspForm_aux`, applies Mathlib's Liouville-type `ModularForm.eq_const_of_weight_zero` to get f ≡ c, and identifies c = 0 by uniqueness of limits (`tendsto_nhds_unique`) against the vanishing at i∞.
- **Hypotheses**: same as `levelOneWeightZeroCuspForm_aux`.
- **Uses from project**: [`levelOneWeightZeroCuspForm_aux`]
- **Used by**: `j_surjective`
- **Visibility**: private
- **Lines**: 622–630 (proof 7 lines)
- **Notes**: none

### `theorem inv_j_sub_slashInvariant_aux`
- **Type**: `(c : ℂ) : letI f : ℍ → ℂ := fun τ => (j τ - c)⁻¹; ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f`
- **What**: For any constant c, the function 1/(j − c) is weight-0 invariant under SL₂(ℤ).
- **How**: Follows pointwise from the SL₂(ℤ)-invariance of j itself (project lemma `j_slash_invariant`), after simplifying the weight-0 slash action to plain composition via `SL_slash_apply`.
- **Hypotheses**: none.
- **Uses from project**: [`j` (analytic), `j_slash_invariant` (XYin/PhD/jFunction/jfunction.lean)]
- **Used by**: `j_surjective`
- **Visibility**: private
- **Lines**: 632–639 (proof 6 lines)
- **Notes**: statement uses a `letI` binder

### `lemma j_mdifferentiable_aux`
- **Type**: `MDiff j`
- **What**: The analytic j-function is holomorphic on the upper half-plane (as a manifold-differentiable map).
- **How**: Via `UpperHalfPlane.mdifferentiable_iff`, reduces to complex differentiability of j ∘ ofComplex = E₄³/Δ on Im > 0; E₄ and Δ are differentiable there by `ModularFormClass.holo` (through `mdifferentiableAt_iff`), and Δ ≠ 0 by the project's `Δ_ne_zero`, so the quotient rule applies.
- **Hypotheses**: none.
- **Uses from project**: [`j` (analytic), `E4`, `Delta`, `Delta_apply`, `Δ_ne_zero` (XYin/PhD/Modularforms/Delta.lean)]
- **Used by**: `inv_j_sub_mdiff_aux`
- **Visibility**: private
- **Lines**: 641–653 (proof 11 lines)
- **Notes**: none

### `theorem inv_j_sub_mdiff_aux`
- **Type**: `(c : ℂ) (hc : ∀ τ : ℍ, j τ ≠ c) : MDiff (fun τ : ℍ => (j τ - c)⁻¹)`
- **What**: If j omits the value c, then 1/(j − c) is holomorphic on the upper half-plane.
- **How**: Pointwise: j is MDifferentiable (`j_mdifferentiable_aux`), subtracting the constant preserves this, and the inverse is differentiable since j(τ) − c ≠ 0 by hypothesis (`MDifferentiableAt.inv` with `sub_ne_zero`).
- **Hypotheses**: j never takes the value c.
- **Uses from project**: [`j` (analytic), `j_mdifferentiable_aux`]
- **Used by**: `j_surjective`
- **Visibility**: private
- **Lines**: 655–658 (term-mode proof, 3 lines)
- **Notes**: none

### `lemma E4_tendsto_atImInfty_aux`
- **Type**: `Tendsto (E4 : ℍ → ℂ) atImInfty (nhds 1)`
- **What**: E₄(τ) → 1 as Im τ → ∞ (its q-expansion has constant term 1).
- **How**: E₄ is 1-periodic (`SlashInvariantFormClass.periodic_comp_ofComplex`), so E₄ = cuspFunction ∘ q with q = e^{2πiτ}; the cusp function is continuous at 0 (`ModularFormClass.analyticAt_cuspFunction_zero`) with value 1 by the Eisenstein constant-term computation `EisensteinSeries.E_qExpansion_coeff_zero`, and q → 0 at i∞ (`UpperHalfPlane.qParam_tendsto_atImInfty`).
- **Hypotheses**: none.
- **Uses from project**: [`E4`]
- **Used by**: `qj_tendsto_atImInfty_aux`
- **Visibility**: private
- **Lines**: 660–669 (proof 9 lines)
- **Notes**: none

### `lemma qj_tendsto_atImInfty_aux`
- **Type**: `Tendsto qj atImInfty (nhds 1)`
- **What**: The function qj = q·j (the q-expansion of j shifted to kill the pole) tends to 1 at i∞, encoding that j has a simple pole with residue-coefficient 1 in q.
- **How**: Factors qj = E₄³ · (q/Δ) via the project identity `E4_pow_three_mul_qOverDelta_eq_qj`; E₄³ → 1 by `E4_tendsto_atImInfty_aux` and q/Δ → 1 by the project lemma `qOverDelta_tendsto_atImInfty`, so the product tends to 1.
- **Hypotheses**: none.
- **Uses from project**: [`qj`, `qOverDelta`, `E4`, `E4_tendsto_atImInfty_aux`, `E4_pow_three_mul_qOverDelta_eq_qj` (jfunction.lean), `qOverDelta_tendsto_atImInfty` (jfunction.lean)]
- **Used by**: `inv_j_sub_isZeroAtImInfty_aux`
- **Visibility**: private
- **Lines**: 671–679 (proof 8 lines)
- **Notes**: none

### `theorem inv_j_sub_isZeroAtImInfty_aux`
- **Type**: `(c : ℂ) : IsZeroAtImInfty (fun τ : ℍ => (j τ - c)⁻¹)`
- **What**: For any constant c, the function 1/(j − c) tends to 0 as Im τ → ∞, because j blows up like 1/q at the cusp.
- **How**: Rewrites 1/(j − c) = q/(qj − cq) using qj = q·j and q ≠ 0; the denominator tends to 1 (by `qj_tendsto_atImInfty_aux` and q → 0 via `UpperHalfPlane.qParam_tendsto_atImInfty`) while the numerator q tends to 0, so the ratio tends to 0 (`Tendsto.congr'` on an eventual equality).
- **Hypotheses**: none.
- **Uses from project**: [`j` (analytic), `qj`, `qj_tendsto_atImInfty_aux`]
- **Used by**: `j_surjective`
- **Visibility**: private
- **Lines**: 681–696 (proof 14 lines)
- **Notes**: uses the local notation `𝕢` for `Periodic.qParam`

### `theorem j_surjective`
- **Type**: `Function.Surjective j`
- **What**: Cox Theorem 11.2(iii): the analytic modular j-function is surjective onto ℂ.
- **How**: If j omitted a value c, then 1/(j − c) would be a holomorphic weight-0 SL₂(ℤ)-invariant function vanishing at i∞ (by the three aux lemmas), hence identically zero by `weight_zero_cuspForm_eq_zero_aux` — contradicting that its value at τ = i is the inverse of the nonzero number j(i) − c.
- **Hypotheses**: none.
- **Uses from project**: [`j` (analytic), `weight_zero_cuspForm_eq_zero_aux`, `inv_j_sub_slashInvariant_aux`, `inv_j_sub_mdiff_aux`, `inv_j_sub_isZeroAtImInfty_aux`]
- **Used by**: unused in file (top-level result)
- **Visibility**: public
- **Lines**: 698–705 (proof 7 lines)
- **Notes**: none

### File Summary
- Total declarations: 55 (7 defs, 47 lemmas/theorems, 1 instance, 0 tactic/meta decls)
- Key API (used by 3+ others): `instance : SMul ℂˣ PeriodPair`, `PeriodPair.Homothetic`, `PeriodPair.discriminant`, `PeriodPair.j`, `PeriodPair.mem_smul_lattice`, `PeriodPair.g₂_smul`, `PeriodPair.g₃_smul`, `PeriodPair.discriminant_ne_zero`, `UpperHalfPlane.periodPair`
- Unused declarations (not used by anything in this file): `PeriodPair.coe_smulLatticeEquiv_apply`, `PeriodPair.coe_smulLatticeEquiv_symm_apply`, `j_eq_iff_exists_sl2_smul_eq` (top-level result), `j_surjective` (top-level result)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `exists_homothetic_periodPair` (37), `PeriodPair.homothetic_of_j_eq_of_g₂_ne_zero_of_g₃_ne_zero_aux` (38), `exists_sl2_smul_eq_of_periodPair_homothetic_aux` (42), `periodPair_homothetic_of_sl2_smul_aux` (37)
