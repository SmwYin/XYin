# Inventory: XYin/PhD/Cox/CyclicSublattice/Classification.lean  (370 lines)

Cox Lemma 11.24 and Theorem 11.23: cyclic index-`m` sublattices of any period lattice `L` are in bijection with Cox matrices `C(m)` (`Cox.CoxMatrix m`, `CoxMatrices/Basic.lean:24`: `a, b, d` with `ad = m`, `0 ≤ b < d`, `gcd(a,b,d) = 1`) via the HNF inclusion matrix `!![d, b; 0, a]`; for `L = [1,τ]` the sublattice of `σ` is `[d, aτ + b] = d·[1, στ]` so its `j` is `j(στ)`; hence the roots of `Φ_m(X, j(τ))` are exactly the `j`-invariants of cyclic sublattices, and `Φ_m(u, v) = 0 ↔ ∃ L, S ⊂ L cyclic of index m, u = j(S), v = j(L)`. Consumed by `Cox/Arithmetic.lean:42–44` (symmetry of `Φ_m`).

## Declarations

### `noncomputable def PeriodPair.CyclicSublattice.toCoxMatrix`
- **Type**: `(S : CyclicSublattice L m) : Cox.CoxMatrix m`
- **What**: the Cox representative `(a, b, d) = (|A 1 1|, |A 0 1|, |A 0 0|)` read off the HNF matrix `A` of `S`.
- **How**: tactic-mode definition: `a_pos` from `diagonal_pos`; `determinant : a * d = m` from `HermiteNormalForm.index_eq_natAbs_det` + `S.index_eq` + `Matrix.det_fin_two`, `Int.natAbs_mul`; `b_lt` from `reduced` via `Int.natAbs_lt_natAbs_of_nonneg_of_lt`; `primitive` from `quotient_isAddCyclic_iff_rankTwoContent_eq_one` + the AC-gcd simp.
- **Hypotheses**: none.
- **Uses from project**: `CyclicSublattice`, `hermiteNormalForm`, `Matrix.IsColumnHermiteNormalForm` (fields), `Module.Basis.HermiteNormalForm.index_eq_natAbs_det`, `Matrix.rankTwoContent`, `Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`, `Cox.CoxMatrix`
- **Used by**: `hermiteNormalForm_matrix_eq_inclusionMatrix` (60), `toCoxMatrix_inclusionMatrix` (79), `toCyclicSublatticeOfPeriodPair_toCoxMatrix` (149), `toCoxMatrix_toCyclicSublatticeOfPeriodPair` (158), `cyclicSublatticeEquivCoxMatrixOfPeriodPair` (172), `modularPolynomialC_zero_iff_normalizedCyclicSublattice` (339)
- **Visibility**: public
- **Lines**: 28–55, body ≈ 27 lines
- **Notes**: a `def` built with `by … exact { … }` (style; L74 `simp [toCoxMatrix, …]` must unfold through the tactic block). `hmul` (37–40) and `hprimitive` (43–47) re-derive `CyclicSublattice.lean:306 d_mul_a_eq_m` and `:470 dual_content_eq_one` because those are private.

### `theorem PeriodPair.CyclicSublattice.hermiteNormalForm_matrix_eq_inclusionMatrix`
- **Type**: `(S) : S.hermiteNormalForm.matrix = S.toCoxMatrix.inclusionMatrix`
- **What**: the HNF matrix is the inclusion matrix `!![d, b; 0, a]` (`CoxMatrices/Basic.lean:56`) of the extracted Cox representative.
- **How**: `ext`, `fin_cases`, `simp [toCoxMatrix, inclusionMatrix, abs_of_nonneg, hz]` (casts `↑(natAbs x) = |x|` with nonnegativity from `diagonal_pos`/`reduced`).
- **Hypotheses**: none.
- **Uses from project**: `toCoxMatrix`, `hermiteNormalForm`, `Cox.CoxMatrix.inclusionMatrix`, `Matrix.IsColumnHermiteNormalForm` (fields)
- **Used by**: `toCoxMatrix_inclusionMatrix` (80), `toCoxMatrix_toCyclicSublatticeOfPeriodPair` (163), `cyclicSublattice_hnf_matrix` (292)
- **Visibility**: public
- **Lines**: 59–75, proof ≈ 15 lines
- **Notes**: —

### `theorem PeriodPair.CyclicSublattice.toCoxMatrix_inclusionMatrix`
- **Type**: `(S) : S.toCoxMatrix.inclusionMatrix = S.hermiteNormalForm.matrix`
- **What**: symmetric form of the previous (simp-normal orientation).
- **How**: `.symm`.
- **Hypotheses**: none.
- **Uses from project**: `hermiteNormalForm_matrix_eq_inclusionMatrix`
- **Used by**: `toCyclicSublatticeOfPeriodPair_toCoxMatrix` (151)
- **Visibility**: public, `@[simp]`
- **Lines**: 78–80
- **Notes**: —

### `private def Cox.CoxMatrix.inclusionLinearMap`
- **Type**: `(σ : CoxMatrix m) (L : PeriodPair) : L.lattice →ₗ[ℤ] L.lattice := Matrix.toLin L.latticeBasis L.latticeBasis σ.inclusionMatrix`
- **What**: the endomorphism of `L` with matrix `!![d, b; 0, a]` in the period basis (its image is the sublattice `[dω₁, bω₁ + aω₂]`).
- **How**: `Matrix.toLin`.
- **Hypotheses**: none.
- **Uses from project**: `Cox.CoxMatrix.inclusionMatrix`
- **Used by**: `inclusionLinearMap_injective`, `sublatticeOfPeriodPair`, `inclusionHermiteNormalForm`, `sublattice_eq_span`
- **Visibility**: private
- **Lines**: 94–96
- **Notes**: —

### `private theorem Cox.CoxMatrix.inclusionLinearMap_injective`
- **Type**: `(σ) (L) : Function.Injective (σ.inclusionLinearMap L)`
- **What**: the inclusion endomorphism is injective (`det = m ≠ 0`).
- **How**: `LinearMap.det_toMatrix` (mathlib `LinearAlgebra/Determinant.lean:205`), `LinearMap.toMatrix_toLin`, `σ.inclusionMatrix_det` (`CoxMatrices/Basic.lean:67`), then `LinearMap.det_eq_zero_iff_ker_ne_bot` (`Determinant.lean:351`) + `LinearMap.ker_eq_bot`.
- **Hypotheses**: none.
- **Uses from project**: `inclusionLinearMap`, `Cox.CoxMatrix.inclusionMatrix`, `Cox.CoxMatrix.inclusionMatrix_det`
- **Used by**: `inclusionHermiteNormalForm` (123)
- **Visibility**: private
- **Lines**: 98–110, proof ≈ 11 lines
- **Notes**: same "det ≠ 0 ⇒ injective" skeleton as `HermiteNormalForm.lean:376–389`.

### `def Cox.CoxMatrix.sublatticeOfPeriodPair`
- **Type**: `(σ : CoxMatrix m) (L : PeriodPair) : Submodule ℤ L.lattice := LinearMap.range (σ.inclusionLinearMap L)`
- **What**: the sublattice generated by the columns of `σ.inclusionMatrix` in `L`.
- **How**: `LinearMap.range`.
- **Hypotheses**: none.
- **Uses from project**: `inclusionLinearMap`
- **Used by**: `inclusionHermiteNormalForm`, `toCyclicSublatticeOfPeriodPair`, `CoxMatrix.sublattice`
- **Visibility**: public
- **Lines**: 113–115
- **Notes**: exposes a private def in a public statement (`inclusionLinearMap` is private, so the definition cannot be unfolded by users).

### `private noncomputable def Cox.CoxMatrix.inclusionHermiteNormalForm`
- **Type**: `(σ) (L) : Module.Basis.HermiteNormalForm L.latticeBasis (σ.sublatticeOfPeriodPair L)`
- **What**: an explicit HNF for `σ`'s sublattice with matrix `σ.inclusionMatrix`.
- **How**: basis `L.latticeBasis.map (LinearEquiv.ofInjective f _)` (mathlib `Submodule/Equiv.lean:167`); `toMatrix_eq` by `LinearMap.toMatrix_map_left` (`ToLin.lean:699`) + `LinearMap.toMatrix_toLin`; HNF-ness from `inclusionMatrix_isColumnHermiteNormalForm` (`CoxMatrices/Basic.lean:59`).
- **Hypotheses**: none.
- **Uses from project**: `inclusionLinearMap`, `inclusionLinearMap_injective`, `sublatticeOfPeriodPair`, `Module.Basis.HermiteNormalForm`, `Cox.CoxMatrix.inclusionMatrix`, `Cox.CoxMatrix.inclusionMatrix_isColumnHermiteNormalForm`
- **Used by**: `toCyclicSublatticeOfPeriodPair` (135), `toCyclicSublatticeOfPeriodPair_toCoxMatrix` (153)
- **Visibility**: private
- **Lines**: 117–130, body ≈ 12 lines
- **Notes**: the basis construction duplicates `CyclicSublattice.lean:348 dualBasis`.

### `noncomputable def Cox.CoxMatrix.toCyclicSublatticeOfPeriodPair`
- **Type**: `(σ : CoxMatrix m) (L : PeriodPair) : PeriodPair.CyclicSublattice L m`
- **What**: Lemma 11.24 converse: a Cox matrix yields a cyclic index-`m` sublattice of any `L`.
- **How**: carrier `sublatticeOfPeriodPair`; index via `HermiteNormalForm.index_eq_natAbs_det` and `inclusionMatrix_det`; cyclicity via `quotient_isAddCyclic_iff_rankTwoContent_eq_one` and `inclusionMatrix_content_eq_one` (`CoxMatrices/Basic.lean:74`).
- **Hypotheses**: none.
- **Uses from project**: `inclusionHermiteNormalForm`, `sublatticeOfPeriodPair`, `Module.Basis.HermiteNormalForm.index_eq_natAbs_det`, `Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`, `Matrix.rankTwoContent`, `Cox.CoxMatrix.inclusionMatrix_det`, `Cox.CoxMatrix.inclusionMatrix_content_eq_one`, `PeriodPair.CyclicSublattice`
- **Used by**: `toCyclicSublatticeOfPeriodPair_toCoxMatrix`, `toCoxMatrix_toCyclicSublatticeOfPeriodPair`, `cyclicSublatticeEquivCoxMatrixOfPeriodPair`, `CoxMatrix.toCyclicSublattice`
- **Visibility**: public
- **Lines**: 133–144, body ≈ 10 lines
- **Notes**: tactic-mode def.

### `theorem Cox.CoxMatrix.toCyclicSublatticeOfPeriodPair_toCoxMatrix`
- **Type**: `(σ) (L) : (σ.toCyclicSublatticeOfPeriodPair L).toCoxMatrix = σ`
- **What**: round trip `C(m) → sublattices → C(m)` is the identity.
- **How**: `CoxMatrix.inclusionMatrix_injective` (`CoxMatrices/Basic.lean:288`), `toCoxMatrix_inclusionMatrix`, and HNF uniqueness `HermiteNormalForm.matrix_eq` (`HermiteNormalForm.lean:241`) between the chosen HNF and `inclusionHermiteNormalForm`.
- **Hypotheses**: none.
- **Uses from project**: `toCyclicSublatticeOfPeriodPair`, `toCoxMatrix`, `Cox.CoxMatrix.inclusionMatrix_injective`, `toCoxMatrix_inclusionMatrix`, `hermiteNormalForm`, `Module.Basis.HermiteNormalForm.matrix_eq`, `inclusionHermiteNormalForm`
- **Used by**: `cyclicSublatticeEquivCoxMatrixOfPeriodPair` (175)
- **Visibility**: public, `@[simp]`
- **Lines**: 147–153, proof ≈ 4 lines
- **Notes**: —

### `theorem Cox.CoxMatrix.toCoxMatrix_toCyclicSublatticeOfPeriodPair`
- **Type**: `(S : PeriodPair.CyclicSublattice L m) : S.toCoxMatrix.toCyclicSublatticeOfPeriodPair L = S`
- **What**: round trip `sublattices → C(m) → sublattices` is the identity.
- **How**: `CyclicSublattice.ext`; the carrier is `range (toLin b b (inclusionMatrix))` = `range (toLin b b (HNF matrix))` = `S.carrier` by `hermiteNormalForm_matrix_eq_inclusionMatrix` and `HermiteNormalForm.range_toLin_matrix_eq` (`HermiteNormalForm.lean:212`).
- **Hypotheses**: none.
- **Uses from project**: `toCyclicSublatticeOfPeriodPair`, `toCoxMatrix`, `PeriodPair.CyclicSublattice.ext`, `hermiteNormalForm_matrix_eq_inclusionMatrix`, `hermiteNormalForm`, `Module.Basis.HermiteNormalForm.range_toLin_matrix_eq`, `Cox.CoxMatrix.inclusionMatrix`
- **Used by**: `cyclicSublatticeEquivCoxMatrixOfPeriodPair` (174), `modularPolynomialC_zero_iff_normalizedCyclicSublattice` (342)
- **Visibility**: public, `@[simp]`
- **Lines**: 156–164, proof ≈ 6 lines
- **Notes**: —

### `noncomputable def Cox.cyclicSublatticeEquivCoxMatrixOfPeriodPair`
- **Type**: `(L : PeriodPair) (m : ℕ+) : PeriodPair.CyclicSublattice L m ≃ CoxMatrix m`
- **What**: Cox Lemma 11.24 for an arbitrary period lattice: cyclic index-`m` sublattices ≃ `C(m)`.
- **How**: `toCoxMatrix` / `toCyclicSublatticeOfPeriodPair` with the two round-trip lemmas.
- **Hypotheses**: none.
- **Uses from project**: `toCoxMatrix`, `toCyclicSublatticeOfPeriodPair`, `toCoxMatrix_toCyclicSublatticeOfPeriodPair`, `toCyclicSublatticeOfPeriodPair_toCoxMatrix`, `PeriodPair.CyclicSublattice`, `Cox.CoxMatrix`
- **Used by**: `cyclicSublatticeEquivCoxMatrix` (284)
- **Visibility**: public
- **Lines**: 169–175
- **Notes**: gives `Fintype (CyclicSublattice L m)` via `Fintype.ofEquiv` — not registered.

### `noncomputable def Cox.CoxMatrix.sublattice`
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : Submodule ℤ (UpperHalfPlane.periodPair τ).lattice := σ.sublatticeOfPeriodPair (periodPair τ)`
- **What**: the carrier `[d, aτ + b]` in the normalised lattice `[1, τ]`.
- **How**: specialisation.
- **Hypotheses**: none.
- **Uses from project**: `sublatticeOfPeriodPair`, `UpperHalfPlane.periodPair`
- **Used by**: `toCyclicSublattice_carrier`, `sublattice_eq_span`, `sublattice_map_subtype`, `coxMatrix_toPeriodPair_lattice`
- **Visibility**: public
- **Lines**: 178–180
- **Notes**: one-line alias.

### `noncomputable def Cox.CoxMatrix.toCyclicSublattice`
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : PeriodPair.CyclicSublattice (UpperHalfPlane.periodPair τ) m`
- **What**: the cyclic sublattice of `[1,τ]` attached to `σ`.
- **How**: specialisation of `toCyclicSublatticeOfPeriodPair`.
- **Hypotheses**: none.
- **Uses from project**: `toCyclicSublatticeOfPeriodPair`, `UpperHalfPlane.periodPair`
- **Used by**: `toCyclicSublattice_carrier`, `coxMatrix_toPeriodPair_lattice`, `toCyclicSublattice_j`, `modularPolynomialC_zero_iff_normalizedCyclicSublattice`
- **Visibility**: public
- **Lines**: 184–186
- **Notes**: one-line alias.

### `theorem Cox.CoxMatrix.toCyclicSublattice_carrier`
- **Type**: `(σ) (τ) : (σ.toCyclicSublattice τ).carrier = σ.sublattice τ`
- **What**: carrier of the attached sublattice.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `toCyclicSublattice`, `sublattice`
- **Used by**: unused in file
- **Visibility**: public, `@[simp]`
- **Lines**: 189–192
- **Notes**: unused project-wide (L301–303 goes through the defeq without it).

### `private def Cox.CoxMatrix.sublatticeGenerators`
- **Type**: `(σ) (τ) : Fin 2 → (periodPair τ).lattice := ![d • e₀, b • e₀ + a • e₁]` (with `e = (periodPair τ).latticeBasis`)
- **What**: the two generators `d·1`, `b·1 + a·τ` inside the lattice.
- **How**: vector literal.
- **Hypotheses**: none.
- **Uses from project**: `UpperHalfPlane.periodPair`, `Cox.CoxMatrix`
- **Used by**: `sublattice_eq_span`, `coe_sublatticeGenerators`
- **Visibility**: private
- **Lines**: 194–199
- **Notes**: —

### `private theorem Cox.CoxMatrix.sublattice_eq_span`
- **Type**: `(σ) (τ) : σ.sublattice τ = Submodule.span ℤ (Set.range (σ.sublatticeGenerators τ))`
- **What**: the range of the inclusion map is the span of the two generators.
- **How**: `LinearMap.range = map ⊤`, `Basis.span_eq`, `Submodule.map_span`, `Set.range_comp`; then `Matrix.toLin_self` and `fin_cases`/`simp [inclusionMatrix]` to evaluate on basis vectors.
- **Hypotheses**: none.
- **Uses from project**: `sublattice`, `inclusionLinearMap`, `sublatticeGenerators`, `Cox.CoxMatrix.inclusionMatrix`, `UpperHalfPlane.periodPair`
- **Used by**: `sublattice_map_subtype` (249)
- **Visibility**: private
- **Lines**: 201–218, proof ≈ 16 lines
- **Notes**: generic fact "range of `toLin b b A` = span of `A`'s columns in `b`" — mathlib `Matrix.range_toLin`/`Matrix.toLin_apply` route; would generalise `HermiteNormalForm.range_toLin_matrix_eq`.

### `private def Cox.CoxMatrix.complexSublatticeGenerators`
- **Type**: `(σ) (τ) : Fin 2 → ℂ := ![(d : ℂ), (b : ℂ) + (a : ℂ) * τ]`
- **What**: the same generators as complex numbers.
- **How**: vector literal.
- **Hypotheses**: none.
- **Uses from project**: `Cox.CoxMatrix`
- **Used by**: `coe_sublatticeGenerators`, `sublattice_map_subtype`, `range_complexSublatticeGenerators`, `complexSublatticeSpan_eq_scaledLattice`, `coxMatrix_toPeriodPair_lattice`
- **Visibility**: private
- **Lines**: 220–222
- **Notes**: —

### `private theorem Cox.CoxMatrix.coe_sublatticeGenerators`
- **Type**: `(σ) (τ) (i : Fin 2) : ((σ.sublatticeGenerators τ i : (periodPair τ).lattice) : ℂ) = σ.complexSublatticeGenerators τ i`
- **What**: coercion of the lattice generators gives the complex generators.
- **How**: local `rfl` facts `hcoe_add`, `hcoe_zsmul`; `latticeBasis_zero/one`; `simp [periodPair, zsmul_eq_mul]`; `fin_cases`.
- **Hypotheses**: none.
- **Uses from project**: `sublatticeGenerators`, `complexSublatticeGenerators`, `UpperHalfPlane.periodPair`
- **Used by**: `sublattice_map_subtype` (253)
- **Visibility**: private
- **Lines**: 224–243, proof ≈ 18 lines
- **Notes**: the `hcoe_add`/`hcoe_zsmul` rfl-lemmas are `Submodule.coe_add`/`Submodule.coe_smul` (mathlib simp lemmas) restated locally; the HEAD version had them as private lemmas `coe_carrier_add`/`coe_carrier_zsmul` in `CyclicSublattice.lean` (removed).

### `private theorem Cox.CoxMatrix.sublattice_map_subtype`
- **Type**: `(σ) (τ) : (σ.sublattice τ).map (periodPair τ).lattice.subtype = Submodule.span ℤ (Set.range (σ.complexSublatticeGenerators τ))`
- **What**: embedded in ℂ, `σ`'s sublattice is `span {d, b + aτ}`.
- **How**: `sublattice_eq_span`, `Submodule.map_span`, `Set.range_comp`, `coe_sublatticeGenerators`.
- **Hypotheses**: none.
- **Uses from project**: `sublattice`, `sublattice_eq_span`, `complexSublatticeGenerators`, `coe_sublatticeGenerators`, `UpperHalfPlane.periodPair`
- **Used by**: `coxMatrix_toPeriodPair_lattice` (306)
- **Visibility**: private
- **Lines**: 245–253, proof ≈ 5 lines
- **Notes**: —

### `private theorem Cox.CoxMatrix.range_complexSublatticeGenerators`
- **Type**: `(σ) (τ) : Set.range (σ.complexSublatticeGenerators τ) = ({(d : ℂ), (b : ℂ) + (a : ℂ) * τ} : Set ℂ)`
- **What**: range of the 2-vector is the pair set.
- **How**: mathlib `Matrix.range_cons_cons_empty` (`Data/Fin/VecNotation.lean:254`).
- **Hypotheses**: none.
- **Uses from project**: `complexSublatticeGenerators`
- **Used by**: `complexSublatticeSpan_eq_scaledLattice` (278)
- **Visibility**: private
- **Lines**: 255–259, proof ≈ 1 line
- **Notes**: one-line wrapper around a single mathlib call.

### `private theorem Cox.CoxMatrix.complexSublatticeSpan_eq_scaledLattice`
- **Type**: `(σ) (τ) : Submodule.span ℤ (Set.range (σ.complexSublatticeGenerators τ)) = ((Units.mk0 (σ.d : ℂ) _) • UpperHalfPlane.periodPair (σ.act τ)).lattice`
- **What**: `span {d, b + aτ} = d · [1, στ]` where `στ = (aτ + b)/d` (`CoxMatrix.act`, `CoxMatrices/Basic.lean:80`).
- **How**: compute `ω₁ = d`, `ω₂ = d·(aτ+b)/d = b + aτ` of the scaled pair via `PeriodPair.smul_ω₂`, `CoxMatrix.coe_act`, `field_simp`, `ring`; unfold `PeriodPair.lattice`; `range_complexSublatticeGenerators`.
- **Hypotheses**: none.
- **Uses from project**: `complexSublatticeGenerators`, `range_complexSublatticeGenerators`, `PeriodPair.smul_ω₂` (and `smul_ω₁` via simp), `Cox.CoxMatrix.coe_act`, `Cox.CoxMatrix.act`, `Cox.CoxMatrix.d_pos`, `UpperHalfPlane.periodPair`, `instance SMul ℂˣ PeriodPair`
- **Used by**: `coxMatrix_toPeriodPair_lattice` (307)
- **Visibility**: private
- **Lines**: 261–278, proof ≈ 16 lines
- **Notes**: —

### `noncomputable def Cox.cyclicSublatticeEquivCoxMatrix`
- **Type**: `(m : ℕ+) (τ : ℍ) : PeriodPair.CyclicSublattice (UpperHalfPlane.periodPair τ) m ≃ CoxMatrix m`
- **What**: Cox Lemma 11.24 for `[1,τ]`.
- **How**: specialisation of `cyclicSublatticeEquivCoxMatrixOfPeriodPair`.
- **Hypotheses**: none.
- **Uses from project**: `cyclicSublatticeEquivCoxMatrixOfPeriodPair`, `UpperHalfPlane.periodPair`
- **Used by**: `cyclicSublattice_hnf_matrix` (291)
- **Visibility**: public
- **Lines**: 282–284
- **Notes**: one-line alias.

### `theorem Cox.cyclicSublattice_hnf_matrix`
- **Type**: `(m) (τ) (S : CyclicSublattice (periodPair τ) m) : S.hermiteNormalForm.matrix = (cyclicSublatticeEquivCoxMatrix m τ S).inclusionMatrix`
- **What**: the HNF matrix of a cyclic sublattice of `[1,τ]` is `!![d, b; 0, a]` of its Cox representative.
- **How**: `hermiteNormalForm_matrix_eq_inclusionMatrix`.
- **Hypotheses**: none.
- **Uses from project**: `cyclicSublatticeEquivCoxMatrix`, `hermiteNormalForm_matrix_eq_inclusionMatrix`, `hermiteNormalForm`, `Cox.CoxMatrix.inclusionMatrix`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 288–292, proof ≈ 1 line
- **Notes**: unused project-wide; one-line restatement.

### `theorem Cox.coxMatrix_toPeriodPair_lattice`
- **Type**: `(m) (τ) (σ : CoxMatrix m) : (σ.toCyclicSublattice τ).toPeriodPair.lattice = ((Units.mk0 (σ.d : ℂ) _) • UpperHalfPlane.periodPair (σ.act τ)).lattice`
- **What**: the canonical period lattice of `σ`'s sublattice is `d · [1, στ]` (Cox: `[d, aτ+b] = d[1, στ]`).
- **How**: `calc`: `toPeriodPair_lattice` (`CyclicSublattice.lean:106`), `sublattice_map_subtype`, `complexSublatticeSpan_eq_scaledLattice`.
- **Hypotheses**: none.
- **Uses from project**: `toCyclicSublattice`, `PeriodPair.CyclicSublattice.toPeriodPair`, `PeriodPair.CyclicSublattice.toPeriodPair_lattice`, `sublattice`, `sublattice_map_subtype`, `complexSublatticeGenerators`, `complexSublatticeSpan_eq_scaledLattice`, `Cox.CoxMatrix.act`, `Cox.CoxMatrix.d_pos`, `UpperHalfPlane.periodPair`
- **Used by**: `toCyclicSublattice_j` (318)
- **Visibility**: public
- **Lines**: 295–307, proof ≈ 9 lines
- **Notes**: —

### `theorem Cox.CoxMatrix.toCyclicSublattice_j`
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : (σ.toCyclicSublattice τ).j = j (σ.act τ)`
- **What**: the sublattice attached to `σ` has `j`-invariant `j(στ)` (the root of `Φ_m(X, j(τ))` indexed by `σ`).
- **How**: `PeriodPair.j_congr` (via `coxMatrix_toPeriodPair_lattice`), `PeriodPair.j_smul`, `j_eq_periodPair_j` (`LatticeJ.lean:221`).
- **Hypotheses**: none.
- **Uses from project**: `toCyclicSublattice`, `PeriodPair.CyclicSublattice.j`, `coxMatrix_toPeriodPair_lattice`, `PeriodPair.j_congr`, `PeriodPair.j_smul`, `j_eq_periodPair_j`, `j`, `Cox.CoxMatrix.act`, `Cox.CoxMatrix.d_pos`, `UpperHalfPlane.periodPair`
- **Used by**: `modularPolynomialC_zero_iff_normalizedCyclicSublattice` (337, 340)
- **Visibility**: public
- **Lines**: 311–321, proof ≈ 8 lines
- **Notes**: —

### `theorem Cox.modularPolynomialC_zero_iff_normalizedCyclicSublattice`
- **Type**: `(m : ℕ+) (τ : ℍ) (u : ℂ) : (modularPolynomialC m).eval u (j τ) = 0 ↔ ∃ S : CyclicSublattice (periodPair τ) m, u = S.j`
- **What**: Theorem 11.23 over a normalised lattice: `u` is a root of `Φ_m(X, j(τ))` iff `u = j(L')` for a cyclic index-`m` sublattice `L' ⊂ [1,τ]`.
- **How**: `BivariatePolynomial.specializeY_eval` (`ModularPolynomial/Construction.lean:70`), `modularPolynomialC_specializeY` (`:350`), `coxPhiAtJ = ∏_{σ} (X − C (j (σ.act τ)))` (`:59`), `Polynomial.eval_prod`, `Finset.prod_eq_zero_iff`; forward via `toCyclicSublattice_j`, backward via `toCoxMatrix` and `toCoxMatrix_toCyclicSublatticeOfPeriodPair`.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialC`, `modularPolynomialC_specializeY`, `coxPhiAtJ`, `BivariatePolynomial.specializeY_eval`, `j`, `toCyclicSublattice`, `toCyclicSublattice_j`, `toCoxMatrix`, `toCoxMatrix_toCyclicSublatticeOfPeriodPair`, `PeriodPair.CyclicSublattice.j`, `UpperHalfPlane.periodPair`
- **Used by**: `theorem_11_23` (354, 367)
- **Visibility**: public
- **Lines**: 324–342, proof ≈ 17 lines
- **Notes**: `classical` at 329.

### `theorem Cox.theorem_11_23`
- **Type**: `(m : ℕ+) (u v : ℂ) : (BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m)).eval u v = 0 ↔ ∃ L : PeriodPair, ∃ S : CyclicSublattice L m, u = S.j ∧ v = L.j`
- **What**: Cox Theorem 11.23: the zeros of the integral modular polynomial `Φ_m` over ℂ are exactly the pairs `(j(L'), j(L))` with `L' ⊂ L` cyclic of index `m`.
- **How**: `modularPolynomial_map_complex` (`ModularPolynomial/IntegralDescent.lean:290`); `→`: `j_surjective` gives `v = j τ`, then the normalised theorem with `L = [1,τ]`; `←`: `exists_homothetic_periodPair` (`LatticeJ.lean:235`) gives `a • L = [1,τ]`, transport `S` by `scale a` then `ofLatticeEq`, `j_ofLatticeEq`, `j_scale`, `j_eq_of_homothetic`, `j_eq_periodPair_j`, and apply the normalised theorem.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomial`, `modularPolynomial_map_complex`, `BivariatePolynomial.map`, `modularPolynomialC_zero_iff_normalizedCyclicSublattice`, `j_surjective`, `j_eq_periodPair_j`, `exists_homothetic_periodPair`, `PeriodPair.CyclicSublattice.scale`, `PeriodPair.CyclicSublattice.ofLatticeEq`, `PeriodPair.CyclicSublattice.j_ofLatticeEq`, `PeriodPair.CyclicSublattice.j_scale`, `PeriodPair.j_eq_of_homothetic`, `PeriodPair.CyclicSublattice.j`, `PeriodPair.j`, `UpperHalfPlane.periodPair`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 345–368, proof ≈ 22 lines
- **Notes**: external uses `Cox/Arithmetic.lean:42–43` (symmetry `Φ_m(u,v) = 0 ↔ Φ_m(v,u) = 0` via `dual`). Name is a theorem number, not descriptive (`modularPolynomial_eval_eq_zero_iff_exists_cyclicSublattice`).

## File Summary
- Total declarations: 27 (11 defs, 16 theorems, 0 instances, 0 other); 10 private
- Key API (used by 3+ others in the file): `toCoxMatrix` (6), `hermiteNormalForm_matrix_eq_inclusionMatrix` (3), `inclusionLinearMap` (4), `sublatticeOfPeriodPair` (3), `toCyclicSublatticeOfPeriodPair` (4), `CoxMatrix.sublattice` (4), `CoxMatrix.toCyclicSublattice` (4), `complexSublatticeGenerators` (5)
- Unused declarations (not used by anything in this file): `CoxMatrix.toCyclicSublattice_carrier` (unused project-wide), `cyclicSublattice_hnf_matrix` (unused project-wide), `theorem_11_23` (used by `Arithmetic.lean`)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: `toCoxMatrix` ≈27 body, `theorem_11_23` ≈22)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `inclusionLinearMap_injective` (L98–110) and `HermiteNormalForm.lean:376–389` both prove "`Matrix.toLin b b A` is injective when `det A ≠ 0`" from `LinearMap.det_toMatrix` (`Mathlib/LinearAlgebra/Determinant.lean:205`) + `LinearMap.det_eq_zero_iff_ker_ne_bot` (`:351`). No single mathlib lemma states it for `Matrix.toLin` over a domain (mathlib has `Matrix.toLinearEquiv` only for `IsUnit det`, `ToLinearEquiv.lean:83`); add one project lemma.
- `sublattice_eq_span` (L201–218): "range of `toLin b b A` is the span of `A`'s columns expressed in `b`" — a general `Matrix.range_toLin_eq_span` (mathlib has `Matrix.range_toLin'`-style results only for `toLin'`) would also subsume `HermiteNormalForm.range_toLin_matrix_eq`.
- `coe_sublatticeGenerators` (L224–243): the local `hcoe_add`/`hcoe_zsmul` are `Submodule.coe_add`/`Submodule.coe_smul` (`@[simp, norm_cast]` in mathlib) restated by `rfl`; `simp` with `latticeBasis_zero/one` should close both cases without them.
- `range_complexSublatticeGenerators` (L255–259) is a one-line wrapper around `Matrix.range_cons_cons_empty` (`Mathlib/Data/Fin/VecNotation.lean:254`).
- `complexSublatticeSpan_eq_scaledLattice` (L261–278): is `PeriodPair.map_lattice_mulLeftLinearEquiv` (`LatticeJ.lean:72`) + `Submodule.map_span` on `{1, στ}`; the proof instead recomputes `ω₁, ω₂` by `simp`/`field_simp`. A `PeriodPair.smul_lattice_eq_span : (a • L).lattice = span {a * ω₁, a * ω₂}` lemma (missing in `LatticeJ`) would make it two rewrites.
- `toCoxMatrix` (L28–55): `hmul` (37–40) and `hprimitive` (43–47) are `CyclicSublattice.lean:306 d_mul_a_eq_m` and `:470 dual_content_eq_one` (private there) — publish those and reuse; `Matrix.det_of_upperTriangular` (`Block.lean:324`) removes the `det_fin_two`/`hz` step. `Int.natAbs_lt_natAbs_of_nonneg_of_lt`, `Int.natAbs_pos`, `Int.natAbs_mul` are core/mathlib and correctly used.
- `Cox.CoxMatrix` itself vs mathlib `FixedDetMatrices.reps` (`LinearAlgebra/Matrix/FixedDetMatrices.lean:69`): both are "reduced triangular matrices of det `m`", but with different reduction conventions and mathlib lacks the primitivity condition — no direct ride.
### Missing API / repeated patterns
- `Units.mk0 (σ.d : ℂ) (by exact_mod_cast σ.d_pos.ne')` at L264, 297, 313 (and the `m` version in `CyclicSublattice.lean:515, 523, 528`) — add `CoxMatrix.dUnit : ℂˣ` (and `PNat`→`ℂˣ`).
- HNF-field extraction `hd/ha/hb/hz` at L31–36 and L63–70 (5 sites project-wide) — add `Matrix.isColumnHermiteNormalForm_fin_two_iff`.
- `letI Free/Finite of_basis` at L100–101 (3 sites project-wide).
- `dualBasis`-style `L.latticeBasis.map (LinearEquiv.ofInjective f _)` at L122–124 and `CyclicSublattice.lean:348–351` — add `PeriodPair.latticeBasis_map_ofInjective`.
- `cyclicSublatticeEquivCoxMatrixOfPeriodPair` (L169) gives `Fintype (CyclicSublattice L m)` and `Nat.card = ψ(m)` (via `CoxMatrices/Cardinality.lean`) — not stated.
- No simp lemmas `toCoxMatrix_a/_b/_d` exposing the fields (L74 unfolds `toCoxMatrix` inside `simp`).
### Junk candidates
- `CoxMatrix.toCyclicSublattice_carrier` (L189–192): `rfl`, unused project-wide.
- `cyclicSublattice_hnf_matrix` (L288–292): one-line restatement, unused project-wide.
- `cyclicSublatticeEquivCoxMatrix` (L282–284) and `CoxMatrix.sublattice` (L178–180), `CoxMatrix.toCyclicSublattice` (L184–186): one-line specialisations to `periodPair τ`; only `toCyclicSublattice` earns its keep (5 uses).
- `range_complexSublatticeGenerators` (L255): one-line mathlib wrapper.
- No dead `#check`/`example`s or commented-out blocks.
### Moral duplicates within this batch
- `toCoxMatrix.hmul` (L37–40) ≡ `CyclicSublattice.d_mul_a_eq_m` (`CyclicSublattice.lean:306`); `toCoxMatrix.hprimitive` (L43–47) ≡ `dual_content_eq_one` (`:470`) modulo `!![d,b;0,a]` vs `!![a,-b;0,d]`.
- `inclusionHermiteNormalForm` (L117) ≡ the tail of `Submodule.exists_hermiteNormalForm` (`HermiteNormalForm.lean:392–400`): both build an HNF from `Basis.map (LinearEquiv …)` + `LinearMap.toMatrix_map_left` + `LinearMap.toMatrix_toLin`.
- `inclusionLinearMap_injective` (L98) ≡ `HermiteNormalForm.lean:378–389`.
- `hermiteNormalForm_matrix_eq_inclusionMatrix` (L59) ≡ `CyclicSublattice.originalMatrix_eq` (`CyclicSublattice.lean:300`) up to `natAbs` casts.
- `sublattice_map_subtype` (L245) ≡ `CyclicSublattice.toPeriodPair_lattice` (`:106`) pattern (`Submodule.map_span` + `Set.range_comp`).
### Generalization notes
- `toCoxMatrix`, `inclusionLinearMap`, `sublatticeOfPeriodPair`, `inclusionHermiteNormalForm`, `toCyclicSublatticeOfPeriodPair`, both round trips and `cyclicSublatticeEquivCoxMatrixOfPeriodPair` (L28–175) never use ℂ or `PeriodPair` beyond `L.latticeBasis : Basis (Fin 2) ℤ L.lattice`; the classification "cyclic index-`m` submodules of a rank-2 free ℤ-module with chosen basis ≃ `CoxMatrix m`" holds for any `(M, bM : Basis (Fin 2) ℤ M)` and should be stated there (with `CyclicSublattice` generalised accordingly).
- `inclusionLinearMap_injective` (L98) needs only `IsDomain` (uses `det ≠ 0`).
- Only L178–368 (`periodPair τ`, `act`, `j`) are genuinely about ℂ/ℍ.
