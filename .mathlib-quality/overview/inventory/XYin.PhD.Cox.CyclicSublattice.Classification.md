# XYin/PhD/Cox/CyclicSublattice/Classification.lean

**Source**: `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/CyclicSublattice/Classification.lean`
**Project-internal imports**: `XYin.PhD.Cox.CyclicSublattice`, `XYin.PhD.Cox.ModularPolynomial`

Proves Cox Lemma 11.24 (cyclic index-`m` sublattices ↔ Cox matrices `C(m)`) and Cox Theorem 11.23 (roots of `Φ_m` classify cyclic lattice inclusions). Declarations split between namespaces `PeriodPair.CyclicSublattice` (extraction direction) and `Cox` / `Cox.CoxMatrix` (construction direction and the classification theorems).

### `def toCoxMatrix`
- **Type**: `(S : CyclicSublattice L m) : Cox.CoxMatrix m`
- **What**: Extracts the unique Cox representative `⟨a, b, d⟩` (with `ad = m`, `0 ≤ b < d`, `gcd(a,b,d) = 1`) from a cyclic sublattice: the natAbs's of the entries of its HNF inclusion matrix `!![d, b; 0, a]`.
- **How**: The HNF normalization supplies triangularity (`belowDiagonal_eq_zero`), positive diagonal (`diagonal_pos`), and reducedness `0 ≤ b < d` (`reduced`); the determinant condition `a·d = m` comes from the project lemma `HermiteNormalForm.index_eq_natAbs_det` plus `Matrix.det_fin_two`; primitivity `gcd(a, b, d) = 1` comes from `quotient_isAddCyclic_iff_rankTwoContent_eq_one` applied to `S.cyclic`, after a `Nat.gcd` shuffle.
- **Hypotheses**: cyclicity and index of `S` (structure fields).
- **Uses from project**: [`PeriodPair.CyclicSublattice`, `CyclicSublattice.hermiteNormalForm`, `Matrix.IsColumnHermiteNormalForm.diagonal_pos`, `Matrix.IsColumnHermiteNormalForm.reduced`, `Matrix.IsColumnHermiteNormalForm.belowDiagonal_eq_zero`, `Module.Basis.HermiteNormalForm.index_eq_natAbs_det`, `Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`, `Matrix.rankTwoContent`, `Cox.CoxMatrix`]
- **Used by**: `hermiteNormalForm_matrix_eq_inclusionMatrix`, `toCoxMatrix_inclusionMatrix`, `toCyclicSublatticeOfPeriodPair_toCoxMatrix`, `toCoxMatrix_toCyclicSublatticeOfPeriodPair`, `cyclicSublatticeEquivCoxMatrixOfPeriodPair`, `modularPolynomialC_zero_iff_normalizedCyclicSublattice`
- **Visibility**: public
- **Lines**: 28–67, 40-line def-with-proofs
- **Notes**: `noncomputable`; body >30 lines

### `theorem hermiteNormalForm_matrix_eq_inclusionMatrix`
- **Type**: `(S : CyclicSublattice L m) : S.hermiteNormalForm.matrix = S.toCoxMatrix.inclusionMatrix`
- **What**: The HNF matrix of a cyclic sublattice is literally the inclusion matrix `!![d, b; 0, a]` of its extracted Cox representative — the natAbs round-trip loses nothing since all relevant entries are nonnegative.
- **How**: Entry-wise (`fin_cases`); each nonzero entry is its own `natAbs` by `abs_of_nonneg` with sign facts from `diagonal_pos` / `reduced`, and the lower-left entry vanishes by `belowDiagonal_eq_zero`.
- **Hypotheses**: none.
- **Uses from project**: [`toCoxMatrix`, `CyclicSublattice.hermiteNormalForm`, `Cox.CoxMatrix.inclusionMatrix`, `Matrix.IsColumnHermiteNormalForm.diagonal_pos`, `Matrix.IsColumnHermiteNormalForm.reduced`, `Matrix.IsColumnHermiteNormalForm.belowDiagonal_eq_zero`]
- **Used by**: `toCoxMatrix_inclusionMatrix`, `toCyclicSublatticeOfPeriodPair_toCoxMatrix`, `toCoxMatrix_toCyclicSublatticeOfPeriodPair`, `cyclicSublattice_hnf_matrix`
- **Visibility**: public
- **Lines**: 71–92, 21-line proof
- **Notes**: none

### `theorem toCoxMatrix_inclusionMatrix`
- **Type**: `(S : CyclicSublattice L m) : S.toCoxMatrix.inclusionMatrix = S.hermiteNormalForm.matrix`
- **What**: Simp-normal-form restatement of the previous lemma (symmetric orientation).
- **How**: `.symm` of `hermiteNormalForm_matrix_eq_inclusionMatrix`.
- **Hypotheses**: none.
- **Uses from project**: [`toCoxMatrix`, `hermiteNormalForm_matrix_eq_inclusionMatrix`, `Cox.CoxMatrix.inclusionMatrix`, `CyclicSublattice.hermiteNormalForm`]
- **Used by**: unused in file (public simp API)
- **Visibility**: public
- **Lines**: 94–97, term proof
- **Notes**: tagged `@[simp]`

### `def inclusionLinearMap` (private)
- **Type**: `(σ : CoxMatrix m) (L : PeriodPair) : L.lattice →ₗ[ℤ] L.lattice`
- **What**: The endomorphism of the period lattice given by the Cox inclusion matrix `!![d, b; 0, a]` in the standard basis; its image will be the classified sublattice.
- **How**: `Matrix.toLin L.latticeBasis L.latticeBasis σ.inclusionMatrix`.
- **Hypotheses**: none.
- **Uses from project**: [`Cox.CoxMatrix`, `Cox.CoxMatrix.inclusionMatrix`]
- **Used by**: `inclusionLinearMap_injective`, `sublatticeOfPeriodPair`, `inclusionHermiteNormalForm`, `sublattice_eq_span`
- **Visibility**: private
- **Lines**: 111–113
- **Notes**: none

### `theorem inclusionLinearMap_injective` (private)
- **Type**: `(σ : CoxMatrix m) (L : PeriodPair) : Function.Injective (σ.inclusionLinearMap L)`
- **What**: The Cox inclusion endomorphism is injective, since its determinant `m` is nonzero.
- **How**: `LinearMap.det_toMatrix` identifies the map's determinant with `σ.inclusionMatrix.det = m` (project lemma `inclusionMatrix_det`); a nonzero determinant forces trivial kernel by mathlib's `LinearMap.det_eq_zero_iff_ker_ne_bot`.
- **Hypotheses**: `m ≠ 0` (from `ℕ+`).
- **Uses from project**: [`inclusionLinearMap`, `Cox.CoxMatrix.inclusionMatrix`, `Cox.CoxMatrix.inclusionMatrix_det`]
- **Used by**: `inclusionHermiteNormalForm`
- **Visibility**: private
- **Lines**: 115–129, 14-line proof
- **Notes**: none

### `def sublatticeOfPeriodPair`
- **Type**: `(σ : CoxMatrix m) (L : PeriodPair) : Submodule ℤ L.lattice`
- **What**: The sublattice generated by the columns of the Cox inclusion matrix in any period lattice — abstractly, `[dω₁, bω₁ + aω₂]`.
- **How**: `LinearMap.range (σ.inclusionLinearMap L)`.
- **Hypotheses**: none.
- **Uses from project**: [`inclusionLinearMap`, `Cox.CoxMatrix`]
- **Used by**: `inclusionHermiteNormalForm`, `toCyclicSublatticeOfPeriodPair`, `CoxMatrix.sublattice`
- **Visibility**: public
- **Lines**: 131–134
- **Notes**: none

### `def inclusionHermiteNormalForm` (private)
- **Type**: `(σ : CoxMatrix m) (L : PeriodPair) : Module.Basis.HermiteNormalForm L.latticeBasis (σ.sublatticeOfPeriodPair L)`
- **What**: The Cox inclusion matrix, being already in column HNF, directly equips its range sublattice with HNF data (basis = image of the standard basis, matrix = the inclusion matrix itself).
- **How**: Basis by `Basis.map` along `LinearEquiv.ofInjective` (using `inclusionLinearMap_injective`); the matrix identity is `LinearMap.toMatrix_map_left` plus `LinearMap.toMatrix_toLin`; HNF shape is the project lemma `inclusionMatrix_isColumnHermiteNormalForm`.
- **Hypotheses**: none.
- **Uses from project**: [`inclusionLinearMap`, `inclusionLinearMap_injective`, `sublatticeOfPeriodPair`, `Module.Basis.HermiteNormalForm`, `Cox.CoxMatrix.inclusionMatrix`, `Cox.CoxMatrix.inclusionMatrix_isColumnHermiteNormalForm`]
- **Used by**: `toCyclicSublatticeOfPeriodPair`, `toCyclicSublatticeOfPeriodPair_toCoxMatrix`
- **Visibility**: private
- **Lines**: 136–153, 17-line def-with-proof
- **Notes**: `noncomputable`

### `def toCyclicSublatticeOfPeriodPair`
- **Type**: `(σ : CoxMatrix m) (L : PeriodPair) : PeriodPair.CyclicSublattice L m`
- **What**: The construction half of Lemma 11.24: every Cox matrix produces a cyclic index-`m` sublattice in any period lattice.
- **How**: Carrier is `sublatticeOfPeriodPair`; index `= |det| = m` via the project lemma `HermiteNormalForm.index_eq_natAbs_det` and `inclusionMatrix_det`; cyclicity via `quotient_isAddCyclic_iff_rankTwoContent_eq_one` and the primitivity lemma `inclusionMatrix_content_eq_one`.
- **Hypotheses**: none (the `CoxMatrix` fields carry `ad = m`, `0 ≤ b < d`, primitivity).
- **Uses from project**: [`sublatticeOfPeriodPair`, `inclusionHermiteNormalForm`, `PeriodPair.CyclicSublattice`, `Module.Basis.HermiteNormalForm.index_eq_natAbs_det`, `Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`, `Matrix.rankTwoContent`, `Cox.CoxMatrix.inclusionMatrix_det`, `Cox.CoxMatrix.inclusionMatrix_content_eq_one`]
- **Used by**: `toCyclicSublatticeOfPeriodPair_toCoxMatrix`, `toCoxMatrix_toCyclicSublatticeOfPeriodPair`, `cyclicSublatticeEquivCoxMatrixOfPeriodPair`, `CoxMatrix.toCyclicSublattice`
- **Visibility**: public
- **Lines**: 155–167, 12-line def-with-proofs
- **Notes**: `noncomputable`

### `theorem toCyclicSublatticeOfPeriodPair_toCoxMatrix`
- **Type**: `(σ : CoxMatrix m) (L : PeriodPair) : (σ.toCyclicSublatticeOfPeriodPair L).toCoxMatrix = σ`
- **What**: Round-trip 1 of the classification: constructing a sublattice from a Cox matrix and extracting its Cox representative recovers the original matrix.
- **How**: HNF matrices of a submodule are unique (project lemma `HermiteNormalForm.matrix_eq`), so the constructed sublattice's HNF matrix is `σ.inclusionMatrix`; the extraction inverts this by `hermiteNormalForm_matrix_eq_inclusionMatrix`, and `CoxMatrix.inclusionMatrix_injective` finishes.
- **Hypotheses**: none.
- **Uses from project**: [`toCyclicSublatticeOfPeriodPair`, `toCoxMatrix`, `inclusionHermiteNormalForm`, `hermiteNormalForm_matrix_eq_inclusionMatrix`, `CyclicSublattice.hermiteNormalForm`, `Module.Basis.HermiteNormalForm.matrix_eq`, `Cox.CoxMatrix.inclusionMatrix`, `Cox.CoxMatrix.inclusionMatrix_injective`]
- **Used by**: `cyclicSublatticeEquivCoxMatrixOfPeriodPair`
- **Visibility**: public
- **Lines**: 169–179, 10-line proof
- **Notes**: tagged `@[simp]`

### `theorem toCoxMatrix_toCyclicSublatticeOfPeriodPair`
- **Type**: `(S : PeriodPair.CyclicSublattice L m) : S.toCoxMatrix.toCyclicSublatticeOfPeriodPair L = S`
- **What**: Round-trip 2: rebuilding a cyclic sublattice from its extracted Cox representative gives back the same sublattice.
- **How**: By carrier extensionality (`CyclicSublattice.ext`): the range of `toLin` of the extracted inclusion matrix equals the carrier via `hermiteNormalForm_matrix_eq_inclusionMatrix` and the project lemma `HermiteNormalForm.range_toLin_matrix_eq`.
- **Hypotheses**: none.
- **Uses from project**: [`toCoxMatrix`, `toCyclicSublatticeOfPeriodPair`, `PeriodPair.CyclicSublattice.ext`, `hermiteNormalForm_matrix_eq_inclusionMatrix`, `CyclicSublattice.hermiteNormalForm`, `Module.Basis.HermiteNormalForm.range_toLin_matrix_eq`, `Cox.CoxMatrix.inclusionMatrix`]
- **Used by**: `cyclicSublatticeEquivCoxMatrixOfPeriodPair`, `modularPolynomialC_zero_iff_normalizedCyclicSublattice`
- **Visibility**: public
- **Lines**: 181–190, 9-line proof
- **Notes**: tagged `@[simp]`

### `def cyclicSublatticeEquivCoxMatrixOfPeriodPair`
- **Type**: `(L : PeriodPair) (m : ℕ+) : PeriodPair.CyclicSublattice L m ≃ CoxMatrix m`
- **What**: The classification bijection for an arbitrary period lattice: cyclic index-`m` sublattices correspond exactly to Cox matrices in `C(m)`.
- **How**: `Equiv` assembled from `toCoxMatrix` / `toCyclicSublatticeOfPeriodPair` with the two round-trip lemmas as `left_inv` / `right_inv`.
- **Hypotheses**: none.
- **Uses from project**: [`PeriodPair.CyclicSublattice.toCoxMatrix`, `toCyclicSublatticeOfPeriodPair`, `toCoxMatrix_toCyclicSublatticeOfPeriodPair`, `toCyclicSublatticeOfPeriodPair_toCoxMatrix`, `Cox.CoxMatrix`]
- **Used by**: `cyclicSublatticeEquivCoxMatrix`
- **Visibility**: public
- **Lines**: 194–201
- **Notes**: `noncomputable`

### `def CoxMatrix.sublattice`
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : Submodule ℤ (UpperHalfPlane.periodPair τ).lattice`
- **What**: The concrete carrier `[d, aτ+b]` associated to a Cox representative inside the normalized lattice `[1, τ]`.
- **How**: Specialization of `sublatticeOfPeriodPair` to `UpperHalfPlane.periodPair τ`.
- **Hypotheses**: none.
- **Uses from project**: [`sublatticeOfPeriodPair`, `UpperHalfPlane.periodPair`, `Cox.CoxMatrix`]
- **Used by**: `toCyclicSublattice_carrier`, `sublattice_eq_span`, `sublattice_map_subtype`
- **Visibility**: public
- **Lines**: 204–206
- **Notes**: `noncomputable`

### `def CoxMatrix.toCyclicSublattice`
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : PeriodPair.CyclicSublattice (UpperHalfPlane.periodPair τ) m`
- **What**: The converse half of Lemma 11.24 specialized to `[1, τ]`: a Cox representative produces a cyclic index-`m` sublattice of the normalized lattice.
- **How**: Specialization of `toCyclicSublatticeOfPeriodPair`.
- **Hypotheses**: none.
- **Uses from project**: [`toCyclicSublatticeOfPeriodPair`, `UpperHalfPlane.periodPair`, `PeriodPair.CyclicSublattice`, `Cox.CoxMatrix`]
- **Used by**: `toCyclicSublattice_carrier`, `coxMatrix_toPeriodPair_lattice`, `toCyclicSublattice_j`, `modularPolynomialC_zero_iff_normalizedCyclicSublattice`
- **Visibility**: public
- **Lines**: 210–212
- **Notes**: `noncomputable`

### `theorem CoxMatrix.toCyclicSublattice_carrier`
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : (σ.toCyclicSublattice τ).carrier = σ.sublattice τ`
- **What**: The carrier of the constructed cyclic sublattice is the concrete sublattice `[d, aτ+b]` (simp API).
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.toCyclicSublattice`, `CoxMatrix.sublattice`]
- **Used by**: unused in file (definitional; the identification is used by defeq in `coxMatrix_toPeriodPair_lattice`)
- **Visibility**: public
- **Lines**: 214–218, rfl
- **Notes**: tagged `@[simp]`

### `def CoxMatrix.sublatticeGenerators` (private)
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : Fin 2 → (UpperHalfPlane.periodPair τ).lattice`
- **What**: The two generators `d·ω₁` and `b·ω₁ + a·ω₂` of the Cox sublattice, as lattice elements of `[1, τ]`.
- **How**: Explicit `![...]` vector of ℤ-combinations of the standard basis.
- **Hypotheses**: none.
- **Uses from project**: [`UpperHalfPlane.periodPair`, `Cox.CoxMatrix`]
- **Used by**: `sublattice_eq_span`, `coe_sublatticeGenerators`, `sublattice_map_subtype`
- **Visibility**: private
- **Lines**: 220–225
- **Notes**: none

### `theorem CoxMatrix.sublattice_eq_span` (private)
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : σ.sublattice τ = Submodule.span ℤ (Set.range (σ.sublatticeGenerators τ))`
- **What**: The range of the inclusion endomorphism equals the ℤ-span of the two explicit generators.
- **How**: `range f = map f ⊤ = map f (span basis) = span (f '' basis)` via mathlib's `Submodule.map_span` and `Basis.span_eq`; then `Matrix.toLin_self` computes `f(basisᵢ)` column-wise as exactly the generators.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.sublattice`, `inclusionLinearMap`, `sublatticeGenerators`, `UpperHalfPlane.periodPair`, `Cox.CoxMatrix.inclusionMatrix`]
- **Used by**: `sublattice_map_subtype`
- **Visibility**: private
- **Lines**: 227–255, 28-line proof
- **Notes**: none

### `def CoxMatrix.complexSublatticeGenerators` (private)
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : Fin 2 → ℂ`
- **What**: The complex numbers `d` and `b + aτ` — the images in ℂ of the two sublattice generators.
- **How**: Explicit `![...]` vector.
- **Hypotheses**: none.
- **Uses from project**: [`Cox.CoxMatrix`]
- **Used by**: `coe_sublatticeGenerators`, `sublattice_map_subtype`, `range_complexSublatticeGenerators`, `complexSublatticeSpan_eq_scaledLattice`, `coxMatrix_toPeriodPair_lattice`
- **Visibility**: private
- **Lines**: 257–259
- **Notes**: none

### `theorem CoxMatrix.coe_sublatticeGenerators` (private)
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) (i : Fin 2) : ((σ.sublatticeGenerators τ i : ...lattice) : ℂ) = σ.complexSublatticeGenerators τ i`
- **What**: Embedding the lattice generators in ℂ gives exactly `d` and `b + aτ`, since `ω₁ = 1` and `ω₂ = τ` for the normalized pair.
- **How**: Case split on `i`; coercion commutes with `+` and ℤ-scaling (`rfl` facts), then mathlib's `PeriodPair.latticeBasis_zero/one` and unfolding `UpperHalfPlane.periodPair` (project) evaluate the basis vectors to `1` and `τ`.
- **Hypotheses**: none.
- **Uses from project**: [`sublatticeGenerators`, `complexSublatticeGenerators`, `UpperHalfPlane.periodPair`]
- **Used by**: `sublattice_map_subtype`
- **Visibility**: private
- **Lines**: 261–280, 19-line proof
- **Notes**: none

### `theorem CoxMatrix.sublattice_map_subtype` (private)
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : (σ.sublattice τ).map (...).lattice.subtype = Submodule.span ℤ (Set.range (σ.complexSublatticeGenerators τ))`
- **What**: Embedded in ℂ, the Cox sublattice of `[1, τ]` is the ℤ-span of `{d, b + aτ}`.
- **How**: Rewrite by `sublattice_eq_span` and mathlib's `Submodule.map_span`; the image of the generator set is identified element-wise by `coe_sublatticeGenerators`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.sublattice`, `sublattice_eq_span`, `sublatticeGenerators`, `complexSublatticeGenerators`, `coe_sublatticeGenerators`, `UpperHalfPlane.periodPair`]
- **Used by**: `coxMatrix_toPeriodPair_lattice`
- **Visibility**: private
- **Lines**: 282–294, 12-line proof
- **Notes**: none

### `theorem CoxMatrix.range_complexSublatticeGenerators` (private)
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : Set.range (σ.complexSublatticeGenerators τ) = ({(σ.d : ℂ), (σ.b : ℂ) + (σ.a : ℂ) * τ} : Set ℂ)`
- **What**: The range of the generator function is the two-element set `{d, b + aτ}`.
- **How**: Set extensionality and `fin_cases` on the index.
- **Hypotheses**: none.
- **Uses from project**: [`complexSublatticeGenerators`, `Cox.CoxMatrix`]
- **Used by**: `complexSublatticeSpan_eq_scaledLattice`
- **Visibility**: private
- **Lines**: 296–309, 13-line proof
- **Notes**: none

### `theorem CoxMatrix.complexSublatticeSpan_eq_scaledLattice` (private)
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : Submodule.span ℤ (Set.range (σ.complexSublatticeGenerators τ)) = ((Units.mk0 (σ.d : ℂ) _) • UpperHalfPlane.periodPair (σ.act τ)).lattice`
- **What**: The key homothety identity `[d, b+aτ] = d·[1, στ]` where `στ = (aτ+b)/d` is the Cox action: the span of the generators is the `d`-scaled normalized lattice at `σ.act τ`.
- **How**: Computes the scaled periods: `d·1 = d` (project simp lemma `PeriodPair.smul_ω₂`/`smul_ω₁` machinery) and `d·(στ) = b + aτ` by `CoxMatrix.coe_act` and `field_simp` with `d ≠ 0` (`σ.d_pos`); membership on both sides is `Submodule.mem_span_pair` vs. mathlib's `PeriodPair.mem_lattice`.
- **Hypotheses**: `d > 0` (Cox matrix field, via `d_pos`).
- **Uses from project**: [`complexSublatticeGenerators`, `range_complexSublatticeGenerators`, `UpperHalfPlane.periodPair`, `Cox.CoxMatrix.act`, `Cox.CoxMatrix.coe_act`, `Cox.CoxMatrix.d_pos`, `PeriodPair.smul_ω₂`]
- **Used by**: `coxMatrix_toPeriodPair_lattice`
- **Visibility**: private
- **Lines**: 311–331, 20-line proof
- **Notes**: none

### `def cyclicSublatticeEquivCoxMatrix`
- **Type**: `(m : ℕ+) (τ : ℍ) : PeriodPair.CyclicSublattice (UpperHalfPlane.periodPair τ) m ≃ CoxMatrix m`
- **What**: Cox Lemma 11.24: cyclic index-`m` sublattices of the normalized lattice `[1, τ]` are uniquely classified by the set `C(m)` of Cox matrices.
- **How**: Specialization of `cyclicSublatticeEquivCoxMatrixOfPeriodPair` to `UpperHalfPlane.periodPair τ`.
- **Hypotheses**: none.
- **Uses from project**: [`cyclicSublatticeEquivCoxMatrixOfPeriodPair`, `UpperHalfPlane.periodPair`, `PeriodPair.CyclicSublattice`, `Cox.CoxMatrix`]
- **Used by**: `cyclicSublattice_hnf_matrix`
- **Visibility**: public
- **Lines**: 335–337
- **Notes**: `noncomputable`

### `theorem cyclicSublattice_hnf_matrix`
- **Type**: `(m : ℕ+) (τ : ℍ) (S : PeriodPair.CyclicSublattice (UpperHalfPlane.periodPair τ) m) : S.hermiteNormalForm.matrix = (cyclicSublatticeEquivCoxMatrix m τ S).inclusionMatrix`
- **What**: The HNF inclusion matrix of any cyclic sublattice of `[1, τ]` is `!![d, b; 0, a]` for its unique Cox representative under the classification.
- **How**: Restates `hermiteNormalForm_matrix_eq_inclusionMatrix` through the equivalence (whose forward map is `toCoxMatrix`).
- **Hypotheses**: none.
- **Uses from project**: [`cyclicSublatticeEquivCoxMatrix`, `hermiteNormalForm_matrix_eq_inclusionMatrix`, `CyclicSublattice.hermiteNormalForm`, `Cox.CoxMatrix.inclusionMatrix`, `UpperHalfPlane.periodPair`]
- **Used by**: unused in file (public API)
- **Visibility**: public
- **Lines**: 341–345, 1-line proof
- **Notes**: none

### `theorem coxMatrix_toPeriodPair_lattice`
- **Type**: `(m : ℕ+) (τ : ℍ) (σ : CoxMatrix m) : (σ.toCyclicSublattice τ).toPeriodPair.lattice = ((Units.mk0 (σ.d : ℂ) _) • UpperHalfPlane.periodPair (σ.act τ)).lattice`
- **What**: The canonical period lattice of the sublattice classified by `σ` is `[d, aτ+b] = d·[1, στ]` — the geometric identity behind `j(L') = j(στ)`.
- **How**: Calc chain: `CyclicSublattice.toPeriodPair_lattice` (carrier embedding), `sublattice_map_subtype` (explicit generators), `complexSublatticeSpan_eq_scaledLattice` (homothety identity).
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.toCyclicSublattice`, `PeriodPair.CyclicSublattice.toPeriodPair_lattice`, `sublattice_map_subtype`, `complexSublatticeGenerators`, `complexSublatticeSpan_eq_scaledLattice`, `UpperHalfPlane.periodPair`, `Cox.CoxMatrix.act`, `Cox.CoxMatrix.d_pos`]
- **Used by**: `toCyclicSublattice_j`
- **Visibility**: public
- **Lines**: 348–360, 12-line proof
- **Notes**: none

### `theorem CoxMatrix.toCyclicSublattice_j`
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : (σ.toCyclicSublattice τ).j = j (σ.act τ)`
- **What**: The sublattice attached to a Cox representative has `j`-invariant equal to the analytic `j`-value `j(στ) = j((aτ+b)/d)` — the bridge from lattice `j` to the analytic `j`-function values appearing in `Φ_m`.
- **How**: `PeriodPair.j_congr` on `coxMatrix_toPeriodPair_lattice`, homothety invariance `PeriodPair.j_smul` to drop the factor `d`, then the analytic-lattice comparison `j_eq_periodPair_j` (project, LatticeJ).
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.toCyclicSublattice`, `PeriodPair.CyclicSublattice.j`, `coxMatrix_toPeriodPair_lattice`, `PeriodPair.j_congr`, `PeriodPair.j_smul`, `j_eq_periodPair_j`, `UpperHalfPlane.j`, `UpperHalfPlane.periodPair`, `Cox.CoxMatrix.act`, `Cox.CoxMatrix.d_pos`]
- **Used by**: `modularPolynomialC_zero_iff_normalizedCyclicSublattice`
- **Visibility**: public
- **Lines**: 364–374, 10-line proof
- **Notes**: none

### `theorem modularPolynomialC_zero_iff_normalizedCyclicSublattice`
- **Type**: `(m : ℕ+) (τ : ℍ) (u : ℂ) : (modularPolynomialC m).eval u (j τ) = 0 ↔ ∃ S : PeriodPair.CyclicSublattice (UpperHalfPlane.periodPair τ) m, u = S.j`
- **What**: Local form of Theorem 11.23 over a normalized lattice: `u` is a root of `Φ_m(·, j(τ))` iff `u` is the `j`-invariant of some cyclic index-`m` sublattice of `[1, τ]`.
- **How**: Specialize `Φ_m` at `Y = j(τ)` via `modularPolynomialC_specializeY`, which factors it as the product `coxPhiAtJ = ∏_{σ ∈ C(m)} (X − j(στ))`; `Finset.prod_eq_zero_iff` turns vanishing into existence of a factor, and `toCyclicSublattice_j` plus the round-trip `toCoxMatrix_toCyclicSublatticeOfPeriodPair` convert between `σ ∈ C(m)` and sublattices `S`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialC`, `modularPolynomialC_specializeY`, `coxPhiAtJ`, `BivariatePolynomial.eval`, `BivariatePolynomial.specializeY_eval`, `UpperHalfPlane.j`, `UpperHalfPlane.periodPair`, `PeriodPair.CyclicSublattice`, `PeriodPair.CyclicSublattice.j`, `PeriodPair.CyclicSublattice.toCoxMatrix`, `CoxMatrix.toCyclicSublattice`, `CoxMatrix.toCyclicSublattice_j`, `CoxMatrix.toCoxMatrix_toCyclicSublatticeOfPeriodPair`]
- **Used by**: `theorem_11_23`
- **Visibility**: public
- **Lines**: 377–395, 18-line proof
- **Notes**: uses `classical`

### `theorem theorem_11_23`
- **Type**: `(m : ℕ+) (u v : ℂ) : (BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m)).eval u v = 0 ↔ ∃ L : PeriodPair, ∃ S : PeriodPair.CyclicSublattice L m, u = S.j ∧ v = L.j`
- **What**: Cox Theorem 11.23 in full: `Φ_m(u, v) = 0` (for the integral modular polynomial, mapped to ℂ) iff there is a lattice `L` and a cyclic index-`m` sublattice `L' ⊂ L` with `u = j(L')`, `v = j(L)`.
- **How**: Reduce to `modularPolynomialC` by `modularPolynomial_map_complex`. Forward: surjectivity of the analytic `j` (`j_surjective`, project) writes `v = j(τ)` and applies the normalized classification. Backward: `exists_homothetic_periodPair` (project) normalizes an arbitrary `L` to some `[1, τ]` via a homothety `a`; the sublattice is transported by `CyclicSublattice.scale` then `ofLatticeEq`, with `j_scale`, `j_ofLatticeEq`, and `j_eq_of_homothetic` guaranteeing all `j`-invariants match.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomial`, `modularPolynomial_map_complex`, `modularPolynomialC`, `BivariatePolynomial.map`, `BivariatePolynomial.eval`, `modularPolynomialC_zero_iff_normalizedCyclicSublattice`, `j_surjective`, `j_eq_periodPair_j`, `exists_homothetic_periodPair`, `PeriodPair.j_eq_of_homothetic`, `PeriodPair.j`, `UpperHalfPlane.j`, `UpperHalfPlane.periodPair`, `PeriodPair.CyclicSublattice`, `PeriodPair.CyclicSublattice.j`, `PeriodPair.CyclicSublattice.scale`, `PeriodPair.CyclicSublattice.ofLatticeEq`, `PeriodPair.CyclicSublattice.j_scale`, `PeriodPair.CyclicSublattice.j_ofLatticeEq`]
- **Used by**: unused in file (terminal result of the file)
- **Visibility**: public
- **Lines**: 398–421, 23-line proof
- **Notes**: none

### File Summary
- Total declarations: 27 (11 defs, 16 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): `toCoxMatrix` (6), `hermiteNormalForm_matrix_eq_inclusionMatrix` (4), `inclusionLinearMap` (4), `sublatticeOfPeriodPair` (3), `toCyclicSublatticeOfPeriodPair` (4), `CoxMatrix.sublattice` (3), `CoxMatrix.toCyclicSublattice` (4), `complexSublatticeGenerators` (5), `sublatticeGenerators` (3)
- Unused declarations (not used by anything in this file): `toCoxMatrix_inclusionMatrix` (public simp API), `toCyclicSublattice_carrier` (definitional simp API), `cyclicSublattice_hnf_matrix` (public API), `theorem_11_23` (terminal theorem of the file)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [`toCoxMatrix` (40-line def with embedded proofs)]
