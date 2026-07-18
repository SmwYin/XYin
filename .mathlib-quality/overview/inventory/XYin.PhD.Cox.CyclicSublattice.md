# XYin/PhD/Cox/CyclicSublattice.lean

**Source**: `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/CyclicSublattice.lean`
**Project-internal imports**: `XYin.PhD.Cox.HermiteNormalForm`, `XYin.PhD.Cox.LatticeJ`

All declarations live in namespace `PeriodPair.CyclicSublattice` (the structure itself in `PeriodPair`). Note: `PeriodPair` and its core API (`lattice`, `latticeBasis`, `latticeBasis_zero/one`, `mem_lattice`, `finrank_lattice`) are **mathlib** (Weierstrass.lean); `PeriodPair.j`, the `ℂˣ`-scaling action, and homothety API are project code in `LatticeJ.lean`; the HNF machinery is project code in `HermiteNormalForm.lean`.

### `structure CyclicSublattice`
- **Type**: `CyclicSublattice (L : PeriodPair) (m : ℕ+)` with fields `carrier : Submodule ℤ L.lattice`, `index_eq : carrier.toAddSubgroup.index = m`, `cyclic : IsAddCyclic (L.lattice ⧸ carrier)`
- **What**: A cyclic sublattice of index `m` in a period lattice: a ℤ-submodule of the rank-2 lattice `[ω₁, ω₂]` whose additive index is `m` and whose quotient group is cyclic (i.e. `L/L' ≅ ℤ/m`). This is the object classified by Cox's `C(m)` (Cox §11).
- **How**: Bundled structure; no proof content.
- **Hypotheses**: none beyond the fields.
- **Uses from project**: []
- **Used by**: every other declaration in the file (they all take `S : CyclicSublattice L m`)
- **Visibility**: public
- **Lines**: 24–27
- **Notes**: none

### `theorem ext`
- **Type**: `{S T : CyclicSublattice L m} (h : S.carrier = T.carrier) : S = T`
- **What**: Extensionality: two cyclic sublattices with the same carrier submodule are equal, since the index and cyclicity fields are propositions.
- **How**: `cases` both structures and the equality; proof irrelevance closes the propositional fields.
- **Hypotheses**: equal carriers.
- **Uses from project**: [`CyclicSublattice`]
- **Used by**: unused in file (used in `Classification.lean` for `toCoxMatrix_toCyclicSublatticeOfPeriodPair`)
- **Visibility**: public
- **Lines**: 35–40, 4-line proof
- **Notes**: tagged `@[ext]`

### `theorem carrier_finrank`
- **Type**: `(S : CyclicSublattice L m) : Module.finrank ℤ S.carrier = 2`
- **What**: A finite-index sublattice of the rank-2 period lattice again has ℤ-rank 2.
- **How**: The lattice is free and finite via `L.latticeBasis`; since the index `m ≠ 0` the subgroup has `FiniteIndex`, so mathlib's `AddSubgroup.finrank_eq_of_finiteIndex` gives rank equality with the ambient lattice, whose rank is 2 by `PeriodPair.finrank_lattice`.
- **Hypotheses**: the sublattice has finite index `m` (a positive natural).
- **Uses from project**: [`CyclicSublattice`] (plus `CyclicSublattice.index_eq` field; `finrank_lattice`, `latticeBasis` are mathlib)
- **Used by**: `hermiteNormalForm`
- **Visibility**: public
- **Lines**: 43–52, 9-line proof
- **Notes**: none

### `def hermiteNormalForm`
- **Type**: `(S : CyclicSublattice L m) : Module.Basis.HermiteNormalForm L.latticeBasis S.carrier`
- **What**: The canonical Hermite normal form data of the carrier relative to the standard lattice basis `(ω₁, ω₂)`: a basis of the sublattice whose inclusion matrix is upper triangular with positive diagonal and reduced upper entry.
- **How**: Direct application of the project constructor `Submodule.hermiteNormalForm` (from `HermiteNormalForm.lean`), fed the rank-2 fact `carrier_finrank`.
- **Hypotheses**: none beyond the structure.
- **Uses from project**: [`Submodule.hermiteNormalForm`, `Module.Basis.HermiteNormalForm`, `carrier_finrank`]
- **Used by**: `hnfPeriod`, `hnfPeriod_eq`, `hnfPeriods_linearIndependent`, `toPeriodPair_lattice`, `transportedBasis`, `d`, `b`, `a`, `d_pos`, `a_pos`, `lower_left_eq_zero`, `hermite_repr_apply`, `originalMatrix_eq`, `d_mul_a_eq_m`, `nsmul_basis_zero_eq`, `nsmul_basis_one_eq`, `dualLinearMap_basis_zero_eq`, `dualLinearMap_basis_one_eq`, `dual_content_eq_one` (and, in `Classification.lean`, `toCoxMatrix`)
- **Visibility**: public
- **Lines**: 55–57
- **Notes**: `noncomputable`

### `def hnfPeriod` (private)
- **Type**: `(S : CyclicSublattice L m) (i : Fin 2) : ℂ`
- **What**: The complex number underlying the `i`-th HNF basis vector of the sublattice — the candidate periods of the sub-period-pair.
- **How**: Double coercion `S.carrier → L.lattice → ℂ` applied to `S.hermiteNormalForm.bN i`.
- **Hypotheses**: none.
- **Uses from project**: [`hermiteNormalForm`, `CyclicSublattice`]
- **Used by**: `hnfPeriod_eq`, `hnfPeriods_linearIndependent`, `toPeriodPair`, `toPeriodPair_lattice`
- **Visibility**: private
- **Lines**: 59–60
- **Notes**: `noncomputable`

### `theorem hnfPeriod_eq` (private)
- **Type**: `(S : CyclicSublattice L m) (j : Fin 2) : hnfPeriod S j = (S.hermiteNormalForm.matrix 0 j : ℂ) * L.ω₁ + (S.hermiteNormalForm.matrix 1 j : ℂ) * L.ω₂`
- **What**: Expresses each HNF period explicitly as the integer linear combination of `ω₁, ω₂` given by the corresponding column of the HNF matrix.
- **How**: Expand `bN j` via `Module.Basis.sum_repr` for `L.latticeBasis`, identify the coordinates with matrix entries by the project lemma `HermiteNormalForm.repr_apply`, and push the coercion to ℂ through sums/ℤ-scalars (which are `rfl`), finishing with mathlib's `latticeBasis_zero/one`.
- **Hypotheses**: none.
- **Uses from project**: [`hnfPeriod`, `hermiteNormalForm`, `Module.Basis.HermiteNormalForm.repr_apply`]
- **Used by**: `hnfPeriods_linearIndependent`
- **Visibility**: private
- **Lines**: 62–87, 25-line proof
- **Notes**: none

### `theorem hnfPeriods_linearIndependent` (private)
- **Type**: `(S : CyclicSublattice L m) : LinearIndependent ℝ ![hnfPeriod S 0, hnfPeriod S 1]`
- **What**: The two HNF periods of the sublattice are ℝ-linearly independent, so they form a genuine period pair.
- **How**: The HNF matrix is upper triangular (`belowDiagonal_eq_zero`) with positive diagonal (`diagonal_pos`), hence has nonzero real determinant; mathlib's `LinearIndependent.pair_add_smul_add_smul_iff` transfers independence of `(ω₁, ω₂)` (i.e. `L.indep`) across this invertible change of coordinates.
- **Hypotheses**: none (positivity of diagonal comes from the HNF normalization).
- **Uses from project**: [`hermiteNormalForm`, `hnfPeriod`, `hnfPeriod_eq`, `Matrix.IsColumnHermiteNormalForm.belowDiagonal_eq_zero`, `Matrix.IsColumnHermiteNormalForm.diagonal_pos`]
- **Used by**: `toPeriodPair`
- **Visibility**: private
- **Lines**: 89–113, 24-line proof
- **Notes**: none

### `def toPeriodPair`
- **Type**: `(S : CyclicSublattice L m) : PeriodPair`
- **What**: The canonical period pair attached to a cyclic sublattice: its periods are the two HNF basis vectors, viewed in ℂ. This normalizes the choice of basis for the sublattice.
- **How**: Packages `hnfPeriod S 0`, `hnfPeriod S 1` with `hnfPeriods_linearIndependent`.
- **Hypotheses**: none.
- **Uses from project**: [`hnfPeriod`, `hnfPeriods_linearIndependent`]
- **Used by**: `toPeriodPair_lattice`, `j`, `carrierToPeriodPairLinearMap`, `carrierEquiv`, `transportedBasis`, `dualLinearMap`, `dualCarrier`, `dual`, `dual_carrier_map_subtype`, `dual_toPeriodPair_lattice`, `dual_sub_j`, `dual_base_j`, `scale_toPeriodPair_lattice`, `ofLatticeEq_toPeriodPair_lattice`
- **Visibility**: public
- **Lines**: 117–120
- **Notes**: `noncomputable`

### `theorem coe_carrier_add` (private)
- **Type**: `(S : CyclicSublattice L m) (u v : S.carrier) : (((u + v : S.carrier) : L.lattice) : ℂ) = ... + ...`
- **What**: The double coercion `S.carrier → ℂ` is additive.
- **How**: Definitional (`rfl`): both coercions are subtype inclusions.
- **Hypotheses**: none.
- **Uses from project**: [`CyclicSublattice`]
- **Used by**: `toPeriodPair_lattice`
- **Visibility**: private
- **Lines**: 122–125, rfl
- **Notes**: none

### `theorem coe_carrier_zsmul` (private)
- **Type**: `(S : CyclicSublattice L m) (a : ℤ) (u : S.carrier) : (((a • u : S.carrier) : L.lattice) : ℂ) = a • (((u : S.carrier) : L.lattice) : ℂ)`
- **What**: The double coercion `S.carrier → ℂ` commutes with ℤ-scalar multiplication.
- **How**: Definitional (`rfl`).
- **Hypotheses**: none.
- **Uses from project**: [`CyclicSublattice`]
- **Used by**: `toPeriodPair_lattice`
- **Visibility**: private
- **Lines**: 127–130, rfl
- **Notes**: none

### `theorem toPeriodPair_lattice`
- **Type**: `(S : CyclicSublattice L m) : S.toPeriodPair.lattice = S.carrier.map L.lattice.subtype`
- **What**: The period lattice spanned by the canonical HNF periods is exactly the carrier submodule, embedded in ℂ. This is the key coherence lemma: `toPeriodPair` really represents the sublattice.
- **How**: Both inclusions via basis expansion. Forward: an element `a·ω₁' + b·ω₂'` of the span is the image of `a • bN 0 + b • bN 1 ∈ S.carrier`, using `coe_carrier_add/zsmul`. Backward: expand any carrier element in the HNF basis with `Module.Basis.sum_repr` and read off the coefficients; membership in the span uses mathlib's `PeriodPair.mem_lattice`.
- **Hypotheses**: none.
- **Uses from project**: [`toPeriodPair`, `hermiteNormalForm`, `hnfPeriod`, `coe_carrier_add`, `coe_carrier_zsmul`]
- **Used by**: `ofLatticeEq_toPeriodPair_lattice`, `scale_toPeriodPair_lattice`, `carrierToPeriodPairLinearMap`, `carrierToPeriodPairLinearMap_bijective`, `dual_toPeriodPair_lattice` (and in `Classification.lean`, `coxMatrix_toPeriodPair_lattice`)
- **Visibility**: public
- **Lines**: 133–161, 28-line proof
- **Notes**: none

### `def j`
- **Type**: `(S : CyclicSublattice L m) : ℂ`
- **What**: The `j`-invariant of a cyclic sublattice, defined as the lattice `j`-invariant of its canonical period pair. This is the quantity `j(L')` in Cox Theorem 11.23.
- **How**: `S.toPeriodPair.j`, using the project's `PeriodPair.j` from `LatticeJ.lean`.
- **Hypotheses**: none.
- **Uses from project**: [`toPeriodPair`, `PeriodPair.j`]
- **Used by**: `j_ofLatticeEq`, `j_scale`, `dual_sub_j`, `dual_base_j`
- **Visibility**: public
- **Lines**: 164
- **Notes**: none

### `def mapCarrier` (private)
- **Type**: `{M : PeriodPair} (e : L.lattice ≃ₗ[ℤ] M.lattice) (S : CyclicSublattice L m) : Submodule ℤ M.lattice`
- **What**: The image of the carrier under a ℤ-linear equivalence of ambient lattices.
- **How**: `Submodule.map` along `e.toLinearMap`.
- **Hypotheses**: none.
- **Uses from project**: [`CyclicSublattice`]
- **Used by**: `mapCarrier_index`, `mapQuotientEquiv`, `map`, `ofLatticeEq_carrier_map_subtype`
- **Visibility**: private
- **Lines**: 166–168
- **Notes**: none

### `theorem mapCarrier_index` (private)
- **Type**: `(e : L.lattice ≃ₗ[ℤ] M.lattice) (S : CyclicSublattice L m) : (mapCarrier e S).toAddSubgroup.index = S.carrier.toAddSubgroup.index`
- **What**: Transporting the carrier along a lattice isomorphism preserves the subgroup index.
- **How**: `Submodule.map_toAddSubgroup` reduces to additive subgroups, then mathlib's `AddSubgroup.index_map_equiv` for the additive equivalence underlying `e`.
- **Hypotheses**: `e` is a linear equivalence (bijectivity is essential for index preservation).
- **Uses from project**: [`mapCarrier`, `CyclicSublattice`]
- **Used by**: `map`
- **Visibility**: private
- **Lines**: 170–175, 4-line proof
- **Notes**: none

### `def mapQuotientEquiv` (private)
- **Type**: `(e : L.lattice ≃ₗ[ℤ] M.lattice) (S : CyclicSublattice L m) : (L.lattice ⧸ S.carrier) ≃ₗ[ℤ] (M.lattice ⧸ mapCarrier e S)`
- **What**: The induced isomorphism of quotient modules coming from a lattice equivalence carrying the carrier onto its image.
- **How**: Mathlib's `Submodule.Quotient.equiv` with the (`rfl`) compatibility of `e` with the mapped submodule.
- **Hypotheses**: none.
- **Uses from project**: [`mapCarrier`, `CyclicSublattice`]
- **Used by**: `map`
- **Visibility**: private
- **Lines**: 177–180
- **Notes**: none

### `def map`
- **Type**: `{M : PeriodPair} (S : CyclicSublattice L m) (e : L.lattice ≃ₗ[ℤ] M.lattice) : CyclicSublattice M m`
- **What**: Transport of a cyclic sublattice along a ℤ-linear equivalence of ambient period lattices; index and cyclicity of the quotient are preserved.
- **How**: Carrier is `mapCarrier`; index by `mapCarrier_index`; cyclicity by pushing `IsAddCyclic` through the surjection underlying `mapQuotientEquiv` via mathlib's `isAddCyclic_of_surjective`.
- **Hypotheses**: `e` a linear equivalence.
- **Uses from project**: [`CyclicSublattice`, `mapCarrier`, `mapCarrier_index`, `mapQuotientEquiv`]
- **Used by**: `map_carrier`, `ofLatticeEq`, `scale`
- **Visibility**: public
- **Lines**: 184–189
- **Notes**: `noncomputable`

### `theorem map_carrier`
- **Type**: `(S : CyclicSublattice L m) (e : L.lattice ≃ₗ[ℤ] M.lattice) : (S.map e).carrier = S.carrier.map e.toLinearMap`
- **What**: The carrier of a transported sublattice is the mapped carrier (definitional unfolding, exposed as simp API).
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`map`, `CyclicSublattice`]
- **Used by**: unused in file (public simp API)
- **Visibility**: public
- **Lines**: 191–195, rfl
- **Notes**: tagged `@[simp]`

### `def ofLatticeEq`
- **Type**: `{M : PeriodPair} (S : CyclicSublattice L m) (h : L.lattice = M.lattice) : CyclicSublattice M m`
- **What**: Reinterpret a cyclic sublattice inside a different period pair that happens to have the same underlying lattice (e.g. after a rescaling identity).
- **How**: `map` along `LinearEquiv.ofEq`.
- **Hypotheses**: the two period pairs have equal lattices as submodules of ℂ.
- **Uses from project**: [`map`, `CyclicSublattice`]
- **Used by**: `ofLatticeEq_carrier`, `ofLatticeEq_carrier_map_subtype`, `ofLatticeEq_toPeriodPair_lattice`, `j_ofLatticeEq` (and in `Classification.lean`, `theorem_11_23`)
- **Visibility**: public
- **Lines**: 198–200
- **Notes**: `noncomputable`

### `theorem ofLatticeEq_carrier`
- **Type**: `(S : CyclicSublattice L m) (h : L.lattice = M.lattice) : (S.ofLatticeEq h).carrier = S.carrier.map (LinearEquiv.ofEq L.lattice M.lattice h).toLinearMap`
- **What**: Carrier of the reinterpreted sublattice, unfolded (simp API).
- **How**: `rfl`.
- **Hypotheses**: equal lattices.
- **Uses from project**: [`ofLatticeEq`, `CyclicSublattice`]
- **Used by**: unused in file (public simp API)
- **Visibility**: public
- **Lines**: 202–207, rfl
- **Notes**: tagged `@[simp]`

### `theorem ofLatticeEq_carrier_map_subtype`
- **Type**: `(S : CyclicSublattice L m) (h : L.lattice = M.lattice) : (S.ofLatticeEq h).carrier.map M.lattice.subtype = S.carrier.map L.lattice.subtype`
- **What**: Reinterpreting the ambient period pair does not change the carrier's image in ℂ.
- **How**: Element-chase both inclusions: `LinearEquiv.ofEq` acts as the identity on underlying complex numbers, witnessed by mathlib's `LinearEquiv.coe_ofEq_apply`.
- **Hypotheses**: equal lattices.
- **Uses from project**: [`ofLatticeEq`, `mapCarrier`, `CyclicSublattice`]
- **Used by**: `ofLatticeEq_toPeriodPair_lattice`
- **Visibility**: public
- **Lines**: 210–229, 19-line proof
- **Notes**: none

### `theorem ofLatticeEq_toPeriodPair_lattice`
- **Type**: `(S : CyclicSublattice L m) (h : L.lattice = M.lattice) : (S.ofLatticeEq h).toPeriodPair.lattice = S.toPeriodPair.lattice`
- **What**: Reinterpreting the ambient pair leaves the canonical sub-period-lattice (as a subset of ℂ) unchanged.
- **How**: Rewrite both sides with `toPeriodPair_lattice` and apply `ofLatticeEq_carrier_map_subtype`.
- **Hypotheses**: equal lattices.
- **Uses from project**: [`ofLatticeEq`, `toPeriodPair`, `toPeriodPair_lattice`, `ofLatticeEq_carrier_map_subtype`]
- **Used by**: `j_ofLatticeEq`
- **Visibility**: public
- **Lines**: 233–237, 3-line proof
- **Notes**: none

### `theorem j_ofLatticeEq`
- **Type**: `(S : CyclicSublattice L m) (h : L.lattice = M.lattice) : (S.ofLatticeEq h).j = S.j`
- **What**: The sublattice `j`-invariant is unchanged by reinterpreting the ambient period pair.
- **How**: `PeriodPair.j_congr` (project: equal lattices give equal `j`) applied to `ofLatticeEq_toPeriodPair_lattice`.
- **Hypotheses**: equal lattices.
- **Uses from project**: [`j`, `ofLatticeEq`, `ofLatticeEq_toPeriodPair_lattice`, `PeriodPair.j_congr`]
- **Used by**: unused in file (used in `Classification.lean`, `theorem_11_23`)
- **Visibility**: public
- **Lines**: 240–243, 2-line proof
- **Notes**: none

### `def scale`
- **Type**: `(a : ℂˣ) (S : CyclicSublattice L m) : CyclicSublattice (a • L) m`
- **What**: Scale a cyclic sublattice by a nonzero complex number: gives a cyclic index-`m` sublattice of the scaled period pair `a • L`.
- **How**: `map` along the project's `smulLatticeEquiv a L` (multiplication-by-`a` isomorphism `L.lattice ≃ (a•L).lattice` from `LatticeJ.lean`).
- **Hypotheses**: `a` a unit of ℂ.
- **Uses from project**: [`map`, `smulLatticeEquiv`, `CyclicSublattice`]
- **Used by**: `scale_carrier`, `scale_carrier_map_subtype`, `scale_toPeriodPair_lattice`, `j_scale` (and in `Classification.lean`, `theorem_11_23`)
- **Visibility**: public
- **Lines**: 246–248
- **Notes**: `noncomputable`

### `theorem scale_carrier`
- **Type**: `(a : ℂˣ) (S : CyclicSublattice L m) : (S.scale a).carrier = S.carrier.map (smulLatticeEquiv a L : L.lattice →ₗ[ℤ] (a • L).lattice)`
- **What**: The carrier of the scaled sublattice is the image of the original carrier under multiplication by `a` (simp API).
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`scale`, `smulLatticeEquiv`, `CyclicSublattice`]
- **Used by**: `scale_carrier_map_subtype`
- **Visibility**: public
- **Lines**: 250–255, rfl
- **Notes**: tagged `@[simp]`

### `theorem scale_carrier_map_subtype`
- **Type**: `(a : ℂˣ) (S : CyclicSublattice L m) : (S.scale a).carrier.map (a • L).lattice.subtype = (S.carrier.map L.lattice.subtype).map (a.mulLeftLinearEquiv ℤ ℂ : ℂ →ₗ[ℤ] ℂ)`
- **What**: After embedding in ℂ, the scaled carrier is literally `a · (carrier)` — the image of the embedded carrier under multiplication by `a`.
- **How**: Element-chase in both directions unfolding `scale_carrier` and the definition of `smulLatticeEquiv`, which acts on the underlying complex number as multiplication by `a`.
- **Hypotheses**: none.
- **Uses from project**: [`scale`, `scale_carrier`, `smulLatticeEquiv`, `CyclicSublattice`]
- **Used by**: `scale_toPeriodPair_lattice`
- **Visibility**: public
- **Lines**: 258–278, 20-line proof
- **Notes**: none

### `theorem scale_toPeriodPair_lattice`
- **Type**: `(a : ℂˣ) (S : CyclicSublattice L m) : (S.scale a).toPeriodPair.lattice = (a • S.toPeriodPair).lattice`
- **What**: The canonical period pair of a scaled sublattice spans the correspondingly scaled lattice `a · Λ(S)`.
- **How**: Calc chain: `toPeriodPair_lattice` twice, `scale_carrier_map_subtype` in the middle, and the project lemma `map_lattice_mulLeftLinearEquiv` (LatticeJ) identifying the pushforward of a lattice under multiplication-by-`a` with the lattice of the scaled pair.
- **Hypotheses**: none.
- **Uses from project**: [`scale`, `toPeriodPair`, `toPeriodPair_lattice`, `scale_carrier_map_subtype`, `map_lattice_mulLeftLinearEquiv`]
- **Used by**: `j_scale`
- **Visibility**: public
- **Lines**: 281–294, 13-line proof
- **Notes**: none

### `theorem j_scale`
- **Type**: `(a : ℂˣ) (S : CyclicSublattice L m) : (S.scale a).j = S.j`
- **What**: The sublattice `j`-invariant is a homothety invariant: scaling by `a ∈ ℂˣ` does not change it.
- **How**: `PeriodPair.j_congr` on `scale_toPeriodPair_lattice`, then the project's homothety-invariance `PeriodPair.j_smul`.
- **Hypotheses**: none.
- **Uses from project**: [`j`, `scale`, `scale_toPeriodPair_lattice`, `PeriodPair.j_congr`, `PeriodPair.j_smul`]
- **Used by**: unused in file (used in `Classification.lean`, `theorem_11_23`)
- **Visibility**: public
- **Lines**: 296–301, 5-line proof
- **Notes**: none

### `def carrierToPeriodPairLinearMap` (private)
- **Type**: `(S : CyclicSublattice L m) : S.carrier →ₗ[ℤ] S.toPeriodPair.lattice`
- **What**: The tautological ℤ-linear map sending a carrier element to itself viewed inside the canonical sub-period-lattice.
- **How**: The underlying complex number lies in `S.toPeriodPair.lattice` by `toPeriodPair_lattice`; additivity and ℤ-linearity are `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`toPeriodPair`, `toPeriodPair_lattice`, `CyclicSublattice`]
- **Used by**: `carrierToPeriodPairLinearMap_bijective`, `carrierEquiv`
- **Visibility**: private
- **Lines**: 303–309
- **Notes**: none

### `theorem carrierToPeriodPairLinearMap_bijective` (private)
- **Type**: `(S : CyclicSublattice L m) : Function.Bijective (carrierToPeriodPairLinearMap S)`
- **What**: The tautological map from the carrier to the canonical sub-period-lattice is a bijection.
- **How**: Injectivity: elements are determined by their complex value (`Subtype.ext` twice). Surjectivity: any element of `S.toPeriodPair.lattice` lies in the embedded carrier by `toPeriodPair_lattice`, so it has a preimage.
- **Hypotheses**: none.
- **Uses from project**: [`carrierToPeriodPairLinearMap`, `toPeriodPair_lattice`, `CyclicSublattice`]
- **Used by**: `carrierEquiv`
- **Visibility**: private
- **Lines**: 311–325, 14-line proof
- **Notes**: none

### `def carrierEquiv` (private)
- **Type**: `(S : CyclicSublattice L m) : S.carrier ≃ₗ[ℤ] S.toPeriodPair.lattice`
- **What**: The canonical ℤ-linear isomorphism between the carrier and the lattice of its canonical period pair.
- **How**: `LinearEquiv.ofBijective` on `carrierToPeriodPairLinearMap` with `carrierToPeriodPairLinearMap_bijective`.
- **Hypotheses**: none.
- **Uses from project**: [`carrierToPeriodPairLinearMap`, `carrierToPeriodPairLinearMap_bijective`, `CyclicSublattice`]
- **Used by**: `carrierEquiv_apply_coe`, `transportedBasis`, `transportedBasis_repr_carrierEquiv`, `dualLinearMap`, `dualLinearMap_injective`, `dualLinearMap_basis_zero_eq`, `dualLinearMap_basis_one_eq`
- **Visibility**: private
- **Lines**: 327–330
- **Notes**: `noncomputable`

### `theorem carrierEquiv_apply_coe` (private)
- **Type**: `(S : CyclicSublattice L m) (x : S.carrier) : ((carrierEquiv S x : S.toPeriodPair.lattice) : ℂ) = ((x : L.lattice) : ℂ)`
- **What**: `carrierEquiv` is the identity on underlying complex numbers.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`carrierEquiv`, `toPeriodPair`, `CyclicSublattice`]
- **Used by**: fires via `simp` in `transportedBasis_apply_coe` (and available to other simp calls in the file)
- **Visibility**: private
- **Lines**: 332–336, rfl
- **Notes**: tagged `@[simp]`

### `def transportedBasis` (private)
- **Type**: `(S : CyclicSublattice L m) : Module.Basis (Fin 2) ℤ S.toPeriodPair.lattice`
- **What**: The HNF basis of the carrier transported to a basis of the canonical sub-period-lattice.
- **How**: `Module.Basis.map` of `S.hermiteNormalForm.bN` along `carrierEquiv`.
- **Hypotheses**: none.
- **Uses from project**: [`hermiteNormalForm`, `carrierEquiv`, `toPeriodPair`, `CyclicSublattice`]
- **Used by**: `transportedBasis_repr_carrierEquiv`, `transportedBasis_apply_coe`, `dual_repr_zero_zero`, `dual_repr_one_zero`, `dual_repr_zero_one`, `dual_repr_one_one`, `dualToMatrix_eq`, `dual_index_eq`, `dual_cyclic`
- **Visibility**: private
- **Lines**: 338–340
- **Notes**: `noncomputable`

### `theorem transportedBasis_repr_carrierEquiv` (private)
- **Type**: `(S : CyclicSublattice L m) (x : S.carrier) (i : Fin 2) : (transportedBasis S).repr (carrierEquiv S x) i = S.hermiteNormalForm.bN.repr x i`
- **What**: Coordinates in the transported basis of a transported element agree with coordinates in the original HNF basis.
- **How**: `simp [transportedBasis]` — mathlib's `Basis.map_repr` unfolds the transported representation.
- **Hypotheses**: none.
- **Uses from project**: [`transportedBasis`, `carrierEquiv`, `hermiteNormalForm`, `CyclicSublattice`]
- **Used by**: `dual_repr_zero_zero`, `dual_repr_one_zero`, `dual_repr_zero_one`, `dual_repr_one_one`
- **Visibility**: private
- **Lines**: 342–347, 1-line proof
- **Notes**: tagged `@[simp]`

### `theorem transportedBasis_apply_coe` (private)
- **Type**: `(S : CyclicSublattice L m) (i : Fin 2) : ((transportedBasis S i : S.toPeriodPair.lattice) : ℂ) = (((S.hermiteNormalForm.bN i : S.carrier) : L.lattice) : ℂ)`
- **What**: The transported basis vectors have the same underlying complex numbers as the original HNF basis vectors.
- **How**: `simp [transportedBasis]`, resting on `carrierEquiv_apply_coe`.
- **Hypotheses**: none.
- **Uses from project**: [`transportedBasis`, `hermiteNormalForm`, `carrierEquiv_apply_coe`, `CyclicSublattice`]
- **Used by**: unused in file (private simp lemma, no explicit call site)
- **Visibility**: private
- **Lines**: 349–353, 1-line proof
- **Notes**: tagged `@[simp]`

### `def d` (private)
- **Type**: `(S : CyclicSublattice L m) : ℤ`
- **What**: The `(0,0)` entry of the HNF matrix — the coefficient `d` in Cox's normal form `[d, aτ+b]` (matrix `!![d, b; 0, a]`).
- **How**: Projection of `S.hermiteNormalForm.matrix`.
- **Hypotheses**: none.
- **Uses from project**: [`hermiteNormalForm`, `CyclicSublattice`]
- **Used by**: `d_pos`, `originalMatrix_eq`, `d_mul_a_eq_m`, `dualMatrix`, `nsmul_basis_zero_repr_zero`, `nsmul_basis_one_repr_zero`, `nsmul_basis_one_repr_one`, `nsmul_basis_one_eq`, `dualLinearMap_basis_one_eq`, `dual_index_eq`, `dual_content_eq_one`
- **Visibility**: private
- **Lines**: 355–356
- **Notes**: none

### `def b` (private)
- **Type**: `(S : CyclicSublattice L m) : ℤ`
- **What**: The `(0,1)` entry of the HNF matrix — the reduced off-diagonal coefficient `b`, `0 ≤ b < d`.
- **How**: Projection of `S.hermiteNormalForm.matrix`.
- **Hypotheses**: none.
- **Uses from project**: [`hermiteNormalForm`, `CyclicSublattice`]
- **Used by**: `originalMatrix_eq`, `dualMatrix`, `nsmul_basis_one_repr_zero`, `nsmul_basis_one_repr_one`, `nsmul_basis_one_eq`, `dualLinearMap_basis_one_eq`, `dual_content_eq_one`
- **Visibility**: private
- **Lines**: 358–359
- **Notes**: none

### `def a` (private)
- **Type**: `(S : CyclicSublattice L m) : ℤ`
- **What**: The `(1,1)` entry of the HNF matrix — the coefficient `a` with `a·d = m`.
- **How**: Projection of `S.hermiteNormalForm.matrix`.
- **Hypotheses**: none.
- **Uses from project**: [`hermiteNormalForm`, `CyclicSublattice`]
- **Used by**: `a_pos`, `originalMatrix_eq`, `d_mul_a_eq_m`, `dualMatrix`, `nsmul_basis_zero_repr_zero`, `nsmul_basis_zero_eq`, `nsmul_basis_one_repr_one`, `dualLinearMap_basis_zero_eq`, `dual_index_eq`, `dual_content_eq_one`
- **Visibility**: private
- **Lines**: 361–362
- **Notes**: none

### `theorem d_pos` (private)
- **Type**: `(S : CyclicSublattice L m) : 0 < d S`
- **What**: Positivity of the HNF diagonal entry `d`.
- **How**: The project HNF normalization `IsColumnHermiteNormalForm.diagonal_pos`.
- **Hypotheses**: none.
- **Uses from project**: [`d`, `hermiteNormalForm`, `Matrix.IsColumnHermiteNormalForm.diagonal_pos`]
- **Used by**: `d_mul_a_eq_m`
- **Visibility**: private
- **Lines**: 364–365
- **Notes**: none

### `theorem a_pos` (private)
- **Type**: `(S : CyclicSublattice L m) : 0 < a S`
- **What**: Positivity of the HNF diagonal entry `a`.
- **How**: `IsColumnHermiteNormalForm.diagonal_pos`.
- **Hypotheses**: none.
- **Uses from project**: [`a`, `hermiteNormalForm`, `Matrix.IsColumnHermiteNormalForm.diagonal_pos`]
- **Used by**: `d_mul_a_eq_m`
- **Visibility**: private
- **Lines**: 367–368
- **Notes**: none

### `theorem lower_left_eq_zero` (private)
- **Type**: `(S : CyclicSublattice L m) : S.hermiteNormalForm.matrix 1 0 = 0`
- **What**: The HNF matrix is upper triangular: its lower-left entry vanishes.
- **How**: `IsColumnHermiteNormalForm.belowDiagonal_eq_zero`.
- **Hypotheses**: none.
- **Uses from project**: [`hermiteNormalForm`, `Matrix.IsColumnHermiteNormalForm.belowDiagonal_eq_zero`]
- **Used by**: `originalMatrix_eq`, `nsmul_basis_zero_repr_one`, `nsmul_basis_one_repr_one`
- **Visibility**: private
- **Lines**: 370–372
- **Notes**: none

### `theorem hermite_repr_apply` (private)
- **Type**: `(S : CyclicSublattice L m) (i j : Fin 2) : L.latticeBasis.repr (((S.hermiteNormalForm.bN j : S.carrier) : L.lattice)) i = S.hermiteNormalForm.matrix i j`
- **What**: The `latticeBasis`-coordinates of the HNF basis vectors are the entries of the HNF matrix (restated in a simp-friendly, doubly-coerced form).
- **How**: The project lemma `HermiteNormalForm.repr_apply`.
- **Hypotheses**: none.
- **Uses from project**: [`hermiteNormalForm`, `Module.Basis.HermiteNormalForm.repr_apply`]
- **Used by**: `nsmul_basis_one_repr_zero`, `nsmul_basis_one_repr_one` (in their `simp only` lists; also available to `simp` in `nsmul_basis_zero_repr_zero/one`)
- **Visibility**: private
- **Lines**: 374–379
- **Notes**: tagged `@[simp]`

### `theorem originalMatrix_eq` (private)
- **Type**: `(S : CyclicSublattice L m) : S.hermiteNormalForm.matrix = !![d S, b S; 0, a S]`
- **What**: Full entry-wise description of the HNF matrix as the Cox normal form `!![d, b; 0, a]`.
- **How**: `fin_cases` on both indices; the three named entries are definitional, the lower-left is `lower_left_eq_zero`.
- **Hypotheses**: none.
- **Uses from project**: [`hermiteNormalForm`, `d`, `b`, `a`, `lower_left_eq_zero`]
- **Used by**: `d_mul_a_eq_m`, `dual_content_eq_one`
- **Visibility**: private
- **Lines**: 381–385, 4-line proof
- **Notes**: none

### `theorem d_mul_a_eq_m` (private)
- **Type**: `(S : CyclicSublattice L m) : d S * a S = (m : ℤ)`
- **What**: The determinant relation of Cox Lemma 11.24: the diagonal entries of the HNF multiply to the index, `d·a = m`.
- **How**: The project lemma `HermiteNormalForm.index_eq_natAbs_det` gives `|det| = index = m`; the determinant of the triangular matrix `!![d,b;0,a]` is `d·a` (mathlib `Matrix.det_fin_two_of`), which is positive by `d_pos`, `a_pos`, so the absolute value drops.
- **Hypotheses**: none (index equality is a structure field).
- **Uses from project**: [`d`, `a`, `hermiteNormalForm`, `originalMatrix_eq`, `d_pos`, `a_pos`, `Module.Basis.HermiteNormalForm.index_eq_natAbs_det`]
- **Used by**: `nsmul_basis_zero_repr_zero`, `nsmul_basis_one_repr_one`, `dual_index_eq`
- **Visibility**: private
- **Lines**: 387–396, 9-line proof
- **Notes**: none

### `theorem index_nsmul_mem_carrier` (private)
- **Type**: `(S : CyclicSublattice L m) (x : L.lattice) : (m : ℕ) • x ∈ S.carrier`
- **What**: Multiplication by the index lands any lattice element inside the sublattice — Lagrange's theorem for abelian groups, `m·L ⊆ L'`.
- **How**: Mathlib's `AddSubgroup.nsmul_index_mem` (from `Mathlib.GroupTheory.IndexNSmul`) combined with the structure field `index_eq`.
- **Hypotheses**: none.
- **Uses from project**: [`CyclicSublattice`]
- **Used by**: `dualLinearMap`, `nsmul_basis_zero_eq`, `nsmul_basis_one_eq`, `dualLinearMap_basis_zero_eq`, `dualLinearMap_basis_one_eq`
- **Visibility**: private
- **Lines**: 398–401, 2-line proof
- **Notes**: none

### `def dualLinearMap` (private)
- **Type**: `(S : CyclicSublattice L m) : L.lattice →ₗ[ℤ] S.toPeriodPair.lattice`
- **What**: The dual-isogeny map on lattices: sends `x ∈ L` to `m·x`, viewed inside the sublattice's period lattice (legitimate since `m·L ⊆ L'`).
- **How**: Composes multiplication-by-`m` (into the carrier, via `index_nsmul_mem_carrier`) with `carrierEquiv`; linearity by `Subtype.ext` and `smul_comm`.
- **Hypotheses**: none.
- **Uses from project**: [`carrierEquiv`, `index_nsmul_mem_carrier`, `toPeriodPair`, `CyclicSublattice`]
- **Used by**: `dualLinearMap_injective`, `dualCarrier`, `dualBasis`, `dualLinearMap_basis_zero_eq`, `dualLinearMap_basis_one_eq`, `dual_repr_zero_zero`, `dual_repr_one_zero`, `dual_repr_zero_one`, `dual_repr_one_one`, `dualToMatrix_eq`, `dualLinearMap_apply_coe`, `dualCarrier_map_subtype_aux`
- **Visibility**: private
- **Lines**: 403–415
- **Notes**: none

### `theorem dualLinearMap_injective` (private)
- **Type**: `(S : CyclicSublattice L m) : Function.Injective (dualLinearMap S)`
- **What**: The dual map `x ↦ m·x` is injective on the lattice.
- **How**: `carrierEquiv` is injective, and multiplication by `m ≠ 0` is injective on the torsion-free lattice via mathlib's `AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree`.
- **Hypotheses**: `m ≠ 0` (from `ℕ+`); the lattice is torsion-free (instance).
- **Uses from project**: [`dualLinearMap`, `carrierEquiv`, `CyclicSublattice`]
- **Used by**: `dualBasis`
- **Visibility**: private
- **Lines**: 417–423, 6-line proof
- **Notes**: none

### `def dualCarrier` (private)
- **Type**: `(S : CyclicSublattice L m) : Submodule ℤ S.toPeriodPair.lattice`
- **What**: The carrier of the dual cyclic sublattice: the image `m·L` inside the sublattice's period lattice.
- **How**: `LinearMap.range (dualLinearMap S)`.
- **Hypotheses**: none.
- **Uses from project**: [`dualLinearMap`, `toPeriodPair`, `CyclicSublattice`]
- **Used by**: `dualBasis`, `dualToMatrix_eq`, `dual_index_eq`, `dual_cyclic`, `dualCarrier_map_subtype_aux`, `dual`, `dual_carrier_map_subtype`
- **Visibility**: private
- **Lines**: 425–427
- **Notes**: `noncomputable`

### `def dualBasis` (private)
- **Type**: `(S : CyclicSublattice L m) : Module.Basis (Fin 2) ℤ (dualCarrier S)`
- **What**: A basis of the dual carrier: the image of the standard lattice basis `(ω₁, ω₂)` under the injective dual map.
- **How**: `Basis.map` along `LinearEquiv.ofInjective (dualLinearMap S) (dualLinearMap_injective S)`.
- **Hypotheses**: none.
- **Uses from project**: [`dualCarrier`, `dualLinearMap`, `dualLinearMap_injective`, `CyclicSublattice`]
- **Used by**: `dualToMatrix_eq`, `dual_index_eq`, `dual_cyclic`
- **Visibility**: private
- **Lines**: 429–432
- **Notes**: `noncomputable`

### `def dualMatrix` (private)
- **Type**: `(S : CyclicSublattice L m) : Matrix (Fin 2) (Fin 2) ℤ`
- **What**: The predicted inclusion matrix `!![a, -b; 0, d]` of the dual sublattice — the classical adjugate-like matrix of the dual isogeny.
- **How**: Explicit matrix literal from the HNF entries.
- **Hypotheses**: none.
- **Uses from project**: [`a`, `b`, `d`, `CyclicSublattice`]
- **Used by**: `dual_repr_zero_zero`, `dual_repr_one_zero`, `dual_repr_zero_one`, `dual_repr_one_one`, `dualToMatrix_eq`, `dual_index_eq`, `dual_content_eq_one`
- **Visibility**: private
- **Lines**: 434–435
- **Notes**: none

### `theorem nsmul_basis_zero_repr_zero` (private)
- **Type**: `(S : CyclicSublattice L m) : L.latticeBasis.repr ((m : ℕ) • L.latticeBasis 0) 0 = L.latticeBasis.repr (((a S • S.hermiteNormalForm.bN 0 : S.carrier) : L.lattice)) 0`
- **What**: Coordinate 0 of the identity `m·ω₁ = a·(first HNF vector)`: both sides have `ω₁`-coordinate `m = a·d`.
- **How**: `simp` reduces both representations, then the determinant relation `d_mul_a_eq_m` (with `mul_comm`) closes the arithmetic.
- **Hypotheses**: none.
- **Uses from project**: [`a`, `d`, `hermiteNormalForm`, `d_mul_a_eq_m`, `hermite_repr_apply` (via simp), `CyclicSublattice`]
- **Used by**: `nsmul_basis_zero_eq`
- **Visibility**: private
- **Lines**: 437–442, 2-line proof
- **Notes**: none

### `theorem nsmul_basis_zero_repr_one` (private)
- **Type**: `(S : CyclicSublattice L m) : L.latticeBasis.repr ((m : ℕ) • L.latticeBasis 0) 1 = L.latticeBasis.repr (((a S • S.hermiteNormalForm.bN 0 : S.carrier) : L.lattice)) 1`
- **What**: Coordinate 1 of `m·ω₁ = a·(first HNF vector)`: both sides vanish since the HNF matrix is upper triangular.
- **How**: `simp [lower_left_eq_zero S]`.
- **Hypotheses**: none.
- **Uses from project**: [`a`, `hermiteNormalForm`, `lower_left_eq_zero`, `hermite_repr_apply` (via simp), `CyclicSublattice`]
- **Used by**: `nsmul_basis_zero_eq`
- **Visibility**: private
- **Lines**: 444–448, 1-line proof
- **Notes**: none

### `theorem nsmul_basis_zero_eq` (private)
- **Type**: `(S : CyclicSublattice L m) : (⟨(m : ℕ) • L.latticeBasis 0, _⟩ : S.carrier) = a S • S.hermiteNormalForm.bN 0`
- **What**: In the carrier, `m·ω₁` equals `a` times the first HNF basis vector — the first column of the dual-matrix computation.
- **How**: Coordinates in `L.latticeBasis` determine lattice elements (`repr.injective`); the two coordinates are `nsmul_basis_zero_repr_zero/one`.
- **Hypotheses**: none.
- **Uses from project**: [`a`, `hermiteNormalForm`, `index_nsmul_mem_carrier`, `nsmul_basis_zero_repr_zero`, `nsmul_basis_zero_repr_one`, `CyclicSublattice`]
- **Used by**: `dualLinearMap_basis_zero_eq`
- **Visibility**: private
- **Lines**: 450–458, 8-line proof
- **Notes**: none

### `theorem nsmul_basis_one_repr_zero` (private)
- **Type**: `(S : CyclicSublattice L m) : L.latticeBasis.repr ((m : ℕ) • L.latticeBasis 1) 0 = L.latticeBasis.repr (((-b S • bN 0 + d S • bN 1 : S.carrier) : L.lattice)) 0`
- **What**: Coordinate 0 of `m·ω₂ = -b·(HNF vector 0) + d·(HNF vector 1)`: both sides are `0` since `-b·d + d·b = 0`.
- **How**: A `simp only` with `hermite_repr_apply` and `Basis.repr_self`-type lemmas reduces to the ring identity `0 = -(b·d) + d·b`, closed by `ring`.
- **Hypotheses**: none.
- **Uses from project**: [`b`, `d`, `hermiteNormalForm`, `hermite_repr_apply`, `CyclicSublattice`]
- **Used by**: `nsmul_basis_one_eq`
- **Visibility**: private
- **Lines**: 460–474, 13-line proof
- **Notes**: none

### `theorem nsmul_basis_one_repr_one` (private)
- **Type**: `(S : CyclicSublattice L m) : L.latticeBasis.repr ((m : ℕ) • L.latticeBasis 1) 1 = L.latticeBasis.repr (((-b S • bN 0 + d S • bN 1 : S.carrier) : L.lattice)) 1`
- **What**: Coordinate 1 of `m·ω₂ = -b·(HNF vector 0) + d·(HNF vector 1)`: both sides equal `m = d·a`, using triangularity.
- **How**: `simp only` with `hermite_repr_apply` and `lower_left_eq_zero` reduces to `m = d·a`, closed by `d_mul_a_eq_m`.
- **Hypotheses**: none.
- **Uses from project**: [`b`, `d`, `a`, `hermiteNormalForm`, `hermite_repr_apply`, `lower_left_eq_zero`, `d_mul_a_eq_m`, `CyclicSublattice`]
- **Used by**: `nsmul_basis_one_eq`
- **Visibility**: private
- **Lines**: 476–489, 12-line proof
- **Notes**: none

### `theorem nsmul_basis_one_eq` (private)
- **Type**: `(S : CyclicSublattice L m) : (⟨(m : ℕ) • L.latticeBasis 1, _⟩ : S.carrier) = -b S • bN 0 + d S • bN 1`
- **What**: In the carrier, `m·ω₂ = -b·(HNF vector 0) + d·(HNF vector 1)` — the second column of the dual-matrix computation.
- **How**: Basis-coordinate injectivity (`repr.injective`) with the two coordinate lemmas `nsmul_basis_one_repr_zero/one`.
- **Hypotheses**: none.
- **Uses from project**: [`b`, `d`, `hermiteNormalForm`, `index_nsmul_mem_carrier`, `nsmul_basis_one_repr_zero`, `nsmul_basis_one_repr_one`, `CyclicSublattice`]
- **Used by**: `dualLinearMap_basis_one_eq`
- **Visibility**: private
- **Lines**: 491–499, 8-line proof
- **Notes**: none

### `theorem dualLinearMap_basis_zero_eq` (private)
- **Type**: `(S : CyclicSublattice L m) : dualLinearMap S (L.latticeBasis 0) = carrierEquiv S (a S • S.hermiteNormalForm.bN 0)`
- **What**: The dual map sends `ω₁` to (the transport of) `a·(HNF vector 0)`.
- **How**: Unfold `dualLinearMap` and apply `congrArg (carrierEquiv S)` to `nsmul_basis_zero_eq`.
- **Hypotheses**: none.
- **Uses from project**: [`dualLinearMap`, `carrierEquiv`, `a`, `hermiteNormalForm`, `index_nsmul_mem_carrier`, `nsmul_basis_zero_eq`]
- **Used by**: `dual_repr_zero_zero`, `dual_repr_one_zero`
- **Visibility**: private
- **Lines**: 501–506, 3-line proof
- **Notes**: none

### `theorem dualLinearMap_basis_one_eq` (private)
- **Type**: `(S : CyclicSublattice L m) : dualLinearMap S (L.latticeBasis 1) = carrierEquiv S (-b S • bN 0 + d S • bN 1)`
- **What**: The dual map sends `ω₂` to (the transport of) `-b·(HNF vector 0) + d·(HNF vector 1)`.
- **How**: Unfold and `congrArg (carrierEquiv S)` on `nsmul_basis_one_eq`.
- **Hypotheses**: none.
- **Uses from project**: [`dualLinearMap`, `carrierEquiv`, `b`, `d`, `hermiteNormalForm`, `index_nsmul_mem_carrier`, `nsmul_basis_one_eq`]
- **Used by**: `dual_repr_zero_one`, `dual_repr_one_one`
- **Visibility**: private
- **Lines**: 508–513, 3-line proof
- **Notes**: none

### `theorem dual_repr_zero_zero` (private)
- **Type**: `(S : CyclicSublattice L m) : (transportedBasis S).repr (dualLinearMap S (L.latticeBasis 0)) 0 = dualMatrix S 0 0`
- **What**: Entry (0,0) of the dual inclusion matrix equals `a`.
- **How**: Rewrite with `dualLinearMap_basis_zero_eq` and `transportedBasis_repr_carrierEquiv`; a `simp only` computes the HNF-basis coordinate of `a • bN 0`.
- **Hypotheses**: none.
- **Uses from project**: [`transportedBasis`, `dualLinearMap`, `dualMatrix`, `dualLinearMap_basis_zero_eq`, `transportedBasis_repr_carrierEquiv`]
- **Used by**: `dualToMatrix_eq`
- **Visibility**: private
- **Lines**: 515–522, 6-line proof
- **Notes**: none

### `theorem dual_repr_one_zero` (private)
- **Type**: `(S : CyclicSublattice L m) : (transportedBasis S).repr (dualLinearMap S (L.latticeBasis 0)) 1 = dualMatrix S 1 0`
- **What**: Entry (1,0) of the dual inclusion matrix equals `0`.
- **How**: Same rewrites as `dual_repr_zero_zero`; `Finsupp.single_eq_of_ne` kills the off-index coordinate.
- **Hypotheses**: none.
- **Uses from project**: [`transportedBasis`, `dualLinearMap`, `dualMatrix`, `dualLinearMap_basis_zero_eq`, `transportedBasis_repr_carrierEquiv`]
- **Used by**: `dualToMatrix_eq`
- **Visibility**: private
- **Lines**: 524–532, 7-line proof
- **Notes**: none

### `theorem dual_repr_zero_one` (private)
- **Type**: `(S : CyclicSublattice L m) : (transportedBasis S).repr (dualLinearMap S (L.latticeBasis 1)) 0 = dualMatrix S 0 1`
- **What**: Entry (0,1) of the dual inclusion matrix equals `-b`.
- **How**: Rewrite with `dualLinearMap_basis_one_eq` and `transportedBasis_repr_carrierEquiv`; `simp only` with `Basis.repr_self`/`Finsupp` lemmas computes the coordinate of `-b • bN 0 + d • bN 1`.
- **Hypotheses**: none.
- **Uses from project**: [`transportedBasis`, `dualLinearMap`, `dualMatrix`, `dualLinearMap_basis_one_eq`, `transportedBasis_repr_carrierEquiv`]
- **Used by**: `dualToMatrix_eq`
- **Visibility**: private
- **Lines**: 534–544, 9-line proof
- **Notes**: none

### `theorem dual_repr_one_one` (private)
- **Type**: `(S : CyclicSublattice L m) : (transportedBasis S).repr (dualLinearMap S (L.latticeBasis 1)) 1 = dualMatrix S 1 1`
- **What**: Entry (1,1) of the dual inclusion matrix equals `d`.
- **How**: Same pattern as `dual_repr_zero_one`.
- **Hypotheses**: none.
- **Uses from project**: [`transportedBasis`, `dualLinearMap`, `dualMatrix`, `dualLinearMap_basis_one_eq`, `transportedBasis_repr_carrierEquiv`]
- **Used by**: `dualToMatrix_eq`
- **Visibility**: private
- **Lines**: 546–556, 9-line proof
- **Notes**: none

### `theorem dualToMatrix_eq` (private)
- **Type**: `(S : CyclicSublattice L m) : LinearMap.toMatrix (dualBasis S) (transportedBasis S) (dualCarrier S).subtype = dualMatrix S`
- **What**: The inclusion matrix of the dual carrier, in the transported/dual bases, is exactly `!![a, -b; 0, d]`.
- **How**: Entry-wise via `LinearMap.toMatrix_apply` and `fin_cases`, delegating each entry to the four `dual_repr_*` lemmas.
- **Hypotheses**: none.
- **Uses from project**: [`dualBasis`, `transportedBasis`, `dualCarrier`, `dualMatrix`, `dualLinearMap`, `dual_repr_zero_zero`, `dual_repr_zero_one`, `dual_repr_one_zero`, `dual_repr_one_one`]
- **Used by**: `dual_index_eq`, `dual_cyclic`
- **Visibility**: private
- **Lines**: 558–568, 10-line proof
- **Notes**: none

### `theorem dual_index_eq` (private)
- **Type**: `(S : CyclicSublattice L m) : (dualCarrier S).toAddSubgroup.index = (m : ℕ)`
- **What**: The dual sublattice `mL ⊂ L'` again has index `m`.
- **How**: Mathlib's `AddSubgroup.index_eq_natAbs_det` (index = |det| of the change-of-basis) with `dualToMatrix_eq`; `det !![a,-b;0,d] = a·d = m` by `d_mul_a_eq_m` (via `Matrix.det_fin_two_of`).
- **Hypotheses**: none.
- **Uses from project**: [`dualCarrier`, `transportedBasis`, `dualBasis`, `dualMatrix`, `dualToMatrix_eq`, `a`, `d`, `d_mul_a_eq_m`]
- **Used by**: `dual`
- **Visibility**: private
- **Lines**: 570–585, 15-line proof
- **Notes**: none

### `theorem dual_content_eq_one` (private)
- **Type**: `(S : CyclicSublattice L m) : Matrix.rankTwoContent (dualMatrix S) = 1`
- **What**: The dual matrix `!![a,-b;0,d]` is primitive: the gcd of its entries is 1. Content is symmetric in `(a,b,d)` so primitivity transfers from the original HNF matrix.
- **How**: The original matrix has content 1 because the quotient is cyclic (project lemma `quotient_isAddCyclic_iff_rankTwoContent_eq_one`); a gcd shuffle (`Nat.gcd_comm/left_comm/assoc`) identifies the two contents.
- **Hypotheses**: cyclicity of `L/L'` (structure field `cyclic`).
- **Uses from project**: [`dualMatrix`, `hermiteNormalForm`, `originalMatrix_eq`, `d`, `b`, `a`, `Matrix.rankTwoContent`, `Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`]
- **Used by**: `dual_cyclic`
- **Visibility**: private
- **Lines**: 587–593, 6-line proof
- **Notes**: none

### `theorem dual_cyclic` (private)
- **Type**: `(S : CyclicSublattice L m) : IsAddCyclic (S.toPeriodPair.lattice ⧸ dualCarrier S)`
- **What**: The quotient by the dual sublattice is cyclic, so the dual really is a cyclic sublattice.
- **How**: The project criterion `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` (cyclic ⟺ inclusion matrix has content 1), with the matrix identified by `dualToMatrix_eq` and content computed by `dual_content_eq_one`.
- **Hypotheses**: cyclicity of the original quotient (through `dual_content_eq_one`).
- **Uses from project**: [`toPeriodPair`, `dualCarrier`, `transportedBasis`, `dualBasis`, `dualToMatrix_eq`, `dual_content_eq_one`, `Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one`]
- **Used by**: `dual`
- **Visibility**: private
- **Lines**: 595–600, 4-line proof
- **Notes**: `open Module.Basis.HermiteNormalForm in`

### `def indexUnit` (private)
- **Type**: `(m : ℕ+) : ℂˣ`
- **What**: The positive integer `m` as a unit of ℂ.
- **How**: `Units.mk0` with `m ≠ 0` cast to ℂ.
- **Hypotheses**: `m` positive (from `ℕ+`).
- **Uses from project**: []
- **Used by**: `dualCarrier_map_subtype_aux`, `dual_carrier_map_subtype`
- **Visibility**: private
- **Lines**: 602–603
- **Notes**: none

### `theorem dualLinearMap_apply_coe` (private)
- **Type**: `(S : CyclicSublattice L m) (x : L.lattice) : ((dualLinearMap S x : S.toPeriodPair.lattice) : ℂ) = (m : ℂ) * (x : ℂ)`
- **What**: On underlying complex numbers, the dual map is just multiplication by `m`.
- **How**: `change` unfolds through `carrierEquiv` (which is the identity on ℂ) to `((m • x : L.lattice) : ℂ)`; `simp [nsmul_eq_mul]` finishes.
- **Hypotheses**: none.
- **Uses from project**: [`dualLinearMap`, `toPeriodPair`, `CyclicSublattice`]
- **Used by**: `dualCarrier_map_subtype_aux`
- **Visibility**: private
- **Lines**: 605–610, 2-line proof
- **Notes**: tagged `@[simp]`

### `theorem dualCarrier_map_subtype_aux` (private)
- **Type**: `(S : CyclicSublattice L m) : (dualCarrier S).map S.toPeriodPair.lattice.subtype = (indexUnit m • L).lattice`
- **What**: Embedded in ℂ, the dual carrier is exactly the scaled lattice `m·L`.
- **How**: Element-chase both ways using `dualLinearMap_apply_coe` and the project lemma `PeriodPair.mem_smul_lattice` (LatticeJ) characterizing membership in a scaled lattice.
- **Hypotheses**: none.
- **Uses from project**: [`dualCarrier`, `dualLinearMap`, `dualLinearMap_apply_coe`, `indexUnit`, `toPeriodPair`, `PeriodPair.mem_smul_lattice`]
- **Used by**: `dual_carrier_map_subtype`
- **Visibility**: private
- **Lines**: 612–632, 20-line proof
- **Notes**: none

### `def dual`
- **Type**: `(S : CyclicSublattice L m) : CyclicSublattice S.toPeriodPair m`
- **What**: The dual cyclic inclusion: if `L' ⊂ L` is cyclic of index `m`, then `mL ⊂ L'` is again cyclic of index `m`. This is the dual-isogeny operation used to prove symmetry of the modular equation.
- **How**: Packages `dualCarrier` with `dual_index_eq` and `dual_cyclic`.
- **Hypotheses**: none.
- **Uses from project**: [`CyclicSublattice`, `toPeriodPair`, `dualCarrier`, `dual_index_eq`, `dual_cyclic`]
- **Used by**: `dual_carrier_map_subtype`, `dual_toPeriodPair_lattice`, `dual_sub_j`, `dual_base_j`
- **Visibility**: public
- **Lines**: 634–640
- **Notes**: `noncomputable`

### `theorem dual_carrier_map_subtype`
- **Type**: `(S : CyclicSublattice L m) : S.dual.carrier.map S.toPeriodPair.lattice.subtype = ((Units.mk0 (m : ℂ) _) • L).lattice`
- **What**: Public restatement: the dual sublattice, embedded in ℂ, spans exactly `m·L`.
- **How**: `change` to the private `dualCarrier_map_subtype_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`dual`, `dualCarrier`, `indexUnit`, `dualCarrier_map_subtype_aux`, `toPeriodPair`]
- **Used by**: `dual_toPeriodPair_lattice`
- **Visibility**: public
- **Lines**: 642–648, 3-line proof
- **Notes**: none

### `theorem dual_toPeriodPair_lattice`
- **Type**: `(S : CyclicSublattice L m) : S.dual.toPeriodPair.lattice = ((Units.mk0 (m : ℂ) _) • L).lattice`
- **What**: The canonical period pair of the dual sublattice represents the lattice `m·L`.
- **How**: `toPeriodPair_lattice` for the dual, then `dual_carrier_map_subtype`.
- **Hypotheses**: none.
- **Uses from project**: [`dual`, `toPeriodPair`, `toPeriodPair_lattice`, `dual_carrier_map_subtype`]
- **Used by**: `dual_sub_j`
- **Visibility**: public
- **Lines**: 650–655, 2-line proof
- **Notes**: none

### `theorem dual_sub_j`
- **Type**: `(S : CyclicSublattice L m) : S.dual.j = L.j`
- **What**: The `j`-invariant of the dual sublattice is the `j`-invariant of the original ambient lattice — since `m·L` is homothetic to `L`. This is the analytic heart of the symmetry `Φ_m(X,Y) = ±Φ_m(Y,X)` argument.
- **How**: `PeriodPair.j_congr` on `dual_toPeriodPair_lattice`, then `PeriodPair.j_smul` (homothety invariance of `j`).
- **Hypotheses**: none.
- **Uses from project**: [`dual`, `j`, `dual_toPeriodPair_lattice`, `PeriodPair.j_congr`, `PeriodPair.j_smul`]
- **Used by**: unused in file (symmetry API for downstream files)
- **Visibility**: public
- **Lines**: 657–664, 7-line proof
- **Notes**: none

### `theorem dual_base_j`
- **Type**: `(S : CyclicSublattice L m) : S.toPeriodPair.j = S.j`
- **What**: The `j`-invariant of the ambient period pair of the dual construction agrees with the sublattice `j`-invariant (definitional companion to `dual_sub_j`).
- **How**: `rfl` — `S.j` is defined as `S.toPeriodPair.j`.
- **Hypotheses**: none.
- **Uses from project**: [`toPeriodPair`, `j`, `PeriodPair.j`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 666–667, rfl
- **Notes**: none

### File Summary
- Total declarations: 73 (21 defs + 1 structure, 51 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): `CyclicSublattice` (all), `hermiteNormalForm` (~19), `toPeriodPair` (~14), `toPeriodPair_lattice` (6), `hnfPeriod` (4), `carrierEquiv` (7), `transportedBasis` (9), `dualLinearMap` (12), `dualCarrier` (7), `dualMatrix` (7), `dualBasis` (3), `d` (11), `b` (7), `a` (10), `d_mul_a_eq_m` (3), `index_nsmul_mem_carrier` (5), `lower_left_eq_zero` (3), `dualToMatrix_eq` (2 in-file + entries), `map` (3), `j` (4), `dual` (4), `scale` (4), `ofLatticeEq` (4)
- Unused declarations (not used by anything in this file): `ext`, `map_carrier`, `ofLatticeEq_carrier`, `j_ofLatticeEq`, `j_scale`, `transportedBasis_apply_coe`, `dual_sub_j`, `dual_base_j` (all but `transportedBasis_apply_coe` are public API consumed by `Classification.lean` or downstream; `transportedBasis_apply_coe` is a private simp lemma with no in-file call site)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [] (longest: `toPeriodPair_lattice` 28 lines, `hnfPeriod_eq` 25 lines, `hnfPeriods_linearIndependent` 24 lines)
