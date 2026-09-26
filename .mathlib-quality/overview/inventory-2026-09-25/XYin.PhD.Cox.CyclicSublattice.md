# Inventory: XYin/PhD/Cox/CyclicSublattice.lean  (541 lines)

Cyclic index-`m` sublattices of a period lattice: `CyclicSublattice L m` bundles a submodule `carrier ≤ L.lattice` (mathlib `PeriodPair.lattice`) of index `m` with cyclic quotient. Builds the canonical HNF period pair `toPeriodPair` (columns of the HNF inclusion matrix relative to `L.latticeBasis`), its `j`, transport along lattice equivalences (`map`, `ofLatticeEq`, `scale`), and the dual inclusion `mL ⊂ L' ⊂ L` (`dual`), proving `dual` is again cyclic of index `m` by explicitly computing its inclusion matrix `!![a, -b; 0, d]` (the adjugate of the HNF matrix). Consumed by `CyclicSublattice/Classification.lean` and `Cox/Arithmetic.lean`.

## Declarations

### `structure PeriodPair.CyclicSublattice`
- **Type**: `(L : PeriodPair) (m : ℕ+)`; fields `carrier : Submodule ℤ L.lattice`, `index_eq : carrier.toAddSubgroup.index = (m : ℕ)`, `cyclic : IsAddCyclic (L.lattice ⧸ carrier)`.
- **What**: a sublattice `L' ⊂ L` of index `m` with `L/L'` cyclic (Cox §11.C "cyclic sublattice").
- **How**: structure definition.
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: []
- **Used by**: every declaration in the file; `Classification.lean`, `Arithmetic.lean:44`
- **Visibility**: public
- **Lines**: 24–27
- **Notes**: `carrier` is a submodule of the *subtype* `L.lattice` (not of ℂ), which forces the `map L.lattice.subtype`/`equivSubtypeMap` friction throughout (L107, 170, 203, 222–249, 496). No `Fintype`/`Finite` instance here (finiteness comes only via `Classification.cyclicSublatticeEquivCoxMatrix`).

### `theorem PeriodPair.CyclicSublattice.ext`
- **Type**: `{S T : CyclicSublattice L m} (h : S.carrier = T.carrier) : S = T`
- **What**: cyclic sublattices are determined by their carrier.
- **How**: `cases`, `rfl` (other fields are props).
- **Hypotheses**: equal carriers.
- **Uses from project**: `CyclicSublattice`
- **Used by**: unused in file
- **Visibility**: public, `@[ext]`
- **Lines**: 36–40, proof ≈ 4 lines
- **Notes**: external use `Classification.lean:159`.

### `theorem PeriodPair.CyclicSublattice.carrier_finrank`
- **Type**: `(S : CyclicSublattice L m) : Module.finrank ℤ S.carrier = 2`
- **What**: a finite-index sublattice of a rank-2 lattice has rank 2.
- **How**: `AddSubgroup.finrank_eq_of_finiteIndex` (mathlib `GroupTheory/IndexNSmul.lean:73`) with `FiniteIndex` from `index_eq`, then mathlib `PeriodPair.finrank_lattice` (`Weierstrass.lean:151`); needs `Module.Free/Finite ℤ L.lattice` from `latticeBasis`.
- **Hypotheses**: none beyond the structure.
- **Uses from project**: `CyclicSublattice`
- **Used by**: `hermiteNormalForm` (57)
- **Visibility**: public
- **Lines**: 43–52, proof ≈ 8 lines
- **Notes**: the `letI Free/Finite of_basis` pair (45–46) recurs at `HermiteNormalForm.lean:372–373`, `Classification.lean:100–101`.

### `noncomputable def PeriodPair.CyclicSublattice.hermiteNormalForm`
- **Type**: `(S : CyclicSublattice L m) : Module.Basis.HermiteNormalForm L.latticeBasis S.carrier`
- **What**: the HNF of the carrier relative to the period basis `(ω₁, ω₂)`.
- **How**: `Submodule.hermiteNormalForm` (`HermiteNormalForm.lean:403`) with `carrier_finrank`.
- **Hypotheses**: none.
- **Uses from project**: `Submodule.hermiteNormalForm`, `carrier_finrank`, `CyclicSublattice`
- **Used by**: `hnfPeriod`, `hnfPeriod_eq`, `hnfPeriods_linearIndependent`, `toPeriodPair_lattice`, `transportedBasis`, `d`, `b`, `a`, `d_pos`, `a_pos`, `lower_left_eq_zero`, `hermite_repr_apply`, `originalMatrix_eq`, `d_mul_a_eq_m`, `nsmul_basis_*`, `dualLinearMap_basis_*`, `dual_content_eq_one`
- **Visibility**: public
- **Lines**: 55–57
- **Notes**: external uses `Classification.lean:29, 60, 152, 164, 290`.

### `private noncomputable def PeriodPair.CyclicSublattice.hnfPeriod`
- **Type**: `(S : CyclicSublattice L m) (i : Fin 2) : ℂ := (((S.hermiteNormalForm.bN i : S.carrier) : L.lattice) : ℂ)`
- **What**: the `i`-th HNF basis vector as a complex number.
- **How**: double coercion.
- **Hypotheses**: none.
- **Uses from project**: `hermiteNormalForm`
- **Used by**: `hnfPeriod_eq`, `hnfPeriods_linearIndependent`, `toPeriodPair`, `toPeriodPair_lattice`
- **Visibility**: private
- **Lines**: 59–60
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.hnfPeriod_eq`
- **Type**: `(S) (j : Fin 2) : hnfPeriod S j = (S.hermiteNormalForm.matrix 0 j : ℂ) * L.ω₁ + (S.hermiteNormalForm.matrix 1 j : ℂ) * L.ω₂`
- **What**: the HNF periods are the matrix columns in the basis `ω₁, ω₂`.
- **How**: `Basis.sum_repr` on `L.latticeBasis`, `HermiteNormalForm.repr_apply`, `latticeBasis_zero/one`, `zsmul_eq_mul`.
- **Hypotheses**: none.
- **Uses from project**: `hnfPeriod`, `hermiteNormalForm`, `Module.Basis.HermiteNormalForm.repr_apply`
- **Used by**: `hnfPeriods_linearIndependent` (95)
- **Visibility**: private
- **Lines**: 62–70, proof ≈ 5 lines
- **Notes**: should be the public `toPeriodPair_ω₁`/`toPeriodPair_ω₂` simp lemmas.

### `private theorem PeriodPair.CyclicSublattice.hnfPeriods_linearIndependent`
- **Type**: `(S) : LinearIndependent ℝ ![hnfPeriod S 0, hnfPeriod S 1]`
- **What**: the HNF periods are ℝ-independent (so they form a period pair).
- **How**: mathlib `LinearIndependent.pair_add_smul_add_smul_iff` (`LinearAlgebra/LinearIndependent/Lemmas.lean:330`) applied to `L.indep` with determinant `d·a ≠ 0` from `belowDiagonal_eq_zero`/`diagonal_pos`; `hnfPeriod_eq`.
- **Hypotheses**: none.
- **Uses from project**: `hermiteNormalForm`, `hnfPeriod`, `hnfPeriod_eq`, `Matrix.IsColumnHermiteNormalForm` (fields)
- **Used by**: `toPeriodPair` (103)
- **Visibility**: private
- **Lines**: 72–96, proof ≈ 23 lines
- **Notes**: the `hz/hd/ha` extraction (75–80) is one of 5 sites of the same pattern.

### `noncomputable def PeriodPair.CyclicSublattice.toPeriodPair`
- **Type**: `(S : CyclicSublattice L m) : PeriodPair` with `ω₁ := hnfPeriod S 0`, `ω₂ := hnfPeriod S 1`
- **What**: the canonical period pair of the sublattice (Cox: `[d, aτ + b]` in the normalised case).
- **How**: `hnfPeriods_linearIndependent`.
- **Hypotheses**: none.
- **Uses from project**: `hnfPeriod`, `hnfPeriods_linearIndependent`
- **Used by**: `toPeriodPair_lattice`, `j`, `ofLatticeEq_toPeriodPair_lattice`, `scale_toPeriodPair_lattice`, `carrierToPeriodPairLinearMap`, `carrierEquiv`, `transportedBasis`, `dualLinearMap`, `dualCarrier`, `dual_cyclic`, `dual`, `dual_toPeriodPair_lattice`, `dual_sub_j`, `dual_base_j`
- **Visibility**: public
- **Lines**: 100–103
- **Notes**: external uses `Classification.lean:296`, `Arithmetic.lean:44`.

### `theorem PeriodPair.CyclicSublattice.toPeriodPair_lattice`
- **Type**: `(S) : S.toPeriodPair.lattice = S.carrier.map L.lattice.subtype`
- **What**: the lattice spanned by the HNF periods is the carrier embedded in ℂ.
- **How**: push `S.hermiteNormalForm.bN.span_eq` through `Submodule.map_span`, `LinearMap.range_comp`, `Submodule.range_subtype`, `Set.range_comp`, and identify `Set.range` of the two periods (`Fin.exists_fin_two`).
- **Hypotheses**: none.
- **Uses from project**: `toPeriodPair`, `hermiteNormalForm`, `hnfPeriod`
- **Used by**: `ofLatticeEq_toPeriodPair_lattice` (180), `scale_toPeriodPair_lattice` (212–213), `carrierToPeriodPairLinearMap` (225), `carrierToPeriodPairLinearMap_bijective` (239), `dual_toPeriodPair_lattice` (524)
- **Visibility**: public
- **Lines**: 106–119, proof ≈ 12 lines
- **Notes**: external use `Classification.lean:303`.

### `def PeriodPair.CyclicSublattice.j`
- **Type**: `(S : CyclicSublattice L m) : ℂ := S.toPeriodPair.j`
- **What**: the `j`-invariant of the sublattice.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: `toPeriodPair`, `PeriodPair.j`
- **Used by**: `j_ofLatticeEq`, `j_scale`, `dual_sub_j`, `dual_base_j`
- **Visibility**: public
- **Lines**: 122
- **Notes**: external uses `Classification.lean:312–368`, `Arithmetic.lean:44`. `dual_base_j` (536) is literally this definition unfolded.

### `private def PeriodPair.CyclicSublattice.mapCarrier`
- **Type**: `{M : PeriodPair} (e : L.lattice ≃ₗ[ℤ] M.lattice) (S : CyclicSublattice L m) : Submodule ℤ M.lattice := S.carrier.map e.toLinearMap`
- **What**: image of the carrier under a lattice equivalence.
- **How**: `Submodule.map`.
- **Hypotheses**: none.
- **Uses from project**: `CyclicSublattice`
- **Used by**: `mapCarrier_index`, `mapQuotientEquiv`, `map`
- **Visibility**: private
- **Lines**: 124–126
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.mapCarrier_index`
- **Type**: `(e) (S) : (mapCarrier e S).toAddSubgroup.index = S.carrier.toAddSubgroup.index`
- **What**: index is invariant under transport.
- **How**: `Submodule.map_toAddSubgroup` (mathlib `Algebra/Module/Submodule/Map.lean:494`), `AddSubgroup.index_map_equiv` (`GroupTheory/Index.lean:334`).
- **Hypotheses**: none.
- **Uses from project**: `mapCarrier`
- **Used by**: `map` (144)
- **Visibility**: private
- **Lines**: 128–133, proof ≈ 3 lines
- **Notes**: —

### `private def PeriodPair.CyclicSublattice.mapQuotientEquiv`
- **Type**: `(e) (S) : (L.lattice ⧸ S.carrier) ≃ₗ[ℤ] (M.lattice ⧸ mapCarrier e S)`
- **What**: transported quotient.
- **How**: mathlib `Submodule.Quotient.equiv` (`LinearAlgebra/Quotient/Basic.lean:325`).
- **Hypotheses**: none.
- **Uses from project**: `mapCarrier`
- **Used by**: `map` (146–147)
- **Visibility**: private
- **Lines**: 135–138
- **Notes**: —

### `noncomputable def PeriodPair.CyclicSublattice.map`
- **Type**: `(S : CyclicSublattice L m) (e : L.lattice ≃ₗ[ℤ] M.lattice) : CyclicSublattice M m`
- **What**: transport a cyclic sublattice along a ℤ-linear equivalence of ambient lattices.
- **How**: carrier `mapCarrier`, index by `mapCarrier_index`, cyclicity by `isAddCyclic_of_surjective` (mathlib `SpecificGroups/Cyclic/Basic.lean:185`) through `mapQuotientEquiv`.
- **Hypotheses**: none.
- **Uses from project**: `mapCarrier`, `mapCarrier_index`, `mapQuotientEquiv`, `CyclicSublattice`
- **Used by**: `ofLatticeEq` (158), `scale` (192)
- **Visibility**: public
- **Lines**: 142–147
- **Notes**: defined by `refine`/tactic; no `map_id`, `map_map`, `map_carrier`-based `j_map` lemmas.

### `theorem PeriodPair.CyclicSublattice.map_carrier`
- **Type**: `(S) (e) : (S.map e).carrier = S.carrier.map e.toLinearMap`
- **What**: carrier of the transported sublattice.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `map`
- **Used by**: unused in file
- **Visibility**: public, `@[simp]`
- **Lines**: 150–153
- **Notes**: unused project-wide (`ofLatticeEq_carrier`, `scale_carrier` are proved by `rfl` independently).

### `noncomputable def PeriodPair.CyclicSublattice.ofLatticeEq`
- **Type**: `(S : CyclicSublattice L m) (h : L.lattice = M.lattice) : CyclicSublattice M m`
- **What**: reinterpret `S` inside a period pair with the same lattice.
- **How**: `S.map (LinearEquiv.ofEq _ _ h)`.
- **Hypotheses**: equal lattices.
- **Uses from project**: `map`
- **Used by**: `ofLatticeEq_carrier`, `ofLatticeEq_carrier_map_subtype`, `ofLatticeEq_toPeriodPair_lattice`, `j_ofLatticeEq`
- **Visibility**: public
- **Lines**: 156–158
- **Notes**: external use `Classification.lean:361`.

### `theorem PeriodPair.CyclicSublattice.ofLatticeEq_carrier`
- **Type**: `(S) (h) : (S.ofLatticeEq h).carrier = S.carrier.map (LinearEquiv.ofEq L.lattice M.lattice h).toLinearMap`
- **What**: carrier after reinterpretation.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `ofLatticeEq`
- **Used by**: `ofLatticeEq_carrier_map_subtype` (172)
- **Visibility**: public, `@[simp]`
- **Lines**: 161–165
- **Notes**: —

### `theorem PeriodPair.CyclicSublattice.ofLatticeEq_carrier_map_subtype`
- **Type**: `(S) (h) : (S.ofLatticeEq h).carrier.map M.lattice.subtype = S.carrier.map L.lattice.subtype`
- **What**: the embedded carrier in ℂ is unchanged.
- **How**: `Submodule.map_comp` and `congr 1` (the composite `subtype ∘ ofEq` is `subtype`).
- **Hypotheses**: none.
- **Uses from project**: `ofLatticeEq_carrier`
- **Used by**: `ofLatticeEq_toPeriodPair_lattice` (181)
- **Visibility**: public
- **Lines**: 168–173, proof ≈ 2 lines
- **Notes**: —

### `theorem PeriodPair.CyclicSublattice.ofLatticeEq_toPeriodPair_lattice`
- **Type**: `(S) (h) : (S.ofLatticeEq h).toPeriodPair.lattice = S.toPeriodPair.lattice`
- **What**: the canonical sublattice period lattice is unchanged.
- **How**: `toPeriodPair_lattice` twice + `ofLatticeEq_carrier_map_subtype`.
- **Hypotheses**: none.
- **Uses from project**: `toPeriodPair_lattice`, `ofLatticeEq_carrier_map_subtype`, `ofLatticeEq`
- **Used by**: `j_ofLatticeEq` (187)
- **Visibility**: public
- **Lines**: 177–181, proof ≈ 2 lines
- **Notes**: —

### `theorem PeriodPair.CyclicSublattice.j_ofLatticeEq`
- **Type**: `(S) (h) : (S.ofLatticeEq h).j = S.j`
- **What**: `j` is unchanged by reinterpretation.
- **How**: `PeriodPair.j_congr` + `ofLatticeEq_toPeriodPair_lattice`.
- **Hypotheses**: none.
- **Uses from project**: `j`, `PeriodPair.j_congr`, `ofLatticeEq_toPeriodPair_lattice`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 184–187, proof ≈ 2 lines
- **Notes**: external use `Classification.lean:363`.

### `noncomputable def PeriodPair.CyclicSublattice.scale`
- **Type**: `(a : ℂˣ) (S : CyclicSublattice L m) : CyclicSublattice (a • L) m`
- **What**: scale a cyclic inclusion by a nonzero complex number.
- **How**: `S.map (smulLatticeEquiv a L)` (`LatticeJ.lean:81`).
- **Hypotheses**: none.
- **Uses from project**: `map`, `PeriodPair.smulLatticeEquiv`, `instance SMul ℂˣ PeriodPair`
- **Used by**: `scale_carrier`, `scale_carrier_map_subtype`, `scale_toPeriodPair_lattice`, `j_scale`
- **Visibility**: public
- **Lines**: 190–192
- **Notes**: external use `Classification.lean:361`. No `scale_one`, `scale_scale`.

### `theorem PeriodPair.CyclicSublattice.scale_carrier`
- **Type**: `(a) (S) : (S.scale a).carrier = S.carrier.map (smulLatticeEquiv a L : L.lattice →ₗ[ℤ] (a • L).lattice)`
- **What**: carrier of the scaled sublattice.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `scale`, `PeriodPair.smulLatticeEquiv`
- **Used by**: `scale_carrier_map_subtype` (206)
- **Visibility**: public, `@[simp]`
- **Lines**: 195–199
- **Notes**: —

### `theorem PeriodPair.CyclicSublattice.scale_carrier_map_subtype`
- **Type**: `(a) (S) : (S.scale a).carrier.map (a • L).lattice.subtype = (S.carrier.map L.lattice.subtype).map (a.mulLeftLinearEquiv ℤ ℂ : ℂ →ₗ[ℤ] ℂ)`
- **What**: embedded in ℂ, scaling the carrier is multiplication by `a`.
- **How**: `scale_carrier`, `Submodule.map_comp` twice, `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `scale_carrier`
- **Used by**: `scale_toPeriodPair_lattice` (212)
- **Visibility**: public
- **Lines**: 202–207, proof ≈ 2 lines
- **Notes**: —

### `theorem PeriodPair.CyclicSublattice.scale_toPeriodPair_lattice`
- **Type**: `(a) (S) : (S.scale a).toPeriodPair.lattice = (a • S.toPeriodPair).lattice`
- **What**: the canonical period pair of the scaled sublattice spans the scaled lattice.
- **How**: `toPeriodPair_lattice`, `scale_carrier_map_subtype`, `PeriodPair.map_lattice_mulLeftLinearEquiv` (`LatticeJ.lean:72`).
- **Hypotheses**: none.
- **Uses from project**: `toPeriodPair_lattice`, `scale_carrier_map_subtype`, `PeriodPair.map_lattice_mulLeftLinearEquiv`, `scale`, `toPeriodPair`
- **Used by**: `j_scale` (219)
- **Visibility**: public
- **Lines**: 210–213, proof ≈ 2 lines
- **Notes**: —

### `theorem PeriodPair.CyclicSublattice.j_scale`
- **Type**: `(a) (S) : (S.scale a).j = S.j`
- **What**: `j` of a sublattice is scale-invariant.
- **How**: `PeriodPair.j_congr` (via `scale_toPeriodPair_lattice`) then `PeriodPair.j_smul`.
- **Hypotheses**: none.
- **Uses from project**: `j`, `scale_toPeriodPair_lattice`, `PeriodPair.j_congr`, `PeriodPair.j_smul`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 215–220, proof ≈ 4 lines
- **Notes**: external use `Classification.lean:363`.

### `private def PeriodPair.CyclicSublattice.carrierToPeriodPairLinearMap`
- **Type**: `(S) : S.carrier →ₗ[ℤ] S.toPeriodPair.lattice`, `x ↦ ⟨(x : ℂ), _⟩`
- **What**: the carrier viewed inside the canonical period lattice.
- **How**: membership from `toPeriodPair_lattice`; `map_add'`, `map_smul'` by `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `toPeriodPair_lattice`, `toPeriodPair`
- **Used by**: `carrierToPeriodPairLinearMap_bijective`, `carrierEquiv`
- **Visibility**: private
- **Lines**: 222–228
- **Notes**: hand-rolled; see `carrierEquiv`.

### `private theorem PeriodPair.CyclicSublattice.carrierToPeriodPairLinearMap_bijective`
- **Type**: `(S) : Function.Bijective (carrierToPeriodPairLinearMap S)`
- **What**: that map is a bijection.
- **How**: injective by two `Subtype.ext`; surjective by unpacking membership in `S.carrier.map L.lattice.subtype` via `toPeriodPair_lattice`.
- **Hypotheses**: none.
- **Uses from project**: `carrierToPeriodPairLinearMap`, `toPeriodPair_lattice`
- **Used by**: `carrierEquiv` (249)
- **Visibility**: private
- **Lines**: 230–244, proof ≈ 13 lines
- **Notes**: —

### `private noncomputable def PeriodPair.CyclicSublattice.carrierEquiv`
- **Type**: `(S) : S.carrier ≃ₗ[ℤ] S.toPeriodPair.lattice`
- **What**: the carrier is ℤ-linearly the canonical period lattice.
- **How**: `LinearEquiv.ofBijective` (mathlib `Submodule/Equiv.lean:185`).
- **Hypotheses**: none.
- **Uses from project**: `carrierToPeriodPairLinearMap`, `carrierToPeriodPairLinearMap_bijective`
- **Used by**: `carrierEquiv_apply_coe`, `transportedBasis`, `transportedBasis_repr_carrierEquiv`, `dualLinearMap`, `dualLinearMap_injective`, `dualLinearMap_basis_zero_eq`, `dualLinearMap_basis_one_eq`
- **Visibility**: private
- **Lines**: 246–249
- **Notes**: STILL HAND-ROLLED (L222–249, 28 lines). Scratch-verified replacement: `(Submodule.equivSubtypeMap L.lattice S.carrier).trans (LinearEquiv.ofEq _ _ S.toPeriodPair_lattice.symm)` typechecks (`noncomputable`) and `carrierEquiv_apply_coe` holds for it by `rfl`. Mathlib: `Submodule.equivSubtypeMap` (`Algebra/Module/Submodule/Equiv.lean:219`); `Submodule.equivMapOfInjective` (`Submodule/Map.lean:146`) is the alternative.

### `private theorem PeriodPair.CyclicSublattice.carrierEquiv_apply_coe`
- **Type**: `(S) (x : S.carrier) : ((carrierEquiv S x : S.toPeriodPair.lattice) : ℂ) = ((x : L.lattice) : ℂ)`
- **What**: the equivalence is the identity on complex numbers.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `carrierEquiv`
- **Used by**: unused in file
- **Visibility**: private, `@[simp]`
- **Lines**: 252–255
- **Notes**: unused (junk).

### `private noncomputable def PeriodPair.CyclicSublattice.transportedBasis`
- **Type**: `(S) : Module.Basis (Fin 2) ℤ S.toPeriodPair.lattice := S.hermiteNormalForm.bN.map (carrierEquiv S)`
- **What**: the HNF basis of the carrier transported to the canonical period lattice (= `S.toPeriodPair.latticeBasis` up to coercion).
- **How**: `Basis.map`.
- **Hypotheses**: none.
- **Uses from project**: `hermiteNormalForm`, `carrierEquiv`
- **Used by**: `transportedBasis_repr_carrierEquiv`, `transportedBasis_apply_coe`, `dual_repr_*`, `dualToMatrix_eq`, `dual_index_eq`, `dual_cyclic`
- **Visibility**: private
- **Lines**: 257–259
- **Notes**: mathlib's `S.toPeriodPair.latticeBasis` (`Weierstrass.lean:144`) is the same basis (`latticeBasis_zero/one` = `hnfPeriod 0/1`); not identified.

### `private theorem PeriodPair.CyclicSublattice.transportedBasis_repr_carrierEquiv`
- **Type**: `(S) (x : S.carrier) (i : Fin 2) : (transportedBasis S).repr (carrierEquiv S x) i = S.hermiteNormalForm.bN.repr x i`
- **What**: coordinates are preserved by transport.
- **How**: `simp [transportedBasis]` (`Basis.map_repr`).
- **Hypotheses**: none.
- **Uses from project**: `transportedBasis`, `carrierEquiv`, `hermiteNormalForm`
- **Used by**: `dual_repr_zero_zero`, `dual_repr_one_zero`, `dual_repr_zero_one`, `dual_repr_one_one` (420, 426, 432, 438)
- **Visibility**: private, `@[simp]`
- **Lines**: 262–266, proof ≈ 1 line
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.transportedBasis_apply_coe`
- **Type**: `(S) (i : Fin 2) : ((transportedBasis S i : S.toPeriodPair.lattice) : ℂ) = (((S.hermiteNormalForm.bN i : S.carrier) : L.lattice) : ℂ)`
- **What**: transported basis vectors are the HNF periods.
- **How**: `simp [transportedBasis]`.
- **Hypotheses**: none.
- **Uses from project**: `transportedBasis`, `hermiteNormalForm`
- **Used by**: unused in file
- **Visibility**: private, `@[simp]`
- **Lines**: 269–272, proof ≈ 1 line
- **Notes**: unused (junk).

### `private def PeriodPair.CyclicSublattice.d`
- **Type**: `(S : CyclicSublattice L m) : ℤ := S.hermiteNormalForm.matrix 0 0`
- **What**: the pivot `d = A 0 0` of the HNF matrix `!![d, b; 0, a]` (Cox's `d`).
- **How**: projection of the HNF matrix.
- **Hypotheses**: none.
- **Uses from project**: `hermiteNormalForm`
- **Used by**: `d_pos`, `originalMatrix_eq`, `d_mul_a_eq_m`, `dualMatrix`, `nsmul_basis_zero_repr_zero`, `nsmul_basis_one_repr_zero`, `nsmul_basis_one_repr_one`, `nsmul_basis_one_eq`, `dualLinearMap_basis_one_eq`, `dual_index_eq`, `dual_content_eq_one`
- **Visibility**: private
- **Lines**: 274–275
- **Notes**: private, so `Classification.lean:28–55` re-extracts the same entry as `(A 0 0).natAbs` by hand.

### `private def PeriodPair.CyclicSublattice.b`
- **Type**: `(S : CyclicSublattice L m) : ℤ := S.hermiteNormalForm.matrix 0 1`
- **What**: the corner `b = A 0 1` of the HNF matrix `!![d, b; 0, a]` (Cox's `b`).
- **How**: projection of the HNF matrix.
- **Hypotheses**: none.
- **Uses from project**: `hermiteNormalForm`
- **Used by**: `originalMatrix_eq`, `dualMatrix`, `nsmul_basis_one_repr_zero`, `nsmul_basis_one_repr_one`, `nsmul_basis_one_eq`, `dualLinearMap_basis_one_eq`, `dual_content_eq_one`
- **Visibility**: private
- **Lines**: 277–278
- **Notes**: private, so `Classification.lean:28–55` re-extracts the same entry as `(A 0 1).natAbs` by hand.

### `private def PeriodPair.CyclicSublattice.a`
- **Type**: `(S : CyclicSublattice L m) : ℤ := S.hermiteNormalForm.matrix 1 1`
- **What**: the pivot `a = A 1 1` of the HNF matrix `!![d, b; 0, a]` (Cox's `a`).
- **How**: projection of the HNF matrix.
- **Hypotheses**: none.
- **Uses from project**: `hermiteNormalForm`
- **Used by**: `a_pos`, `originalMatrix_eq`, `d_mul_a_eq_m`, `dualMatrix`, `nsmul_basis_zero_repr_zero`, `nsmul_basis_zero_eq`, `nsmul_basis_one_repr_one`, `dualLinearMap_basis_zero_eq`, `dual_index_eq`, `dual_content_eq_one`
- **Visibility**: private
- **Lines**: 280–281
- **Notes**: private, so `Classification.lean:28–55` re-extracts the same entry as `(A 1 1).natAbs` by hand.

### `private theorem PeriodPair.CyclicSublattice.d_pos`
- **Type**: `(S : CyclicSublattice L m) : 0 < d S`
- **What**: the pivot `d` is positive.
- **How**: `S.hermiteNormalForm.isColumnHermiteNormalForm.diagonal_pos 0`.
- **Hypotheses**: none.
- **Uses from project**: `d`, `hermiteNormalForm`, `Matrix.IsColumnHermiteNormalForm` (field)
- **Used by**: `d_mul_a_eq_m` (315)
- **Visibility**: private
- **Lines**: 283–284, proof ≈ 1 line
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.a_pos`
- **Type**: `(S : CyclicSublattice L m) : 0 < a S`
- **What**: the pivot `a` is positive.
- **How**: `S.hermiteNormalForm.isColumnHermiteNormalForm.diagonal_pos 1`.
- **Hypotheses**: none.
- **Uses from project**: `a`, `hermiteNormalForm`, `Matrix.IsColumnHermiteNormalForm` (field)
- **Used by**: `d_mul_a_eq_m` (315)
- **Visibility**: private
- **Lines**: 286–287, proof ≈ 1 line
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.lower_left_eq_zero`
- **Type**: `(S) : S.hermiteNormalForm.matrix 1 0 = 0`
- **What**: the HNF matrix is upper triangular.
- **How**: `isColumnHermiteNormalForm.belowDiagonal_eq_zero 1 0 (by omega)`.
- **Hypotheses**: none.
- **Uses from project**: `hermiteNormalForm`
- **Used by**: `originalMatrix_eq` (304), `nsmul_basis_zero_repr_one` (367), `nsmul_basis_one_repr_one` (391)
- **Visibility**: private
- **Lines**: 289–291
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.hermite_repr_apply`
- **Type**: `(S) (i j : Fin 2) : L.latticeBasis.repr (((S.hermiteNormalForm.bN j : S.carrier) : L.lattice)) i = S.hermiteNormalForm.matrix i j`
- **What**: coordinates of HNF basis vectors (restatement of `HermiteNormalForm.repr_apply`).
- **How**: `S.hermiteNormalForm.repr_apply i j`.
- **Hypotheses**: none.
- **Uses from project**: `Module.Basis.HermiteNormalForm.repr_apply`, `hermiteNormalForm`
- **Used by**: `nsmul_basis_zero_repr_zero/one`, `nsmul_basis_one_repr_zero/one` (via `simp`, 360, 367, 384, 391)
- **Visibility**: private, `@[simp]`
- **Lines**: 294–298
- **Notes**: verbatim duplicate of `HermiteNormalForm.lean:206` (which is already `@[simp]`); exists only because the coercion form `N.subtype x` vs `(x : L.lattice)` differs syntactically.

### `private theorem PeriodPair.CyclicSublattice.originalMatrix_eq`
- **Type**: `(S) : S.hermiteNormalForm.matrix = !![d S, b S; 0, a S]`
- **What**: the HNF matrix in explicit form.
- **How**: `ext`, `fin_cases`, `simp [d, b, a, lower_left_eq_zero]`.
- **Hypotheses**: none.
- **Uses from project**: `d`, `b`, `a`, `lower_left_eq_zero`, `hermiteNormalForm`
- **Used by**: `d_mul_a_eq_m` (311), `dual_content_eq_one` (474)
- **Visibility**: private
- **Lines**: 300–304, proof ≈ 3 lines
- **Notes**: instance of the missing `HermiteNormalForm.matrix_eq_of_fin_two`.

### `private theorem PeriodPair.CyclicSublattice.d_mul_a_eq_m`
- **Type**: `(S) : d S * a S = (m : ℤ)`
- **What**: the pivots multiply to the index (`det = m`).
- **How**: `HermiteNormalForm.index_eq_natAbs_det` + `S.index_eq`, `originalMatrix_eq`, `Matrix.det_fin_two_of`, `abs_of_pos` with `d_pos`, `a_pos`.
- **Hypotheses**: none.
- **Uses from project**: `Module.Basis.HermiteNormalForm.index_eq_natAbs_det`, `originalMatrix_eq`, `d_pos`, `a_pos`, `d`, `a`, `hermiteNormalForm`, `CyclicSublattice`
- **Used by**: `nsmul_basis_zero_repr_zero` (361), `nsmul_basis_one_repr_one` (391), `dual_index_eq` (467)
- **Visibility**: private
- **Lines**: 306–315, proof ≈ 8 lines
- **Notes**: re-proved as `hmul` at `Classification.lean:37–40`; `Matrix.det_of_upperTriangular` (`Block.lean:324`) would give it in any rank.

### `private theorem PeriodPair.CyclicSublattice.index_nsmul_mem_carrier`
- **Type**: `(S) (x : L.lattice) : (m : ℕ) • x ∈ S.carrier`
- **What**: `m L ⊆ L'` for an index-`m` sublattice.
- **How**: `AddSubgroup.nsmul_index_mem` (to_additive of `Subgroup.pow_index_mem`, mathlib `GroupTheory/OrderOfElement.lean:1187`) + `index_eq`.
- **Hypotheses**: none.
- **Uses from project**: `CyclicSublattice`
- **Used by**: `dualLinearMap` (324), `nsmul_basis_zero_eq` (370), `nsmul_basis_one_eq` (394), `dualLinearMap_basis_zero_eq` (407), `dualLinearMap_basis_one_eq` (414)
- **Visibility**: private
- **Lines**: 317–320, proof ≈ 2 lines
- **Notes**: —

### `private def PeriodPair.CyclicSublattice.dualLinearMap`
- **Type**: `(S) : L.lattice →ₗ[ℤ] S.toPeriodPair.lattice`, `x ↦ carrierEquiv S ⟨(m : ℕ) • x, _⟩`
- **What**: the "multiplication by `m`" map `L → L'` (dual isogeny) landing in the canonical period lattice of `L'`.
- **How**: linearity by `Subtype.ext`, `smul_comm`.
- **Hypotheses**: none.
- **Uses from project**: `carrierEquiv`, `index_nsmul_mem_carrier`, `toPeriodPair`
- **Used by**: `dualLinearMap_injective`, `dualCarrier`, `dualBasis`, `dualLinearMap_basis_*`, `dual_repr_*`, `dualToMatrix_eq`, `dualLinearMap_apply_coe`, `dualCarrier_map_subtype_aux`
- **Visibility**: private
- **Lines**: 322–334
- **Notes**: in matrix terms this is `adjugate H` acting on `L.latticeBasis` (since `H · adj H = m · 1`, mathlib `Matrix.mul_adjugate`, `Adjugate.lean:264`).

### `private theorem PeriodPair.CyclicSublattice.dualLinearMap_injective`
- **Type**: `(S) : Function.Injective (dualLinearMap S)`
- **What**: multiplication by `m` is injective on a torsion-free lattice.
- **How**: `carrierEquiv.injective`, `Subtype.ext_iff`, `AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree` (mathlib `GroupTheory/IndexNSmul.lean:67`).
- **Hypotheses**: none.
- **Uses from project**: `dualLinearMap`, `carrierEquiv`
- **Used by**: `dualBasis` (351)
- **Visibility**: private
- **Lines**: 336–342, proof ≈ 5 lines
- **Notes**: —

### `private noncomputable def PeriodPair.CyclicSublattice.dualCarrier`
- **Type**: `(S) : Submodule ℤ S.toPeriodPair.lattice := LinearMap.range (dualLinearMap S)`
- **What**: the image `mL ⊂ L'` as a submodule of the canonical period lattice.
- **How**: `LinearMap.range`.
- **Hypotheses**: none.
- **Uses from project**: `dualLinearMap`
- **Used by**: `dualBasis`, `dualToMatrix_eq`, `dual_index_eq`, `dual_cyclic`, `dualCarrier_map_subtype_aux`, `dual`, `dual_carrier_map_subtype`
- **Visibility**: private
- **Lines**: 344–346
- **Notes**: —

### `private noncomputable def PeriodPair.CyclicSublattice.dualBasis`
- **Type**: `(S) : Module.Basis (Fin 2) ℤ (dualCarrier S) := L.latticeBasis.map (LinearEquiv.ofInjective (dualLinearMap S) _)`
- **What**: basis of `mL` transported from the period basis of `L`.
- **How**: mathlib `LinearEquiv.ofInjective` (`Submodule/Equiv.lean:167`), `Basis.map`.
- **Hypotheses**: none.
- **Uses from project**: `dualLinearMap`, `dualLinearMap_injective`, `dualCarrier`
- **Used by**: `dualToMatrix_eq`, `dual_index_eq`, `dual_cyclic`
- **Visibility**: private
- **Lines**: 348–351
- **Notes**: same construction as `Classification.lean:122–124`.

### `private def PeriodPair.CyclicSublattice.dualMatrix`
- **Type**: `(S) : Matrix (Fin 2) (Fin 2) ℤ := !![a S, -b S; 0, d S]`
- **What**: the inclusion matrix of `mL ⊂ L'` in the HNF bases.
- **How**: explicit literal.
- **Hypotheses**: none.
- **Uses from project**: `a`, `b`, `d`
- **Used by**: `dual_repr_*`, `dualToMatrix_eq`, `dual_index_eq`, `dual_content_eq_one`
- **Visibility**: private
- **Lines**: 353–354
- **Notes**: STILL HAND-ROLLED: this IS `Matrix.adjugate S.hermiteNormalForm.matrix`. Scratch-verified: `Matrix.adjugate !![d, b; 0, a] = !![a, -b; 0, d]` by `rw [Matrix.adjugate_fin_two_of]; simp` (mathlib `LinearAlgebra/Matrix/Adjugate.lean:380`). With `Matrix.adjugate_mul : adjugate A * A = A.det • 1` (`Adjugate.lean:269`) and `det_adjugate`, L356–468 (entry-by-entry `nsmul_basis_*`, `dual_repr_*`, `dualToMatrix_eq`, `dual_index_eq`; ≈110 lines) collapse.

### `private theorem PeriodPair.CyclicSublattice.nsmul_basis_zero_repr_zero`
- **Type**: `(S) : L.latticeBasis.repr ((m : ℕ) • L.latticeBasis 0) 0 = L.latticeBasis.repr (((a S • S.hermiteNormalForm.bN 0 : S.carrier) : L.lattice)) 0`
- **What**: first coordinate of `m·ω₁` equals that of `a·v₀` (both are `m = a·d`).
- **How**: `simp` (fires `hermite_repr_apply`) then `simpa [d, a, mul_comm] using (d_mul_a_eq_m S).symm`.
- **Hypotheses**: none.
- **Uses from project**: `hermite_repr_apply`, `d_mul_a_eq_m`, `a`, `d`, `hermiteNormalForm`
- **Used by**: `nsmul_basis_zero_eq` (376)
- **Visibility**: private
- **Lines**: 356–361, proof ≈ 2 lines
- **Notes**: non-terminal `simp` at L360.

### `private theorem PeriodPair.CyclicSublattice.nsmul_basis_zero_repr_one`
- **Type**: `(S) : L.latticeBasis.repr ((m : ℕ) • L.latticeBasis 0) 1 = L.latticeBasis.repr (((a S • S.hermiteNormalForm.bN 0 : S.carrier) : L.lattice)) 1`
- **What**: second coordinate of `m·ω₁` equals that of `a·v₀` (both `0`, since `A 1 0 = 0`).
- **How**: `simp [lower_left_eq_zero S]`.
- **Hypotheses**: none.
- **Uses from project**: `hermite_repr_apply`, `lower_left_eq_zero`, `a`, `hermiteNormalForm`
- **Used by**: `nsmul_basis_zero_eq` (377)
- **Visibility**: private
- **Lines**: 363–367, proof ≈ 1 line
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.nsmul_basis_zero_eq`
- **Type**: `(S) : (⟨(m : ℕ) • L.latticeBasis 0, _⟩ : S.carrier) = a S • S.hermiteNormalForm.bN 0`
- **What**: `m·ω₁ = a·v₀` in the carrier.
- **How**: `Subtype.ext`, `latticeBasis.repr.injective`, `fin_cases` with the two coordinate lemmas.
- **Hypotheses**: none.
- **Uses from project**: `index_nsmul_mem_carrier`, `nsmul_basis_zero_repr_zero`, `nsmul_basis_zero_repr_one`, `a`, `hermiteNormalForm`
- **Used by**: `dualLinearMap_basis_zero_eq` (408)
- **Visibility**: private
- **Lines**: 369–377, proof ≈ 6 lines
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.nsmul_basis_one_repr_zero`
- **Type**: `(S) : L.latticeBasis.repr ((m : ℕ) • L.latticeBasis 1) 0 = L.latticeBasis.repr (((-b S • S.hermiteNormalForm.bN 0 + d S • S.hermiteNormalForm.bN 1 : S.carrier) : L.lattice)) 0`
- **What**: first coordinate of `m·ω₂` equals that of `−b·v₀ + d·v₁` (both `0`: `−b·d + d·b`).
- **How**: `simp [d, b, mul_comm]` (via `hermite_repr_apply`).
- **Hypotheses**: none.
- **Uses from project**: `hermite_repr_apply`, `b`, `d`, `hermiteNormalForm`
- **Used by**: `nsmul_basis_one_eq` (400)
- **Visibility**: private
- **Lines**: 379–384, proof ≈ 1 line
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.nsmul_basis_one_repr_one`
- **Type**: `(S) : L.latticeBasis.repr ((m : ℕ) • L.latticeBasis 1) 1 = L.latticeBasis.repr (((-b S • S.hermiteNormalForm.bN 0 + d S • S.hermiteNormalForm.bN 1 : S.carrier) : L.lattice)) 1`
- **What**: second coordinate of `m·ω₂` equals that of `−b·v₀ + d·v₁` (both `m = d·a`).
- **How**: `simpa [lower_left_eq_zero S, d, a] using (d_mul_a_eq_m S).symm`.
- **Hypotheses**: none.
- **Uses from project**: `hermite_repr_apply`, `lower_left_eq_zero`, `d_mul_a_eq_m`, `d`, `a`, `hermiteNormalForm`
- **Used by**: `nsmul_basis_one_eq` (401)
- **Visibility**: private
- **Lines**: 386–391, proof ≈ 1 line
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.nsmul_basis_one_eq`
- **Type**: `(S) : (⟨(m : ℕ) • L.latticeBasis 1, _⟩ : S.carrier) = -b S • S.hermiteNormalForm.bN 0 + d S • S.hermiteNormalForm.bN 1`
- **What**: `m·ω₂ = −b·v₀ + d·v₁` in the carrier.
- **How**: as `nsmul_basis_zero_eq`.
- **Hypotheses**: none.
- **Uses from project**: `index_nsmul_mem_carrier`, `nsmul_basis_one_repr_zero`, `nsmul_basis_one_repr_one`, `b`, `d`, `hermiteNormalForm`
- **Used by**: `dualLinearMap_basis_one_eq` (415)
- **Visibility**: private
- **Lines**: 393–401, proof ≈ 6 lines
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.dualLinearMap_basis_zero_eq`
- **Type**: `(S) : dualLinearMap S (L.latticeBasis 0) = carrierEquiv S (a S • S.hermiteNormalForm.bN 0)`
- **What**: the dual map sends `ω₁` to `a·v₀`.
- **How**: `change` to `carrierEquiv S ⟨m • ω₁, _⟩` and `congrArg (carrierEquiv S) (nsmul_basis_zero_eq S)`.
- **Hypotheses**: none.
- **Uses from project**: `dualLinearMap`, `carrierEquiv`, `index_nsmul_mem_carrier`, `nsmul_basis_zero_eq`, `a`, `hermiteNormalForm`
- **Used by**: `dual_repr_zero_zero` (420), `dual_repr_one_zero` (426)
- **Visibility**: private
- **Lines**: 403–408, proof ≈ 3 lines
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.dualLinearMap_basis_one_eq`
- **Type**: `(S) : dualLinearMap S (L.latticeBasis 1) = carrierEquiv S (-b S • S.hermiteNormalForm.bN 0 + d S • S.hermiteNormalForm.bN 1)`
- **What**: the dual map sends `ω₂` to `−b·v₀ + d·v₁`.
- **How**: `change` + `congrArg (carrierEquiv S) (nsmul_basis_one_eq S)`.
- **Hypotheses**: none.
- **Uses from project**: `dualLinearMap`, `carrierEquiv`, `index_nsmul_mem_carrier`, `nsmul_basis_one_eq`, `b`, `d`, `hermiteNormalForm`
- **Used by**: `dual_repr_zero_one` (432), `dual_repr_one_one` (438)
- **Visibility**: private
- **Lines**: 410–415, proof ≈ 3 lines
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.dual_repr_zero_zero`
- **Type**: `(S) : (transportedBasis S).repr (dualLinearMap S (L.latticeBasis 0)) 0 = dualMatrix S 0 0`
- **What**: entry `(0,0)` of the dual inclusion matrix is `a S`.
- **How**: `dualLinearMap_basis_zero_eq`, `transportedBasis_repr_carrierEquiv`, `simp [dualMatrix]`.
- **Hypotheses**: none.
- **Uses from project**: `transportedBasis`, `dualLinearMap`, `dualMatrix`, `dualLinearMap_basis_zero_eq`, `transportedBasis_repr_carrierEquiv`
- **Used by**: `dualToMatrix_eq` (448)
- **Visibility**: private
- **Lines**: 417–421, proof ≈ 2 lines
- **Notes**: one of four copies of an identical 2-line body.

### `private theorem PeriodPair.CyclicSublattice.dual_repr_one_zero`
- **Type**: `(S) : (transportedBasis S).repr (dualLinearMap S (L.latticeBasis 0)) 1 = dualMatrix S 1 0`
- **What**: entry `(1,0)` of the dual inclusion matrix is `0`.
- **How**: `dualLinearMap_basis_zero_eq`, `transportedBasis_repr_carrierEquiv`, `simp [dualMatrix]`.
- **Hypotheses**: none.
- **Uses from project**: `transportedBasis`, `dualLinearMap`, `dualMatrix`, `dualLinearMap_basis_zero_eq`, `transportedBasis_repr_carrierEquiv`
- **Used by**: `dualToMatrix_eq` (450)
- **Visibility**: private
- **Lines**: 423–427, proof ≈ 2 lines
- **Notes**: one of four copies of an identical 2-line body.

### `private theorem PeriodPair.CyclicSublattice.dual_repr_zero_one`
- **Type**: `(S) : (transportedBasis S).repr (dualLinearMap S (L.latticeBasis 1)) 0 = dualMatrix S 0 1`
- **What**: entry `(0,1)` of the dual inclusion matrix is `-b S`.
- **How**: `dualLinearMap_basis_one_eq`, `transportedBasis_repr_carrierEquiv`, `simp [dualMatrix]`.
- **Hypotheses**: none.
- **Uses from project**: `transportedBasis`, `dualLinearMap`, `dualMatrix`, `dualLinearMap_basis_one_eq`, `transportedBasis_repr_carrierEquiv`
- **Used by**: `dualToMatrix_eq` (449)
- **Visibility**: private
- **Lines**: 429–433, proof ≈ 2 lines
- **Notes**: one of four copies of an identical 2-line body.

### `private theorem PeriodPair.CyclicSublattice.dual_repr_one_one`
- **Type**: `(S) : (transportedBasis S).repr (dualLinearMap S (L.latticeBasis 1)) 1 = dualMatrix S 1 1`
- **What**: entry `(1,1)` of the dual inclusion matrix is `d S`.
- **How**: `dualLinearMap_basis_one_eq`, `transportedBasis_repr_carrierEquiv`, `simp [dualMatrix]`.
- **Hypotheses**: none.
- **Uses from project**: `transportedBasis`, `dualLinearMap`, `dualMatrix`, `dualLinearMap_basis_one_eq`, `transportedBasis_repr_carrierEquiv`
- **Used by**: `dualToMatrix_eq` (451)
- **Visibility**: private
- **Lines**: 435–439, proof ≈ 2 lines
- **Notes**: one of four copies of an identical 2-line body.

### `private theorem PeriodPair.CyclicSublattice.dualToMatrix_eq`
- **Type**: `(S) : LinearMap.toMatrix (dualBasis S) (transportedBasis S) (dualCarrier S).subtype = dualMatrix S`
- **What**: in the transported HNF bases, the inclusion `mL ↪ L'` has matrix `!![a, -b; 0, d]`.
- **How**: `LinearMap.toMatrix_apply`, `change` to `repr (dualLinearMap S (latticeBasis j)) i`, `fin_cases`, the four `dual_repr_*`.
- **Hypotheses**: none.
- **Uses from project**: `dualBasis`, `transportedBasis`, `dualCarrier`, `dualMatrix`, `dualLinearMap`, `dual_repr_zero_zero`, `dual_repr_zero_one`, `dual_repr_one_zero`, `dual_repr_one_one`
- **Used by**: `dual_index_eq` (460), `dual_cyclic` (483)
- **Visibility**: private
- **Lines**: 441–451, proof ≈ 9 lines
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.dual_index_eq`
- **Type**: `(S) : (dualCarrier S).toAddSubgroup.index = (m : ℕ)`
- **What**: `[L' : mL] = m`.
- **How**: mathlib `AddSubgroup.index_eq_natAbs_det` (`FreeModule/Finite/CardQuotient.lean:98`) with `transportedBasis`, `dualBasis`; `Module.Basis.det_apply`, `Basis.toMatrix_apply`, `dualToMatrix_eq`; `det !![a,-b;0,d] = a·d` by `det_fin_two_of`; `d_mul_a_eq_m`.
- **Hypotheses**: none.
- **Uses from project**: `transportedBasis`, `dualCarrier`, `dualBasis`, `dualToMatrix_eq`, `dualMatrix`, `d_mul_a_eq_m`, `a`, `d`
- **Used by**: `dual` (509)
- **Visibility**: private
- **Lines**: 453–468, proof ≈ 14 lines
- **Notes**: with `dualMatrix = adjugate H`, `Matrix.det_adjugate` gives `det = det H = m` directly.

### `private theorem PeriodPair.CyclicSublattice.dual_content_eq_one`
- **Type**: `(S) : Matrix.rankTwoContent (dualMatrix S) = 1`
- **What**: the dual inclusion matrix is primitive.
- **How**: `quotient_isAddCyclic_iff_rankTwoContent_eq_one` on `S.cyclic`, `originalMatrix_eq`, then the AC-gcd `simpa [Matrix.rankTwoContent, dualMatrix, …, Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc]` (gcd is invariant under negating an entry and permuting).
- **Hypotheses**: none.
- **Uses from project**: `Matrix.rankTwoContent`, `Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`, `originalMatrix_eq`, `dualMatrix`, `d`, `b`, `a`, `hermiteNormalForm`, `CyclicSublattice`
- **Used by**: `dual_cyclic` (483)
- **Visibility**: private
- **Lines**: 470–476, proof ≈ 5 lines
- **Notes**: AC-gcd simp idiom (7 sites project-wide).

### `private theorem PeriodPair.CyclicSublattice.dual_cyclic`
- **Type**: `(S) : IsAddCyclic (S.toPeriodPair.lattice ⧸ dualCarrier S)`
- **What**: `L'/mL` is cyclic.
- **How**: `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` (any-basis form) with `transportedBasis`, `dualBasis`, `dualToMatrix_eq`, `dual_content_eq_one`.
- **Hypotheses**: none.
- **Uses from project**: `Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one`, `transportedBasis`, `dualCarrier`, `dualBasis`, `dualToMatrix_eq`, `dual_content_eq_one`
- **Used by**: `dual` (510)
- **Visibility**: private
- **Lines**: 479–483, proof ≈ 3 lines
- **Notes**: `open Module.Basis.HermiteNormalForm in` prefix.

### `private def PeriodPair.CyclicSublattice.indexUnit`
- **Type**: `(m : ℕ+) : ℂˣ := Units.mk0 (m : ℂ) _`
- **What**: the index as a complex unit.
- **How**: `Units.mk0` with `PNat.ne_zero`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `dualCarrier_map_subtype_aux` (497), `dual_carrier_map_subtype` (517)
- **Visibility**: private
- **Lines**: 485–486
- **Notes**: because it is private the public statements L515, L523, L528 inline `Units.mk0 (m : ℂ) (by exact_mod_cast PNat.ne_zero m)`; `Classification.lean:264, 297, 313` do the same for `σ.d`.

### `private theorem PeriodPair.CyclicSublattice.dualLinearMap_apply_coe`
- **Type**: `(S) (x : L.lattice) : ((dualLinearMap S x : S.toPeriodPair.lattice) : ℂ) = (m : ℂ) * (x : ℂ)`
- **What**: the dual map is multiplication by `m` on complex numbers.
- **How**: `change`, `nsmul_eq_mul`.
- **Hypotheses**: none.
- **Uses from project**: `dualLinearMap`
- **Used by**: `dualCarrier_map_subtype_aux` (502)
- **Visibility**: private, `@[simp]`
- **Lines**: 489–493, proof ≈ 2 lines
- **Notes**: —

### `private theorem PeriodPair.CyclicSublattice.dualCarrier_map_subtype_aux`
- **Type**: `(S) : (dualCarrier S).map S.toPeriodPair.lattice.subtype = (indexUnit m • L).lattice`
- **What**: embedded in ℂ, the dual carrier is `m·L`.
- **How**: `LinearMap.range_comp`, `PeriodPair.map_lattice_mulLeftLinearEquiv` (`LatticeJ.lean:72`), `Submodule.range_subtype`, `congr 1`, `dualLinearMap_apply_coe`.
- **Hypotheses**: none.
- **Uses from project**: `dualCarrier`, `indexUnit`, `PeriodPair.map_lattice_mulLeftLinearEquiv`, `dualLinearMap_apply_coe`, `dualLinearMap`, `instance SMul ℂˣ PeriodPair`
- **Used by**: `dual_carrier_map_subtype` (518)
- **Visibility**: private
- **Lines**: 495–502, proof ≈ 5 lines
- **Notes**: —

### `noncomputable def PeriodPair.CyclicSublattice.dual`
- **Type**: `(S : CyclicSublattice L m) : CyclicSublattice S.toPeriodPair m`
- **What**: the dual cyclic inclusion `mL ⊂ L'` of index `m` (the dual isogeny; used for the symmetry of `Φ_m`).
- **How**: carrier `dualCarrier`, `dual_index_eq`, `dual_cyclic`.
- **Hypotheses**: none.
- **Uses from project**: `dualCarrier`, `dual_index_eq`, `dual_cyclic`, `toPeriodPair`, `CyclicSublattice`
- **Used by**: `dual_carrier_map_subtype`, `dual_toPeriodPair_lattice`, `dual_sub_j`
- **Visibility**: public
- **Lines**: 506–510
- **Notes**: external use `Arithmetic.lean:44`. No `dual_dual` lemma.

### `theorem PeriodPair.CyclicSublattice.dual_carrier_map_subtype`
- **Type**: `(S) : S.dual.carrier.map S.toPeriodPair.lattice.subtype = ((Units.mk0 (m : ℂ) _) • L).lattice`
- **What**: the dual carrier spans `mL`.
- **How**: `change` to `indexUnit`, `dualCarrier_map_subtype_aux`.
- **Hypotheses**: none.
- **Uses from project**: `dual`, `dualCarrier`, `indexUnit`, `dualCarrier_map_subtype_aux`, `instance SMul ℂˣ PeriodPair`
- **Used by**: `dual_toPeriodPair_lattice` (525)
- **Visibility**: public
- **Lines**: 513–518, proof ≈ 3 lines
- **Notes**: —

### `theorem PeriodPair.CyclicSublattice.dual_toPeriodPair_lattice`
- **Type**: `(S) : S.dual.toPeriodPair.lattice = ((Units.mk0 (m : ℂ) _) • L).lattice`
- **What**: the canonical period pair of the dual represents `mL`.
- **How**: `toPeriodPair_lattice` + `dual_carrier_map_subtype`.
- **Hypotheses**: none.
- **Uses from project**: `toPeriodPair_lattice`, `dual_carrier_map_subtype`, `dual`
- **Used by**: `dual_sub_j` (533)
- **Visibility**: public
- **Lines**: 521–525, proof ≈ 2 lines
- **Notes**: —

### `theorem PeriodPair.CyclicSublattice.dual_sub_j`
- **Type**: `(S) : S.dual.j = L.j`
- **What**: the `j` of the dual sublattice is the `j` of the original ambient lattice (`j(mL) = j(L)`).
- **How**: `PeriodPair.j_congr` via `dual_toPeriodPair_lattice`, then `PeriodPair.j_smul`.
- **Hypotheses**: none.
- **Uses from project**: `j`, `dual`, `dual_toPeriodPair_lattice`, `PeriodPair.j_congr`, `PeriodPair.j_smul`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 527–534, proof ≈ 6 lines
- **Notes**: external use `Arithmetic.lean:44`; misleading name (`sub`?) — should be `j_dual`.

### `theorem PeriodPair.CyclicSublattice.dual_base_j`
- **Type**: `(S) : S.toPeriodPair.j = S.j`
- **What**: the definition of `S.j`, restated.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `j`, `toPeriodPair`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 536–537
- **Notes**: external use `Arithmetic.lean:44`; name mentions `dual` but the statement does not involve `dual` — should be `j_def`/`toPeriodPair_j`.

## File Summary
- Total declarations: 71 (21 defs, 49 lemmas/theorems, 0 instances, 1 structure); 45 private, 26 public
- Key API (used by 3+ others in the file): `CyclicSublattice`, `hermiteNormalForm` (≈20), `toPeriodPair` (≈14), `toPeriodPair_lattice` (5), `carrierEquiv` (7), `transportedBasis` (8), `d`/`b`/`a`, `index_nsmul_mem_carrier` (5), `dualLinearMap` (9), `dualCarrier` (7), `dualMatrix` (7), `d_mul_a_eq_m` (3), `lower_left_eq_zero` (3)
- Unused declarations (not used by anything in this file): `ext`, `map_carrier`, `j_ofLatticeEq`, `j_scale`, `carrierEquiv_apply_coe`, `transportedBasis_apply_coe`, `dual_sub_j`, `dual_base_j` — of these `map_carrier`, `carrierEquiv_apply_coe`, `transportedBasis_apply_coe` are unused project-wide
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: `hnfPeriods_linearIndependent` ≈23, `dual_index_eq` ≈14, `carrierToPeriodPairLinearMap_bijective` ≈13)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `dualMatrix` (L353–354) is `Matrix.adjugate S.hermiteNormalForm.matrix` — STILL HAND-ROLLED after the Sep 21 cleanup (the HEAD→worktree diff only removed the private `coe_carrier_add`/`coe_carrier_zsmul`). Scratch-verified: `Matrix.adjugate !![d, b; 0, a] = !![a, -b; 0, d]` by `rw [Matrix.adjugate_fin_two_of]; simp` (`Mathlib/LinearAlgebra/Matrix/Adjugate.lean:380`). The dual map `dualLinearMap` (L322) is "multiply by `m = det H`", i.e. `H · adj H = m·1` (`Matrix.mul_adjugate`, `Adjugate.lean:264`; `adjugate_mul`, `:269`). Unlocks: replace `nsmul_basis_*` (L356–401), `dualLinearMap_basis_*` (L403–415), `dual_repr_*` (L417–439), `dualToMatrix_eq` (L441–451), and the determinant step of `dual_index_eq` (L465–467, use `Matrix.det_adjugate`) — ≈110 lines — by one statement `toMatrix dualBasis transportedBasis (dualCarrier S).subtype = adjugate H` proved from `Matrix.toLin_mul`/`adjugate_mul`.
- `carrierEquiv` (L246–249) with `carrierToPeriodPairLinearMap` (L222–228) and `_bijective` (L230–244) — STILL HAND-ROLLED. Scratch-verified: `(Submodule.equivSubtypeMap L.lattice S.carrier).trans (LinearEquiv.ofEq _ _ S.toPeriodPair_lattice.symm) : S.carrier ≃ₗ[ℤ] S.toPeriodPair.lattice` compiles (`noncomputable`) and `carrierEquiv_apply_coe` (L252) holds for it by `rfl`. Mathlib `Submodule.equivSubtypeMap` (`Mathlib/Algebra/Module/Submodule/Equiv.lean:219`); alternative `Submodule.equivMapOfInjective L.lattice.subtype L.lattice.subtype_injective S.carrier` (`Submodule/Map.lean:146`). Unlocks deletion of L222–249 (28 lines).
- `rankTwoContent` in `dual_content_eq_one` (L470–476): see `HermiteNormalForm` inventory (hand-rolled `Finset.gcd`, `Algebra/GCDMonoid/Finset.lean:124`); with `Finset.gcd` the "negate/permute entries" step is `Finset.gcd` congruence + `neg_dvd`.
- `transportedBasis` (L257) coincides with mathlib's `S.toPeriodPair.latticeBasis` (`Elliptic/Weierstrass.lean:144`, `latticeBasis_zero/one`) — not identified; identifying it would let `dual_index_eq` use `PeriodPair`-level API.
- `carrier_finrank` (L43) rides on `AddSubgroup.finrank_eq_of_finiteIndex` (`GroupTheory/IndexNSmul.lean:73`); `index_nsmul_mem_carrier` (L317) on `AddSubgroup.nsmul_index_mem` (to_additive of `Subgroup.pow_index_mem`, `OrderOfElement.lean:1187`); `dualLinearMap_injective` (L336) on `nsmulAddMonoidHom_injective_of_isTorsionFree` (`IndexNSmul.lean:67`); `map` (L142) on `AddSubgroup.index_map_equiv` (`GroupTheory/Index.lean:334`), `Submodule.Quotient.equiv` (`LinearAlgebra/Quotient/Basic.lean:325`), `isAddCyclic_of_surjective` (`SpecificGroups/Cyclic/Basic.lean:185`) — all correct.
- `AddSubgroup.index` / `Submodule.span`: the structure uses `carrier.toAddSubgroup.index` (L26) directly — fine. `ZLattice`/`IsZLattice` (`Mathlib/Algebra/Module/ZLattice/Basic.lean:435`): mathlib already gives `IsZLattice ℝ L.lattice` for `PeriodPair` (`Weierstrass.lean:120`) and `ZLattice.rank` (`:525`), and `Covolume.lean` (doc L31,144) relates index of a sub-ℤ-lattice to covolume ratio; a `CyclicSublattice`-as-`IsZLattice` view is not used and not needed for the current proofs, but an `IsZLattice ℝ (S.carrier.map L.lattice.subtype)` instance would connect to mathlib's covolume/index API. No mathlib notion of "cyclic sublattice of index m" (searched `IsAddCyclic`, `index` in `ZLattice/`).
### Missing API / repeated patterns
- HNF-field extraction `belowDiagonal_eq_zero 1 0 (by omega)` / `diagonal_pos 0`,`1` at L75–80 and L283–291 (also `HermiteNormalForm.lean:246–253`, `Classification.lean:31–36, 63–70`); `originalMatrix_eq` (L300) should be a public `HermiteNormalForm.matrix_eq_of_fin_two`.
- `hermite_repr_apply` (L294) duplicates `HermiteNormalForm.repr_apply` (`HermiteNormalForm.lean:206`) because of `N.subtype x` vs `(x : L.lattice)` syntax; add a `Submodule.coe_subtype`-normalised simp variant upstream and delete this.
- `d_mul_a_eq_m` (L306) re-proved as `hmul` at `Classification.lean:37–40`; both from `index_eq_natAbs_det` + 2×2 det — add public `CyclicSublattice.hnf_det_eq : S.hermiteNormalForm.matrix.det = m` (or `HermiteNormalForm.index_eq_prod_diag` via `Matrix.det_of_upperTriangular`, `Block.lean:324`).
- `Units.mk0 (m : ℂ) (by exact_mod_cast PNat.ne_zero m)` inlined at L515, 523, 528 (and `indexUnit` L485 private); same for `σ.d` at `Classification.lean:264, 297, 313`. Publish `indexUnit` (or a `PNat → ℂˣ` coercion).
- Missing companions: `map_id`, `map_map`, `scale_one`, `scale_scale`, `ofLatticeEq_rfl`, `dual_dual`, `toPeriodPair_ω₁/ω₂` (publish `hnfPeriod_eq` L62), `j_map` for a general equivalence (only `j_ofLatticeEq`, `j_scale` exist and both go through `toPeriodPair_lattice`), `Fintype (CyclicSublattice L m)`.
- The four `dual_repr_*` (L417–439) are four copies of a 3-line body; the two `nsmul_basis_*_eq` (L369, 393) and four `nsmul_basis_*_repr_*` share one skeleton.
### Junk candidates
- `carrierEquiv_apply_coe` (L252–255) and `transportedBasis_apply_coe` (L269–272): `@[simp]` private lemmas never used.
- `map_carrier` (L150–153): unused project-wide (`ofLatticeEq_carrier`, `scale_carrier` are independent `rfl`s).
- `dual_base_j` (L536): `rfl` restatement of `def j`, misnamed.
- `hermite_repr_apply` (L294): duplicate of an existing simp lemma.
- Non-terminal `simp` at L360 (`simp` then `simpa`).
### Moral duplicates within this batch
- `ofLatticeEq_carrier_map_subtype` (L168) ≈ `scale_carrier_map_subtype` (L202): both "`map subtype` commutes with `map e`" via `Submodule.map_comp`; a general `map_carrier_map_subtype (e) : (S.map e).carrier.map M.lattice.subtype = (S.carrier.map L.lattice.subtype).map (…)` would cover both.
- `ofLatticeEq_toPeriodPair_lattice` (L177) / `scale_toPeriodPair_lattice` (L210) / `dual_toPeriodPair_lattice` (L521): identical shape (`toPeriodPair_lattice` + a carrier lemma).
- `j_ofLatticeEq` (L184) / `j_scale` (L215) / `dual_sub_j` (L527): `j_congr` (+ `j_smul`).
- `dualBasis` (L348) ≡ `Classification.lean:122–124` (`latticeBasis.map (LinearEquiv.ofInjective f _)`).
- `d_mul_a_eq_m` (L306) ≡ `Classification.lean:37–40`.
### Generalization notes
- `CyclicSublattice`, `map`, `mapCarrier_index`, `mapQuotientEquiv` (L24–147) use nothing about ℂ or `PeriodPair`: they are "finite-index submodule with cyclic quotient" over any `ℤ`-module and transport along any ℤ-linear equivalence.
- `carrier_finrank` (L43) needs only `Module.Finite ℤ`, `IsTorsionFree ℤ`, `finrank = 2`.
- `dualLinearMap_injective` (L336) needs only `IsTorsionFree ℤ L.lattice` (true for any submodule of a char-0 field).
- `dual_index_eq`, `dual_cyclic` (L453–483) are the general statement "if `N ≤ M` has HNF `H` with `det H = m`, then `m·M ≤ N` has inclusion matrix `adj H`, index `m`, and is cyclic iff `N` is" — valid for any rank-2 free ℤ-module `M`; the ℂ-embedding is only used in `dualCarrier_map_subtype_aux` (L495) and `dual_sub_j` (L527).
