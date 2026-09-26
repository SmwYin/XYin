# Inventory: XYin/PhD/Cox/HermiteNormalForm.lean  (408 lines)

Hermite normal form (HNF) over ℤ relative to a fixed ambient basis: a predicate `Matrix.IsColumnHermiteNormalForm`, a 2×2 gcd-content `Matrix.rankTwoContent`, a constructive 2×2 column-HNF existence theorem (extended Euclid on the bottom row), the bundled structure `Module.Basis.HermiteNormalForm bM N` (basis of `N` + inclusion matrix in HNF), rank-2 uniqueness, index = |det|, and the Cox Ex. 11.16 criterion "quotient cyclic ↔ inclusion matrix primitive" via mathlib's Smith normal form. Imports only mathlib; consumed by `Cox/CyclicSublattice.lean`, `Cox/CyclicSublattice/Classification.lean`, `Cox/CoxMatrices/Basic.lean`.

## Declarations

### `structure Matrix.IsColumnHermiteNormalForm`
- **Type**: `{ι : Type*} [Preorder ι] (A : Matrix ι ι ℤ) : Prop`; fields `belowDiagonal_eq_zero : ∀ i j, j < i → A i j = 0`, `diagonal_pos : ∀ i, 0 < A i i`, `reduced : ∀ i j, i < j → A i j ∈ Set.Ico 0 (A i i)`.
- **What**: `A` is in column Hermite normal form: upper triangular, strictly positive pivots, and every entry above a pivot is the canonical remainder modulo the pivot *in its row* (rank two: `!![d, b; 0, a]` with `0 < d`, `0 < a`, `0 ≤ b < d`).
- **How**: Prop-structure definition.
- **Hypotheses**: index type is preordered.
- **Uses from project**: []
- **Used by**: `isColumnHermiteNormalForm_fin_two`, `exists_hnf_transform`, `exists_right_mul_isColumnHermiteNormalForm`, `HermiteNormalForm` (field), `matrix_eq`.
- **Visibility**: public
- **Lines**: 34–41
- **Notes**: `belowDiagonal_eq_zero` is verbatim `Matrix.BlockTriangular A id` (mathlib `LinearAlgebra/Matrix/Block.lean:61`, verified by a scratch `example`). No `Fin 2` iff-characterisation, no `det`/`det_pos` lemma. Reduction is modulo the row pivot `A i i`, which is NOT the convention of mathlib's `FixedDetMatrices.reps` (`|A 0 1| < |A 1 1|`).

### `def Matrix.rankTwoContent`
- **Type**: `(A : Matrix (Fin 2) (Fin 2) ℤ) : ℕ`
- **What**: the gcd of the absolute values of the four entries of a 2×2 integer matrix (the "content"; `= 1` means primitive).
- **How**: nested `Nat.gcd` on `Int.natAbs`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `rankTwoContent_dvd_entry`, `dvd_rankTwoContent`, `rankTwoContent_dvd_mul_right`, `rankTwoContent_dvd_mul_left`, `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one`, `quotient_isAddCyclic_iff_rankTwoContent_eq_one`.
- **Visibility**: public
- **Lines**: 44–46
- **Notes**: hand-rolled; mathlib `Finset.gcd` (`Algebra/GCDMonoid/Finset.lean:124`) is the natural home (see Observations). Consumed with the same `simp [Matrix.rankTwoContent, …, Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc]` idiom at 7 project sites.

### `private lemma Matrix.rankTwoContent_dvd_entry`
- **Type**: `(A : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) : A.rankTwoContent ∣ (A i j).natAbs`
- **What**: the content divides every entry.
- **How**: `fin_cases i <;> fin_cases j` then explicit chains of `Nat.gcd_dvd_left`/`Nat.gcd_dvd_right` (11-line proof).
- **Hypotheses**: none.
- **Uses from project**: `rankTwoContent`
- **Used by**: `rankTwoContent_dvd_mul_right`, `rankTwoContent_dvd_mul_left`
- **Visibility**: private
- **Lines**: 48–60, proof ≈ 11 lines
- **Notes**: would be one line (`Finset.gcd_dvd`, `Algebra/GCDMonoid/Finset.lean:141`) with a `Finset.gcd` definition.

### `private lemma Matrix.dvd_rankTwoContent`
- **Type**: `{A} {k : ℕ} (h : ∀ i j, k ∣ (A i j).natAbs) : k ∣ A.rankTwoContent`
- **What**: a common divisor of all entries divides the content.
- **How**: `Nat.dvd_gcd` three times.
- **Hypotheses**: `k` divides every `|A i j|`.
- **Uses from project**: `rankTwoContent`
- **Used by**: `rankTwoContent_dvd_mul_right`, `rankTwoContent_dvd_mul_left`
- **Visibility**: private
- **Lines**: 62–64, proof ≈ 1 line
- **Notes**: = `Finset.dvd_gcd` (`Algebra/GCDMonoid/Finset.lean:144`).

### `theorem Matrix.rankTwoContent_dvd_mul_right`
- **Type**: `(A B : Matrix (Fin 2) (Fin 2) ℤ) : A.rankTwoContent ∣ (A * B).rankTwoContent`
- **What**: content of a matrix divides the content of any right multiple.
- **How**: `dvd_rankTwoContent`; each entry of `A * B` is `∑ A i k * B k j` (`Matrix.mul_apply`, `Fin.sum_univ_two`), each term divisible via `rankTwoContent_dvd_entry` and `Int.natCast_dvd`.
- **Hypotheses**: none.
- **Uses from project**: `dvd_rankTwoContent`, `rankTwoContent_dvd_entry`, `rankTwoContent`
- **Used by**: `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` (331, 336)
- **Visibility**: public (was `private` at HEAD; made public in the working tree)
- **Lines**: 67–74, proof ≈ 6 lines
- **Notes**: external consumer `Cox/CoxMatrices/Basic.lean:230–231` (`rankTwoContent_mul_sl`).

### `private lemma Matrix.rankTwoContent_dvd_mul_left`
- **Type**: `(A B) : B.rankTwoContent ∣ (A * B).rankTwoContent`
- **What**: content divides the content of any left multiple.
- **How**: identical skeleton to `_dvd_mul_right` with `dvd_mul_of_dvd_right`.
- **Hypotheses**: none.
- **Uses from project**: `dvd_rankTwoContent`, `rankTwoContent_dvd_entry`, `rankTwoContent`
- **Used by**: `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` (330, 335)
- **Visibility**: private
- **Lines**: 76–83, proof ≈ 6 lines
- **Notes**: because this is private, `Cox/CoxMatrices/Basic.lean:225–231` (`rankTwoContent_mul_sl`) re-derives left invariance under `SL(2,ℤ)` via the `U⁻¹` trick using only `_dvd_mul_right` — make it public.

### `theorem Matrix.isColumnHermiteNormalForm_fin_two`
- **Type**: `{d r a : ℤ} (hd : 0 < d) (ha : 0 < a) (hr0 : 0 ≤ r) (hrd : r < d) : IsColumnHermiteNormalForm !![d, r; 0, a]`
- **What**: the explicit 2×2 shape `!![d, r; 0, a]` with `0<d, 0<a, 0≤r<d` is in column HNF.
- **How**: unfold the three fields, `fin_cases` and `simp_all [Set.mem_Ico]`.
- **Hypotheses**: positivity of pivots, reduced corner.
- **Uses from project**: `IsColumnHermiteNormalForm`
- **Used by**: `exists_hnf_transform` (169)
- **Visibility**: public
- **Lines**: 86–95, proof ≈ 7 lines
- **Notes**: only the `→` direction; the converse extraction (`hd, ha, hb, hz` from `h.isColumnHermiteNormalForm`) is redone by hand at 5 sites (see Observations). External use: `Cox/CoxMatrices/Basic.lean:61`.

### `private lemma Matrix.exists_unit_mul_pos_aux`
- **Type**: `(x : ℤ) (hx : x ≠ 0) : ∃ s : ℤ, IsUnit s ∧ 0 < x * s`
- **What**: a nonzero integer can be made positive by a unit (±1).
- **How**: case on `0 < x`, take `s = 1` or `s = -1`, `omega`.
- **Hypotheses**: `x ≠ 0`.
- **Uses from project**: []
- **Used by**: `exists_hnf_transform` (149)
- **Visibility**: private
- **Lines**: 97–103, proof ≈ 5 lines
- **Notes**: `s := Int.sign x` with mathlib `Int.sign_mul_self_eq_natAbs` (`Data/Int/Init.lean:205`) gives this directly.

### `private lemma Matrix.hnf_transform_det_aux`
- **Type**: `(cg dg u v q s : ℤ) (h : cg * u + dg * v = 1) : Matrix.det !![dg * s, u - q * (dg * s); -(cg * s), v + q * (cg * s)] = s`
- **What**: the column-operation matrix used in the 2×2 HNF reduction has determinant `s`.
- **How**: `Matrix.det_fin_two_of` then `linear_combination s * h`.
- **Hypotheses**: Bézout relation `cg*u + dg*v = 1`.
- **Uses from project**: []
- **Used by**: `exists_hnf_transform` (161)
- **Visibility**: private
- **Lines**: 105–108, proof ≈ 2 lines
- **Notes**: —

### `private lemma Matrix.hnf_transform_mul_aux`
- **Type**: `(a b c d cg dg u v q r g s : ℤ) (hcg : cg * g = c) (hdg : dg * g = d) (hbezout : g = c * u + d * v) (her : r + ((a * dg - b * cg) * s) * q = a * u + b * v) : !![a, b; c, d] * !![dg * s, u - q * (dg * s); -(cg * s), v + q * (cg * s)] = !![(a * dg - b * cg) * s, r; 0, g]`
- **What**: the explicit product identity behind the 2×2 column reduction: multiplying by the Euclid/Bézout column matrix yields an upper-triangular matrix with bottom-right the gcd `g`.
- **How**: `Matrix.mul_fin_two`, `ext`, `fin_cases`, then `ring`/`linear_combination` per entry.
- **Hypotheses**: `g = gcd(c,d)` factorisations, Bézout identity, division-with-remainder relation `her`.
- **Uses from project**: []
- **Used by**: `exists_hnf_transform` (164)
- **Visibility**: private
- **Lines**: 110–121, proof ≈ 7 lines
- **Notes**: 12 explicit integer parameters; purely algebraic.

### `private theorem Matrix.exists_hnf_transform`
- **Type**: `(a b c d : ℤ) (hdet : a * d - b * c ≠ 0) : ∃ B : Matrix (Fin 2) (Fin 2) ℤ, IsUnit B.det ∧ (!![a, b; c, d] * B).IsColumnHermiteNormalForm`
- **What**: constructive 2×2 column HNF: every nonsingular `!![a,b;c,d]` becomes column-HNF after a unimodular column change.
- **How**: extended Euclid on the bottom row: `g = Int.gcd c d`, Bézout coefficients `Int.gcdA/gcdB` (`Int.gcd_eq_gcd_ab`), `cg = c/g, dg = d/g` (`Int.ediv_mul_cancel`), pivot `a*dg - b*cg` made positive by `exists_unit_mul_pos_aux`, top-right reduced by `Int.emod`/`Int.ediv` (`Int.emod_add_mul_ediv`, `Int.emod_nonneg`, `Int.emod_lt_of_pos`), assembled with `hnf_transform_det_aux`, `hnf_transform_mul_aux`, `isColumnHermiteNormalForm_fin_two`.
- **Hypotheses**: nonzero determinant.
- **Uses from project**: `exists_unit_mul_pos_aux`, `hnf_transform_det_aux`, `hnf_transform_mul_aux`, `isColumnHermiteNormalForm_fin_two`, `IsColumnHermiteNormalForm`
- **Used by**: `exists_right_mul_isColumnHermiteNormalForm` (178)
- **Visibility**: private
- **Lines**: 123–169, proof ≈ 44 lines
- **Notes**: proof >30 lines; `grind` at 127. Mathlib's `FixedDetMatrices.reduce`/`reduce_mem_reps`/`induction_on` (`LinearAlgebra/Matrix/FixedDetMatrices.lean:99,175,238`) does the transposed (row, left-`SL₂` action) reduction but to a *different* normal form (`|A 0 1| < |A 1 1|`), so it is not a drop-in replacement.

### `theorem Matrix.exists_right_mul_isColumnHermiteNormalForm`
- **Type**: `(A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det ≠ 0) : ∃ B, IsUnit B.det ∧ (A * B).IsColumnHermiteNormalForm`
- **What**: matrix-level statement of the 2×2 column HNF existence.
- **How**: `Matrix.eta_fin_two A` + `exists_hnf_transform` + `Matrix.det_fin_two`.
- **Hypotheses**: `det A ≠ 0`.
- **Uses from project**: `exists_hnf_transform`, `IsColumnHermiteNormalForm`
- **Used by**: `Submodule.exists_hermiteNormalForm` (391)
- **Visibility**: public
- **Lines**: 173–179, proof ≈ 3 lines
- **Notes**: external use `Cox/CoxMatrices/Basic.lean:347`.

### `structure Module.Basis.HermiteNormalForm`
- **Type**: `{n : ℕ} (bM : Basis (Fin n) ℤ M) (N : Submodule ℤ M)`; fields `bN : Basis (Fin n) ℤ N`, `matrix : Matrix (Fin n) (Fin n) ℤ`, `toMatrix_eq : LinearMap.toMatrix bN bM N.subtype = matrix`, `isColumnHermiteNormalForm : matrix.IsColumnHermiteNormalForm`.
- **What**: bundled HNF data for a full-rank submodule `N ≤ M` relative to a fixed ambient basis: a basis of `N` whose inclusion matrix (columns = coordinates of `bN j` in `bM`) is in column HNF.
- **How**: structure definition, parallel to mathlib's `Basis.SmithNormalForm`.
- **Hypotheses**: `M` an additive commutative group with ℤ-basis `bM`.
- **Uses from project**: `IsColumnHermiteNormalForm`
- **Used by**: every declaration in `namespace HermiteNormalForm`, `Submodule.exists_hermiteNormalForm`, `Submodule.hermiteNormalForm`
- **Visibility**: public
- **Lines**: 189–198
- **Notes**: available in any rank `n`; only rank 2 has existence/uniqueness. Lacks `ext`, `bN_apply_coe`, `matrix_det_pos`, `index_eq_prod_diag` companions.

### `theorem Module.Basis.HermiteNormalForm.repr_apply`
- **Type**: `(h : HermiteNormalForm bM N) (i j : Fin n) : bM.repr (N.subtype (h.bN j)) i = h.matrix i j`
- **What**: the `i`-th ambient coordinate of the `j`-th HNF basis vector is the `(i,j)` matrix entry.
- **How**: rewrite `toMatrix_eq` backwards and `LinearMap.toMatrix_apply`.
- **Hypotheses**: none beyond the structure.
- **Uses from project**: `HermiteNormalForm`
- **Used by**: `bN_eq` (288), `index_eq_natAbs_det` (299)
- **Visibility**: public, `@[simp]`
- **Lines**: 206–208, proof ≈ 1 line
- **Notes**: external uses `Cox/CyclicSublattice.lean:68, 298` (the latter re-states it verbatim as private `hermite_repr_apply`).

### `theorem Module.Basis.HermiteNormalForm.range_toLin_matrix_eq`
- **Type**: `(h : HermiteNormalForm bM N) : LinearMap.range (Matrix.toLin bM bM h.matrix) = N`
- **What**: the column space of the HNF inclusion matrix, read in the ambient basis, is exactly `N`.
- **How**: `toLin bM bM h.matrix = N.subtype ∘ bM.equiv h.bN` by `(LinearMap.toMatrix bM bM).injective` with `LinearMap.toMatrix_comp`, `LinearMap.toMatrix_basis_equiv`, `Matrix.mul_one`; then `LinearEquiv.range_comp`, `Submodule.range_subtype`.
- **Hypotheses**: none beyond the structure.
- **Uses from project**: `HermiteNormalForm`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 212–223, proof ≈ 10 lines
- **Notes**: external use `Cox/CyclicSublattice/Classification.lean:164`. Holds over any commutative ring.

### `private lemma Module.Basis.HermiteNormalForm.matrix_mul_toMatrix_eq`
- **Type**: `(h h' : HermiteNormalForm bM N) : h.matrix * h.bN.toMatrix h'.bN = h'.matrix`
- **What**: two HNF matrices of the same submodule differ by the change-of-basis matrix between their submodule bases.
- **How**: `linearMap_toMatrix_mul_basis_toMatrix`.
- **Hypotheses**: rank 2 (section variable).
- **Uses from project**: `HermiteNormalForm`
- **Used by**: `matrix_eq` (244, 245)
- **Visibility**: private
- **Lines**: 227–230, proof ≈ 2 lines
- **Notes**: —

### `private lemma Module.Basis.HermiteNormalForm.reduced_eq_of_eq_add_mul`
- **Type**: `{d r r' q : ℤ} (hr : r ∈ Set.Ico 0 d) (hr' : r' ∈ Set.Ico 0 d) (e : d * q + r = r') : r = r'`
- **What**: two canonical remainders mod `d` that differ by a multiple of `d` are equal.
- **How**: `r = r % d = r' % d = r'` via `Int.emod_eq_of_lt`, `Int.add_emod`.
- **Hypotheses**: both in `[0, d)`.
- **Uses from project**: []
- **Used by**: `matrix_eq` (272)
- **Visibility**: private
- **Lines**: 232–237, proof ≈ 4 lines
- **Notes**: general integer fact; belongs in an `Int` section, not under `HermiteNormalForm`.

### `theorem Module.Basis.HermiteNormalForm.matrix_eq`
- **Type**: `(h h' : HermiteNormalForm bM N) : h.matrix = h'.matrix` (with `bM : Basis (Fin 2) ℤ M`)
- **What**: uniqueness of the rank-2 HNF inclusion matrix for fixed `bM` and `N`.
- **How**: with `U`, `V` the two change-of-basis matrices, `h.matrix * U = h'.matrix` and `h'.matrix * V = h.matrix` (`matrix_mul_toMatrix_eq`); entry `(1,0)` forces `U 1 0 = 0`; mutual divisibility of positive diagonals (`Int.le_of_dvd`) gives equal diagonals and `U 1 1 = 1`; `reduced_eq_of_eq_add_mul` forces equal `(0,1)` entries; finish by `ext; fin_cases`.
- **Hypotheses**: rank 2.
- **Uses from project**: `matrix_mul_toMatrix_eq`, `reduced_eq_of_eq_add_mul`, `IsColumnHermiteNormalForm` (fields), `HermiteNormalForm`
- **Used by**: `bN_eq` (288)
- **Visibility**: public
- **Lines**: 241–278, proof ≈ 37 lines
- **Notes**: proof >30 lines. External use `Cox/CyclicSublattice/Classification.lean:152`.

### `theorem Module.Basis.HermiteNormalForm.bN_eq`
- **Type**: `(h h' : HermiteNormalForm bM N) : h.bN = h'.bN`
- **What**: the HNF submodule basis is unique in rank 2.
- **How**: `DFunLike.ext`, `Subtype.ext`, `bM.repr.injective`, then `repr_apply` and `matrix_eq`.
- **Hypotheses**: rank 2.
- **Uses from project**: `repr_apply`, `matrix_eq`, `HermiteNormalForm`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 281–288, proof ≈ 7 lines
- **Notes**: unused project-wide (`grep -rnw bN_eq XYin` → only this file).

### `theorem Module.Basis.HermiteNormalForm.index_eq_natAbs_det`
- **Type**: `(h : HermiteNormalForm bM N) : N.toAddSubgroup.index = h.matrix.det.natAbs` (any `n`)
- **What**: the index of a full-rank submodule is the absolute determinant of its HNF inclusion matrix (Cox Ex. 7.15).
- **How**: mathlib `AddSubgroup.index_eq_natAbs_det` (`LinearAlgebra/FreeModule/Finite/CardQuotient.lean:98`) + `Module.Basis.det_apply` (`LinearAlgebra/Determinant.lean:609`) + `repr_apply`.
- **Hypotheses**: none beyond the structure.
- **Uses from project**: `repr_apply`, `HermiteNormalForm`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 294–299, proof ≈ 4 lines
- **Notes**: external uses `Cox/CyclicSublattice.lean:310`, `Classification.lean:39,139`. With `Matrix.det_of_upperTriangular` (`Block.lean:324`) this gives `index = ∏ pivots` in any rank — not stated.

### `theorem Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one`
- **Type**: `(bM : Basis (Fin 2) ℤ M) (N : Submodule ℤ M) (bN : Basis (Fin 2) ℤ N) : IsAddCyclic (M ⧸ N) ↔ Matrix.rankTwoContent (LinearMap.toMatrix bN bM N.subtype) = 1`
- **What**: for ANY bases, the quotient `M/N` is cyclic iff the inclusion matrix is primitive (Cox Ex. 11.16).
- **How**: Smith normal form (`Submodule.smithNormalFormTopBasis`, `smithNormalFormBotBasis`, `smithNormalFormCoeffs`, `smithNormalFormBotBasis_def`, mathlib `LinearAlgebra/FreeModule/PID.lean:599–637`) gives `A = P * diagonal c * Q` with `P, Q` unimodular (`basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`); content is invariant under both multiplications (`rankTwoContent_dvd_mul_left/right`, `Nat.dvd_antisymm`) so `content A = gcd(c₀, c₁)`; `Submodule.quotientEquivPiZMod` (`FreeModule/Finite/Quotient.lean:83`), `RingEquiv.piFinTwo`, `AddGroup.isAddCyclic_prod_iff`, `Nat.card_zmod`, `Nat.coprime_iff_gcd_eq_one`.
- **Hypotheses**: rank 2, `N` full rank (derived from the basis `bN`).
- **Uses from project**: `rankTwoContent`, `rankTwoContent_dvd_mul_left`, `rankTwoContent_dvd_mul_right`
- **Used by**: `quotient_isAddCyclic_iff_rankTwoContent_eq_one` (357)
- **Visibility**: public
- **Lines**: 303–348, proof ≈ 42 lines
- **Notes**: proof >30 lines. External use `Cox/CyclicSublattice.lean:481`. The content-invariance half is the general fact "gcd of entries is invariant under unimodular equivalence" (Smith invariants) and would generalise with `Finset.gcd`.

### `theorem Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`
- **Type**: `(h : HermiteNormalForm bM N) : IsAddCyclic (M ⧸ N) ↔ Matrix.rankTwoContent h.matrix = 1`
- **What**: HNF form of the cyclicity criterion.
- **How**: specialise the previous theorem to `h.bN` and rewrite by `h.toMatrix_eq`.
- **Hypotheses**: rank 2.
- **Uses from project**: `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one`, `rankTwoContent`, `HermiteNormalForm`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 352–357, proof ≈ 2 lines
- **Notes**: external uses `Cox/CyclicSublattice.lean:473`, `Classification.lean:42,142`.

### `theorem Submodule.exists_hermiteNormalForm`
- **Type**: `(bM : Basis (Fin 2) ℤ M) (N : Submodule ℤ M) (hN : Module.finrank ℤ N = 2) : Nonempty (Module.Basis.HermiteNormalForm bM N)`
- **What**: every full-rank rank-2 submodule has an HNF relative to `bM`.
- **How**: start from `Module.finBasis ℤ N`; the inclusion matrix `A` has `det ≠ 0` because `N.subtype ∘ bM.equiv bN₀` is injective (`LinearMap.det_eq_zero_iff_ker_ne_bot`, `LinearMap.det_toMatrix`, `LinearMap.toMatrix_comp`, `toMatrix_basis_equiv`); apply `Matrix.exists_right_mul_isColumnHermiteNormalForm` to get unimodular `B`; re-basis with `Matrix.toLinearEquiv bN₀ B hBunit` (`LinearAlgebra/Matrix/ToLinearEquiv.lean:83`) and `LinearMap.toMatrix_map_left`, `LinearMap.toMatrix_toLin`.
- **Hypotheses**: `finrank ℤ N = 2`.
- **Uses from project**: `Matrix.exists_right_mul_isColumnHermiteNormalForm`, `Module.Basis.HermiteNormalForm`, `Matrix.IsColumnHermiteNormalForm`
- **Used by**: `Submodule.hermiteNormalForm` (406)
- **Visibility**: public
- **Lines**: 369–400, proof ≈ 29 lines
- **Notes**: the "det ≠ 0 ⇒ toLin injective" fragment (378–389) is repeated at `Classification.lean:98–110`.

### `noncomputable def Submodule.hermiteNormalForm`
- **Type**: `(bM : Basis (Fin 2) ℤ M) (N : Submodule ℤ M) (hN : Module.finrank ℤ N = 2) : Module.Basis.HermiteNormalForm bM N`
- **What**: a chosen HNF for `N` (canonical up to the uniqueness theorems).
- **How**: `Classical.choice` of `exists_hermiteNormalForm`.
- **Hypotheses**: `finrank ℤ N = 2`.
- **Uses from project**: `exists_hermiteNormalForm`, `Module.Basis.HermiteNormalForm`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 403–406
- **Notes**: external use `Cox/CyclicSublattice.lean:57`. No `hermiteNormalForm_matrix`/`_bN` characterising simp lemmas (uniqueness must be invoked through `matrix_eq`, as `Classification.lean:152` does).

## File Summary
- Total declarations: 24 (2 defs [`rankTwoContent`, `Submodule.hermiteNormalForm`], 20 lemmas/theorems, 0 instances, 2 structures)
- Key API (used by 3+ others in the file): `Matrix.IsColumnHermiteNormalForm` (5), `Matrix.rankTwoContent` (6), `Module.Basis.HermiteNormalForm` (all namespace members)
- Unused declarations (not used by anything in this file): `range_toLin_matrix_eq`, `bN_eq`, `index_eq_natAbs_det`, `quotient_isAddCyclic_iff_rankTwoContent_eq_one`, `Submodule.hermiteNormalForm` — all except `bN_eq` are used by `CyclicSublattice`/`Classification`/`CoxMatrices`; `bN_eq` is unused project-wide.
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `exists_hnf_transform` (≈44), `matrix_eq` (≈37), `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` (≈42)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `IsColumnHermiteNormalForm.belowDiagonal_eq_zero` (L37) IS `Matrix.BlockTriangular A id` (`Mathlib/LinearAlgebra/Matrix/Block.lean:61`: `∀ ⦃i j⦄, b j < b i → M i j = 0`). Scratch-verified: `example (h : A.IsColumnHermiteNormalForm) : A.BlockTriangular id := fun i j hij => h.belowDiagonal_eq_zero i j hij` and `A.det = A 0 0 * A 1 1` by `rw [Matrix.det_of_upperTriangular (fun i j hij => h.belowDiagonal_eq_zero i j hij)]; simp [Fin.prod_univ_two]` (`Block.lean:324`). Unlocks: `det = ∏ pivots > 0` in ANY rank, replacing the `det_fin_two_of` + `simp only [mul_zero, sub_zero]` computations at `CyclicSublattice.lean:312–313, 465–466` and `Classification.lean:40`, and a rank-`n` `index_eq_prod_diag` from L294.
- `rankTwoContent` (L44) is a hand-rolled `Finset.gcd` (`Mathlib/Algebra/GCDMonoid/Finset.lean:124`, with `gcd_dvd` L141, `dvd_gcd` L144). Scratch check: `(A.rankTwoContent : ℤ) = Finset.univ.gcd (fun p : Fin 2 × Fin 2 => A p.1 p.2)` reduces (after `rw [show univ = {(0,0),(0,1),(1,0),(1,1)} by decide]`, `Finset.gcd_insert`, `Finset.gcd_singleton`, `← Int.coe_gcd`) to the residual goal `↑(Nat.gcd-chain) = ↑(Int.gcd (A 0 0) ↑(Int.gcd (A 0 1) ↑(Int.gcd (A 1 0) (normalize (A 1 1)))))` — i.e. gcd re-association plus `normalize`; not closed within the scratch budget but the identification is exact. Unlocks: L48–64 collapse to `Finset.gcd_dvd`/`Finset.dvd_gcd`; L67–83 become `Finset.dvd_gcd` + `Matrix.mul_apply`; the Smith-invariance argument L327–340 becomes "gcd of entries is invariant under unimodular equivalence" for any `n`.
- `exists_hnf_transform` (L123–169): mathlib's `FixedDetMatrices.reduce` / `reduce_mem_reps` / `induction_on` (`Mathlib/LinearAlgebra/Matrix/FixedDetMatrices.lean:99, 175, 238`) reduce `Δ m` by the LEFT `SL(2,ℤ)`-action to `reps m = {A | A 1 0 = 0 ∧ 0 < A 0 0 ∧ 0 ≤ A 0 1 ∧ |A 0 1| < |A 1 1|}` (L69–70). Transposing converts right-column ops to left-row ops, but mathlib reduces the corner modulo `A 1 1` while the project's `reduced` (L41) reduces modulo `A 0 0`; so mathlib gives existence of *a* triangular representative, not the project's normal form. Mathlib has NO Hermite normal form (`grep -rl Hermite Mathlib` → only `NumberField/Discriminant/Basic.lean`, unrelated).
- `HermiteNormalForm` (L189) parallels `Basis.SmithNormalForm` — the file already rides on `Submodule.smithNormalFormTopBasis/BotBasis/Coeffs` (`FreeModule/PID.lean:599,625,630`) and `Submodule.quotientEquivPiZMod` (`FreeModule/Finite/Quotient.lean:83`) at L310–343.
- `index_eq_natAbs_det` (L294) is a 4-line wrapper over `AddSubgroup.index_eq_natAbs_det` (`FreeModule/Finite/CardQuotient.lean:98`) + `Module.Basis.det_apply` (`Determinant.lean:609`); fine as is.
- `exists_unit_mul_pos_aux` (L97) = `Int.sign x` via `Int.sign_mul_self_eq_natAbs` (`Data/Int/Init.lean:205`).
- `Matrix.toLinearEquiv` (`LinearAlgebra/Matrix/ToLinearEquiv.lean:83`), `LinearMap.toMatrix_map_left` (`ToLin.lean:699`), `LinearMap.det_eq_zero_iff_ker_ne_bot` (`Determinant.lean:351`), `linearMap_toMatrix_mul_basis_toMatrix` (`Matrix/Basis.lean:197`), `AddGroup.isAddCyclic_prod_iff` (to_additive of `Group.isCyclic_prod_iff`, `SpecificGroups/Cyclic.lean:814`) are correctly used.
- `Matrix.SpecialLinearGroup`/`ModularGroup`: not used in this file (the unimodular matrix is carried as `IsUnit B.det`); `CoxMatrices/Basic.lean:345` repackages `exists_right_mul_isColumnHermiteNormalForm` into an `SL(2,ℤ)` statement.
### Missing API / repeated patterns
- Extraction quadruple `hz := h.isColumnHermiteNormalForm.belowDiagonal_eq_zero 1 0 (by omega)`, `hd/ha := diagonal_pos 0/1`, `hr := reduced 0 1 (by omega)` at L246–253, `CyclicSublattice.lean:75–80, 283–291`, `Classification.lean:31–36, 63–70` (5 sites). Add `Matrix.isColumnHermiteNormalForm_fin_two_iff : IsColumnHermiteNormalForm A ↔ A 1 0 = 0 ∧ 0 < A 0 0 ∧ 0 < A 1 1 ∧ A 0 1 ∈ Set.Ico 0 (A 0 0)` and `HermiteNormalForm.matrix_eq_of_fin_two : h.matrix = !![h.matrix 0 0, h.matrix 0 1; 0, h.matrix 1 1]` (currently `originalMatrix_eq` at `CyclicSublattice.lean:300`, private).
- `letI : Module.Free ℤ M := Module.Free.of_basis bM; letI : Module.Finite ℤ M := Module.Finite.of_basis bM` at L372–373, `CyclicSublattice.lean:45–46`, `Classification.lean:100–101`.
- "`det ≠ 0` ⇒ `Matrix.toLin b b A` injective" argued twice (L376–389 and `Classification.lean:98–110`); add `Matrix.toLin_injective_of_det_ne_zero (b : Basis ι R M) [IsDomain R] (h : A.det ≠ 0) : Function.Injective (Matrix.toLin b b A)`.
- AC-gcd simp idiom `simp [Matrix.rankTwoContent, …, Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc]` at L338, `CyclicSublattice.lean:475`, `Classification.lean:46`, `CoxMatrices/Basic.lean:76, 215, 377, 806` (7 sites). Add `Matrix.rankTwoContent_of_fin_two (d b a) : rankTwoContent !![d, b; 0, a] = Nat.gcd (Nat.gcd d.natAbs b.natAbs) a.natAbs`.
- `IsColumnHermiteNormalForm` lacks `det_eq_prod_diag`, `det_pos`, `det_ne_zero`; `HermiteNormalForm` lacks `ext`, `bN_apply_coe`, `matrix_det_pos`; `Submodule.hermiteNormalForm` lacks `_matrix`/`_bN` uniqueness simp lemmas.
### Junk candidates
- `bN_eq` (L281–288): unused anywhere in the project.
- `rankTwoContent_dvd_mul_left` (L76) private while `CoxMatrices/Basic.lean:225–231` works around its privacy — publish it.
- `reduced_eq_of_eq_add_mul` (L232) is a pure `Int` lemma misplaced under `HermiteNormalForm`.
- No dead `#check`/`example`, no commented-out blocks.
### Moral duplicates within this batch
- `rankTwoContent_dvd_mul_right` (L67) / `rankTwoContent_dvd_mul_left` (L76): identical proof skeleton (left/right).
- `repr_apply` (L206) ≡ `CyclicSublattice.lean:294 hermite_repr_apply` (private restatement for `L.latticeBasis`).
- `matrix_eq`'s divisibility-antisymmetry step (L266–270) and `CyclicSublattice.lean:306 d_mul_a_eq_m` / `Classification.lean:37–40 hmul` all re-derive "diag product = m" from `index_eq_natAbs_det` + 2×2 det.
### Generalization notes
- `repr_apply` (L206), `range_toLin_matrix_eq` (L212), `matrix_mul_toMatrix_eq` (L227) use only `LinearMap.toMatrix`/`Basis` API — valid over any `CommRing R`; they are ℤ-only because `IsColumnHermiteNormalForm` is stated over ℤ.
- `IsColumnHermiteNormalForm` needs only an ordered ring with a remainder system (`Set.Ico 0 (A i i)`); `matrix_eq` (L241) uses `Int.le_of_dvd` and `Int.emod_eq_of_lt` — any Euclidean domain with canonical nonnegative remainders (ℤ) — mathlib has no such abstraction.
- `quotient_isAddCyclic_iff_…` (L303) is ℤ-specific through `ZMod`/`Nat.card_zmod`; the content-invariance half is PID-general.
- `exists_hermiteNormalForm` (L369) is rank-2 only because `exists_right_mul_isColumnHermiteNormalForm` is 2×2; a rank-`n` version needs a general HNF algorithm absent from mathlib.
