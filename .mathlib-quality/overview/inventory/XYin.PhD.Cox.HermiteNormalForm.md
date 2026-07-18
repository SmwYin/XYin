# XYin/PhD/Cox/HermiteNormalForm.lean

**Source**: `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/HermiteNormalForm.lean`
**Project-internal imports**: none (mathlib only: `Mathlib.Algebra.Ring.Fin`, `Mathlib.GroupTheory.SpecificGroups.Cyclic`, `Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient`, `Mathlib.LinearAlgebra.Matrix.ToLinearEquiv`)

File purpose: develops the (column) Hermite normal form API for full-rank ℤ-submodules relative to a fixed ambient basis, targeting Cox "Primes of the form x² + ny²", Chapter 11 (sublattices of a rank-two lattice). Unlike Smith normal form, HNF is canonical only after fixing the ambient basis, so the basis is a parameter of the bundled structure. Existence and uniqueness are proved in rank two; the structure itself is stated in arbitrary finite rank.

### `structure Matrix.IsColumnHermiteNormalForm`
- **Type**: `{ι : Type*} [Preorder ι] (A : Matrix ι ι ℤ) : Prop`, with fields `belowDiagonal_eq_zero : ∀ i j, j < i → A i j = 0`, `diagonal_pos : ∀ i, 0 < A i i`, `reduced : ∀ i j, i < j → A i j ∈ Set.Ico 0 (A i i)`
- **What**: The predicate "A is in column Hermite normal form": upper triangular, strictly positive diagonal pivots, and each entry above a pivot is the canonical nonnegative remainder mod that pivot. In rank two this is the shape `!![d, b; 0, a]` with 0 < d, 0 < a, 0 ≤ b < d.
- **How**: Prop-valued structure with three field conditions; note reduction is against the row pivot `A i i` (entry `A i j`, i < j, reduced mod `A i i`).
- **Hypotheses**: index type carries a preorder (to state below/above diagonal).
- **Uses from project**: []
- **Used by**: `isColumnHermiteNormalForm_fin_two`, `exists_hnf_transform`, `exists_right_mul_isColumnHermiteNormalForm`, `Module.Basis.HermiteNormalForm` (field), `matrix_eq` (via fields)
- **Visibility**: public
- **Lines**: 33–40
- **Notes**: docstring explains the rank-two shape

### `def Matrix.rankTwoContent`
- **Type**: `(A : Matrix (Fin 2) (Fin 2) ℤ) : ℕ`
- **What**: The content of a 2×2 integer matrix: the gcd of the absolute values of its four entries. Content 1 ("primitive") is the criterion for the quotient by the column lattice to be cyclic.
- **How**: Iterated `Nat.gcd` of `(A i j).natAbs` over the four entries.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `rankTwoContent_dvd_entry`, `dvd_rankTwoContent`, `rankTwoContent_dvd_mul_right`, `rankTwoContent_dvd_mul_left`, `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one`, `quotient_isAddCyclic_iff_rankTwoContent_eq_one`
- **Visibility**: public
- **Lines**: 43–45
- **Notes**: none

### `lemma Matrix.rankTwoContent_dvd_entry`
- **Type**: `(A : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) : A.rankTwoContent ∣ (A i j).natAbs`
- **What**: The content divides (the absolute value of) every entry of the matrix.
- **How**: Case analysis on the four positions, unfolding the nested gcd via chains of `Nat.gcd_dvd_left`/`Nat.gcd_dvd_right`.
- **Hypotheses**: none.
- **Uses from project**: [`Matrix.rankTwoContent`]
- **Used by**: `rankTwoContent_dvd_mul_right`, `rankTwoContent_dvd_mul_left`
- **Visibility**: private
- **Lines**: 47–59, proof 12 lines
- **Notes**: none

### `lemma Matrix.dvd_rankTwoContent`
- **Type**: `{A : Matrix (Fin 2) (Fin 2) ℤ} {k : ℕ} (h : ∀ i j, k ∣ (A i j).natAbs) : k ∣ A.rankTwoContent`
- **What**: The content is the greatest common divisor: any common divisor of all four entries divides the content.
- **How**: Direct `Nat.dvd_gcd` nesting matching the definition.
- **Hypotheses**: k divides every entry's absolute value.
- **Uses from project**: [`Matrix.rankTwoContent`]
- **Used by**: `rankTwoContent_dvd_mul_right`, `rankTwoContent_dvd_mul_left`
- **Visibility**: private
- **Lines**: 61–63, proof 1 line
- **Notes**: none

### `lemma Matrix.rankTwoContent_dvd_mul_right`
- **Type**: `(A B : Matrix (Fin 2) (Fin 2) ℤ) : A.rankTwoContent ∣ (A * B).rankTwoContent`
- **What**: The content of the left factor divides the content of a product — content only grows under right multiplication (so it is invariant under unimodular column operations).
- **How**: Each entry of A·B is `A i 0 * B 0 j + A i 1 * B 1 j` (`Matrix.mul_apply`, `Fin.sum_univ_two`); the content of A divides both summands via `rankTwoContent_dvd_entry`, hence the sum, and `dvd_rankTwoContent` finishes.
- **Hypotheses**: none.
- **Uses from project**: [`Matrix.rankTwoContent`, `rankTwoContent_dvd_entry`, `dvd_rankTwoContent`]
- **Used by**: `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one`
- **Visibility**: private
- **Lines**: 65–72, proof 6 lines
- **Notes**: none

### `lemma Matrix.rankTwoContent_dvd_mul_left`
- **Type**: `(A B : Matrix (Fin 2) (Fin 2) ℤ) : B.rankTwoContent ∣ (A * B).rankTwoContent`
- **What**: The content of the right factor also divides the content of a product (invariance under unimodular row operations).
- **How**: Mirror of `rankTwoContent_dvd_mul_right`: divisibility of each entry of the product via `rankTwoContent_dvd_entry` on B's entries, then `dvd_rankTwoContent`.
- **Hypotheses**: none.
- **Uses from project**: [`Matrix.rankTwoContent`, `rankTwoContent_dvd_entry`, `dvd_rankTwoContent`]
- **Used by**: `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one`
- **Visibility**: private
- **Lines**: 74–81, proof 6 lines
- **Notes**: none

### `theorem Matrix.isColumnHermiteNormalForm_fin_two`
- **Type**: `{d r a : ℤ} (hd : 0 < d) (ha : 0 < a) (hr0 : 0 ≤ r) (hrd : r < d) : IsColumnHermiteNormalForm !![d, r; 0, a]`
- **What**: The concrete 2×2 matrix `!![d, r; 0, a]` with positive pivots and reduced upper entry is in column HNF — the constructor lemma for the rank-two case.
- **How**: Checks the three structure fields by `fin_cases` on the index pairs and `simp_all` with `Set.mem_Ico`.
- **Hypotheses**: 0 < d, 0 < a, 0 ≤ r < d.
- **Uses from project**: [`Matrix.IsColumnHermiteNormalForm`]
- **Used by**: `exists_hnf_transform`
- **Visibility**: public
- **Lines**: 84–93, proof 7 lines
- **Notes**: none

### `lemma Matrix.exists_unit_mul_pos_aux`
- **Type**: `(x : ℤ) (hx : x ≠ 0) : ∃ s : ℤ, IsUnit s ∧ 0 < x * s`
- **What**: Every nonzero integer can be made positive by multiplying by a unit (±1) — the sign normalisation used to make the HNF pivot positive.
- **How**: Case split on 0 < x, returning s = 1 or s = −1 (`isUnit_one`, `isUnit_neg_one`) with `omega` for the sign arithmetic.
- **Hypotheses**: x ≠ 0.
- **Uses from project**: []
- **Used by**: `exists_hnf_transform`
- **Visibility**: private
- **Lines**: 95–101, proof 5 lines
- **Notes**: none

### `lemma Matrix.hnf_transform_det_aux`
- **Type**: `(cg dg u v q s : ℤ) (h : cg * u + dg * v = 1) : Matrix.det !![dg * s, u - q * (dg * s); -(cg * s), v + q * (cg * s)] = s`
- **What**: The explicit column-transformation matrix built from Bézout data (with reduced cofactors satisfying cg·u + dg·v = 1) has determinant s — so it is unimodular when s = ±1.
- **How**: `Matrix.det_fin_two_of` and a `ring`-normalised calc reducing the determinant to s·(cg·u + dg·v) = s.
- **Hypotheses**: the Bézout-cofactor identity cg·u + dg·v = 1.
- **Uses from project**: []
- **Used by**: `exists_hnf_transform`
- **Visibility**: private
- **Lines**: 103–109, proof 5 lines
- **Notes**: none

### `lemma Matrix.hnf_transform_mul_aux`
- **Type**: `(a b c d cg dg u v q r g s : ℤ) (hcg : cg * g = c) (hdg : dg * g = d) (hbezout : g = c * u + d * v) (her : r + ((a * dg - b * cg) * s) * q = a * u + b * v) : !![a, b; c, d] * !![dg * s, u - q * (dg * s); -(cg * s), v + q * (cg * s)] = !![(a * dg - b * cg) * s, r; 0, g]`
- **What**: The algebraic core of HNF existence: multiplying `!![a,b;c,d]` on the right by the Bézout transformation matrix produces the upper-triangular matrix with pivot `(a·dg − b·cg)·s`, reduced entry r, and gcd g = gcd(c,d) in the corner. The bottom-left entry vanishes because c·dg = d·cg (both equal cd/g).
- **How**: Entrywise verification (`Matrix.mul_fin_two`, `fin_cases`) with `ring` computations; the (0,1) entry uses the Euclidean-division relation `her` and the (1,·) entries substitute cg·g = c, dg·g = d and the Bézout identity.
- **Hypotheses**: cg, dg are the cofactors of c, d by their gcd g; g = c·u + d·v (Bézout); r is the remainder of a·u + b·v modulo the signed pivot.
- **Uses from project**: []
- **Used by**: `exists_hnf_transform`
- **Visibility**: private
- **Lines**: 111–131, proof 17 lines
- **Notes**: none

### `theorem Matrix.exists_hnf_transform`
- **Type**: `(a b c d : ℤ) (hdet : a * d - b * c ≠ 0) : ∃ B : Matrix (Fin 2) (Fin 2) ℤ, IsUnit B.det ∧ (!![a, b; c, d] * B).IsColumnHermiteNormalForm`
- **What**: Constructive HNF existence for an explicit nonsingular 2×2 integer matrix: some unimodular right factor brings it to column Hermite normal form.
- **How**: The classical Euclidean construction. Sets g = gcd(c,d) > 0 with Bézout coefficients u, v from `Int.gcd_eq_gcd_ab`, cofactors cg = c/g, dg = d/g (satisfying cg·u + dg·v = 1 by cancelling g), pivot = a·dg − b·cg (nonzero since pivot·g = det), sign-corrects the pivot with `exists_unit_mul_pos_aux`, and reduces the top-right entry by Euclidean division (`Int.emod_add_mul_ediv`, `Int.emod_nonneg`, `Int.emod_lt_of_pos`). The transformation matrix's determinant is the unit s by `hnf_transform_det_aux` and the product has the required shape by `hnf_transform_mul_aux`, verified in HNF by `isColumnHermiteNormalForm_fin_two`.
- **Hypotheses**: the determinant a·d − b·c is nonzero.
- **Uses from project**: [`Matrix.IsColumnHermiteNormalForm`, `Matrix.isColumnHermiteNormalForm_fin_two`, `exists_unit_mul_pos_aux`, `hnf_transform_det_aux`, `hnf_transform_mul_aux`]
- **Used by**: `exists_right_mul_isColumnHermiteNormalForm`
- **Visibility**: private
- **Lines**: 133–190, proof 55 lines
- **Notes**: proof >30 lines (55); key mathlib lemmas: `Int.gcd_eq_gcd_ab`, `Int.ediv_mul_cancel`, `Int.emod_add_mul_ediv`

### `theorem Matrix.exists_right_mul_isColumnHermiteNormalForm`
- **Type**: `(A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det ≠ 0) : ∃ B : Matrix (Fin 2) (Fin 2) ℤ, IsUnit B.det ∧ (A * B).IsColumnHermiteNormalForm`
- **What**: Every nonsingular 2×2 integer matrix can be brought to column Hermite normal form by a unimodular change of columns — the abstract-matrix form of `exists_hnf_transform`.
- **How**: Rewrites A as the entry literal `!![A 0 0, A 0 1; A 1 0, A 1 1]` (extensionality), converts `A.det ≠ 0` via `Matrix.det_fin_two_of`, and applies `exists_hnf_transform`.
- **Hypotheses**: det A ≠ 0.
- **Uses from project**: [`Matrix.IsColumnHermiteNormalForm`, `exists_hnf_transform`]
- **Used by**: `Submodule.exists_hermiteNormalForm`
- **Visibility**: public
- **Lines**: 194–203, proof 8 lines
- **Notes**: none

### `structure Module.Basis.HermiteNormalForm`
- **Type**: `{M : Type*} [AddCommGroup M] {n : ℕ} (bM : Basis (Fin n) ℤ M) (N : Submodule ℤ M) : Type`, with fields `bN : Basis (Fin n) ℤ N`, `matrix : Matrix (Fin n) (Fin n) ℤ`, `toMatrix_eq : LinearMap.toMatrix bN bM N.subtype = matrix`, `isColumnHermiteNormalForm : matrix.IsColumnHermiteNormalForm`
- **What**: A bundled Hermite-normal-form presentation of a full-rank submodule N ≤ M relative to a fixed ambient basis bM: a basis of N together with the inclusion matrix (columns = coordinates of the N-basis vectors in bM), required to be in column HNF. Parallel to mathlib's `Module.Basis.SmithNormalForm` but records the full inclusion matrix, since HNF is basis-relative.
- **How**: Structure with four data/property fields; stated in arbitrary finite rank n (existence/uniqueness proved below in rank 2).
- **Hypotheses**: M a ℤ-module with a finite basis indexed by Fin n.
- **Uses from project**: [`Matrix.IsColumnHermiteNormalForm`]
- **Used by**: `repr_apply`, `range_toLin_matrix_eq`, `matrix_mul_toMatrix_eq`, `matrix_eq`, `bN_eq`, `index_eq_natAbs_det`, `quotient_isAddCyclic_iff_rankTwoContent_eq_one`, `Submodule.exists_hermiteNormalForm`, `Submodule.hermiteNormalForm`
- **Visibility**: public
- **Lines**: 213–222
- **Notes**: docstring; central definition of the file

### `theorem Module.Basis.HermiteNormalForm.repr_apply`
- **Type**: `(h : HermiteNormalForm bM N) (i j : Fin n) : bM.repr (N.subtype (h.bN j)) i = h.matrix i j`
- **What**: The i-th ambient coordinate of the j-th HNF submodule basis vector is the (i,j) entry of the HNF matrix.
- **How**: Rewrites with the structure field `toMatrix_eq` and `LinearMap.toMatrix_apply`.
- **Hypotheses**: an HNF presentation of N.
- **Uses from project**: [`Module.Basis.HermiteNormalForm`]
- **Used by**: `bN_eq`
- **Visibility**: public
- **Lines**: 230–232, proof 1 line
- **Notes**: @[simp]

### `theorem Module.Basis.HermiteNormalForm.range_toLin_matrix_eq`
- **Type**: `(h : HermiteNormalForm bM N) : LinearMap.range (Matrix.toLin bM bM h.matrix) = N`
- **What**: Interpreting the HNF matrix as an endomorphism of M in the ambient basis, its image (column space) is exactly the submodule N — the matrix's columns really generate N.
- **How**: Shows `Matrix.toLin bM bM h.matrix` equals the composite `N.subtype ∘ (bM.equiv h.bN)` by comparing matrices: `LinearMap.toMatrix_comp` factors the composite as (inclusion matrix)·(identity), where `LinearMap.toMatrix_basis_equiv` gives the identity factor; then the range of subtype ∘ equiv is N since the equiv is surjective onto N.
- **Hypotheses**: an HNF presentation of N (arbitrary rank n).
- **Uses from project**: [`Module.Basis.HermiteNormalForm`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 236–260, proof 23 lines
- **Notes**: none

### `lemma Module.Basis.HermiteNormalForm.matrix_mul_toMatrix_eq`
- **Type**: `(h h' : HermiteNormalForm bM N) : h.matrix * h.bN.toMatrix h'.bN = h'.matrix` (here `bM : Basis (Fin 2) ℤ M`)
- **What**: Two HNF presentations of the same submodule differ by the change-of-basis matrix between their submodule bases: h.matrix · (change of basis) = h'.matrix.
- **How**: Both matrices represent the same inclusion N ↪ M; the mathlib identity `linearMap_toMatrix_mul_basis_toMatrix` composes the representation with the basis-change matrix.
- **Hypotheses**: two HNF presentations of the same N relative to the same rank-two ambient basis.
- **Uses from project**: [`Module.Basis.HermiteNormalForm`]
- **Used by**: `matrix_eq` (applied in both directions)
- **Visibility**: private
- **Lines**: 264–267, proof 2 lines
- **Notes**: stated in rank two only because of the surrounding `variable` block, though the argument is rank-generic

### `lemma Module.Basis.HermiteNormalForm.reduced_eq_of_eq_add_mul`
- **Type**: `{d r r' q : ℤ} (hr : r ∈ Set.Ico 0 d) (hr' : r' ∈ Set.Ico 0 d) (e : d * q + r = r') : r = r'`
- **What**: Uniqueness of the reduced remainder: two integers in [0, d) that differ by a multiple of d are equal.
- **How**: Both equal their residue mod d (`Int.emod_eq_of_lt`), and the residues agree by `Int.add_emod` applied to the relation d·q + r = r'.
- **Hypotheses**: 0 ≤ r < d, 0 ≤ r' < d, r' − r divisible by d (in the given linear form).
- **Uses from project**: []
- **Used by**: `matrix_eq`
- **Visibility**: private
- **Lines**: 269–274, proof 4 lines
- **Notes**: none

### `theorem Module.Basis.HermiteNormalForm.matrix_eq`
- **Type**: `(h h' : HermiteNormalForm bM N) : h.matrix = h'.matrix` (with `bM : Basis (Fin 2) ℤ M`)
- **What**: Rank-two uniqueness of the Hermite normal form: the HNF inclusion matrix of a fixed submodule relative to a fixed ambient basis is unique (only the basis, not the matrix, involves choice).
- **How**: Let U, V be the two change-of-basis matrices between the submodule bases, so h.matrix·U = h'.matrix and h'.matrix·V = h.matrix by `matrix_mul_toMatrix_eq`. Reading off entries (via `Matrix.mul_apply`, `Fin.sum_univ_two`) and using upper-triangularity: U 1 0 = V 1 0 = 0 since the positive pivot a = matrix 1 1 is a nonzero factor of 0; the diagonal entries mutually divide and are positive, hence equal by antisymmetry with `Int.le_of_dvd`; that forces U 1 1 = 1, and the reduced top-right entries then agree by `reduced_eq_of_eq_add_mul` (both are canonical residues mod the common pivot).
- **Hypotheses**: two HNF presentations of the same N over the same rank-two ambient basis.
- **Uses from project**: [`Module.Basis.HermiteNormalForm`, `Matrix.IsColumnHermiteNormalForm` (fields), `matrix_mul_toMatrix_eq`, `reduced_eq_of_eq_add_mul`]
- **Used by**: `bN_eq`
- **Visibility**: public
- **Lines**: 278–335, proof 57 lines
- **Notes**: proof >30 lines (57); key lemma `Int.le_of_dvd` for the divisibility-antisymmetry step

### `theorem Module.Basis.HermiteNormalForm.bN_eq`
- **Type**: `(h h' : HermiteNormalForm bM N) : h.bN = h'.bN` (with `bM : Basis (Fin 2) ℤ M`)
- **What**: In rank two, the submodule basis appearing in an HNF presentation is itself unique — the whole HNF structure is essentially canonical given (bM, N).
- **How**: Basis vectors are determined by their ambient coordinates: by `repr_apply` these are the columns of the HNF matrix, and `matrix_eq` says the matrices agree; injectivity of `bM.repr` and `Subtype.ext` conclude.
- **Hypotheses**: two HNF presentations of the same N over the same rank-two ambient basis.
- **Uses from project**: [`Module.Basis.HermiteNormalForm`, `repr_apply`, `matrix_eq`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 338–345, proof 7 lines
- **Notes**: none

### `theorem Module.Basis.HermiteNormalForm.index_eq_natAbs_det`
- **Type**: `{n : ℕ} {bM : Basis (Fin n) ℤ M} {N : Submodule ℤ M} (h : HermiteNormalForm bM N) : N.toAddSubgroup.index = h.matrix.det.natAbs`
- **What**: The index [M : N] of a full-rank HNF submodule equals the absolute value of the determinant of its inclusion matrix (Cox, Exercise 7.15 in the rank-two case; for HNF this is the product of the pivots).
- **How**: Mathlib's `AddSubgroup.index_eq_natAbs_det` gives the index as |det| of the basis-change map; `Basis.det_apply` and an entrywise identification of `bM.toMatrix (h.bN ·)` with `h.matrix` (via `Basis.toMatrix_apply`, `LinearMap.toMatrix_apply`, and the field `toMatrix_eq`) transfer it to the HNF matrix.
- **Hypotheses**: an HNF presentation of N (arbitrary rank n; full rank is implicit in the equal index types).
- **Uses from project**: [`Module.Basis.HermiteNormalForm`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 351–359, proof 8 lines
- **Notes**: none

### `theorem Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one`
- **Type**: `(bM : Basis (Fin 2) ℤ M) (N : Submodule ℤ M) (bN : Basis (Fin 2) ℤ N) : IsAddCyclic (M ⧸ N) ↔ Matrix.rankTwoContent (LinearMap.toMatrix bN bM N.subtype) = 1`
- **What**: For a full-rank rank-two sublattice, the quotient M/N is a cyclic group iff the inclusion matrix in ANY choice of bases is primitive (content 1) — Cox, Exercise 11.16. This is the lattice-theoretic criterion for cyclic sublattices used in the theory of the modular equation.
- **How**: Passes to Smith normal form: mathlib's `Submodule.smithNormalFormTopBasis`/`smithNormalFormBotBasis`/`smithNormalFormCoeffs` diagonalise the inclusion as D = diag(c₀, c₁), and the two-sided base-change identities `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix` express A and D through each other; content is invariant under unimodular multiplication (`rankTwoContent_dvd_mul_left`/`_right` in both directions plus `Nat.dvd_antisymm`), so content A = gcd(|c₀|, |c₁|). Meanwhile M ⧸ N ≅ ZMod |c₀| × ZMod |c₁| by `Submodule.quotientEquivPiZMod`, and `AddGroup.isAddCyclic_prod_iff` with `Nat.coprime_iff_gcd_eq_one` says the product is cyclic iff gcd(|c₀|, |c₁|) = 1.
- **Hypotheses**: N a submodule of the rank-two ℤ-module M admitting a rank-two basis bN (full rank).
- **Uses from project**: [`Matrix.rankTwoContent`, `rankTwoContent_dvd_mul_left`, `rankTwoContent_dvd_mul_right`]
- **Used by**: `quotient_isAddCyclic_iff_rankTwoContent_eq_one`
- **Visibility**: public
- **Lines**: 363–410, proof 46 lines
- **Notes**: proof >30 lines (46); the mathematical heart of the cyclic-sublattice criterion

### `theorem Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`
- **Type**: `{bM : Basis (Fin 2) ℤ M} {N : Submodule ℤ M} (h : HermiteNormalForm bM N) : IsAddCyclic (M ⧸ N) ↔ Matrix.rankTwoContent h.matrix = 1`
- **What**: HNF specialisation of Exercise 11.16: the quotient by a rank-two sublattice is cyclic iff its (unique) HNF matrix is primitive. Since the HNF matrix is `!![d, b; 0, a]`, this is gcd(d, b, a) = 1.
- **How**: Instance of `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` at the HNF basis, rewriting the inclusion matrix by the field `toMatrix_eq`.
- **Hypotheses**: an HNF presentation of N over a rank-two ambient basis.
- **Uses from project**: [`Module.Basis.HermiteNormalForm`, `Matrix.rankTwoContent`, `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 414–419, proof 2 lines
- **Notes**: none

### `theorem Submodule.exists_hermiteNormalForm`
- **Type**: `(bM : Basis (Fin 2) ℤ M) (N : Submodule ℤ M) (hN : Module.finrank ℤ N = 2) : Nonempty (Module.Basis.HermiteNormalForm bM N)`
- **What**: Existence: every full-rank (rank-two) ℤ-submodule of a rank-two lattice admits an HNF presentation relative to any fixed ambient basis.
- **How**: Picks any basis bN₀ of N (`Module.finBasis` transported along hN) with inclusion matrix A; the inclusion composed with `bM.equiv bN₀` is injective, so det A ≠ 0 by `LinearMap.det_eq_zero_iff_ker_ne_bot` and `LinearMap.det_toMatrix`. `Matrix.exists_right_mul_isColumnHermiteNormalForm` supplies a unimodular B with A·B in HNF; the new basis is bN₀ transported along the linear automorphism `Matrix.toLinearEquiv bN₀ B hBunit`, and `LinearMap.toMatrix_map_left` + `LinearMap.toMatrix_comp` verify its inclusion matrix is A·B.
- **Hypotheses**: M has a rank-two basis; finrank ℤ N = 2 (full rank).
- **Uses from project**: [`Module.Basis.HermiteNormalForm`, `Matrix.exists_right_mul_isColumnHermiteNormalForm`]
- **Used by**: `Submodule.hermiteNormalForm`
- **Visibility**: public
- **Lines**: 431–464, proof 32 lines
- **Notes**: proof >30 lines (32); key mathlib lemmas `Matrix.toLinearEquiv`, `LinearMap.toMatrix_map_left`, `LinearMap.toMatrix_basis_equiv`

### `def Submodule.hermiteNormalForm`
- **Type**: `(bM : Basis (Fin 2) ℤ M) (N : Submodule ℤ M) (hN : Module.finrank ℤ N = 2) : Module.Basis.HermiteNormalForm bM N`
- **What**: The canonical HNF presentation of a full-rank rank-two submodule, chosen from the existence theorem (canonical up to nothing, by the uniqueness theorems `matrix_eq`/`bN_eq`).
- **How**: `Classical.choice` on `exists_hermiteNormalForm`.
- **Hypotheses**: M rank-two with basis bM; finrank ℤ N = 2.
- **Uses from project**: [`Module.Basis.HermiteNormalForm`, `Submodule.exists_hermiteNormalForm`]
- **Used by**: unused in file (public API; consumed downstream in CyclicSublattice / CoxMatrices)
- **Visibility**: public
- **Lines**: 467–470
- **Notes**: noncomputable

### File Summary
- Total declarations: 24 (2 defs, 20 lemmas/theorems, 2 structures, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): `Matrix.IsColumnHermiteNormalForm` (5), `Matrix.rankTwoContent` (6), `Module.Basis.HermiteNormalForm` (9)
- Unused declarations (not used by anything in this file): `range_toLin_matrix_eq`, `bN_eq`, `index_eq_natAbs_det`, `quotient_isAddCyclic_iff_rankTwoContent_eq_one`, `Submodule.hermiteNormalForm` (all public API consumed by downstream files: LevelThree, CyclicSublattice, CyclicSublattice/Classification, CoxMatrices/Basic)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [`Matrix.exists_hnf_transform` (55 lines), `Module.Basis.HermiteNormalForm.matrix_eq` (57 lines), `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` (46 lines), `Submodule.exists_hermiteNormalForm` (32 lines)]
