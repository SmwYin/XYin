# Inventory: XYin/PhD/Cox/CoxMatrices/Basic.lean  (822 lines)

Defines Cox's finite set `C(m)` of primitive upper-triangular determinant-`m` integer matrices as a
structure `CoxMatrix m`, proves it is in bijection with the right cosets `Γ₀(m)\SL₂(ℤ)` (Cox Lemma
11.11) via the project's rank-two column-HNF theory, and builds the right-coset action on
`Γ₀(m)`-modular functions used to define the modular polynomial. Also proves Cox (11.12):
`j(m·γτ)` on the coset of `γ` equals `j(σ·τ)` for the corresponding Cox matrix.

## Declarations

### `structure Cox.CoxMatrix`
- **Type**: `(m : ℕ+) → Type` with fields `a b d : ℕ`, `a_pos : 0 < a`, `determinant : a * d = m`, `b_lt : b < d`, `primitive : Nat.gcd (Nat.gcd a b) d = 1`
- **What**: Cox's set `C(m)`: matrices `[[a,b],[0,d]]` with `ad = m`, `0 ≤ b < d`, `gcd(a,b,d) = 1`.
- **How**: Plain structure over ℕ with three proof fields.
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: []
- **Used by**: every declaration in the file.
- **Visibility**: public
- **Lines**: 24–31
- **Notes**: NO `@[ext]` attribute and no `CoxMatrix.ext` lemma; equality is established by `cases σ; cases τ; simp_all` at 101–103, 296–298 (and LaurentExpansion.lean:349–351) or through `toFin_injective`/`inclusionMatrix_injective`. No `_apply`/`_val` simp family (fields are accessed directly). `DecidableEq`/`Fintype` instances exist (105, 108). No constructor from an HNF matrix (only the existential `exists_coxMatrix_of_isColumnHermiteNormalForm_aux`, 358).

### `theorem Cox.CoxMatrix.d_pos`
- **Type**: `(σ : CoxMatrix m) : 0 < σ.d`
- **What**: The lower-right entry is positive.
- **How**: `a * d = m > 0` and `pos_of_mul_pos_right`.
- **Hypotheses**: none beyond the structure.
- **Uses from project**: [`CoxMatrix.determinant`]
- **Used by**: `a_le`, `inclusionMatrix_isColumnHermiteNormalForm`, `act`, `levelJ_smul_eq_j_act_of_normalization`
- **Visibility**: public
- **Lines**: 37–41, proof ≈ 4 lines
- **Notes**: —

### `theorem Cox.CoxMatrix.a_le`
- **Type**: `(σ : CoxMatrix m) : σ.a ≤ m`
- **What**: `a ≤ m` since `a ∣ m`.
- **How**: `Nat.le_mul_of_pos_right` on `a * d = m`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.determinant`, `CoxMatrix.d_pos`]
- **Used by**: `toFin`
- **Visibility**: public
- **Lines**: 43–45, proof ≈ 2 lines
- **Notes**: Not used outside this file.

### `theorem Cox.CoxMatrix.d_le`
- **Type**: `(σ : CoxMatrix m) : σ.d ≤ m`
- **What**: `d ≤ m`.
- **How**: `Nat.le_mul_of_pos_left` on `a * d = m`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.determinant`, `CoxMatrix.a_pos`]
- **Used by**: `toFin`
- **Visibility**: public
- **Lines**: 47–49, proof ≈ 2 lines
- **Notes**: Not used outside this file.

### `def Cox.CoxMatrix.mobiusMatrix`
- **Type**: `(σ : CoxMatrix m) : Matrix (Fin 2) (Fin 2) ℤ`
- **What**: The matrix `[[a,b],[0,d]]` acting on ℍ.
- **How**: `!![a, b; 0, d]` with ℕ→ℤ casts.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `matrixStar_mobiusMatrix`, `matrixStar_inclusionMatrix`, `coxRepresentative_normalization`, `levelJ_smul_eq_j_act_of_normalization`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: public
- **Lines**: 52–53
- **Notes**: No `mobiusMatrix_apply`/`_det` simp lemmas (det is only proved for `inclusionMatrix`).

### `def Cox.CoxMatrix.inclusionMatrix`
- **Type**: `(σ : CoxMatrix m) : Matrix (Fin 2) (Fin 2) ℤ`
- **What**: The column-HNF basis matrix `[[d,b],[0,a]]` of the sublattice `[d, aτ+b]`.
- **How**: `!![d, b; 0, a]`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `inclusionMatrix_isColumnHermiteNormalForm`, `inclusionMatrix_det`, `inclusionMatrix_content_eq_one`, `matrixStar_mobiusMatrix`, `inclusionMatrix_injective`, `exists_coxMatrix_of_isColumnHermiteNormalForm_aux`, `exists_coxMatrix_reduction`, `coxMatrix_reduction_unique`, `coxReduction_spec`, `matrixStar_inclusionMatrix`, `coxInput_one`, `coxMatrix_smith_normalization`, `coxRepresentative_surjective`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: public
- **Lines**: 56–57
- **Notes**: `inclusionMatrix = matrixStar mobiusMatrix` (175); the two matrices are anti-transposes of each other.

### `theorem Cox.CoxMatrix.inclusionMatrix_isColumnHermiteNormalForm`
- **Type**: `(σ : CoxMatrix m) : σ.inclusionMatrix.IsColumnHermiteNormalForm`
- **What**: The inclusion matrix is in column Hermite normal form.
- **How**: `Matrix.isColumnHermiteNormalForm_fin_two` with `d>0`, `a>0`, `0 ≤ b < d`.
- **Hypotheses**: none.
- **Uses from project**: [`Matrix.isColumnHermiteNormalForm_fin_two`, `CoxMatrix.d_pos`, `CoxMatrix.a_pos`, `CoxMatrix.b_lt`, `CoxMatrix.inclusionMatrix`]
- **Used by**: `coxMatrix_reduction_unique`
- **Visibility**: public
- **Lines**: 59–65, proof ≈ 5 lines
- **Notes**: —

### `theorem Cox.CoxMatrix.inclusionMatrix_det`
- **Type**: `(σ : CoxMatrix m) : σ.inclusionMatrix.det = (m : ℕ)`
- **What**: `det [[d,b],[0,a]] = ad = m`.
- **How**: `Matrix.det_fin_two_of`, `norm_cast`, `σ.determinant`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.inclusionMatrix`, `CoxMatrix.determinant`]
- **Used by**: `coxMatrix_smith_normalization`
- **Visibility**: public
- **Lines**: 67–72, proof ≈ 4 lines
- **Notes**: —

### `theorem Cox.CoxMatrix.inclusionMatrix_content_eq_one`
- **Type**: `(σ : CoxMatrix m) : Matrix.rankTwoContent σ.inclusionMatrix = 1`
- **What**: The gcd of the entries of the inclusion matrix is 1 (primitivity).
- **How**: `simpa` with gcd commutativity/associativity from `σ.primitive`.
- **Hypotheses**: none.
- **Uses from project**: [`Matrix.rankTwoContent`, `CoxMatrix.inclusionMatrix`, `CoxMatrix.primitive`]
- **Used by**: unused in file (used by CyclicSublattice/Classification.lean)
- **Visibility**: public
- **Lines**: 74–77, proof ≈ 2 lines
- **Notes**: The gcd-reassociation `simpa only [Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc] using σ.primitive` recurs (383–384, Cardinality.lean:63–64, 82–83).

### `def Cox.CoxMatrix.act`
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : ℍ`
- **What**: The Möbius action `τ ↦ (aτ + b)/d` of the Cox matrix on ℍ.
- **How**: Direct construction; imaginary part `a·Im τ / d > 0` by `div_pos`/`mul_pos`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.a_pos`, `CoxMatrix.d_pos`]
- **Used by**: `coe_act`, `levelJ_smul_eq_j_act_of_normalization`, `rightCosetEval_equiv`, `j_act_sigmaZero`
- **Visibility**: public
- **Lines**: 80–83
- **Notes**: Hand-rolled; not linked to mathlib's `GL(2,ℝ)⁺`/`SL(2,ℤ)` action on ℍ (see Observations). Used in 7 other project files.

### `theorem Cox.CoxMatrix.coe_act`
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : ((σ.act τ : ℍ) : ℂ) = (a * τ + b) / d`
- **What**: Coercion formula for the action.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.act`]
- **Used by**: `levelJ_smul_eq_j_act_of_normalization`
- **Visibility**: public
- **Lines**: 85–87
- **Notes**: `@[simp]`.

### `def Cox.CoxMatrix.toFin`
- **Type**: `(σ : CoxMatrix m) : Fin (m+1) × Fin (m+1) × Fin (m+1)`
- **What**: Bounded encoding `(a, b, d)` used to get finiteness.
- **How**: Bounds from `a_le`, `b_lt`+`d_le`, `d_le` via `omega`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.a_le`, `CoxMatrix.b_lt`, `CoxMatrix.d_le`]
- **Used by**: `toFin_injective`, `instance DecidableEq`, `instance Fintype`
- **Visibility**: public
- **Lines**: 90–94
- **Notes**: —

### `theorem Cox.CoxMatrix.toFin_injective`
- **Type**: `Function.Injective (toFin (m := m))`
- **What**: The encoding is injective (so `C(m)` is finite).
- **How**: Extract the three coordinates with `congrArg`, then `cases σ; cases τ; simp_all`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.toFin`]
- **Used by**: `instance DecidableEq`, `instance Fintype`
- **Visibility**: public
- **Lines**: 96–103, proof ≈ 7 lines
- **Notes**: Serves as the de-facto extensionality lemma project-wide (Kronecker.lean:67,78; UpperHalfPlaneFunctionField.lean:211; Cardinality.lean:91). A `@[ext] CoxMatrix.ext` would replace it.

### `instance Cox.CoxMatrix.instDecidableEq`
- **Type**: `DecidableEq (CoxMatrix m)`
- **What**: Decidable equality via the injective encoding.
- **How**: `decidable_of_iff (x.toFin = y.toFin) toFin_injective.eq_iff`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.toFin`, `CoxMatrix.toFin_injective`]
- **Used by**: implicitly by `Finset`/`Fintype.card` uses downstream
- **Visibility**: public (anonymous instance)
- **Lines**: 105–106
- **Notes**: —

### `instance Cox.CoxMatrix.instFintype`
- **Type**: `Fintype (CoxMatrix m)`
- **What**: `C(m)` is a finite type.
- **How**: `Fintype.ofInjective toFin toFin_injective`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.toFin`, `CoxMatrix.toFin_injective`]
- **Used by**: `one_lt_card_coxMatrix` (via `Fintype.card`)
- **Visibility**: public (anonymous instance)
- **Lines**: 108
- **Notes**: Noncomputable-by-construction but inside `noncomputable section`; fine.

### `def Cox.sigmaZero`
- **Type**: `(m : ℕ+) : CoxMatrix m`
- **What**: Cox's distinguished matrix `σ₀ = diag(m, 1)`.
- **How**: `a := m, b := 0, d := 1`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`]
- **Used by**: `one_lt_card_coxMatrix`, `coxInput_one`, `coxRepresentative_one`, `coxMatrixEquivRightCosets_sigmaZero`, `rightCosetTranslate_sigmaZero`, `j_act_sigmaZero`
- **Visibility**: public
- **Lines**: 113–120
- **Notes**: No `sigmaZero_a/_b/_d` simp lemmas; used in 5 other files.

### `theorem Cox.one_lt_card_coxMatrix`
- **Type**: `(m : ℕ+) (hm : 1 < (m : ℕ)) : 1 < Fintype.card (CoxMatrix m)`
- **What**: For `m > 1`, `C(m)` has at least two elements.
- **How**: Exhibits `diag(1,m) ≠ diag(m,1)` via `Fintype.one_lt_card_iff`.
- **Hypotheses**: `m > 1`.
- **Uses from project**: [`CoxMatrix`, `sigmaZero`]
- **Used by**: unused in file (used by Cox/Arithmetic.lean)
- **Visibility**: public
- **Lines**: 123–138, proof ≈ 14 lines
- **Notes**: —

### `abbrev Cox.Gamma0RightCosets`
- **Type**: `(m : ℕ+) : Type` := `Quotient (QuotientGroup.rightRel (Gamma0 m))`
- **What**: The set of right cosets `Γ₀(m)γ` of `Γ₀(m)` in `SL₂(ℤ)`.
- **How**: mathlib `QuotientGroup.rightRel`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `gamma0RightCosetsFintype`, `rightCosetToCoxMatrix`, `coxMatrixEquivRightCosets`, `rightCosetTranslate`, `rightCosetEval`, `rightCosetMul`, `baseRightCoset`, `exists_rightCosetMul_baseRightCoset_eq`, `rightCosetTranslate_smul`, `rightCosetEval_smul`
- **Visibility**: public
- **Lines**: 141–142
- **Notes**: Used in 5 other files.

### `instance Cox.gamma0RightCosetsFintype`
- **Type**: `(m : ℕ+) : Fintype (Gamma0RightCosets m)`
- **What**: The right-coset space is finite (finite index of `Γ₀(m)`).
- **How**: mathlib `CongruenceSubgroup.instFiniteIndexGamma0`, `Subgroup.fintypeQuotientOfFiniteIndex`, transported along `QuotientGroup.quotientRightRelEquivQuotientLeftRel`.
- **Hypotheses**: none (`NeZero m` supplied locally).
- **Uses from project**: [`Gamma0RightCosets`]
- **Used by**: implicit (any `Fintype.card (Gamma0RightCosets m)` downstream)
- **Visibility**: public
- **Lines**: 144–152, proof ≈ 7 lines
- **Notes**: —

### `private def Cox.matrixStar`
- **Type**: `(A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ`
- **What**: The anti-transpose `[[A₁₁, A₀₁],[A₁₀, A₀₀]]` (reflect in the anti-diagonal), swapping the "row" and "column" HNF conventions.
- **How**: `!![A 1 1, A 0 1; A 1 0, A 0 0]`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `matrixStar_involutive`, `matrixStar_mul`, `matrixStar_det`, `matrixStar_mobiusMatrix`, `matrixStar_determinantScale`, `coxInput`, `coxInput_eq`, `slStar`, `coe_slStar`, `matrixStar_inclusionMatrix`, `coxRepresentative_normalization`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 154–156
- **Notes**: Equals `(A.submatrix Fin.rev Fin.rev)ᵀ`; see Observations.

### `private theorem Cox.matrixStar_involutive`
- **Type**: `(A) : matrixStar (matrixStar A) = A`
- **What**: Anti-transpose is an involution.
- **How**: `ext; fin_cases; rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`]
- **Used by**: `matrixStar_inclusionMatrix`, `coxRepresentative_normalization`, `coxRepresentative_surjective`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 158–161, proof ≈ 2 lines
- **Notes**: —

### `private theorem Cox.matrixStar_mul`
- **Type**: `(A B) : matrixStar (A * B) = matrixStar B * matrixStar A`
- **What**: Anti-transpose is an anti-homomorphism.
- **How**: Entrywise `fin_cases` + `Matrix.mul_apply`, `Fin.sum_univ_two`, `ring`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`]
- **Used by**: `coxRepresentative_normalization`, `coxRepresentative_surjective`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 163–168, proof ≈ 4 lines
- **Notes**: —

### `private theorem Cox.matrixStar_det`
- **Type**: `(A) : (matrixStar A).det = A.det`
- **What**: Anti-transpose preserves the determinant.
- **How**: `Matrix.det_fin_two` + `ring`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`]
- **Used by**: `coxInput_det`, `slStar`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 170–173, proof ≈ 2 lines
- **Notes**: —

### `private theorem Cox.matrixStar_mobiusMatrix`
- **Type**: `(σ : CoxMatrix m) : matrixStar σ.mobiusMatrix = σ.inclusionMatrix`
- **What**: The Möbius matrix and inclusion matrix are anti-transposes.
- **How**: `ext; fin_cases; rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`, `CoxMatrix.mobiusMatrix`, `CoxMatrix.inclusionMatrix`]
- **Used by**: `matrixStar_inclusionMatrix`
- **Visibility**: private
- **Lines**: 175–178, proof ≈ 2 lines
- **Notes**: —

### `private def Cox.determinantScale`
- **Type**: `(m : ℕ+) : Matrix (Fin 2) (Fin 2) ℤ` := `!![m, 0; 0, 1]`
- **What**: The matrix `diag(m, 1)` realising `τ ↦ mτ`.
- **How**: literal.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `matrixStar_determinantScale`, `determinantScale_det`, `coxInput`, `coxRepresentative_normalization`
- **Visibility**: private
- **Lines**: 180–181
- **Notes**: Equals `(sigmaZero m).mobiusMatrix` but never identified as such.

### `private def Cox.determinantScaleDual`
- **Type**: `(m : ℕ+) : Matrix (Fin 2) (Fin 2) ℤ` := `!![1, 0; 0, m]`
- **What**: `diag(1, m)` = anti-transpose of `determinantScale`.
- **How**: literal.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `matrixStar_determinantScale`, `coxMatrix_smith_normalization`, `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 183–184
- **Notes**: Equals `(sigmaZero m).inclusionMatrix`.

### `private theorem Cox.matrixStar_determinantScale`
- **Type**: `(m) : matrixStar (determinantScale m) = determinantScaleDual m`
- **What**: The two scaling matrices are anti-transposes.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`, `determinantScale`, `determinantScaleDual`]
- **Used by**: `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 186–188
- **Notes**: —

### `private theorem Cox.determinantScale_det`
- **Type**: `(m) : (determinantScale m).det = m`
- **What**: `det diag(m,1) = m`.
- **How**: `simp [Matrix.det_fin_two_of]`.
- **Hypotheses**: none.
- **Uses from project**: [`determinantScale`]
- **Used by**: `coxInput_det`
- **Visibility**: private
- **Lines**: 190–192
- **Notes**: —

### `private def Cox.coxInput`
- **Type**: `(m : ℕ+) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ` := `matrixStar (determinantScale m * γ)`
- **What**: The matrix whose column HNF gives the Cox representative of the coset of `γ`: the anti-transpose of `diag(m,1)·γ`.
- **How**: composition of the two private defs.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`, `determinantScale`]
- **Used by**: `coxInput_eq`, `coxInput_det`, `coxInput_content_eq_one`, `rightRel_of_coxInput_eq_mul`, `exists_coxInput_eq_mul_of_rightRel`, `exists_coxMatrix_reduction`, `coxMatrix_reduction_unique`, `coxReduction_spec`, `rightRel_iff_coxRepresentative_eq`, `coxRepresentative_normalization`, `coxInput_one`, `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 194–195
- **Notes**: —

### `private theorem Cox.coxInput_eq`
- **Type**: `coxInput m γ = !![γ 1 1, m * γ 0 1; γ 1 0, m * γ 0 0]`
- **What**: Explicit entries of `coxInput`.
- **How**: entrywise `fin_cases` + `simp [Matrix.mul_apply, Fin.sum_univ_two]`.
- **Hypotheses**: none.
- **Uses from project**: [`coxInput`, `matrixStar`, `determinantScale`]
- **Used by**: `coxInput_content_eq_one`, `rightRel_of_coxInput_eq_mul`, `exists_coxInput_eq_mul_of_rightRel`, `coxInput_one`
- **Visibility**: private
- **Lines**: 197–202, proof ≈ 3 lines
- **Notes**: —

### `private theorem Cox.coxInput_det`
- **Type**: `(coxInput m γ).det = m`
- **What**: `det = m` since `det γ = 1`.
- **How**: `matrixStar_det`, `Matrix.det_mul`, `determinantScale_det`, `SpecialLinearGroup.det_coe`.
- **Hypotheses**: none.
- **Uses from project**: [`coxInput`, `matrixStar_det`, `determinantScale_det`]
- **Used by**: `exists_coxMatrix_reduction`
- **Visibility**: private
- **Lines**: 204–207, proof ≈ 2 lines
- **Notes**: —

### `private theorem Cox.coxInput_content_eq_one`
- **Type**: `Matrix.rankTwoContent (coxInput m γ) = 1`
- **What**: `coxInput` is primitive because the bottom row of `γ` is coprime.
- **How**: `ModularGroup.bottom_row_coprime` + `Int.isCoprime_iff_gcd_eq_one`, then gcd reassociation via `ac_rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`coxInput`, `coxInput_eq`, `Matrix.rankTwoContent`]
- **Used by**: `exists_coxMatrix_reduction`
- **Visibility**: private
- **Lines**: 209–223, proof ≈ 13 lines
- **Notes**: The 6-line `show … by ac_rfl` (217–222) is pure gcd bookkeeping.

### `private theorem Cox.rankTwoContent_mul_sl`
- **Type**: `(A) (U : SL(2, ℤ)) : (A * U.1).rankTwoContent = A.rankTwoContent`
- **How**: `Nat.dvd_antisymm` with `Matrix.rankTwoContent_dvd_mul_right` applied to `U` and `U⁻¹`.
- **What**: Matrix content is invariant under right multiplication by `SL₂(ℤ)`.
- **Hypotheses**: none.
- **Uses from project**: [`Matrix.rankTwoContent`, `Matrix.rankTwoContent_dvd_mul_right`]
- **Used by**: `exists_coxMatrix_reduction`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 225–231, proof ≈ 5 lines
- **Notes**: Belongs in HermiteNormalForm.lean next to `rankTwoContent_dvd_mul_right` as public API (also needed for left multiplication, which is currently proved ad hoc at 805–811).

### `private def Cox.slStar`
- **Type**: `(γ : SL(2, ℤ)) : SL(2, ℤ)` := `⟨matrixStar γ.1, _⟩`
- **What**: Anti-transpose restricted to `SL₂(ℤ)`.
- **How**: `matrixStar_det`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`, `matrixStar_det`]
- **Used by**: `coe_slStar`, `coxRepresentative_normalization`, `coxRepresentative_surjective`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 233–234
- **Notes**: —

### `private theorem Cox.coe_slStar`
- **Type**: `(slStar γ).1 = matrixStar γ.1`
- **What**: coercion lemma.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`slStar`, `matrixStar`]
- **Used by**: `coxRepresentative_normalization`, `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 236–237
- **Notes**: `@[simp]` on a private lemma.

### `private theorem Cox.reduced_eq_of_eq_add_mul_aux`
- **Type**: `{d r r' q : ℤ} (hr : r ∈ Set.Ico 0 d) (hr' : r' ∈ Set.Ico 0 d) (e : d * q + r = r') : r = r'`
- **What**: Two reduced residues mod `d` that differ by a multiple of `d` are equal.
- **How**: `Int.emod_eq_of_lt` on both sides and `Int.add_emod`.
- **Hypotheses**: `0 ≤ r, r' < d`.
- **Uses from project**: []
- **Used by**: `columnHNF_eq_of_mul`
- **Visibility**: private
- **Lines**: 239–245, proof ≈ 4 lines
- **Notes**: Pure ℤ lemma; mathlib-shaped (`Int.emod_emod_of_dvd`/`Int.ModEq.eq_of_lt_of_lt` analogue — mathlib has `Nat.ModEq.eq_of_lt_of_lt` (Data/Nat/ModEq.lean) but the ℤ `Ico` version was not found).

### `private theorem Cox.columnHNF_eq_of_mul`
- **Type**: `{A B U} (hA : A.IsColumnHermiteNormalForm) (hB : B.IsColumnHermiteNormalForm) (hU : IsUnit U.det) (hmul : A * U = B) : A = B`
- **What**: Uniqueness of 2×2 column HNF under right multiplication by `GL₂(ℤ)`.
- **How**: Compares entries of `A*U = B` and `B*U⁻¹ = A` (`Matrix.mul_nonsing_inv`); mutual divisibility of diagonals gives equality (`Int.le_of_dvd` twice), then `reduced_eq_of_eq_add_mul_aux` for the off-diagonal entry.
- **Hypotheses**: both in column HNF, `U` unimodular.
- **Uses from project**: [`Matrix.IsColumnHermiteNormalForm` (fields `belowDiagonal_eq_zero`, `diagonal_pos`, `reduced`), `reduced_eq_of_eq_add_mul_aux`]
- **Used by**: `coxMatrix_reduction_unique`
- **Visibility**: private
- **Lines**: 247–285, proof ≈ 37 lines
- **Notes**: Proof >30 lines. Mathematically this is `Matrix.IsColumnHermiteNormalForm.eq_of_mul_isUnit_det` and belongs in HermiteNormalForm.lean (public). The "a ∣ b, b ∣ a, both positive ⇒ a = b" step (273–274, 277–278) is `Int.eq_of_dvd_of_dvd`-shaped (mathlib: `Int.dvd_antisymm` needs nonneg).

### `theorem Cox.CoxMatrix.inclusionMatrix_injective`
- **Type**: `Function.Injective (CoxMatrix.inclusionMatrix (m := m))`
- **What**: A Cox representative is determined by its inclusion matrix.
- **How**: Extract entries `(0,0),(0,1),(1,1)` with `congrFun`, `Int.ofNat_inj`, then `cases; simp_all`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.inclusionMatrix`]
- **Used by**: `coxMatrix_reduction_unique`
- **Visibility**: public
- **Lines**: 288–298, proof ≈ 9 lines
- **Notes**: Second hand-rolled ext (cf. `toFin_injective`). Used by CyclicSublattice/Classification.lean.

### `private theorem Cox.rightRel_of_coxInput_eq_mul`
- **Type**: `(h : coxInput m δ = coxInput m γ * U.1) : QuotientGroup.rightRel (Gamma0 m) γ δ`
- **What**: If two `coxInput`s differ by right multiplication by `SL₂(ℤ)`, then `γ, δ` lie in the same right `Γ₀(m)`-coset.
- **How**: Computes `(δγ⁻¹)₁₀ = m·U₁₀` via `SL2_inv_expl`, `Matrix.det_fin_two`, and `linear_combination`; then `CongruenceSubgroup.Gamma0_mem`.
- **Hypotheses**: as stated.
- **Uses from project**: [`coxInput`, `coxInput_eq`]
- **Used by**: `rightRel_iff_coxRepresentative_eq`
- **Visibility**: private
- **Lines**: 300–319, proof ≈ 17 lines
- **Notes**: —

### `private theorem Cox.exists_coxInput_eq_mul_of_rightRel`
- **Type**: `(hrel : rightRel (Gamma0 m) γ δ) : ∃ U : SL(2, ℤ), coxInput m δ = coxInput m γ * U.1`
- **What**: Converse: same coset ⇒ `coxInput`s differ by an explicit `SL₂(ℤ)` factor.
- **How**: With `h = δγ⁻¹ ∈ Γ₀(m)`, `h₁₀ = m k` (`ZMod.intCast_zmod_eq_zero_iff_dvd`), takes `U = [[h₁₁, m h₀₁],[k, h₀₀]]` and checks entrywise (`linear_combination`, `ring`).
- **Hypotheses**: as stated.
- **Uses from project**: [`coxInput`, `coxInput_eq`]
- **Used by**: `rightRel_iff_coxRepresentative_eq`
- **Visibility**: private
- **Lines**: 321–341, proof ≈ 19 lines
- **Notes**: —

### `private theorem Cox.exists_sl_right_mul_isColumnHermiteNormalForm_aux`
- **Type**: `(A) (hdet : 0 < A.det) : ∃ U : SL(2, ℤ), (A * U.1).IsColumnHermiteNormalForm`
- **What**: Any positive-determinant integer 2×2 matrix has a column HNF reached by an `SL₂(ℤ)` (not just `GL₂(ℤ)`) transformation.
- **How**: `Matrix.exists_right_mul_isColumnHermiteNormalForm` gives a unimodular `B`; `det B = -1` is excluded because HNF has positive diagonal (`Int.isUnit_iff`, `omega`).
- **Hypotheses**: `det A > 0`.
- **Uses from project**: [`Matrix.exists_right_mul_isColumnHermiteNormalForm`, `Matrix.IsColumnHermiteNormalForm`]
- **Used by**: `exists_coxMatrix_reduction`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 343–356, proof ≈ 11 lines
- **Notes**: Belongs in HermiteNormalForm.lean as the `SL₂` refinement of the existence theorem.

### `private theorem Cox.exists_coxMatrix_of_isColumnHermiteNormalForm_aux`
- **Type**: `(H) (hH : H.IsColumnHermiteNormalForm) (hdet : H.det = m) (hcontent : H.rankTwoContent = 1) : ∃ σ : CoxMatrix m, H = σ.inclusionMatrix`
- **What**: A column-HNF primitive matrix of determinant `m` is the inclusion matrix of a Cox representative.
- **How**: Builds `σ` with `natAbs` of the entries; `determinant` from `Int.natAbs_mul`, `b_lt` from `Int.natAbs_lt_natAbs_of_nonneg_of_lt`, `primitive` by gcd reassociation; equality entrywise with `Int.ofNat_natAbs_of_nonneg`.
- **Hypotheses**: as stated.
- **Uses from project**: [`Matrix.IsColumnHermiteNormalForm`, `Matrix.rankTwoContent`, `CoxMatrix`, `CoxMatrix.inclusionMatrix`]
- **Used by**: `exists_coxMatrix_reduction`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 358–385, proof ≈ 26 lines
- **Notes**: This is exactly the body a `CoxMatrix.ofColumnHNF` smart constructor (+ `inclusionMatrix_ofColumnHNF` simp lemma) would package; the July `step7-api.md` request is still open, though the earlier duplicate inside `exists_coxMatrix_reduction` has been removed (it now calls this lemma).

### `private theorem Cox.exists_coxMatrix_reduction`
- **Type**: `(m) (γ) : ∃ (σ : CoxMatrix m) (U : SL(2, ℤ)), coxInput m γ * U.1 = σ.inclusionMatrix`
- **What**: Every `coxInput` reduces by `SL₂(ℤ)` to the inclusion matrix of a Cox representative.
- **How**: `exists_sl_right_mul_isColumnHermiteNormalForm_aux` then `exists_coxMatrix_of_isColumnHermiteNormalForm_aux` with `coxInput_det`, `coxInput_content_eq_one`, `rankTwoContent_mul_sl`.
- **Hypotheses**: none.
- **Uses from project**: [`coxInput`, `coxInput_det`, `coxInput_content_eq_one`, `rankTwoContent_mul_sl`, `exists_sl_right_mul_isColumnHermiteNormalForm_aux`, `exists_coxMatrix_of_isColumnHermiteNormalForm_aux`, `CoxMatrix.inclusionMatrix`]
- **Used by**: `coxRepresentative`, `coxReductionMatrix`, `coxReduction_spec`
- **Visibility**: private
- **Lines**: 387–397, proof ≈ 9 lines
- **Notes**: —

### `private theorem Cox.coxMatrix_reduction_unique`
- **Type**: `(hσ : coxInput m γ * U.1 = σ.inclusionMatrix) (hτ : coxInput m γ * V.1 = τ.inclusionMatrix) : σ = τ`
- **What**: The Cox representative of a reduction is unique.
- **How**: `W = U⁻¹V` sends `σ.inclusionMatrix` to `τ.inclusionMatrix`; `columnHNF_eq_of_mul` + `inclusionMatrix_injective`.
- **Hypotheses**: as stated.
- **Uses from project**: [`coxInput`, `CoxMatrix.inclusionMatrix`, `CoxMatrix.inclusionMatrix_isColumnHermiteNormalForm`, `CoxMatrix.inclusionMatrix_injective`, `columnHNF_eq_of_mul`]
- **Used by**: `rightRel_iff_coxRepresentative_eq`, `coxRepresentative_one`, `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 399–411, proof ≈ 11 lines
- **Notes**: Contains the `coe_mul, mul_assoc, mul_inv_cancel, coe_one` cancellation chain (405–407) repeated at 228–230, 443–446, 574–579.

### `private def Cox.coxRepresentative`
- **Type**: `(m) (γ : SL(2, ℤ)) : CoxMatrix m` := `(exists_coxMatrix_reduction m γ).choose`
- **What**: The Cox representative of the coset of `γ` (chosen).
- **How**: `Classical.choose`.
- **Hypotheses**: none.
- **Uses from project**: [`exists_coxMatrix_reduction`, `CoxMatrix`]
- **Used by**: `coxReduction_spec`, `rightRel_iff_coxRepresentative_eq`, `coxRepresentative_normalization`, `coxRepresentative_one`, `coxRepresentative_surjective`, `rightCosetToCoxMatrix`, `coxMatrixEquivRightCosets_coxRepresentative`, `rightCosetEval_equiv`
- **Visibility**: private
- **Lines**: 413–414
- **Notes**: —

### `private def Cox.coxReductionMatrix`
- **Type**: `(m) (γ) : SL(2, ℤ)`
- **What**: The chosen reducing matrix `U` for `γ`.
- **How**: `choose_spec.choose`.
- **Hypotheses**: none.
- **Uses from project**: [`exists_coxMatrix_reduction`]
- **Used by**: `coxReduction_spec`, `rightRel_iff_coxRepresentative_eq`, `coxRepresentative_normalization`
- **Visibility**: private
- **Lines**: 416–417
- **Notes**: —

### `private theorem Cox.coxReduction_spec`
- **Type**: `coxInput m γ * (coxReductionMatrix m γ).1 = (coxRepresentative m γ).inclusionMatrix`
- **What**: Specification of the two chosen objects.
- **How**: `choose_spec.choose_spec`.
- **Hypotheses**: none.
- **Uses from project**: [`coxInput`, `coxReductionMatrix`, `coxRepresentative`, `CoxMatrix.inclusionMatrix`, `exists_coxMatrix_reduction`]
- **Used by**: `rightRel_iff_coxRepresentative_eq`, `coxRepresentative_normalization`, `coxRepresentative_one`, `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 419–422
- **Notes**: —

### `private theorem Cox.rightRel_iff_coxRepresentative_eq`
- **Type**: `rightRel (Gamma0 m) γ δ ↔ coxRepresentative m γ = coxRepresentative m δ`
- **What**: Two matrices are in the same right coset iff they have the same Cox representative — the heart of Lemma 11.11.
- **How**: (⇒) `exists_coxInput_eq_mul_of_rightRel` + `coxMatrix_reduction_unique`; (⇐) `rightRel_of_coxInput_eq_mul` with `W = U_γ U_δ⁻¹`.
- **Hypotheses**: none.
- **Uses from project**: [`coxRepresentative`, `coxReductionMatrix`, `coxReduction_spec`, `exists_coxInput_eq_mul_of_rightRel`, `coxMatrix_reduction_unique`, `rightRel_of_coxInput_eq_mul`, `coxInput`]
- **Used by**: `rightCosetToCoxMatrix`, `rightCosetToCoxMatrix_bijective`
- **Visibility**: private
- **Lines**: 424–446, proof ≈ 21 lines
- **Notes**: —

### `private theorem Cox.matrixStar_inclusionMatrix`
- **Type**: `matrixStar σ.inclusionMatrix = σ.mobiusMatrix`
- **What**: Converse of `matrixStar_mobiusMatrix`.
- **How**: `matrixStar_involutive`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`, `matrixStar_mobiusMatrix`, `matrixStar_involutive`, `CoxMatrix.inclusionMatrix`, `CoxMatrix.mobiusMatrix`]
- **Used by**: `coxRepresentative_normalization`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 448–450, proof ≈ 1 line
- **Notes**: —

### `private theorem Cox.coxRepresentative_normalization`
- **Type**: `∃ δ : SL(2, ℤ), (δ⁻¹).1 * !![m * γ 0 0, m * γ 0 1; γ 1 0, γ 1 1] = (coxRepresentative m γ).mobiusMatrix`
- **What**: `diag(m,1)·γ` is left-`SL₂(ℤ)`-equivalent to the Möbius matrix of its Cox representative (the matrix form of Cox (11.12)).
- **How**: Anti-transpose `coxReduction_spec` with `matrixStar_mul`, `matrixStar_inclusionMatrix`, `matrixStar_involutive`; `δ = (slStar U)⁻¹`.
- **Hypotheses**: none.
- **Uses from project**: [`coxReductionMatrix`, `coxReduction_spec`, `slStar`, `coe_slStar`, `matrixStar`, `matrixStar_mul`, `matrixStar_inclusionMatrix`, `matrixStar_involutive`, `determinantScale`, `coxInput`, `coxRepresentative`, `CoxMatrix.mobiusMatrix`]
- **Used by**: `rightCosetEval_equiv`
- **Visibility**: private
- **Lines**: 452–469, proof ≈ 16 lines
- **Notes**: The `hD` block (462–466) re-proves `determinantScale m * γ = !![m γ₀₀, m γ₀₁; γ₁₀, γ₁₁]`, i.e. the un-starred twin of `coxInput_eq`.

### `private theorem Cox.coxInput_one`
- **Type**: `coxInput m 1 = (sigmaZero m).inclusionMatrix`
- **What**: The identity coset's `coxInput` is already `σ₀`'s inclusion matrix.
- **How**: `coxInput_eq` + entrywise simp.
- **Hypotheses**: none.
- **Uses from project**: [`coxInput`, `coxInput_eq`, `sigmaZero`, `CoxMatrix.inclusionMatrix`]
- **Used by**: `coxRepresentative_one`
- **Visibility**: private
- **Lines**: 471–475, proof ≈ 3 lines
- **Notes**: —

### `private theorem Cox.coxRepresentative_one`
- **Type**: `coxRepresentative m 1 = sigmaZero m`
- **What**: The identity coset corresponds to `σ₀`.
- **How**: `coxMatrix_reduction_unique` with `V = 1` and `coxInput_one`.
- **Hypotheses**: none.
- **Uses from project**: [`coxRepresentative`, `coxMatrix_reduction_unique`, `coxReduction_spec`, `coxInput_one`, `sigmaZero`]
- **Used by**: `coxMatrixEquivRightCosets_sigmaZero`
- **Visibility**: private
- **Lines**: 477–482, proof ≈ 4 lines
- **Notes**: —

### `private theorem Cox.exists_coprime_add_mul_of_gcd_gcd_eq_one`
- **Type**: `(a b d : ℕ) (ha : a ≠ 0) (h : Nat.gcd (Nat.gcd a b) d = 1) : ∃ x : ℕ, Nat.Coprime a (b + x * d)`
- **What**: If `gcd(a,b,d) = 1` then some `b + xd` is coprime to `a` (a residue class mod `d` contains an element coprime to `a`).
- **How**: Takes `x = ∏{p ∣ a prime, p ∤ b}`; for each prime `p ∣ a`, splits on `p ∣ b` (`Nat.Prime.dvd_finsetProd_iff`, `Nat.dvd_add_iff_right/left`).
- **Hypotheses**: `a ≠ 0`, `gcd(a,b,d) = 1`.
- **Uses from project**: []
- **Used by**: `coxMatrix_smith_normalization`
- **Visibility**: private
- **Lines**: 484–507, proof ≈ 22 lines
- **Notes**: Pure ℕ lemma; no mathlib analogue found (searched `exists_coprime`, `coprime_add_mul*` in Data/Nat/GCD, RingTheory/Coprime, NumberTheory — mathlib's `Nat.coprime_add_mul_right_right` etc. are the trivial iff versions). Mathlib-worthy as `Nat.exists_coprime_add_mul`.

### `private theorem Cox.coxMatrix_smith_normalization`
- **Type**: `(σ : CoxMatrix m) : ∃ L R : SL(2, ℤ), (L⁻¹).1 * σ.inclusionMatrix * R.1 = determinantScaleDual m`
- **What**: Every primitive determinant-`m` Cox inclusion matrix is `SL₂(ℤ)×SL₂(ℤ)`-equivalent to `diag(1, m)` (Smith normal form with unit-determinant transforms).
- **How**: Column op `R₁` makes the `(0,0)` entry `b + xd` coprime to `a` (`exists_coprime_add_mul_of_gcd_gcd_eq_one`), `IsCoprime.exists_SL2_col` gives `L` with first column `(b+xd, a)`, then `N = L⁻¹ M` has `N₀₀ = 1`, `N₁₀ = 0`, `N₁₁ = m` (`Matrix.det_fin_two`, `SL2_inv_expl`, `linear_combination`); a shear `R₂` clears `N₀₁`.
- **Hypotheses**: none.
- **Uses from project**: [`exists_coprime_add_mul_of_gcd_gcd_eq_one`, `CoxMatrix.inclusionMatrix`, `CoxMatrix.inclusionMatrix_det`, `CoxMatrix.primitive`, `CoxMatrix.a_pos`, `determinantScaleDual`]
- **Used by**: `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 509–560, proof ≈ 50 lines
- **Notes**: Proof >30 lines (longest in file). Mathlib's Smith normal form (`Mathlib/LinearAlgebra/FreeModule/Int.lean`, `LinearAlgebra/PID.lean`: `Submodule.smithNormalForm`, basis-level) does not give explicit `SL₂` factors; no direct analogue.

### `private theorem Cox.coxRepresentative_surjective`
- **Type**: `Function.Surjective (coxRepresentative m)`
- **What**: Every Cox matrix is the representative of some coset.
- **How**: From `L⁻¹ H R = diag(1,m)` take `γ = slStar L`; then `coxInput γ · R⁻¹ = H` by `matrixStar_mul`, `matrixStar_determinantScale`; conclude with `coxMatrix_reduction_unique`.
- **Hypotheses**: none.
- **Uses from project**: [`coxRepresentative`, `coxMatrix_smith_normalization`, `slStar`, `coe_slStar`, `coxMatrix_reduction_unique`, `coxReduction_spec`, `coxInput`, `matrixStar_mul`, `matrixStar_involutive`, `matrixStar_determinantScale`, `determinantScaleDual`, `CoxMatrix.inclusionMatrix`]
- **Used by**: `rightCosetToCoxMatrix_bijective`, `rightCosetEval_equiv`
- **Visibility**: private
- **Lines**: 562–579, proof ≈ 16 lines
- **Notes**: —

### `private def Cox.rightCosetToCoxMatrix`
- **Type**: `(m) : Gamma0RightCosets m → CoxMatrix m`
- **What**: The representative map descended to right cosets.
- **How**: `Quotient.lift` with `rightRel_iff_coxRepresentative_eq`.
- **Hypotheses**: none.
- **Uses from project**: [`Gamma0RightCosets`, `coxRepresentative`, `rightRel_iff_coxRepresentative_eq`]
- **Used by**: `rightCosetToCoxMatrix_bijective`, `coxMatrixEquivRightCosets`, `coxMatrixEquivRightCosets_coxRepresentative`
- **Visibility**: private
- **Lines**: 581–584
- **Notes**: —

### `private theorem Cox.rightCosetToCoxMatrix_bijective`
- **Type**: `Function.Bijective (rightCosetToCoxMatrix m)`
- **What**: The descended map is a bijection.
- **How**: Injective by `rightRel_iff_coxRepresentative_eq` + `Quotient.sound`; surjective by `coxRepresentative_surjective`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetToCoxMatrix`, `rightRel_iff_coxRepresentative_eq`, `coxRepresentative_surjective`]
- **Used by**: `coxMatrixEquivRightCosets`, `coxMatrixEquivRightCosets_coxRepresentative`
- **Visibility**: private
- **Lines**: 586–596, proof ≈ 9 lines
- **Notes**: —

### `def Cox.coxMatrixEquivRightCosets`
- **Type**: `(m : ℕ+) : CoxMatrix m ≃ Gamma0RightCosets m`
- **What**: Cox Lemma 11.11: `C(m)` is in bijection with `Γ₀(m)\SL₂(ℤ)`.
- **How**: `(Equiv.ofBijective _ rightCosetToCoxMatrix_bijective).symm`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`, `Gamma0RightCosets`, `rightCosetToCoxMatrix`, `rightCosetToCoxMatrix_bijective`]
- **Used by**: `coxMatrixEquivRightCosets_coxRepresentative`, `coxMatrixEquivRightCosets_sigmaZero`, `rightCosetEval_equiv`, `rightCosetTranslate_sigmaZero`
- **Visibility**: public (noncomputable)
- **Lines**: 600–603
- **Notes**: Used by 5 other files. The corollary `(Gamma0 m).index = Fintype.card (CoxMatrix m)` is never stated.

### `private theorem Cox.coxMatrixEquivRightCosets_coxRepresentative`
- **Type**: `coxMatrixEquivRightCosets m (coxRepresentative m γ) = Quotient.mk'' γ`
- **What**: The equivalence sends the representative of `γ` to the class of `γ`.
- **How**: `Equiv.symm_apply_eq` + `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`coxMatrixEquivRightCosets`, `coxRepresentative`, `rightCosetToCoxMatrix`, `rightCosetToCoxMatrix_bijective`]
- **Used by**: `coxMatrixEquivRightCosets_sigmaZero`, `rightCosetEval_equiv`
- **Visibility**: private
- **Lines**: 605–611, proof ≈ 3 lines
- **Notes**: `@[simp]` on a private lemma.

### `def Cox.rightCosetTranslate`
- **Type**: `(m) {f : ℍ → ℂ} (hf : CuspData m f) (c : Gamma0RightCosets m) (τ : ℍ) : ℂ`
- **What**: `f(γτ)` for `c = Γ₀(m)γ`, well defined because `f` is `Γ₀(m)`-invariant.
- **How**: `Quotient.liftOn`; invariance from `hf.2.1` (weight-0 slash invariance) via `ModularForm.SL_slash_apply` and `mul_smul`.
- **Hypotheses**: `f` has `CuspData m` (meromorphic, `Γ₀(m)`-invariant, meromorphic at cusps).
- **Uses from project**: [`CuspData`, `Gamma0RightCosets`]
- **Used by**: `rightCosetTranslate_mk`, `rightCosetEval`, `rightCosetTranslate_smul`, `rightCosetTranslate_sigmaZero`
- **Visibility**: public (noncomputable)
- **Lines**: 615–623
- **Notes**: Only `hf.2.1` is used; the meromorphy parts of `CuspData` are dead weight here (generalization note).

### `theorem Cox.rightCosetTranslate_mk`
- **Type**: `rightCosetTranslate m hf (Quotient.mk'' γ) τ = f (γ • τ)`
- **What**: Evaluation on a representative.
- **How**: `rfl`.
- **Hypotheses**: as above.
- **Uses from project**: [`rightCosetTranslate`, `CuspData`]
- **Used by**: `rightCosetTranslate_sigmaZero`
- **Visibility**: public
- **Lines**: 626–629
- **Notes**: `@[simp]`.

### `def Cox.rightCosetEval`
- **Type**: `(m) (c : Gamma0RightCosets m) (τ : ℍ) : ℂ` := `rightCosetTranslate m (levelJ_cuspData m) c τ`
- **What**: The conjugate `j(mγτ)` attached to the coset of `γ`.
- **How**: specialisation of `rightCosetTranslate` to `levelJ m = j(m·)`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetTranslate`, `levelJ_cuspData`, `Gamma0RightCosets`]
- **Used by**: `rightCosetEval_mk`, `rightCosetEval_smul`, `rightCosetEval_equiv`
- **Visibility**: public (noncomputable)
- **Lines**: 632–633
- **Notes**: Used by 5 other files.

### `theorem Cox.rightCosetEval_mk`
- **Type**: `rightCosetEval m (Quotient.mk'' γ) τ = levelJ m (γ • τ)`
- **What**: Evaluation on a representative.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetEval`, `levelJ`]
- **Used by**: `rightCosetEval_equiv`
- **Visibility**: public
- **Lines**: 636–638
- **Notes**: `@[simp]`.

### `def Cox.rightCosetMul`
- **Type**: `(m) (δ : SL(2, ℤ)) : Gamma0RightCosets m ≃ Gamma0RightCosets m`
- **What**: Right multiplication by `δ` permutes the right cosets.
- **How**: `Quotient.map'` for `γ ↦ γδ` and `γ ↦ γδ⁻¹`, with `QuotientGroup.rightRel_apply` and `mul_assoc`; inverse laws by `Quotient.inductionOn`.
- **Hypotheses**: none.
- **Uses from project**: [`Gamma0RightCosets`]
- **Used by**: `rightCosetMul_mk`, `exists_rightCosetMul_baseRightCoset_eq`, `rightCosetTranslate_smul`, `rightCosetEval_smul`
- **Visibility**: public
- **Lines**: 641–662 (22 lines)
- **Notes**: Nothing about `Γ₀(m)` is used — this is the right action of `G` (or `Gᵐᵒᵖ`) on `H\G` for any subgroup; not packaged as a `MulAction`. Mathlib's `MulAction.right_quotientAction'` (GroupAction/Quotient.lean:77) needs `H.Normal`; no mathlib action of `Gᵐᵒᵖ` on `Quotient (rightRel H)` found.

### `theorem Cox.rightCosetMul_mk`
- **Type**: `rightCosetMul m δ (Quotient.mk'' γ) = Quotient.mk'' (γ * δ)`
- **What**: Formula on representatives.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetMul`]
- **Used by**: `exists_rightCosetMul_baseRightCoset_eq` (via `simp`)
- **Visibility**: public
- **Lines**: 666–668
- **Notes**: `@[simp]`.

### `def Cox.baseRightCoset`
- **Type**: `(m) : Gamma0RightCosets m` := `Quotient.mk'' 1`
- **What**: The coset of the identity.
- **How**: literal.
- **Hypotheses**: none.
- **Uses from project**: [`Gamma0RightCosets`]
- **Used by**: `exists_rightCosetMul_baseRightCoset_eq`
- **Visibility**: public
- **Lines**: 671–672
- **Notes**: Used by 3 other files. `coxMatrixEquivRightCosets_sigmaZero` (763) proves `… = Quotient.mk'' 1` without naming `baseRightCoset`.

### `theorem Cox.exists_rightCosetMul_baseRightCoset_eq`
- **Type**: `(c) : ∃ δ, rightCosetMul m δ (baseRightCoset m) = c`
- **What**: The right action on cosets is transitive from the identity coset.
- **How**: `Quotient.exists_rep` + `simp`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetMul`, `baseRightCoset`, `rightCosetMul_mk`]
- **Used by**: unused in file (used by ModularPolynomial/Irreducibility.lean)
- **Visibility**: public
- **Lines**: 675–678, proof ≈ 2 lines
- **Notes**: —

### `theorem Cox.rightCosetTranslate_smul`
- **Type**: `rightCosetTranslate m hf c (δ • τ) = rightCosetTranslate m hf (rightCosetMul m δ c) τ`
- **What**: Translating the argument by `δ` is right multiplication of the coset.
- **How**: `Quotient.inductionOn` + `mul_smul`.
- **Hypotheses**: `CuspData m f`.
- **Uses from project**: [`rightCosetTranslate`, `rightCosetMul`, `CuspData`]
- **Used by**: `rightCosetEval_smul`
- **Visibility**: public
- **Lines**: 682–690, proof ≈ 4 lines
- **Notes**: —

### `theorem Cox.rightCosetEval_smul`
- **Type**: `rightCosetEval m c (δ • τ) = rightCosetEval m (rightCosetMul m δ c) τ`
- **What**: Same for the `j`-conjugates.
- **How**: instance of `rightCosetTranslate_smul`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetEval`, `rightCosetTranslate_smul`, `levelJ_cuspData`, `rightCosetMul`]
- **Used by**: unused in file (used by 3 other files)
- **Visibility**: public
- **Lines**: 694–697, proof ≈ 1 line
- **Notes**: —

### `private lemma Cox.complex_mobius_scale_eq_affine`
- **Type**: `{n p q u v a b c d g r s z : ℂ} (hD : c*z + d ≠ 0) (hs : s ≠ 0) (h00 : p*(n*a) + q*c = g) (h01 : p*(n*b) + q*d = r) (h10 : u*(n*a) + v*c = 0) (h11 : u*(n*b) + v*d = s) : (p*(n*((a*z+b)/(c*z+d))) + q) / (u*(n*((a*z+b)/(c*z+d))) + v) = r/s + g/s * z`
- **What**: If `[[p,q],[u,v]]·diag(n,1)·[[a,b],[c,d]] = [[g,r],[0,s]]` then the composite Möbius map is the affine map `z ↦ (gz + r)/s`.
- **How**: `field_simp` + `linear_combination` twice, then `ring`.
- **Hypotheses**: denominators nonzero and the four entry identities.
- **Uses from project**: []
- **Used by**: `levelJ_smul_eq_j_act_of_normalization`
- **Visibility**: private
- **Lines**: 699–717, proof ≈ 11 lines
- **Notes**: Pure field identity; would be unnecessary if `act` were defined through mathlib's Möbius action (then it is `mul_smul`).

### `private theorem Cox.levelJ_smul_eq_j_act_of_normalization`
- **Type**: `(hmat : (δ⁻¹).1 * !![m γ₀₀, m γ₀₁; γ₁₀, γ₁₁] = σ.mobiusMatrix) (τ) : levelJ m (γ • τ) = j (σ.act τ)`
- **What**: Cox (11.12) at the level of points: if `δ⁻¹·diag(m,1)·γ = σ` then `j(m·γτ) = j(σ·τ)`.
- **How**: `j` is `SL₂(ℤ)`-invariant (`j_modularGroup_smul` with `δ⁻¹`), so it suffices that `δ⁻¹ • (m·γτ) = σ·τ`, which is `complex_mobius_scale_eq_affine` after casting the four matrix identities to ℂ (`UpperHalfPlane.coe_specialLinearGroup_apply`, `UpperHalfPlane.denom_ne_zero`).
- **Hypotheses**: the matrix identity.
- **Uses from project**: [`levelJ`, `j`, `j_modularGroup_smul`, `CoxMatrix.act`, `CoxMatrix.coe_act`, `CoxMatrix.mobiusMatrix`, `CoxMatrix.d_pos`, `complex_mobius_scale_eq_affine`]
- **Used by**: `rightCosetEval_equiv`
- **Visibility**: private
- **Lines**: 719–761, proof ≈ 41 lines
- **Notes**: Proof >30 lines; 20 of them are `change`/cast bookkeeping (739–753). See Observations (GL⁺ action).

### `private theorem Cox.coxMatrixEquivRightCosets_sigmaZero`
- **Type**: `coxMatrixEquivRightCosets m (sigmaZero m) = Quotient.mk'' 1`
- **What**: `σ₀` corresponds to the identity coset.
- **How**: `coxRepresentative_one` + `coxMatrixEquivRightCosets_coxRepresentative`.
- **Hypotheses**: none.
- **Uses from project**: [`coxMatrixEquivRightCosets`, `sigmaZero`, `coxRepresentative_one`, `coxMatrixEquivRightCosets_coxRepresentative`]
- **Used by**: `rightCosetTranslate_sigmaZero`
- **Visibility**: private
- **Lines**: 763–766, proof ≈ 2 lines
- **Notes**: RHS is `baseRightCoset m` but not written so.

### `theorem Cox.rightCosetEval_equiv`
- **Type**: `(σ : CoxMatrix m) (τ) : rightCosetEval m (coxMatrixEquivRightCosets m σ) τ = j (σ.act τ)`
- **What**: Cox (11.12): the `j`-conjugate of the coset corresponding to `σ` is `j(σ·τ)`.
- **How**: Write `σ = coxRepresentative γ` (`coxRepresentative_surjective`), reduce with `rightCosetEval_mk`, apply `coxRepresentative_normalization` and `levelJ_smul_eq_j_act_of_normalization`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetEval`, `rightCosetEval_mk`, `coxMatrixEquivRightCosets`, `coxMatrixEquivRightCosets_coxRepresentative`, `coxRepresentative_surjective`, `coxRepresentative_normalization`, `levelJ_smul_eq_j_act_of_normalization`, `CoxMatrix.act`, `j`]
- **Used by**: unused in file (used by 4 other files)
- **Visibility**: public
- **Lines**: 769–774, proof ≈ 4 lines
- **Notes**: —

### `theorem Cox.rightCosetTranslate_sigmaZero`
- **Type**: `rightCosetTranslate m hf (coxMatrixEquivRightCosets m (sigmaZero m)) τ = f τ`
- **What**: Translating by `σ₀` (identity coset) is trivial.
- **How**: `coxMatrixEquivRightCosets_sigmaZero`, `rightCosetTranslate_mk`, `simp`.
- **Hypotheses**: `CuspData m f`.
- **Uses from project**: [`rightCosetTranslate`, `rightCosetTranslate_mk`, `coxMatrixEquivRightCosets`, `coxMatrixEquivRightCosets_sigmaZero`, `sigmaZero`, `CuspData`]
- **Used by**: unused in file (used by ModularPolynomial/Interpolation.lean)
- **Visibility**: public
- **Lines**: 778–782, proof ≈ 3 lines
- **Notes**: —

### `theorem Cox.j_act_sigmaZero`
- **Type**: `(fun τ ↦ j ((sigmaZero m).act τ)) = levelJ m`
- **What**: `j(σ₀·τ) = j(mτ)`.
- **How**: `funext`, `UpperHalfPlane.ext`, `simp [sigmaZero, CoxMatrix.act]`.
- **Hypotheses**: none.
- **Uses from project**: [`j`, `sigmaZero`, `CoxMatrix.act`, `levelJ`]
- **Used by**: unused in file (used by ModularPolynomial/Interpolation, Construction)
- **Visibility**: public
- **Lines**: 784–789, proof ≈ 4 lines
- **Notes**: —

### `theorem Cox.exists_sl2_mul_eq_coxMatrix`
- **Type**: `(M) (hdet : M.det = m) (hprimitive : M.rankTwoContent = 1) : ∃ γ : SL(2, ℤ), ∃ σ : CoxMatrix m, γ.1 * M = σ.mobiusMatrix`
- **What**: Report Lemma 5.8: every primitive integer matrix of determinant `m` is left-`SL₂(ℤ)`-equivalent to a Cox matrix.
- **How**: Anti-transpose `M`, column-reduce with `exists_sl_right_mul_isColumnHermiteNormalForm_aux`, package via `exists_coxMatrix_of_isColumnHermiteNormalForm_aux`, anti-transpose back with `matrixStar_mul`/`matrixStar_involutive`/`matrixStar_inclusionMatrix`.
- **Hypotheses**: `det M = m`, content 1.
- **Uses from project**: [`matrixStar`, `matrixStar_det`, `matrixStar_mul`, `matrixStar_involutive`, `matrixStar_inclusionMatrix`, `rankTwoContent_mul_sl`, `exists_sl_right_mul_isColumnHermiteNormalForm_aux`, `exists_coxMatrix_of_isColumnHermiteNormalForm_aux`, `slStar`, `Matrix.rankTwoContent`, `CoxMatrix.mobiusMatrix`]
- **Used by**: unused in file (used by SingularModuli.lean)
- **Visibility**: public
- **Lines**: 793–820, proof ≈ 26 lines
- **Notes**: 805–808 re-proves content invariance under anti-transpose (`ac_rfl`) — a missing `rankTwoContent_matrixStar` lemma. Uniqueness of `σ` is not stated (it follows from `columnHNF_eq_of_mul`).

## File Summary
- Total declarations: 76 (17 defs/abbrevs incl. 1 structure, 55 lemmas/theorems, 3 instances, 1 other[structure counted in defs])
- Key API (used by 3+ others in the file): `CoxMatrix`, `CoxMatrix.inclusionMatrix` (14), `CoxMatrix.mobiusMatrix` (5), `CoxMatrix.act` (4), `sigmaZero` (6), `Gamma0RightCosets` (10), `matrixStar` (12), `matrixStar_involutive` (4), `matrixStar_mul` (3), `matrixStar_det` (3), `coxInput` (12), `coxInput_eq` (4), `coxRepresentative` (8), `coxReduction_spec` (4), `coxMatrix_reduction_unique` (3), `coxMatrixEquivRightCosets` (4), `rightCosetTranslate` (4), `rightCosetMul` (4), `slStar` (4), `determinantScaleDual` (3)
- Unused declarations (not used by anything in this file): `inclusionMatrix_content_eq_one`, `one_lt_card_coxMatrix`, `exists_rightCosetMul_baseRightCoset_eq`, `rightCosetEval_smul`, `rightCosetEval_equiv`, `rightCosetTranslate_sigmaZero`, `j_act_sigmaZero`, `exists_sl2_mul_eq_coxMatrix` (all are used by other project files); instances `instDecidableEq`, `gamma0RightCosetsFintype` (implicit)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `columnHNF_eq_of_mul` (247–285, 37), `coxMatrix_smith_normalization` (509–560, 50), `levelJ_smul_eq_j_act_of_normalization` (719–761, 41)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `matrixStar` (154) is `Aᵀ` conjugated by the swap: `matrixStar A = (A.submatrix Fin.rev Fin.rev)ᵀ`. With mathlib `Matrix.transpose_mul` (Data/Matrix/Mul.lean:1144), `Matrix.submatrix_mul_equiv` (Mul.lean:1161), `Matrix.det_transpose` (LinearAlgebra/Matrix/Determinant/Basic.lean:202), `Matrix.det_submatrix_equiv_self` (Determinant/Basic.lean:223) and `Fin.revPerm` (Data/Fin/Rev.lean:35), `matrixStar_involutive/_mul/_det` (158–173) become one-liners and the def generalises to any `CommRing` and any `Fin n`.
- `Gamma0RightCosets` (141) + `gamma0RightCosetsFintype` (144): fine as is (mathlib `QuotientGroup.rightRel`, `Subgroup.fintypeQuotientOfFiniteIndex` GroupTheory/Index.lean:707, `quotientRightRelEquivQuotientLeftRel` GroupTheory/Coset/Defs.lean:130). Missing corollary: `(Gamma0 m).index = Fintype.card (CoxMatrix m)` (from `Fintype.card_congr (coxMatrixEquivRightCosets m)` + `Subgroup.index_eq_card`); mathlib's CongruenceSubgroups.lean has NO index formula for `Gamma0` (only `instFiniteIndexGamma0`, line 206), so this + Cardinality.lean's `card_coxMatrix` would be a mathlib-worthy `Gamma0_index`.
- `CoxMatrix.act` (80) hand-rolls the Möbius action of a positive-determinant integer matrix. Mathlib's `UpperHalfPlane` has the `SL(2,ℤ)`/`GL(2,ℝ)⁺` action (`UpperHalfPlane.coe_specialLinearGroup_apply`, used at 733/737) and `posRealAction` (UpperHalfPlane/Basic.lean:197). Defining `act σ τ := (σ.mobiusMatrix mapped to GL(2,ℝ)⁺) • τ` would turn `levelJ_smul_eq_j_act_of_normalization` (719–761, 41 lines) + `complex_mobius_scale_eq_affine` (699–717) into `mul_smul` + "scalar matrices act trivially", and `qParam_coxAction_aux`/`coe_act` stay as the explicit formula. No exact mathlib analogue of `act` found (searched `UpperHalfPlane/Basic.lean` instances).
- `Matrix.rankTwoContent` (HermiteNormalForm.lean:44) has no mathlib analogue (searched `Matrix.content`, `gcd` of entries); the invariance `rankTwoContent_mul_sl` (225) and the anti-transpose invariance (805–808) are its natural companions.
- `mathlib` `FixedDetMatrix.reps m` (LinearAlgebra/Matrix/FixedDetMatrices.lean:69: `{A ∈ Δ m | A₁₀ = 0 ∧ 0 < A₀₀ ∧ 0 ≤ A₀₁ ∧ |A₀₁| < |A₁₁|}`) is Cox's `C(m)` WITHOUT primitivity, with `repsFintype` (159), `reduce_mem_reps` (175: every `Δ m` element is `SL₂`-equivalent to a rep) and `induction_on` (238). `exists_sl2_mul_eq_coxMatrix` (793) is the primitive refinement of `reduce_mem_reps`; mathlib has no uniqueness of reps (which is `columnHNF_eq_of_mul`, 247). Overlap worth recording for a future mathlib PR: `CoxMatrix m ≃ {A ∈ reps m | primitive}`.
- `one_lt_card_coxMatrix` (123): could use `Fintype.one_lt_card_iff_nontrivial`; fine.
- The entrywise 2×2 pattern `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]` at 167–168, 201–202, 340–341, 464–466, 558–560, 255–256, 380–385: mathlib's `Matrix.det_fin_two_of` is used, but `Matrix.mul_fin_two` (LinearAlgebra/Matrix/Notation.lean:475: `!![a₁₁,a₁₂;a₂₁,a₂₂] * !![b₁₁,…] = !![…]`) is not — each of these sites could be `rw [Matrix.mul_fin_two]` + `Matrix.ext_iff`/`simp` instead of the `fin_cases`/`mul_apply`/`sum_univ_two` unfolding.
### Missing API / repeated patterns
- `@[ext] CoxMatrix.ext` (still absent; requested in `.mathlib-quality/overview/analysis/step7-api.md:313`): the `cases σ; cases τ; simp_all` ext at 101–103, 296–298, LaurentExpansion.lean:349–351, and `apply CoxMatrix.toFin_injective` at Cardinality.lean:91, Kronecker.lean:67,78, UpperHalfPlaneFunctionField.lean:211.
- `CoxMatrix.ofColumnHNF` (still absent; step7-api.md:148): `exists_coxMatrix_of_isColumnHermiteNormalForm_aux` (358–385) is its body; the July-flagged duplicate inside `exists_coxMatrix_reduction` is already gone (387–397 now calls it).
- `CoxMatrix.d_dvd : σ.d ∣ m`, `CoxMatrix.a_dvd`, `CoxMatrix.div_d : m / σ.d = σ.a`: re-derived at Cardinality.lean:56–59, 93–94, LaurentExpansion.lean:313–314, 339–340.
- `CoxMatrix.coprime_gcd : Nat.Coprime (Nat.gcd σ.a σ.d) σ.b` (or a canonical `primitive'`): the gcd-reassociation `simpa only [Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc]` at 76–77, 383–384, Cardinality.lean:63–64, 82–83.
- `SL₂` cancellation chain `[coe_mul, ← mul_assoc, mul_inv_cancel, coe_one, mul_one]` at 228–230, 405–407, 443–446, 574–579 → `SpecialLinearGroup.mul_coe_inv_coe : A * U.1 * (U⁻¹).1 = A` (or a `MulAction SL(2,ℤ)ᵐᵒᵖ (Matrix …)` so `smul_inv_smul` applies).
- Public-API gaps in HermiteNormalForm.lean that this file fills privately: `rankTwoContent_mul_sl` (225), `columnHNF_eq_of_mul` (247, uniqueness), `exists_sl_right_mul_isColumnHermiteNormalForm_aux` (343, `SL₂` refinement), `rankTwoContent_matrixStar` (805–808).
- `sigmaZero_a/_b/_d`, `mobiusMatrix_det`, `act_apply`-style simp lemmas absent; `coxMatrixEquivRightCosets_sigmaZero` (763) should be stated with `baseRightCoset`.
### Junk candidates
- `cuspFunction`-free file: no dead `#check`/`example`s, no commented code. `coe_slStar` (236) and `coxMatrixEquivRightCosets_coxRepresentative` (605) carry `@[simp]` on private lemmas. `determinantScale`/`determinantScaleDual` (180, 183) duplicate `(sigmaZero m).mobiusMatrix`/`.inclusionMatrix` (never identified; `coxInput_one` 471 proves the identification in passing). `a_le`/`d_le` (43, 47) only serve `toFin`.
### Moral duplicates within this batch
- `matrixStar_mobiusMatrix` (175) / `matrixStar_inclusionMatrix` (448): same identity, two directions.
- `coxInput_eq` (197) / the `hD` block in `coxRepresentative_normalization` (462–466): un-starred vs starred entries of `diag(m,1)·γ`.
- `coxRepresentative_one` (477) / `coxMatrixEquivRightCosets_sigmaZero` (763): same fact in two coordinates.
- `rightCosetEval_mk` (636) / `rightCosetTranslate_mk` (626) and `rightCosetEval_smul` (694) / `rightCosetTranslate_smul` (682): one-line specialisations to `levelJ`.
- `toFin_injective` (96) / `inclusionMatrix_injective` (288): both are `CoxMatrix.ext` in disguise.
### Generalization notes
- `Gamma0RightCosets`, `rightCosetMul` (641), `baseRightCoset` (671), `exists_rightCosetMul_baseRightCoset_eq` (675), `rightCosetTranslate` (615) and `rightCosetTranslate_smul` (682) use nothing about `Γ₀(m)` or ℍ beyond "`f` is invariant under the subgroup" (`hf.2.1`): they hold for any `H : Subgroup G` acting on any `X` — a `Subgroup.rightCosetTranslate` API over `Quotient (rightRel H)`.
- `matrixStar*` (154–192) and `reduced_eq_of_eq_add_mul_aux` (239) hold over any `CommRing`/ordered ring; stated for ℤ.
- `complex_mobius_scale_eq_affine` (699) is a `Field` identity stated for ℂ.
- `columnHNF_eq_of_mul` (247) is stated for 2×2 but only uses the three HNF fields; the `Fin 2` case analysis is the only dimension-specific part.
