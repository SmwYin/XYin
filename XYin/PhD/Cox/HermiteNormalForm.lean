import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Hermite normal form for full-rank integer submodules

This is the declaration skeleton for the Hermite-normal-form API needed in Cox, Chapter 11.
Unlike Smith normal form, Hermite normal form is canonical only after fixing the ambient basis,
so that basis is an explicit parameter of `Module.Basis.HermiteNormalForm`.
-/

open Module

noncomputable section

namespace Matrix

/-- A square integer matrix is in column Hermite normal form when it is upper triangular,
has positive pivots, and each entry above a pivot is the canonical nonnegative remainder.

With columns interpreted as generators, the rank-two shape is `!![d, b; 0, a]` with
`0 < d`, `0 < a`, and `0 ≤ b < d`.
-/
def IsColumnHermiteNormalForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, j < i → A i j = 0) ∧
  (∀ i, 0 < A i i) ∧
  (∀ i j, i < j → A i j ∈ Set.Ico 0 (A i i))

/-- The gcd of the four entries of a two-by-two integer matrix. -/
def rankTwoContent (A : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  Nat.gcd (Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
    (A 1 0).natAbs) (A 1 1).natAbs

end Matrix

namespace Module.Basis

variable {M : Type*} [AddCommGroup M]

/-- A Hermite-normal-form basis for a full-rank submodule `N ≤ M`, relative to a fixed
ambient basis `bM`.  This deliberately parallels `Module.Basis.SmithNormalForm`, while
recording the entire inclusion matrix instead of only diagonal coefficients.
-/
structure HermiteNormalForm {n : ℕ} (bM : Basis (Fin n) ℤ M)
    (N : Submodule ℤ M) where
  /-- The basis of the submodule. -/
  bN : Basis (Fin n) ℤ N
  /-- The matrix of `N.subtype` from `bN` to the fixed ambient basis `bM`. -/
  matrix : Matrix (Fin n) (Fin n) ℤ
  /-- The matrix really represents the inclusion `N ↪ M`. -/
  relation : LinearMap.toMatrix bN bM N.subtype = matrix
  /-- The inclusion matrix is in column Hermite normal form. -/
  isHermite : matrix.IsColumnHermiteNormalForm

namespace HermiteNormalForm

variable {n : ℕ} {bM : Basis (Fin n) ℤ M} {N : Submodule ℤ M}

/-- Coordinates of an HNF submodule basis vector in the ambient basis. -/
theorem repr_apply (h : HermiteNormalForm bM N) (i j : Fin n) :
    bM.repr (N.subtype (h.bN j)) i = h.matrix i j := by
  sorry

/-- The HNF matrix of a fixed submodule relative to a fixed ambient basis is unique. -/
theorem matrix_eq (h h' : HermiteNormalForm bM N) : h.matrix = h'.matrix := by
  sorry

/-- The submodule basis occurring in HNF is unique as well. -/
theorem bN_eq (h h' : HermiteNormalForm bM N) : h.bN = h'.bN := by
  sorry

/-- The index of a full-rank HNF submodule is the absolute determinant of its inclusion
matrix (Cox, Exercise 7.15 in the rank-two case). -/
theorem index_eq_natAbs_det (h : HermiteNormalForm bM N) :
    N.toAddSubgroup.index = h.matrix.det.natAbs := by
  sorry

/-- In rank two, the quotient is cyclic exactly when the entries of the inclusion matrix
are primitive (Cox, Exercise 11.16). -/
theorem quotient_isAddCyclic_iff_rankTwoContent_eq_one
    {bM : Basis (Fin 2) ℤ M} {N : Submodule ℤ M}
    (h : HermiteNormalForm bM N) :
    IsAddCyclic (M ⧸ N) ↔ Matrix.rankTwoContent h.matrix = 1 := by
  sorry

end HermiteNormalForm

end Module.Basis

namespace Submodule

variable {M : Type*} [AddCommGroup M]

/-- Every full-rank integer submodule admits an HNF basis relative to a fixed ambient basis. -/
theorem exists_hermiteNormalForm {n : ℕ} (bM : Basis (Fin n) ℤ M)
    (N : Submodule ℤ M) (hN : Module.finrank ℤ N = n) :
    Nonempty (Module.Basis.HermiteNormalForm bM N) := by
  sorry

/-- The canonical HNF chosen from `exists_hermiteNormalForm`. -/
noncomputable def hermiteNormalForm {n : ℕ} (bM : Basis (Fin n) ℤ M)
    (N : Submodule ℤ M) (hN : Module.finrank ℤ N = n) :
    Module.Basis.HermiteNormalForm bM N :=
  Classical.choice (N.exists_hermiteNormalForm bM hN)

end Submodule
