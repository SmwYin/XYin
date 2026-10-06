import XYin.PhD.Cox.LatticeJ
import XYin.PhD.Test.MMeromorphic.OrbitCoordinate

/-!
# The level-one orbit quotient has coordinate `j`

The local production `j_modularGroup_smul`, `j_surjective`, and
`j_eq_iff_exists_sl2_smul_eq` instantiate the abstract orbit-coordinate bridge.
This gives a set-level equivalence `ℍ / SL₂(ℤ) ≃ ℂ` with the actual modular invariant.
It does not construct an analytic modular curve, its compactification, or a function field.
-/

open UpperHalfPlane
open scoped MatrixGroups

namespace MMeromorphicTest.LevelOneOrbit

/-- The actual modular invariant identifies the level-one orbit quotient with `ℂ`. -/
noncomputable def equiv : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ ≃ ℂ :=
  OrbitCoordinate.coordinateEquivOfExists j j_modularGroup_smul j_surjective
    fun τ τ' h ↦ (j_eq_iff_exists_sl2_smul_eq τ τ').mp h

@[simp] theorem equiv_mk (τ : ℍ) :
    equiv (Quotient.mk (MulAction.orbitRel SL(2, ℤ) ℍ) τ) = j τ := rfl

@[simp] theorem equiv_symm_apply_j (τ : ℍ) :
    equiv.symm (j τ) = Quotient.mk (MulAction.orbitRel SL(2, ℤ) ℍ) τ := by
  simpa only [equiv_mk] using
    equiv.symm_apply_apply (Quotient.mk (MulAction.orbitRel SL(2, ℤ) ℍ) τ)

/-- Equality of actual `j` values is equality in the orbit quotient. -/
theorem mk_eq_iff_j_eq (τ τ' : ℍ) :
    Quotient.mk (MulAction.orbitRel SL(2, ℤ) ℍ) τ =
      Quotient.mk (MulAction.orbitRel SL(2, ℤ) ℍ) τ' ↔ j τ = j τ' := by
  rw [← equiv_mk τ, ← equiv_mk τ']
  exact equiv.injective.eq_iff.symm

example (γ : SL(2, ℤ)) (τ : ℍ) :
    Quotient.mk (MulAction.orbitRel SL(2, ℤ) ℍ) (γ • τ) =
      Quotient.mk (MulAction.orbitRel SL(2, ℤ) ℍ) τ :=
  (mk_eq_iff_j_eq _ _).mpr (j_modularGroup_smul γ τ)

example (z : ℂ) : equiv (equiv.symm z) = z := equiv.apply_symm_apply z

#print axioms j_surjective
#print axioms j_eq_iff_exists_sl2_smul_eq
#print axioms equiv
#print axioms equiv_symm_apply_j

end MMeromorphicTest.LevelOneOrbit
