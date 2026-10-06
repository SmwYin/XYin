import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Logic.Equiv.Defs

/-!
# A coordinate bijection for an orbit quotient

An invariant surjective coordinate that separates group orbits identifies the orbit quotient
with its coordinate space. This is the abstract bridge for AINTLIB's `j_surjective` and
`sameOrbit_of_j_eq_j`; it is checked here without importing or instantiating the external `j`.
The result is a bijection of types. Additional topology and analytic geometry are separate input.
-/

namespace MMeromorphicTest.OrbitCoordinate

universe u v w

variable {G : Type u} {X : Type v} {Y : Type w} [Group G] [MulAction G X]

/-- Group invariance makes the coordinate constant on every orbit. -/
theorem coordinate_eq_of_orbitRel (j : X → Y) (hInv : ∀ g : G, ∀ x : X, j (g • x) = j x)
    {x y : X} (hxy : MulAction.orbitRel G X x y) : j x = j y := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hxy)
  exact hInv g y

/-- An invariant coordinate descends through mathlib's group-orbit quotient. -/
def coordinateMap (j : X → Y) (hInv : ∀ g : G, ∀ x : X, j (g • x) = j x) :
    MulAction.orbitRel.Quotient G X → Y :=
  Quotient.lift j fun _ _ h ↦ coordinate_eq_of_orbitRel j hInv h

@[simp] theorem coordinateMap_mk (j : X → Y)
    (hInv : ∀ g : G, ∀ x : X, j (g • x) = j x) (x : X) :
    coordinateMap j hInv (Quotient.mk (MulAction.orbitRel G X) x) = j x := rfl

/-- Surjectivity and separation of orbits are precisely the needed bijection hypotheses. -/
theorem coordinateMap_bijective (j : X → Y)
    (hInv : ∀ g : G, ∀ x : X, j (g • x) = j x) (hSurj : Function.Surjective j)
    (hSep : ∀ x y : X, j x = j y → MulAction.orbitRel G X x y) :
    Function.Bijective (coordinateMap j hInv) := by
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y hxy
    exact Quotient.sound (hSep x y hxy)
  · intro y
    obtain ⟨x, rfl⟩ := hSurj y
    exact ⟨Quotient.mk (MulAction.orbitRel G X) x, rfl⟩

/-- The orbit quotient is equivalent to the space of coordinates. -/
noncomputable def coordinateEquiv (j : X → Y)
    (hInv : ∀ g : G, ∀ x : X, j (g • x) = j x) (hSurj : Function.Surjective j)
    (hSep : ∀ x y : X, j x = j y → MulAction.orbitRel G X x y) :
    MulAction.orbitRel.Quotient G X ≃ Y :=
  Equiv.ofBijective (coordinateMap j hInv) (coordinateMap_bijective j hInv hSurj hSep)

@[simp] theorem coordinateEquiv_mk (j : X → Y)
    (hInv : ∀ g : G, ∀ x : X, j (g • x) = j x) (hSurj : Function.Surjective j)
    (hSep : ∀ x y : X, j x = j y → MulAction.orbitRel G X x y) (x : X) :
    coordinateEquiv j hInv hSurj hSep (Quotient.mk (MulAction.orbitRel G X) x) = j x := rfl

@[simp] theorem coordinateEquiv_symm_apply_coordinate (j : X → Y)
    (hInv : ∀ g : G, ∀ x : X, j (g • x) = j x) (hSurj : Function.Surjective j)
    (hSep : ∀ x y : X, j x = j y → MulAction.orbitRel G X x y) (x : X) :
    (coordinateEquiv j hInv hSurj hSep).symm (j x) =
      Quotient.mk (MulAction.orbitRel G X) x := by
  simpa only [coordinateEquiv_mk] using
    (coordinateEquiv j hInv hSurj hSep).symm_apply_apply
      (Quotient.mk (MulAction.orbitRel G X) x)

/-- Convert the witness orientation used by AINTLIB's `sameOrbit_of_j_eq_j`. -/
theorem orbitRel_of_exists_smul_eq {x y : X} (h : ∃ g : G, g • x = y) :
    MulAction.orbitRel G X x y :=
  (MulAction.orbitRel G X).symm
    (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr h))

/-- The same equivalence with separation stated in the external theorem's witness form. -/
noncomputable def coordinateEquivOfExists (j : X → Y)
    (hInv : ∀ g : G, ∀ x : X, j (g • x) = j x) (hSurj : Function.Surjective j)
    (hSep : ∀ x y : X, j x = j y → ∃ g : G, g • x = y) :
    MulAction.orbitRel.Quotient G X ≃ Y :=
  coordinateEquiv j hInv hSurj fun x y h ↦ orbitRel_of_exists_smul_eq (hSep x y h)

@[simp] theorem coordinateEquivOfExists_mk (j : X → Y)
    (hInv : ∀ g : G, ∀ x : X, j (g • x) = j x) (hSurj : Function.Surjective j)
    (hSep : ∀ x y : X, j x = j y → ∃ g : G, g • x = y) (x : X) :
    coordinateEquivOfExists j hInv hSurj hSep
      (Quotient.mk (MulAction.orbitRel G X) x) = j x := rfl

example (j : X → Y) (hInv : ∀ g : G, ∀ x : X, j (g • x) = j x)
    (hSurj : Function.Surjective j)
    (hSep : ∀ x y : X, j x = j y → ∃ g : G, g • x = y) (y : Y) :
    coordinateEquivOfExists j hInv hSurj hSep
      ((coordinateEquivOfExists j hInv hSurj hSep).symm y) = y :=
  (coordinateEquivOfExists j hInv hSurj hSep).apply_symm_apply y

#print axioms coordinateMap_bijective
#print axioms coordinateEquivOfExists
#print axioms coordinateEquiv_symm_apply_coordinate

end MMeromorphicTest.OrbitCoordinate
