/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicModules
import XYin.PhD.Cox.Theorem11_1.ClassFieldFieldUnits

/-! # The finite ideal cokernel in Janusz V.4.2

Erasing prime factors induces a quotient of the ordinary ideal class group.
Finiteness is carried in this direction; no injection into the class group is asserted.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Class-group finiteness gives finite index to the actual principal-ideal range. -/
theorem principalIdeal_range_finiteIndex :
    (toPrincipalIdeal (𝓞 K) K).range.FiniteIndex := by
  rw [← classGroup_mk_ker_eq_principal_range]
  exact Subgroup.finiteIndex_ker _

/-- The erasure projection is onto since it fixes every good ideal. -/
theorem eraseModulusFactors_surjective (m : Ideal (𝓞 K)) :
    Function.Surjective (eraseModulusFactors K m) := by
  intro I
  exact ⟨I, eraseModulusFactors_coprime K m I⟩

/-- The erased principal ideals still have finite index in the good-ideal group. -/
theorem erasePrincipal_range_finiteIndex (m : Ideal (𝓞 K)) :
    ((eraseModulusFactors K m).comp (toPrincipalIdeal (𝓞 K) K)).range.FiniteIndex := by
  rw [MonoidHom.range_comp]
  have hdvd := Subgroup.index_map_dvd (H := (toPrincipalIdeal (𝓞 K) K).range)
    (eraseModulusFactors_surjective K m)
  exact ⟨ne_zero_of_dvd_ne_zero (principalIdeal_range_finiteIndex K).index_ne_zero hdvd⟩

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]

/-- The actual equivariant principal-away image is the additive erased-principal image. -/
theorem principalAway_range_eq (m : Ideal (𝓞 K)) :
    LinearMap.range (principalAwayIntertwining K L m).toLinearMap =
      (((eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L)))).comp
        (toPrincipalIdeal (𝓞 L) L)).range).toAddSubgroup.toIntSubmodule := by
  have hspec : ∀ x : Lˣ, Additive.toMul ((principalAwayIntertwining K L m (Additive.ofMul x) :
      awayIdealSubmodule K L m) : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ) =
      (eraseModulusFactors L (m.map (algebraMap (𝓞 K) (𝓞 L))) (toPrincipalIdeal (𝓞 L) L x) :
        (FractionalIdeal (𝓞 L)⁰ L)ˣ) :=
    Classical.choose_spec (exists_principalAwayIntertwining K L m)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Additive.toMul y, Subtype.ext (hspec (Additive.toMul y)).symm⟩
  · rintro ⟨u, hu⟩
    refine LinearMap.mem_range.mpr
      ⟨Additive.ofMul u, Subtype.ext (Additive.toMul.injective ?_)⟩
    exact (hspec u).trans (congrArg Subtype.val hu)

end Cox.ClassFieldTheory
