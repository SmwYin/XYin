/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnits
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-! # Finite S-unit radical extensions

Source: Janusz V.8.2 and V.9.3. The S-units are finitely generated, so their quotient
by ambient nth powers is finite.
-/

noncomputable section
namespace Cox.ClassFieldTheory
open NumberField IsDedekindDomain IntermediateField

/-- A finitely generated subgroup has finite quotient by ambient nth powers. -/
theorem finite_quotient_ambient_powers {G : Type*} [CommGroup G]
    (U : Subgroup G) [Group.FG U] (n : ℕ) (hn : n ≠ 0) :
    Finite (U ⧸ ((powMonoidHom n : G →* G).range).subgroupOf U) := by
  letI := Subgroup.finiteIndex_range_powMonoidHom_of_fg U hn
  have hle : (powMonoidHom n : U →* U).range ≤
      ((powMonoidHom n : G →* G).range).subgroupOf U := by
    rintro x ⟨y, rfl⟩
    exact ⟨(y : G), rfl⟩
  letI := Subgroup.finiteIndex_of_le hle
  infer_instance

/-- The S-unit quotient by ambient nth powers is finite. -/
theorem sUnits_finiteQuotient (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : 0 < n) :
    Finite ((sUnits K S) ⧸ (nthPowers K n).subgroupOf (sUnits K S)) := by
  obtain ⟨e⟩ := sUnits_equiv_units_prod_free K S
  letI : Monoid.FG (sUnits K S) :=
    Monoid.fg_of_surjective e.symm.toMonoidHom e.symm.surjective
  letI : Group.FG (sUnits K S) := Group.fg_iff_monoid_fg.mpr inferInstance
  exact finite_quotient_ambient_powers (sUnits K S) n (Nat.ne_of_gt hn)

end Cox.ClassFieldTheory
