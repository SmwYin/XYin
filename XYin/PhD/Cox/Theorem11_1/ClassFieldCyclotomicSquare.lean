/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Algebra.Algebra.Tower

/-! # The compatible cyclotomic square
Janusz V.11.2 uses Z′=Z(β), E′=E(β). The splitting-field construction below works over arbitrary
fields and every natural exponent. It does not require a primitive root in the ground field or an
exponent nonzero in its characteristic.
-/

noncomputable section
namespace Cox.ClassFieldTheory
variable (K E : Type*) [Field K] [Field E] [Algebra K E] (q : ℕ)

/-- The upper cyclotomic splitting field contains a copy of the lower splitting field. -/
theorem exists_cyclotomicBaseChangeHom :
    Nonempty (CyclotomicField q K →ₐ[K] CyclotomicField q E) := by
  refine ⟨Polynomial.SplittingField.lift (Polynomial.cyclotomic q K) ?_⟩
  rw [Polynomial.map_cyclotomic,
    ← Polynomial.map_cyclotomic q (algebraMap E (CyclotomicField q E))]
  exact Polynomial.SplittingField.splits (Polynomial.cyclotomic q E)

/-- A fixed compatible embedding for the source cyclotomic square. -/
def cyclotomicBaseChangeHom : CyclotomicField q K →ₐ[K] CyclotomicField q E :=
  Classical.choice (exists_cyclotomicBaseChangeHom K E q)

/-- The upper field is an algebra over the chosen model of the cyclotomic base. -/
@[reducible]
def cyclotomicBaseChangeAlgebra : Algebra (CyclotomicField q K) (CyclotomicField q E) :=
  (cyclotomicBaseChangeHom K E q).toRingHom.toAlgebra

/-- The chosen cyclotomic embedding is compatible with the original K-algebra structure. -/
theorem cyclotomicBaseChange_tower :
    letI := cyclotomicBaseChangeAlgebra K E q
    IsScalarTower K (CyclotomicField q K) (CyclotomicField q E) := by
  letI := cyclotomicBaseChangeAlgebra K E q
  exact IsScalarTower.of_algebraMap_eq' (cyclotomicBaseChangeHom K E q).comp_algebraMap.symm

/-- The images of E and the lower cyclotomic splitting field generate the upper field. -/
theorem cyclotomicBaseChange_adjoin_eq_top :
    letI := cyclotomicBaseChangeAlgebra K E q
    Algebra.adjoin (CyclotomicField q K)
      (Set.range (algebraMap E (CyclotomicField q E))) = ⊤ := by
  letI := cyclotomicBaseChangeAlgebra K E q
  haveI := cyclotomicBaseChange_tower K E q
  haveI : Polynomial.IsSplittingField K (CyclotomicField q K) (Polynomial.cyclotomic q K) :=
    inferInstanceAs (Polynomial.IsSplittingField K (Polynomial.cyclotomic q K).SplittingField _)
  haveI : Polynomial.IsSplittingField E (CyclotomicField q E) (Polynomial.cyclotomic q E) :=
    inferInstanceAs (Polynomial.IsSplittingField E (Polynomial.cyclotomic q E).SplittingField _)
  set f := cyclotomicBaseChangeHom K E q with hf
  have hroots : (Polynomial.cyclotomic q K).rootSet (CyclotomicField q E) =
      (Polynomial.cyclotomic q E).rootSet (CyclotomicField q E) := by
    simp [Polynomial.rootSet, Polynomial.aroots, Polynomial.map_cyclotomic]
  have hlow : Algebra.adjoin K ((Polynomial.cyclotomic q K).rootSet (CyclotomicField q E)) =
      f.range :=
    Polynomial.IsSplittingField.adjoin_rootSet_eq_range (CyclotomicField q K) _ f
  have hup : Algebra.adjoin E ((Polynomial.cyclotomic q E).rootSet (CyclotomicField q E)) = ⊤ :=
    Polynomial.IsSplittingField.adjoin_rootSet (CyclotomicField q E) _
  have htopK : (IsScalarTower.toAlgHom K E (CyclotomicField q E)).range ⊔ f.range = ⊤ := by
    rw [← hlow, hroots, ← Algebra.Subalgebra.restrictScalars_adjoin, hup,
      Subalgebra.restrictScalars_top]
  have hle : (IsScalarTower.toAlgHom K E (CyclotomicField q E)).range ⊔ f.range ≤
      (Algebra.adjoin (CyclotomicField q K)
        (Set.range (algebraMap E (CyclotomicField q E)))).restrictScalars K := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨y, rfl⟩ := (AlgHom.mem_range _).mp hx
      rw [Subalgebra.mem_restrictScalars, IsScalarTower.toAlgHom_apply]
      exact Algebra.subset_adjoin (Set.mem_range_self y)
    · obtain ⟨y, rfl⟩ := (AlgHom.mem_range _).mp hx
      rw [Subalgebra.mem_restrictScalars]
      have hfy : f y = algebraMap (CyclotomicField q K) (CyclotomicField q E) y := rfl
      rw [hfy]
      exact Subalgebra.algebraMap_mem _ y
  rw [eq_top_iff]
  intro x _
  exact hle (htopK ▸ Algebra.mem_top)

end Cox.ClassFieldTheory
