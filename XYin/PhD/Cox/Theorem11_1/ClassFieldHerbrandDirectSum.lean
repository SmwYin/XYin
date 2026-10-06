/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldHerbrandProduct
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators

/-! # Finite direct sums of cyclic Tate modules

Use the native Option and index equivalences and iterate the split sequence from Janusz V.1.3.
The finiteness endpoint needs only a finite index type; the product formula uses a chosen Fintype.
-/

noncomputable section

open DirectSum

universe u v w

namespace Cox.CyclicCohomology

/-- The native Option decomposition of a direct sum preserves the componentwise action. -/
theorem directSum_option_equivariant
    {G ι : Type*} [Monoid G] {A : Option ι → Type*}
    [∀ i, AddCommGroup (A i)] (ρ : ∀ i, Representation ℤ G (A i))
    (γ : G) (x : ⨁ i, A i) :
    (DirectSum.lequivProdDirectSum (R := ℤ) (α := A))
        ((Representation.directSum ρ) γ x) =
      ((ρ none).prod (Representation.directSum (fun i => ρ (some i)))) γ
        ((DirectSum.lequivProdDirectSum (R := ℤ) (α := A)) x) := by
  refine Prod.ext rfl ?_
  ext i
  rfl

/-- The native index equivalence preserves the reindexed componentwise action. -/
theorem directSum_reindex_equivariant
    {G ι κ : Type*} [Monoid G] {A : ι → Type*}
    [∀ i, AddCommGroup (A i)] (ρ : ∀ i, Representation ℤ G (A i))
    (e : ι ≃ κ) (γ : G) (x : ⨁ i, A i) :
    (DirectSum.lequivCongrLeft (R := ℤ) (M := A) e)
        ((Representation.directSum ρ) γ x) =
      (Representation.directSum (fun k => ρ (e.symm k))) γ
        ((DirectSum.lequivCongrLeft (R := ℤ) (M := A) e) x) := by
  ext k
  rfl

/-- Finite direct sums of modules with finite Tate groups again have finite Tate groups. -/
theorem finiteHerbrand_directSum
    {G : Type u} {ι : Type v} [Group G] [Fintype G] [Finite ι]
    {A : ι → Type w} [∀ i, AddCommGroup (A i)]
    (ρ : ∀ i, Representation ℤ G (A i)) (g : G)
    (h : ∀ i, FiniteHerbrand (ρ i) g) :
    FiniteHerbrand (Representation.directSum ρ) g := by
  suffices key : ∀ (ι : Type v) [Finite ι] (A : ι → Type w) [∀ i, AddCommGroup (A i)]
      (ρ : ∀ i, Representation ℤ G (A i)), (∀ i, FiniteHerbrand (ρ i) g) →
        FiniteHerbrand (Representation.directSum ρ) g from key ι A ρ h
  intro ι _
  refine Finite.induction_empty_option (P := fun ι : Type v => ∀ (A : ι → Type w)
      [∀ i, AddCommGroup (A i)] (ρ : ∀ i, Representation ℤ G (A i)),
      (∀ i, FiniteHerbrand (ρ i) g) → FiniteHerbrand (Representation.directSum ρ) g)
    ?_ ?_ ?_ ι
  · intro α β e hα A _ ρ h
    exact (finiteHerbrand_iff g _ _ (DirectSum.lequivCongrLeft (R := ℤ) (M := A) e.symm).toAddEquiv
      (directSum_reindex_equivariant ρ e.symm)).mpr
      (hα (fun a => A (e.symm.symm a)) (fun a => ρ (e.symm.symm a)) (fun a => h _))
  · intro A _ ρ _
    haveI : Unique (⨁ i : PEmpty, A i) := DFinsupp.uniqueOfIsEmpty
    exact finiteHerbrand_of_finite _ g
  · intro α _ hα A _ ρ h
    exact (finiteHerbrand_iff g _ _ (DirectSum.lequivProdDirectSum (R := ℤ) (α := A)).toAddEquiv
      (directSum_option_equivariant ρ)).mpr
      (finiteHerbrand_prod (ρ none) (Representation.directSum fun i => ρ (some i)) g (h none)
        (hα (fun i => A (some i)) (fun i => ρ (some i)) (fun i => h (some i))))

/-- Janusz V.1.3 iterated over a finite index type: the quotient is the product of the factors. -/
theorem herbrandQuotient_directSum
    {G : Type u} {ι : Type v} [Group G] [Fintype G] [Fintype ι]
    {A : ι → Type w} [∀ i, AddCommGroup (A i)]
    (ρ : ∀ i, Representation ℤ G (A i)) (g : G)
    (hg : ∀ γ, γ ∈ Subgroup.zpowers g)
    (h : ∀ i, FiniteHerbrand (ρ i) g) :
    herbrandQuotient (Representation.directSum ρ) g =
      ∏ i, herbrandQuotient (ρ i) g := by
  suffices key : ∀ (ι : Type v) [Fintype ι] (A : ι → Type w) [∀ i, AddCommGroup (A i)]
      (ρ : ∀ i, Representation ℤ G (A i)), (∀ i, FiniteHerbrand (ρ i) g) →
        herbrandQuotient (Representation.directSum ρ) g = ∏ i, herbrandQuotient (ρ i) g from
    key ι A ρ h
  intro ι _
  refine Fintype.induction_empty_option (P := fun ι [Fintype ι] => ∀ (A : ι → Type w)
      [∀ i, AddCommGroup (A i)] (ρ : ∀ i, Representation ℤ G (A i)),
      (∀ i, FiniteHerbrand (ρ i) g) →
        herbrandQuotient (Representation.directSum ρ) g = ∏ i, herbrandQuotient (ρ i) g)
    ?_ ?_ ?_ ι
  · intro α β _ e hα A _ ρ h
    letI : Fintype α := Fintype.ofEquiv β e.symm
    exact (herbrandQuotient_congr g _ _
        (DirectSum.lequivCongrLeft (R := ℤ) (M := A) e.symm).toAddEquiv
        (directSum_reindex_equivariant ρ e.symm)).trans
      ((hα (fun a => A (e.symm.symm a)) (fun a => ρ (e.symm.symm a)) (fun a => h _)).trans
        (Fintype.prod_equiv e _ _ (fun _ => rfl)))
  · intro A _ ρ _
    haveI : Unique (⨁ i : PEmpty, A i) := DFinsupp.uniqueOfIsEmpty
    exact (herbrandQuotient_eq_one_of_finite _ g).trans (Fintype.prod_empty _).symm
  · intro α _ hα A _ ρ h
    calc herbrandQuotient (Representation.directSum ρ) g
        = herbrandQuotient ((ρ none).prod (Representation.directSum fun i => ρ (some i))) g :=
          herbrandQuotient_congr g _ _
            (DirectSum.lequivProdDirectSum (R := ℤ) (α := A)).toAddEquiv
            (directSum_option_equivariant ρ)
      _ = herbrandQuotient (ρ none) g *
            herbrandQuotient (Representation.directSum fun i => ρ (some i)) g :=
          herbrandQuotient_prod _ _ g hg (h none)
            (finiteHerbrand_directSum (fun i => ρ (some i)) g (fun i => h (some i)))
      _ = herbrandQuotient (ρ none) g * ∏ i, herbrandQuotient (ρ (some i)) g := by
          rw [hα (fun i => A (some i)) (fun i => ρ (some i)) (fun i => h (some i))]
      _ = ∏ i, herbrandQuotient (ρ i) g :=
          (Fintype.prod_option fun i => herbrandQuotient (ρ i) g).symm

end Cox.CyclicCohomology
