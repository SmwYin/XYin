/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldHenselMonicFactor
import Mathlib.FieldTheory.Separable

/-! # Hensel factor lifting and the local degree comparison

Source: Janusz II.3.5 and V.9.3.
-/

noncomputable section
open Polynomial IsLocalRing
namespace Cox.ClassFieldTheory

attribute [local instance] Ideal.Quotient.field

/-- A monic irreducible polynomial with separable reduction remains irreducible after reduction. -/
theorem irreducible_map_of_separable_of_adicComplete
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [I.IsPrime]
    [IsAdicComplete I R] (f : R[X]) (hf : f.Monic) (hirr : Irreducible f)
    (hsep : (f.map (Ideal.Quotient.mk I)).Separable) :
    Irreducible (f.map (Ideal.Quotient.mk I)) := by
  have hm := hf.map (Ideal.Quotient.mk I)
  have hne : f.map (Ideal.Quotient.mk I) ≠ 1 := by
    intro h
    have hd : f.natDegree = 0 := by
      rw [← hf.natDegree_map (Ideal.Quotient.mk I), h, natDegree_one]
    exact hirr.ne_one (hf.natDegree_eq_zero.mp hd)
  apply (irreducible_of_monic hm hne).mpr
  intro g h hg hh hprod
  have hs : (g * h).Separable := by simpa only [hprod] using hsep
  have hcop : IsCoprime g h := hs.isCoprime
  obtain ⟨G, H, hG, hH, hfactor, hGmap, hHmap⟩ :=
    exists_monic_factors_of_coprime_map I f hf g h hg hh hprod.symm hcop
  rcases hirr.2 hfactor with hGU | hHU
  · left
    rw [← hGmap, hG.eq_one_of_isUnit hGU, Polynomial.map_one]
  · right
    rw [← hHmap, hH.eq_one_of_isUnit hHU, Polynomial.map_one]

end Cox.ClassFieldTheory
