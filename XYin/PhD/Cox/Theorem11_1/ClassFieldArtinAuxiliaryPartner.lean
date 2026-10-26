/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicFrobenius

/-!
# The independent cyclotomic Frobenius partner

Janusz V.5.4, printed161/PDF172, chooses the second automorphism through its power on the root. The
order and independence clauses share that one witness. The separate order bound on Frobenius belongs
to the later assembly.
-/

open NumberField Polynomial Cox.Chebotarev
noncomputable section
namespace Cox.ClassFieldTheory.ArtinAuxiliary

/-- Janusz V.5.4: transport the independent residue unit to one Frobenius partner. -/
theorem independent_frobenius_partner
    (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsGalois K E] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K E] (hirr : Irreducible (cyclotomic m K))
    (q : Ideal (𝓞 K)) [q.IsPrime] (hU : UnramifiedIn K E q)
    (hcop : q.absNorm.Coprime m) (n : ℕ) (u v : (ZMod m)ˣ)
    (hu : (u : ZMod m) = q.absNorm) (hnv : n ∣ orderOf v)
    (hind : Disjoint (Subgroup.zpowers u) (Subgroup.zpowers v)) :
    ∃ τ : Gal(E/K), n ∣ orderOf τ ∧
      Disjoint (Subgroup.zpowers τ) (Subgroup.zpowers (frobeniusClass K E q).out) := by
  set e := IsCyclotomicExtension.autEquivPow E hirr
  have hu' : u = ZMod.unitOfCoprime q.absNorm hcop :=
    Units.ext (by rw [hu, ZMod.coe_unitOfCoprime])
  have hfrob : (frobeniusClass K E q).out = e.symm u := by
    rw [hu', ← CyclotomicFrobenius.autEquivPow_frobeniusClass_out K E m hirr q hU hcop,
      MulEquiv.symm_apply_apply]
  refine ⟨e.symm v, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hnv
  · rw [hfrob]
    exact ResidueIndependence.disjoint_zpowers_pullback e v u hind.symm

end Cox.ClassFieldTheory.ArtinAuxiliary
