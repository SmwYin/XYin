/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicAutomorphisms
import XYin.PhD.Cox.Theorem11_1.ChebotarevCyclotomicFrobenius

/-!
# Identify the actual cyclotomic Frobenius

Janusz V.5.4, printed161/PDF172, identifies Frobenius by its norm-power action on the chosen
primitive root. These adapters reuse the existing Chebotarev Frobenius contract. Unramifiedness in
the cyclotomic field remains an explicit premise.
-/

namespace Cox.ClassFieldTheory.CyclotomicFrobenius

open NumberField IntermediateField Polynomial Cox.Chebotarev
open CyclotomicBaseChange CyclotomicIntersection CyclotomicAutomorphisms

/-- A primitive root has the same power at a residue-unit representative
and its original exponent. -/
theorem primitiveRoot_pow_unitOfCoprime {M : Type*} [CommMonoid M]
    (n a : ℕ) (ζ : M) (hζ : IsPrimitiveRoot ζ n) (hcop : a.Coprime n) :
    ζ ^ (ZMod.unitOfCoprime a hcop).val.val = ζ ^ a := by
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, hζ.eq_orderOf, pow_mod_orderOf]

/-- The actual Frobenius representative acts on a primitive root by the norm power. -/
theorem frobeniusClass_out_apply_primitiveRoot
    (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsGalois K E]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K E]
    (ζ : E) (hζ : IsPrimitiveRoot ζ m)
    (p : Ideal (𝓞 K)) [p.IsPrime] (hunr : UnramifiedIn K E p)
    (hcop : p.absNorm.Coprime m) :
    (frobeniusClass K E p).out ζ = ζ ^ p.absNorm := by
  have h := Cox.Chebotarev.autToPow_frobeniusClass_out K E m hζ p hunr hcop
  rw [← hζ.autToPow_spec K (frobeniusClass K E p).out, h,
    primitiveRoot_pow_unitOfCoprime m _ ζ hζ hcop]

/-- The full cyclotomic equivalence identifies the actual Frobenius residue. -/
theorem autEquivPow_frobeniusClass_out
    (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsGalois K E]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K E]
    (hirr : Irreducible (cyclotomic m K))
    (p : Ideal (𝓞 K)) [p.IsPrime] (hunr : UnramifiedIn K E p)
    (hcop : p.absNorm.Coprime m) :
    IsCyclotomicExtension.autEquivPow E hirr (frobeniusClass K E p).out =
      ZMod.unitOfCoprime p.absNorm hcop := by
  rw [IsCyclotomicExtension.autEquivPow_apply]
  exact Cox.Chebotarev.autToPow_frobeniusClass_out K E m (IsCyclotomicExtension.zeta_spec m K E)
    p hunr hcop

/-- The chosen embedded root field has the same actual Frobenius residue identity. -/
theorem residueEquiv_frobeniusClass_out
    {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (m : ℕ) (hm : 0 < m) (ξ : Ω) (hξ : IsPrimitiveRoot ξ m)
    [NumberField (adjoin K {ξ})] [IsGalois K (adjoin K {ξ})]
    (hirr : Irreducible (cyclotomic m K))
    (p : Ideal (𝓞 K)) [p.IsPrime]
    (hunr : UnramifiedIn K (adjoin K {ξ}) p) (hcop : p.absNorm.Coprime m) :
    residueEquiv m hm ξ hξ hirr (frobeniusClass K (adjoin K {ξ}) p).out =
      ZMod.unitOfCoprime p.absNorm hcop := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI := rootField_isCyclotomic m hm ξ hξ (F := K)
  exact autEquivPow_frobeniusClass_out K (adjoin K {ξ}) m hirr p hunr hcop

end Cox.ClassFieldTheory.CyclotomicFrobenius
