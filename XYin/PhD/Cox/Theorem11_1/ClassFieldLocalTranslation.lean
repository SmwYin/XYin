/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldExistence
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinTranslation

/-! # The norm-preimage calculation in Janusz V.11.1

The prime calculation is Janusz III.3.1, printed pp. 103–104. Restriction from the compositum
`F = E·L` is injective and carries the Artin symbol of an ideal of `E` to the Artin symbol of
its relative norm, so the Artin kernel over `E` is the norm preimage of the kernel over `K`.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory

variable (K L E F : Type*) [Field K] [hNF_K : NumberField K] [Field L] [hNF_L : NumberField L]
  [Field E] [hNF_E : NumberField E] [Field F] [hNF_F : NumberField F]
  [Algebra K L] [Algebra K E] [Algebra K F] [Algebra L F] [Algebra E F]
  [IsScalarTower K L F] [IsScalarTower K E F]

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
include hNF_K hNF_L hNF_E hNF_F in
/-- Janusz V.11.1: injective restriction converts norm compatibility into the exact kernel. -/
theorem artin_baseChange_ker_eq_normPreimage [IsGalois K L]
    [Module.Finite (𝓞 K) (𝓞 E)] (H : CongruenceSubgroup K)
    (hgen : Algebra.adjoin E (Set.range (algebraMap L F)) = ⊤)
    (φ : coprimeIdeals K H.modulus →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K H.modulus L φ) (hU : IsUnramifiedAway K H.modulus L)
    (hker : φ.ker = H.subgroup)
    (ψ : coprimeIdeals E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E))) →* (F ≃ₐ[E] F))
    (hψ : IsArtinMap E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E))) F ψ) :
    ψ.ker = normPreimage K E H := by
  have hinj := compositum_restriction_injective K L E F hgen
  have hone : AlgEquiv.restrictNormalHom L ((1 : F ≃ₐ[E] F).restrictScalars K) = 1 := by
    have h1 : (1 : F ≃ₐ[E] F).restrictScalars K = 1 := AlgEquiv.ext fun _ => rfl
    rw [h1, map_one]
  ext u
  rw [MonoidHom.mem_ker, mem_normPreimage_iff]
  constructor
  · intro h1
    obtain ⟨A, B, uN, hA, hB, hAm, hBm, hu, hN⟩ := exists_coprime_norm_quotient K E H.modulus u
    have hres := artin_baseChange_quotient_norm K L E F H.modulus φ hφ hU ψ hψ u A B hA hB hAm
      hBm hu uN hN
    rw [h1, hone] at hres
    refine ⟨A, B, hA, hB, hAm, hBm, hu, uN, ?_, hN⟩
    rw [← hker, MonoidHom.mem_ker]
    exact hres.symm
  · rintro ⟨A, B, hA, hB, hAm, hBm, hu, v, hv, hvn⟩
    have hres := artin_baseChange_quotient_norm K L E F H.modulus φ hφ hU ψ hψ u A B hA hB hAm
      hBm hu v hvn
    rw [← hker, MonoidHom.mem_ker] at hv
    apply hinj
    change AlgEquiv.restrictNormalHom L ((ψ u).restrictScalars K) =
      AlgEquiv.restrictNormalHom L ((1 : F ≃ₐ[E] F).restrictScalars K)
    rw [hres, hv, hone]

end Cox.ClassFieldTheory
