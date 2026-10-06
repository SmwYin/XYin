/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArithmetic

/-! # The actual paired groups in Janusz V.9

These existing definitions and the actual power/principal/supported factorization
are shared by the existence construction and its later norm calculation.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The congruence group `H_j` of Janusz V.9, with the opposite finite support. -/
def pairedSubgroup (n : ℕ) (m : Ideal (𝓞 K))
    (T : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (coprimeIdeals K m) :=
  raySubgroup K m ⊔ (powMonoidHom n : coprimeIdeals K m →* coprimeIdeals K m).range ⊔
    (supportedIdeals K T).comap (coprimeIdeals K m).subtype

/-- The radical group `W_j = K^S K^n ∩ K_(m_k,1)`, using the opposite modulus. -/
def pairedRadicands (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (mOpposite : Ideal (𝓞 K)) : Subgroup Kˣ :=
  (sUnits K S ⊔ nthPowers K n) ⊓ rayElements K mOpposite

variable (F : Type*) [Field F] [hNF_F : NumberField F]

include hNF_F in
/-- The source paired subgroup has a literal power/principal/supported factorization. -/
theorem pairedSubgroup_mem_factorization (q : ℕ) (m : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (X : coprimeIdeals F m) (hX : X ∈ pairedSubgroup F q m S) :
    ∃ (B : coprimeIdeals F m) (u : Fˣ) (C : (FractionalIdeal (𝓞 F)⁰ F)ˣ),
      u ∈ rayElements F m ∧ C ∈ supportedIdeals F S ∧
      (X : (FractionalIdeal (𝓞 F)⁰ F)ˣ) =
        (B : (FractionalIdeal (𝓞 F)⁰ F)ˣ) ^ q * toPrincipalIdeal (𝓞 F) F u * C := by
  obtain ⟨rp, hrp, s, hs, rfl⟩ := Subgroup.mem_sup.mp hX
  obtain ⟨r, hr, p, hp, rfl⟩ := Subgroup.mem_sup.mp hrp
  obtain ⟨B, rfl⟩ := hp
  obtain ⟨u, hu, hur⟩ := exists_rayElement_of_mem_closure F m hr
  refine ⟨B, u, (s : (FractionalIdeal (𝓞 F)⁰ F)ˣ), hu, hs, ?_⟩
  have hur' : toPrincipalIdeal (𝓞 F) F u = (r : (FractionalIdeal (𝓞 F)⁰ F)ˣ) := hur
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hur', powMonoidHom_apply, SubgroupClass.coe_pow,
    mul_comm (r : (FractionalIdeal (𝓞 F)⁰ F)ˣ)]

end Cox.ClassFieldTheory
