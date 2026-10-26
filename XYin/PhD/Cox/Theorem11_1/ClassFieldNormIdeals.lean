/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormCongruence
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-! # Good relative ideal norms

Janusz III.3.1 uses the norm map on ideals avoiding the modulus. The domain
and representative adapters are explicit here. All theorem bodies are sorries.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory

/-- A good upstairs ideal has good relative norm. -/
theorem relNorm_coprime
    (K : Type*) [Field K] [NumberField K] (E : Type*) [Field E] [NumberField E]
    [Algebra K E]
    [Module.Finite (𝓞 K) (𝓞 E)] (m : Ideal (𝓞 K)) (A : Ideal (𝓞 E))
    (hA : A ⊔ m.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤) :
    Ideal.relNorm (𝓞 K) A ⊔ m = ⊤ := by
  have h1 : (1 : 𝓞 E) ∈ A ⊔ m.map (algebraMap (𝓞 K) (𝓞 E)) := by
    rw [hA]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  have hb' : a - 1 ∈ m.map (algebraMap (𝓞 K) (𝓞 E)) := by
    have h : a - 1 = -b := by rw [← hab]; ring
    rw [h]
    exact neg_mem hb
  have hN := intNorm_sub_one_mem K E m a hb'
  have hNA : Algebra.intNorm (𝓞 K) (𝓞 E) a ∈ Ideal.relNorm (𝓞 K) A := by
    rw [Ideal.relNorm_apply]
    exact Ideal.intNorm_mem_spanNorm (𝓞 K) ha
  rw [Ideal.eq_top_iff_one]
  have h : (1 : 𝓞 K) =
      Algebra.intNorm (𝓞 K) (𝓞 E) a - (Algebra.intNorm (𝓞 K) (𝓞 E) a - 1) := by ring
  rw [h]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left hNA) (Ideal.mem_sup_right hN)

/-- Contraction of an ideal avoiding the extended modulus avoids the base modulus. -/
theorem under_coprime
    (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    [Module.Finite (𝓞 K) (𝓞 E)] (m : Ideal (𝓞 K)) (A : Ideal (𝓞 E))
    (hA : A ⊔ m.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤) :
    A.under (𝓞 K) ⊔ m = ⊤ := by
  have h := relNorm_coprime K E m A hA
  rw [eq_top_iff] at h ⊢
  exact h.trans (sup_le_sup_right (Ideal.relNorm_le_comap (𝓞 K) A) m)

/-- A nonzero good ideal norm has its actual representative in the good-ideal group. -/
theorem exists_coprime_relNorm_unit
    (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    [Module.Finite (𝓞 K) (𝓞 E)] (m : Ideal (𝓞 K)) (A : Ideal (𝓞 E))
    (hA : A ≠ ⊥) (hAm : A ⊔ m.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤) :
    ∃ u : coprimeIdeals K m,
      ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        (Ideal.relNorm (𝓞 K) A : FractionalIdeal (𝓞 K)⁰ K) := by
  have hN0 : Ideal.relNorm (𝓞 K) A ≠ ⊥ := fun h => hA (Ideal.relNorm_eq_bot_iff.mp h)
  exact exists_coprimeIdealUnit K m _ hN0 (relNorm_coprime K E m A hAm)

end Cox.ClassFieldTheory
