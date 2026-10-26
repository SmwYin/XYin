/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldTheory
import Mathlib.NumberTheory.RamificationInertia.Ramification

/-! # Equivalence of extension fields

These native transport adapters support Janusz V.5.6, printed162–164,
and the fixed complex model used for Cox8.6. The base field and modulus stay fixed.
-/
open NumberField
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory

/-- Unramified support is invariant under a base-preserving field equivalence.
Native source: `Ideal.ramificationIdx_comap_eq`, Ramification.lean:137–138. -/
theorem isUnramifiedAway_algEquiv
    (K : Type*) [Field K] (m : Ideal (𝓞 K)) (L M : Type*)
    [Field L] [Field M] [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) (hL : IsUnramifiedAway K m L) : IsUnramifiedAway K m M := by
  let eO : 𝓞 L ≃ₐ[𝓞 K] 𝓞 M := RingOfIntegers.mapAlgEquiv e
  intro q hq hq0 hqm P hP
  obtain ⟨hPp, hPo⟩ := hP
  haveI := hPp
  haveI := hPo
  have h := hL q hq hq0 hqm (P.comap eO) ⟨Ideal.IsPrime.comap _, inferInstance⟩
  rwa [Ideal.ramificationIdx_comap_eq] at h

/-- Conjugating automorphisms transports the actual arithmetic Frobenius congruence.
Native source: `RingOfIntegers.mapAlgEquiv`, NumberField/Basic.lean:223–230. -/
theorem isArtinMap_algEquiv
    (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (L M : Type*)
    [Field L] [Field M] [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) (φ : coprimeIdeals K m →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K m L φ) :
    IsArtinMap K m M (e.autCongr.toMonoidHom.comp φ) := by
  let eO : 𝓞 L ≃ₐ[𝓞 K] 𝓞 M := RingOfIntegers.mapAlgEquiv e
  intro q hq hq0 hqm u hu P hP x
  obtain ⟨hPp, hPo⟩ := hP
  haveI := hPp
  haveI := hPo
  have h := hφ q hq hq0 hqm u hu (P.comap eO) ⟨Ideal.IsPrime.comap _, inferInstance⟩ (eO.symm x)
  rw [Ideal.mem_comap, map_sub, map_pow, AlgEquiv.apply_symm_apply] at h
  have hx : RingOfIntegers.mapRingHom ((e.autCongr.toMonoidHom.comp φ) u).toRingHom x =
      eO (RingOfIntegers.mapRingHom (φ u).toRingHom (eO.symm x)) := RingOfIntegers.ext rfl
  rw [hx]
  exact h

/-- One inclusion of norm images along a base-preserving field equivalence. -/
theorem normImage_le_of_algEquiv
    (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (L M : Type*)
    [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] (e : L ≃ₐ[K] M) :
    normImage K m L ≤ normImage K m M := by
  let eO : 𝓞 L ≃ₐ[𝓞 K] 𝓞 M := RingOfIntegers.mapAlgEquiv e
  refine (Subgroup.closure_le _).mpr ?_
  rintro u ⟨A, hA0, hAm, hu⟩
  have hm : (m.map (algebraMap (𝓞 K) (𝓞 L))).map eO = m.map (algebraMap (𝓞 K) (𝓞 M)) := by
    change Ideal.map (eO : 𝓞 L →+* 𝓞 M) (m.map (algebraMap (𝓞 K) (𝓞 L))) = _
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun x => eO.commutes x
  refine Subgroup.subset_closure ⟨A.map eO, ?_, ?_, ?_⟩
  · rwa [Ne, Ideal.map_eq_bot_iff_of_injective eO.injective]
  · have h := congrArg (Ideal.map eO) hAm
    rwa [Ideal.map_sup, Ideal.map_top, hm] at h
  · rw [hu, Ideal.relNorm_map_algEquiv]

/-- The existing norm images are equal in the same prime-to-modulus ideal group.
Native source: `Ideal.relNorm_map_algEquiv`, Ideal/Norm/RelNorm.lean:321–328. -/
theorem normImage_algEquiv
    (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (L M : Type*)
    [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] (e : L ≃ₐ[K] M) :
    normImage K m L = normImage K m M := by
  exact le_antisymm (normImage_le_of_algEquiv K m L M e)
    (normImage_le_of_algEquiv K m M L e.symm)

end Cox.ClassFieldTheory
