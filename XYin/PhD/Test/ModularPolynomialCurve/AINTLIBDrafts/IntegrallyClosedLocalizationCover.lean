/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Integral closedness from a basic-open cover

A domain is integrally closed if each nonzero member of a spanning set
has an integrally closed away localization. Zero members of the cover impose
no condition. Embed the actual localizations in the original fraction field,
clear denominators locally and use unit-span submodule membership to descend.

No finiteness, Noetherian, smoothness or field-base assumption is needed.
The examples check actual localization of a normal domain and the unit cover.
-/

@[expose] public section

open scoped nonZeroDivisors

universe u

namespace IsIntegrallyClosed

variable (R : Type u) [CommRing R] [IsDomain R]

theorem of_localizationAway_span (s : Set R) (hs : Ideal.span s = ⊤)
    (h : ∀ a ∈ s, a ≠ 0 → IsIntegrallyClosed (Localization.Away a)) :
    IsIntegrallyClosed R := by
  let K := FractionRing R
  refine (isIntegrallyClosed_iff K).mpr fun {x} hx ↦ ?_
  let M := (Algebra.linearMap R K).range
  have hm : x ∈ M := by
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem M s hs x
    intro a
    by_cases ha : (a : R) = 0
    · exact ⟨1, by simp [ha]⟩
    have hS : Submonoid.powers (a : R) ≤ R⁰ :=
      Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
    let S := Localization.subalgebra K (Submonoid.powers (a : R)) hS
    have : IsIntegrallyClosed S :=
      (h a a.property ha).of_equiv
        (IsLocalization.algEquiv (Submonoid.powers (a : R))
          (Localization.Away (a : R)) S).toRingEquiv
    obtain ⟨b, hb⟩ := (isIntegrallyClosed_iff K).mp ‹IsIntegrallyClosed S› hx.tower_top
    obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (a : R) b
    refine ⟨n, c, ?_⟩
    have he := congrArg (algebraMap S K) hc
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply R S K,
      ← IsScalarTower.algebraMap_apply R S K, hb] at he
    change algebraMap R K c = (a : R) ^ n • x
    rw [Algebra.smul_def, map_pow, mul_comm]
    exact he.symm
  exact hm

example (s : Set R) (hs : Ideal.span s = ⊤) [IsIntegrallyClosed R] :
    IsIntegrallyClosed R :=
  of_localizationAway_span R s hs fun a _ ha ↦
    isIntegrallyClosed_of_isLocalization (Localization.Away a) (Submonoid.powers a)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr ha))

example (h : IsIntegrallyClosed (Localization.Away (1 : R))) : IsIntegrallyClosed R :=
  of_localizationAway_span R {1} (by simp) fun _ ha _ ↦ by simpa using ha ▸ h

#print axioms of_localizationAway_span
#print axioms IsIntegrallyClosed.of_equiv
#print axioms isIntegrallyClosed_iff
#print axioms Submodule.mem_of_span_eq_top_of_smul_pow_mem
#print axioms IsLocalization.Away.surj
#print axioms IsLocalization.algEquiv
#print axioms Localization.subalgebra
#print axioms isIntegrallyClosed_of_isLocalization

end IsIntegrallyClosed
