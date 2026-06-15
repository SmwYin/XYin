/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.Embeddings

/-!
# `ℚ(ζ₅)` RingOfIntegers

Integral basis, ring-of-integers description, and integral-coordinate norm forms.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Ring Of Integers
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicFive

/-- `ζ` is integral over `ℤ` (a root of the monic `X⁵ - 1`), hence lies in `𝓞 K`. -/
theorem zeta_integral : ζ ∈ integralClosure ℤ K :=
  zeta_isPrimitiveRoot.isIntegral (by norm_num)

/-- `ζ` as an element of the ring of integers `𝓞 K`. -/
noncomputable def zetaInt : 𝓞 K := ⟨ζ, zeta_integral⟩

/-- The integral generator also satisfies `ζ⁵ = 1` in `𝓞 K`. -/
theorem zetaInt_pow_five : zetaInt ^ 5 = 1 :=
  Subtype.ext (by push_cast [zetaInt]; exact zeta_pow_five)

/-- The `𝓞 K`-level form of the cyclotomic relation `Φ₅(ζ) = 0`. -/
theorem zetaInt_sum_eq_zero : 1 + zetaInt + zetaInt ^ 2 + zetaInt ^ 3 + zetaInt ^ 4 = 0 :=
  Subtype.ext (by push_cast [zetaInt]; exact zeta_sum_eq_zero)

/-- Mathlib's integral power basis `1, ζ, ζ², ζ³` of the ring of integers. -/
abbrev integralPowerBasis : PowerBasis ℤ (𝓞 K) :=
  zeta_isPrimitiveRoot.integralPowerBasis

/-- The integral power-basis generator is the chosen primitive root of unity in `𝓞 K`. -/
theorem integralPowerBasis_gen : integralPowerBasis.gen = zeta_isPrimitiveRoot.toInteger := by
  simp [integralPowerBasis]

theorem integralPowerBasis_dim : integralPowerBasis.dim = 4 :=
  zeta_isPrimitiveRoot.integralPowerBasis_dim.trans rfl

/-- The displayed integral-basis vectors `1, ζ, ζ², ζ³` (as elements of `K`). -/
def integralBasisVectors : Fin 4 → K := ![1, ζ, ζ ^ 2, ζ ^ 3]

/-- `1, ζ, ζ², ζ³` is an integral basis of `ℚ(ζ₅)`: their `ℤ`-span in `K` is exactly the
ring of integers `𝓞 K`. -/
theorem span_integralBasisVectors_eq :
    Submodule.span ℤ (Set.range integralBasisVectors) =
      Subalgebra.toSubmodule (integralClosure ℤ K) := by
  set q : Polynomial ℤ := Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 +
    Polynomial.X + Polynomial.C 1 with hq
  have hmonic : q.Monic := by
    rw [hq]
    monicity!
  have hdeg4 : q.degree = 4 := by
    rw [hq]
    compute_degree!
  have haq : Polynomial.aeval ζ q = 0 := by
    rw [hq]
    simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
    linear_combination zeta_sum_eq_zero
  refine le_antisymm (Submodule.span_le.mpr ?_) (fun x hx => ?_)
  · rintro y ⟨i, rfl⟩
    fin_cases i
    · exact Subalgebra.one_mem _
    · exact zeta_integral
    · exact Subalgebra.pow_mem _ zeta_integral 2
    · exact Subalgebra.pow_mem _ zeta_integral 3
  · have hx' : x ∈ Algebra.adjoin ℤ ({ζ} : Set K) := by
      obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (self :=
        IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton zeta_isPrimitiveRoot)).mp hx
      exact hy ▸ y.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
    obtain ⟨p, hp⟩ := hx'
    have hkey : x = Polynomial.aeval ζ (p %ₘ q) := by
      conv_lhs => rw [← hp, ← Polynomial.modByMonic_add_div p q]
      rw [map_add, map_mul, show (Polynomial.aeval ζ).toRingHom q = 0 from haq, zero_mul,
        add_zero]; rfl
    have hdeg : (p %ₘ q).natDegree < 4 := by
      rcases eq_or_ne (p %ₘ q) 0 with h0 | h0
      · rw [h0]
        norm_num
      · refine (Polynomial.natDegree_lt_iff_degree_lt h0).mpr ?_
        have h := Polynomial.degree_modByMonic_lt p hmonic
        rwa [hdeg4] at h
    rw [hkey, Polynomial.aeval_eq_sum_range' hdeg]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    interval_cases i
    · exact ⟨0, by simp [integralBasisVectors]⟩
    · exact ⟨1, by simp [integralBasisVectors]⟩
    · exact ⟨2, by simp [integralBasisVectors]⟩
    · exact ⟨3, by simp [integralBasisVectors]⟩

/-- The integral basis `1, ζ, ζ², ζ³` packaged as a genuine `ℤ`-basis of `𝓞 K`. -/
noncomputable def concreteIntegralBasis : Basis (Fin 4) ℤ (𝓞 K) :=
  integralPowerBasis.basis.reindex (finCongr integralPowerBasis_dim)

/-- The packaged integral basis is, vector by vector, the displayed family `1, ζ, ζ², ζ³`. -/
theorem concreteIntegralBasis_apply (i : Fin 4) :
    (algebraMap (𝓞 K) K) (concreteIntegralBasis i) = integralBasisVectors i := by
  fin_cases i <;>
    simp [concreteIntegralBasis, integralBasisVectors, IsPrimitiveRoot.toInteger]

/-- The displayed integral basis spans the same `ℤ`-lattice in `K` as mathlib's
`NumberField.integralBasis K` (the correct form of "the two integral bases agree": equality
of lattices, not a mere reindexing). -/
theorem span_integralBasisVectors_eq_integralBasis :
    Submodule.span ℤ (Set.range integralBasisVectors) =
      Submodule.span ℤ (Set.range (NumberField.integralBasis K)) := by
  rw [span_integralBasisVectors_eq]
  ext x
  rw [Subalgebra.mem_toSubmodule]
  constructor
  · intro hx
    exact (NumberField.mem_span_integralBasis K).mpr (RingHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)
  · intro hx
    obtain ⟨y, hy⟩ := RingHom.mem_range.mp ((NumberField.mem_span_integralBasis K).mp hx)
    exact hy ▸ y.2

/-- The concrete order `ℤ[ζ]` inside `K`. -/
abbrev concreteRingOfIntegers : Subalgebra ℤ K := Algebra.adjoin ℤ ({ζ} : Set K)

/-- The order `ℤ[ζ]` is the full ring of integers of `ℚ(ζ₅)`. -/
theorem isIntegralClosure_adjoin_zeta :
    IsIntegralClosure (Algebra.adjoin ℤ ({ζ} : Set K)) ℤ K :=
  IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton zeta_isPrimitiveRoot

/-- The integral power-basis generator generates `𝓞 K` over `ℤ`. -/
theorem integralPowerBasis_adjoin_gen_eq_top :
    Algebra.adjoin ℤ ({integralPowerBasis.gen} : Set (𝓞 K)) = ⊤ :=
  integralPowerBasis.adjoin_gen_eq_top

/-- The full ring of integers of `ℚ(ζ₅)` is `ℤ[ζ]`: cyclotomic fields are monogenic. -/
theorem ringOfIntegers_eq : integralClosure ℤ K = concreteRingOfIntegers := by
  refine le_antisymm (fun x hx => ?_)
    (Algebra.adjoin_le (Set.singleton_subset_iff.mpr zeta_integral))
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (self :=
    isIntegralClosure_adjoin_zeta)).mp hx
  exact hy ▸ y.2


end NumberField.CyclotomicFive
