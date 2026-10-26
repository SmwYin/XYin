/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealTate
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormCongruence

/-! # Relative norms preserve finite ray subgroups

Janusz V.5.6, printed163, takes the norm of the same ray-principal factor.
This is the finite-modulus statement; the norm is the existing prime-product map.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory

/-- Janusz V.5.6, p163: the actual relative ideal norm preserves the finite ray condition. -/
theorem raySubgroup_map_awayIdealNorm_le
    (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] (m : Ideal (𝓞 K)) :
    (raySubgroup E (m.map (algebraMap (𝓞 K) (𝓞 E)))).map (awayIdealNorm K E m) ≤
      raySubgroup K m := by
  haveI : Module.Finite (𝓞 K) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 E)
  have hgen : Subgroup.closure (rayGenerators E (m.map (algebraMap (𝓞 K) (𝓞 E)))) ≤
      (Subgroup.closure (rayGenerators K m)).comap (idealUnitNorm K E) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨a, ha0, ha1, hu⟩
    refine Subgroup.subset_closure
      ⟨Algebra.intNorm (𝓞 K) (𝓞 E) a, ?_, intNorm_sub_one_mem K E m a ha1, ?_⟩
    · exact fun h => ha0 (Algebra.intNorm_eq_zero.mp h)
    · have hI : (u : FractionalIdeal (𝓞 E)⁰ E) = (Ideal.span {a} : Ideal (𝓞 E)) := by
        rw [hu, FractionalIdeal.coeIdeal_span_singleton]
      rw [idealUnitNorm_integral K E u _ hI, Ideal.relNorm_singleton,
        FractionalIdeal.coeIdeal_span_singleton]
  rintro _ ⟨X, hX, rfl⟩
  exact hgen hX

end Cox.ClassFieldTheory
