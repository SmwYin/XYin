/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldPrincipalCokernel

/-! # The actual principal S-ideal image in Janusz V.2.2

The image is the intersection of supported and principal ideals. Its quotient
in the supported ideals is finite by restriction of the ideal class map.
This differs from the erased principal image used in V.4.2.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The actual principal-ideal map from S-units to supported ideals. -/
def sUnitPrincipalLinearMap (m : Ideal (𝓞 K)) :
    sUnitSubmodule K L m →ₗ[ℤ] supportedIdealSubmodule K L m :=
  ((((toPrincipalIdeal (𝓞 L) L).comp (sUnitsAtModulus K L m).subtype).codRestrict
    (modulusSupportedIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L))))
    (fun x => x.property)).toAdditive).toIntLinearMap

-- `[NumberField K]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- A global unit has trivial principal ideal, hence belongs to every S-unit group. -/
theorem globalUnitSubmodule_le_sUnitSubmodule (m : Ideal (𝓞 K)) :
    globalUnitSubmodule L ≤ sUnitSubmodule K L m := by
  intro x hx
  change toPrincipalIdeal (𝓞 L) L (Additive.toMul x) ∈
    modulusSupportedIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))
  rw [show toPrincipalIdeal (𝓞 L) L (Additive.toMul x) = 1 from hx]
  exact Subgroup.one_mem _

-- `[NumberField K]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- The first kernel in V.2.2 is the genuine global-unit kernel, restricted to S-units. -/
theorem sUnitPrincipalLinearMap_ker (m : Ideal (𝓞 K)) :
    LinearMap.ker (sUnitPrincipalLinearMap K L m) =
      (globalUnitSubmodule L).comap (sUnitSubmodule K L m).subtype := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap, ← Submodule.coe_eq_zero, ← toMul_eq_one]
  exact Iff.rfl

-- `[NumberField K]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- The principal S-ideal image is precisely the supported part of the principal range. -/
theorem sUnitPrincipalLinearMap_range (m : Ideal (𝓞 K)) :
    LinearMap.range (sUnitPrincipalLinearMap K L m) =
      (((toPrincipalIdeal (𝓞 L) L).range).subgroupOf
        (modulusSupportedIdeals L
          (m.map (algebraMap (𝓞 K) (𝓞 L))))).toAddSubgroup.toIntSubmodule := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Additive.toMul (x : Additive Lˣ), rfl⟩
  · rintro ⟨u, hu⟩
    have hmem : u ∈ sUnitsAtModulus K L m := by
      change toPrincipalIdeal (𝓞 L) L u ∈
        modulusSupportedIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))
      rw [hu]
      exact y.2
    exact ⟨⟨Additive.ofMul u, hmem⟩, Subtype.ext (congrArg Additive.ofMul hu)⟩

/-- The quotient by principal supported ideals embeds in the finite ideal class group. -/
theorem sUnitPrincipalLinearMap_cokernel_finite (m : Ideal (𝓞 K)) :
    Finite ((supportedIdealSubmodule K L m) ⧸ LinearMap.range (sUnitPrincipalLinearMap K L m)) := by
  rw [sUnitPrincipalLinearMap_range]
  haveI := principalIdeal_range_finiteIndex L
  exact Finite.of_equiv _ (Additive.ofMul.trans (Cox.CyclicCohomology.additiveIntQuotientEquiv
    ((toPrincipalIdeal (𝓞 L) L).range.subgroupOf
      (modulusSupportedIdeals L (m.map (algebraMap (𝓞 K) (𝓞 L)))))).symm.toEquiv)

end Cox.ClassFieldTheory
