import XYin.PhD.Test.MMeromorphic.LocalFractionChecks
import XYin.PhD.Test.MMeromorphic.RiemannSurface
import XYin.PhD.Test.MMeromorphic.ChartsChecks
import XYin.PhD.Test.MMeromorphic.ModularFieldChecks
import XYin.PhD.Test.MMeromorphic.ModularSlashChecks
import XYin.PhD.Test.MMeromorphic.SheafChecks
import XYin.PhD.Test.MMeromorphic.SheafLocalBridge
import XYin.PhD.Test.MMeromorphic.SheafGlobalBridge
import XYin.PhD.Test.MMeromorphic.SheafOpenBridge
import XYin.PhD.Test.MMeromorphic.SheafOpenField
import XYin.PhD.Test.MMeromorphic.SheafQuotientBridge
import XYin.PhD.Test.MMeromorphic.SheafEquivalence

/-!
# Cross-checks between the independently defined analytic predicates and field constructions

Every map below takes an analytic proof as input. None defines analytic meromorphy by membership
in a field. The quotient, normal-form, and sheaf constructions are compared globally.
-/

open UpperHalfPlane Set
open scoped Manifold

namespace MMeromorphicTest.IntegrationChecks

noncomputable section

example {f : ℍ → ℂ} :
    LocalFraction.MMeromorphic 𝓘(ℂ) f ↔ MMeromorphicExperiment.Charts.MMeromorphic f :=
  LocalFraction.mmeromorphic_upperHalfPlane_iff.trans
    MMeromorphicExperiment.Charts.mMeromorphic_upperHalfPlane_iff.symm

/-- The broad local analytic fraction condition proves membership in the ambient field. -/
def fractionToAmbient {f : ℍ → ℂ} (hf : LocalFraction.MMeromorphic 𝓘(ℂ) f) :
    Modular.Ambient :=
  Modular.toAmbient (LocalFraction.mmeromorphic_upperHalfPlane_iff.mp hf)

example {f g : ℍ → ℂ} (hf : LocalFraction.MMeromorphic 𝓘(ℂ) f)
    (hg : LocalFraction.MMeromorphic 𝓘(ℂ) g) :
    fractionToAmbient (hf.add hg) = fractionToAmbient hf + fractionToAmbient hg :=
  toGerm_add (LocalFraction.mmeromorphic_upperHalfPlane_iff.mp hf)
    (LocalFraction.mmeromorphic_upperHalfPlane_iff.mp hg)

example {f : ℍ → ℂ} (hf : LocalFraction.MMeromorphic 𝓘(ℂ) f) :
    fractionToAmbient hf.inv_manifold = (fractionToAmbient hf)⁻¹ :=
  toGerm_inv Modular.upperHalfPlaneDomain Modular.upperHalfPlane_preconnected
    (LocalFraction.mmeromorphic_upperHalfPlane_iff.mp hf)

/-- On the complex line the independent fraction predicate has the local sheaf interpretation. -/
theorem fractionAt_iff_localSheafFraction {f : ℂ → ℂ} {x : ℂ} :
    LocalFraction.MMeromorphicAt 𝓘(ℂ) f x ↔
      Nonempty (SheafLocalBridge.LocalSheafFraction f x) :=
  LocalFraction.mmeromorphicAt_iff_meromorphicAt.trans
    SheafLocalBridge.meromorphicAt_iff_localSheafFraction

example {f : ℂ → ℂ} {x : ℂ} (hf : MMeromorphicExperiment.Charts.MMeromorphicAt f x) :
    Nonempty (SheafLocalBridge.LocalSheafFraction f x) :=
  SheafLocalBridge.exists_localSheafFraction
    (MMeromorphicExperiment.Charts.mMeromorphicAt_complex_iff.mp hf)

example {f : ℂ → ℂ} (hf : LocalFraction.MMeromorphic 𝓘(ℂ) f) :
    MeromorphicGerms (univ : Set ℂ) :=
  toGerm (LocalFraction.mmeromorphic_iff_meromorphicOn.mp hf)

/-- A directly proved analytic condition also supplies a global section of the other field. -/
def fractionToGlobalSheaf {f : ℂ → ℂ} (hf : LocalFraction.MMeromorphic 𝓘(ℂ) f) :
    SheafLocalBridge.X.meromorphicGlobalSections :=
  SheafLocalBridge.globalSection (LocalFraction.mmeromorphic_iff_meromorphicOn.mp hf)

def fractionToUpperHalfPlaneSheaf {f : ℍ → ℂ}
    (hf : LocalFraction.MMeromorphic 𝓘(ℂ) f) :
    SheafLocalBridge.X.meromorphicSheaf.presheaf.obj
      (Opposite.op SheafLocalBridge.upperHalfPlaneOpen) :=
  SheafLocalBridge.upperHalfPlaneSection
    (LocalFraction.mmeromorphic_upperHalfPlane_iff.mp hf)

example : Field (SheafLocalBridge.X.meromorphicSheaf.presheaf.obj
    (Opposite.op SheafLocalBridge.upperHalfPlaneOpen)) :=
  SheafOpen.upperHalfPlaneSheafField

/-- The modular analytic condition gives an element of the separately constructed sheaf field. -/
def modularToSheaf {ι : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)}
    {c : ι → Modular.CuspCoordinate} {f : ℍ → ℂ}
    (hf : Modular.IsModularFunction Γ c f) :
    SheafLocalBridge.X.meromorphicSheaf.presheaf.obj
      (Opposite.op SheafLocalBridge.upperHalfPlaneOpen) :=
  SheafLocalBridge.upperHalfPlaneSection hf.meromorphic

/-- The two constructions agree, rather than merely producing unrelated field elements. -/
def upperHalfPlaneComparison : Modular.Ambient ≃+*
    SheafLocalBridge.X.meromorphicSheaf.presheaf.obj
      (Opposite.op SheafLocalBridge.upperHalfPlaneOpen) :=
  SheafLocalBridge.toSheafRingEquivOn SheafLocalBridge.upperHalfPlaneOpen

@[simp] theorem upperHalfPlaneComparison_fraction {f : ℍ → ℂ}
    (hf : LocalFraction.MMeromorphic 𝓘(ℂ) f) :
    upperHalfPlaneComparison (fractionToAmbient hf) = fractionToUpperHalfPlaneSheaf hf :=
  SheafLocalBridge.toSheafRingEquivOn_toGerm
    (U := SheafLocalBridge.upperHalfPlaneOpen) (f := f ∘ UpperHalfPlane.ofComplex)
    (LocalFraction.mmeromorphic_upperHalfPlane_iff.mp hf)

@[simp] theorem upperHalfPlaneComparison_modular {ι : Type*}
    {Γ : Subgroup (GL (Fin 2) ℝ)} {c : ι → Modular.CuspCoordinate} {f : ℍ → ℂ}
    (hf : Modular.IsModularFunction Γ c f) :
    upperHalfPlaneComparison (Modular.toAmbient hf.meromorphic) = modularToSheaf hf :=
  SheafLocalBridge.toSheafRingEquivOn_toGerm
    (U := SheafLocalBridge.upperHalfPlaneOpen) (f := f ∘ UpperHalfPlane.ofComplex)
    hf.meromorphic

/-- The modular subfield can also be realized inside the independently constructed sheaf field. -/
def modularSheafSubfield {ι : Type*} (Γ : Subgroup (GL (Fin 2) ℝ))
    (c : ι → Modular.CuspCoordinate) :
    letI : Field (SheafLocalBridge.X.meromorphicSheaf.presheaf.obj
      (Opposite.op SheafLocalBridge.upperHalfPlaneOpen)) := SheafOpen.upperHalfPlaneSheafField
    Subfield (SheafLocalBridge.X.meromorphicSheaf.presheaf.obj
      (Opposite.op SheafLocalBridge.upperHalfPlaneOpen)) := by
  letI : Field (SheafLocalBridge.X.meromorphicSheaf.presheaf.obj
    (Opposite.op SheafLocalBridge.upperHalfPlaneOpen)) := SheafOpen.upperHalfPlaneSheafField
  exact (Modular.modularSubfield Γ c).map upperHalfPlaneComparison.toRingHom

example {ι : Type*} (Γ : Subgroup (GL (Fin 2) ℝ)) (c : ι → Modular.CuspCoordinate) :
    letI : Field (SheafLocalBridge.X.meromorphicSheaf.presheaf.obj
      (Opposite.op SheafLocalBridge.upperHalfPlaneOpen)) := SheafOpen.upperHalfPlaneSheafField
    Field (modularSheafSubfield Γ c) := by
  letI : Field (SheafLocalBridge.X.meromorphicSheaf.presheaf.obj
    (Opposite.op SheafLocalBridge.upperHalfPlaneOpen)) := SheafOpen.upperHalfPlaneSheafField
  infer_instance

example {f : ℍ → ℂ} (hf : LocalFraction.MMeromorphic 𝓘(ℂ) f) :
    letI : Field (SheafLocalBridge.X.meromorphicSheaf.presheaf.obj
      (Opposite.op SheafLocalBridge.upperHalfPlaneOpen)) := SheafOpen.upperHalfPlaneSheafField
    fractionToUpperHalfPlaneSheaf hf ≠ 0 →
      fractionToUpperHalfPlaneSheaf hf * (fractionToUpperHalfPlaneSheaf hf)⁻¹ = 1 := by
  letI : Field (SheafLocalBridge.X.meromorphicSheaf.presheaf.obj
    (Opposite.op SheafLocalBridge.upperHalfPlaneOpen)) := SheafOpen.upperHalfPlaneSheafField
  exact mul_inv_cancel₀

/-- The comparison already embeds the complex-plane classes field into the sheaf field. -/
theorem sheafMap_injective : Function.Injective SheafLocalBridge.toSheafRingHom := by
  letI : Filter.NeBot (Filter.codiscreteWithin (univ : Set ℂ)) :=
    codiscreteWithin_neBot_of_open univ isOpen_univ ⟨0, mem_univ 0⟩
  letI : Field (MeromorphicGerms (univ : Set ℂ)) :=
    meromorphicGermField univ isPreconnected_univ
  letI : Field SheafLocalBridge.X.meromorphicGlobalSections := Sheaf.complexPlaneField
  exact SheafLocalBridge.toSheafRingHom.injective

#print axioms fractionToAmbient
#print axioms fractionAt_iff_localSheafFraction
#print axioms fractionToGlobalSheaf
#print axioms fractionToUpperHalfPlaneSheaf
#print axioms modularToSheaf
#print axioms upperHalfPlaneComparison
#print axioms modularSheafSubfield
#print axioms sheafMap_injective

end

end MMeromorphicTest.IntegrationChecks
