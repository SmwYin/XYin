import XYin.PhD.Test.MMeromorphic.UpperHalfPlane
import XYin.PhD.Test.MMeromorphic.Field
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Algebra.Field.Subfield.Basic

/-!
# A modular-function field test with a direct analytic condition

The raw predicate consists of meromorphy on `ℍ`, weight-zero invariance, and meromorphy
in each supplied cusp coordinate. The quotient field is constructed afterwards.
The family of cusp coordinates is explicit input; this file does not identify the cusps of Γ.
-/

open Filter Set UpperHalfPlane
open scoped Topology MatrixGroups

namespace MMeromorphicTest.Modular

noncomputable section

/-- Fixed scaling matrix and positive width for a cusp coordinate. -/
structure CuspCoordinate where
  scaling : GL (Fin 2) ℝ
  scaling_pos : 0 < scaling.det.val
  width : ℝ
  width_pos : 0 < width

/-- A direct condition expressing a meromorphic q-germ at a fixed cusp. -/
def MeromorphicAtCusp (c : CuspCoordinate) (f : ℍ → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, MeromorphicAt F 0 ∧
    (fun τ : ℍ ↦ f (c.scaling • τ)) =ᶠ[atImInfty]
      (fun τ : ℍ ↦ F (Function.Periodic.qParam c.width (τ : ℂ)))

namespace MeromorphicAtCusp

variable {c : CuspCoordinate} {f g : ℍ → ℂ}

theorem const (c : CuspCoordinate) (a : ℂ) : MeromorphicAtCusp c (fun _ ↦ a) :=
  ⟨fun _ ↦ a, MeromorphicAt.const a 0, EventuallyEq.rfl⟩

theorem add (hf : MeromorphicAtCusp c f) (hg : MeromorphicAtCusp c g) :
    MeromorphicAtCusp c (f + g) := by
  obtain ⟨F, hF, hf⟩ := hf
  obtain ⟨G, hG, hg⟩ := hg
  exact ⟨F + G, hF.add hG, hf.add hg⟩

theorem neg (hf : MeromorphicAtCusp c f) : MeromorphicAtCusp c (-f) := by
  obtain ⟨F, hF, hf⟩ := hf
  exact ⟨-F, hF.neg, hf.neg⟩

theorem mul (hf : MeromorphicAtCusp c f) (hg : MeromorphicAtCusp c g) :
    MeromorphicAtCusp c (f * g) := by
  obtain ⟨F, hF, hf⟩ := hf
  obtain ⟨G, hG, hg⟩ := hg
  exact ⟨F * G, hF.mul hG, hf.mul hg⟩

theorem inv (hf : MeromorphicAtCusp c f) : MeromorphicAtCusp c f⁻¹ := by
  obtain ⟨F, hF, hf⟩ := hf
  exact ⟨F⁻¹, hF.inv, hf.inv⟩

end MeromorphicAtCusp

variable {ι : Type*} (Γ : Subgroup (GL (Fin 2) ℝ)) (c : ι → CuspCoordinate)

/-- The analytic and modular conditions are predicates on the original raw function. -/
structure IsModularFunction (f : ℍ → ℂ) : Prop where
  meromorphic : UHP.Meromorphic f
  invariant : ∀ γ ∈ Γ, ∀ τ : ℍ, f (γ • τ) = f τ
  at_cusps : ∀ i, MeromorphicAtCusp (c i) f

namespace IsModularFunction

variable {Γ c} {f g : ℍ → ℂ}

theorem const (a : ℂ) : IsModularFunction Γ c (fun _ ↦ a) :=
  ⟨UHP.const a, fun _ _ _ ↦ rfl, fun i ↦ MeromorphicAtCusp.const (c i) a⟩

theorem add (hf : IsModularFunction Γ c f) (hg : IsModularFunction Γ c g) :
    IsModularFunction Γ c (f + g) :=
  ⟨UHP.add hf.meromorphic hg.meromorphic,
    fun γ hγ τ ↦ by simp only [Pi.add_apply, hf.invariant γ hγ τ, hg.invariant γ hγ τ],
    fun i ↦ (hf.at_cusps i).add (hg.at_cusps i)⟩

theorem neg (hf : IsModularFunction Γ c f) : IsModularFunction Γ c (-f) :=
  ⟨UHP.neg hf.meromorphic,
    fun γ hγ τ ↦ by simp only [Pi.neg_apply, hf.invariant γ hγ τ],
    fun i ↦ (hf.at_cusps i).neg⟩

theorem mul (hf : IsModularFunction Γ c f) (hg : IsModularFunction Γ c g) :
    IsModularFunction Γ c (f * g) :=
  ⟨UHP.mul hf.meromorphic hg.meromorphic,
    fun γ hγ τ ↦ by simp only [Pi.mul_apply, hf.invariant γ hγ τ, hg.invariant γ hγ τ],
    fun i ↦ (hf.at_cusps i).mul (hg.at_cusps i)⟩

theorem inv (hf : IsModularFunction Γ c f) : IsModularFunction Γ c f⁻¹ :=
  ⟨UHP.inv hf.meromorphic,
    fun γ hγ τ ↦ by simp only [Pi.inv_apply, hf.invariant γ hγ τ],
    fun i ↦ (hf.at_cusps i).inv⟩

end IsModularFunction

abbrev upperHalfPlaneDomain : Set ℂ := {z | 0 < z.im}

instance upperHalfPlane_codiscrete_neBot : NeBot (codiscreteWithin upperHalfPlaneDomain) :=
  codiscreteWithin_neBot_of_open upperHalfPlaneDomain isOpen_upperHalfPlaneSet
    ⟨Complex.I, by simp⟩

theorem upperHalfPlane_preconnected : IsPreconnected upperHalfPlaneDomain :=
  (Complex.isConnected_of_upperHalfPlane subset_rfl (by grind)).isPreconnected

/-- The independently constructed ambient field of meromorphic classes. -/
abbrev Ambient := MeromorphicGerms upperHalfPlaneDomain

noncomputable instance : Field Ambient :=
  meromorphicGermField upperHalfPlaneDomain upperHalfPlane_preconnected

/-- The predicate proves that the raw function determines an element of the ambient field. -/
def toAmbient {f : ℍ → ℂ} (hf : UHP.Meromorphic f) : Ambient := toGerm hf

@[simp] theorem toAmbient_add {f g : ℍ → ℂ}
    (hf : UHP.Meromorphic f) (hg : UHP.Meromorphic g) :
    toAmbient (UHP.add hf hg) = toAmbient hf + toAmbient hg := toGerm_add hf hg

@[simp] theorem toAmbient_mul {f g : ℍ → ℂ}
    (hf : UHP.Meromorphic f) (hg : UHP.Meromorphic g) :
    toAmbient (UHP.mul hf hg) = toAmbient hf * toAmbient hg := toGerm_mul hf hg

@[simp] theorem toAmbient_neg {f : ℍ → ℂ} (hf : UHP.Meromorphic f) :
    toAmbient (UHP.neg hf) = -toAmbient hf := Subtype.ext (Germ.coe_neg _)

@[simp] theorem toAmbient_inv {f : ℍ → ℂ} (hf : UHP.Meromorphic f) :
    toAmbient (UHP.inv hf) = (toAmbient hf)⁻¹ :=
  toGerm_inv upperHalfPlaneDomain upperHalfPlane_preconnected hf

/-- Modular classes form a subfield, with all analytic conditions imposed on representatives. -/
def modularSubfield : Subfield Ambient where
  carrier := {a | ∃ f : ℍ → ℂ, ∃ hf : IsModularFunction Γ c f, toAmbient hf.meromorphic = a}
  zero_mem' := ⟨fun _ ↦ 0, IsModularFunction.const 0, toGerm_zero⟩
  one_mem' := ⟨fun _ ↦ 1, IsModularFunction.const 1, toGerm_one⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, toAmbient_add _ _⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, toAmbient_neg _⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, toAmbient_mul _ _⟩
  inv_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨f⁻¹, hf.inv, toAmbient_inv _⟩

/-- The tested modular-function field, defined only after the raw predicate. -/
abbrev ModularFunctionField := modularSubfield Γ c

example : Field (ModularFunctionField Γ c) := inferInstance

def IsModularFunction.toField {f : ℍ → ℂ} (hf : IsModularFunction Γ c f) :
    ModularFunctionField Γ c := ⟨toAmbient hf.meromorphic, f, hf, rfl⟩

#print axioms modularSubfield
#print axioms toAmbient_inv

end

end MMeromorphicTest.Modular
