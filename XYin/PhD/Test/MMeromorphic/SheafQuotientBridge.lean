import XYin.PhD.Test.MMeromorphic.Field
import XYin.PhD.Test.MMeromorphic.SheafArithmeticBridge

/-!
# Descending the forward sheaf construction to codiscrete classes

The independently constructed meromorphic quotient supplies a meromorphic representative.
The forward sheaf construction is independent of that choice by `globalSection_congr`.
Local fraction arithmetic makes the resulting function a ring homomorphism.
Bijectivity is a separate theorem.
-/

open Filter Set

namespace MMeromorphicTest.SheafLocalBridge

noncomputable section

/-- Send a class in the independently constructed meromorphic field to a global section
of the reference meromorphic sheaf. -/
def ofGerm (a : MeromorphicGerms (univ : Set ℂ)) : X.meromorphicGlobalSections :=
  globalSection a.property.choose_spec.1

/-- On any direct meromorphic representative, the descended construction agrees with
the forward local-fraction construction. -/
@[simp] theorem ofGerm_toGerm {f : ℂ → ℂ} (hf : MeromorphicOn f univ) :
    ofGerm (toGerm hf) = globalSection hf := by
  apply globalSection_congr
  exact Germ.coe_eq.mp (toGerm hf).property.choose_spec.2

@[simp] theorem ofGerm_add (a b : MeromorphicGerms (univ : Set ℂ)) :
    ofGerm (a + b) = ofGerm a + ofGerm b := by
  obtain ⟨f, hf, hef⟩ := a.property
  obtain ⟨g, hg, heg⟩ := b.property
  have ha : toGerm hf = a := Subtype.ext hef
  have hb : toGerm hg = b := Subtype.ext heg
  rw [← ha, ← hb, ← toGerm_add, ofGerm_toGerm, ofGerm_toGerm, ofGerm_toGerm]
  exact globalSection_add hf hg

@[simp] theorem ofGerm_mul (a b : MeromorphicGerms (univ : Set ℂ)) :
    ofGerm (a * b) = ofGerm a * ofGerm b := by
  obtain ⟨f, hf, hef⟩ := a.property
  obtain ⟨g, hg, heg⟩ := b.property
  have ha : toGerm hf = a := Subtype.ext hef
  have hb : toGerm hg = b := Subtype.ext heg
  rw [← ha, ← hb, ← toGerm_mul, ofGerm_toGerm, ofGerm_toGerm, ofGerm_toGerm]
  exact globalSection_mul hf hg

@[simp] theorem ofGerm_one : ofGerm 1 = 1 := by
  rw [← toGerm_one (𝕜 := ℂ) (U := univ), ofGerm_toGerm, globalSection_one]

@[simp] theorem ofGerm_zero : ofGerm 0 = 0 := by
  have h := ofGerm_add 0 0
  rw [zero_add] at h
  exact add_eq_left.mp h.symm

/-- The direct meromorphic quotient maps to the reference meromorphic sheaf by a
ring homomorphism constructed from local fractions. -/
def toSheafRingHom : MeromorphicGerms (univ : Set ℂ) →+* X.meromorphicGlobalSections where
  toFun := ofGerm
  map_zero' := ofGerm_zero
  map_one' := ofGerm_one
  map_add' := ofGerm_add
  map_mul' := ofGerm_mul

@[simp] theorem toSheafRingHom_toGerm {f : ℂ → ℂ} (hf : MeromorphicOn f univ) :
    toSheafRingHom (toGerm hf) = globalSection hf := ofGerm_toGerm hf

example (a b : MeromorphicGerms (univ : Set ℂ)) :
    toSheafRingHom (a * b + 1) = toSheafRingHom a * toSheafRingHom b + 1 := by
  simp

example {f g : ℂ → ℂ} (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (hfg : f =ᶠ[codiscreteWithin (univ : Set ℂ)] g) :
    ofGerm (toGerm hf) = ofGerm (toGerm hg) := by
  simp only [ofGerm_toGerm]
  exact globalSection_congr hf hg hfg

#print axioms ofGerm
#print axioms ofGerm_toGerm
#print axioms toSheafRingHom

end

end MMeromorphicTest.SheafLocalBridge
