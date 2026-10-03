import XYin.PhD.Test.MMeromorphic.SheafOpenInjective
import XYin.PhD.Test.MMeromorphic.SheafSurjective

/-!
# Equivalence of direct meromorphic classes and the localized sheaf construction

On every complex open, the comparison is a ring equivalence. Connectedness and
nonemptiness enter only when asserting that these rings are fields. The analytic
predicate, its quotient, and its normal representatives were defined independently.
-/

open CategoryTheory Opposite AlgebraicGeometry Filter Set TopologicalSpace
open TopologicalSpace.Opens
open scoped Topology

namespace MMeromorphicTest.SheafLocalBridge

open MeromorphicFunction

noncomputable section

/-- Every sheaf section on a complex open comes from a directly meromorphic function. -/
theorem toSheafRingHomOn_surjective (U : Opens ComplexTopCat) :
    Function.Surjective (toSheafRingHomOn U) := by
  intro s
  refine ⟨toGerm (sheafRepresentative_meromorphic s), ?_⟩
  rw [toSheafRingHomOn_toGerm, sectionOn_sheafRepresentative]

/-- The codiscrete and sheaf constructions agree on every open complex domain. -/
def toSheafRingEquivOn (U : Opens ComplexTopCat) :
    MeromorphicGerms (U : Set ℂ) ≃+* X.meromorphicSheaf.presheaf.obj (op U) :=
  RingEquiv.ofBijective (toSheafRingHomOn U)
    ⟨toSheafRingHomOn_injective_all U, toSheafRingHomOn_surjective U⟩

@[simp] theorem toSheafRingEquivOn_toGerm {U : Opens ComplexTopCat} {f : ℂ → ℂ}
    (hf : MeromorphicOn f U) : toSheafRingEquivOn U (toGerm hf) = sectionOn hf :=
  toSheafRingHomOn_toGerm hf

@[simp] theorem toSheafRingEquivOn_symm_sectionOn {U : Opens ComplexTopCat} {f : ℂ → ℂ}
    (hf : MeromorphicOn f U) : (toSheafRingEquivOn U).symm (sectionOn hf) = toGerm hf := by
  rw [← toSheafRingEquivOn_toGerm hf, RingEquiv.symm_apply_apply]

/-- On a connected nonempty domain normal representatives and sheaf sections are
ring-isomorphic for their independently verified field structures. -/
def normalToSheafRingEquivOn (U : Opens ComplexTopCat)
    (hU : IsConnected (U : Set ℂ)) :
    letI : NeBot (codiscreteWithin (U : Set ℂ)) :=
      codiscreteWithin_neBot_of_open (U : Set ℂ) U.isOpen hU.nonempty
    letI := normalField U.isOpen hU.isPreconnected
    NormalMeromorphic (U : Set ℂ) ≃+* X.meromorphicSheaf.presheaf.obj (op U) := by
  letI : NeBot (codiscreteWithin (U : Set ℂ)) :=
    codiscreteWithin_neBot_of_open (U : Set ℂ) U.isOpen hU.nonempty
  letI := meromorphicGermField (U : Set ℂ) hU.isPreconnected
  letI := normalField U.isOpen hU.isPreconnected
  exact (normalRingEquiv U.isOpen hU.isPreconnected).trans (toSheafRingEquivOn U)

@[simp] theorem normalToSheafRingEquivOn_normalize (U : Opens ComplexTopCat)
    (hU : IsConnected (U : Set ℂ)) {f : ℂ → ℂ} (hf : MeromorphicOn f U) :
    normalToSheafRingEquivOn U hU (normalize U.isOpen hf) = sectionOn hf := by
  change toSheafRingEquivOn U (normalToGerm (normalize U.isOpen hf)) = sectionOn hf
  rw [normalToGerm_normalize, toSheafRingEquivOn_toGerm]

example (U : Opens ComplexTopCat) (a b : MeromorphicGerms (U : Set ℂ)) :
    toSheafRingEquivOn U (a * b + 1) =
      toSheafRingEquivOn U a * toSheafRingEquivOn U b + 1 := by
  simp

/-- The upper-half-plane comparison is an actual ring equivalence. -/
example : MeromorphicGerms (upperHalfPlaneOpen : Set ℂ) ≃+*
    X.meromorphicSheaf.presheaf.obj (op upperHalfPlaneOpen) :=
  toSheafRingEquivOn upperHalfPlaneOpen

/-- The theorem also covers the complex plane. -/
example : MeromorphicGerms (univ : Set ℂ) ≃+* X.meromorphicGlobalSections :=
  toSheafRingEquivOn ⊤

#print axioms toSheafRingEquivOn
#print axioms normalToSheafRingEquivOn

end

end MMeromorphicTest.SheafLocalBridge
