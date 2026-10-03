import XYin.PhD.Test.MMeromorphic.SheafQuotientBridge
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Recovering local holomorphic fractions from meromorphic sheaf sections

The canonical map into sheafification is locally surjective. Consequently every meromorphic
sheaf section is locally the image of a holomorphic localization fraction with a stalkwise
regular denominator. This is a local reverse-comparison statement; it does not yet construct
a global raw meromorphic representative or assert global surjectivity.
-/

open CategoryTheory Opposite AlgebraicGeometry Set TopologicalSpace
open TopologicalSpace.Opens
open scoped Topology nonZeroDivisors

namespace MMeromorphicTest.SheafLocalBridge

open MeromorphicFunction

noncomputable section

/-- A section of the meromorphic sheaf lifts locally to the original localization presheaf. -/
theorem exists_localizedLift {U : Opens ComplexTopCat}
    (s : X.meromorphicSheaf.presheaf.obj (op U)) {x : ℂ} (hx : x ∈ U) :
    ∃ (V : Opens ComplexTopCat) (hVU : V ≤ U), x ∈ V ∧
      ∃ t : X.meromorphicPresheaf.obj (op V),
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
          X.meromorphicPresheaf).app (op V) t =
            X.meromorphicSheaf.presheaf.map (homOfLE hVU).op s := by
  let α := CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf
  have hα : TopCat.Presheaf.IsLocallySurjective α := by
    change CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X.toTopCat) α
    infer_instance
  obtain ⟨V, hVU, ⟨t, ht⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff α).mp hα U s x hx
  exact ⟨V, hVU, hxV, t, ht⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every meromorphic sheaf section is locally a fraction of holomorphic sections whose
denominator is nonzero in every stalk. -/
theorem exists_holomorphicFraction_lift {U : Opens ComplexTopCat}
    (s : X.meromorphicSheaf.presheaf.obj (op U)) {x : ℂ} (hx : x ∈ U) :
    ∃ (V : Opens ComplexTopCat) (hVU : V ≤ U), x ∈ V ∧
      ∃ (a b : HolomorphicSection V)
        (hb : b ∈ X.meromorphicSubmonoidPresheaf.obj (op V)),
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
          X.meromorphicPresheaf).app (op V) (Localization.mk a ⟨b, hb⟩) =
            X.meromorphicSheaf.presheaf.map (homOfLE hVU).op s := by
  obtain ⟨V, hVU, hxV, t, ht⟩ := exists_localizedLift s hx
  change Localization (X.meromorphicSubmonoidPresheaf.obj (op V)) at t
  obtain ⟨a, b, heq⟩ := IsLocalization.exists_mk'_eq
    (X.meromorphicSubmonoidPresheaf.obj (op V)) t
  refine ⟨V, hVU, hxV, a, b.val, b.property, ?_⟩
  rw [Localization.mk_eq_mk', heq]
  exact ht

example (s : X.meromorphicGlobalSections) (x : ℂ) :
    ∃ (V : Opens ComplexTopCat) (hV : V ≤ ⊤), x ∈ V ∧
      ∃ t : X.meromorphicPresheaf.obj (op V),
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
          X.meromorphicPresheaf).app (op V) t =
            X.meromorphicSheaf.presheaf.map (homOfLE hV).op s :=
  exists_localizedLift s (mem_top x)

#print axioms exists_localizedLift
#print axioms exists_holomorphicFraction_lift

end

end MMeromorphicTest.SheafLocalBridge
