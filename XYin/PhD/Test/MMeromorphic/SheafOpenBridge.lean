import XYin.PhD.Test.MMeromorphic.SheafGlobalBridge
import XYin.PhD.Test.MMeromorphic.UpperHalfPlane

/-!
# Direct meromorphy gives meromorphic sheaf sections on arbitrary opens

Local certified fractions can be restricted to any smaller open containing their center.
For a function meromorphic on an open `U`, we intersect each local fraction domain with `U`,
prove compatibility using the certified overlap theorem, and glue to a section over `U`.
This supplies the upper half-plane comparison directly from the raw analytic condition.
It asserts a forward construction, not an isomorphism of meromorphic-section fields.
-/

open CategoryTheory Opposite AlgebraicGeometry Filter Set TopologicalSpace UpperHalfPlane
open TopologicalSpace.Opens
open scoped Topology nonZeroDivisors

namespace MMeromorphicTest.SheafLocalBridge

open MeromorphicFunction

noncomputable section

namespace LocalSheafFraction

/-- Restrict a certified local fraction to a smaller open containing its center.
Stalkwise regularity restricts along the submonoid presheaf. -/
def restrict {f : ℂ → ℂ} {x : ℂ} (q : LocalSheafFraction f x)
    (V : Opens ComplexTopCat) (hVq : V ≤ q.domain) (hxV : x ∈ V) :
    LocalSheafFraction f x := by
  let i : V ⟶ q.domain := homOfLE hVq
  refine ⟨V, hxV, X.presheaf.map i.op q.numerator, X.presheaf.map i.op q.denominator,
    X.meromorphicSubmonoidPresheaf.map i.op q.denominator_regular, ?_⟩
  intro y hy
  exact q.eq_away_center ⟨y, hVq y.property⟩ hy

@[simp]
lemma restrict_domain {f : ℂ → ℂ} {x : ℂ} (q : LocalSheafFraction f x)
    (V : Opens ComplexTopCat) (hVq : V ≤ q.domain) (hxV : x ∈ V) :
    (q.restrict V hVq hxV).domain = V := rfl

end LocalSheafFraction

/-- A local fraction from direct meromorphy whose domain is contained in the requested open. -/
def localSheafFractionOn {f : ℂ → ℂ} {U : Opens ComplexTopCat}
    (hf : MeromorphicOn f U) (x : U) : LocalSheafFraction f x :=
  let q := localSheafFraction (hf x x.property)
  q.restrict (q.domain ⊓ U) inf_le_left ⟨q.point_mem, x.property⟩

@[simp]
lemma localSheafFractionOn_domain {f : ℂ → ℂ} {U : Opens ComplexTopCat}
    (hf : MeromorphicOn f U) (x : U) :
    (localSheafFractionOn hf x).domain =
      (localSheafFraction (hf x x.property)).domain ⊓ U := rfl

/-- Direct meromorphy on an open provides a unique compatible meromorphic sheaf section there. -/
theorem existsUnique_sectionOn {f : ℂ → ℂ} {U : Opens ComplexTopCat}
    (hf : MeromorphicOn f U) :
    ∃! s : X.meromorphicSheaf.presheaf.obj (op U), ∀ x : U,
      X.meromorphicSheaf.presheaf.map (homOfLE
        (show (localSheafFractionOn hf x).domain ≤ U from inf_le_right)).op s =
        (localSheafFractionOn hf x).toSheaf := by
  let q := fun x : U ↦ localSheafFractionOn hf x
  let V := fun x : U ↦ (q x).domain
  have hcover : U ≤ iSup V := by
    intro z hz
    exact Opens.mem_iSup.mpr ⟨⟨z, hz⟩, (q ⟨z, hz⟩).point_mem⟩
  have hcompatible : TopCat.Presheaf.IsCompatible X.meromorphicSheaf.presheaf V
      (fun x ↦ (q x).toSheaf) := fun x y ↦ (q x).toSheaf_overlap (q y)
  exact X.meromorphicSheaf.existsUnique_gluing' V U (fun _ ↦ homOfLE inf_le_right)
    hcover (fun x ↦ (q x).toSheaf) hcompatible

/-- A meromorphic section over the requested open, constructed from the direct predicate. -/
def sectionOn {f : ℂ → ℂ} {U : Opens ComplexTopCat} (hf : MeromorphicOn f U) :
    X.meromorphicSheaf.presheaf.obj (op U) := (existsUnique_sectionOn hf).choose

lemma sectionOn_restrict {f : ℂ → ℂ} {U : Opens ComplexTopCat}
    (hf : MeromorphicOn f U) (x : U) :
    X.meromorphicSheaf.presheaf.map (homOfLE
      (show (localSheafFractionOn hf x).domain ≤ U from inf_le_right)).op (sectionOn hf) =
      (localSheafFractionOn hf x).toSheaf :=
  (existsUnique_sectionOn hf).choose_spec.1 x

/-- The upper half-plane as an open of the complex holomorphic locally ringed space. -/
def upperHalfPlaneOpen : Opens ComplexTopCat :=
  ⟨{z : ℂ | 0 < z.im}, isOpen_upperHalfPlaneSet⟩

/-- The independently defined upper half-plane condition concretely gives a section of the
reference meromorphic sheaf over `{z : ℂ | 0 < z.im}`. -/
def upperHalfPlaneSection {f : ℍ → ℂ} (hf : MMeromorphicTest.UHP.Meromorphic f) :
    X.meromorphicSheaf.presheaf.obj (op upperHalfPlaneOpen) :=
  sectionOn (f := f ∘ ofComplex) (U := upperHalfPlaneOpen) hf

example {f : ℂ → ℂ} {U : Opens ComplexTopCat} (hf : MeromorphicOn f U) :
    X.meromorphicSheaf.presheaf.obj (op U) := sectionOn hf

example : X.meromorphicSheaf.presheaf.obj (op upperHalfPlaneOpen) :=
  upperHalfPlaneSection (MMeromorphicTest.UHP.const 1)

example : X.meromorphicSheaf.presheaf.obj (op upperHalfPlaneOpen) :=
  upperHalfPlaneSection (MMeromorphicTest.UHP.of_mdifferentiable UpperHalfPlane.mdifferentiable_coe)

#print axioms LocalSheafFraction.restrict
#print axioms existsUnique_sectionOn
#print axioms upperHalfPlaneSection

end

end MMeromorphicTest.SheafLocalBridge
