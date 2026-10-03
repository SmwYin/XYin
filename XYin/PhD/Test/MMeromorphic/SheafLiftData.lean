import XYin.PhD.Test.MMeromorphic.SheafReverseBridge

/-! Certified local fraction data for a meromorphic sheaf section. -/

open CategoryTheory Opposite AlgebraicGeometry Set TopologicalSpace
open TopologicalSpace.Opens
open scoped Topology nonZeroDivisors

namespace MMeromorphicTest.SheafLocalBridge

open MeromorphicFunction

noncomputable section

/-- A local holomorphic fraction representing a given sheaf section near a specified point. -/
structure FractionLift {U : Opens ComplexTopCat}
    (s : X.meromorphicSheaf.presheaf.obj (op U)) (x : U) where
  domain : Opens ComplexTopCat
  inclusion : domain ≤ U
  point_mem : (x : ℂ) ∈ domain
  numerator : HolomorphicSection domain
  denominator : HolomorphicSection domain
  regular : denominator ∈ X.meromorphicSubmonoidPresheaf.obj (op domain)
  represents : (CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf).app (op domain)
      (Localization.mk numerator ⟨denominator, regular⟩) =
        X.meromorphicSheaf.presheaf.map (homOfLE inclusion).op s

theorem exists_fractionLift {U : Opens ComplexTopCat}
    (s : X.meromorphicSheaf.presheaf.obj (op U)) (x : U) : Nonempty (FractionLift s x) := by
  obtain ⟨V, hVU, hxV, a, b, hb, hrep⟩ := exists_holomorphicFraction_lift s x.property
  exact ⟨⟨V, hVU, hxV, a, b, hb, hrep⟩⟩

def fractionLift {U : Opens ComplexTopCat}
    (s : X.meromorphicSheaf.presheaf.obj (op U)) (x : U) : FractionLift s x :=
  Classical.choice (exists_fractionLift s x)

namespace FractionLift

variable {U : Opens ComplexTopCat} {s : X.meromorphicSheaf.presheaf.obj (op U)} {x : U}

/-- Extend the local ratio arbitrarily outside its open domain. -/
def ratio (q : FractionLift s x) : ℂ → ℂ :=
  ringSectionFun q.numerator / ringSectionFun q.denominator

theorem ratio_meromorphic (q : FractionLift s x) : MeromorphicOn q.ratio q.domain := by
  intro z hz
  exact (analyticOnNhd_ringSectionFun q.numerator z hz).meromorphicAt.div
    (analyticOnNhd_ringSectionFun q.denominator z hz).meromorphicAt

/-- A lift is a certified raw fraction at every point of its open domain. -/
def certificate (q : FractionLift s x) {z : ℂ} (hz : z ∈ q.domain) :
    LocalSheafFraction q.ratio z := by
  refine ⟨q.domain, hz, q.numerator, q.denominator, q.regular, ?_⟩
  intro y hy
  simp only [ratio, Pi.div_apply, ringSectionFun_apply _ y.property]

theorem certificate_represents (q : FractionLift s x) {z : ℂ} (hz : z ∈ q.domain) :
    (q.certificate hz).toSheaf =
      X.meromorphicSheaf.presheaf.map (homOfLE q.inclusion).op s := q.represents

theorem certificates_overlap {y : U} (q : FractionLift s x) (r : FractionLift s y) :
    X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op
      (q.certificate q.point_mem).toSheaf =
        X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op
          (r.certificate r.point_mem).toSheaf := by
  rw [q.certificate_represents q.point_mem, r.certificate_represents r.point_mem]
  exact (TopCat.Presheaf.restrict_restrict
    (F := X.meromorphicSheaf.presheaf) (inf_le_left : q.domain ⊓ r.domain ≤ q.domain)
    q.inclusion s).trans
      (TopCat.Presheaf.restrict_restrict
        (F := X.meromorphicSheaf.presheaf) (inf_le_right : q.domain ⊓ r.domain ≤ r.domain)
        r.inclusion s).symm

end FractionLift

#print axioms exists_fractionLift
#print axioms FractionLift.ratio_meromorphic

end

end MMeromorphicTest.SheafLocalBridge
