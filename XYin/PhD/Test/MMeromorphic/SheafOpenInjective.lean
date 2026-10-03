import XYin.PhD.Test.MMeromorphic.SheafFractionEquality
import XYin.PhD.Test.MMeromorphic.SheafOpenQuotientBridge

/-!
# Injectivity of the direct meromorphic comparison on arbitrary complex opens

Equality of the forward sheaf sections forces equality of the raw meromorphic functions
on every punctured germ in the open. This gives codiscrete equality without connectedness
and therefore equality in the independently defined meromorphic quotient ring.
-/

open CategoryTheory Opposite AlgebraicGeometry Filter Set TopologicalSpace
open TopologicalSpace.Opens
open scoped Topology nonZeroDivisors

namespace MMeromorphicTest.SheafLocalBridge

open MeromorphicFunction

noncomputable section

/-- Equality of forward sheaf sections identifies all raw punctured meromorphic germs. -/
lemma sectionOn_eq_imp_eventuallyEq {f g : ℂ → ℂ} {U : Opens ComplexTopCat}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (heq : sectionOn hf = sectionOn hg)
    {z : ℂ} (hz : z ∈ U) : f =ᶠ[𝓝[≠] z] g := by
  let q := localSheafFractionOn hf ⟨z, hz⟩
  let r := localSheafFractionOn hg ⟨z, hz⟩
  have hqU : q.domain ≤ U := inf_le_right
  have hrU : r.domain ≤ U := inf_le_right
  have hq := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op k)
      (sectionOn_restrict hf ⟨z, hz⟩)
  have hr := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op k)
      (sectionOn_restrict hg ⟨z, hz⟩)
  have hqcomp := TopCat.Presheaf.restrict_restrict (F := X.meromorphicSheaf.presheaf)
    (inf_le_left : q.domain ⊓ r.domain ≤ q.domain) hqU (sectionOn hf)
  have hrcomp := TopCat.Presheaf.restrict_restrict (F := X.meromorphicSheaf.presheaf)
    (inf_le_right : q.domain ⊓ r.domain ≤ r.domain) hrU (sectionOn hg)
  have hres := congrArg (fun k ↦ X.meromorphicSheaf.presheaf.map
    (homOfLE (inf_le_left.trans hqU : q.domain ⊓ r.domain ≤ U)).op k) heq
  exact q.eventuallyEq_of_toSheaf_overlap_eq r q.point_mem r.point_mem
    (hq.symm.trans (hqcomp.trans (hres.trans (hrcomp.symm.trans hr))))

/-- Equality of forward sections gives codiscrete equality on any open, with no
connectedness or nonemptiness hypothesis. -/
theorem sectionOn_eq_imp_codiscrete {f g : ℂ → ℂ} {U : Opens ComplexTopCat}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (heq : sectionOn hf = sectionOn hg) :
    f =ᶠ[codiscreteWithin (U : Set ℂ)] g := by
  rw [EventuallyEq, eventually_iff, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hz
  exact (sectionOn_eq_imp_eventuallyEq hf hg heq hz).mono fun w hw ↦ Or.inl hw

/-- The sheaf comparison identifies exactly the codiscrete equivalence relation. -/
theorem sectionOn_eq_iff_codiscrete {f g : ℂ → ℂ} {U : Opens ComplexTopCat}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    sectionOn hf = sectionOn hg ↔ f =ᶠ[codiscreteWithin (U : Set ℂ)] g :=
  ⟨sectionOn_eq_imp_codiscrete hf hg, sectionOn_congr hf hg⟩

/-- The raw-to-quotient map is injective after comparison with the sheaf construction. -/
theorem toGerm_eq_of_sectionOn_eq {f g : ℂ → ℂ} {U : Opens ComplexTopCat}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (heq : sectionOn hf = sectionOn hg) :
    toGerm hf = toGerm hg :=
  (toGerm_eq_iff hf hg).mpr (sectionOn_eq_imp_codiscrete hf hg heq)

/-- The comparison ring homomorphism is injective on every complex open, including
disconnected and empty opens. The proof does not use a field structure. -/
theorem toSheafRingHomOn_injective_all (U : Opens ComplexTopCat) :
    Function.Injective (toSheafRingHomOn U) := by
  intro a b heq
  obtain ⟨f, hf, hef⟩ := a.property
  obtain ⟨g, hg, heg⟩ := b.property
  have ha : toGerm hf = a := Subtype.ext hef
  have hb : toGerm hg = b := Subtype.ext heg
  rw [← ha, ← hb, toSheafRingHomOn_toGerm, toSheafRingHomOn_toGerm] at heq
  exact ha.symm.trans ((toGerm_eq_of_sectionOn_eq hf hg heq).trans hb)

example (U : Opens ComplexTopCat) (a b : MeromorphicGerms (U : Set ℂ))
    (h : toSheafRingHomOn U a = toSheafRingHomOn U b) : a = b :=
  toSheafRingHomOn_injective_all U h

#print axioms sectionOn_eq_imp_codiscrete
#print axioms toGerm_eq_of_sectionOn_eq
#print axioms toSheafRingHomOn_injective_all

end

end MMeromorphicTest.SheafLocalBridge
