import XYin.PhD.Test.MMeromorphic.LevelOneOrbit
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Defs

/-!
# The topology of the open level-one orbit quotient

The actual holomorphic modular invariant `j : ℍ → ℂ` is an open map, by the complex open
mapping theorem and its established surjectivity. The previously constructed orbit bijection
therefore gives a homeomorphism for the existing quotient topology on `ℍ / SL₂(ℤ)`.

This result concerns the open curve as a topological space. It does not construct an analytic
atlas, add the cusp, identify an analytic sheaf, or identify a compactified modular curve.
-/

open UpperHalfPlane Set Topology
open scoped MatrixGroups

namespace MMeromorphicTest.LevelOneTopology

/-- The actual modular invariant is open on the upper half-plane. -/
theorem isOpenMap_j : IsOpenMap j := by
  have hhol : AnalyticOnNhd ℂ (j ∘ ofComplex) upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff.mp j_mdifferentiable).analyticOnNhd
      isOpen_upperHalfPlaneSet
  rcases hhol.is_constant_or_isOpen (convex_halfSpace_im_gt 0).isPreconnected with
    ⟨c, hc⟩ | hopen
  · obtain ⟨τ, hτ⟩ := j_surjective (c + 1)
    have h : c + 1 = c := hτ.symm.trans (by simpa using hc τ τ.im_pos)
    exact (one_ne_zero (add_left_cancel (h.trans (add_zero c).symm))).elim
  · intro s hs
    have hsub : ((↑) '' s : Set ℂ) ⊆ upperHalfPlaneSet := by
      rintro z ⟨τ, hτ, rfl⟩
      exact τ.im_pos
    simpa only [image_image, Function.comp_def, ofComplex_apply] using
      hopen ((↑) '' s) hsub (isOpenEmbedding_coe.isOpenMap s hs)

/-- The modular invariant equips `ℂ` with precisely its quotient topology from `ℍ`. -/
theorem isQuotientMap_j : IsQuotientMap j :=
  isOpenMap_j.isQuotientMap j_mdifferentiable.continuous j_surjective

/-- The actual `j`-coordinate is a homeomorphism of the open orbit quotient with `ℂ`. -/
noncomputable def homeomorph : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ ≃ₜ ℂ :=
  LevelOneOrbit.equiv.toHomeomorph fun s ↦
    (isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage
      (s := LevelOneOrbit.equiv ⁻¹' s)).symm.trans
        (isQuotientMap_j.isCoinducing.isOpen_preimage (s := s))

@[simp]
theorem homeomorph_mk (τ : ℍ) :
    homeomorph (Quotient.mk (MulAction.orbitRel SL(2, ℤ) ℍ) τ) = j τ := rfl

@[simp]
theorem homeomorph_symm_apply_j (τ : ℍ) :
    homeomorph.symm (j τ) = Quotient.mk (MulAction.orbitRel SL(2, ℤ) ℍ) τ :=
  LevelOneOrbit.equiv_symm_apply_j τ

example : Continuous homeomorph := homeomorph.continuous

example : Continuous homeomorph.symm := homeomorph.symm.continuous

#print axioms isOpenMap_j
#print axioms isQuotientMap_j
#print axioms homeomorph
#print axioms homeomorph_mk
#print axioms homeomorph_symm_apply_j

end MMeromorphicTest.LevelOneTopology
