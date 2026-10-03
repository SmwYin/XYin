import XYin.PhD.Test.MMeromorphic.Reference.ComplexPlane
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.Convex

/-!
# Meromorphic sheaf sections on a connected open set form a field

This generalizes the global-sections argument in the attributed `Reference.Basic` experiment,
adapted from
https://github.com/Zeta-Wu/MeromorphicFunction/blob/main/MeromorphicFunction/Basic.lean.
Connectedness is needed only on the chosen nonempty open set. No comparison between sheaf
sections and pointwise meromorphic representatives is assumed in this file.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Set

namespace MMeromorphicTest.SheafOpen

/-- Sections of the meromorphic sheaf form a field on any connected nonempty open domain,
provided its stalks are nontrivial and every stalk element is a unit or zero. -/
theorem isField_meromorphicSections (X : LocallyRingedSpace)
    [LocallyRingedSpace.HasNontrivialMeromorphicStalks X]
    [LocallyRingedSpace.HasZeroOrUnitMeromorphicStalks X]
    (U : Opens X) (hU : _root_.IsConnected (U : Set X)) :
    IsField (X.meromorphicSheaf.presheaf.obj (op U)) := by
  let Y := X.meromorphicRingedSpace
  letI : ConnectedSpace U := Subtype.connectedSpace hU
  refine { exists_pair_ne := ?_, mul_comm := mul_comm, mul_inv_cancel := ?_ }
  · obtain ⟨x, hx⟩ := hU.nonempty
    letI : Nontrivial (X.meromorphicStalk x) := inferInstance
    refine ⟨0, 1, ?_⟩
    intro he
    have hg := congrArg (fun s ↦ (X.meromorphicSheaf.presheaf.germ U x hx).hom s) he
    simp only [map_zero, map_one] at hg
    exact zero_ne_one hg
  · intro s hs
    let sY : Y.presheaf.obj (op U) := s
    let A : Set U := {x | IsUnit (Y.presheaf.germ U x.1 x.2 sY)}
    have hAne : A.Nonempty := by
      classical
      by_contra hnone
      apply hs
      apply TopCat.Presheaf.section_ext X.meromorphicSheaf U s 0
      intro x hx
      rw [map_zero]
      have hn : ¬IsUnit (Y.presheaf.germ U x hx sY) := fun h ↦ hnone ⟨⟨x, hx⟩, h⟩
      rcases LocallyRingedSpace.HasZeroOrUnitMeromorphicStalks.isUnit_or_eq_zero_stalk
        (X := X) x (Y.presheaf.germ U x hx sY) with hu | hz
      · exact False.elim (hn hu)
      · exact hz
    have hAo : IsOpen A := by
      rw [isOpen_iff_forall_mem_open]
      intro x hx
      obtain ⟨V, i, hxV, hu⟩ := Y.isUnit_res_of_isUnit_germ U sY x.1 x.2 hx
      refine ⟨Subtype.val ⁻¹' (V : Set Y), ?_, V.isOpen.preimage continuous_subtype_val, hxV⟩
      intro z hz
      change IsUnit (Y.presheaf.germ U z.1 z.2 sY)
      have hzu := RingHom.isUnit_map (Y.presheaf.germ V z.1 hz).hom hu
      simpa only [Y.presheaf.germ_res_apply (i := i) z.1 hz sY] using hzu
    have hAc : IsOpen Aᶜ := by
      rw [isOpen_iff_forall_mem_open]
      intro x hx
      have hn : ¬IsUnit (Y.presheaf.germ U x.1 x.2 sY) := hx
      have hx0 : Y.presheaf.germ U x.1 x.2 sY = 0 := by
        rcases LocallyRingedSpace.HasZeroOrUnitMeromorphicStalks.isUnit_or_eq_zero_stalk
          (X := X) x.1 (Y.presheaf.germ U x.1 x.2 sY) with hu | hz
        · exact False.elim (hn hu)
        · exact hz
      obtain ⟨V, i, hxV, hv0⟩ := Y.exists_res_eq_zero_of_germ_eq_zero U sY x hx0
      refine ⟨Subtype.val ⁻¹' (V : Set Y), ?_, V.isOpen.preimage continuous_subtype_val, hxV⟩
      intro z hz hzu
      letI : Nontrivial (Y.presheaf.stalk z.1) :=
        LocallyRingedSpace.HasNontrivialMeromorphicStalks.nontrivial_stalk (X := X) z.1
      have hz0 : Y.presheaf.germ V z.1 hz (Y.presheaf.map i.op sY) = 0 := by
        rw [hv0, map_zero]
      have hzn : Y.presheaf.germ V z.1 hz (Y.presheaf.map i.op sY) ≠ 0 := by
        rw [Y.presheaf.germ_res_apply (i := i) z.1 hz sY]
        exact IsUnit.ne_zero hzu
      exact hzn hz0
    have hA : A = univ := by
      rcases (isClopen_iff (α := U)).mp
        ⟨by simpa using hAc.isClosed_compl, hAo⟩ with he | he
      · exact False.elim (Set.not_nonempty_iff_eq_empty.mpr he hAne)
      · exact he
    have hu : IsUnit sY := by
      apply Y.isUnit_of_isUnit_germ U sY
      intro x hx
      have hm : (⟨x, hx⟩ : U) ∈ A := by simp [hA]
      exact hm
    exact hu.exists_right_inv

/-- The usual upper half-plane as an open subset of the reference holomorphic ringed space. -/
def upperHalfPlaneOpen : Opens MeromorphicFunction.holomorphicLocallyRingedSpace :=
  ⟨{z : ℂ | 0 < z.im}, UpperHalfPlane.isOpen_upperHalfPlaneSet⟩

theorem upperHalfPlaneOpen_connected :
    _root_.IsConnected (upperHalfPlaneOpen : Set
      MeromorphicFunction.holomorphicLocallyRingedSpace) := by
  change _root_.IsConnected {z : ℂ | 0 < z.im}
  apply Complex.isConnected_of_upperHalfPlane (r := 0) subset_rfl
  intro z hz
  change 0 < z.im at hz
  change 0 ≤ z.im
  exact hz.le

/-- An actual field structure on meromorphic sheaf sections over the upper half-plane. -/
noncomputable abbrev upperHalfPlaneSheafField :
    Field (MeromorphicFunction.holomorphicLocallyRingedSpace.meromorphicSheaf.presheaf.obj
      (op upperHalfPlaneOpen)) := by
  let X := MeromorphicFunction.holomorphicLocallyRingedSpace
  letI : LocallyConnectedSpace X := by
    change LocallyConnectedSpace ℂ
    infer_instance
  exact (isField_meromorphicSections X upperHalfPlaneOpen upperHalfPlaneOpen_connected).toField

example :
    letI := upperHalfPlaneSheafField
    (0 : MeromorphicFunction.holomorphicLocallyRingedSpace.meromorphicSheaf.presheaf.obj
      (op upperHalfPlaneOpen)) ≠ 1 := by
  letI := upperHalfPlaneSheafField
  exact zero_ne_one

example (f : MeromorphicFunction.holomorphicLocallyRingedSpace.meromorphicSheaf.presheaf.obj
    (op upperHalfPlaneOpen)) :
    letI := upperHalfPlaneSheafField
    f ≠ 0 → f * f⁻¹ = 1 := by
  letI := upperHalfPlaneSheafField
  exact mul_inv_cancel₀

#print axioms isField_meromorphicSections
#print axioms upperHalfPlaneSheafField

end MMeromorphicTest.SheafOpen
