import XYin.PhD.Test.MMeromorphic.Field
import Mathlib.Analysis.Complex.Basic

/-!
# Gluing compatible local meromorphic representatives

The local functions need only agree as punctured germs on overlaps. Normalization makes
their values agree there, so a global normal representative can be defined by choosing
the local function indexed by its evaluation point. This is an analytic gluing theorem;
it does not itself assert that every section of a meromorphic sheaf has such local data.
-/

open Filter Topology Set

namespace MMeromorphicTest.NormalGluing

/-- Local meromorphic representatives, with compatibility of punctured germs on overlaps. -/
structure LocalFamily (U : TopologicalSpace.Opens ℂ) where
  domain : U → TopologicalSpace.Opens ℂ
  domain_le : ∀ x, domain x ≤ U
  mem_domain : ∀ x, (x : ℂ) ∈ domain x
  representative : U → ℂ → ℂ
  meromorphic : ∀ x, MeromorphicOn (representative x) (domain x)
  compatible : ∀ x y z, z ∈ domain x → z ∈ domain y →
    representative x =ᶠ[𝓝[≠] z] representative y

variable {U : TopologicalSpace.Opens ℂ}

/-- The normal representative attached to one member of the local family. -/
noncomputable def LocalFamily.normalized (a : LocalFamily U) (x : U) : ℂ → ℂ :=
  toMeromorphicNFOn (a.representative x) (a.domain x)

/-- Normalization upgrades compatibility of punctured germs to actual equality on overlaps. -/
theorem LocalFamily.normalized_eq (a : LocalFamily U) {x y : U} {z : ℂ}
    (hx : z ∈ a.domain x) (hy : z ∈ a.domain y) :
    a.normalized x z = a.normalized y z := by
  have hnx := meromorphicNFOn_toMeromorphicNFOn (a.representative x) (a.domain x) hx
  have hny := meromorphicNFOn_toMeromorphicNFOn (a.representative y) (a.domain y) hy
  have he : a.normalized x =ᶠ[𝓝[≠] z] a.normalized y :=
    ((a.meromorphic x).toMeromorphicNFOn_eq_self_on_nhdsNE hx).trans
      ((a.compatible x y z hx hy).trans
        ((a.meromorphic y).toMeromorphicNFOn_eq_self_on_nhdsNE hy).symm)
  exact ((hnx.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hny).mp he).eq_of_nhds

/-- At points of `U`, use the normalized local function centered at that point. -/
noncomputable def LocalFamily.glue (a : LocalFamily U) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ U then a.normalized ⟨z, hz⟩ z else 0

@[simp] theorem LocalFamily.glue_apply (a : LocalFamily U) (z : U) :
    a.glue z = a.normalized z z := by
  classical
  simp [LocalFamily.glue, z.property]

/-- The glued function agrees pointwise with every local normal representative. -/
theorem LocalFamily.glue_eqOn (a : LocalFamily U) (x : U) :
    EqOn a.glue (a.normalized x) (a.domain x) := by
  intro z hz
  have hzU : z ∈ U := a.domain_le x hz
  let y : U := ⟨z, hzU⟩
  change a.glue y = a.normalized x y
  rw [a.glue_apply]
  exact a.normalized_eq (a.mem_domain y) hz

/-- The glued function is in meromorphic normal form on the whole open domain. -/
theorem LocalFamily.glue_meromorphicNFOn (a : LocalFamily U) :
    MeromorphicNFOn a.glue U := by
  intro z hz
  let x : U := ⟨z, hz⟩
  have he : a.glue =ᶠ[𝓝 z] a.normalized x := by
    filter_upwards [(a.domain x).isOpen.mem_nhds (a.mem_domain x)] with w hw
    exact a.glue_eqOn x hw
  exact (meromorphicNFAt_congr he).mpr
    (meromorphicNFOn_toMeromorphicNFOn (a.representative x) (a.domain x) (a.mem_domain x))

/-- The glued normal representative supplies an element of the ordinary normal-form model. -/
noncomputable def LocalFamily.normalMeromorphic (a : LocalFamily U) :
    NormalMeromorphic (U : Set ℂ) := by
  refine ⟨fun x ↦ a.glue x, ?_⟩
  intro z hz
  have he : extendDomain (fun x : U ↦ a.glue x) =ᶠ[𝓝 z] a.glue := by
    filter_upwards [U.isOpen.mem_nhds hz] with w hw
    simp [extendDomain, hw]
  exact (meromorphicNFAt_congr he).mpr (a.glue_meromorphicNFOn hz)

example (a : LocalFamily U) : MeromorphicOn a.glue U :=
  a.glue_meromorphicNFOn.meromorphicOn

example (a : LocalFamily U) (x : U) : EqOn a.glue (a.normalized x) (a.domain x) :=
  a.glue_eqOn x

#print axioms LocalFamily.normalized_eq
#print axioms LocalFamily.glue_meromorphicNFOn

end MMeromorphicTest.NormalGluing
