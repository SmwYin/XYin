/-
Reference experiment adapted from Zhenhua Wu's public MeromorphicFunction repository.
Source: https://github.com/Zeta-Wu/MeromorphicFunction/blob/main/MeromorphicFunction/Basic.lean
Source blob: 857308c2e3dc7cfae5202f6210a3dffdfda7c652.
This copy is retained to test the cited sheaf construction against this project's mathlib.
-/
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyConnected

-- Compatibility with the pinned Lean 4.30 elaborator.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open Opposite
open TopCat
open TopCat.Presheaf
open scoped AlgebraicGeometry nonZeroDivisors

namespace AlgebraicGeometry
namespace RingedSpace

/-- The presheaf of total quotient rings associated to the structure sheaf of a ringed space. -/
noncomputable def meromorphicPresheaf (X : RingedSpace) :
    TopCat.Presheaf CommRingCat (X : TopCat) :=
  X.presheaf.totalQuotientPresheaf

/-- The canonical map from the structure presheaf to the meromorphic presheaf. -/
noncomputable def toMeromorphicPresheaf (X : RingedSpace) : X.presheaf ⟶ X.meromorphicPresheaf :=
  X.presheaf.toTotalQuotientPresheaf

/-- The sheafification of the meromorphic presheaf on a ringed space. -/
noncomputable def meromorphicSheaf (X : RingedSpace) : Sheaf CommRingCat (X : TopCat) :=
  CategoryTheory.presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) CommRingCat |>.obj
    X.meromorphicPresheaf

end RingedSpace

namespace LocallyRingedSpace

/-- The meromorphic presheaf of a locally ringed space, viewed via the underlying ringed space. -/
noncomputable abbrev meromorphicPresheaf (X : LocallyRingedSpace) :
    TopCat.Presheaf CommRingCat X.toTopCat :=
  X.toRingedSpace.meromorphicPresheaf

/-- The submonoid presheaf used to define the meromorphic presheaf of a locally ringed space. -/
noncomputable abbrev meromorphicSubmonoidPresheaf (X : LocallyRingedSpace) :
    X.presheaf.SubmonoidPresheaf :=
  X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰

/-- The meromorphic sheaf of a locally ringed space, viewed via the underlying ringed space. -/
noncomputable abbrev meromorphicSheaf (X : LocallyRingedSpace) :
    Sheaf CommRingCat X.toTopCat :=
  X.toRingedSpace.meromorphicSheaf

/-- The global sections of the meromorphic sheaf of a locally ringed space. -/
noncomputable abbrev meromorphicGlobalSections (X : LocallyRingedSpace) : CommRingCat :=
  X.meromorphicSheaf.1.obj (op ⊤)

/-- A locally ringed space has domain stalks if each stalk of the structure sheaf is a domain. -/
class HasDomainStalks (X : LocallyRingedSpace) : Prop where
  isDomain_stalk : ∀ x : X, IsDomain (X.presheaf.stalk x)

/-- Local form of `HasDomainStalks` on an open subset. -/
def HasDomainStalksOn (X : LocallyRingedSpace) (U : TopologicalSpace.Opens X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ U → IsDomain (X.presheaf.stalk x)

instance (X : LocallyRingedSpace) [h : HasDomainStalks X] (x : X) :
    IsDomain (X.presheaf.stalk x) :=
  h.isDomain_stalk x

theorem hasDomainStalksOn_univ_iff (X : LocallyRingedSpace) :
    HasDomainStalksOn X ⊤ ↔ HasDomainStalks X := by
  constructor
  · intro h
    refine ⟨?_⟩
    intro x
    exact h (show x ∈ (⊤ : TopologicalSpace.Opens X) by trivial)
  · intro h x hx
    exact h.isDomain_stalk x

theorem hasDomainStalks_of_open_cover (X : LocallyRingedSpace) {ι : Type*}
    (U : ι → TopologicalSpace.Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hlocal : ∀ i, HasDomainStalksOn X (U i)) :
    HasDomainStalks X := by
  refine ⟨?_⟩
  intro x
  obtain ⟨i, hxU⟩ := hcover x
  exact hlocal i hxU

theorem locallyConnectedSpace_of_open_cover (X : LocallyRingedSpace) {ι : Type*}
    (U : ι → TopologicalSpace.Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hlocal : ∀ i, LocallyConnectedSpace (U i)) :
    LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro F hF x hxF
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨i, hyU⟩ := hcover y
  let yU : U i := ⟨y, hyU⟩
  let FU : Set (U i) := ((↑) : U i → X) ⁻¹' F
  have hyF : y ∈ F := connectedComponentIn_subset F x hy
  have hyFU : yU ∈ FU := by
    exact hyF
  have hFU_open : IsOpen FU := hF.preimage continuous_subtype_val
  have hcc_open : IsOpen (connectedComponentIn FU yU) := by
    let _ : LocallyConnectedSpace (U i) := hlocal i
    exact hFU_open.connectedComponentIn
  let V : Set X := ((↑) : U i → X) '' connectedComponentIn FU yU
  have hV_open : IsOpen V := (U i).isOpen.isOpenMap_subtype_val _ hcc_open
  have hyV : y ∈ V := by
    refine ⟨yU, ?_, rfl⟩
    exact mem_connectedComponentIn hyFU
  refine mem_nhds_iff.mpr ⟨V, ?_, hV_open, hyV⟩
  intro z hzV
  rcases hzV with ⟨zU, hzU, rfl⟩
  have hzFy :
      zU.1 ∈ connectedComponentIn (F ∩ (U i : Set X)) y := by
    have hz_image :
        zU.1 ∈ connectedComponentIn (((↑) : U i → X) '' FU) y := by
      exact
        continuous_subtype_val.mapsTo_connectedComponentIn
          (s := FU) hyFU hzU
    have himage : ((↑) : U i → X) '' FU = (U i : Set X) ∩ F := by
      exact Subtype.image_preimage_coe (U i : Set X) F
    have hz_image' :
        zU.1 ∈ connectedComponentIn ((U i : Set X) ∩ F) y := by
      rw [himage] at hz_image
      exact hz_image
    rwa [Set.inter_comm] at hz_image'
  have hzFx : zU.1 ∈ connectedComponentIn F x := by
    have hzF : zU.1 ∈ connectedComponentIn F y := by
      exact connectedComponentIn_mono y (fun w hw => hw.1) hzFy
    simpa [connectedComponentIn_eq hy] using hzF
  exact hzFx

/-- The ringed space obtained by equipping the underlying topological space with the meromorphic
sheaf. -/
noncomputable def meromorphicRingedSpace (X : LocallyRingedSpace) : RingedSpace :=
  { carrier := X.toTopCat
    presheaf := X.meromorphicSheaf.1
    IsSheaf := X.meromorphicSheaf.2 }

/-- The stalk of the meromorphic sheaf at a point. -/
noncomputable abbrev meromorphicStalk (X : LocallyRingedSpace) (x : X) : CommRingCat :=
  X.meromorphicSheaf.presheaf.stalk x

/-- Analytically, the key local input is that every meromorphic stalk is a field. -/
class HasFieldMeromorphicStalks (X : LocallyRingedSpace) : Prop where
  isField_stalk : ∀ x : X, IsField (X.meromorphicStalk x)

/-- A weaker nontriviality hypothesis for meromorphic stalks. -/
class HasNontrivialMeromorphicStalks (X : LocallyRingedSpace) : Prop where
  nontrivial_stalk : ∀ x : X, Nontrivial (X.meromorphicStalk x)

instance (X : LocallyRingedSpace) [h : HasNontrivialMeromorphicStalks X] (x : X) :
    Nontrivial (X.meromorphicStalk x) :=
  h.nontrivial_stalk x

/-- A weaker field-like hypothesis: every meromorphic stalk element is either a unit or zero. -/
class HasZeroOrUnitMeromorphicStalks (X : LocallyRingedSpace) : Prop where
  isUnit_or_eq_zero_stalk : ∀ (x : X) (z : X.meromorphicStalk x), IsUnit z ∨ z = 0

/-- Analytic-style unique continuation: on a preconnected open set, a section is determined by any
one of its germs. -/
class UniqueContinuation (X : LocallyRingedSpace) : Prop where
  eq_of_germ_eq :
    ∀ {U : TopologicalSpace.Opens X} (_hU : IsPreconnected (U : Set X))
      (s t : X.presheaf.obj (op U)) {x : X} (hx : x ∈ U),
      X.presheaf.germ U x hx s = X.presheaf.germ U x hx t → s = t

/-- Local form of `UniqueContinuation` on an open subset. -/
def UniqueContinuationOn (X : LocallyRingedSpace) (U : TopologicalSpace.Opens X) : Prop :=
  ∀ ⦃V : TopologicalSpace.Opens X⦄, V ≤ U → IsPreconnected (V : Set X) →
    ∀ (s t : X.presheaf.obj (op V)) ⦃x : X⦄ (hx : x ∈ V),
      X.presheaf.germ V x hx s = X.presheaf.germ V x hx t → s = t

theorem uniqueContinuationOn_univ_iff (X : LocallyRingedSpace) :
    UniqueContinuationOn X ⊤ ↔ UniqueContinuation X := by
  constructor
  · intro h
    refine ⟨?_⟩
    intro U hU s t x hx hst
    exact h (show U ≤ (⊤ : TopologicalSpace.Opens X) by intro y hy; trivial) hU s t hx hst
  · intro h V hV hV_preconnected s t x hx hst
    exact UniqueContinuation.eq_of_germ_eq (X := X) (U := V) hV_preconnected s t hx hst

theorem UniqueContinuation.toOn (X : LocallyRingedSpace) [UniqueContinuation X]
    (U : TopologicalSpace.Opens X) : UniqueContinuationOn X U := by
  intro V hV hV_preconnected s t x hx hst
  exact UniqueContinuation.eq_of_germ_eq (X := X) (U := V) hV_preconnected s t hx hst

theorem uniqueContinuation_of_open_cover (X : LocallyRingedSpace) [LocallyConnectedSpace X]
    {ι : Type*} (U : ι → TopologicalSpace.Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hlocal : ∀ i, UniqueContinuationOn X (U i)) :
    UniqueContinuation X := by
  refine ⟨?_⟩
  intro V hV_preconnected s t x hx hst
  let A : Set V :=
    { y : V | X.presheaf.germ V y.1 y.2 s = X.presheaf.germ V y.1 y.2 t }
  have hA_open : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hyA
    obtain ⟨W, hyW, iWV₁, iWV₂, hW_eq⟩ := X.presheaf.germ_eq y.1 y.2 y.2 s t hyA
    refine Filter.mem_of_superset ((W.isOpen.preimage continuous_subtype_val).mem_nhds hyW) ?_
    intro z hzW
    change X.presheaf.germ V z.1 z.2 s = X.presheaf.germ V z.1 z.2 t
    rw [← X.presheaf.germ_res_apply (i := iWV₁) z.1 hzW s]
    rw [← X.presheaf.germ_res_apply (i := iWV₂) z.1 hzW t]
    exact congrArg (fun q => X.presheaf.germ W z.1 hzW q) hW_eq
  have hA_compl_open : IsOpen Aᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro y hyA
    obtain ⟨i, hyU⟩ := hcover y.1
    let WSet := connectedComponentIn ((V : Set X) ∩ U i) y.1
    have hWSet_open : IsOpen WSet := by
      exact (V.isOpen.inter (U i).isOpen).connectedComponentIn
    have hyWSet : y.1 ∈ WSet := by
      exact mem_connectedComponentIn ⟨y.2, hyU⟩
    refine Filter.mem_of_superset
      ((hWSet_open.preimage continuous_subtype_val).mem_nhds hyWSet) ?_
    intro z hzWSet hzA
    let W : TopologicalSpace.Opens X := ⟨WSet, hWSet_open⟩
    have hW_preconnected : IsPreconnected (W : Set X) := by
      change IsPreconnected (connectedComponentIn ((V : Set X) ∩ U i) y.1)
      exact isPreconnected_connectedComponentIn
    have hWV : W ≤ V := by
      intro p hp
      exact (connectedComponentIn_subset ((V : Set X) ∩ U i) y.1 hp).1
    have hWU : W ≤ U i := by
      intro p hp
      exact (connectedComponentIn_subset ((V : Set X) ∩ U i) y.1 hp).2
    let iWV : W ⟶ V := homOfLE hWV
    have hzA' :
        X.presheaf.germ W z.1 hzWSet (X.presheaf.map iWV.op s) =
          X.presheaf.germ W z.1 hzWSet (X.presheaf.map iWV.op t) := by
      rw [X.presheaf.germ_res_apply (i := iWV) z.1 hzWSet s]
      rw [X.presheaf.germ_res_apply (i := iWV) z.1 hzWSet t]
      exact hzA
    have hW_eq : X.presheaf.map iWV.op s = X.presheaf.map iWV.op t :=
      hlocal i hWU hW_preconnected (X.presheaf.map iWV.op s) (X.presheaf.map iWV.op t)
        hzWSet hzA'
    apply hyA
    change X.presheaf.germ V y.1 y.2 s = X.presheaf.germ V y.1 y.2 t
    rw [← X.presheaf.germ_res_apply (i := iWV) y.1 hyWSet s]
    rw [← X.presheaf.germ_res_apply (i := iWV) y.1 hyWSet t]
    exact congrArg (fun q => X.presheaf.germ W y.1 hyWSet q) hW_eq
  have hA_eq_univ : A = Set.univ := by
    let _ : PreconnectedSpace V := Subtype.preconnectedSpace hV_preconnected
    have hA_clopen : IsClopen A := by
      refine ⟨?_, hA_open⟩
      rw [← compl_compl A]
      exact isClosed_compl_iff.mpr hA_compl_open
    have hxA : (⟨x, hx⟩ : V) ∈ A := by
      exact hst
    rcases isClopen_iff.mp hA_clopen with hA_empty | hA_univ
    · exfalso
      rw [hA_empty] at hxA
      exact hxA
    · exact hA_univ
  apply X.IsSheaf.section_ext
  intro y hy
  have hyA : (⟨y, hy⟩ : V) ∈ A := by
    rw [hA_eq_univ]
    trivial
  obtain ⟨W, hyW, iWV₁, iWV₂, hW_eq⟩ := X.presheaf.germ_eq y hy hy s t hyA
  refine ⟨W, iWV₁.le, hyW, ?_⟩
  have hi : iWV₁ = iWV₂ := by
    exact Subsingleton.elim _ _
  rw [hi] at hW_eq
  exact hW_eq

/-- Analytic-style local nonvanishing hypothesis: for every section, its nonvanishing locus is open.
-/
class NonvanishingLocusIsOpen (X : LocallyRingedSpace) : Prop where
  isOpen_nonvanishing :
    ∀ {U : TopologicalSpace.Opens X} (s : X.presheaf.obj (op U)),
      IsOpen { x : X | ∃ hx : x ∈ U, X.presheaf.germ U x hx s ≠ 0 }

instance (X : LocallyRingedSpace) [LocallyConnectedSpace X] [UniqueContinuation X] :
    NonvanishingLocusIsOpen X where
  isOpen_nonvanishing {U} s := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    rcases hx with ⟨hxU, hx_ne_zero⟩
    let V : TopologicalSpace.Opens X :=
      ⟨connectedComponentIn (U : Set X) x, U.isOpen.connectedComponentIn⟩
    have hxV : x ∈ V := by
      change x ∈ connectedComponentIn (U : Set X) x
      exact mem_connectedComponentIn hxU
    let i : V ⟶ U := homOfLE (connectedComponentIn_subset (U : Set X) x)
    have hV_preconnected : IsPreconnected (V : Set X) := by
      change IsPreconnected (connectedComponentIn (U : Set X) x)
      exact isPreconnected_connectedComponentIn
    use (V : Set X)
    refine ⟨?_, V.isOpen, hxV⟩
    intro y hyV
    have hyU : y ∈ U := i.le hyV
    refine ⟨hyU, ?_⟩
    intro hy_zero
    have hy_zero' :
        X.presheaf.germ V y hyV (X.presheaf.map i.op s) =
          X.presheaf.germ V y hyV 0 := by
      rw [X.presheaf.germ_res_apply (i := i) y hyV s, map_zero]
      exact hy_zero
    have hV_zero : X.presheaf.map i.op s = 0 :=
      UniqueContinuation.eq_of_germ_eq (X := X) (U := V) hV_preconnected
        (X.presheaf.map i.op s) 0 hyV hy_zero'
    have hx_zero : X.presheaf.germ U x hxU s = 0 := by
      rw [← X.presheaf.germ_res_apply (i := i) x hxV s, hV_zero, map_zero]
    exact hx_ne_zero hx_zero

/-- The map on stalks from the meromorphic presheaf to its sheafification is an isomorphism. -/
noncomputable def meromorphicPresheafStalkToSheafStalkIso (X : LocallyRingedSpace) (x : X) :
    X.meromorphicPresheaf.stalk x ≅ X.meromorphicStalk x := by
  let f := (TopCat.Presheaf.stalkFunctor CommRingCat x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat) X.meromorphicPresheaf)
  have hf : IsIso f :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat X.meromorphicPresheaf
  exact @CategoryTheory.asIso _ _ _ _ f hf

lemma meromorphicSubmonoid_mem_iff (X : LocallyRingedSpace) {U : TopologicalSpace.Opens X}
    (s : X.presheaf.obj (op U)) :
    s ∈ X.meromorphicSubmonoidPresheaf.obj (op U) ↔
      ∀ y : U, X.presheaf.germ U y.1 y.2 s ∈ (X.presheaf.stalk y.1)⁰ := by
  change s ∈ ⨅ y : U, Submonoid.comap (X.presheaf.germ U y.1 y.2).hom ((X.presheaf.stalk y.1)⁰) ↔
      ∀ y : U, X.presheaf.germ U y.1 y.2 s ∈ (X.presheaf.stalk y.1)⁰
  simp [Submonoid.mem_iInf]

lemma mem_meromorphicSubmonoid_of_nonzero_representative (X : LocallyRingedSpace)
    [HasDomainStalks X] [NonvanishingLocusIsOpen X]
    {U : TopologicalSpace.Opens X} (s : X.presheaf.obj (op U)) {x : X} (hx : x ∈ U)
    (hs : X.presheaf.germ U x hx s ≠ 0) :
    ∃ (V : TopologicalSpace.Opens X) (i : V ⟶ U) (_ : x ∈ V),
      X.presheaf.map i.op s ∈ X.meromorphicSubmonoidPresheaf.obj (op V) := by
  let W : Set X := { y : X | ∃ hy : y ∈ U, X.presheaf.germ U y hy s ≠ 0 }
  have hW_open : IsOpen W :=
    NonvanishingLocusIsOpen.isOpen_nonvanishing (X := X) s
  have hxW : x ∈ W := ⟨hx, hs⟩
  let V : TopologicalSpace.Opens X := ⟨W, hW_open⟩
  have hxV : x ∈ V := hxW
  let i : V ⟶ U := homOfLE (by
    intro y hyV
    exact (hyV : y ∈ W).choose)
  refine ⟨V, i, hxV, ?_⟩
  rw [meromorphicSubmonoid_mem_iff]
  intro y
  let _ : Nontrivial (X.presheaf.stalk y.1) := inferInstance
  have hyW : y.1 ∈ W := y.2
  have hy_ne_zero : X.presheaf.germ U y.1 ((show y.1 ∈ U from i.le y.2)) s ≠ 0 :=
    hyW.choose_spec
  have hy_ne_zero' : X.presheaf.germ V y.1 y.2 (X.presheaf.map i.op s) ≠ 0 := by
    simpa [X.presheaf.germ_res_apply (i := i) y.1 y.2 s] using hy_ne_zero
  exact mem_nonZeroDivisors_iff_ne_zero.mpr hy_ne_zero'

lemma meromorphicPresheafObj_nontrivial (X : LocallyRingedSpace) [HasDomainStalks X]
    {U : TopologicalSpace.Opens X} {x : X} (hx : x ∈ U) :
    Nontrivial (X.meromorphicPresheaf.obj (op U)) := by
  let M := X.meromorphicSubmonoidPresheaf.obj (op U)
  change Nontrivial (Localization M)
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h01
  have hEq :
      IsLocalization.mk' (Localization M) 0 (1 : M) =
        IsLocalization.mk' (Localization M) 1 (1 : M) := by
    rw [IsLocalization.mk'_one, IsLocalization.mk'_one, map_zero, map_one]
    exact h01
  obtain ⟨m, hm⟩ := (IsLocalization.eq (M := M) (S := Localization M)).mp hEq
  have hm_zero : (m : X.presheaf.obj (op U)) = 0 := by
    have hm' : (0 : X.presheaf.obj (op U)) = (m : X.presheaf.obj (op U)) := by
      simpa [mul_zero, mul_one] using hm
    exact hm'.symm
  have hm_mem : (X.presheaf.germ U x hx) (m : X.presheaf.obj (op U)) ∈ (X.presheaf.stalk x)⁰ := by
    have hm_mem' : (m : X.presheaf.obj (op U)) ∈ X.meromorphicSubmonoidPresheaf.obj (op U) := m.2
    rw [meromorphicSubmonoid_mem_iff] at hm_mem'
    exact hm_mem' ⟨x, hx⟩
  have hm_ne_zero : (X.presheaf.germ U x hx) (m : X.presheaf.obj (op U)) ≠ 0 :=
    nonZeroDivisors.ne_zero hm_mem
  apply hm_ne_zero
  rw [hm_zero, map_zero]

lemma meromorphicPresheafStalk_nontrivial (X : LocallyRingedSpace) [HasDomainStalks X] (x : X) :
    Nontrivial (X.meromorphicPresheaf.stalk x) := by
  refine ⟨⟨X.meromorphicPresheaf.Γgerm x 0, X.meromorphicPresheaf.Γgerm x 1, ?_⟩⟩
  intro h01
  obtain ⟨V, hxV, i₁, i₂, hVeq⟩ := X.meromorphicPresheaf.germ_eq x
    (show x ∈ (⊤ : TopologicalSpace.Opens X.toTopCat) by trivial)
    (show x ∈ (⊤ : TopologicalSpace.Opens X.toTopCat) by trivial) 0 1 h01
  let _ : Nontrivial (X.meromorphicPresheaf.obj (op V)) :=
    meromorphicPresheafObj_nontrivial (X := X) hxV
  have hVeq' : (0 : X.meromorphicPresheaf.obj (op V)) = 1 := by
    have htmp := hVeq
    simp [map_zero, map_one] at htmp
  exact zero_ne_one hVeq'

lemma isUnit_or_eq_zero_meromorphicPresheafStalk (X : LocallyRingedSpace)
    [HasDomainStalks X] [NonvanishingLocusIsOpen X]
    (x : X) (z : X.meromorphicPresheaf.stalk x) : IsUnit z ∨ z = 0 := by
  obtain ⟨U, hxU, t, rfl⟩ := X.meromorphicPresheaf.exists_germ_eq z
  let M := X.meromorphicSubmonoidPresheaf.obj (op U)
  have ht :
      ∃ a : X.presheaf.obj (op U), ∃ b : M, IsLocalization.mk' (Localization M) a b = t := by
    simpa using (IsLocalization.exists_mk'_eq (M := M) (S := Localization M) t)
  obtain ⟨a, b, rfl⟩ := ht
  by_cases ha0 : X.presheaf.germ U x hxU a = 0
  · right
    obtain ⟨V, i, hxV, hVzero⟩ :=
      X.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero U a ⟨x, hxU⟩ ha0
    let MV := X.meromorphicSubmonoidPresheaf.obj (op V)
    have hmap_zero :
        X.meromorphicPresheaf.map i.op (IsLocalization.mk' (Localization M) a b) =
          0 := by
      change (IsLocalization.map (Localization MV) (X.presheaf.map i.op).hom
        (X.meromorphicSubmonoidPresheaf.map i.op)) (IsLocalization.mk' (Localization M) a b) = 0
      simpa [hVzero] using
        (IsLocalization.map_mk' (Q := Localization MV)
          (g := (X.presheaf.map i.op).hom) (hy := X.meromorphicSubmonoidPresheaf.map i.op) a b)
    rw [← X.meromorphicPresheaf.germ_res_apply i x hxV
      (IsLocalization.mk' (Localization M) a b), hmap_zero, map_zero]
  · left
    obtain ⟨V, i, hxV, haVmem⟩ :=
      mem_meromorphicSubmonoid_of_nonzero_representative (X := X) a hxU ha0
    let MV := X.meromorphicSubmonoidPresheaf.obj (op V)
    let aV : MV := ⟨X.presheaf.map i.op a, haVmem⟩
    let bV : MV := ⟨X.presheaf.map i.op b.1, X.meromorphicSubmonoidPresheaf.map i.op b.2⟩
    have hmap_unit :
        IsUnit (X.meromorphicPresheaf.map i.op
          (IsLocalization.mk' (Localization M) a b)) := by
      change IsUnit ((IsLocalization.map (Localization MV) (X.presheaf.map i.op).hom
        (X.meromorphicSubmonoidPresheaf.map i.op)) (IsLocalization.mk' (Localization M) a b))
      have hmap_eq :
          (IsLocalization.map (Localization MV) (X.presheaf.map i.op).hom
            (X.meromorphicSubmonoidPresheaf.map i.op)) (IsLocalization.mk' (Localization M) a b) =
              IsLocalization.mk' (Localization MV) (X.presheaf.map i.op a) bV := by
        simpa [bV] using
          (IsLocalization.map_mk' (Q := Localization MV)
            (g := (X.presheaf.map i.op).hom) (hy := X.meromorphicSubmonoidPresheaf.map i.op) a b)
      rw [hmap_eq]
      refine isUnit_iff_exists_inv.mpr ?_
      refine ⟨IsLocalization.mk' (Localization MV) (bV : X.presheaf.obj (op V)) aV, ?_⟩
      simpa [aV, bV] using
        (IsLocalization.mk'_mul_mk'_eq_one (S := Localization MV) aV bV)
    have hgerm_unit :
        IsUnit (X.meromorphicPresheaf.germ U x hxU
          (IsLocalization.mk' (Localization M) a b)) := by
      rw [← X.meromorphicPresheaf.germ_res_apply i x hxV
        (IsLocalization.mk' (Localization M) a b)]
      exact RingHom.isUnit_map (X.meromorphicPresheaf.germ V x hxV).hom hmap_unit
    exact hgerm_unit

instance (X : LocallyRingedSpace) [HasDomainStalks X] [NonvanishingLocusIsOpen X] :
    HasNontrivialMeromorphicStalks X where
  nontrivial_stalk x := by
    let e := X.meromorphicPresheafStalkToSheafStalkIso x
    rcases meromorphicPresheafStalk_nontrivial (X := X) x with ⟨⟨a, b, hab⟩⟩
    refine ⟨⟨e.hom.hom a, e.hom.hom b, ?_⟩⟩
    intro h
    apply hab
    have h' := congrArg e.inv.hom h
    simpa using h'

instance (X : LocallyRingedSpace) [HasDomainStalks X] [NonvanishingLocusIsOpen X] :
    HasZeroOrUnitMeromorphicStalks X where
  isUnit_or_eq_zero_stalk x z := by
    let e := X.meromorphicPresheafStalkToSheafStalkIso x
    rcases isUnit_or_eq_zero_meromorphicPresheafStalk (X := X) x (e.inv.hom z) with h | h
    · left
      simpa using RingHom.isUnit_map e.hom.hom h
    · right
      have h' := congrArg e.hom.hom h
      simpa using h'

instance (X : LocallyRingedSpace) [HasFieldMeromorphicStalks X] :
    HasNontrivialMeromorphicStalks X where
  nontrivial_stalk x := (HasFieldMeromorphicStalks.isField_stalk (X := X) x).nontrivial

instance (X : LocallyRingedSpace) [HasFieldMeromorphicStalks X] :
    HasZeroOrUnitMeromorphicStalks X where
  isUnit_or_eq_zero_stalk x z :=
    let _ : Field (X.meromorphicStalk x) :=
      (HasFieldMeromorphicStalks.isField_stalk (X := X) x).toField
    by
      by_cases hz : z = 0
      · exact Or.inr hz
      · exact Or.inl (isUnit_iff_ne_zero.mpr hz)

lemma meromorphicGlobalSections_eq_zero_of_forall_germ_eq_zero (X : LocallyRingedSpace)
    (s : X.meromorphicGlobalSections)
    (h : ∀ x : X, X.meromorphicSheaf.presheaf.Γgerm x s = 0) :
    s = 0 := by
  apply TopCat.Presheaf.section_ext X.meromorphicSheaf ⊤ s 0
  intro x hx
  rw [map_zero]
  have hx0 : X.meromorphicSheaf.presheaf.Γgerm x s = 0 := h x
  exact hx0

lemma zero_ne_one_meromorphicGlobalSections (X : LocallyRingedSpace)
    [Nonempty X] [HasNontrivialMeromorphicStalks X] :
    (0 : X.meromorphicGlobalSections) ≠ 1 := by
  let x : X := Classical.choice inferInstance
  let _ : Nontrivial (X.meromorphicStalk x) :=
    HasNontrivialMeromorphicStalks.nontrivial_stalk (X := X) x
  intro h01
  have hEq := congrArg (fun t => (X.meromorphicSheaf.presheaf.Γgerm x).hom t) h01
  have hEq' : (0 : X.meromorphicStalk x) = 1 := by
    calc
      (0 : X.meromorphicStalk x) = (X.meromorphicSheaf.presheaf.Γgerm x).hom 0 := by
        exact (X.meromorphicSheaf.presheaf.Γgerm x).hom.map_zero.symm
      _ = (X.meromorphicSheaf.presheaf.Γgerm x).hom 1 := hEq
      _ = (1 : X.meromorphicStalk x) := by
        exact (X.meromorphicSheaf.presheaf.Γgerm x).hom.map_one
  exact zero_ne_one hEq'

/--
On a connected locally ringed space whose meromorphic stalks are nontrivial and every element is
either a unit or zero, the global meromorphic sections form a field.

This is the analytic-style argument: a nonzero meromorphic section is invertible on a nonempty
clopen basic open, hence on all of a connected space.
-/
theorem isField_meromorphicGlobalSections (X : LocallyRingedSpace) [ConnectedSpace X]
    [HasNontrivialMeromorphicStalks X] [HasZeroOrUnitMeromorphicStalks X] :
    IsField X.meromorphicGlobalSections := by
  let Y := X.meromorphicRingedSpace
  let _ : ConnectedSpace Y := by
    change ConnectedSpace X
    infer_instance
  refine
    { exists_pair_ne := ?_
      mul_comm := fun a b => mul_comm a b
      mul_inv_cancel := ?_ }
  · exact ⟨0, 1, zero_ne_one_meromorphicGlobalSections X⟩
  · intro s hs
    let sY : Y.presheaf.obj (op (⊤ : TopologicalSpace.Opens Y)) := s
    let U : Set Y := { x | IsUnit (Y.presheaf.Γgerm x sY) }
    have hU_nonempty : U.Nonempty := by
      classical
      by_contra hU_empty
      have hzero : ∀ x : X, X.meromorphicSheaf.presheaf.Γgerm x s = 0 := by
        intro x
        let xY : Y := x
        have hx_notunit : ¬ IsUnit (Y.presheaf.Γgerm xY sY) := by
          have hx_notin : xY ∉ U := by
            intro hxU
            exact hU_empty ⟨xY, hxU⟩
          simpa [U] using hx_notin
        rcases HasZeroOrUnitMeromorphicStalks.isUnit_or_eq_zero_stalk (X := X) x
            (X.meromorphicSheaf.presheaf.Γgerm x s) with hx_unit | hx_zero
        · exact False.elim (hx_notunit hx_unit)
        · exact hx_zero
      exact hs (meromorphicGlobalSections_eq_zero_of_forall_germ_eq_zero X s hzero)
    have hU_open : IsOpen U := by
      rw [isOpen_iff_forall_mem_open]
      intro x hx
      obtain ⟨V, i, hxV, hV_unit⟩ :=
        Y.isUnit_res_of_isUnit_germ (⊤ : TopologicalSpace.Opens Y) sY x trivial hx
      use (V : Set Y)
      refine ⟨?_, V.isOpen, hxV⟩
      · intro z hzV
        change IsUnit (Y.presheaf.Γgerm z sY)
        have hz_unit' : IsUnit (Y.presheaf.germ V z hzV (Y.presheaf.map i.op sY)) :=
          RingHom.isUnit_map (Y.presheaf.germ V z hzV).hom hV_unit
        simpa [Y.presheaf.Γgerm_res_apply (i := i) z hzV sY] using hz_unit'
    have hU_compl_open : IsOpen Uᶜ := by
      rw [isOpen_iff_forall_mem_open]
      intro x hx
      have hx_notunit : ¬ IsUnit (Y.presheaf.Γgerm x sY) := by
        simpa [U] using hx
      have hx_zero : Y.presheaf.Γgerm x sY = 0 := by
        rcases HasZeroOrUnitMeromorphicStalks.isUnit_or_eq_zero_stalk (X := X) x
            (Y.presheaf.Γgerm x sY) with hx_unit | hx_zero
        · exact False.elim (hx_notunit hx_unit)
        · exact hx_zero
      obtain ⟨V, i, hxV, hVzero⟩ :=
        Y.exists_res_eq_zero_of_germ_eq_zero (⊤ : TopologicalSpace.Opens Y) sY
          ⟨x, show x ∈ (⊤ : TopologicalSpace.Opens Y) by trivial⟩ hx_zero
      use (V : Set Y)
      refine ⟨?_, V.isOpen, hxV⟩
      · intro z hzV
        change ¬ IsUnit (Y.presheaf.Γgerm z sY)
        intro hz_unit
        let _ : Nontrivial (Y.presheaf.stalk z) :=
          HasNontrivialMeromorphicStalks.nontrivial_stalk (X := X) z
        have hz_zero : Y.presheaf.germ V z hzV (Y.presheaf.map i.op sY) = 0 := by
          rw [hVzero, map_zero]
        have hz_nonzero : Y.presheaf.germ V z hzV (Y.presheaf.map i.op sY) ≠ 0 := by
          rw [Y.presheaf.Γgerm_res_apply (i := i) z hzV sY]
          exact IsUnit.ne_zero hz_unit
        exact hz_nonzero hz_zero
    have hU_eq_univ : U = Set.univ := by
      rcases (isClopen_iff (α := Y)).1 ⟨by
        simpa using hU_compl_open.isClosed_compl, hU_open⟩ with hEmpty | hUniv
      · exact False.elim (Set.not_nonempty_iff_eq_empty.mpr hEmpty hU_nonempty)
      · exact hUniv
    have hs_unit : IsUnit sY := by
      apply Y.isUnit_of_isUnit_germ (⊤ : TopologicalSpace.Opens Y) sY
      intro x hx
      have hx_mem : x ∈ U := by simp [hU_eq_univ]
      exact hx_mem
    exact hs_unit.exists_right_inv

/-- Analytic-style corollary: domain stalks plus local persistence of nonzero germs suffice for
the global meromorphic sections to form a field on a connected space. -/
theorem isField_meromorphicGlobalSections_of_domain_stalks (X : LocallyRingedSpace)
    [ConnectedSpace X] [HasDomainStalks X] [NonvanishingLocusIsOpen X] :
    IsField X.meromorphicGlobalSections :=
  isField_meromorphicGlobalSections X

/-- Analytic-style corollary packaged through unique continuation on locally connected spaces. -/
theorem isField_meromorphicGlobalSections_of_uniqueContinuation (X : LocallyRingedSpace)
    [ConnectedSpace X] [LocallyConnectedSpace X] [HasDomainStalks X] [UniqueContinuation X] :
    IsField X.meromorphicGlobalSections := by
  let _ : NonvanishingLocusIsOpen X := inferInstance
  exact isField_meromorphicGlobalSections_of_domain_stalks X

/-- Open-cover version of the analytic criterion: if local connectedness, domain stalks, and unique
continuation can all be checked on an open cover of a connected space, then the global
meromorphic sections form a field. -/
theorem isField_meromorphicGlobalSections_of_open_cover (X : LocallyRingedSpace) {ι : Type*}
    [ConnectedSpace X] (U : ι → TopologicalSpace.Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hloc : ∀ i, LocallyConnectedSpace (U i)) (hdomain : ∀ i, HasDomainStalksOn X (U i))
    (huc : ∀ i, UniqueContinuationOn X (U i)) :
    IsField X.meromorphicGlobalSections := by
  let _ : LocallyConnectedSpace X := locallyConnectedSpace_of_open_cover X U hcover hloc
  let _ : HasDomainStalks X := hasDomainStalks_of_open_cover X U hcover hdomain
  let _ : UniqueContinuation X := uniqueContinuation_of_open_cover X U hcover huc
  exact isField_meromorphicGlobalSections_of_uniqueContinuation X

end LocallyRingedSpace
end AlgebraicGeometry
