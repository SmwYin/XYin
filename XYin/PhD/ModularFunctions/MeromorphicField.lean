/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, Samuel Yin
-/
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Topology.Perfect
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.RingTheory.Valuation.Basic

/-!
# The field of meromorphic functions

Functions meromorphic on a set `U` form a subring `MeromorphicOn.subring 𝕜 U` of the ring of all
functions `𝕜 → 𝕜`. This ring is never a field: functions supported on discrete sets are zero
divisors. Passing to germs with respect to the filter `Filter.codiscreteWithin U` remedies this:
the image `MeromorphicOn.germRing 𝕜 U` of the subring in the germ ring carries a natural
pointwise inverse, and if `U` is preconnected with at least two points, it is a field.

## Main definitions and results

* `MeromorphicOn.germRing 𝕜 U`: germs of meromorphic functions along `codiscreteWithin U`, with
  the field instance `MeromorphicOn.GermRing.instField` under `Fact` assumptions on `U`.
* `MeromorphicOn.GermRing.orderAt`, `MeromorphicOn.GermRing.orderAtAddValuation`: the order of a
  germ at a point of `U`, and the associated additive valuation.
* `MeromorphicOn.GermRing.divisor`: the divisor of a germ, additive on products of nonzero germs.
* `MeromorphicOn.GermRing.toNF`: the canonical representative of a germ, in normal form.
* `UpperHalfPlane.MeromorphicField`: the field of meromorphic functions on the upper half-plane,
  with canonical representatives `UpperHalfPlane.MeromorphicField.toFun : ℍ → ℂ` and the
  constructor `UpperHalfPlane.MeromorphicField.ofMeromorphic`.

## Implementation notes

The codiscrete germ field and its normal-form API are adapted from Stefan Kebekus's
ProjectVD, pinned at commit `9c218722ad71e9bd2ba357892bc835c8c648aaa8`:
<https://github.com/kebekus/ProjectVD/tree/9c218722ad71e9bd2ba357892bc835c8c648aaa8/VD/Field>.
The five source files are `CodiscreteWithinEventually.lean`, `CodiscreteWithinNeBot.lean`,
`MeromorphicGermZero.lean`, `GermField.lean`, and `GermFieldAPI.lean`.
This port reuses mathlib's codiscrete filters, isolated-zero theorem, and normal forms.

`MeromorphicOn.germRing` is the actual image of meromorphic functions in the codiscrete
quotient of functions; no fraction-field replacement is used. The key input for the field
structure is the identity theorem for meromorphic functions: on a preconnected set, a
meromorphic function whose germ is nonzero has finite order everywhere
(`MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall`), so its zero set is codiscrete
within `U` and the pointwise inverse is a genuine inverse
(`MeromorphicOn.self_mul_inv_eventuallyEq_one_codiscreteWithin`). The upper-half-plane
specialization adds canonical representatives on `ℍ`.
-/

open Filter Set Topology

/-!
## Eventual statements along the filter `codiscreteWithin`

A predicate that holds eventually along every punctured neighborhood of every point of `U` holds
eventually along `codiscreteWithin U`, for arbitrary sets `U`. For open `U`, the converse holds as
well.
-/

section Codiscrete

variable {X Y : Type*} [TopologicalSpace X] {U : Set X} {p : X → Prop} {f g : X → Y}

/--
A predicate holds eventually along `codiscreteWithin U` if it holds eventually along the
punctured neighborhood of every point of `U`.
-/
theorem Filter.eventually_codiscreteWithin_of_forall_eventually_nhdsNE
    (h : ∀ x ∈ U, ∀ᶠ y in 𝓝[≠] x, p y) : ∀ᶠ y in codiscreteWithin U, p y :=
  mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun x hx ↦
    mem_of_superset (h x hx) subset_union_left

/--
Two functions agree along `codiscreteWithin U` if they agree along the punctured neighborhood
of every point of `U`.
-/
theorem Filter.eventuallyEq_codiscreteWithin_of_forall_eventuallyEq_nhdsNE
    (h : ∀ x ∈ U, f =ᶠ[𝓝[≠] x] g) : f =ᶠ[codiscreteWithin U] g :=
  eventually_codiscreteWithin_of_forall_eventually_nhdsNE h

/--
On an open set `U`, a predicate holds eventually along `codiscreteWithin U` if and only if it
holds eventually along the punctured neighborhood of every point of `U`.
-/
theorem Filter.eventually_codiscreteWithin_iff_forall_eventually_nhdsNE (hU : IsOpen U) :
    (∀ᶠ y in codiscreteWithin U, p y) ↔ ∀ x ∈ U, ∀ᶠ y in 𝓝[≠] x, p y := by
  refine ⟨fun h x hx ↦ ?_, eventually_codiscreteWithin_of_forall_eventually_nhdsNE⟩
  have := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x hx
  filter_upwards [this, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)] with z hz h₂z
  exact hz.resolve_right fun h₃z ↦ h₃z h₂z

/--
On an open set `U`, two functions agree along `codiscreteWithin U` if and only if they agree
along the punctured neighborhood of every point of `U`. This is the `EventuallyEq` version of
`Filter.eventually_codiscreteWithin_iff_forall_eventually_nhdsNE`.
-/
theorem Filter.eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE (hU : IsOpen U) :
    f =ᶠ[codiscreteWithin U] g ↔ ∀ x ∈ U, f =ᶠ[𝓝[≠] x] g :=
  eventually_codiscreteWithin_iff_forall_eventually_nhdsNE hU

/--
A predicate holds eventually along `codiscrete X` if and only if it holds eventually along the
punctured neighborhood of every point.
-/
theorem Filter.eventually_codiscrete_iff_forall_eventually_nhdsNE :
    (∀ᶠ y in codiscrete X, p y) ↔ ∀ x, ∀ᶠ y in 𝓝[≠] x, p y := by
  simp [codiscrete, eventually_codiscreteWithin_iff_forall_eventually_nhdsNE isOpen_univ]

end Codiscrete

/-!
## Nontriviality of the filter `codiscreteWithin`

The filter `Filter.codiscreteWithin S` is not the bottom filter iff `S` is not discrete, and in
particular whenever `S` has an accumulation point in itself, whenever `S` is preperfect and
nonempty, or whenever `S` is preconnected with more than one point. Nontriviality of
`codiscreteWithin S` guarantees that the germ ring `Filter.Germ (codiscreteWithin S) 𝕜` is
nontrivial.
-/

section NeBot

variable {X : Type*} [TopologicalSpace X] {S : Set X} {x : X}

/-- The filter `codiscreteWithin S` is nontrivial iff `S` is not discrete. -/
theorem Filter.codiscreteWithin_neBot_iff : (codiscreteWithin S).NeBot ↔ ¬IsDiscrete S := by
  rw [neBot_iff, not_iff_not, codiscreteWithin_eq_bot_iff]

/-- The filter `codiscreteWithin S` is nontrivial if some point of `S` is an accumulation point
of `S`. -/
theorem AccPt.codiscreteWithin_neBot (hx : x ∈ S) (h : AccPt x (𝓟 S)) :
    (codiscreteWithin S).NeBot := by
  have := accPt_principal_iff_nhdsWithin.1 h
  exact neBot_of_le (le_iSup₂ (f := fun x _ ↦ 𝓝[S \ {x}] x) x hx)

/-- The filter `codiscreteWithin S` is nontrivial if `S` is preperfect and nonempty. -/
theorem Preperfect.codiscreteWithin_neBot (hS : Preperfect S) (hne : S.Nonempty) :
    (codiscreteWithin S).NeBot := by
  obtain ⟨x, hx⟩ := hne
  exact (hS x hx).codiscreteWithin_neBot hx

/-- The filter `codiscreteWithin S` is nontrivial if `S` is preconnected and has at least two
points. -/
theorem IsPreconnected.codiscreteWithin_neBot [T1Space X] (hS : IsPreconnected S)
    (h2S : S.Nontrivial) : (codiscreteWithin S).NeBot :=
  (hS.preperfect_of_nontrivial h2S).codiscreteWithin_neBot h2S.nonempty

end NeBot

/-!
## Vanishing germs of meromorphic functions

On a preperfect set, the meromorphic functions on `U` that vanish along `codiscreteWithin U` are
exactly the functions of infinite order at every point of `U`; on a preconnected set with at
least two points, infinite order at a single point suffices. As a complement, a function of
finite order everywhere satisfies `f * f⁻¹ =ᶠ[codiscreteWithin U] 1`. These are the key
ingredients in the construction of the field of meromorphic functions on a connected set, where
they identify the invertible germs.
-/

section VanishingGerms

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f : 𝕜 → E} {s : 𝕜 → 𝕜'} {U : Set 𝕜}

/--
A function meromorphic on a preperfect set `U` vanishes along `codiscreteWithin U` iff it has
infinite order at every point of `U`.
-/
theorem MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top
    (hf : MeromorphicOn f U) (hU : Preperfect U) :
    f =ᶠ[codiscreteWithin U] 0 ↔ ∀ x ∈ U, meromorphicOrderAt f x = ⊤ := by
  constructor
  · intro h x hx
    exact meromorphicOrderAt_eq_top_iff.2
      ((hf x hx).eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin hx (hU x hx) h)
  · intro h
    exact eventuallyEq_codiscreteWithin_of_forall_eventuallyEq_nhdsNE fun x hx ↦
      meromorphicOrderAt_eq_top_iff.1 (h x hx)

/--
A function meromorphic on a preconnected set `U` with at least two points vanishes along
`codiscreteWithin U` iff it has infinite order at one point of `U`.
-/
theorem MeromorphicOn.eventuallyEq_zero_codiscreteWithin_iff_exists_meromorphicOrderAt_eq_top
    (hf : MeromorphicOn f U) (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) :
    f =ᶠ[codiscreteWithin U] 0 ↔ ∃ x ∈ U, meromorphicOrderAt f x = ⊤ := by
  have hU : Preperfect U := h₁U.preperfect_of_nontrivial h₂U
  rw [hf.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top hU]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h₂U.nonempty
    exact ⟨x, hx, h x hx⟩
  · rintro ⟨x, h₁x, h₂x⟩ y hy
    by_contra hcon
    exact (hf.exists_meromorphicOrderAt_ne_top_iff_forall
      ⟨h₂U.nonempty, h₁U⟩).1 ⟨⟨y, hy⟩, hcon⟩ ⟨x, h₁x⟩ h₂x

/--
If a function meromorphic on `U` has finite order at every point of `U`, then `f * f⁻¹` equals
one along `codiscreteWithin U`.
-/
theorem MeromorphicOn.self_mul_inv_eventuallyEq_one_codiscreteWithin (hs : MeromorphicOn s U)
    (h : ∀ x ∈ U, meromorphicOrderAt s x ≠ ⊤) :
    s * s⁻¹ =ᶠ[codiscreteWithin U] 1 :=
  (hs.codiscreteWithin_setOfPred_ne_zero h).mono
    fun _ hz ↦ mul_inv_cancel₀ hz

end VanishingGerms

section NormalForm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜} {U : Set 𝕜}

/-- Negation preserves meromorphic normal form at a point. -/
theorem MeromorphicNFAt.neg (hf : MeromorphicNFAt f x) : MeromorphicNFAt (-f) x := by
  convert hf.smul_analytic (analyticAt_const (v := (-1 : 𝕜))) (by simp) using 1
  funext z
  simp

/-- Negation preserves meromorphic normal form on a set. -/
theorem MeromorphicNFOn.neg (hf : MeromorphicNFOn f U) : MeromorphicNFOn (-f) U :=
  fun _ hz ↦ (hf hz).neg

end NormalForm

/-!
## The field of meromorphic functions on a connected set

Functions meromorphic on a set `U` form the subring `MeromorphicOn.subring 𝕜 U`; its image
`MeromorphicOn.germRing 𝕜 U` in the germ ring along `codiscreteWithin U` carries the pointwise
inverse, and is a field if `U` is preconnected with at least two points.
-/

section Germs

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {f g : 𝕜 → 𝕜} {x : 𝕜}

namespace MeromorphicOn

/-!
### The Ring of Meromorphic Functions
-/

/-- Functions meromorphic on `U`, as a subring of the ring of all functions `𝕜 → 𝕜`. -/
def subring (𝕜 : Type*) [NontriviallyNormedField 𝕜] (U : Set 𝕜) : Subring (𝕜 → 𝕜) where
  carrier := {f | MeromorphicOn f U}
  zero_mem' := const 0
  one_mem' := const 1
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  neg_mem' hf := hf.neg

@[simp]
theorem mem_subring_iff : f ∈ subring 𝕜 U ↔ MeromorphicOn f U := Iff.rfl

/-!
### The Ring of Meromorphic Germs
-/

/--
Germs of meromorphic functions with respect to the filter `codiscreteWithin U`, as a subring of
the ring of all germs. If `U` is preconnected with at least two points, this ring is a field, see
`MeromorphicOn.GermRing.instField`.
-/
def germRing (𝕜 : Type*) [NontriviallyNormedField 𝕜] (U : Set 𝕜) :
    Subring (Germ (codiscreteWithin U) 𝕜) :=
  (subring 𝕜 U).map (Germ.coeRingHom _)

/-- Membership in `germRing 𝕜 U` means: the germ has a meromorphic representative. -/
theorem mem_germRing_iff {γ : Germ (codiscreteWithin U) 𝕜} :
    γ ∈ germRing 𝕜 U ↔ ∃ f : 𝕜 → 𝕜, MeromorphicOn f U ∧ (f : Germ (codiscreteWithin U) 𝕜) = γ :=
  ⟨fun ⟨f, hf, h⟩ ↦ ⟨f, hf, h⟩, fun ⟨f, hf, h⟩ ↦ ⟨f, hf, h⟩⟩

/-- The germ of a meromorphic function lies in `germRing 𝕜 U`. -/
theorem coe_mem_germRing (hf : MeromorphicOn f U) :
    (f : Germ (codiscreteWithin U) 𝕜) ∈ germRing 𝕜 U :=
  mem_germRing_iff.2 ⟨f, hf, rfl⟩

/-- The surjective ring homomorphism mapping a meromorphic function to its germ. -/
def toGermRingHom : subring 𝕜 U →+* germRing 𝕜 U :=
  ((Germ.coeRingHom _).comp (subring 𝕜 U).subtype).codRestrict _
    fun f ↦ coe_mem_germRing f.2

theorem toGermRingHom_surjective :
    Function.Surjective (toGermRingHom (𝕜 := 𝕜) (U := U)) := by
  rintro ⟨γ, hγ⟩
  obtain ⟨f, hf, rfl⟩ := mem_germRing_iff.1 hγ
  exact ⟨⟨f, hf⟩, rfl⟩

namespace GermRing

/-!
### Inverses in the Ring of Meromorphic Germs

The ring of meromorphic germs inherits the pointwise inverse of germs, using the junk-value
convention `(0 : 𝕜)⁻¹ = 0`: the inverse of a function meromorphic on `U` is meromorphic on `U`,
so the subring is closed under `Inv` without any hypotheses on `U`.
-/

noncomputable instance : Inv (germRing 𝕜 U) where
  inv a := ⟨(a : Germ (codiscreteWithin U) 𝕜)⁻¹, by
    obtain ⟨f, hf, hfa⟩ := mem_germRing_iff.1 a.2
    exact mem_germRing_iff.2 ⟨f⁻¹, hf.inv, by rw [Germ.coe_inv, hfa]⟩⟩

@[simp, norm_cast]
theorem coe_inv (a : germRing 𝕜 U) :
    ((a⁻¹ : germRing 𝕜 U) : Germ (codiscreteWithin U) 𝕜) = (a : Germ (codiscreteWithin U) 𝕜)⁻¹ :=
  rfl

noncomputable instance : Div (germRing 𝕜 U) where
  div a b := a * b⁻¹

theorem div_eq_mul_inv (a b : germRing 𝕜 U) : a / b = a * b⁻¹ := rfl

@[simp, norm_cast]
theorem coe_div (a b : germRing 𝕜 U) :
    ((a / b : germRing 𝕜 U) : Germ (codiscreteWithin U) 𝕜) =
      (a : Germ (codiscreteWithin U) 𝕜) / (b : Germ (codiscreteWithin U) 𝕜) := by
  rw [div_eq_mul_inv, division_def]
  push_cast
  rfl

protected theorem inv_zero : (0 : germRing 𝕜 U)⁻¹ = 0 := by
  apply Subtype.ext
  rw [coe_inv]
  change ((0 : 𝕜 → 𝕜) : Germ (codiscreteWithin U) 𝕜)⁻¹ = ((0 : 𝕜 → 𝕜) : Germ _ 𝕜)
  rw [← Germ.coe_inv, Germ.coe_eq]
  filter_upwards with x
  simp

/-!
### Nontriviality and the Field Structure
-/

/-- The ring of meromorphic germs is nontrivial whenever `codiscreteWithin U` is nontrivial. -/
theorem nontrivial (h : (codiscreteWithin U).NeBot) : Nontrivial (germRing 𝕜 U) := by
  refine ⟨0, 1, fun hcon ↦ ?_⟩
  have h₂ : ((0 : 𝕜 → 𝕜) : Germ (codiscreteWithin U) 𝕜) = ((1 : 𝕜 → 𝕜) : Germ _ 𝕜) :=
    congrArg Subtype.val hcon
  obtain ⟨x, hx⟩ := (Germ.coe_eq.1 h₂).exists
  exact zero_ne_one (α := 𝕜) hx

instance [h₁U : Fact (IsPreconnected U)] [h₂U : Fact U.Nontrivial] :
    Nontrivial (germRing 𝕜 U) :=
  nontrivial (h₁U.out.codiscreteWithin_neBot h₂U.out)

/--
The germ of a function meromorphic on a preperfect set `U` vanishes iff the function has
infinite order at every point of `U`.
-/
theorem coe_eq_zero_iff (hf : MeromorphicOn f U) (hU : Preperfect U) :
    (f : Germ (codiscreteWithin U) 𝕜) = 0 ↔ ∀ x ∈ U, meromorphicOrderAt f x = ⊤ := by
  rw [show (0 : Germ (codiscreteWithin U) 𝕜) = ((0 : 𝕜 → 𝕜) : Germ _ 𝕜) from rfl, Germ.coe_eq]
  exact hf.eventuallyEq_zero_codiscreteWithin_iff_forall_meromorphicOrderAt_eq_top hU

/--
On a preconnected set with at least two points, every nonzero meromorphic germ is invertible,
with the pointwise inverse as its inverse.
-/
protected theorem mul_inv_cancel (h₁U : IsPreconnected U) (h₂U : U.Nontrivial)
    {a : germRing 𝕜 U} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  obtain ⟨f, hf, hfa⟩ := mem_germRing_iff.1 a.2
  have horder : ∀ x ∈ U, meromorphicOrderAt f x ≠ ⊤ := by
    intro x hx htop
    apply ha
    apply Subtype.ext
    rw [← hfa]
    exact Germ.coe_eq.mpr
      ((hf.eventuallyEq_zero_codiscreteWithin_iff_exists_meromorphicOrderAt_eq_top
        h₁U h₂U).mpr ⟨x, hx, htop⟩)
  apply Subtype.ext
  push_cast
  rw [← hfa, ← Germ.coe_inv, ← Germ.coe_mul,
    show (1 : Germ (codiscreteWithin U) 𝕜) = ((1 : 𝕜 → 𝕜) : Germ _ 𝕜) from rfl, Germ.coe_eq]
  exact hf.self_mul_inv_eventuallyEq_one_codiscreteWithin horder

/-- On a preconnected set with at least two points, the ring of meromorphic germs is a field. -/
theorem isField (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) : IsField (germRing 𝕜 U) where
  exists_pair_ne := (nontrivial (h₁U.codiscreteWithin_neBot h₂U)).exists_pair_ne
  mul_comm := mul_comm
  mul_inv_cancel ha := ⟨_, GermRing.mul_inv_cancel h₁U h₂U ha⟩

/--
The field of meromorphic functions on a preconnected set with at least two points: field
instance for the ring of meromorphic germs, with the pointwise inverse.
-/
noncomputable instance instField [h₁U : Fact (IsPreconnected U)] [h₂U : Fact U.Nontrivial] :
    Field (germRing 𝕜 U) where
  __ := (inferInstance : CommRing (germRing 𝕜 U))
  inv := Inv.inv
  div := Div.div
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := exists_pair_ne _
  mul_inv_cancel _ ha := GermRing.mul_inv_cancel h₁U.out h₂U.out ha
  inv_zero := GermRing.inv_zero
  nnqsmul := _
  qsmul := _

/-- On a preconnected set with at least two points, the ring of meromorphic germs is a domain. -/
theorem isDomain (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) : IsDomain (germRing 𝕜 U) :=
  have : Fact (IsPreconnected U) := ⟨h₁U⟩
  have : Fact U.Nontrivial := ⟨h₂U⟩
  inferInstance

end GermRing

end MeromorphicOn

/-!
## Supporting API for the field of meromorphic functions

The basic objects attached to the ring `MeromorphicOn.germRing 𝕜 U` of meromorphic germs are the
embedding of constants `MeromorphicOn.GermRing.constRingHom` and the associated `Algebra 𝕜`
instance; the order `MeromorphicOn.GermRing.orderAt` of a germ at a point of `U`, additive on
products; the divisor `MeromorphicOn.GermRing.divisor`, additive on products of nonzero germs;
and the canonical representative `MeromorphicOn.GermRing.toNF` of a germ, in normal form. On an
open set, this is the unique normal-form representative, up to values outside of `U`. Since
functions in normal form are not stable under addition or multiplication, this is a section of
`MeromorphicOn.toGermRingHom` as a map of sets, not a ring homomorphism.

The definitions choose a meromorphic representative of the germ; the accompanying congruence
lemmas show independence of that choice on preperfect sets.
-/

namespace MeromorphicOn.GermRing

/-!
### Choice of Representatives
-/

/-- A choice of meromorphic representative of a germ in `germRing 𝕜 U`. -/
noncomputable def out (a : germRing 𝕜 U) : 𝕜 → 𝕜 := (mem_germRing_iff.1 a.2).choose

/-- The chosen representative is meromorphic on `U`. -/
theorem meromorphicOn_out (a : germRing 𝕜 U) : MeromorphicOn (out a) U :=
  (mem_germRing_iff.1 a.2).choose_spec.1

@[simp]
theorem coe_out (a : germRing 𝕜 U) :
    ((out a : 𝕜 → 𝕜) : Germ (codiscreteWithin U) 𝕜) = a :=
  (mem_germRing_iff.1 a.2).choose_spec.2

/-- Any representative of a germ agrees with the chosen one along `codiscreteWithin U`. -/
theorem out_eventuallyEq {a : germRing 𝕜 U}
    (hfa : (f : Germ (codiscreteWithin U) 𝕜) = a) : f =ᶠ[codiscreteWithin U] out a :=
  Germ.coe_eq.1 (by rw [hfa, coe_out])

/-!
### The Embedding of Constants
-/

/-- The ring homomorphism mapping a constant to its germ. -/
def constRingHom (𝕜 : Type*) [NontriviallyNormedField 𝕜] (U : Set 𝕜) : 𝕜 →+* germRing 𝕜 U :=
  ((Germ.coeRingHom _).comp (Pi.constRingHom 𝕜 𝕜)).codRestrict _
    fun c ↦ coe_mem_germRing (const c)

@[simp]
theorem coe_constRingHom (c : 𝕜) :
    ((constRingHom 𝕜 U c : germRing 𝕜 U) : Germ (codiscreteWithin U) 𝕜) =
      ((fun _ ↦ c : 𝕜 → 𝕜) : Germ (codiscreteWithin U) 𝕜) :=
  rfl

/-- If `codiscreteWithin U` is nontrivial, distinct constants have distinct germs. -/
theorem constRingHom_injective (h : (codiscreteWithin U).NeBot) :
    Function.Injective (constRingHom 𝕜 U) := by
  intro c d hcd
  obtain ⟨x, hx⟩ := (Germ.coe_eq.1 (congrArg Subtype.val hcd)).exists
  exact hx

/-- The ring of meromorphic germs is a `𝕜`-algebra, with constants acting as scalars. -/
noncomputable instance : Algebra 𝕜 (germRing 𝕜 U) := (constRingHom 𝕜 U).toAlgebra

theorem algebraMap_eq_constRingHom :
    algebraMap 𝕜 (germRing 𝕜 U) = constRingHom 𝕜 U := rfl

/-!
### Order at a Point
-/

/-- The order of a meromorphic germ at a point, defined as the order of the chosen
representative. On preperfect sets, this is the order of any representative, see
`MeromorphicOn.GermRing.orderAt_coe`. -/
noncomputable def orderAt (a : germRing 𝕜 U) (x : 𝕜) : WithTop ℤ :=
  meromorphicOrderAt (out a) x

/-- On preperfect sets, the order of a germ at a point of `U` equals the order of any
meromorphic representative. -/
theorem orderAt_coe (hU : Preperfect U) (hf : MeromorphicOn f U) (hx : x ∈ U)
    {a : germRing 𝕜 U} (hfa : (f : Germ (codiscreteWithin U) 𝕜) = a) :
    orderAt a x = meromorphicOrderAt f x :=
  (meromorphicOrderAt_congr
    ((hf x hx).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (meromorphicOn_out a x hx) hx hU (out_eventuallyEq hfa))).symm

/-- The order at points of a preperfect set is additive on products of germs. -/
theorem orderAt_mul (hU : Preperfect U) (hx : x ∈ U) (a b : germRing 𝕜 U) :
    orderAt (a * b) x = orderAt a x + orderAt b x := by
  rw [orderAt_coe hU ((meromorphicOn_out a).mul (meromorphicOn_out b)) hx
    (by push_cast [coe_out]; rfl)]
  exact meromorphicOrderAt_mul (meromorphicOn_out a x hx) (meromorphicOn_out b x hx)

/-- On a preperfect set, a germ vanishes iff its order is infinite at every point of `U`. -/
theorem eq_zero_iff_forall_orderAt_eq_top (hU : Preperfect U) {a : germRing 𝕜 U} :
    a = 0 ↔ ∀ x ∈ U, orderAt a x = ⊤ := by
  rw [Subtype.ext_iff, ← coe_out a]
  exact coe_eq_zero_iff (meromorphicOn_out a) hU

/-- On a preconnected set with at least two points, nonzero germs have finite order at every
point of `U`. In particular, `orderAt · x` restricts to a `ℤ`-valued valuation on the field of
meromorphic germs, see `MeromorphicOn.GermRing.orderAtAddValuation`. -/
theorem orderAt_ne_top (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) {a : germRing 𝕜 U}
    (ha : a ≠ 0) (hx : x ∈ U) : orderAt a x ≠ ⊤ := by
  have hU := h₁U.preperfect_of_nontrivial h₂U
  have h : ¬∀ y ∈ U, orderAt a y = ⊤ := fun h ↦ ha ((eq_zero_iff_forall_orderAt_eq_top hU).2 h)
  push Not at h
  obtain ⟨y, hy, hne⟩ := h
  exact ((meromorphicOn_out a).exists_meromorphicOrderAt_ne_top_iff_forall
    ⟨h₂U.nonempty, h₁U⟩).1 ⟨⟨y, hy⟩, hne⟩ ⟨x, hx⟩

/-- The zero germ has infinite order at every point of a preperfect set. -/
@[simp]
theorem orderAt_zero (hU : Preperfect U) (hx : x ∈ U) : orderAt (0 : germRing 𝕜 U) x = ⊤ :=
  (eq_zero_iff_forall_orderAt_eq_top hU).1 rfl x hx

/-- The unit germ has order zero at every point of a preperfect set. -/
@[simp]
theorem orderAt_one (hU : Preperfect U) (hx : x ∈ U) : orderAt (1 : germRing 𝕜 U) x = 0 := by
  classical
  rw [orderAt_coe hU (f := fun _ ↦ 1) (MeromorphicOn.const 1) hx rfl]
  simp [meromorphicOrderAt_const]

/-- A nonzero constant germ has order zero at every point of a preperfect set. -/
theorem orderAt_algebraMap (hU : Preperfect U) (hx : x ∈ U) {c : 𝕜} (hc : c ≠ 0) :
    orderAt (algebraMap 𝕜 (germRing 𝕜 U) c) x = 0 := by
  classical
  rw [orderAt_coe hU (f := fun _ ↦ c) (MeromorphicOn.const c) hx rfl]
  simp [meromorphicOrderAt_const, hc]

/-- The order of the negative of a germ is the order of the germ. -/
@[simp]
theorem orderAt_neg (hU : Preperfect U) (hx : x ∈ U) (a : germRing 𝕜 U) :
    orderAt (-a) x = orderAt a x := by
  rw [orderAt_coe hU (meromorphicOn_out a).neg hx (by rw [Germ.coe_neg, coe_out]; rfl),
    ← meromorphicOrderAt_neg]
  rfl

/-- The order of the inverse of a germ is the negative of the order. -/
@[simp]
theorem orderAt_inv (hU : Preperfect U) (hx : x ∈ U) (a : germRing 𝕜 U) :
    orderAt a⁻¹ x = -orderAt a x := by
  rw [orderAt_coe hU (meromorphicOn_out a).inv hx (by rw [Germ.coe_inv, coe_out, coe_inv]),
    meromorphicOrderAt_inv]
  rfl

/-- The order of a quotient of germs is the difference of the orders. -/
theorem orderAt_div (hU : Preperfect U) (hx : x ∈ U) (a b : germRing 𝕜 U) :
    orderAt (a / b) x = orderAt a x - orderAt b x := by
  rw [div_eq_mul_inv, orderAt_mul hU hx, orderAt_inv hU hx, sub_eq_add_neg]

/-- The order of a sum of germs is at least the minimum of the orders of the summands. -/
theorem min_orderAt_le_orderAt_add (hU : Preperfect U) (hx : x ∈ U) (a b : germRing 𝕜 U) :
    min (orderAt a x) (orderAt b x) ≤ orderAt (a + b) x := by
  rw [orderAt_coe hU ((meromorphicOn_out a).add (meromorphicOn_out b)) hx (a := a + b)
    (by push_cast [coe_out]; rfl), orderAt, orderAt]
  exact meromorphicOrderAt_add (meromorphicOn_out a x hx) (meromorphicOn_out b x hx)

/-- On a preperfect set, the order at a point `x ∈ U` is an additive valuation on the ring of
meromorphic germs. -/
noncomputable def orderAtAddValuation (hU : Preperfect U) (hx : x ∈ U) :
    AddValuation (germRing 𝕜 U) (WithTop ℤ) :=
  AddValuation.of (orderAt · x) (orderAt_zero hU hx) (orderAt_one hU hx)
    (min_orderAt_le_orderAt_add hU hx) (fun a b ↦ orderAt_mul hU hx a b)

@[simp]
theorem orderAtAddValuation_apply (hU : Preperfect U) (hx : x ∈ U) (a : germRing 𝕜 U) :
    orderAtAddValuation hU hx a = orderAt a x :=
  rfl

/-!
### The Divisor of a Germ
-/

/-- The divisor of a meromorphic germ, defined as the divisor of the chosen representative. On
preperfect sets, this is the divisor of any representative, see
`MeromorphicOn.GermRing.divisor_coe`. -/
noncomputable def divisor (a : germRing 𝕜 U) : Function.locallyFinsuppWithin U ℤ :=
  MeromorphicOn.divisor (out a) U

/-- On preperfect sets, the divisor of a germ equals the divisor of any meromorphic
representative. -/
theorem divisor_coe (hU : Preperfect U) (hf : MeromorphicOn f U) {a : germRing 𝕜 U}
    (hfa : (f : Germ (codiscreteWithin U) 𝕜) = a) :
    divisor a = MeromorphicOn.divisor f U :=
  divisor_of_eventuallyEq_codiscreteWithin_preperfect (meromorphicOn_out a) hf hU
    (out_eventuallyEq hfa).symm

/-- On a preconnected set with at least two points, the divisor is additive on products of
nonzero germs. In particular, it restricts to a group homomorphism on the units of the field of
meromorphic germs. -/
theorem divisor_mul (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) {a b : germRing 𝕜 U}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    divisor (a * b) = divisor a + divisor b := by
  have hU := h₁U.preperfect_of_nontrivial h₂U
  rw [divisor_coe hU ((meromorphicOn_out a).mul (meromorphicOn_out b))
    (by push_cast [coe_out]; rfl)]
  exact MeromorphicOn.divisor_mul (meromorphicOn_out a) (meromorphicOn_out b)
    (fun z hz ↦ orderAt_ne_top h₁U h₂U ha hz) (fun z hz ↦ orderAt_ne_top h₁U h₂U hb hz)

/-- On a preperfect set, the divisor of the inverse germ is the negative of the divisor. -/
theorem divisor_inv (hU : Preperfect U) (a : germRing 𝕜 U) : divisor a⁻¹ = -divisor a := by
  rw [divisor_coe hU (meromorphicOn_out a).inv (by rw [Germ.coe_inv, coe_out, coe_inv])]
  exact MeromorphicOn.divisor_inv

/-- On a preperfect set, the divisor of the zero germ vanishes. -/
@[simp]
theorem divisor_zero (hU : Preperfect U) : divisor (0 : germRing 𝕜 U) = 0 := by
  rw [divisor_coe hU (f := fun _ ↦ 0) (MeromorphicOn.const 0) rfl]
  exact MeromorphicOn.divisor_const 0

/-- On a preperfect set, the divisor of the unit germ vanishes. -/
@[simp]
theorem divisor_one (hU : Preperfect U) : divisor (1 : germRing 𝕜 U) = 0 := by
  rw [divisor_coe hU (f := fun _ ↦ 1) (MeromorphicOn.const 1) rfl]
  exact MeromorphicOn.divisor_const 1

/-- On a preperfect set, the divisor of a constant germ vanishes. -/
@[simp]
theorem divisor_algebraMap (hU : Preperfect U) (c : 𝕜) :
    divisor (algebraMap 𝕜 (germRing 𝕜 U) c) = 0 := by
  rw [divisor_coe hU (f := fun _ ↦ c) (MeromorphicOn.const c) rfl]
  exact MeromorphicOn.divisor_const c

/-- On a preconnected set with at least two points, the divisor of a quotient of nonzero germs
is the difference of the divisors. -/
theorem divisor_div (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) {a b : germRing 𝕜 U}
    (ha : a ≠ 0) (hb : b ≠ 0) : divisor (a / b) = divisor a - divisor b := by
  have : Fact (IsPreconnected U) := ⟨h₁U⟩
  have : Fact U.Nontrivial := ⟨h₂U⟩
  rw [div_eq_mul_inv, divisor_mul h₁U h₂U ha (inv_ne_zero hb),
    divisor_inv (h₁U.preperfect_of_nontrivial h₂U), sub_eq_add_neg]

/-!
### The Normal Form Representative
-/

/-- The canonical representative of a meromorphic germ: the normal form of the chosen
representative. On open sets, this is the unique representative in normal form, up to values
outside of `U`, see `MeromorphicOn.GermRing.eqOn_toNF_of_meromorphicNFOn`.

Since functions in normal form are not stable under addition or multiplication, `toNF` is a
section of `MeromorphicOn.toGermRingHom` as a map of sets, not a ring homomorphism. -/
noncomputable def toNF (a : germRing 𝕜 U) : 𝕜 → 𝕜 := toMeromorphicNFOn (out a) U

/-- The canonical representative is in normal form. -/
theorem meromorphicNFOn_toNF (a : germRing 𝕜 U) : MeromorphicNFOn (toNF a) U :=
  meromorphicNFOn_toMeromorphicNFOn (out a) U

/-- The canonical representative represents the germ. -/
@[simp]
theorem coe_toNF (a : germRing 𝕜 U) :
    ((toNF a : 𝕜 → 𝕜) : Germ (codiscreteWithin U) 𝕜) = a := by
  rw [← coe_out a]
  exact (Germ.coe_eq.2 (toMeromorphicNFOn_eqOn_codiscrete (meromorphicOn_out a))).symm

/-- The map `toNF` is a section of the quotient map `toGermRingHom`. -/
theorem toGermRingHom_toNF (a : germRing 𝕜 U) :
    toGermRingHom ⟨toNF a, (meromorphicNFOn_toNF a).meromorphicOn⟩ = a :=
  Subtype.ext (coe_toNF a)

/-- On open sets, any normal-form representative of a germ agrees with the canonical
representative on `U`. Off `U`, representatives of the germ are unconstrained, so this is the
strongest possible uniqueness statement. -/
theorem eqOn_toNF_of_meromorphicNFOn (hU : IsOpen U) {a : germRing 𝕜 U}
    (h₁g : MeromorphicNFOn g U) (h₂g : (g : Germ (codiscreteWithin U) 𝕜) = a) :
    Set.EqOn g (toNF a) U := by
  intro x hx
  have h₁ : g =ᶠ[codiscreteWithin U] toNF a := Germ.coe_eq.1 (by rw [h₂g, coe_toNF])
  have h₂ : g =ᶠ[𝓝[≠] x] toNF a :=
    (eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE hU).1 h₁ x hx
  have h₃ : g =ᶠ[𝓝 x] toNF a :=
    ((h₁g hx).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (meromorphicNFOn_toNF a hx)).1 h₂
  exact h₃.eq_of_nhds

end MeromorphicOn.GermRing

end Germs

/-!
## Canonical representatives on the upper half-plane
-/

open scoped Manifold

namespace UpperHalfPlane

instance instFactIsPreconnectedUpperHalfPlaneSet : Fact (IsPreconnected upperHalfPlaneSet) :=
  ⟨(convex_halfSpace_im_gt 0).isPreconnected⟩

instance instFactNontrivialUpperHalfPlaneSet : Fact upperHalfPlaneSet.Nontrivial := by
  refine ⟨Complex.I, by simp, 2 * Complex.I, by simp, ?_⟩
  intro h
  have := congrArg Complex.im h
  norm_num at this

/-- Punctured neighborhoods in `ℍ` correspond to punctured neighborhoods in `ℂ` under
`ofComplex`. -/
theorem eventually_nhdsNE_comp_ofComplex_iff {p : ℍ → Prop} {τ : ℍ} :
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), p (ofComplex z)) ↔ ∀ᶠ w in 𝓝[≠] τ, p w := by
  have h := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq {(τ : ℂ)}ᶜ τ
  rw [show ((↑) : ℍ → ℂ) ⁻¹' {(τ : ℂ)}ᶜ = {τ}ᶜ by ext; simp] at h
  rw [← h, eventually_map]
  simp only [ofComplex_apply]

/-- The filter `codiscreteWithin upperHalfPlaneSet` on `ℂ` corresponds to the filter
`codiscrete ℍ` under `ofComplex`. -/
theorem eventually_codiscreteWithin_comp_ofComplex_iff {p : ℍ → Prop} :
    (∀ᶠ z in codiscreteWithin upperHalfPlaneSet, p (ofComplex z)) ↔
      ∀ᶠ τ in codiscrete ℍ, p τ := by
  rw [eventually_codiscreteWithin_iff_forall_eventually_nhdsNE isOpen_upperHalfPlaneSet,
    Filter.eventually_codiscrete_iff_forall_eventually_nhdsNE]
  refine ⟨fun h τ ↦ eventually_nhdsNE_comp_ofComplex_iff.1 (h τ τ.im_pos), fun h z hz ↦ ?_⟩
  simpa using eventually_nhdsNE_comp_ofComplex_iff.2 (h ⟨z, hz⟩)

/-- Two functions on `ℍ` in meromorphic normal form which agree on a punctured neighborhood of a
point agree at that point. -/
theorem apply_eq_of_eventuallyEq_nhdsNE {f g : ℍ → ℂ} {τ : ℍ}
    (hf : MeromorphicNFAt (f ∘ ofComplex) τ) (hg : MeromorphicNFAt (g ∘ ofComplex) τ)
    (h : ∀ᶠ w in 𝓝[≠] τ, f w = g w) : f τ = g τ := by
  have h' : f ∘ ofComplex =ᶠ[𝓝[≠] (τ : ℂ)] g ∘ ofComplex :=
    eventually_nhdsNE_comp_ofComplex_iff.2 h
  simpa using ((hf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hg).1 h').eq_of_nhds

/-- A holomorphic function on `ℍ` has meromorphic normal form. -/
theorem _root_.MDifferentiable.meromorphicNFOn_comp_ofComplex {f : ℍ → ℂ} (hf : MDiff f) :
    MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet :=
  ((mdifferentiable_iff.1 hf).analyticOnNhd isOpen_upperHalfPlaneSet).meromorphicNFOn

/-- The field of meromorphic functions on the upper half-plane, modulo agreement away from
discrete sets. Its representatives use the canonical meromorphic normal form. -/
noncomputable abbrev MeromorphicField := MeromorphicOn.germRing ℂ upperHalfPlaneSet

namespace MeromorphicField

open MeromorphicOn MeromorphicOn.GermRing

/-- The canonical normal-form representative of a meromorphic field element on `ℍ`. -/
noncomputable def toFun (a : MeromorphicField) : ℍ → ℂ := fun τ ↦ toNF a τ

/-- The canonical representative has meromorphic normal form on the upper half-plane. -/
theorem meromorphicNFOn_toFun (a : MeromorphicField) :
    MeromorphicNFOn (toFun a ∘ ofComplex) upperHalfPlaneSet := by
  intro z hz
  apply (meromorphicNFAt_congr ?_).1 (meromorphicNFOn_toNF a hz)
  filter_upwards [eventuallyEq_coe_comp_ofComplex hz] with w hw
  exact congrArg (toNF a) hw.symm

/-- A meromorphic function on `ℍ` determines its codiscrete germ. Values at isolated points
need not be preserved by the canonical representative unless the input has normal form. -/
noncomputable def ofMeromorphic (f : ℍ → ℂ)
    (hf : MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet) : MeromorphicField :=
  toGermRingHom ⟨f ∘ ofComplex, hf⟩

/-- A normal-form function is the canonical representative of its codiscrete germ. -/
@[simp]
theorem toFun_ofMeromorphic {f : ℍ → ℂ}
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet) :
    toFun (ofMeromorphic f hf.meromorphicOn) = f := by
  funext τ
  have h := eqOn_toNF_of_meromorphicNFOn isOpen_upperHalfPlaneSet
    (a := ofMeromorphic f hf.meromorphicOn) hf rfl τ.im_pos
  simpa [toFun] using h.symm

/-- Canonical representatives distinguish elements of the meromorphic field. -/
theorem toFun_injective : Function.Injective toFun := by
  intro a b hab
  apply Subtype.ext
  rw [← coe_toNF a, ← coe_toNF b, Germ.coe_eq]
  filter_upwards [self_mem_codiscreteWithin upperHalfPlaneSet] with z hz
  exact congrFun hab ⟨z, hz⟩

/-- A map into the meromorphic field is injective if its canonical representatives are given
by an injective map. -/
theorem injective_of_toFun_eq {α : Type*} {F : α → MeromorphicField} {f : α → ℍ → ℂ}
    (hf : Function.Injective f) (hF : ∀ a, toFun (F a) = f a) : Function.Injective F :=
  fun a b h ↦ hf (by rw [← hF, ← hF, h])

/-- A function on `ℍ` has meromorphic normal form exactly when it is the canonical
representative of an element of the meromorphic field. -/
theorem meromorphicNFOn_iff_exists (f : ℍ → ℂ) :
    MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet ↔
      ∃ a : MeromorphicField, toFun a = f := by
  constructor
  · intro hf
    exact ⟨ofMeromorphic f hf.meromorphicOn, toFun_ofMeromorphic hf⟩
  · rintro ⟨a, rfl⟩
    exact meromorphicNFOn_toFun a

/-- A holomorphic function on `ℍ` defines a canonical element of the meromorphic field. -/
noncomputable def ofHolomorphic (f : ℍ → ℂ) (hf : MDiff f) : MeromorphicField :=
  ofMeromorphic f hf.meromorphicNFOn_comp_ofComplex.meromorphicOn

/-- The canonical representative of a holomorphic function is the original function. -/
@[simp]
theorem toFun_ofHolomorphic (f : ℍ → ℂ) (hf : MDiff f) :
    toFun (ofHolomorphic f hf) = f :=
  toFun_ofMeromorphic hf.meromorphicNFOn_comp_ofComplex

/-!
### `ofMeromorphic` and the field operations

`ofMeromorphic` is compatible with the pointwise operations on functions, and two functions
define the same element iff they agree away from a discrete subset of `ℍ`.
-/

section ofMeromorphic

variable {f g : ℍ → ℂ}

/-- The germ underlying `ofMeromorphic f hf` is the germ of `f ∘ ofComplex`. -/
theorem coe_ofMeromorphic (f : ℍ → ℂ) (hf : MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet) :
    ((ofMeromorphic f hf : MeromorphicField) : Germ (codiscreteWithin upperHalfPlaneSet) ℂ) =
      ((f ∘ ofComplex : ℂ → ℂ) : Germ (codiscreteWithin upperHalfPlaneSet) ℂ) :=
  rfl

/-- Two meromorphic functions define the same element of the meromorphic field iff they agree
away from a discrete subset of `ℍ`. -/
theorem ofMeromorphic_eq_iff (hf : MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet)
    (hg : MeromorphicOn (g ∘ ofComplex) upperHalfPlaneSet) :
    ofMeromorphic f hf = ofMeromorphic g hg ↔ f =ᶠ[codiscrete ℍ] g := by
  rw [Subtype.ext_iff, coe_ofMeromorphic, coe_ofMeromorphic, Germ.coe_eq]
  exact eventually_codiscreteWithin_comp_ofComplex_iff (p := fun τ ↦ f τ = g τ)

/-- Meromorphic functions which agree away from a discrete subset of `ℍ` define the same
element of the meromorphic field. -/
theorem ofMeromorphic_eq_of_eventuallyEq (hf : MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet)
    (hg : MeromorphicOn (g ∘ ofComplex) upperHalfPlaneSet) (h : f =ᶠ[codiscrete ℍ] g) :
    ofMeromorphic f hf = ofMeromorphic g hg :=
  (ofMeromorphic_eq_iff hf hg).2 h

/-- Every element of the meromorphic field is defined by its canonical representative. -/
@[simp]
theorem ofMeromorphic_toFun (a : MeromorphicField) :
    ofMeromorphic (toFun a) (meromorphicNFOn_toFun a).meromorphicOn = a := by
  apply Subtype.ext
  rw [coe_ofMeromorphic, ← coe_toNF a, Germ.coe_eq]
  filter_upwards [self_mem_codiscreteWithin upperHalfPlaneSet] with z hz
  simp [toFun, ofComplex_apply_of_im_pos hz]

/-- The canonical representative of `ofMeromorphic f hf` agrees with `f` away from a discrete
subset of `ℍ`. -/
theorem toFun_eventuallyEq (hf : MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet) :
    toFun (ofMeromorphic f hf) =ᶠ[codiscrete ℍ] f :=
  (ofMeromorphic_eq_iff _ hf).1 (ofMeromorphic_toFun _)

/-- Two elements of the meromorphic field are equal iff their canonical representatives agree
away from a discrete subset of `ℍ`. -/
theorem eq_iff_toFun_eventuallyEq {a b : MeromorphicField} :
    a = b ↔ toFun a =ᶠ[codiscrete ℍ] toFun b := by
  conv_lhs => rw [← ofMeromorphic_toFun a, ← ofMeromorphic_toFun b]
  exact ofMeromorphic_eq_iff _ _

/-- Two functions on `ℍ` in meromorphic normal form which agree away from a discrete subset of
`ℍ` are equal. -/
theorem _root_.UpperHalfPlane.eq_of_meromorphicNFOn_of_eventuallyEq
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet)
    (hg : MeromorphicNFOn (g ∘ ofComplex) upperHalfPlaneSet) (h : f =ᶠ[codiscrete ℍ] g) :
    f = g := by
  rw [← toFun_ofMeromorphic hf, ← toFun_ofMeromorphic hg, (ofMeromorphic_eq_iff _ _).2 h]

theorem ofMeromorphic_zero : ofMeromorphic 0 (MeromorphicOn.const 0) = 0 :=
  rfl

theorem ofMeromorphic_one : ofMeromorphic 1 (MeromorphicOn.const 1) = 1 :=
  rfl

theorem ofMeromorphic_const (c : ℂ) :
    ofMeromorphic (fun _ ↦ c) (MeromorphicOn.const c) = algebraMap ℂ MeromorphicField c :=
  rfl

variable (hf : MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet)
  (hg : MeromorphicOn (g ∘ ofComplex) upperHalfPlaneSet)
include hf hg

theorem ofMeromorphic_add :
    ofMeromorphic (f + g) (hf.add hg) = ofMeromorphic f hf + ofMeromorphic g hg :=
  rfl

theorem ofMeromorphic_sub :
    ofMeromorphic (f - g) (hf.sub hg) = ofMeromorphic f hf - ofMeromorphic g hg :=
  rfl

theorem ofMeromorphic_mul :
    ofMeromorphic (f * g) (hf.mul hg) = ofMeromorphic f hf * ofMeromorphic g hg :=
  rfl

theorem ofMeromorphic_div :
    ofMeromorphic (f / g) (hf.div hg) = ofMeromorphic f hf / ofMeromorphic g hg :=
  rfl

omit hg in
theorem ofMeromorphic_neg : ofMeromorphic (-f) hf.neg = -ofMeromorphic f hf :=
  rfl

omit hg in
theorem ofMeromorphic_inv : ofMeromorphic f⁻¹ hf.inv = (ofMeromorphic f hf)⁻¹ :=
  rfl

end ofMeromorphic

/-!
### Canonical representatives of field operations

Canonical representatives are compatible with negation, inversion and constants. For the other
field operations they agree with the pointwise operation away from a discrete subset of `ℍ`, but
not necessarily at poles.
-/

@[simp]
theorem toFun_zero : toFun (0 : MeromorphicField) = 0 :=
  toFun_ofMeromorphic (f := 0) (analyticOnNhd_const (v := (0 : ℂ))).meromorphicNFOn

@[simp]
theorem toFun_one : toFun (1 : MeromorphicField) = 1 :=
  toFun_ofMeromorphic (f := 1) (analyticOnNhd_const (v := (1 : ℂ))).meromorphicNFOn

/-- The canonical representative of a constant is the constant function. -/
@[simp]
theorem toFun_algebraMap_complex (c : ℂ) :
    toFun (algebraMap ℂ MeromorphicField c) = fun _ ↦ c :=
  toFun_ofMeromorphic (f := fun _ ↦ c) (analyticOnNhd_const (v := c)).meromorphicNFOn

@[simp]
theorem toFun_neg (a : MeromorphicField) : toFun (-a) = -toFun a := by
  conv_lhs => rw [← ofMeromorphic_toFun a, ← ofMeromorphic_neg]
  exact toFun_ofMeromorphic (f := -toFun a) (meromorphicNFOn_toFun a).neg

theorem toFun_add_eventuallyEq (a b : MeromorphicField) :
    toFun (a + b) =ᶠ[codiscrete ℍ] toFun a + toFun b := by
  have ha := (meromorphicNFOn_toFun a).meromorphicOn
  have hb := (meromorphicNFOn_toFun b).meromorphicOn
  have h := toFun_eventuallyEq (f := toFun a + toFun b) (ha.add hb)
  rwa [ofMeromorphic_add ha hb, ofMeromorphic_toFun, ofMeromorphic_toFun] at h

theorem toFun_sub_eventuallyEq (a b : MeromorphicField) :
    toFun (a - b) =ᶠ[codiscrete ℍ] toFun a - toFun b := by
  have ha := (meromorphicNFOn_toFun a).meromorphicOn
  have hb := (meromorphicNFOn_toFun b).meromorphicOn
  have h := toFun_eventuallyEq (f := toFun a - toFun b) (ha.sub hb)
  rwa [ofMeromorphic_sub ha hb, ofMeromorphic_toFun, ofMeromorphic_toFun] at h

theorem toFun_mul_eventuallyEq (a b : MeromorphicField) :
    toFun (a * b) =ᶠ[codiscrete ℍ] toFun a * toFun b := by
  have ha := (meromorphicNFOn_toFun a).meromorphicOn
  have hb := (meromorphicNFOn_toFun b).meromorphicOn
  have h := toFun_eventuallyEq (f := toFun a * toFun b) (ha.mul hb)
  rwa [ofMeromorphic_mul ha hb, ofMeromorphic_toFun, ofMeromorphic_toFun] at h

theorem toFun_div_eventuallyEq (a b : MeromorphicField) :
    toFun (a / b) =ᶠ[codiscrete ℍ] toFun a / toFun b := by
  have ha := (meromorphicNFOn_toFun a).meromorphicOn
  have hb := (meromorphicNFOn_toFun b).meromorphicOn
  have h := toFun_eventuallyEq (f := toFun a / toFun b) (ha.div hb)
  rwa [ofMeromorphic_div ha hb, ofMeromorphic_toFun, ofMeromorphic_toFun] at h

@[simp]
theorem toFun_inv (a : MeromorphicField) : toFun a⁻¹ = (toFun a)⁻¹ := by
  conv_lhs => rw [← ofMeromorphic_toFun a, ← ofMeromorphic_inv]
  exact toFun_ofMeromorphic (f := (toFun a)⁻¹) (meromorphicNFOn_inv.2 (meromorphicNFOn_toFun a))

end MeromorphicField

end UpperHalfPlane
