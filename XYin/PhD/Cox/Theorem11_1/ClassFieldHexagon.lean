/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCohomologyDefs
import Mathlib.GroupTheory.Index

/-!
# Source-local cyclic exact hexagon

Janusz V.1.1–1.4 constructs the connecting homomorphisms by lifts in a short exact
sequence. These relations specify those actual lifts. We use σ−1 in place of the
source's 1−σ; the images and quotient groups agree and the connecting sign changes
consistently. No finiteness of the ambient modules is assumed in the hexagon.
-/

noncomputable section
namespace Cox.CyclicCohomology

variable {G A B C : Type*} [Group G] [Fintype G]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable (ρ : Representation ℤ G A) (τ : Representation ℤ G B)
variable (υ : Representation ℤ G C) (g : G)

/-- An invariant vector's class in the invariant/norm quotient. -/
def zeroClass (x : LinearMap.ker (ρ g - LinearMap.id)) : tateZero ρ g :=
  Submodule.Quotient.mk x

/-- A norm-zero vector's class in the norm-zero/difference quotient. -/
def oneClass (x : LinearMap.ker ρ.norm) : tateOne ρ g :=
  Submodule.Quotient.mk x

/-- An intertwiner commutes with the finite group norm. -/
theorem intertwining_norm (f : ρ.IntertwiningMap τ) (x : A) :
    f (ρ.norm x) = τ.norm (f x) := by
  simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply, map_sum,
    f.isIntertwining]

omit [Fintype G] in
/-- An intertwiner also commutes with the generator difference. -/
theorem intertwining_difference (f : ρ.IntertwiningMap τ) (x : A) :
    f ((ρ g - LinearMap.id : Module.End ℤ A) x) = (τ g - LinearMap.id : Module.End ℤ B) (f x) := by
  change f (ρ g x - x) = τ g (f x) - f x
  rw [map_sub, f.isIntertwining]

/-- The induced map on the zeroth Tate quotient, specified on representatives. -/
theorem exists_tateZeroMap (f : ρ.IntertwiningMap τ) :
    ∃ F : tateZero ρ g →+ tateZero τ g,
      ∀ (x : LinearMap.ker (ρ g - LinearMap.id)) (y : LinearMap.ker (τ g - LinearMap.id)),
        f (x : A) = (y : B) → F (zeroClass ρ g x) = zeroClass τ g y := by
  let φ : LinearMap.ker (ρ g - LinearMap.id) →ₗ[ℤ] LinearMap.ker (τ g - LinearMap.id) :=
    (f.toLinearMap.comp (LinearMap.ker (ρ g - LinearMap.id)).subtype).codRestrict _ fun x => by
      rw [LinearMap.mem_ker]
      change (τ g - LinearMap.id : Module.End ℤ B) (f (x : A)) = 0
      rw [← intertwining_difference ρ τ g f, LinearMap.mem_ker.mp x.2, map_zero]
  have hφ : (LinearMap.range ρ.norm).comap (LinearMap.ker (ρ g - LinearMap.id)).subtype ≤
      ((LinearMap.range τ.norm).comap (LinearMap.ker (τ g - LinearMap.id)).subtype).comap φ := by
    rintro x ⟨y, hy⟩
    refine ⟨f y, ?_⟩
    change τ.norm (f y) = f (x : A)
    rw [← intertwining_norm ρ τ f, hy]
    rfl
  refine ⟨(Submodule.mapQ _ _ φ hφ).toAddMonoidHom, fun x y hxy => ?_⟩
  change Submodule.mapQ _ _ φ hφ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y
  rw [Submodule.mapQ_apply]
  congr 1
  exact Subtype.ext hxy

/-- The actual map induced by an intertwiner on the zeroth Tate quotient. -/
def tateZeroMap (f : ρ.IntertwiningMap τ) : tateZero ρ g →+ tateZero τ g :=
  Classical.choose (exists_tateZeroMap ρ τ g f)

/-- The representative formula for the induced zeroth quotient map. -/
theorem tateZeroMap_apply (f : ρ.IntertwiningMap τ)
    (x : LinearMap.ker (ρ g - LinearMap.id)) (y : LinearMap.ker (τ g - LinearMap.id))
    (hxy : f (x : A) = (y : B)) :
    tateZeroMap ρ τ g f (zeroClass ρ g x) = zeroClass τ g y := by
  exact Classical.choose_spec (exists_tateZeroMap ρ τ g f) x y hxy

/-- The induced map on the oneth Tate quotient, specified on representatives. -/
theorem exists_tateOneMap (f : ρ.IntertwiningMap τ) :
    ∃ F : tateOne ρ g →+ tateOne τ g,
      ∀ (x : LinearMap.ker ρ.norm) (y : LinearMap.ker τ.norm),
        f (x : A) = (y : B) → F (oneClass ρ g x) = oneClass τ g y := by
  let φ : LinearMap.ker ρ.norm →ₗ[ℤ] LinearMap.ker τ.norm :=
    (f.toLinearMap.comp (LinearMap.ker ρ.norm).subtype).codRestrict _ fun x => by
      rw [LinearMap.mem_ker]
      change τ.norm (f (x : A)) = 0
      rw [← intertwining_norm ρ τ f, LinearMap.mem_ker.mp x.2, map_zero]
  have hφ : (LinearMap.range (ρ g - LinearMap.id)).comap (LinearMap.ker ρ.norm).subtype ≤
      ((LinearMap.range (τ g - LinearMap.id)).comap (LinearMap.ker τ.norm).subtype).comap φ := by
    rintro x ⟨y, hy⟩
    refine ⟨f y, ?_⟩
    change (τ g - LinearMap.id : Module.End ℤ B) (f y) = f (x : A)
    rw [← intertwining_difference ρ τ g f, hy]
    rfl
  refine ⟨(Submodule.mapQ _ _ φ hφ).toAddMonoidHom, fun x y hxy => ?_⟩
  change Submodule.mapQ _ _ φ hφ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y
  rw [Submodule.mapQ_apply]
  congr 1
  exact Subtype.ext hxy

/-- The actual map induced by an intertwiner on the oneth Tate quotient. -/
def tateOneMap (f : ρ.IntertwiningMap τ) : tateOne ρ g →+ tateOne τ g :=
  Classical.choose (exists_tateOneMap ρ τ g f)

/-- The representative formula for the induced oneth quotient map. -/
theorem tateOneMap_apply (f : ρ.IntertwiningMap τ)
    (x : LinearMap.ker ρ.norm) (y : LinearMap.ker τ.norm) (hxy : f (x : A) = (y : B)) :
    tateOneMap ρ τ g f (oneClass ρ g x) = oneClass τ g y := by
  exact Classical.choose_spec (exists_tateOneMap ρ τ g f) x y hxy

section FiniteGroups

/-- An exact pair with finite source and target has finite middle group. -/
theorem finite_of_exact [Finite A] [Finite C] (f : A →+ B) (h : B →+ C)
    (hexact : f.range = h.ker) : Finite B := by
  haveI : Finite f.range := (Set.finite_range f).to_subtype
  haveI : Finite h.ker := hexact ▸ (inferInstance : Finite f.range)
  haveI : Finite (B ⧸ h.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange h).symm.toEquiv
  apply Nat.finite_of_card_ne_zero
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup h.ker]
  exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

/-- Kernel and image cardinalities multiply to the cardinality of a finite group. -/
theorem card_eq_ker_mul_range [Finite A] (f : A →+ B) :
    Nat.card A = Nat.card f.ker * Nat.card f.range := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker, mul_comm,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]

variable {D E F : Type*} [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]

/-- Alternating cardinal products agree in a finite exact six-cycle. -/
theorem finite_hexagon_card [Finite A] [Finite B] [Finite C]
    [Finite D] [Finite E] [Finite F]
    (f₀ : A →+ B) (f₁ : B →+ C) (f₂ : C →+ D)
    (f₃ : D →+ E) (f₄ : E →+ F) (f₅ : F →+ A)
    (h₀ : f₅.range = f₀.ker) (h₁ : f₀.range = f₁.ker)
    (h₂ : f₁.range = f₂.ker) (h₃ : f₂.range = f₃.ker)
    (h₄ : f₃.range = f₄.ker) (h₅ : f₄.range = f₅.ker) :
    Nat.card A * Nat.card C * Nat.card E = Nat.card B * Nat.card D * Nat.card F := by
  rw [card_eq_ker_mul_range f₀, card_eq_ker_mul_range f₁, card_eq_ker_mul_range f₂,
    card_eq_ker_mul_range f₃, card_eq_ker_mul_range f₄, card_eq_ker_mul_range f₅,
    ← h₀, ← h₁, ← h₂, ← h₃, ← h₄, ← h₅]
  ring

end FiniteGroups

section SubmoduleSequence

variable (W : Submodule ℤ A) (hW : ∀ x, W ≤ W.comap (ρ x))

omit [Fintype G] in
/-- The stable-submodule inclusion commutes with the inherited action. -/
theorem submodule_isIntertwining (γ : G) (x : W) :
    W.subtype ((ρ.subrepresentation W hW) γ x) = ρ γ (W.subtype x) := by
  rfl

omit [Fintype G] in
/-- The quotient projection commutes with the quotient action. -/
theorem quotient_isIntertwining (γ : G) (x : A) :
    W.mkQ (ρ γ x) = (ρ.quotient W hW) γ (W.mkQ x) := by
  exact (Submodule.mapQ_apply W W (ρ γ) (h := hW γ) x).symm

/-- The actual stable-submodule inclusion as an intertwiner. -/
def submoduleIntertwining : (ρ.subrepresentation W hW).IntertwiningMap ρ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (ρ.subrepresentation W hW) ρ
    W.subtype (submodule_isIntertwining ρ W hW)

/-- The actual quotient projection as an intertwiner. -/
def quotientIntertwining : ρ.IntertwiningMap (ρ.quotient W hW) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap ρ (ρ.quotient W hW)
    W.mkQ (quotient_isIntertwining ρ W hW)

omit [Fintype G] in
/-- The submodule inclusion is injective. -/
theorem submoduleIntertwining_injective :
    Function.Injective (submoduleIntertwining ρ W hW) := by
  exact W.injective_subtype

omit [Fintype G] in
/-- The quotient projection is surjective. -/
theorem quotientIntertwining_surjective :
    Function.Surjective (quotientIntertwining ρ W hW) := by
  exact W.mkQ_surjective

omit [Fintype G] in
/-- The stable submodule is exactly the kernel of its quotient projection. -/
theorem submodule_sequence_exact :
    LinearMap.range (submoduleIntertwining ρ W hW).toLinearMap =
      LinearMap.ker (quotientIntertwining ρ W hW).toLinearMap := by
  change LinearMap.range W.subtype = LinearMap.ker W.mkQ
  rw [Submodule.range_subtype, Submodule.ker_mkQ]

end SubmoduleSequence

section Classes

/-- Every zeroth Tate class has a representative. -/
theorem zeroClass_surjective : Function.Surjective (zeroClass ρ g) :=
  Submodule.Quotient.mk_surjective _

/-- Every first Tate class has a representative. -/
theorem oneClass_surjective : Function.Surjective (oneClass ρ g) :=
  Submodule.Quotient.mk_surjective _

/-- A zeroth Tate class vanishes exactly when its representative is a norm. -/
theorem zeroClass_eq_zero_iff (x : LinearMap.ker (ρ g - LinearMap.id)) :
    zeroClass ρ g x = 0 ↔ ∃ y, ρ.norm y = (x : A) :=
  Submodule.Quotient.mk_eq_zero _

/-- Two zeroth Tate classes agree exactly when their representatives differ by a norm. -/
theorem zeroClass_eq_iff (x x' : LinearMap.ker (ρ g - LinearMap.id)) :
    zeroClass ρ g x = zeroClass ρ g x' ↔ ∃ y, ρ.norm y = (x : A) - x' :=
  Submodule.Quotient.eq _

/-- A first Tate class vanishes exactly when its representative is a generator difference. -/
theorem oneClass_eq_zero_iff (x : LinearMap.ker ρ.norm) :
    oneClass ρ g x = 0 ↔ ∃ y, (ρ g - LinearMap.id : Module.End ℤ A) y = (x : A) :=
  Submodule.Quotient.mk_eq_zero _

/-- Two first Tate classes agree exactly when their representatives differ by a difference. -/
theorem oneClass_eq_iff (x x' : LinearMap.ker ρ.norm) :
    oneClass ρ g x = oneClass ρ g x' ↔
      ∃ y, (ρ g - LinearMap.id : Module.End ℤ A) y = (x : A) - x' :=
  Submodule.Quotient.eq _

omit [Fintype G] in
/-- An intertwiner preserves generator-invariant vectors. -/
theorem map_mem_ker_difference (f : ρ.IntertwiningMap τ)
    (x : LinearMap.ker (ρ g - LinearMap.id)) :
    f (x : A) ∈ LinearMap.ker (τ g - LinearMap.id) := by
  rw [LinearMap.mem_ker, ← intertwining_difference ρ τ g f, LinearMap.mem_ker.mp x.2, map_zero]

/-- An intertwiner preserves norm-zero vectors. -/
theorem map_mem_ker_norm (f : ρ.IntertwiningMap τ) (x : LinearMap.ker ρ.norm) :
    f (x : A) ∈ LinearMap.ker τ.norm := by
  rw [LinearMap.mem_ker, ← intertwining_norm ρ τ f, LinearMap.mem_ker.mp x.2, map_zero]

end Classes

section Connecting

variable (f : ρ.IntertwiningMap τ) (h : τ.IntertwiningMap υ)

/-- The source lift relation defining δ₀: lift c to b and lift (σ−1)b to a. -/
def zeroConnectingRelation (c : tateZero υ g) (a : tateOne ρ g) : Prop :=
  ∃ x : LinearMap.ker (υ g - LinearMap.id), zeroClass υ g x = c ∧
    ∃ b : B, h b = (x : C) ∧
      ∃ y : LinearMap.ker ρ.norm,
        f (y : A) = (τ g - LinearMap.id : Module.End ℤ B) b ∧ oneClass ρ g y = a

/-- The source lift relation defining δ₁: lift c to b and lift Nb to a. -/
def oneConnectingRelation (c : tateOne υ g) (a : tateZero ρ g) : Prop :=
  ∃ x : LinearMap.ker υ.norm, oneClass υ g x = c ∧
    ∃ b : B, h b = (x : C) ∧
      ∃ y : LinearMap.ker (ρ g - LinearMap.id),
        f (y : A) = τ.norm b ∧ zeroClass ρ g y = a

variable (hf : Function.Injective f) (hh : Function.Surjective h)
variable (hexact : LinearMap.range f.toLinearMap = LinearMap.ker h.toLinearMap)
include hf hh hexact

omit [Fintype G] hf hh in
/-- Exactness makes the composite of the two intertwiners vanish. -/
theorem intertwiner_comp_apply (z : A) : h (f z) = 0 :=
  LinearMap.mem_ker.mp (hexact ▸ LinearMap.mem_range_self f.toLinearMap z)

/-- Every zero connecting input has a lift satisfying the defining relation. -/
theorem zeroConnecting_lift (c : tateZero υ g) :
    ∃ a : tateOne ρ g, zeroConnectingRelation ρ τ υ g f h c a := by
  obtain ⟨x, rfl⟩ := zeroClass_surjective υ g c
  obtain ⟨b, hb⟩ := hh (x : C)
  obtain ⟨y, hy⟩ : (τ g - LinearMap.id : Module.End ℤ B) b ∈ LinearMap.range f.toLinearMap := by
    rw [hexact, LinearMap.mem_ker]
    change h ((τ g - LinearMap.id : Module.End ℤ B) b) = 0
    rw [intertwining_difference τ υ g h, hb, LinearMap.mem_ker.mp x.2]
  have hy' : f y = (τ g - LinearMap.id : Module.End ℤ B) b := hy
  have hyN : y ∈ LinearMap.ker ρ.norm := by
    rw [LinearMap.mem_ker]
    apply hf
    rw [intertwining_norm ρ τ f, hy', map_zero]
    exact LinearMap.mem_ker.mp (range_difference_le_ker_norm τ g ⟨b, rfl⟩)
  exact ⟨oneClass ρ g ⟨y, hyN⟩, x, rfl, b, hb, ⟨y, hyN⟩, hy', rfl⟩

/-- Changing representatives and lifts does not change the zero connecting class. -/
theorem zeroConnecting_singleValued (c : tateZero υ g) (a a' : tateOne ρ g)
    (ha : zeroConnectingRelation ρ τ υ g f h c a)
    (ha' : zeroConnectingRelation ρ τ υ g f h c a') : a = a' := by
  obtain ⟨x, hxc, b, hb, y, hy, rfl⟩ := ha
  obtain ⟨x', hxc', b', hb', y', hy', rfl⟩ := ha'
  obtain ⟨z, hz⟩ := (zeroClass_eq_iff υ g x x').mp (hxc.trans hxc'.symm)
  obtain ⟨w, hw⟩ := hh z
  obtain ⟨u, hu⟩ : b - b' - τ.norm w ∈ LinearMap.range f.toLinearMap := by
    rw [hexact, LinearMap.mem_ker]
    change h (b - b' - τ.norm w) = 0
    rw [map_sub, map_sub, intertwining_norm τ υ h, hw, hz, hb, hb', sub_self]
  have hu' : f u = b - b' - τ.norm w := hu
  have hDN : (τ g - LinearMap.id : Module.End ℤ B) (τ.norm w) = 0 :=
    LinearMap.mem_ker.mp (range_norm_le_ker_difference τ g ⟨w, rfl⟩)
  rw [oneClass_eq_iff]
  refine ⟨u, ?_⟩
  apply hf
  rw [intertwining_difference ρ τ g f, hu', map_sub, map_sub, hDN, sub_zero, map_sub, ← hy, ← hy']

omit hf hh hexact in
/-- Adding lifts proves additivity of the zero connecting relation. -/
theorem zeroConnecting_add (c c' : tateZero υ g) (a a' : tateOne ρ g)
    (ha : zeroConnectingRelation ρ τ υ g f h c a)
    (ha' : zeroConnectingRelation ρ τ υ g f h c' a') :
    zeroConnectingRelation ρ τ υ g f h (c + c') (a + a') := by
  obtain ⟨x, hxc, b, hb, y, hy, hya⟩ := ha
  obtain ⟨x', hxc', b', hb', y', hy', hya'⟩ := ha'
  refine ⟨x + x', ?_, b + b', ?_, y + y', ?_, ?_⟩
  · rw [← hxc, ← hxc']
    exact Submodule.Quotient.mk_add _
  · rw [map_add, hb, hb']
    rfl
  · change f ((y : A) + y') = _
    rw [map_add, hy, hy', map_add]
  · rw [← hya, ← hya']
    exact Submodule.Quotient.mk_add _

/-- The zero connecting relation is represented by an actual additive homomorphism. -/
theorem exists_zeroConnecting :
    ∃ δ : tateZero υ g →+ tateOne ρ g,
      ∀ c a, zeroConnectingRelation ρ τ υ g f h c a ↔ δ c = a := by
  choose δ hδ using zeroConnecting_lift ρ τ υ g f h hf hh hexact
  have hzero : zeroConnectingRelation ρ τ υ g f h 0 0 :=
    ⟨0, Submodule.Quotient.mk_zero _, 0, map_zero _, 0, by simp, Submodule.Quotient.mk_zero _⟩
  refine ⟨{ toFun := δ
            map_zero' := zeroConnecting_singleValued ρ τ υ g f h hf hh hexact 0 _ _ (hδ 0) hzero
            map_add' := fun c c' => zeroConnecting_singleValued ρ τ υ g f h hf hh hexact _ _ _
              (hδ (c + c')) (zeroConnecting_add ρ τ υ g f h c c' _ _ (hδ c) (hδ c')) },
    fun c a => ⟨fun ha => zeroConnecting_singleValued ρ τ υ g f h hf hh hexact c _ _ (hδ c) ha,
      fun ha => ha ▸ hδ c⟩⟩

/-- The zero connecting homomorphism chosen from its explicit lift relation. -/
def zeroConnecting : tateZero υ g →+ tateOne ρ g :=
  Classical.choose (exists_zeroConnecting ρ τ υ g f h hf hh hexact)

/-- The lift relation characterizes the chosen zero connecting homomorphism. -/
theorem zeroConnecting_iff (c : tateZero υ g) (a : tateOne ρ g) :
    zeroConnectingRelation ρ τ υ g f h c a ↔
      zeroConnecting ρ τ υ g f h hf hh hexact c = a := by
  exact Classical.choose_spec (exists_zeroConnecting ρ τ υ g f h hf hh hexact) c a

/-- Every one connecting input has a lift satisfying the defining relation. -/
theorem oneConnecting_lift (c : tateOne υ g) :
    ∃ a : tateZero ρ g, oneConnectingRelation ρ τ υ g f h c a := by
  obtain ⟨x, rfl⟩ := oneClass_surjective υ g c
  obtain ⟨b, hb⟩ := hh (x : C)
  obtain ⟨y, hy⟩ : τ.norm b ∈ LinearMap.range f.toLinearMap := by
    rw [hexact, LinearMap.mem_ker]
    change h (τ.norm b) = 0
    rw [intertwining_norm τ υ h, hb, LinearMap.mem_ker.mp x.2]
  have hy' : f y = τ.norm b := hy
  have hyD : y ∈ LinearMap.ker (ρ g - LinearMap.id) := by
    rw [LinearMap.mem_ker]
    apply hf
    rw [intertwining_difference ρ τ g f, hy', map_zero]
    exact LinearMap.mem_ker.mp (range_norm_le_ker_difference τ g ⟨b, rfl⟩)
  exact ⟨zeroClass ρ g ⟨y, hyD⟩, x, rfl, b, hb, ⟨y, hyD⟩, hy', rfl⟩

/-- Changing representatives and lifts does not change the one connecting class. -/
theorem oneConnecting_singleValued (c : tateOne υ g) (a a' : tateZero ρ g)
    (ha : oneConnectingRelation ρ τ υ g f h c a)
    (ha' : oneConnectingRelation ρ τ υ g f h c a') : a = a' := by
  obtain ⟨x, hxc, b, hb, y, hy, rfl⟩ := ha
  obtain ⟨x', hxc', b', hb', y', hy', rfl⟩ := ha'
  obtain ⟨z, hz⟩ := (oneClass_eq_iff υ g x x').mp (hxc.trans hxc'.symm)
  obtain ⟨w, hw⟩ := hh z
  obtain ⟨u, hu⟩ : b - b' - (τ g - LinearMap.id : Module.End ℤ B) w ∈
      LinearMap.range f.toLinearMap := by
    rw [hexact, LinearMap.mem_ker]
    change h (b - b' - (τ g - LinearMap.id : Module.End ℤ B) w) = 0
    rw [map_sub, map_sub, intertwining_difference τ υ g h, hw, hz, hb, hb', sub_self]
  have hu' : f u = b - b' - (τ g - LinearMap.id : Module.End ℤ B) w := hu
  have hND : τ.norm ((τ g - LinearMap.id : Module.End ℤ B) w) = 0 :=
    LinearMap.mem_ker.mp (range_difference_le_ker_norm τ g ⟨w, rfl⟩)
  rw [zeroClass_eq_iff]
  refine ⟨u, ?_⟩
  apply hf
  rw [intertwining_norm ρ τ f, hu', map_sub, map_sub, hND, sub_zero, map_sub, ← hy, ← hy']

omit hf hh hexact in
/-- Adding lifts proves additivity of the one connecting relation. -/
theorem oneConnecting_add (c c' : tateOne υ g) (a a' : tateZero ρ g)
    (ha : oneConnectingRelation ρ τ υ g f h c a)
    (ha' : oneConnectingRelation ρ τ υ g f h c' a') :
    oneConnectingRelation ρ τ υ g f h (c + c') (a + a') := by
  obtain ⟨x, hxc, b, hb, y, hy, hya⟩ := ha
  obtain ⟨x', hxc', b', hb', y', hy', hya'⟩ := ha'
  refine ⟨x + x', ?_, b + b', ?_, y + y', ?_, ?_⟩
  · rw [← hxc, ← hxc']
    exact Submodule.Quotient.mk_add _
  · rw [map_add, hb, hb']
    rfl
  · change f ((y : A) + y') = _
    rw [map_add, hy, hy', map_add]
  · rw [← hya, ← hya']
    exact Submodule.Quotient.mk_add _

/-- The one connecting relation is represented by an actual additive homomorphism. -/
theorem exists_oneConnecting :
    ∃ δ : tateOne υ g →+ tateZero ρ g,
      ∀ c a, oneConnectingRelation ρ τ υ g f h c a ↔ δ c = a := by
  choose δ hδ using oneConnecting_lift ρ τ υ g f h hf hh hexact
  have hzero : oneConnectingRelation ρ τ υ g f h 0 0 :=
    ⟨0, Submodule.Quotient.mk_zero _, 0, map_zero _, 0, by simp, Submodule.Quotient.mk_zero _⟩
  refine ⟨{ toFun := δ
            map_zero' := oneConnecting_singleValued ρ τ υ g f h hf hh hexact 0 _ _ (hδ 0) hzero
            map_add' := fun c c' => oneConnecting_singleValued ρ τ υ g f h hf hh hexact _ _ _
              (hδ (c + c')) (oneConnecting_add ρ τ υ g f h c c' _ _ (hδ c) (hδ c')) },
    fun c a => ⟨fun ha => oneConnecting_singleValued ρ τ υ g f h hf hh hexact c _ _ (hδ c) ha,
      fun ha => ha ▸ hδ c⟩⟩

/-- The one connecting homomorphism chosen from its explicit lift relation. -/
def oneConnecting : tateOne υ g →+ tateZero ρ g :=
  Classical.choose (exists_oneConnecting ρ τ υ g f h hf hh hexact)

/-- The lift relation characterizes the chosen one connecting homomorphism. -/
theorem oneConnecting_iff (c : tateOne υ g) (a : tateZero ρ g) :
    oneConnectingRelation ρ τ υ g f h c a ↔
      oneConnecting ρ τ υ g f h hf hh hexact c = a := by
  exact Classical.choose_spec (exists_oneConnecting ρ τ υ g f h hf hh hexact) c a

/-- Exactness of Janusz's hexagon at A0. -/
theorem hexagon_exact_A0 :
    (oneConnecting ρ τ υ g f h hf hh hexact).range = (tateZeroMap ρ τ g f).ker := by
  ext a
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨x, -, b, -, y, hy, hya⟩ :=
      (oneConnecting_iff ρ τ υ g f h hf hh hexact c _).mpr rfl
    rw [← hya, tateZeroMap_apply ρ τ g f y ⟨f y, map_mem_ker_difference ρ τ g f y⟩ rfl,
      zeroClass_eq_zero_iff]
    exact ⟨b, hy.symm⟩
  · intro ha
    obtain ⟨y, rfl⟩ := zeroClass_surjective ρ g a
    rw [tateZeroMap_apply ρ τ g f y ⟨f y, map_mem_ker_difference ρ τ g f y⟩ rfl,
      zeroClass_eq_zero_iff] at ha
    obtain ⟨b, hb⟩ := ha
    have hx : h b ∈ LinearMap.ker υ.norm := by
      rw [LinearMap.mem_ker, ← intertwining_norm τ υ h, hb]
      exact intertwiner_comp_apply ρ τ υ f h hexact y
    exact ⟨oneClass υ g ⟨h b, hx⟩, (oneConnecting_iff ρ τ υ g f h hf hh hexact _ _).mp
      ⟨⟨h b, hx⟩, rfl, b, rfl, y, hb.symm, rfl⟩⟩

/-- Exactness of Janusz's hexagon at B0. -/
theorem hexagon_exact_B0 :
    (tateZeroMap ρ τ g f).range = (tateZeroMap τ υ g h).ker := by
  ext b'
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨y, rfl⟩ := zeroClass_surjective ρ g a
    rw [tateZeroMap_apply ρ τ g f y ⟨f y, map_mem_ker_difference ρ τ g f y⟩ rfl,
      tateZeroMap_apply τ υ g h ⟨f y, map_mem_ker_difference ρ τ g f y⟩
        ⟨h (f y), map_mem_ker_difference τ υ g h ⟨f y, map_mem_ker_difference ρ τ g f y⟩⟩ rfl,
      zeroClass_eq_zero_iff]
    exact ⟨0, by rw [map_zero]; exact (intertwiner_comp_apply ρ τ υ f h hexact y).symm⟩
  · intro hb'
    obtain ⟨b, rfl⟩ := zeroClass_surjective τ g b'
    rw [tateZeroMap_apply τ υ g h b ⟨h b, map_mem_ker_difference τ υ g h b⟩ rfl,
      zeroClass_eq_zero_iff] at hb'
    obtain ⟨z, hz⟩ := hb'
    obtain ⟨w, hw⟩ := hh z
    obtain ⟨y, hy⟩ : (b : B) - τ.norm w ∈ LinearMap.range f.toLinearMap := by
      rw [hexact, LinearMap.mem_ker]
      change h ((b : B) - τ.norm w) = 0
      rw [map_sub, intertwining_norm τ υ h, hw, hz, sub_self]
    have hy' : f y = (b : B) - τ.norm w := hy
    have hyD : y ∈ LinearMap.ker (ρ g - LinearMap.id) := by
      rw [LinearMap.mem_ker]
      apply hf
      rw [intertwining_difference ρ τ g f, hy', map_sub, LinearMap.mem_ker.mp b.2,
        LinearMap.mem_ker.mp (range_norm_le_ker_difference τ g ⟨w, rfl⟩), sub_zero, map_zero]
    refine ⟨zeroClass ρ g ⟨y, hyD⟩, ?_⟩
    rw [tateZeroMap_apply ρ τ g f ⟨y, hyD⟩ ⟨f y, map_mem_ker_difference ρ τ g f ⟨y, hyD⟩⟩ rfl,
      zeroClass_eq_iff]
    refine ⟨-w, ?_⟩
    change τ.norm (-w) = f y - (b : B)
    rw [map_neg, hy']
    abel

/-- Exactness of Janusz's hexagon at C0. -/
theorem hexagon_exact_C0 :
    (tateZeroMap τ υ g h).range = (zeroConnecting ρ τ υ g f h hf hh hexact).ker := by
  ext c
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨b', rfl⟩
    obtain ⟨b, rfl⟩ := zeroClass_surjective τ g b'
    rw [tateZeroMap_apply τ υ g h b ⟨h b, map_mem_ker_difference τ υ g h b⟩ rfl,
      ← zeroConnecting_iff ρ τ υ g f h hf hh hexact]
    refine ⟨⟨h b, map_mem_ker_difference τ υ g h b⟩, rfl, b, rfl, 0, ?_,
      Submodule.Quotient.mk_zero _⟩
    change f 0 = _
    rw [map_zero, LinearMap.mem_ker.mp b.2]
  · intro hc
    obtain ⟨x, rfl⟩ := zeroClass_surjective υ g c
    obtain ⟨x0, hx0c, b, hb, y, hy, hya⟩ :=
      (zeroConnecting_iff ρ τ υ g f h hf hh hexact _ 0).mpr hc
    rw [oneClass_eq_zero_iff] at hya
    obtain ⟨u, hu⟩ := hya
    have hbD : b - f u ∈ LinearMap.ker (τ g - LinearMap.id) := by
      rw [LinearMap.mem_ker, map_sub, ← intertwining_difference ρ τ g f, hu, hy, sub_self]
    refine ⟨zeroClass τ g ⟨b - f u, hbD⟩, ?_⟩
    rw [tateZeroMap_apply τ υ g h ⟨b - f u, hbD⟩
      ⟨h (b - f u), map_mem_ker_difference τ υ g h ⟨b - f u, hbD⟩⟩ rfl, ← hx0c]
    congr 1
    apply Subtype.ext
    change h (b - f u) = (x0 : C)
    rw [map_sub, intertwiner_comp_apply ρ τ υ f h hexact, sub_zero, hb]

/-- Exactness of Janusz's hexagon at A1. -/
theorem hexagon_exact_A1 :
    (zeroConnecting ρ τ υ g f h hf hh hexact).range = (tateOneMap ρ τ g f).ker := by
  ext a
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨x, -, b, -, y, hy, hya⟩ :=
      (zeroConnecting_iff ρ τ υ g f h hf hh hexact c _).mpr rfl
    rw [← hya, tateOneMap_apply ρ τ g f y ⟨f y, map_mem_ker_norm ρ τ f y⟩ rfl,
      oneClass_eq_zero_iff]
    exact ⟨b, hy.symm⟩
  · intro ha
    obtain ⟨y, rfl⟩ := oneClass_surjective ρ g a
    rw [tateOneMap_apply ρ τ g f y ⟨f y, map_mem_ker_norm ρ τ f y⟩ rfl,
      oneClass_eq_zero_iff] at ha
    obtain ⟨b, hb⟩ := ha
    have hx : h b ∈ LinearMap.ker (υ g - LinearMap.id) := by
      rw [LinearMap.mem_ker, ← intertwining_difference τ υ g h, hb]
      exact intertwiner_comp_apply ρ τ υ f h hexact y
    exact ⟨zeroClass υ g ⟨h b, hx⟩, (zeroConnecting_iff ρ τ υ g f h hf hh hexact _ _).mp
      ⟨⟨h b, hx⟩, rfl, b, rfl, y, hb.symm, rfl⟩⟩

/-- Exactness of Janusz's hexagon at B1. -/
theorem hexagon_exact_B1 :
    (tateOneMap ρ τ g f).range = (tateOneMap τ υ g h).ker := by
  ext b'
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨y, rfl⟩ := oneClass_surjective ρ g a
    rw [tateOneMap_apply ρ τ g f y ⟨f y, map_mem_ker_norm ρ τ f y⟩ rfl,
      tateOneMap_apply τ υ g h ⟨f y, map_mem_ker_norm ρ τ f y⟩
        ⟨h (f y), map_mem_ker_norm τ υ h ⟨f y, map_mem_ker_norm ρ τ f y⟩⟩ rfl,
      oneClass_eq_zero_iff]
    exact ⟨0, by rw [map_zero]; exact (intertwiner_comp_apply ρ τ υ f h hexact y).symm⟩
  · intro hb'
    obtain ⟨b, rfl⟩ := oneClass_surjective τ g b'
    rw [tateOneMap_apply τ υ g h b ⟨h b, map_mem_ker_norm τ υ h b⟩ rfl,
      oneClass_eq_zero_iff] at hb'
    obtain ⟨z, hz⟩ := hb'
    obtain ⟨w, hw⟩ := hh z
    obtain ⟨y, hy⟩ : (b : B) - (τ g - LinearMap.id : Module.End ℤ B) w ∈
        LinearMap.range f.toLinearMap := by
      rw [hexact, LinearMap.mem_ker]
      change h ((b : B) - (τ g - LinearMap.id : Module.End ℤ B) w) = 0
      rw [map_sub, intertwining_difference τ υ g h, hw, hz, sub_self]
    have hy' : f y = (b : B) - (τ g - LinearMap.id : Module.End ℤ B) w := hy
    have hyN : y ∈ LinearMap.ker ρ.norm := by
      rw [LinearMap.mem_ker]
      apply hf
      rw [intertwining_norm ρ τ f, hy', map_sub, LinearMap.mem_ker.mp b.2,
        LinearMap.mem_ker.mp (range_difference_le_ker_norm τ g ⟨w, rfl⟩), sub_zero, map_zero]
    refine ⟨oneClass ρ g ⟨y, hyN⟩, ?_⟩
    rw [tateOneMap_apply ρ τ g f ⟨y, hyN⟩ ⟨f y, map_mem_ker_norm ρ τ f ⟨y, hyN⟩⟩ rfl,
      oneClass_eq_iff]
    refine ⟨-w, ?_⟩
    change (τ g - LinearMap.id : Module.End ℤ B) (-w) = f y - (b : B)
    rw [map_neg, hy']
    abel

/-- Exactness of Janusz's hexagon at C1. -/
theorem hexagon_exact_C1 :
    (tateOneMap τ υ g h).range = (oneConnecting ρ τ υ g f h hf hh hexact).ker := by
  ext c
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨b', rfl⟩
    obtain ⟨b, rfl⟩ := oneClass_surjective τ g b'
    rw [tateOneMap_apply τ υ g h b ⟨h b, map_mem_ker_norm τ υ h b⟩ rfl,
      ← oneConnecting_iff ρ τ υ g f h hf hh hexact]
    refine ⟨⟨h b, map_mem_ker_norm τ υ h b⟩, rfl, b, rfl, 0, ?_,
      Submodule.Quotient.mk_zero _⟩
    change f 0 = _
    rw [map_zero, LinearMap.mem_ker.mp b.2]
  · intro hc
    obtain ⟨x, rfl⟩ := oneClass_surjective υ g c
    obtain ⟨x0, hx0c, b, hb, y, hy, hya⟩ :=
      (oneConnecting_iff ρ τ υ g f h hf hh hexact _ 0).mpr hc
    rw [zeroClass_eq_zero_iff] at hya
    obtain ⟨u, hu⟩ := hya
    have hbN : b - f u ∈ LinearMap.ker τ.norm := by
      rw [LinearMap.mem_ker, map_sub, ← intertwining_norm ρ τ f, hu, hy, sub_self]
    refine ⟨oneClass τ g ⟨b - f u, hbN⟩, ?_⟩
    rw [tateOneMap_apply τ υ g h ⟨b - f u, hbN⟩
      ⟨h (b - f u), map_mem_ker_norm τ υ h ⟨b - f u, hbN⟩⟩ rfl, ← hx0c]
    congr 1
    apply Subtype.ext
    change h (b - f u) = (x0 : C)
    rw [map_sub, intertwiner_comp_apply ρ τ υ f h hexact, sub_zero, hb]

/-- Exactness and finiteness of A and B give finiteness of both Tate groups of C. -/
theorem finiteHerbrand_of_first_middle
    (hA : FiniteHerbrand ρ g) (hB : FiniteHerbrand τ g) : FiniteHerbrand υ g := by
  haveI := hA.1
  haveI := hA.2
  haveI := hB.1
  haveI := hB.2
  exact ⟨finite_of_exact (tateZeroMap τ υ g h) (zeroConnecting ρ τ υ g f h hf hh hexact)
      (hexagon_exact_C0 ρ τ υ g f h hf hh hexact),
    finite_of_exact (tateOneMap τ υ g h) (oneConnecting ρ τ υ g f h hf hh hexact)
      (hexagon_exact_C1 ρ τ υ g f h hf hh hexact)⟩

/-- Exactness and finiteness of A and C give finiteness of both Tate groups of B. -/
theorem finiteHerbrand_of_first_last
    (hA : FiniteHerbrand ρ g) (hC : FiniteHerbrand υ g) : FiniteHerbrand τ g := by
  haveI := hA.1
  haveI := hA.2
  haveI := hC.1
  haveI := hC.2
  exact ⟨finite_of_exact (tateZeroMap ρ τ g f) (tateZeroMap τ υ g h)
      (hexagon_exact_B0 ρ τ υ g f h hf hh hexact),
    finite_of_exact (tateOneMap ρ τ g f) (tateOneMap τ υ g h)
      (hexagon_exact_B1 ρ τ υ g f h hf hh hexact)⟩

/-- Exactness and finiteness of B and C give finiteness of both Tate groups of A. -/
theorem finiteHerbrand_of_middle_last
    (hB : FiniteHerbrand τ g) (hC : FiniteHerbrand υ g) : FiniteHerbrand ρ g := by
  haveI := hB.1
  haveI := hB.2
  haveI := hC.1
  haveI := hC.2
  exact ⟨finite_of_exact (oneConnecting ρ τ υ g f h hf hh hexact) (tateZeroMap ρ τ g f)
      (hexagon_exact_A0 ρ τ υ g f h hf hh hexact),
    finite_of_exact (zeroConnecting ρ τ υ g f h hf hh hexact) (tateOneMap ρ τ g f)
      (hexagon_exact_A1 ρ τ υ g f h hf hh hexact)⟩

/-- The finite exact hexagon gives the alternating cardinal-product identity. -/
theorem tate_card_product
    (hA : FiniteHerbrand ρ g) (hB : FiniteHerbrand τ g) (hC : FiniteHerbrand υ g) :
    Nat.card (tateZero ρ g) * Nat.card (tateZero υ g) * Nat.card (tateOne τ g) =
      Nat.card (tateZero τ g) * Nat.card (tateOne ρ g) * Nat.card (tateOne υ g) := by
  haveI := hA.1
  haveI := hA.2
  haveI := hB.1
  haveI := hB.2
  haveI := hC.1
  haveI := hC.2
  exact finite_hexagon_card (tateZeroMap ρ τ g f) (tateZeroMap τ υ g h)
    (zeroConnecting ρ τ υ g f h hf hh hexact) (tateOneMap ρ τ g f) (tateOneMap τ υ g h)
    (oneConnecting ρ τ υ g f h hf hh hexact)
    (hexagon_exact_A0 ρ τ υ g f h hf hh hexact) (hexagon_exact_B0 ρ τ υ g f h hf hh hexact)
    (hexagon_exact_C0 ρ τ υ g f h hf hh hexact) (hexagon_exact_A1 ρ τ υ g f h hf hh hexact)
    (hexagon_exact_B1 ρ τ υ g f h hf hh hexact) (hexagon_exact_C1 ρ τ υ g f h hf hh hexact)

end Connecting
end Cox.CyclicCohomology
