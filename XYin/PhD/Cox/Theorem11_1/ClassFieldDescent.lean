/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldConstruction
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormCongruence
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormIdeals
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealQuotients
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormModulus

/-! # Cyclic descent of class-field existence

Janusz, *Algebraic Number Fields* (1973), V.7.1–7.2, printed pp. 169–170.
Compatible isomorphisms of base and extension fields transport congruence subgroups,
Artin maps and class fields. The norm preimage of an ideal group is stable under
conjugation, so its class field is normal over the base with central relative kernel,
hence abelian over a cyclic base extension; transitivity of relative norms then descends
the class field.
-/

open NumberField IsDedekindDomain
open NumberField.InfinitePlace
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [hNF : NumberField K]

section SemilinearTransport
variable {K' : Type*} [Field K'] [hNF' : NumberField K']

/-- Transport actual fractional ideals along a ring isomorphism of number fields. -/
def transportFractional (σ : K ≃+* K') :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ ≃* (FractionalIdeal (𝓞 K')⁰ K')ˣ :=
  Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K K'
    (RingOfIntegers.mapRingEquiv σ)).toMulEquiv

/-- The fractional-ideal transport agrees with ideal image on integral ideals. -/
theorem ringEquivOfRingEquiv_coeIdeal (σ : K ≃+* K') (A : Ideal (𝓞 K)) :
    FractionalIdeal.ringEquivOfRingEquiv K K' (RingOfIntegers.mapRingEquiv σ)
        (A : FractionalIdeal (𝓞 K)⁰ K) =
      (A.map (RingOfIntegers.mapRingEquiv σ).toRingHom : FractionalIdeal (𝓞 K')⁰ K') := by
  ext x
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.ringEquivOfRingEquiv_apply,
    FractionalIdeal.coe_mk, Submodule.mem_map, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [FractionalIdeal.val_eq_coe, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    refine ⟨(RingOfIntegers.mapRingEquiv σ) a, Ideal.mem_map_of_mem _ ha, ?_⟩
    rw [LinearEquiv.coe_coe, IsFractionRing.semilinearEquivOfRingEquiv_apply,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ (RingOfIntegers.mapRingEquiv σ).surjective).mp hb
    refine ⟨algebraMap (𝓞 K) K a, ?_, ?_⟩
    · rw [FractionalIdeal.val_eq_coe, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]
      exact ⟨a, ha, rfl⟩
    · rw [LinearEquiv.coe_coe, IsFractionRing.semilinearEquivOfRingEquiv_apply,
        IsFractionRing.ringEquivOfRingEquiv_algebraMap]

/-- Semilinear transport agrees with ideal image on integral ideals. -/
theorem transportFractional_integral (σ : K ≃+* K')
    (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : Ideal (𝓞 K))
    (hu : (u : FractionalIdeal (𝓞 K)⁰ K) = A) :
    (transportFractional K σ u : FractionalIdeal (𝓞 K')⁰ K') =
      A.map (RingOfIntegers.mapRingEquiv σ).toRingHom := by
  rw [← ringEquivOfRingEquiv_coeIdeal, ← hu]
  rfl

/-- The image of the good-ideal subgroup is the subgroup for the image modulus. -/
theorem transportFractional_coprime (σ : K ≃+* K') (m : Ideal (𝓞 K)) :
    (coprimeIdeals K m).map (transportFractional K σ).toMonoidHom =
      coprimeIdeals K' (m.map (RingOfIntegers.mapRingEquiv σ).toRingHom) := by
  have hmm : (m.map (RingOfIntegers.mapRingEquiv σ).toRingHom).map
      (RingOfIntegers.mapRingEquiv σ).symm.toRingHom = m := by
    rw [Ideal.map_map]
    convert Ideal.map_id m using 2
    exact RingHom.ext fun x => (RingOfIntegers.mapRingEquiv σ).symm_apply_apply x
  rw [coprimeIdeals, coprimeIdeals, MonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨u, ⟨A, hA, hAm, hu⟩, rfl⟩
    refine ⟨A.map (RingOfIntegers.mapRingEquiv σ).toRingHom, ?_, ?_,
      transportFractional_integral K σ u A hu⟩
    · exact (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv σ).injective).not.mpr hA
    · rw [← Ideal.map_sup, hAm, Ideal.map_top]
  · rintro ⟨B, hB, hBm, hv⟩
    set A := B.map (RingOfIntegers.mapRingEquiv σ).symm.toRingHom with hAdef
    have hAB : A.map (RingOfIntegers.mapRingEquiv σ).toRingHom = B := by
      rw [hAdef, Ideal.map_map]
      convert Ideal.map_id B using 2
      exact RingHom.ext fun x => (RingOfIntegers.mapRingEquiv σ).apply_symm_apply x
    have hA : A ≠ ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv σ).symm.injective).not.mpr hB
    have hAne : (A : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hA
    refine ⟨Units.mk0 _ hAne, ⟨A, hA, ?_, rfl⟩, ?_⟩
    · have h := congrArg (Ideal.map (RingOfIntegers.mapRingEquiv σ).symm.toRingHom) hBm
      rwa [Ideal.map_sup, Ideal.map_top, hmm] at h
    · apply Units.ext
      rw [hv]
      exact (transportFractional_integral K σ _ A rfl).trans (congrArg _ hAB)

/-- Restrict the actual ideal transport to the two good-ideal subgroups. -/
theorem exists_transportCoprime (σ : K ≃+* K') (m : Ideal (𝓞 K)) :
    ∃ e : coprimeIdeals K m ≃*
        coprimeIdeals K' (m.map (RingOfIntegers.mapRingEquiv σ).toRingHom),
      ∀ u, (e u : (FractionalIdeal (𝓞 K')⁰ K')ˣ) = transportFractional K σ u := by
  refine ⟨((transportFractional K σ).subgroupMap (coprimeIdeals K m)).trans
    (MulEquiv.subgroupCongr (transportFractional_coprime K σ m)), fun u => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply]

/-- The canonical good-ideal equivalence, specified by its ambient transport API. -/
def transportCoprime (σ : K ≃+* K') (m : Ideal (𝓞 K)) :
    coprimeIdeals K m ≃*
      coprimeIdeals K' (m.map (RingOfIntegers.mapRingEquiv σ).toRingHom) :=
  (exists_transportCoprime K σ m).choose

/-- Choice independence is fixed by the equality of the ambient ideal values. -/
theorem transportCoprime_coe (σ : K ≃+* K') (m : Ideal (𝓞 K))
    (u : coprimeIdeals K m) :
    (transportCoprime K σ m u : (FractionalIdeal (𝓞 K')⁰ K')ˣ) =
      transportFractional K σ u := by
  exact (exists_transportCoprime K σ m).choose_spec u

/-- Transport carries the closure of the ray generators onto the image-modulus closure. -/
theorem transportFractional_rayClosure (σ : K ≃+* K') (m : Ideal (𝓞 K)) :
    (Subgroup.closure (rayGenerators K m)).map (transportFractional K σ).toMonoidHom =
      Subgroup.closure (rayGenerators K' (m.map (RingOfIntegers.mapRingEquiv σ).toRingHom)) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨u, ⟨α, hα, hαm, hu⟩, rfl⟩
    refine ⟨RingOfIntegers.mapRingEquiv σ α, ?_, ?_, ?_⟩
    · exact (map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv σ).injective).mpr hα
    · rw [← map_one (RingOfIntegers.mapRingEquiv σ), ← map_sub]
      exact Ideal.mem_map_of_mem _ hαm
    · change FractionalIdeal.ringEquivOfRingEquiv K K' (RingOfIntegers.mapRingEquiv σ)
          (u : FractionalIdeal (𝓞 K)⁰ K) = _
      rw [hu, FractionalIdeal.ringEquivOfRingEquiv_spanSingleton]
      exact congrArg _ (IsFractionRing.ringEquivOfRingEquiv_algebraMap _ α)
  · rintro ⟨β, hβ, hβm, hv⟩
    set α := (RingOfIntegers.mapRingEquiv σ).symm β with hαdef
    have hα : α ≠ 0 := (map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv σ).symm.injective).mpr hβ
    have hαK : (α : K) ≠ 0 := fun h => hα (RingOfIntegers.ext h)
    have hαne : FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) ≠ 0 :=
      (FractionalIdeal.spanSingleton_ne_zero_iff).mpr hαK
    refine ⟨Units.mk0 _ hαne, ⟨α, hα, ?_, rfl⟩, ?_⟩
    · obtain ⟨γ, hγ, hγβ⟩ := (Ideal.mem_map_iff_of_surjective _
        (RingOfIntegers.mapRingEquiv σ).surjective).mp hβm
      have hαγ : α - 1 = γ := by
        apply (RingOfIntegers.mapRingEquiv σ).injective
        rw [map_sub, map_one, hαdef, RingEquiv.apply_symm_apply]
        exact hγβ.symm
      rw [hαγ]
      exact hγ
    · apply Units.ext
      rw [hv]
      change FractionalIdeal.ringEquivOfRingEquiv K K' (RingOfIntegers.mapRingEquiv σ)
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K)) = _
      rw [FractionalIdeal.ringEquivOfRingEquiv_spanSingleton]
      refine congrArg _ ((IsFractionRing.ringEquivOfRingEquiv_algebraMap _ α).trans ?_)
      rw [hαdef, RingEquiv.apply_symm_apply]

/-- Ring isomorphisms carry ray principals to ray principals at the image modulus. -/
theorem transportCoprime_ray (σ : K ≃+* K') (m : Ideal (𝓞 K)) :
    (raySubgroup K m).map (transportCoprime K σ m).toMonoidHom =
      raySubgroup K' (m.map (RingOfIntegers.mapRingEquiv σ).toRingHom) := by
  ext v
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [raySubgroup, Subgroup.mem_comap, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      transportCoprime_coe, ← transportFractional_rayClosure]
    exact Subgroup.mem_map_of_mem _ hu
  · intro hv
    refine ⟨(transportCoprime K σ m).symm v, ?_, (transportCoprime K σ m).apply_symm_apply v⟩
    rw [raySubgroup, Subgroup.mem_comap, Subgroup.coe_subtype,
      ← transportFractional_rayClosure] at hv
    obtain ⟨w, hw, hwv⟩ := hv
    have hw' : w = (((transportCoprime K σ m).symm v : coprimeIdeals K m) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
      apply (transportFractional K σ).injective
      rw [← transportCoprime_coe, MulEquiv.apply_symm_apply]
      exact hwv
    rw [raySubgroup, Subgroup.mem_comap, Subgroup.coe_subtype, ← hw']
    exact hw

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- The transported modulus remains nonzero. -/
theorem transport_modulus_ne_bot (σ : K ≃+* K') (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    m.map (RingOfIntegers.mapRingEquiv σ).toRingHom ≠ ⊥ := by
  exact (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv σ).injective).not.mpr hm

/-- Transported congruence subgroups contain the transported ray subgroup. -/
theorem transport_contains_ray (σ : K ≃+* K') (H : CongruenceSubgroup K) :
    raySubgroup K' (H.modulus.map (RingOfIntegers.mapRingEquiv σ).toRingHom) ≤
      H.subgroup.map (transportCoprime K σ H.modulus).toMonoidHom := by
  rw [← transportCoprime_ray]
  exact Subgroup.map_mono H.contains_ray

/-- The actual image of a congruence subgroup under a base-field isomorphism. -/
def transportCongruence (σ : K ≃+* K') (H : CongruenceSubgroup K) : CongruenceSubgroup K' where
  modulus := H.modulus.map (RingOfIntegers.mapRingEquiv σ).toRingHom
  modulus_ne_bot := transport_modulus_ne_bot K σ H.modulus H.modulus_ne_bot
  subgroup := H.subgroup.map (transportCoprime K σ H.modulus).toMonoidHom
  contains_ray := transport_contains_ray K σ H

/-- The ambient group of a transported congruence subgroup is the transported ambient group. -/
theorem transportCongruence_ambient (σ : K ≃+* K') (H : CongruenceSubgroup K) :
    (transportCongruence K σ H).ambient =
      H.ambient.map (transportFractional K σ).toMonoidHom := by
  change (H.subgroup.map (transportCoprime K σ H.modulus).toMonoidHom).map
      (coprimeIdeals K' (H.modulus.map (RingOfIntegers.mapRingEquiv σ).toRingHom)).subtype = _
  rw [Subgroup.map_map, CongruenceSubgroup.ambient, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun u => transportCoprime_coe K σ H.modulus u

/-- Transport preserves equivalence of congruence representatives. -/
theorem transportCongruence_equivalent (σ : K ≃+* K') (H J : CongruenceSubgroup K)
    (h : CongruenceEquivalent K H J) :
    CongruenceEquivalent K' (transportCongruence K σ H) (transportCongruence K σ J) := by
  obtain ⟨m, hm0, hmH, hmJ, hHJ⟩ := h
  refine ⟨m.map (RingOfIntegers.mapRingEquiv σ).toRingHom, transport_modulus_ne_bot K σ m hm0,
    Ideal.map_mono hmH, Ideal.map_mono hmJ, ?_⟩
  rw [transportCongruence_ambient, transportCongruence_ambient, ← transportFractional_coprime,
    ← Subgroup.map_inf_eq _ _ (transportFractional K σ).toMonoidHom
      (transportFractional K σ).injective,
    ← Subgroup.map_inf_eq _ _ (transportFractional K σ).toMonoidHom
      (transportFractional K σ).injective, hHJ]

/-- Transport along the identity of the base is an equivalent congruence subgroup. -/
theorem transportCongruence_refl_equivalent (H : CongruenceSubgroup K) :
    CongruenceEquivalent K (transportCongruence K (RingEquiv.refl K) H) H := by
  have hrefl : RingOfIntegers.mapRingEquiv (RingEquiv.refl K) = RingEquiv.refl (𝓞 K) :=
    RingEquiv.ext fun _ => rfl
  have hT : ∀ x, transportFractional K (RingEquiv.refl K) x = x := fun x => by
    apply Units.ext
    change FractionalIdeal.ringEquivOfRingEquiv K K (RingOfIntegers.mapRingEquiv (RingEquiv.refl K))
      (x : FractionalIdeal (𝓞 K)⁰ K) = x
    rw [hrefl, FractionalIdeal.ringEquivOfRingEquiv_refl, RingEquiv.refl_apply]
  have hmod : H.modulus.map (RingOfIntegers.mapRingEquiv (RingEquiv.refl K)).toRingHom =
      H.modulus := by
    rw [hrefl, RingEquiv.toRingHom_refl, Ideal.map_id]
  refine ⟨H.modulus, H.modulus_ne_bot, hmod.ge, le_rfl, ?_⟩
  rw [transportCongruence_ambient]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hT]
    exact hy
  · intro hx
    exact ⟨x, hx, hT x⟩

/-- A residue quotient has the same cardinal after an isomorphism. -/
theorem absNorm_transport (σ : K ≃+* K') (q : Ideal (𝓞 K)) :
    (q.map (RingOfIntegers.mapRingEquiv σ).toRingHom).absNorm = q.absNorm := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv q _ (RingOfIntegers.mapRingEquiv σ) rfl).toEquiv).symm

variable {L L' : Type*} [Field L] [Field L'] [Algebra K L] [Algebra K' L']

omit hNF hNF' in
/-- The inverse extension isomorphism carries the target base field to the source one. -/
theorem symm_algebraMap_semilinear (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x)) (c : K') :
    τ.symm (algebraMap K' L' c) = algebraMap K L (σ.symm c) := by
  rw [RingEquiv.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]

omit hNF hNF' in
/-- Conjugate a relative automorphism by a compatible pair of field isomorphisms. -/
def semilinearConj (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x)) (g : L ≃ₐ[K] L) :
    L' ≃ₐ[K'] L' :=
  AlgEquiv.ofRingEquiv (f := (τ.symm.trans g.toRingEquiv).trans τ) fun c => by
    change τ (g (τ.symm (algebraMap K' L' c))) = algebraMap K' L' c
    rw [symm_algebraMap_semilinear K σ τ hτ, AlgEquiv.commutes, hτ, RingEquiv.apply_symm_apply]

omit hNF hNF' in
theorem semilinearConj_apply (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x)) (g : L ≃ₐ[K] L) (y : L') :
    semilinearConj K σ τ hτ g y = τ (g (τ.symm y)) :=
  rfl

omit hNF hNF' in
/-- Conjugation by a semilinear field equivalence transports relative automorphisms. -/
theorem exists_semilinearAutEquiv (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x)) :
    ∃ e : (L ≃ₐ[K] L) ≃* (L' ≃ₐ[K'] L'),
      ∀ g x, e g (τ x) = τ (g x) := by
  have hτ' : ∀ c, τ.symm (algebraMap K' L' c) = algebraMap K L (σ.symm c) :=
    symm_algebraMap_semilinear K σ τ hτ
  refine ⟨{ toFun := semilinearConj K σ τ hτ
            invFun := semilinearConj K' σ.symm τ.symm hτ'
            left_inv := fun g => AlgEquiv.ext fun y => ?_
            right_inv := fun g => AlgEquiv.ext fun y => ?_
            map_mul' := fun g h => AlgEquiv.ext fun y => ?_ }, fun g x => ?_⟩
  · rw [semilinearConj_apply, semilinearConj_apply, RingEquiv.symm_symm,
      RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  · rw [semilinearConj_apply, semilinearConj_apply, RingEquiv.symm_symm,
      RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  · rw [AlgEquiv.mul_apply, semilinearConj_apply, semilinearConj_apply, semilinearConj_apply,
      AlgEquiv.mul_apply, RingEquiv.symm_apply_apply]
  · change semilinearConj K σ τ hτ g (τ x) = τ (g x)
    rw [semilinearConj_apply, RingEquiv.symm_apply_apply]

/-- The canonical automorphism-group conjugation for a semilinear field equivalence. -/
def semilinearAutEquiv (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x)) :
    (L ≃ₐ[K] L) ≃* (L' ≃ₐ[K'] L') :=
  (exists_semilinearAutEquiv K σ τ hτ).choose

omit hNF hNF' in
/-- The chosen group equivalence acts by the explicit conjugation formula. -/
theorem semilinearAutEquiv_apply (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x))
    (g : L ≃ₐ[K] L) (x : L) :
    semilinearAutEquiv K σ τ hτ g (τ x) = τ (g x) := by
  exact (exists_semilinearAutEquiv K σ τ hτ).choose_spec g x

/-- Apply a semilinear equivalence to the arithmetic Frobenius congruence. -/
theorem frobenius_congruence_semilinear (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x))
    (q : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) (g : L ≃ₐ[K] L)
    (hg : ∀ x : 𝓞 L, RingOfIntegers.mapRingHom g.toRingHom x - x ^ q.absNorm ∈ P) :
    ∀ x : 𝓞 L',
      RingOfIntegers.mapRingHom (semilinearAutEquiv K σ τ hτ g).toRingHom x -
          x ^ (q.map (RingOfIntegers.mapRingEquiv σ).toRingHom).absNorm ∈
        P.map (RingOfIntegers.mapRingEquiv τ).toRingHom := by
  intro x
  obtain ⟨y, rfl⟩ := (RingOfIntegers.mapRingEquiv τ).surjective x
  have hconj : RingOfIntegers.mapRingHom (semilinearAutEquiv K σ τ hτ g).toRingHom
      (RingOfIntegers.mapRingEquiv τ y) =
        RingOfIntegers.mapRingEquiv τ (RingOfIntegers.mapRingHom g.toRingHom y) :=
    RingOfIntegers.ext (semilinearAutEquiv_apply K σ τ hτ g y)
  rw [hconj, absNorm_transport, ← map_pow (RingOfIntegers.mapRingEquiv τ),
    ← map_sub (RingOfIntegers.mapRingEquiv τ)]
  exact Ideal.mem_map_of_mem _ (hg y)

omit hNF hNF' in
/-- Compatible field isomorphisms give a commuting square of rings of integers. -/
theorem algebraMap_comp_mapRingEquiv (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x)) :
    (algebraMap (𝓞 K') (𝓞 L')).comp (RingOfIntegers.mapRingEquiv σ).toRingHom =
      (RingOfIntegers.mapRingEquiv τ).toRingHom.comp (algebraMap (𝓞 K) (𝓞 L)) :=
  RingHom.ext fun x => RingOfIntegers.ext (hτ x).symm

omit hNF hNF' in
/-- Pull a good prime and a prime above it back along compatible isomorphisms. -/
theorem exists_pullback_primesOver (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x))
    (m : Ideal (𝓞 K)) (q' : Ideal (𝓞 K')) (hq : q'.IsPrime) (hq0 : q' ≠ ⊥)
    (hqm : q' ⊔ m.map (RingOfIntegers.mapRingEquiv σ).toRingHom = ⊤)
    (P' : Ideal (𝓞 L')) (hP : P' ∈ q'.primesOver (𝓞 L')) :
    ∃ (q : Ideal (𝓞 K)) (P : Ideal (𝓞 L)), q.IsPrime ∧ q ≠ ⊥ ∧ q ⊔ m = ⊤ ∧
      P ∈ q.primesOver (𝓞 L) ∧ q.map (RingOfIntegers.mapRingEquiv σ).toRingHom = q' ∧
        P.map (RingOfIntegers.mapRingEquiv τ).toRingHom = P' := by
  have hq' : (q'.comap (RingOfIntegers.mapRingEquiv σ).toRingHom).map
      (RingOfIntegers.mapRingEquiv σ).toRingHom = q' :=
    Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv σ).surjective q'
  have hP' : (P'.comap (RingOfIntegers.mapRingEquiv τ).toRingHom).map
      (RingOfIntegers.mapRingEquiv τ).toRingHom = P' :=
    Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv τ).surjective P'
  obtain ⟨hPp, hPo⟩ := hP
  refine ⟨q'.comap (RingOfIntegers.mapRingEquiv σ).toRingHom,
    P'.comap (RingOfIntegers.mapRingEquiv τ).toRingHom, Ideal.comap_isPrime _ _, ?_, ?_,
    ⟨Ideal.comap_isPrime _ _, ?_⟩, hq', hP'⟩
  · intro h
    apply hq0
    rw [← hq', h, Ideal.map_bot]
  · have h1 : (q'.comap (RingOfIntegers.mapRingEquiv σ).toRingHom ⊔ m).map
        (RingOfIntegers.mapRingEquiv σ).toRingHom = ⊤ := by
      rw [Ideal.map_sup, hq', hqm]
    rw [← Ideal.comap_map_of_bijective (RingOfIntegers.mapRingEquiv σ).toRingHom
      (RingOfIntegers.mapRingEquiv σ).bijective
      (I := q'.comap (RingOfIntegers.mapRingEquiv σ).toRingHom ⊔ m), h1, Ideal.comap_top]
  · constructor
    rw [Ideal.under, Ideal.comap_comap, ← algebraMap_comp_mapRingEquiv K σ τ hτ,
      ← Ideal.comap_comap]
    exact congrArg _ hPo.over

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- Ramification indices are unchanged by compatible isomorphisms of both fields. -/
theorem ramificationIdx_semilinear (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x))
    (q : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) :
    Ideal.ramificationIdx (q.map (RingOfIntegers.mapRingEquiv σ).toRingHom)
      (P.map (RingOfIntegers.mapRingEquiv τ).toRingHom) = Ideal.ramificationIdx q P := by
  unfold Ideal.ramificationIdx
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  rw [Ideal.map_map, algebraMap_comp_mapRingEquiv K σ τ hτ, ← Ideal.map_map, ← Ideal.map_pow,
    Ideal.map_le_iff_le_comap,
    Ideal.comap_map_of_bijective (RingOfIntegers.mapRingEquiv τ).toRingHom
      (RingOfIntegers.mapRingEquiv τ).bijective]

/-- No good prime becomes ramified under semilinear transport. -/
theorem isUnramifiedAway_semilinear (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x))
    (m : Ideal (𝓞 K)) (hU : IsUnramifiedAway K m L) :
    IsUnramifiedAway K' (m.map (RingOfIntegers.mapRingEquiv σ).toRingHom) L' := by
  intro q' hq hq0 hqm P' hP
  obtain ⟨q, P, hqp, hq0', hqm', hPq, rfl, rfl⟩ :=
    exists_pullback_primesOver K σ τ hτ m q' hq hq0 hqm P' hP
  rw [ramificationIdx_semilinear K σ τ hτ q P]
  exact hU q hqp hq0' hqm' P hPq

/-- Arithmetic Artin is transported using ideal image and group conjugation. -/
theorem isArtinMap_semilinear (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x))
    (m : Ideal (𝓞 K)) (φ : coprimeIdeals K m →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K m L φ) :
    IsArtinMap K' (m.map (RingOfIntegers.mapRingEquiv σ).toRingHom) L'
      (((semilinearAutEquiv K σ τ hτ).toMonoidHom.comp φ).comp
        (transportCoprime K σ m).symm.toMonoidHom) := by
  intro q' hq hq0 hqm u' hu' P' hP x
  obtain ⟨q, P, hqp, hq0', hqm', hPq, rfl, rfl⟩ :=
    exists_pullback_primesOver K σ τ hτ m q' hq hq0 hqm P' hP
  set u := (transportCoprime K σ m).symm u' with hudef
  have hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q := by
    have hqne : (q : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hq0'
    have hT : transportFractional K σ (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        transportFractional K σ (Units.mk0 _ hqne) := by
      apply Units.ext
      rw [transportFractional_integral K σ (Units.mk0 _ hqne) q rfl,
        ← transportCoprime_coe K σ m u, hudef, MulEquiv.apply_symm_apply]
      exact hu'
    rw [(transportFractional K σ).injective hT, Units.val_mk0]
  exact frobenius_congruence_semilinear K σ τ hτ q P (φ u) (hφ q hqp hq0' hqm' u hu P hPq) x

omit hNF hNF' in
/-- Finite extension degree is unchanged by compatible base/extension isomorphisms. -/
theorem finiteDimensional_semilinear (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x))
    [FiniteDimensional K L] : FiniteDimensional K' L' := by
  exact Module.Finite.of_equiv_equiv σ τ (RingHom.ext fun x => (hτ x).symm)

omit hNF hNF' in
/-- Equality between automorphism cardinality and degree transports Galoisness. -/
theorem isGalois_semilinear (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x))
    [FiniteDimensional K L] [IsGalois K L] : IsGalois K' L' := by
  exact IsGalois.of_equiv_equiv (f := σ) (g := τ) (RingHom.ext fun x => (hτ x).symm)

/-- Exact Artin kernels transport under a compatible pair of base/extension isomorphisms. -/
theorem hasArtinKernel_semilinear (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x))
    (m : Ideal (𝓞 K)) (H : Subgroup (coprimeIdeals K m))
    (hH : HasArtinKernel K m L H) :
    HasArtinKernel K' (m.map (RingOfIntegers.mapRingEquiv σ).toRingHom) L'
      (H.map (transportCoprime K σ m).toMonoidHom) := by
  obtain ⟨hfin, hgal, hcomm, hU, φ, hφ, hsurj, hφk⟩ := hH
  haveI := hfin
  haveI := hgal
  haveI := finiteDimensional_semilinear K σ τ hτ
  refine ⟨inferInstance, isGalois_semilinear K σ τ hτ, ?_,
    isUnramifiedAway_semilinear K σ τ hτ m hU,
    ((semilinearAutEquiv K σ τ hτ).toMonoidHom.comp φ).comp
      (transportCoprime K σ m).symm.toMonoidHom,
    isArtinMap_semilinear K σ τ hτ m φ hφ, ?_, ?_⟩
  · refine ⟨⟨fun a b => (semilinearAutEquiv K σ τ hτ).symm.injective ?_⟩⟩
    rw [map_mul, map_mul]
    exact hcomm.is_comm.comm _ _
  · exact (semilinearAutEquiv K σ τ hτ).surjective.comp
      (hsurj.comp (transportCoprime K σ m).symm.surjective)
  · ext v
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ (semilinearAutEquiv K σ τ hτ).injective, ← MonoidHom.mem_ker, hφk,
      Subgroup.mem_map_equiv]

end SemilinearTransport

/-- A field is class field to an ideal group when some equivalent congruence subgroup
is its genuine Artin kernel at an admissible modulus. -/
def IsClassFieldFor (H : CongruenceSubgroup K) (L : Type*) [Field L] [Algebra K L] : Prop :=
  ∃ J : CongruenceSubgroup K,
    CongruenceEquivalent K H J ∧ HasArtinKernel K J.modulus L J.subgroup

/-- The class-field predicate depends only on the represented ideal group. -/
theorem isClassFieldFor_of_equivalent (H J : CongruenceSubgroup K)
    (hHJ : CongruenceEquivalent K H J) (L : Type*) [Field L] [Algebra K L]
    (hL : IsClassFieldFor K H L) : IsClassFieldFor K J L := by
  obtain ⟨J', hHJ', hJ'⟩ := hL
  exact ⟨J', (congruenceEquivalent_equivalence K).trans
    ((congruenceEquivalent_equivalence K).symm hHJ) hHJ', hJ'⟩

/-- Janusz V.7.2: conjugate extensions correspond to conjugate ideal groups. -/
theorem isClassFieldFor_semilinear {K' L L' : Type*} [Field K'] [NumberField K']
    [Field L] [Field L'] [Algebra K L] [Algebra K' L']
    (σ : K ≃+* K') (τ : L ≃+* L')
    (hτ : ∀ x, τ (algebraMap K L x) = algebraMap K' L' (σ x))
    (H : CongruenceSubgroup K) (hL : IsClassFieldFor K H L) :
    IsClassFieldFor K' (transportCongruence K σ H) L' := by
  obtain ⟨J, hHJ, hJ⟩ := hL
  exact ⟨transportCongruence K σ J, transportCongruence_equivalent K σ H J hHJ,
    hasArtinKernel_semilinear K σ τ hτ J.modulus J.subgroup hJ⟩

/-- The class-field predicate is invariant under isomorphism over the base. -/
theorem isClassFieldFor_of_algEquiv (H : CongruenceSubgroup K) {L L' : Type*} [Field L]
    [Field L'] [Algebra K L] [Algebra K L'] (e : L ≃ₐ[K] L') (hL : IsClassFieldFor K H L) :
    IsClassFieldFor K H L' :=
  isClassFieldFor_of_equivalent K _ H (transportCongruence_refl_equivalent K H) L'
    (isClassFieldFor_semilinear K (RingEquiv.refl K) e.toRingEquiv (fun x => e.commutes x) H hL)

/-- Existence of an embedded class field for an ideal group, independently of CM. -/
def HasClassField (H : CongruenceSubgroup K) : Prop :=
  ∃ L : IntermediateField K (AlgebraicClosure K), IsClassFieldFor K H L

/-- Janusz V.6.1: a stronger ray condition lies in the restricted congruence group. -/
theorem raySubgroup_le_restrict (H : CongruenceSubgroup K) (m : Ideal (𝓞 K))
    (hm : m ≤ H.modulus) :
    raySubgroup K m ≤ H.subgroup.comap (Subgroup.inclusion (coprimeIdeals_mono K hm)) := by
  intro u hu
  rw [Subgroup.mem_comap]
  apply H.contains_ray
  rw [raySubgroup, Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.coe_inclusion]
  have hgen : rayGenerators K m ⊆ rayGenerators K H.modulus := by
    rintro v ⟨α, hα, hαm, hv⟩
    exact ⟨α, hα, hm hαm, hv⟩
  exact Subgroup.closure_mono hgen hu

/-- Restriction of an ideal group to a more divisible nonzero modulus. -/
def restrictCongruence (H : CongruenceSubgroup K) (m : Ideal (𝓞 K))
    (hm0 : m ≠ ⊥) (hm : m ≤ H.modulus) : CongruenceSubgroup K where
  modulus := m
  modulus_ne_bot := hm0
  subgroup := H.subgroup.comap (Subgroup.inclusion (coprimeIdeals_mono K hm))
  contains_ray := raySubgroup_le_restrict K H m hm

/-- Membership in a restricted congruence subgroup is ambient membership. -/
theorem mem_comap_inclusion_iff (H : CongruenceSubgroup K) (m : Ideal (𝓞 K))
    (hmH : m ≤ H.modulus) (w : coprimeIdeals K m) :
    w ∈ H.subgroup.comap (Subgroup.inclusion (coprimeIdeals_mono K hmH)) ↔
      (w : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ H.ambient := by
  rw [Subgroup.mem_comap, CongruenceSubgroup.ambient, Subgroup.mem_map]
  constructor
  · intro hw
    exact ⟨_, hw, Subgroup.coe_inclusion (coprimeIdeals_mono K hmH) w⟩
  · rintro ⟨v, hv, hvw⟩
    have hv' : Subgroup.inclusion (coprimeIdeals_mono K hmH) w = v := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
      exact hvw.symm
    rw [hv']
    exact hv

/-- Equal ambient restrictions give equal restricted subgroups. -/
theorem comap_inclusion_eq_of_inf_eq (H J : CongruenceSubgroup K) (m : Ideal (𝓞 K))
    (hmH : m ≤ H.modulus) (hmJ : m ≤ J.modulus)
    (h : H.ambient ⊓ coprimeIdeals K m = J.ambient ⊓ coprimeIdeals K m) :
    H.subgroup.comap (Subgroup.inclusion (coprimeIdeals_mono K hmH)) =
      J.subgroup.comap (Subgroup.inclusion (coprimeIdeals_mono K hmJ)) := by
  ext w
  rw [mem_comap_inclusion_iff K H m hmH, mem_comap_inclusion_iff K J m hmJ]
  have hw : (w : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ coprimeIdeals K m := w.property
  constructor
  · intro hH
    have h2 : (w : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ J.ambient ⊓ coprimeIdeals K m := by
      rw [← h]
      exact ⟨hH, hw⟩
    exact h2.1
  · intro hJ
    have h2 : (w : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ H.ambient ⊓ coprimeIdeals K m := by
      rw [h]
      exact ⟨hJ, hw⟩
    exact h2.1

/-- Restriction leaves the represented ideal group unchanged. -/
theorem restrictCongruence_equivalent (H : CongruenceSubgroup K) (m : Ideal (𝓞 K))
    (hm0 : m ≠ ⊥) (hm : m ≤ H.modulus) :
    CongruenceEquivalent K H (restrictCongruence K H m hm0 hm) := by
  refine ⟨m, hm0, hm, le_rfl, ?_⟩
  ext x
  constructor
  · rintro ⟨hxH, hx⟩
    refine ⟨⟨⟨x, hx⟩, (mem_comap_inclusion_iff K H m hm ⟨x, hx⟩).mpr hxH, rfl⟩, hx⟩
  · rintro ⟨⟨w, hw, rfl⟩, hx⟩
    exact ⟨(mem_comap_inclusion_iff K H m hm w).mp hw, hx⟩

/-- Janusz V.6.1: changing to a more divisible modulus restricts the exact Artin kernel. -/
theorem hasArtinKernel_restrictModulus (m n : Ideal (𝓞 K))
    (hm : m ≠ ⊥) (hmn : m ≤ n) (L : Type*) [Field L] [Algebra K L]
    (H : Subgroup (coprimeIdeals K n)) (hH : HasArtinKernel K n L H) :
    HasArtinKernel K m L (H.comap (Subgroup.inclusion (coprimeIdeals_mono K hmn))) := by
  obtain ⟨hfin, hgal, hcomm, hU, φ, hφ, hsurj, hφk⟩ := hH
  haveI := hfin
  haveI := hgal
  haveI := hcomm
  haveI : NumberField L := NumberField.of_module_finite K L
  haveI : IsAbelianGalois K L := ⟨⟩
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)
  have hUm : IsUnramifiedAway K m L := fun q hq hq0 hqm P hP =>
    hU q hq hq0 (eq_top_mono (sup_le_sup_left hmn q) hqm) P hP
  obtain ⟨ψ, hψ, hψs⟩ := exists_artinMap K m L hm hUm
  have hres := isArtinMap_comp_inclusion K L hmn φ hφ
  have heq := isArtinMap_unique K m L hUm hψ hres
  refine ⟨hfin, hgal, hcomm, hUm, φ.comp (Subgroup.inclusion (coprimeIdeals_mono K hmn)), hres,
    ?_, ?_⟩
  · rw [← heq]
    exact hψs
  · rw [← MonoidHom.comap_ker, hφk]

/-- Janusz V.5.8: equivalent ideal groups uniquely determine embedded class fields. -/
theorem isClassFieldFor_eq {Ω : Type*} [Field Ω] [Algebra K Ω]
    (H : CongruenceSubgroup K) (L F : IntermediateField K Ω)
    [NumberField L] [NumberField F]
    (hL : IsClassFieldFor K H L) (hF : IsClassFieldFor K H F) : L = F := by
  obtain ⟨J₁, hHJ₁, hJ₁⟩ := hL
  obtain ⟨J₂, hHJ₂, hJ₂⟩ := hF
  obtain ⟨m, hm0, hm₁, hm₂, hJJ⟩ := (congruenceEquivalent_equivalence K).trans
    ((congruenceEquivalent_equivalence K).symm hHJ₁) hHJ₂
  have hL' := hasArtinKernel_restrictModulus K m J₁.modulus hm0 hm₁ L J₁.subgroup hJ₁
  have hF' := hasArtinKernel_restrictModulus K m J₂.modulus hm0 hm₂ F J₂.subgroup hJ₂
  rw [comap_inclusion_eq_of_inf_eq K J₁ J₂ m hm₁ hm₂ hJJ] at hL'
  exact eq_of_artinKernel_eq L F m hm0 hL' hF'

/-- A commuting relation follows from a quotient in the Artin kernel. -/
theorem commute_of_artin_quotient {A G : Type*} [Group A] [Group G]
    (φ : A →* G) (u v : A) (σ : G)
    (hconj : σ * φ u * σ⁻¹ = φ v) (hker : u / v ∈ φ.ker) :
    Commute σ (φ u) := by
  have huv : φ u = φ v := by
    rw [MonoidHom.mem_ker, map_div, div_eq_one] at hker
    exact hker
  rw [← huv] at hconj
  exact mul_inv_eq_iff_eq_mul.mp hconj

section Descent

variable (E : Type*) [Field E] [NumberField E] [Algebra K E]
variable [Module.Finite (𝓞 K) (𝓞 E)]

/-- Restrict an E-automorphism to integers, then transport actual fractional-ideal units. -/
def conjugateFractional (σ : E ≃ₐ[K] E) :
    (FractionalIdeal (𝓞 E)⁰ E)ˣ ≃* (FractionalIdeal (𝓞 E)⁰ E)ˣ :=
  Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv E E
    (RingOfIntegers.mapAlgEquiv σ).toRingEquiv).toMulEquiv

omit hNF [NumberField E] [Module.Finite (𝓞 K) (𝓞 E)] in
/-- The integer-ring conjugation is the ring-isomorphism transport of `σ`. -/
theorem mapAlgEquiv_toRingEquiv (σ : E ≃ₐ[K] E) :
    (RingOfIntegers.mapAlgEquiv σ).toRingEquiv = RingOfIntegers.mapRingEquiv σ.toRingEquiv :=
  RingEquiv.ext fun _ => rfl

omit hNF [Module.Finite (𝓞 K) (𝓞 E)] in
/-- Conjugation of fractional ideals is ring-isomorphism transport. -/
theorem conjugateFractional_eq (σ : E ≃ₐ[K] E) :
    conjugateFractional K E σ = transportFractional E σ.toRingEquiv := by
  rw [conjugateFractional, transportFractional, mapAlgEquiv_toRingEquiv]

omit hNF [Module.Finite (𝓞 K) (𝓞 E)] in
/-- Conjugation agrees with ideal image on integral ideals. -/
theorem conjugate_coeIdeal (σ : E ≃ₐ[K] E) (A : Ideal (𝓞 E)) :
    FractionalIdeal.ringEquivOfRingEquiv E E (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
        (A : FractionalIdeal (𝓞 E)⁰ E) =
      (A.map (RingOfIntegers.mapAlgEquiv σ).toRingHom : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [mapAlgEquiv_toRingEquiv, ringEquivOfRingEquiv_coeIdeal]

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- The transport agrees with the ordinary image on integral ideals. -/
theorem conjugateFractional_integral (σ : E ≃ₐ[K] E)
    (u : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (A : Ideal (𝓞 E))
    (hu : (u : FractionalIdeal (𝓞 E)⁰ E) = A) :
    (conjugateFractional K E σ u : FractionalIdeal (𝓞 E)⁰ E) =
      A.map (RingOfIntegers.mapAlgEquiv σ).toRingHom := by
  change FractionalIdeal.ringEquivOfRingEquiv E E (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
    (u : FractionalIdeal (𝓞 E)⁰ E) = _
  rw [hu, conjugate_coeIdeal]

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- The inverse automorphism undoes conjugation of a fractional ideal. -/
theorem conjugateFractional_symm_apply (σ : E ≃ₐ[K] E)
    (u : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    conjugateFractional K E σ.symm (conjugateFractional K E σ u) = u := by
  have hsymm : (RingOfIntegers.mapAlgEquiv σ.symm).toRingEquiv =
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv.symm := RingEquiv.ext fun _ => rfl
  apply Units.ext
  change FractionalIdeal.ringEquivOfRingEquiv E E (RingOfIntegers.mapAlgEquiv σ.symm).toRingEquiv
    (FractionalIdeal.ringEquivOfRingEquiv E E (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
      (u : FractionalIdeal (𝓞 E)⁰ E)) = u
  rw [hsymm, ← FractionalIdeal.ringEquivOfRingEquiv_symm_eq, RingEquiv.symm_apply_apply]

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- Janusz V.7.2: a base-field modulus is fixed by every relative automorphism. -/
theorem conjugate_extended_modulus (σ : E ≃ₐ[K] E) (m : Ideal (𝓞 K)) :
    (m.map (algebraMap (𝓞 K) (𝓞 E))).map
      (RingOfIntegers.mapAlgEquiv σ).toRingHom =
        m.map (algebraMap (𝓞 K) (𝓞 E)) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext fun x => (RingOfIntegers.mapAlgEquiv σ).commutes x

/-- Janusz V.7.2: N(σA)=N(A). -/
theorem relNorm_conjugate (σ : E ≃ₐ[K] E) (A : Ideal (𝓞 E)) :
    Ideal.relNorm (𝓞 K) (A.map (RingOfIntegers.mapAlgEquiv σ).toRingHom) =
      Ideal.relNorm (𝓞 K) A := by
  exact Ideal.relNorm_map_algEquiv (RingOfIntegers.mapAlgEquiv σ) A

/-- Conjugation preserves the prime-to-base-modulus subgroup. -/
theorem conjugateFractional_mem_coprime (σ : E ≃ₐ[K] E) (m : Ideal (𝓞 K))
    {u : (FractionalIdeal (𝓞 E)⁰ E)ˣ}
    (hu : u ∈ coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E)))) :
    conjugateFractional K E σ u ∈ coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))) := by
  have hM : (m.map (algebraMap (𝓞 K) (𝓞 E))).map
      (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom = m.map (algebraMap (𝓞 K) (𝓞 E)) := by
    rw [← mapAlgEquiv_toRingEquiv]
    exact conjugate_extended_modulus K E σ m
  have h := transportFractional_coprime E σ.toRingEquiv (m.map (algebraMap (𝓞 K) (𝓞 E)))
  rw [hM] at h
  rw [conjugateFractional_eq, ← h]
  exact Subgroup.mem_map_of_mem _ hu

/-- The conjugation map on the exact good-ideal group used in descent. -/
def conjugateCoprime (σ : E ≃ₐ[K] E) (m : Ideal (𝓞 K)) :
    coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))) →*
      coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))) :=
  (((conjugateFractional K E σ).toMonoidHom).comp
    (coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E)))).subtype).codRestrict _
      (fun u => conjugateFractional_mem_coprime K E σ m u.property)

/-- The restricted action has the advertised ambient ideal value. -/
theorem conjugateCoprime_coe (σ : E ≃ₐ[K] E) (m : Ideal (𝓞 K))
    (u : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E)))) :
    (conjugateCoprime K E σ m u : (FractionalIdeal (𝓞 E)⁰ E)ˣ) =
      conjugateFractional K E σ u := by
  rfl

/-- A sufficiently divisible base modulus restricts below any given upstairs modulus. -/
theorem exists_base_modulus (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (n : Ideal (𝓞 E)) (hn : n ≠ ⊥) :
    ∃ d : Ideal (𝓞 K), d ≠ ⊥ ∧ d ≤ m ∧
      d.map (algebraMap (𝓞 K) (𝓞 E)) ≤ n := by
  refine ⟨m * Ideal.relNorm (𝓞 K) n, mul_ne_zero hm (Ideal.relNorm_eq_bot_iff.not.mpr hn),
    Ideal.mul_le_right, ?_⟩
  rw [Ideal.map_mul]
  exact Ideal.mul_le_left.trans (Ideal.map_le_iff_le_comap.mpr (Ideal.relNorm_le_comap _ n))

/-- The norm preimage of a congruence subgroup, expressed using quotients of integral
good ideals; no unspecified relative fractional-ideal norm is used. -/
def normPreimage (H : CongruenceSubgroup K) :
    Subgroup (coprimeIdeals E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E)))) :=
  Subgroup.closure {u | ∃ A B : Ideal (𝓞 E), A ≠ ⊥ ∧ B ≠ ⊥ ∧
    A ⊔ H.modulus.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤ ∧
    B ⊔ H.modulus.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤ ∧
    ((u : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) * B = A ∧
    ∃ v : coprimeIdeals K H.modulus, v ∈ H.subgroup ∧
      ((v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
        (Ideal.relNorm (𝓞 K) B : FractionalIdeal (𝓞 K)⁰ K) =
          (Ideal.relNorm (𝓞 K) A : FractionalIdeal (𝓞 K)⁰ K)}

/-- The closure definition is exactly the source's relative-norm preimage. -/
theorem mem_normPreimage_iff (H : CongruenceSubgroup K)
    (u : coprimeIdeals E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E)))) :
    u ∈ normPreimage K E H ↔
      ∃ A B : Ideal (𝓞 E), A ≠ ⊥ ∧ B ≠ ⊥ ∧
        A ⊔ H.modulus.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤ ∧
        B ⊔ H.modulus.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤ ∧
        ((u : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) * B = A ∧
        ∃ v : coprimeIdeals K H.modulus, v ∈ H.subgroup ∧
          ((v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
            (Ideal.relNorm (𝓞 K) B : FractionalIdeal (𝓞 K)⁰ K) =
              (Ideal.relNorm (𝓞 K) A : FractionalIdeal (𝓞 K)⁰ K) := by
  constructor
  · intro hu
    induction hu using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one =>
      refine ⟨⊤, ⊤, top_ne_bot, top_ne_bot, top_sup_eq _, top_sup_eq _, ?_, 1, one_mem _, ?_⟩
      · rw [OneMemClass.coe_one, Units.val_one, one_mul]
      · rw [OneMemClass.coe_one, Units.val_one, one_mul]
    | mul x y _ _ hx hy =>
      obtain ⟨A₁, B₁, hA₁, hB₁, hA₁m, hB₁m, hx₁, v₁, hv₁, hn₁⟩ := hx
      obtain ⟨A₂, B₂, hA₂, hB₂, hA₂m, hB₂m, hy₁, v₂, hv₂, hn₂⟩ := hy
      refine ⟨A₁ * A₂, B₁ * B₂, mul_ne_zero hA₁ hA₂, mul_ne_zero hB₁ hB₂, ?_, ?_, ?_,
        v₁ * v₂, mul_mem hv₁ hv₂, ?_⟩
      · rw [Ideal.mul_sup_eq_of_coprime_left hA₁m, hA₂m]
      · rw [Ideal.mul_sup_eq_of_coprime_left hB₁m, hB₂m]
      · rw [Subgroup.coe_mul, Units.val_mul, FractionalIdeal.coeIdeal_mul,
          FractionalIdeal.coeIdeal_mul, ← hx₁, ← hy₁]
        ring
      · rw [Subgroup.coe_mul, Units.val_mul, map_mul, map_mul, FractionalIdeal.coeIdeal_mul,
          FractionalIdeal.coeIdeal_mul, ← hn₁, ← hn₂]
        ring
    | inv x _ hx =>
      obtain ⟨A, B, hA, hB, hAm, hBm, hx₁, v, hv, hn⟩ := hx
      refine ⟨B, A, hB, hA, hBm, hAm, ?_, v⁻¹, inv_mem hv, ?_⟩
      · rw [← hx₁, ← mul_assoc, InvMemClass.coe_inv, Units.inv_mul, one_mul]
      · rw [← hn, ← mul_assoc, InvMemClass.coe_inv, Units.inv_mul, one_mul]
  · intro hu
    exact Subgroup.subset_closure hu

/-- Conjugation preserves the norm preimage. -/
theorem conjugate_mem_normPreimage (H : CongruenceSubgroup K) (σ : E ≃ₐ[K] E)
    (u : coprimeIdeals E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E))))
    (hu : u ∈ normPreimage K E H) :
    conjugateCoprime K E σ H.modulus u ∈ normPreimage K E H := by
  rw [mem_normPreimage_iff] at hu ⊢
  obtain ⟨A, B, hA, hB, hAm, hBm, huAB, v, hv, hvn⟩ := hu
  have hinj := (RingOfIntegers.mapAlgEquiv σ).injective
  refine ⟨A.map (RingOfIntegers.mapAlgEquiv σ).toRingHom,
    B.map (RingOfIntegers.mapAlgEquiv σ).toRingHom,
    (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr hA,
    (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr hB, ?_, ?_, ?_, v, hv, ?_⟩
  · rw [← conjugate_extended_modulus K E σ H.modulus, ← Ideal.map_sup, hAm, Ideal.map_top]
  · rw [← conjugate_extended_modulus K E σ H.modulus, ← Ideal.map_sup, hBm, Ideal.map_top]
  · rw [conjugateCoprime_coe, ← conjugate_coeIdeal, ← conjugate_coeIdeal, ← huAB, map_mul]
    rfl
  · rw [relNorm_conjugate, relNorm_conjugate]
    exact hvn

/-- Janusz V.7.2: σ(H_E)=H_E, using relative norm invariance. -/
theorem mem_normPreimage_conjugate_iff (H : CongruenceSubgroup K)
    (σ : E ≃ₐ[K] E)
    (u : coprimeIdeals E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E)))) :
    conjugateCoprime K E σ H.modulus u ∈ normPreimage K E H ↔
      u ∈ normPreimage K E H := by
  constructor
  · intro hu
    have h := conjugate_mem_normPreimage K E H σ.symm _ hu
    have heq : conjugateCoprime K E σ.symm H.modulus (conjugateCoprime K E σ H.modulus u) = u := by
      apply Subtype.ext
      rw [conjugateCoprime_coe, conjugateCoprime_coe]
      exact conjugateFractional_symm_apply K E σ u
    rwa [heq] at h
  · exact conjugate_mem_normPreimage K E H σ u

/-- Janusz V.7.2: the quotient a/σ(a) has norm one and lies in H_E. -/
theorem div_conjugate_mem_normPreimage (H : CongruenceSubgroup K)
    (σ : E ≃ₐ[K] E)
    (u : coprimeIdeals E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E)))) :
    u / conjugateCoprime K E σ H.modulus u ∈ normPreimage K E H := by
  obtain ⟨A, B, hA, hB, hAm, hBm, huAB⟩ := exists_coprime_ideal_quotient E _ u
  have hinj := (RingOfIntegers.mapAlgEquiv σ).injective
  have hσA := (Ideal.map_eq_bot_iff_of_injective hinj (I := A)).not.mpr hA
  have hσB := (Ideal.map_eq_bot_iff_of_injective hinj (I := B)).not.mpr hB
  have hσAm : A.map (RingOfIntegers.mapAlgEquiv σ).toRingHom ⊔
      H.modulus.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤ := by
    rw [← conjugate_extended_modulus K E σ H.modulus, ← Ideal.map_sup, hAm, Ideal.map_top]
  have hσBm : B.map (RingOfIntegers.mapAlgEquiv σ).toRingHom ⊔
      H.modulus.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤ := by
    rw [← conjugate_extended_modulus K E σ H.modulus, ← Ideal.map_sup, hBm, Ideal.map_top]
  have hcu : (((conjugateCoprime K E σ H.modulus u : coprimeIdeals E _) :
      (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) *
        (B.map (RingOfIntegers.mapAlgEquiv σ).toRingHom : FractionalIdeal (𝓞 E)⁰ E) =
          (A.map (RingOfIntegers.mapAlgEquiv σ).toRingHom : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [conjugateCoprime_coe, ← conjugate_coeIdeal, ← conjugate_coeIdeal, ← huAB, map_mul]
    rfl
  rw [mem_normPreimage_iff]
  refine ⟨A * B.map (RingOfIntegers.mapAlgEquiv σ).toRingHom,
    B * A.map (RingOfIntegers.mapAlgEquiv σ).toRingHom, mul_ne_zero hA hσB, mul_ne_zero hB hσA,
    ?_, ?_, ?_, 1, one_mem _, ?_⟩
  · rw [Ideal.mul_sup_eq_of_coprime_left hAm, hσBm]
  · rw [Ideal.mul_sup_eq_of_coprime_left hBm, hσAm]
  · have hinv := Units.inv_mul
      ((conjugateCoprime K E σ H.modulus u : coprimeIdeals E _) : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    rw [Subgroup.coe_div, div_eq_mul_inv, Units.val_mul, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_mul, ← huAB, ← hcu]
    calc _ = ((u : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) * B *
          (B.map (RingOfIntegers.mapAlgEquiv σ).toRingHom : FractionalIdeal (𝓞 E)⁰ E) *
          ((((conjugateCoprime K E σ H.modulus u : coprimeIdeals E _) :
            (FractionalIdeal (𝓞 E)⁰ E)ˣ)⁻¹ : (FractionalIdeal (𝓞 E)⁰ E)ˣ) *
            (((conjugateCoprime K E σ H.modulus u : coprimeIdeals E _) :
              (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E)) := by ring
      _ = _ := by rw [hinv, mul_one]
  · rw [OneMemClass.coe_one, Units.val_one, one_mul, map_mul, map_mul, relNorm_conjugate,
      relNorm_conjugate, mul_comm]

/-- Norms of ray principal elements are ray principal, so the norm preimage is congruence. -/
theorem raySubgroup_le_normPreimage (H : CongruenceSubgroup K) :
    raySubgroup E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E))) ≤ normPreimage K E H := by
  have hR := rayGenerators_mem_coprimeIdeals E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E)))
  have key : ∀ x (_ : x ∈ Subgroup.closure
      (rayGenerators E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E))))),
      ∀ hM : x ∈ coprimeIdeals E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E))),
        (⟨x, hM⟩ : coprimeIdeals E _) ∈ normPreimage K E H := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      intro hM
      obtain ⟨α, hα, hα1, hxα⟩ := hx
      set N := Algebra.intNorm (𝓞 K) (𝓞 E) α with hNdef
      have hN0 : N ≠ 0 := Algebra.intNorm_ne_zero.mpr hα
      have hN1 : N - 1 ∈ H.modulus := intNorm_sub_one_mem K E H.modulus α hα1
      have hNK : (N : K) ≠ 0 := fun h => hN0 (RingOfIntegers.ext h)
      have hNne : FractionalIdeal.spanSingleton (𝓞 K)⁰ (N : K) ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr hNK
      have hNgen : Units.mk0 _ hNne ∈ rayGenerators K H.modulus := ⟨N, hN0, hN1, rfl⟩
      let v : coprimeIdeals K H.modulus :=
        ⟨Units.mk0 _ hNne, rayGenerators_mem_coprimeIdeals K H.modulus hNgen⟩
      have hv : v ∈ H.subgroup := H.contains_ray (Subgroup.subset_closure hNgen)
      rw [mem_normPreimage_iff]
      refine ⟨Ideal.span {α}, ⊤, by rwa [Ne, Ideal.span_singleton_eq_bot], top_ne_bot, ?_,
        top_sup_eq _, ?_, v, hv, ?_⟩
      · rw [Ideal.eq_top_iff_one]
        have h1 : α ∈ Ideal.span {α} ⊔ H.modulus.map (algebraMap (𝓞 K) (𝓞 E)) :=
          Ideal.mem_sup_left (Ideal.mem_span_singleton_self α)
        have h2 : α - 1 ∈ Ideal.span {α} ⊔ H.modulus.map (algebraMap (𝓞 K) (𝓞 E)) :=
          Ideal.mem_sup_right hα1
        have h3 := Ideal.sub_mem _ h1 h2
        rwa [sub_sub_cancel] at h3
      · change (x : FractionalIdeal (𝓞 E)⁰ E) * _ = _
        rw [hxα, FractionalIdeal.coeIdeal_top, mul_one, FractionalIdeal.coeIdeal_span_singleton]
      · rw [Ideal.relNorm_singleton, Ideal.relNorm_top, FractionalIdeal.coeIdeal_top, mul_one,
          FractionalIdeal.coeIdeal_span_singleton, ← hNdef]
        rfl
    | one => intro hM; exact (normPreimage K E H).one_mem
    | mul x y hx hy ihx ihy =>
      intro hM
      exact (normPreimage K E H).mul_mem (ihx ((Subgroup.closure_le _).mpr hR hx))
        (ihy ((Subgroup.closure_le _).mpr hR hy))
    | inv x hx ihx =>
      intro hM
      exact (normPreimage K E H).inv_mem (ihx ((Subgroup.closure_le _).mpr hR hx))
  intro u hu
  exact key _ hu u.2

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- Extension along the injective integer-ring map preserves a nonzero finite modulus. -/
theorem modulus_map_ne_bot (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    m.map (algebraMap (𝓞 K) (𝓞 E)) ≠ ⊥ := by
  exact Ideal.map_ne_bot_of_ne_bot hm

/-- The extended nonzero modulus together with the actual norm-preimage subgroup. -/
def normPreimageCongruence (H : CongruenceSubgroup K) : CongruenceSubgroup E where
  modulus := H.modulus.map (algebraMap (𝓞 K) (𝓞 E))
  modulus_ne_bot := modulus_map_ne_bot K E H.modulus H.modulus_ne_bot
  subgroup := normPreimage K E H
  contains_ray := raySubgroup_le_normPreimage K E H

/-- The source's equality σ(H_E)=H_E is an equality of represented ideal groups. -/
theorem normPreimageCongruence_conjugate (H : CongruenceSubgroup K) (σ : E ≃ₐ[K] E) :
    CongruenceEquivalent E
      (transportCongruence E σ.toRingEquiv (normPreimageCongruence K E H))
      (normPreimageCongruence K E H) := by
  have hM : (H.modulus.map (algebraMap (𝓞 K) (𝓞 E))).map
      (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom =
        H.modulus.map (algebraMap (𝓞 K) (𝓞 E)) := by
    rw [← mapAlgEquiv_toRingEquiv K E σ]
    exact conjugate_extended_modulus K E σ H.modulus
  have hamb : (normPreimageCongruence K E H).ambient.map
      (transportFractional E σ.toRingEquiv).toMonoidHom =
        (normPreimageCongruence K E H).ambient := by
    rw [← conjugateFractional_eq]
    apply le_antisymm
    · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨conjugateCoprime K E σ H.modulus u,
        (mem_normPreimage_conjugate_iff K E H σ u).mpr hu, conjugateCoprime_coe K E σ _ u⟩
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨_, ⟨conjugateCoprime K E σ.symm H.modulus u,
        (mem_normPreimage_conjugate_iff K E H σ.symm u).mpr hu, rfl⟩, ?_⟩
      have h := conjugateFractional_symm_apply K E σ.symm (u : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
      rw [AlgEquiv.symm_symm] at h
      exact h
  refine ⟨H.modulus.map (algebraMap (𝓞 K) (𝓞 E)), modulus_map_ne_bot K E H.modulus
    H.modulus_ne_bot, hM.ge, le_rfl, ?_⟩
  rw [transportCongruence_ambient, hamb]

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- A conjugate of an E-intermediate field still contains E when E/K is normal. -/
theorem exists_conjugate_intermediateField [Normal K E]
    {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra E Ω] [IsScalarTower K E Ω]
    [Normal K Ω] (L : IntermediateField E Ω) (σ : Ω ≃ₐ[K] Ω) :
    ∃ F : IntermediateField E Ω,
      F.restrictScalars K = (L.restrictScalars K).map σ.toAlgHom ∧
      ∃ τ : L ≃+* F, ∀ x : E,
        τ (algebraMap E L x) =
          algebraMap E F (AlgEquiv.restrictNormalHom E σ x) := by
  set F₀ := (L.restrictScalars K).map σ.toAlgHom with hF₀
  have hcomm : ∀ x : E,
      σ (algebraMap E Ω x) = algebraMap E Ω (AlgEquiv.restrictNormalHom E σ x) :=
    fun x => (AlgEquiv.restrictNormal_commutes σ E x).symm
  have hE : ∀ r : E, algebraMap E Ω r ∈ F₀ := fun r => by
    refine (IntermediateField.mem_map _).mpr
      ⟨algebraMap E Ω ((AlgEquiv.restrictNormalHom E σ).symm r), L.algebraMap_mem _, ?_⟩
    change σ _ = _
    rw [hcomm, AlgEquiv.apply_symm_apply]
  let F : IntermediateField E Ω :=
    { toSubalgebra := { toSubsemiring := F₀.toSubalgebra.toSubsemiring, algebraMap_mem' := hE }
      inv_mem' := fun x hx => F₀.inv_mem hx }
  have hmemF : ∀ x : L, σ (x : Ω) ∈ F := fun x => (IntermediateField.mem_map _).mpr ⟨x, x.2, rfl⟩
  have hmemL : ∀ y : F, σ.symm (y : Ω) ∈ L := fun y => by
    obtain ⟨x, hx, hxy⟩ := (IntermediateField.mem_map _).mp (y.2 : (y : Ω) ∈ F₀)
    rw [← hxy]
    simpa using hx
  refine ⟨F, IntermediateField.ext fun x => Iff.rfl,
    { toFun := fun x => ⟨σ (x : Ω), hmemF x⟩
      invFun := fun y => ⟨σ.symm (y : Ω), hmemL y⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : Ω))
      right_inv := fun y => Subtype.ext (σ.apply_symm_apply (y : Ω))
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : Ω) (y : Ω))
      map_add' := fun x y => Subtype.ext (map_add σ (x : Ω) (y : Ω)) }, fun x => ?_⟩
  apply Subtype.ext
  exact hcomm x

/-- Cross multiplication of integral representatives respects the relative norm. -/
theorem relNorm_cross_mul (A B C D : Ideal (𝓞 E))
    (h : (A : FractionalIdeal (𝓞 E)⁰ E) * D = C * B) :
    Ideal.relNorm (𝓞 K) A * Ideal.relNorm (𝓞 K) D =
      Ideal.relNorm (𝓞 K) C * Ideal.relNorm (𝓞 K) B := by
  rw [← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul] at h
  have h' : A * D = C * B := FractionalIdeal.coeIdeal_injective h
  rw [← map_mul, ← map_mul, h']

/-- The source's norm-preimage construction commutes with restriction of modulus. -/
theorem normPreimage_restrict (H : CongruenceSubgroup K)
    (m : Ideal (𝓞 K)) (hm0 : m ≠ ⊥) (hm : m ≤ H.modulus) :
    (normPreimage K E H).comap
        (Subgroup.inclusion (coprimeIdeals_mono E (Ideal.map_mono hm))) =
      normPreimage K E (restrictCongruence K H m hm0 hm) := by
  ext w
  rw [Subgroup.mem_comap, mem_normPreimage_iff]
  refine Iff.trans ?_ (mem_normPreimage_iff K E (restrictCongruence K H m hm0 hm) w).symm
  constructor
  · rintro ⟨A, B, hA, hB, -, -, hwAB, v, hv, hvn⟩
    rw [Subgroup.coe_inclusion] at hwAB
    obtain ⟨A', B', hA', hB', hA'm, hB'm, hw'⟩ := exists_coprime_ideal_quotient E _ w
    have hNA' : Ideal.relNorm (𝓞 K) A' ≠ ⊥ := Ideal.relNorm_eq_bot_iff.not.mpr hA'
    have hNB' : Ideal.relNorm (𝓞 K) B' ≠ ⊥ := Ideal.relNorm_eq_bot_iff.not.mpr hB'
    have hNA'ne : (Ideal.relNorm (𝓞 K) A' : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr hNA'
    have hNB'ne : (Ideal.relNorm (𝓞 K) B' : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr hNB'
    have hNB0 : (Ideal.relNorm (𝓞 K) B : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (Ideal.relNorm_eq_bot_iff.not.mpr hB)
    have ha : Units.mk0 _ hNA'ne ∈ coprimeIdeals K m :=
      Subgroup.subset_closure ⟨_, hNA', relNorm_coprime K E m A' hA'm, rfl⟩
    have hb : Units.mk0 _ hNB'ne ∈ coprimeIdeals K m :=
      Subgroup.subset_closure ⟨_, hNB', relNorm_coprime K E m B' hB'm, rfl⟩
    have hcross : (A : FractionalIdeal (𝓞 E)⁰ E) * B' = A' * B := by
      rw [← hwAB, ← hw']
      ring
    have hN := relNorm_cross_mul K E A B A' B' hcross
    have hvB' : ((v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
        (Ideal.relNorm (𝓞 K) B' : FractionalIdeal (𝓞 K)⁰ K) = Ideal.relNorm (𝓞 K) A' := by
      apply mul_right_cancel₀ hNB0
      calc _ = ((v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
            (Ideal.relNorm (𝓞 K) B : FractionalIdeal (𝓞 K)⁰ K) *
            (Ideal.relNorm (𝓞 K) B' : FractionalIdeal (𝓞 K)⁰ K) := by ring
        _ = ((Ideal.relNorm (𝓞 K) A * Ideal.relNorm (𝓞 K) B' : Ideal (𝓞 K)) :
            FractionalIdeal (𝓞 K)⁰ K) := by rw [hvn, FractionalIdeal.coeIdeal_mul]
        _ = _ := by rw [hN, FractionalIdeal.coeIdeal_mul]
    have key : ((Units.mk0 _ hNA'ne / Units.mk0 _ hNB'ne : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = ((v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) := by
      rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, ← hvB', mul_div_assoc,
        div_self hNB'ne, mul_one]
    refine ⟨A', B', hA', hB', hA'm, hB'm, hw', ⟨_, div_mem ha hb⟩, ?_, ?_⟩
    · refine (Subgroup.mem_comap (K := H.subgroup)
        (f := Subgroup.inclusion (coprimeIdeals_mono K hm))).mpr ?_
      convert hv
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
      exact Units.ext key
    · change ((Units.mk0 _ hNA'ne / Units.mk0 _ hNB'ne : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) * _ = _
      rw [key]
      exact hvB'
  · rintro ⟨A, B, hA, hB, hAm, hBm, hwAB, v, hv, hvn⟩
    have hle : m.map (algebraMap (𝓞 K) (𝓞 E)) ≤ H.modulus.map (algebraMap (𝓞 K) (𝓞 E)) :=
      Ideal.map_mono hm
    refine ⟨A, B, hA, hB, eq_top_mono (sup_le_sup_left hle A) hAm,
      eq_top_mono (sup_le_sup_left hle B) hBm, ?_,
      Subgroup.inclusion (coprimeIdeals_mono K hm) v,
      (Subgroup.mem_comap (K := H.subgroup)
        (f := Subgroup.inclusion (coprimeIdeals_mono K hm))).mp hv, ?_⟩
    · rw [Subgroup.coe_inclusion]
      exact hwAB
    · rw [Subgroup.coe_inclusion]
      exact hvn

/-- Choose a base modulus whose extension supports an exact upstairs Artin kernel. -/
theorem classField_normPreimage_at_base_modulus (H : CongruenceSubgroup K)
    (L : Type*) [Field L] [Algebra E L]
    (hL : IsClassFieldFor E (normPreimageCongruence K E H) L) :
    ∃ (m : Ideal (𝓞 K)) (hm0 : m ≠ ⊥) (hm : m ≤ H.modulus),
      HasArtinKernel E (m.map (algebraMap (𝓞 K) (𝓞 E))) L
        (normPreimage K E (restrictCongruence K H m hm0 hm)) := by
  obtain ⟨J, ⟨n, hn0, hnH, hnJ, hamb⟩, hJ⟩ := hL
  obtain ⟨d, hd0, hdH, hdn⟩ := exists_base_modulus K E H.modulus H.modulus_ne_bot n hn0
  refine ⟨d, hd0, hdH, ?_⟩
  have hK := hasArtinKernel_restrictModulus E (d.map (algebraMap (𝓞 K) (𝓞 E))) J.modulus
    (modulus_map_ne_bot K E d hd0) (hdn.trans hnJ) L J.subgroup hJ
  have hamb' : (normPreimageCongruence K E H).ambient ⊓
      coprimeIdeals E (d.map (algebraMap (𝓞 K) (𝓞 E))) =
        J.ambient ⊓ coprimeIdeals E (d.map (algebraMap (𝓞 K) (𝓞 E))) := by
    rw [← inf_eq_right.mpr (coprimeIdeals_mono E hdn), ← inf_assoc, ← inf_assoc, hamb]
  rw [← comap_inclusion_eq_of_inf_eq E (normPreimageCongruence K E H) J _
    (hdn.trans hnH) (hdn.trans hnJ) hamb'] at hK
  rw [← normPreimage_restrict K E H d hd0 hdH]
  exact hK

/-- Janusz V.7.2: conjugate extensions have the same norm-preimage ideal group. -/
theorem classField_normPreimage_conjugate [IsGalois K E]
    {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra E Ω] [IsScalarTower K E Ω]
    [Normal K Ω] (L : IntermediateField E Ω) [NumberField L]
    (H : CongruenceSubgroup K)
    (hL : IsClassFieldFor E (normPreimageCongruence K E H) L)
    (σ : Ω ≃ₐ[K] Ω) :
    (L.restrictScalars K).map σ.toAlgHom = L.restrictScalars K := by
  obtain ⟨F, hF, τ, hτ⟩ := exists_conjugate_intermediateField K E L σ
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  have hτ' : ∀ x, τ (algebraMap E L x) =
      algebraMap E F ((AlgEquiv.restrictNormalHom E σ).toRingEquiv x) := hτ
  haveI : FiniteDimensional E F :=
    finiteDimensional_semilinear E (AlgEquiv.restrictNormalHom E σ).toRingEquiv τ hτ'
  haveI : NumberField F := NumberField.of_module_finite E F
  have h1 := isClassFieldFor_semilinear E (AlgEquiv.restrictNormalHom E σ).toRingEquiv τ hτ' _ hL
  have h2 := isClassFieldFor_of_equivalent E _ _
    (normPreimageCongruence_conjugate K E H (AlgEquiv.restrictNormalHom E σ)) F h1
  have h3 := isClassFieldFor_eq E (normPreimageCongruence K E H) L F hL h2
  rw [← hF, ← h3]

section Tower
variable (L : Type*) [Field L] [NumberField L] [Algebra E L] [Algebra K L]
variable [IsScalarTower K E L]
variable [Module.Finite (𝓞 E) (𝓞 L)] [Module.Finite (𝓞 K) (𝓞 L)]

-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- Janusz V.7.2: invariance of all conjugates proves normality over K. -/
theorem classField_normPreimage_normal [IsGalois K E]
    (H : CongruenceSubgroup K)
    (hL : IsClassFieldFor E (normPreimageCongruence K E H) L) : Normal K L := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : IsAlgClosure K (AlgebraicClosure L) := IsAlgClosure.ofAlgebraic K L (AlgebraicClosure L)
  haveI : Normal K (AlgebraicClosure L) := IsAlgClosure.normal K (AlgebraicClosure L)
  let ιE : L →ₐ[E] AlgebraicClosure L := IsScalarTower.toAlgHom E L (AlgebraicClosure L)
  let ιK : L →ₐ[K] AlgebraicClosure L := IsScalarTower.toAlgHom K L (AlgebraicClosure L)
  let e : L ≃ₐ[E] ιE.fieldRange := AlgEquiv.ofInjectiveField ιE
  letI : NumberField ιE.fieldRange := NumberField.of_ringEquiv L _ e.toRingEquiv
  have hL' : IsClassFieldFor E (normPreimageCongruence K E H) ιE.fieldRange :=
    isClassFieldFor_of_algEquiv E _ e hL
  have hrange : ιK.fieldRange = ιE.fieldRange.restrictScalars K := by
    ext x
    rw [IntermediateField.mem_restrictScalars, AlgHom.mem_fieldRange, AlgHom.mem_fieldRange]
    rfl
  haveI hN : Normal K ιK.fieldRange := by
    rw [hrange]
    exact IntermediateField.normal_iff_forall_map_eq'.mpr fun σ =>
      classField_normPreimage_conjugate K E ιE.fieldRange H hL' σ
  let f : ιK.fieldRange ≃ₐ[K] L := (AlgEquiv.ofInjectiveField ιK).symm
  exact Normal.of_algEquiv f

-- The unused hypotheses are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Janusz V.7.2: arithmetic Artin maps commute with conjugation over K. -/
theorem artin_conjugation [IsGalois K E] [IsGalois K L]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (hU : IsUnramifiedAway E (m.map (algebraMap (𝓞 K) (𝓞 E))) L)
    (φ : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))) →* (L ≃ₐ[E] L))
    (hφ : IsArtinMap E (m.map (algebraMap (𝓞 K) (𝓞 E))) L φ)
    (σ : L ≃ₐ[K] L)
    (u : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E)))) :
    σ * (φ u).restrictScalars K * σ⁻¹ =
      (φ (conjugateCoprime K E (AlgEquiv.restrictNormalHom E σ) m u)).restrictScalars K := by
  haveI : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  have hτ : ∀ x : E, σ.toRingEquiv (algebraMap E L x) =
      algebraMap E L ((AlgEquiv.restrictNormalHom E σ).toRingEquiv x) :=
    fun x => (AlgEquiv.restrictNormal_commutes σ E x).symm
  have hM : m.map (algebraMap (𝓞 K) (𝓞 E)) ≤ (m.map (algebraMap (𝓞 K) (𝓞 E))).map
      (RingOfIntegers.mapRingEquiv (AlgEquiv.restrictNormalHom E σ).toRingEquiv).toRingHom := by
    rw [← mapAlgEquiv_toRingEquiv K E (AlgEquiv.restrictNormalHom E σ)]
    exact (conjugate_extended_modulus K E (AlgEquiv.restrictNormalHom E σ) m).ge
  have hψ := isArtinMap_comp_inclusion E L hM _
    (isArtinMap_semilinear E (AlgEquiv.restrictNormalHom E σ).toRingEquiv σ.toRingEquiv hτ
      (m.map (algebraMap (𝓞 K) (𝓞 E))) φ hφ)
  have heq := isArtinMap_unique E (m.map (algebraMap (𝓞 K) (𝓞 E))) L hU hφ hψ
  have hu' : (transportCoprime E (AlgEquiv.restrictNormalHom E σ).toRingEquiv
      (m.map (algebraMap (𝓞 K) (𝓞 E)))).symm (Subgroup.inclusion (coprimeIdeals_mono E hM)
        (conjugateCoprime K E (AlgEquiv.restrictNormalHom E σ) m u)) = u := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [Subgroup.coe_inclusion, conjugateCoprime_coe, transportCoprime_coe, conjugateFractional_eq]
  have hφc : φ (conjugateCoprime K E (AlgEquiv.restrictNormalHom E σ) m u) =
      semilinearAutEquiv E (AlgEquiv.restrictNormalHom E σ).toRingEquiv σ.toRingEquiv hτ
        (φ u) := by
    rw [DFunLike.congr_fun heq, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, hu']
  rw [hφc]
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := σ.surjective x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply,
    AlgEquiv.restrictScalars_apply, AlgEquiv.restrictScalars_apply]
  exact (semilinearAutEquiv_apply E (AlgEquiv.restrictNormalHom E σ).toRingEquiv σ.toRingEquiv
    hτ (φ u) y).symm

/-- The norm-one quotient and Artin surjectivity put the relative Galois kernel in the center. -/
theorem classField_normPreimage_ker_le_center [IsGalois K E] [IsGalois K L]
    (H : CongruenceSubgroup K)
    (hL : IsClassFieldFor E (normPreimageCongruence K E H) L) :
    (AlgEquiv.restrictNormalHom E : (L ≃ₐ[K] L) →* (E ≃ₐ[K] E)).ker ≤
      Subgroup.center (L ≃ₐ[K] L) := by
  obtain ⟨m, hm0, hm, hK⟩ := classField_normPreimage_at_base_modulus K E H L hL
  obtain ⟨-, -, -, hU, φ, hφ, hsurj, hφk⟩ := hK
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro σ
  have hgE : ∀ x : E, g.toRingEquiv (algebraMap E L x) = algebraMap E L x := by
    intro x
    have h1 := AlgEquiv.restrictNormal_commutes g E x
    have h2 : g.restrictNormal E = 1 := hg
    rw [h2, AlgEquiv.one_apply] at h1
    exact h1.symm
  obtain ⟨u, hu⟩ := hsurj (AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hgE)
  have hgu : g = (φ u).restrictScalars K := by
    ext x
    rw [hu]
    rfl
  have hconj := artin_conjugation K E L m hm0 hU φ hφ σ u
  have hker : u / conjugateCoprime K E (AlgEquiv.restrictNormalHom E σ) m u ∈ φ.ker := by
    rw [hφk]
    exact div_conjugate_mem_normPreimage K E (restrictCongruence K H m hm0 hm)
      (AlgEquiv.restrictNormalHom E σ) u
  rw [MonoidHom.mem_ker, map_div, div_eq_one] at hker
  rw [← hker, ← hgu] at hconj
  exact mul_inv_eq_iff_eq_mul.mp hconj

/-- Janusz V.7.2: central relative kernel and cyclic quotient give an abelian total group. -/
theorem classField_normPreimage_commutative [IsGalois K E] [IsGalois K L]
    [IsCyclic (E ≃ₐ[K] E)] (H : CongruenceSubgroup K)
    (hL : IsClassFieldFor E (normPreimageCongruence K E H) L) :
    IsMulCommutative (L ≃ₐ[K] L) := by
  exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (AlgEquiv.restrictNormalHom E)
    (classField_normPreimage_ker_le_center K E L H hL)

/-- Janusz V.7.2: relative norm transitivity takes the upstairs norm image into H. -/
theorem normImage_transitivity_le (H : CongruenceSubgroup K)
    (hN : normImage E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E))) L ≤
      normPreimage K E H) :
    normImage K H.modulus L ≤ H.subgroup := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro u ⟨A, hA, hAm, hu⟩
  have hML : (H.modulus.map (algebraMap (𝓞 K) (𝓞 E))).map (algebraMap (𝓞 E) (𝓞 L)) =
      H.modulus.map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hAE : Ideal.relNorm (𝓞 E) A ≠ ⊥ := Ideal.relNorm_eq_bot_iff.not.mpr hA
  have hAEm : Ideal.relNorm (𝓞 E) A ⊔ H.modulus.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤ :=
    relNorm_coprime E L _ A (by rw [hML]; exact hAm)
  have hAEne : (Ideal.relNorm (𝓞 E) A : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hAE
  let w : coprimeIdeals E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E))) :=
    ⟨Units.mk0 _ hAEne, Subgroup.subset_closure ⟨_, hAE, hAEm, rfl⟩⟩
  have hw : w ∈ normImage E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E))) L :=
    Subgroup.subset_closure ⟨A, hA, by rw [hML]; exact hAm, rfl⟩
  have hw' := hN hw
  rw [mem_normPreimage_iff] at hw'
  obtain ⟨A', B', -, hB', -, -, hwAB, v, hv, hvn⟩ := hw'
  have h1' : ((Ideal.relNorm (𝓞 E) A * B' : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = A' := by
    rw [FractionalIdeal.coeIdeal_mul]
    exact hwAB
  have h1 : Ideal.relNorm (𝓞 E) A * B' = A' := FractionalIdeal.coeIdeal_injective h1'
  have hNB'ne : (Ideal.relNorm (𝓞 K) B' : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (Ideal.relNorm_eq_bot_iff.not.mpr hB')
  have h3 : ((v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      Ideal.relNorm (𝓞 K) (Ideal.relNorm (𝓞 E) A) := by
    apply mul_right_cancel₀ hNB'ne
    rw [hvn, ← FractionalIdeal.coeIdeal_mul, ← map_mul, h1]
  have huv : u = v := by
    apply Subtype.ext
    apply Units.ext
    rw [hu, h3, Ideal.relNorm_relNorm (𝓞 K) (𝓞 E) A]
  rw [SetLike.mem_coe, huv]
  exact hv

end Tower

/-- An isomorphic embedded copy realizes the same class-field predicate. -/
theorem hasClassField_of_isClassFieldFor (H : CongruenceSubgroup K)
    (F : Type*) [Field F] [Algebra K F]
    (hF : IsClassFieldFor K H F) : HasClassField K H := by
  obtain ⟨J, hHJ, hJ⟩ := hF
  haveI := hJ.finiteDimensional
  let ι : F →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let e : F ≃ₐ[K] ι.fieldRange := AlgEquiv.ofInjectiveField ι
  exact ⟨ι.fieldRange, isClassFieldFor_of_algEquiv K H e ⟨J, hHJ, hJ⟩⟩

/-- Class-field existence depends only on the represented ideal group. -/
theorem hasClassField_of_equivalent (H J : CongruenceSubgroup K)
    (hHJ : CongruenceEquivalent K H J) (hH : HasClassField K H) : HasClassField K J := by
  obtain ⟨L, hL⟩ := hH
  exact ⟨L, isClassFieldFor_of_equivalent K H J hHJ L hL⟩

/-- Janusz V.7.1: an abelian extension with its norm image in H supplies a class subfield. -/
theorem hasClassField_of_normImage_le [IsTotallyComplex K]
    (F : Type*) [Field F] [NumberField F] [Algebra K F] [IsAbelianGalois K F]
    [Module.Finite (𝓞 K) (𝓞 F)]
    (H : CongruenceSubgroup K) (hN : normImage K H.modulus F ≤ H.subgroup) :
    HasClassField K H := by
  obtain ⟨m₀, hm₀, -, hK₀⟩ := artin_reciprocity K F
  have hm0 : m₀ * H.modulus ≠ ⊥ := mul_ne_zero hm₀ H.modulus_ne_bot
  have hmH : m₀ * H.modulus ≤ H.modulus := Ideal.mul_le_left
  obtain ⟨-, -, -, hU, φ, hφ, hsurj, hφk⟩ := hK₀ _ hm0 Ideal.mul_le_right
  have hle : φ.ker ≤ H.subgroup.comap (Subgroup.inclusion (coprimeIdeals_mono K hmH)) := by
    rw [hφk]
    refine sup_le ?_ (raySubgroup_le_restrict K H _ hmH)
    rw [← Subgroup.map_le_iff_le_comap]
    exact (normImage_restrictModulus K F _ _ hmH).trans hN
  exact hasClassField_of_isClassFieldFor K H _
    ⟨restrictCongruence K H _ hm0 hmH, restrictCongruence_equivalent K H _ hm0 hmH,
      hasArtinKernel_fixedField K _ F hU φ hφ hsurj _ hle⟩

/-- Janusz V.7.2: descend existence along a cyclic base-field extension. -/
theorem classField_descends_cyclic [IsTotallyComplex K] [IsGalois K E]
    [IsCyclic (E ≃ₐ[K] E)] (H : CongruenceSubgroup K)
    (hE : HasClassField E (normPreimageCongruence K E H)) : HasClassField K H := by
  obtain ⟨L, J, hHJ, hJ⟩ := hE
  haveI : FiniteDimensional E L := hJ.finiteDimensional
  haveI : NumberField L := NumberField.of_module_finite E L
  haveI : Module.Finite (𝓞 E) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) (𝓞 L)
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)
  have hL : IsClassFieldFor E (normPreimageCongruence K E H) L := ⟨J, hHJ, hJ⟩
  haveI : Normal K L := classField_normPreimage_normal K E L H hL
  haveI : IsGalois K L := IsGalois.mk
  haveI : IsMulCommutative (L ≃ₐ[K] L) := classField_normPreimage_commutative K E L H hL
  haveI : IsAbelianGalois K L := ⟨⟩
  obtain ⟨m, hm0, hm, hK⟩ := classField_normPreimage_at_base_modulus K E H L hL
  obtain ⟨-, hgal, -, hU, φ, hφ, -, hφk⟩ := hK
  haveI := hgal
  have hNE : normImage E (m.map (algebraMap (𝓞 K) (𝓞 E))) L ≤
      normPreimage K E (restrictCongruence K H m hm0 hm) := by
    rw [← hφk]
    exact normImage_le_artin_ker E _ L hU φ hφ
  have hNK := normImage_transitivity_le K E L (restrictCongruence K H m hm0 hm) hNE
  exact hasClassField_of_equivalent K _ H
    ((congruenceEquivalent_equivalence K).symm (restrictCongruence_equivalent K H m hm0 hm))
    (hasClassField_of_normImage_le K L (restrictCongruence K H m hm0 hm) hNK)

end Descent

end Cox.ClassFieldTheory
