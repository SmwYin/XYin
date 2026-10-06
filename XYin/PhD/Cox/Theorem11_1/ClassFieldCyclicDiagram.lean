/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicHexagons
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealExtension
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealTate
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicCardinality
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalNorm

/-!
# Cyclic cardinality and the norm/principal square

The Herbrand quotient uses Janusz's convention H¹/H⁰_Tate.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise WithZero

noncomputable section

namespace Cox.ClassFieldTheory

open Cox.CyclicCohomology

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

variable [hGalois : IsGalois K L]
include hGalois

section SquareTransport

variable {A B C D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
variable {f : A →+ B} {g : C →+ D} {e : A ≃+ C} {d : B ≃+ D}

omit hGalois in
/-- A commuting square with equivalences on both sides identifies the two kernels. -/
theorem squareTransport_ker_eq (h : d.toAddMonoidHom.comp f = g.comp e.toAddMonoidHom) :
    f.ker = g.ker.map e.symm.toAddMonoidHom :=
  (AddMonoidHom.ker_addEquiv_comp f d).symm.trans
    ((congrArg AddMonoidHom.ker h).trans (AddMonoidHom.ker_comp_addEquiv g e))

omit hGalois in
/-- A commuting square with equivalences on both sides preserves the kernel cardinality. -/
theorem squareTransport_card_ker (h : d.toAddMonoidHom.comp f = g.comp e.toAddMonoidHom) :
    Nat.card f.ker = Nat.card g.ker := by
  rw [squareTransport_ker_eq h]
  exact AddSubgroup.card_map_of_injective e.symm.injective

omit hGalois in
/-- A commuting square with equivalences on both sides preserves the range index. -/
theorem squareTransport_index (h : d.toAddMonoidHom.comp f = g.comp e.toAddMonoidHom) :
    g.range.index = f.range.index := by
  have hr : g.range = f.range.map d.toAddMonoidHom := by
    have hh := congrArg AddMonoidHom.range h
    have he : e.toAddMonoidHom.range = ⊤ := AddMonoidHom.range_eq_top.mpr e.surjective
    simpa only [AddMonoidHom.range_comp, he, ← AddMonoidHom.range_eq_map] using hh.symm
  rw [hr]
  exact AddSubgroup.index_map_equiv _ d

omit hGalois in
/-- The kernel of an additivized group homomorphism has the same elements. -/
def toAdditiveKerEquiv {G H : Type*} [Group G] [Group H] (f : G →* H) :
    f.toAdditive.ker ≃ f.ker where
  toFun z := ⟨Additive.toMul z.1, z.2⟩
  invFun z := ⟨Additive.ofMul z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit hGalois in
/-- Clearing the common finite factor in a cardinal identity gives the quotient identity. -/
theorem ratio_of_cleared {i k a0 a1 v0 v1 : ℕ} (hk : 0 < k) (ha0 : 0 < a0) (hv0 : 0 < v0)
    (hcard : i * a0 * v1 = k * a1 * v0) (hv : (v1 : ℚ) / v0 = 1) :
    (i : ℚ) / k = a1 / a0 := by
  have hv' : v1 = v0 := by
    have h := (div_eq_one_iff_eq (by exact_mod_cast hv0.ne')).mp hv
    exact_mod_cast h
  subst hv'
  have h := Nat.eq_of_mul_eq_mul_right hv0 hcard
  rw [div_eq_div_iff (by exact_mod_cast hk.ne') (by exact_mod_cast ha0.ne')]
  exact_mod_cast h.trans (mul_comm _ _)

end SquareTransport

-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
omit hGalois in
/-- The finite literal quotient V has two finite Tate groups. -/
theorem principalCokernel_finiteHerbrand (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) :
    FiniteHerbrand (principalCokernelRepresentation K L m) σ := by
  haveI : Finite ((awayIdealSubmodule K L m) ⧸ principalImageSubmodule K L m) :=
    principalAway_cokernel_finite K L m
  exact finiteHerbrand_of_finite _ σ

-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
omit hGalois in
/-- The source's finite V contributes a Herbrand quotient of one. -/
theorem principalCokernel_herbrandQuotient (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) :
    herbrandQuotient (principalCokernelRepresentation K L m) σ = 1 := by
  haveI : Finite ((awayIdealSubmodule K L m) ⧸ principalImageSubmodule K L m) :=
    principalAway_cokernel_finite K L m
  exact herbrandQuotient_eq_one_of_finite _ σ

-- `hGalois` is included for the whole section; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Both finite end-group pairs, rather than an embedding into H⁰(S), bound the kernel. -/
theorem principalTateComposite_ker_finite (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Finite ((principalTateBeta K L m σ).comp (principalTateAlpha K L m σ)).ker := by
  have hS := sUnit_finiteHerbrand K L m hm σ hσ
  have hV := principalCokernel_finiteHerbrand K L m hm σ
  haveI := hS.1
  haveI := hS.2
  haveI := hV.1
  haveI := hV.2
  exact punctured_composite_kernel_finite
    (tateZeroMap (sUnitRepresentation K L m)
      (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ (sUnitInclusion K L m))
    (principalTateAlpha K L m σ) (principalSecondLeft K L m σ) (principalTateBeta K L m σ)
    (principal_firstHexagon_B0 K L m σ) (principal_secondHexagon_A0 K L m σ)

/-- The same two rows have a composite with finite cokernel. -/
theorem principalTateComposite_range_finiteIndex (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    ((principalTateBeta K L m σ).comp (principalTateAlpha K L m σ)).range.FiniteIndex := by
  have hS := sUnit_finiteHerbrand K L m hm σ hσ
  have hV := principalCokernel_finiteHerbrand K L m hm σ
  haveI := hS.1
  haveI := hS.2
  haveI := hV.1
  haveI := hV.2
  exact punctured_composite_cokernel_finite (principalTateAlpha K L m σ)
    (principalFirstRight K L m σ) (principalTateBeta K L m σ)
    (tateZeroMap (awayIdealRepresentation K L m) (principalCokernelRepresentation K L m) σ
      (principalCokernelProjection K L m))
    (principalFirstRight_surjective K L m σ hσ) (principal_firstHexagon_C0 K L m σ)
    (principal_secondHexagon_B0 K L m σ)

/-- The punctured cardinal identity specialized to the two literal source rows. -/
theorem principalTateComposite_index_card (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    ((principalTateBeta K L m σ).comp (principalTateAlpha K L m σ)).range.index *
        Nat.card (tateZero (sUnitRepresentation K L m) σ) *
        Nat.card (tateOne (principalCokernelRepresentation K L m) σ) =
      Nat.card ((principalTateBeta K L m σ).comp (principalTateAlpha K L m σ)).ker *
        Nat.card (tateOne (sUnitRepresentation K L m) σ) *
        Nat.card (tateZero (principalCokernelRepresentation K L m) σ) := by
  have hS := sUnit_finiteHerbrand K L m hm σ hσ
  have hV := principalCokernel_finiteHerbrand K L m hm σ
  haveI := hS.1
  haveI := hS.2
  haveI := hV.1
  haveI := hV.2
  exact punctured_index_card (principalFirstLeft K L m σ)
    (tateZeroMap (sUnitRepresentation K L m)
      (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ (sUnitInclusion K L m))
    (principalTateAlpha K L m σ) (principalFirstRight K L m σ)
    (principalSecondLeft K L m σ) (principalTateBeta K L m σ)
    (tateZeroMap (awayIdealRepresentation K L m) (principalCokernelRepresentation K L m) σ
      (principalCokernelProjection K L m)) (principalSecondRight K L m σ)
    (principalFirstLeft_injective K L m σ hσ) (principalFirstRight_surjective K L m σ hσ)
    (principalSecondLeft_injective K L m σ hσ) (principalSecondRight_surjective K L m σ hσ)
    (principal_firstHexagon_A0 K L m σ) (principal_firstHexagon_B0 K L m σ)
    (principal_firstHexagon_C0 K L m σ) (principal_secondHexagon_A0 K L m σ)
    (principal_secondHexagon_B0 K L m σ) (principal_secondHexagon_C0 K L m σ)

/-- The common finite V cancels, leaving precisely the S-unit Herbrand quotient. -/
theorem principalTateComposite_index_ratio (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    (((principalTateBeta K L m σ).comp (principalTateAlpha K L m σ)).range.index : ℚ) /
        Nat.card ((principalTateBeta K L m σ).comp (principalTateAlpha K L m σ)).ker =
      herbrandQuotient (sUnitRepresentation K L m) σ := by
  have hcard := principalTateComposite_index_card K L m hm σ hσ
  have hS := sUnit_finiteHerbrand K L m hm σ hσ
  have hV := principalCokernel_finiteHerbrand K L m hm σ
  haveI := hS.1
  haveI := hV.1
  haveI := principalTateComposite_ker_finite K L m hm σ hσ
  haveI : Nonempty (tateZero (sUnitRepresentation K L m) σ) := ⟨0⟩
  haveI : Nonempty (tateZero (principalCokernelRepresentation K L m) σ) := ⟨0⟩
  haveI : Nonempty ((principalTateBeta K L m σ).comp (principalTateAlpha K L m σ)).ker := ⟨0⟩
  have ha0 : 0 < Nat.card (tateZero (sUnitRepresentation K L m) σ) := Nat.card_pos
  have hv0 : 0 < Nat.card (tateZero (principalCokernelRepresentation K L m) σ) := Nat.card_pos
  have hk : 0 < Nat.card ((principalTateBeta K L m σ).comp (principalTateAlpha K L m σ)).ker :=
    Nat.card_pos
  exact ratio_of_cleared hk ha0 hv0 hcard (principalCokernel_herbrandQuotient K L m hm σ)

/-- Field elements whose principal ideals belong to the relative ideal norm image. -/
def principalIdealNormElements (m : Ideal (𝓞 K)) : Subgroup Kˣ :=
  ((normImage K m L).map (coprimeIdeals K m).subtype).comap (toPrincipalIdeal (𝓞 K) K)

/-- Janusz V.4.1's correction index n(m), defined independently of the desired equality. -/
def normCorrectionIndex (m : Ideal (𝓞 K)) : ℕ :=
  (rayElements K m ⊓ elementNormGroup K L).relIndex
    (rayElements K m ⊓ principalIdealNormElements K L m)

-- `hGalois` is included for the whole section; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- The principal-ideal map with modulus factors erased descends through actual norms.
This is the map f₀ in the upper row of Janusz V.4.1. -/
theorem exists_normPrincipalMap (m : Ideal (𝓞 K)) :
    ∃ f₀ : (Kˣ ⧸ elementNormGroup K L) →*
        (coprimeIdeals K m ⧸ normImage K m L),
      ∀ x : Kˣ, f₀ (QuotientGroup.mk x) = QuotientGroup.mk
        (eraseModulusFactors K m (toPrincipalIdeal (𝓞 K) K x)) := by
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)
  let φ : Kˣ →* coprimeIdeals K m ⧸ normImage K m L :=
    (QuotientGroup.mk' (normImage K m L)).comp
      ((eraseModulusFactors K m).comp (toPrincipalIdeal (𝓞 K) K))
  have hle : elementNormGroup K L ≤ φ.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk (eraseModulusFactors K m
      (toPrincipalIdeal (𝓞 K) K (Units.map (Algebra.norm K : L →* K) y))) :
        coprimeIdeals K m ⧸ normImage K m L) = 1
    rw [QuotientGroup.eq_one_iff, ← idealUnitNorm_principal K L y]
    convert idealUnitNorm_mem_normImage K L m (eraseModulusFactors L
      (m.map (algebraMap (𝓞 K) (𝓞 L))) (toPrincipalIdeal (𝓞 L) L y)) using 1
    exact Subtype.ext (idealUnitNorm_erase K L m _).symm
  exact ⟨QuotientGroup.lift (elementNormGroup K L) φ hle, fun x => rfl⟩

/-- The induced norm/principal map, characterized on representatives. -/
def normPrincipalMap (m : Ideal (𝓞 K)) :
    (Kˣ ⧸ elementNormGroup K L) →* (coprimeIdeals K m ⧸ normImage K m L) :=
  Classical.choose (exists_normPrincipalMap K L m)

/-- The source square commutes for the specified equivalences and the actual map f₀. -/
theorem normPrincipalMap_tate_commutes (m : Ideal (𝓞 K))
    (hU : IsUnramifiedAway K m L) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (a : tateZero (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ) :
    awayIdealTateEquiv K L m hU σ hσ
        ((principalTateBeta K L m σ) (principalTateAlpha K L m σ a)) =
      Additive.ofMul ((normPrincipalMap K L m)
        (Additive.toMul (fieldUnitsTateEquiv K L σ hσ a))) := by
  -- The proof is a chain of equalities: tactics that re-check this goal are very slow,
  -- because the goal mixes the field-unit and Hexagon presentations of one Tate group.
  have hf0 : ∀ x : Kˣ, normPrincipalMap K L m (QuotientGroup.mk x) =
      QuotientGroup.mk (eraseModulusFactors K m (toPrincipalIdeal (𝓞 K) K x)) :=
    Classical.choose_spec (exists_normPrincipalMap K L m)
  have hq := QuotientGroup.mk_surjective (Additive.toMul (fieldUnitsTateEquiv K L σ hσ a))
  have hx : QuotientGroup.mk (Classical.choose hq) =
      Additive.toMul (fieldUnitsTateEquiv K L σ hσ a) := Classical.choose_spec hq
  have hEa : fieldUnitsTateEquiv K L σ hσ a =
      Additive.ofMul (QuotientGroup.mk (Classical.choose hq)) :=
    (congrArg Additive.ofMul hx).symm
  have ha := ((fieldUnitsTateEquiv K L σ hσ).symm_apply_apply a).symm.trans
    (congrArg (fieldUnitsTateEquiv K L σ hσ).symm hEa)
  have hR := (congrArg (fun q => Additive.ofMul (normPrincipalMap K L m q)) hx.symm).trans
    (congrArg Additive.ofMul (hf0 (Classical.choose hq)))
  have hL := congrArg (fun z => awayIdealTateEquiv K L m hU σ hσ
    ((principalTateBeta K L m σ) (principalTateAlpha K L m σ z))) ha
  have hE0 := fieldUnitsTateEquiv_apply K L σ hσ (Classical.choose hq)
    (fixedFieldUnitMap K L σ (Additive.ofMul (Classical.choose hq))) rfl
  have hz := (fieldUnitsTateEquiv K L σ hσ).injective
    (((fieldUnitsTateEquiv K L σ hσ).apply_symm_apply _).trans hE0.symm)
  have hL' := hL.trans (congrArg (fun z => awayIdealTateEquiv K L m hU σ hσ
    ((principalTateBeta K L m σ) (principalTateAlpha K L m σ z))) hz)
  have hm1 := map_mem_ker_difference (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)
    (principalImageRepresentation K L m) σ (principalImageProjection K L m)
    (fixedFieldUnitMap K L σ (Additive.ofMul (Classical.choose hq)))
  have hα := tateZeroMap_apply (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)
    (principalImageRepresentation K L m) σ (principalImageProjection K L m)
    (fixedFieldUnitMap K L σ (Additive.ofMul (Classical.choose hq))) ⟨_, hm1⟩ rfl
  have hm2 := map_mem_ker_difference (principalImageRepresentation K L m)
    (awayIdealRepresentation K L m) σ (principalImageInclusion K L m) ⟨_, hm1⟩
  have hβ := tateZeroMap_apply (principalImageRepresentation K L m)
    (awayIdealRepresentation K L m) σ (principalImageInclusion K L m) ⟨_, hm1⟩ ⟨_, hm2⟩ rfl
  have hval := congrArg (fun z : awayIdealSubmodule K L m =>
    Additive.toMul (z : Additive (FractionalIdeal (𝓞 L)⁰ L)ˣ))
    (principalAway_base_unit K L m (Classical.choose hq))
  have hD := awayIdealTateEquiv_apply K L m hU σ hσ
    (eraseModulusFactors K m (toPrincipalIdeal (𝓞 K) K (Classical.choose hq))) ⟨_, hm2⟩ hval
  exact hL'.trans ((congrArg (awayIdealTateEquiv K L m hU σ hσ)
    ((congrArg (principalTateBeta K L m σ) hα).trans hβ)).trans (hD.trans hR.symm))

/-- The commuting square as an equality of additive homomorphisms. -/
theorem normPrincipal_square (m : Ideal (𝓞 K)) (hU : IsUnramifiedAway K m L)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    (awayIdealTateEquiv K L m hU σ hσ).toAddMonoidHom.comp
        ((principalTateBeta K L m σ).comp (principalTateAlpha K L m σ)) =
      (normPrincipalMap K L m).toAdditive.comp (fieldUnitsTateEquiv K L σ hσ).toAddMonoidHom := by
  ext a
  exact normPrincipalMap_tate_commutes K L m hU σ hσ a

/-- The two exact hexagons express the kernel of f₀ using finite S-unit and cokernel Tate groups. -/
theorem normPrincipalMap_ker_finite (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (hU : IsUnramifiedAway K m L) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) : Finite (normPrincipalMap K L m).ker := by
  have hsq := normPrincipal_square K L m hU σ hσ
  haveI := principalTateComposite_ker_finite K L m hm σ hσ
  have hk := squareTransport_ker_eq hsq
  haveI : Finite ((normPrincipalMap K L m).toAdditive.ker.map
      (fieldUnitsTateEquiv K L σ hσ).symm.toAddMonoidHom) := hk ▸ inferInstance
  haveI : Finite (normPrincipalMap K L m).toAdditive.ker := Finite.of_equiv _
    (AddSubgroup.equivMapOfInjective _ (fieldUnitsTateEquiv K L σ hσ).symm.toAddMonoidHom
      (fieldUnitsTateEquiv K L σ hσ).symm.injective).symm.toEquiv
  exact Finite.of_equiv _ (toAdditiveKerEquiv (normPrincipalMap K L m))

/-- The second exact hexagon and finite ideal-class quotient make the cokernel finite. -/
theorem normPrincipalMap_range_finiteIndex (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (hU : IsUnramifiedAway K m L) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    (normPrincipalMap K L m).range.FiniteIndex := by
  have hsq := normPrincipal_square K L m hU σ hσ
  haveI := principalTateComposite_range_finiteIndex K L m hm σ hσ
  rw [Subgroup.finiteIndex_iff, ← Subgroup.index_toAddSubgroup, ← MonoidHom.coe_toAdditive_range,
    squareTransport_index hsq]
  exact AddSubgroup.FiniteIndex.index_ne_zero

/-- Janusz V.4.2: combining the two exact hexagons cancels their common middle group;
no finiteness assertion is made about H⁰ of all field units. -/
theorem normPrincipalMap_index_ratio (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (hU : IsUnramifiedAway K m L) (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    ((normPrincipalMap K L m).range.index : ℚ) / Nat.card (normPrincipalMap K L m).ker =
      herbrandQuotient (sUnitRepresentation K L m) σ := by
  have hsq := normPrincipal_square K L m hU σ hσ
  have h1 := (Subgroup.index_toAddSubgroup (H := (normPrincipalMap K L m).range)).symm.trans
    ((congrArg AddSubgroup.index
      (MonoidHom.coe_toAdditive_range (normPrincipalMap K L m)).symm).trans
        (squareTransport_index hsq))
  have h2 := (Nat.card_congr (toAdditiveKerEquiv (normPrincipalMap K L m))).symm.trans
    (squareTransport_card_ker hsq).symm
  exact (congrArg₂ (fun p q : ℕ => (p : ℚ) / q) h1 h2).trans
    (principalTateComposite_index_ratio K L m hm σ hσ)


end Cox.ClassFieldTheory
