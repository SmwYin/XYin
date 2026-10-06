/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalTranslation
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnramifiedModulus
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalPairedNorm
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalSplitDescent

/-! # Comparison at a common finer modulus in Janusz V.11.2

Passing to a finer comparison modulus avoids assuming any assertion about the
ramification of the translated field at the chosen prime: the Artin kernels of the
compositum and of the given class field are compared at one base-extended modulus, and
classification by Artin kernels produces the embedding.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K E F : Type*) [Field K] [hNF_K : NumberField K] [Field E] [hNF_E : NumberField E]
  [Field F] [hNF_F : NumberField F] [Algebra K E] [Algebra K F]

/-- Exact Artin kernels transport along isomorphisms of extensions over the same base. -/
theorem hasArtinKernel_of_algEquiv (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (L L' : Type*) [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra K L]
    [Algebra K L'] (e : L ≃ₐ[K] L') {H : Subgroup (coprimeIdeals K m)}
    (h : HasArtinKernel K m L H) : HasArtinKernel K m L' H := by
  obtain ⟨hfin, hgal, hcomm, hU, φ, hφ, hsurj, hφk⟩ := h
  haveI := hfin
  haveI := hgal
  refine ⟨e.toLinearEquiv.finiteDimensional, IsGalois.of_algEquiv e, ?_,
    CyclicReciprocity.unramified_transport K m L L' e hU, e.autCongr.toMonoidHom.comp φ,
    CyclicReciprocity.artin_transport K m L L' e φ hφ, e.autCongr.surjective.comp hsurj, ?_⟩
  · refine ⟨⟨fun a b => e.autCongr.symm.injective ?_⟩⟩
    rw [map_mul, map_mul]
    exact hcomm.is_comm.comm _ _
  · rw [← hφk]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.autCongr.injective]

include hNF_K hNF_E hNF_F in
/-- Classification is independent of the chosen algebraic-closure models. -/
theorem exists_algHom_of_artin_kernel_le (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    {H J : Subgroup (coprimeIdeals K m)}
    (hE : HasArtinKernel K m E H) (hF : HasArtinKernel K m F J) (h : J ≤ H) :
    Nonempty (E →ₐ[K] F) := by
  haveI := hE.finiteDimensional
  haveI := hF.finiteDimensional
  let ιE : E →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let ιF : F →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let eE : E ≃ₐ[K] ιE.fieldRange := AlgEquiv.ofInjectiveField ιE
  let eF : F ≃ₐ[K] ιF.fieldRange := AlgEquiv.ofInjectiveField ιF
  letI : NumberField ιE.fieldRange := NumberField.of_ringEquiv E _ eE.toRingEquiv
  letI : NumberField ιF.fieldRange := NumberField.of_ringEquiv F _ eF.toRingEquiv
  have hE' := hasArtinKernel_of_algEquiv K m E _ eE hE
  have hF' := hasArtinKernel_of_algEquiv K m F _ eF hF
  have hle : ιE.fieldRange ≤ ιF.fieldRange :=
    (le_iff_artinKernel_le ιE.fieldRange ιF.fieldRange m hm hE' hF').mpr h
  exact ⟨((eF.symm.toAlgHom).comp (IntermediateField.inclusion hle)).comp eE.toAlgHom⟩

include hNF_K hNF_E hNF_F in
/-- Complete splitting descends along an embedding fixing the base field. -/
theorem splittingIdeals_of_algHom (ι : E →ₐ[K] F)
    {p : Ideal (𝓞 K)} (hp : p ∈ splittingIdeals K F) :
    p ∈ splittingIdeals K E := by
  obtain ⟨hpp, hp0, hsplit⟩ := hp
  letI : Algebra E F := ι.toRingHom.toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  refine ⟨hpp, hp0, fun P hP => ?_⟩
  obtain ⟨hPp, hPo⟩ := hP
  haveI := hpp
  haveI := hPp
  haveI := hPo
  haveI : p.IsMaximal := hpp.isMaximal hp0
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  haveI : P.IsMaximal := hPp.isMaximal hP0
  obtain ⟨Q, hQp, hQc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) P (by simp)
  haveI := hQp
  haveI : Q.LiesOver P := ⟨hQc.symm⟩
  haveI : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  obtain ⟨he, hf⟩ := hsplit Q ⟨hQp, inferInstance⟩
  rw [Ideal.ramificationIdx_algebra_tower' p P Q] at he
  rw [Ideal.inertiaDeg_algebra_tower p P Q] at hf
  exact ⟨Nat.eq_one_of_mul_eq_one_right he, Nat.eq_one_of_mul_eq_one_right hf⟩

include hNF_K hNF_E hNF_F in
/-- A supplied pair of Artin maps can be compared after refining to one modulus. -/
theorem exists_common_unramified_modulus [IsGalois K E] [IsGalois K F]
    (m n : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hn : n ≠ ⊥) :
    ∃ r : Ideal (𝓞 K), r ≠ ⊥ ∧ r ≤ m ∧ r ≤ n ∧
      IsUnramifiedAway K r E ∧ IsUnramifiedAway K r F := by
  obtain ⟨rE, hrE0, hrE⟩ := exists_unramifiedAway_modulus K E
  obtain ⟨rF, hrF0, hrF⟩ := exists_unramifiedAway_modulus K F
  refine ⟨m * n * (rE * rF), mul_ne_zero (mul_ne_zero hm hn) (mul_ne_zero hrE0 hrF0),
    Ideal.mul_le_right.trans Ideal.mul_le_right, Ideal.mul_le_right.trans Ideal.mul_le_left,
    fun q hq hq0 hqr => hrE q hq hq0 (eq_top_mono
      (sup_le_sup_left (Ideal.mul_le_left.trans Ideal.mul_le_right) q) hqr),
    fun q hq hq0 hqr => hrF q hq hq0 (eq_top_mono
      (sup_le_sup_left (Ideal.mul_le_left.trans Ideal.mul_le_left) q) hqr)⟩

variable (B : Type*) [Field B] [hNF_B : NumberField B]
  [Algebra K B] [Algebra B F] [Algebra E F]
  [IsScalarTower K B F] [IsScalarTower K E F]

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
include hNF_K hNF_E hNF_F hNF_B in
/-- A compositum of an abelian Galois extension with any base extension remains abelian Galois. -/
theorem isAbelianGalois_compositum [IsAbelianGalois K E]
    (hgen : Algebra.adjoin B (Set.range (algebraMap E F)) = ⊤) :
    IsAbelianGalois B F := by
  haveI : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite ℚ K E
  haveI : FiniteDimensional K F := Module.Finite.of_restrictScalars_finite ℚ K F
  haveI : IsGalois K (IsScalarTower.toAlgHom K E F).fieldRange :=
    IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K E F))
  haveI : FiniteDimensional K (IsScalarTower.toAlgHom K E F).fieldRange :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K E F)).toLinearEquiv.finiteDimensional
  have hsup : (IsScalarTower.toAlgHom K E F).fieldRange ⊔
      (IsScalarTower.toAlgHom K B F).fieldRange = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Algebra.adjoin B (Set.range (algebraMap E F)) := by
      rw [hgen]
      exact Algebra.mem_top
    let T : Subalgebra B F :=
      { toSubsemiring := ((IsScalarTower.toAlgHom K E F).fieldRange ⊔
          (IsScalarTower.toAlgHom K B F).fieldRange).toSubalgebra.toSubsemiring
        algebraMap_mem' := fun b => (le_sup_right : (IsScalarTower.toAlgHom K B F).fieldRange ≤ _)
          ⟨b, rfl⟩ }
    have hle : Algebra.adjoin B (Set.range (algebraMap E F)) ≤ T := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨e, rfl⟩
      exact (le_sup_left : (IsScalarTower.toAlgHom K E F).fieldRange ≤ _) ⟨e, rfl⟩
    exact hle hx
  haveI : IsGalois (IsScalarTower.toAlgHom K B F).fieldRange F := IsGalois.sup_right _ _ hsup
  haveI : Algebra.IsAlgebraic (IsScalarTower.toAlgHom K B F).fieldRange F :=
    Algebra.IsAlgebraic.tower_top (K := K) _
  let eB : B ≃ₐ[K] (IsScalarTower.toAlgHom K B F).fieldRange :=
    AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K B F)
  haveI : IsGalois B F := IsGalois.of_equiv_equiv (f := eB.symm.toRingEquiv)
    (g := RingEquiv.refl F) (RingHom.ext fun x => congrArg Subtype.val (eB.apply_symm_apply x))
  have hinj := compositum_restriction_injective K E B F hgen
  haveI : IsMulCommutative (F ≃ₐ[B] F) := by
    refine ⟨⟨fun σ τ => hinj ?_⟩⟩
    change AlgEquiv.restrictNormalHom E ((σ * τ).restrictScalars K) =
      AlgEquiv.restrictNormalHom E ((τ * σ).restrictScalars K)
    have hm : ∀ a b : F ≃ₐ[B] F,
        (a * b).restrictScalars K = a.restrictScalars K * b.restrictScalars K := fun a b => rfl
    rw [hm, hm, map_mul, map_mul]
    exact (inferInstance : IsMulCommutative (E ≃ₐ[K] E)).is_comm.comm _ _
  exact ⟨⟩

include hNF_K hNF_E hNF_F hNF_B in
/-- Janusz p186's classification step, using a finer comparison modulus when necessary. -/
theorem exists_algHom_of_erased_norm_kernel [IsAbelianGalois K E] [IsAbelianGalois B F]
    (C : Type*) [Field C] [NumberField C] [Algebra B C]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (n : Ideal (𝓞 B)) (hn : n ≠ ⊥)
    (φ : coprimeIdeals K m →* (E ≃ₐ[K] E)) (hφ : IsArtinMap K m E φ)
    (hU : IsUnramifiedAway K m E)
    (H : Subgroup (coprimeIdeals B n)) (hC : HasArtinKernel B n C H)
    (hgen : Algebra.adjoin B (Set.range (algebraMap E F)) = ⊤)
    (hNorm : ∀ X : coprimeIdeals B n, X ∈ H →
      φ (eraseModulusFactors K m (idealUnitNorm K B X)) = 1) :
    Nonempty (F →ₐ[B] C) := by
  obtain ⟨hfinC, hgalC, hcommC, hUC, χ, hχ, hχs, hχk⟩ := hC
  haveI : FiniteDimensional B F := Module.Finite.of_restrictScalars_finite ℚ B F
  haveI : Module.Finite (𝓞 K) (𝓞 B) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 B)
  haveI : Module.Finite (𝓞 B) (𝓞 F) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 B) (𝓞 F)
  obtain ⟨rF, hrF0, hrFU⟩ := exists_unramifiedAway_modulus B F
  have hr₀ : n * (m.map (algebraMap (𝓞 K) (𝓞 B)) * rF) ≠ ⊥ :=
    mul_ne_zero hn (mul_ne_zero (Ideal.map_ne_bot_of_ne_bot hm) hrF0)
  obtain ⟨d, hd0, hdm, hdr⟩ := exists_base_modulus K B m hm _ hr₀
  have hR0 : d.map (algebraMap (𝓞 K) (𝓞 B)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hd0
  have hRn : d.map (algebraMap (𝓞 K) (𝓞 B)) ≤ n := hdr.trans Ideal.mul_le_right
  have hUF : IsUnramifiedAway B (d.map (algebraMap (𝓞 K) (𝓞 B))) F := fun q hq hq0 hqR =>
    hrFU q hq hq0 (eq_top_mono (sup_le_sup_left
      (hdr.trans (Ideal.mul_le_left.trans Ideal.mul_le_left)) q) hqR)
  obtain ⟨ψ, hψ, hψs⟩ := exists_artinMap B _ F hR0 hUF
  have hCR := hasArtinKernel_restrictModulus B _ n hR0 hRn C H
    ⟨hfinC, hgalC, hcommC, hUC, χ, hχ, hχs, hχk⟩
  have hUd : IsUnramifiedAway K d E := fun q hq hq0 hqd =>
    hU q hq hq0 (eq_top_mono (sup_le_sup_left hdm q) hqd)
  have hφd := isArtinMap_comp_inclusion K E hdm φ hφ
  have hinj := compositum_restriction_injective K E B F hgen
  have hone : AlgEquiv.restrictNormalHom E ((1 : F ≃ₐ[B] F).restrictScalars K) = 1 := by
    have h1 : (1 : F ≃ₐ[B] F).restrictScalars K = 1 := AlgEquiv.ext fun _ => rfl
    rw [h1, map_one]
  have hker : H.comap (Subgroup.inclusion (coprimeIdeals_mono B hRn)) ≤ ψ.ker := by
    intro X hX
    rw [Subgroup.mem_comap] at hX
    have hX1 := hNorm _ hX
    obtain ⟨A, B', uN, hA, hB', hAm, hB'm, hu, hN⟩ := exists_coprime_norm_quotient K B d X
    have hres := artin_baseChange_quotient_norm K E B F d _ hφd hUd ψ hψ X A B' hA hB' hAm hB'm
      hu uN hN
    have hB'ne : (B' : FractionalIdeal (𝓞 B)⁰ B) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hB'
    have hNB' : (Ideal.relNorm (𝓞 K) B' : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (Ideal.relNorm_eq_bot_iff.not.mpr hB')
    have hNX : ((idealUnitNorm K B X : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
        (Ideal.relNorm (𝓞 K) B' : FractionalIdeal (𝓞 K)⁰ K) = Ideal.relNorm (𝓞 K) A := by
      have h1 := idealUnitNorm_integral K B (Units.mk0 _ hB'ne) B' rfl
      have h2 := idealUnitNorm_integral K B ((X : (FractionalIdeal (𝓞 B)⁰ B)ˣ) * Units.mk0 _ hB'ne)
        A (by rw [Units.val_mul, Units.val_mk0, hu])
      rw [map_mul, Units.val_mul, h1] at h2
      exact h2
    have huN : (uN : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = idealUnitNorm K B X :=
      Units.ext (mul_right_cancel₀ hNB' (hN.trans hNX.symm))
    have hmN : idealUnitNorm K B X ∈ coprimeIdeals K m := huN ▸ coprimeIdeals_mono K hdm uN.2
    have herase : eraseModulusFactors K m (idealUnitNorm K B
        (Subgroup.inclusion (coprimeIdeals_mono B hRn) X)) =
          Subgroup.inclusion (coprimeIdeals_mono K hdm) uN := by
      rw [Subgroup.coe_inclusion]
      rw [show (idealUnitNorm K B X : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        ((⟨_, hmN⟩ : coprimeIdeals K m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) from rfl,
        eraseModulusFactors_coprime]
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
      exact huN.symm
    rw [herase] at hX1
    rw [MonoidHom.mem_ker]
    apply hinj
    change AlgEquiv.restrictNormalHom E ((ψ X).restrictScalars K) =
      AlgEquiv.restrictNormalHom E ((1 : F ≃ₐ[B] F).restrictScalars K)
    rw [hres, hone, MonoidHom.comp_apply]
    exact hX1
  have hFK : HasArtinKernel B (d.map (algebraMap (𝓞 K) (𝓞 B))) F ψ.ker :=
    ⟨inferInstance, inferInstance, inferInstance, hUF, ψ, hψ, hψs, rfl⟩
  exact exists_algHom_of_artin_kernel_le B F C _ hR0 hFK hCR hker

end Cox.ClassFieldTheory
